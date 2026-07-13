#include <SFML/Graphics.hpp>
#include <SFML/Window.hpp>
#include <SFML/System.hpp>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <queue>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// ============================================================
// National Disaster Evacuation System (Professional 2D)
// - Province-cluster layout with Poisson-disc spacing 
// - Highways + secondary roads (toggle + auto hide when zoomed out)
// - Labels only on hover (always show start + destination shelter)
// - Many shelters (~100) distributed by province
// - Wizard input: trim, partial match, suggestions, back/restart
// - Destination: AUTO nearest shelter or manual city
// - Disaster menu: number or words
// - Algorithm menu: number or words
// - Voice: intro + wizard prompts + result only (rate-limited)
// Font: Windows Arial (no external file)
// ============================================================

static float clampf(float v, float lo, float hi) { return std::max(lo, std::min(hi, v)); }
static float dist2(const sf::Vector2f& a, const sf::Vector2f& b){ float dx=a.x-b.x, dy=a.y-b.y; return dx*dx+dy*dy; }
static float dist(const sf::Vector2f& a, const sf::Vector2f& b){ return std::sqrt(dist2(a,b)); }

static std::string toLower(std::string s){
    for(char& c : s) c = (char)std::tolower((unsigned char)c);
    return s;
}
static std::string trim(std::string s){
    while(!s.empty() && std::isspace((unsigned char)s.front())) s.erase(s.begin());
    while(!s.empty() && std::isspace((unsigned char)s.back())) s.pop_back();
    return s;
}
static bool startsWith(const std::string& a, const std::string& b){
    if(b.size() > a.size()) return false;
    for(size_t i=0;i<b.size();i++) if(std::tolower((unsigned char)a[i]) != std::tolower((unsigned char)b[i])) return false;
    return true;
}
static bool containsCaseInsensitive(const std::string& hay, const std::string& needle){
    std::string h = toLower(hay);
    std::string n = toLower(needle);
    return h.find(n) != std::string::npos;
}

// --------------------------- Voice (rate-limited, dedupe) ---------------------------
static std::string escapeForCmd(std::string s) {
    for (auto &ch : s) {
        if (ch == '"') ch = '\'';
        if (ch == '\n' || ch == '\r') ch = ' ';
    }
    return s;
}
struct Speaker {
    bool enabled = true;
    sf::Clock cd;
    float cooldownSec = 1.2f;
    std::string lastMsg;

    void say(const std::string& msg){
        if(!enabled) return;
        std::string m = escapeForCmd(msg);
        float t = cd.getElapsedTime().asSeconds();
        if(m == lastMsg && t < cooldownSec) return;
        if(t < cooldownSec) return;
        lastMsg = m;
        cd.restart();

        std::thread([m](){
#ifdef _WIN32
            std::string cmd =
                "powershell -NoProfile -Command \""
                "Add-Type -AssemblyName System.Speech; "
                "$speak = New-Object System.Speech.Synthesis.SpeechSynthesizer; "
                "$speak.Rate = 0; "
                "$speak.Volume = 90; "
                "$speak.Speak(\\\"" + m + "\\\");\"";
            system(cmd.c_str());
#elif __APPLE__
            std::string cmd = "say \"" + m + "\"";
            system(cmd.c_str());
#else
            std::string cmd = "espeak \"" + m + "\" >/dev/null 2>&1";
            system(cmd.c_str());
#endif
        }).detach();
    }
};

// --------------------------- Types ---------------------------
enum class Province { Punjab, Sindh, KPK, Balochistan, GB, AJK };
static const char* provinceName(Province p){
    switch(p){
        case Province::Punjab: return "Punjab";
        case Province::Sindh: return "Sindh";
        case Province::KPK: return "KPK";
        case Province::Balochistan: return "Balochistan";
        case Province::GB: return "Gilgit-Baltistan";
        default: return "AJK";
    }
}
enum class NodeType { City, Shelter };
enum class Disaster { None, Flood, Earthquake, Fire, Cyclone };
static const char* disasterName(Disaster d){
    switch(d){
        case Disaster::None: return "None";
        case Disaster::Flood: return "Flood";
        case Disaster::Earthquake: return "Earthquake";
        case Disaster::Fire: return "Fire";
        default: return "Cyclone";
    }
}
enum class Algo { BFS, DFS, Dijkstra };
static const char* algoName(Algo a){
    switch(a){
        case Algo::BFS: return "BFS";
        case Algo::DFS: return "DFS";
        default: return "Dijkstra";
    }
}
struct Edge { int to; float w; bool highway=false; };

struct Node {
    std::string name;
    NodeType type = NodeType::City;
    Province prov = Province::Punjab;
    sf::Vector2f pos{};
    bool blocked=false; // cities only
};

struct AlgoResult{
    std::vector<int> path;
    std::vector<int> visited;
    bool found=false;
    float cost=0.f;
    int dest=-1;
};

// --------------------------- Graph ---------------------------
struct Graph {
    std::vector<Node> nodes;
    std::vector<std::vector<Edge>> adj;

    std::vector<int> cities;
    std::vector<int> shelters;

    std::unordered_map<std::string,int> cityByExact; // exact city name -> index

    int addCity(const std::string& name, Province p){
        int idx=(int)nodes.size();
        nodes.push_back(Node{name, NodeType::City, p, {0,0}, false});
        adj.emplace_back();
        cities.push_back(idx);
        cityByExact[toLower(name)] = idx;
        return idx;
    }
    int addShelter(const std::string& name, Province p){
        int idx=(int)nodes.size();
        nodes.push_back(Node{name, NodeType::Shelter, p, {0,0}, false});
        adj.emplace_back();
        shelters.push_back(idx);
        return idx;
    }
    void addEdge2(int a,int b,float w,bool highway){
        if(a==b) return;
        adj[a].push_back({b,w,highway});
        adj[b].push_back({a,w,highway});
    }
};

// --------------------------- Data (Cities 220+) ---------------------------
static std::vector<std::string> pakistanCities220plus() {
    return {
        // Punjab (includes required)
        "Lahore","Faisalabad","Rawalpindi","Gujranwala","Multan","Sialkot","Bahawalpur","Sargodha","Sheikhupura",
        "Rahim Yar Khan","Jhang","Dera Ghazi Khan","Gujrat","Sahiwal","Wah Cantonment","Kasur","Okara","Mandi Bahauddin",
        "Chiniot","Hafizabad","Khanewal","Muzaffargarh","Mianwali","Toba Tek Singh","Narowal","Shakargarh","Zafarwal","Pasrur",
        "Jhelum","Attock","Chakwal","Nankana Sahib","Layyah","Bhakkar","Vehari","Pakpattan","Lodhran","Bahawalnagar",
        "Khushab","Arifwala","Burewala","Chichawatni","Mailsi","Dunyapur","Kabirwala","Shorkot","Ahmadpur East",
        "Hasilpur","Yazman","Haroonabad","Fort Abbas","Chishtian","Minchinabad","Dipalpur","Renala Khurd",
        "Pattoki","Kot Radha Kishan","Kahna","Raiwind","Murree","Taxila","Hasan Abdal","Gujar Khan",
        "Kahuta","Bhalwal","Shahpur","Sillanwali","Lalian","Bhawana","Kharian","Sarai Alamgir",
        "Daska","Sambrial","Wazirabad","Eminabad","Kamoke","Ghakhar Mandi","Muridke","Sharqpur",
        "Safdarabad","Farooqabad","Jaranwala","Tandlianwala","Sangla Hill","Shahkot","Pindi Bhattian",
        "Gojra","Kamalia","Pir Mahal","Chak Jhumra","Sammundri","Kot Addu","Alipur (Muzaffargarh)",
        "Jampur","Rajanpur","Rojhan","Jalalpur Pirwala","Khanpur","Liaquatpur","Sadiqabad","Uch Sharif",
        "Jatoi","Kundian","Daud Khel","Piplan","Isakhel","Kalabagh","Darya Khan","Kaloorkot",
        "Chawinda","Noor Kot","Baddomalhi","Narang Mandi","Kunjah","Guliana",

        // Sindh
        "Karachi","Hyderabad","Sukkur","Larkana","Nawabshah","Mirpur Khas","Jacobabad","Shikarpur","Khairpur","Dadu",
        "Thatta","Badin","Tando Adam","Tando Allahyar","Tando Muhammad Khan","Umerkot","Mithi","Islamkot",
        "Kandhkot","Kashmore","Ghotki","Rohri","Pano Aqil","Moro","Kandiaro","Mehrabpur",
        "Sanghar","Jamshoro","Sehwan Sharif","Kotri","Hala","Matiari","Talhar","Sujawal",
        "Sakrand","Qazi Ahmad","Daur","Dighri","Kunri","Samaro",
        "Ubauro","Daharki","Mirpur Mathelo","Khanpur Mahar","Warah","Dokri","Ratodero","Mehar","Johi",

        // KPK
        "Peshawar","Mardan","Mingora","Kohat","Dera Ismail Khan","Abbottabad","Mansehra","Swabi","Nowshera","Charsadda",
        "Haripur","Bannu","Karak","Lakki Marwat","Tank","Hangu","Jamrud","Bara","Landikotal",
        "Dir","Timergara","Chitral","Drosh","Kalam","Batkhela","Takht Bhai",
        "Topi","Risalpur","Akora Khattak","Kabal","Matta","Barikot","Alpuri","Besham",
        "Daggar","Dasu","Paharpur","Kulachi","Daraban","Saidu Sharif",

        // Balochistan
        "Quetta","Turbat","Khuzdar","Chaman","Gwadar","Sibi","Zhob","Loralai","Dera Murad Jamali","Usta Muhammad",
        "Hub","Uthal","Bela","Ormara","Pasni","Kalat","Mastung","Nushki","Kharan",
        "Panjgur","Awaran","Qila Abdullah","Qila Saifullah","Pishin","Barkhan","Musakhel","Kohlu","Duki",
        "Ziarat","Harnai","Mach","Dalbandin","Taftan","Jiwani","Surab","Wadh","Gaddani",

        // GB
        "Gilgit","Skardu","Hunza","Aliabad","Karimabad","Gahkuch","Chilas","Danyor","Jaglot",
        "Khaplu","Shigar","Astore","Sost","Passu","Gupis","Yasin","Phander","Naltar",

        // AJK
        "Muzaffarabad","Mirpur (AJK)","Rawalakot","Kotli (AJK)","Bhimber","Bagh","Neelum","Athmuqam",
        "Sehnsa","Pallandri","Dadyal","Samahni","Chikar","Dhirkot","Hajira","Tattapani"
    };
}

// --------------------------- Province mapping by index range (stable to our list) ---------------------------
static Province provinceForCityIndex(int i){
    // Our list ordering is: Punjab (~100), Sindh (~45), KPK (~45), Balochistan (~45), GB (~19), AJK (~16)
    if(i < 100) return Province::Punjab;
    if(i < 145) return Province::Sindh;
    if(i < 190) return Province::KPK;
    if(i < 235) return Province::Balochistan;
    if(i < 254) return Province::GB;
    return Province::AJK;
}

// --------------------------- Layout regions (map-like, not vast) ---------------------------
struct Region { sf::FloatRect r; Province p; };

static std::vector<Region> regions(){
    // World area (right side) is 1600x1000; HUD takes left ~460px.
    // These rectangles are tuned for compact, professional look.
    return {
        { { 520.f, 160.f, 480.f, 360.f }, Province::Punjab },
        { { 980.f, 580.f, 520.f, 340.f }, Province::Sindh },
        { { 520.f,  40.f, 360.f, 190.f }, Province::KPK },
        { { 520.f, 580.f, 430.f, 360.f }, Province::Balochistan },
        { { 900.f,  40.f, 330.f, 160.f }, Province::GB },
        { { 1090.f, 200.f, 410.f, 240.f }, Province::AJK }
    };
}

static sf::FloatRect regionRect(Province p){
    for(const auto& reg : regions()) if(reg.p==p) return reg.r;
    return {520.f,160.f,480.f,360.f};
}

// Poisson-disc-ish placement inside region to avoid merging
static std::vector<sf::Vector2f> scatterPointsInRect(
    std::mt19937& rng, sf::FloatRect r, int count, float minDist, int maxTries=40000)
{
    std::uniform_real_distribution<float> X(r.left, r.left + r.width);
    std::uniform_real_distribution<float> Y(r.top,  r.top  + r.height);

    std::vector<sf::Vector2f> pts;
    pts.reserve(count);

    for(int t=0; t<maxTries && (int)pts.size() < count; t++){
        sf::Vector2f p{ X(rng), Y(rng) };
        bool ok=true;
        for(const auto& q : pts){
            if(dist2(p,q) < minDist*minDist){ ok=false; break; }
        }
        if(ok) pts.push_back(p);
    }

    // If not enough, relax minDist slightly and fill
    while((int)pts.size() < count){
        sf::Vector2f p{ X(rng), Y(rng) };
        pts.push_back(p);
    }
    return pts;
}

// --------------------------- Roads building (clean + readable) ---------------------------
static void dedupe(std::vector<std::vector<Edge>>& adj){
    for(auto& v : adj){
        std::sort(v.begin(), v.end(), [](const Edge& a, const Edge& b){
            if(a.to!=b.to) return a.to<b.to;
            if(a.highway!=b.highway) return a.highway > b.highway;
            return a.w < b.w;
        });
        v.erase(std::unique(v.begin(), v.end(), [](const Edge& a, const Edge& b){
            return a.to==b.to && a.highway==b.highway;
        }), v.end());
    }
}

static void rebuildRoads(Graph& g, int withinK=3, int shelterLinks=2){
    g.adj.assign(g.nodes.size(), {});

    // KNN within province for cities (secondary)
    for(int i : g.cities){
        std::vector<std::pair<float,int>> d;
        d.reserve(64);
        for(int j : g.cities){
            if(i==j) continue;
            if(g.nodes[i].prov != g.nodes[j].prov) continue;
            d.push_back({dist2(g.nodes[i].pos, g.nodes[j].pos), j});
        }
        if(d.empty()) continue;
        int take = std::min(withinK, (int)d.size());
        std::nth_element(d.begin(), d.begin()+take, d.end(), [](auto& a, auto& b){ return a.first<b.first; });
        for(int k=0;k<take;k++){
            int j=d[k].second;
            float w=std::sqrt(d[k].first);
            g.addEdge2(i,j,w,false);
        }
    }

    // Highways between hubs (clean “main roads”)
    auto city = [&](const std::string& name)->int{
        auto it = g.cityByExact.find(toLower(name));
        return (it==g.cityByExact.end()) ? -1 : it->second;
    };
    auto addHW = [&](const std::string& a, const std::string& b){
        int ia=city(a), ib=city(b);
        if(ia>=0 && ib>=0){
            float w = dist(g.nodes[ia].pos, g.nodes[ib].pos) * 0.55f;
            g.addEdge2(ia,ib,w,true);
        }
    };

    addHW("Lahore","Faisalabad");
    addHW("Lahore","Rawalpindi");
    addHW("Rawalpindi","Peshawar");
    addHW("Lahore","Multan");
    addHW("Multan","Sukkur");
    addHW("Sukkur","Hyderabad");
    addHW("Hyderabad","Karachi");
    addHW("Quetta","Karachi");
    addHW("Quetta","Gwadar");
    addHW("Islamabad","Muzaffarabad"); // may not exist in list; safe if not found
    addHW("Gilgit","Skardu");          // may not exist; safe if not found

    // Shelters to nearby cities
    for(int s : g.shelters){
        std::vector<std::pair<float,int>> d;
        d.reserve(64);
        for(int c : g.cities){
            float w = dist2(g.nodes[s].pos, g.nodes[c].pos);
            if(g.nodes[s].prov == g.nodes[c].prov) w *= 0.75f;
            d.push_back({w,c});
        }
        int take = std::min(shelterLinks, (int)d.size());
        std::nth_element(d.begin(), d.begin()+take, d.end(), [](auto& a, auto& b){ return a.first<b.first; });
        for(int k=0;k<take;k++){
            int c=d[k].second;
            float w=std::sqrt(d[k].first) * 0.85f;
            g.addEdge2(s,c,w,false);
        }
    }

    dedupe(g.adj);
}

// --------------------------- Algorithms ---------------------------
static bool passable(const Graph& g, int idx){
    const Node& n = g.nodes[idx];
    if(n.type==NodeType::City && n.blocked) return false;
    return true;
}

static std::vector<int> reconstruct(int start,int goal,const std::vector<int>& parent){
    std::vector<int> p;
    int cur=goal;
    while(cur!=-1){
        p.push_back(cur);
        if(cur==start) break;
        cur=parent[cur];
    }
    if(p.empty() || p.back()!=start) return {};
    std::reverse(p.begin(), p.end());
    return p;
}

static AlgoResult BFS(const Graph& g, int start, int goal){
    AlgoResult r;
    int n=(int)g.nodes.size();
    if(start<0||goal<0||start>=n||goal>=n) return r;
    if(!passable(g,start) || !passable(g,goal)) return r;

    std::vector<int> parent(n,-1);
    std::vector<char> vis(n,0);
    std::queue<int> q;
    q.push(start); vis[start]=1;

    while(!q.empty()){
        int u=q.front(); q.pop();
        r.visited.push_back(u);
        if(u==goal) break;
        for(const auto& e : g.adj[u]){
            int v=e.to;
            if(vis[v]) continue;
            if(!passable(g,v)) continue;
            vis[v]=1;
            parent[v]=u;
            q.push(v);
        }
    }
    r.path = reconstruct(start,goal,parent);
    r.found = !r.path.empty();
    r.cost = r.found ? (float)(r.path.size()-1) : 0.f;
    r.dest=goal;
    return r;
}

static void dfsRec(const Graph& g, int u, int goal, std::vector<char>& vis, std::vector<int>& parent, AlgoResult& r, bool& stop){
    if(stop) return;
    vis[u]=1;
    r.visited.push_back(u);
    if(u==goal){ stop=true; return; }
    for(const auto& e : g.adj[u]){
        int v=e.to;
        if(vis[v]) continue;
        if(!passable(g,v)) continue;
        parent[v]=u;
        dfsRec(g,v,goal,vis,parent,r,stop);
        if(stop) return;
    }
}

static AlgoResult DFS(const Graph& g, int start, int goal){
    AlgoResult r;
    int n=(int)g.nodes.size();
    if(start<0||goal<0||start>=n||goal>=n) return r;
    if(!passable(g,start) || !passable(g,goal)) return r;

    std::vector<char> vis(n,0);
    std::vector<int> parent(n,-1);
    bool stop=false;
    dfsRec(g,start,goal,vis,parent,r,stop);

    r.path = reconstruct(start,goal,parent);
    r.found = !r.path.empty();
    r.cost = r.found ? (float)(r.path.size()-1) : 0.f;
    r.dest=goal;
    return r;
}

static AlgoResult Dijkstra(const Graph& g, int start, int goal, bool preferHighways=true){
    AlgoResult r;
    int n=(int)g.nodes.size();
    if(start<0||goal<0||start>=n||goal>=n) return r;
    if(!passable(g,start) || !passable(g,goal)) return r;

    const float INF = std::numeric_limits<float>::infinity();
    std::vector<float> distv(n, INF);
    std::vector<int> parent(n, -1);
    std::vector<char> done(n,0);

    using P = std::pair<float,int>;
    std::priority_queue<P, std::vector<P>, std::greater<P>> pq;

    distv[start]=0;
    pq.push({0,start});

    while(!pq.empty()){
        auto [d,u]=pq.top(); pq.pop();
        if(done[u]) continue;
        done[u]=1;
        r.visited.push_back(u);
        if(u==goal) break;

        for(const auto& e : g.adj[u]){
            int v=e.to;
            if(!passable(g,v)) continue;
            float w = e.w;
            if(preferHighways && e.highway) w *= 0.85f;
            float nd = d + w;
            if(nd < distv[v]){
                distv[v]=nd;
                parent[v]=u;
                pq.push({nd,v});
            }
        }
    }

    r.path = reconstruct(start,goal,parent);
    r.found = !r.path.empty();
    r.cost = r.found ? distv[goal] : 0.f;
    r.dest=goal;
    return r;
}

// --------------------------- Nearest shelter destination (free help) ---------------------------
static int findNearestShelter(const Graph& g, int start, Algo algo){
    int best=-1;
    float bestCost = std::numeric_limits<float>::infinity();

    for(int s : g.shelters){
        if(!passable(g,s)) continue;
        AlgoResult rr;
        if(algo==Algo::BFS) rr = BFS(g,start,s);
        else if(algo==Algo::DFS) rr = DFS(g,start,s);
        else rr = Dijkstra(g,start,s,true);

        if(rr.found && rr.cost < bestCost){
            bestCost = rr.cost;
            best = s;
        }
    }
    return best;
}

// --------------------------- Disaster effects ---------------------------
static void applyDisaster(Graph& g, Disaster d, int epicenterCity){
    // reset
    for(auto& n : g.nodes) if(n.type==NodeType::City) n.blocked=false;
    if(d==Disaster::None) return;
    if(epicenterCity < 0 || epicenterCity >= (int)g.nodes.size()) return;

    sf::Vector2f c = g.nodes[epicenterCity].pos;

    float radius=0.f;
    float blockProb=0.f;
    switch(d){
        case Disaster::Flood:      radius=170.f; blockProb=0.26f; break;
        case Disaster::Earthquake: radius=140.f; blockProb=0.20f; break;
        case Disaster::Fire:       radius=110.f; blockProb=0.16f; break;
        case Disaster::Cyclone:    radius=200.f; blockProb=0.30f; break;
        default: break;
    }

    std::mt19937 rng(20260125);
    std::uniform_real_distribution<float> U(0.f,1.f);

    for(int idx : g.cities){
        float dpx = dist(g.nodes[idx].pos, c);
        if(dpx <= radius){
            float p = blockProb * (1.f - dpx/radius);
            if(U(rng) < p) g.nodes[idx].blocked=true;
        }
    }

    // ensure user city stays accessible
    g.nodes[epicenterCity].blocked=false;
}

// --------------------------- UI ---------------------------
struct Button {
    sf::FloatRect rect;
    std::string text;
    bool hovered=false;
    bool hit(sf::Vector2f p) const { return rect.contains(p); }
};
struct TextBox {
    sf::FloatRect rect;
    std::string value;
    bool active=false;
    void append(uint32_t u){
        if(u==8){ if(!value.empty()) value.pop_back(); return; }
        if(u>=32 && u<127) value.push_back((char)u);
    }
};

// --------------------------- Professional rendering helpers ---------------------------
static void drawLineGlow(sf::RenderWindow& win, sf::Vector2f a, sf::Vector2f b, float w, sf::Color core, sf::Color glow){
    sf::Vector2f d = b-a;
    float len = std::sqrt(d.x*d.x + d.y*d.y);
    if(len < 0.01f) return;

    float ang = std::atan2(d.y,d.x) * 180.f / 3.1415926f;

    // glow layer
    sf::RectangleShape g({len, w*2.2f});
    g.setOrigin(0.f, (w*2.2f)*0.5f);
    g.setPosition(a);
    g.setRotation(ang);
    g.setFillColor(glow);
    win.draw(g);

    // core layer
    sf::RectangleShape c({len, w});
    c.setOrigin(0.f, w*0.5f);
    c.setPosition(a);
    c.setRotation(ang);
    c.setFillColor(core);
    win.draw(c);
}

static void drawNodeCity(sf::RenderWindow& win, sf::Vector2f p, sf::Color fill, bool isStart, bool blocked){
    // glow ring + core + highlight
    float r = isStart ? 7.5f : 5.3f;

    sf::CircleShape glow(r*1.9f);
    glow.setOrigin(r*1.9f, r*1.9f);
    glow.setPosition(p);
    glow.setFillColor(sf::Color(fill.r, fill.g, fill.b, 45));
    win.draw(glow);

    sf::CircleShape outer(r*1.15f);
    outer.setOrigin(r*1.15f, r*1.15f);
    outer.setPosition(p);
    outer.setFillColor(blocked ? sf::Color(160,40,40,220) : sf::Color(30,40,70,220));
    win.draw(outer);

    sf::CircleShape core(r);
    core.setOrigin(r,r);
    core.setPosition(p);
    core.setFillColor(blocked ? sf::Color(230,75,75,255) : fill);
    win.draw(core);

    sf::CircleShape hi(r*0.45f);
    hi.setOrigin(r*0.45f, r*0.45f);
    hi.setPosition(p + sf::Vector2f(-r*0.25f, -r*0.25f));
    hi.setFillColor(sf::Color(255,255,255,120));
    win.draw(hi);
}

static void drawNodeShelter(sf::RenderWindow& win, sf::Vector2f p, bool isDest){
    // shelter as diamond with glow
    float s = isDest ? 13.f : 10.f;

    sf::CircleShape glow(s*1.2f);
    glow.setOrigin(s*1.2f, s*1.2f);
    glow.setPosition(p);
    glow.setFillColor(isDest ? sf::Color(255,180,90,60) : sf::Color(90,240,220,50));
    win.draw(glow);

    sf::ConvexShape diamond(4);
    diamond.setPoint(0, {0, -s});
    diamond.setPoint(1, {s, 0});
    diamond.setPoint(2, {0, s});
    diamond.setPoint(3, {-s, 0});
    diamond.setPosition(p);
    diamond.setFillColor(isDest ? sf::Color(255,170,70,255) : sf::Color(120,255,220,240));
    win.draw(diamond);

    sf::ConvexShape inner(4);
    float si = s*0.55f;
    inner.setPoint(0, {0, -si});
    inner.setPoint(1, {si, 0});
    inner.setPoint(2, {0, si});
    inner.setPoint(3, {-si, 0});
    inner.setPosition(p);
    inner.setFillColor(sf::Color(20,25,40,210));
    win.draw(inner);
}

// --------------------------- Suggestions for city input ---------------------------
static std::vector<std::string> suggestCities(const Graph& g, const std::string& query, int maxSug=6){
    std::vector<std::pair<int,std::string>> scored;

    std::string q = toLower(trim(query));
    if(q.empty()) return {};

    // Score: startsWith high, contains medium
    for(int idx : g.cities){
        const std::string& name = g.nodes[idx].name;
        std::string ln = toLower(name);

        int score = -100000;
        if(ln == q) score = 1000;
        else if(startsWith(ln, q)) score = 800 - (int)(ln.size()-q.size());
        else if(ln.find(q) != std::string::npos) score = 400 - (int)(ln.size());
        if(score > -100000) scored.push_back({score, name});
    }

    std::sort(scored.begin(), scored.end(), [](auto& a, auto& b){ return a.first>b.first; });
    std::vector<std::string> out;
    for(int i=0;i<(int)scored.size() && (int)out.size()<maxSug;i++) out.push_back(scored[i].second);
    return out;
}

static int resolveCitySmart(const Graph& g, const std::string& input, std::vector<std::string>* outSug=nullptr){
    std::string s = toLower(trim(input));
    if(s.empty()) return -1;

    // exact first
    auto it = g.cityByExact.find(s);
    if(it != g.cityByExact.end()) return it->second;

    // if user typed partial, pick best suggestion
    auto sug = suggestCities(g, s, 6);
    if(outSug) *outSug = sug;
    if(!sug.empty()){
        // auto-pick first only if it is strong (startsWith)
        std::string best = sug[0];
        if(startsWith(toLower(best), s)) {
            auto it2 = g.cityByExact.find(toLower(best));
            if(it2 != g.cityByExact.end()) return it2->second;
        }
    }
    return -1;
}

// --------------------------- Parse disaster/algo from input ---------------------------
static bool parseDisaster(const std::string& input, Disaster& out){
    std::string s = toLower(trim(input));
    if(s=="1" || s=="none") { out=Disaster::None; return true; }
    if(s=="2" || s=="flood") { out=Disaster::Flood; return true; }
    if(s=="3" || s=="earthquake" || s=="quake") { out=Disaster::Earthquake; return true; }
    if(s=="4" || s=="fire") { out=Disaster::Fire; return true; }
    if(s=="5" || s=="cyclone" || s=="storm") { out=Disaster::Cyclone; return true; }
    return false;
}
static bool parseAlgo(const std::string& input, Algo& out){
    std::string s = toLower(trim(input));
    if(s=="1" || s=="bfs") { out=Algo::BFS; return true; }
    if(s=="2" || s=="dfs") { out=Algo::DFS; return true; }
    if(s=="3" || s=="dijkstra" || s=="dijk" || s=="dj") { out=Algo::Dijkstra; return true; }
    return false;
}

// --------------------------- App State ---------------------------
struct App {
    Graph g;
    Speaker sp;
    sf::Font font;

    // Camera
    sf::View view;
    float zoom=1.f;
    bool panning=false;
    sf::Vector2f panStartWorld{};
    sf::Vector2i panStartMouse{};

    // Visual toggles
    bool showSecondary=true;
    bool autoHideSecondary=true;
    bool showVisited=true;

    // Wizard
    bool wizard=true;
    int step=0; // 0 start, 1 destination, 2 disaster, 3 algo, 4 done
    TextBox input;
    std::string prompt;
    std::vector<std::string> suggestions; // for city not found

    // Selection
    int start=-1;     // city
    int dest=-1;      // shelter or city
    bool destAuto=true;

    Disaster disaster=Disaster::None;
    Algo algo=Algo::Dijkstra;

    // Result
    AlgoResult last;
    bool hasResult=false;
    size_t visitedShown=0;
    sf::Clock animClock;
    int hovered=-1;

    // Steps list
    int stepsScroll=0;

    std::string status="Ready.";
};

// --------------------------- Build Graph (Professional layout + many shelters) ---------------------------
static void buildGraph(App& app){
    app.g = Graph{};

    auto cities = pakistanCities220plus();
    for(int i=0;i<(int)cities.size();i++){
        app.g.addCity(cities[i], provinceForCityIndex(i));
    }

    // Shelters: ~100 (distributed)
    auto addShelters = [&](Province p, const std::string& prefix, int count){
        for(int i=1;i<=count;i++){
            app.g.addShelter(prefix + " Shelter " + std::to_string(i), p);
        }
    };
    addShelters(Province::Punjab, "Rescue 1122 Punjab", 26);
    addShelters(Province::Sindh, "Rescue 1122 Sindh", 22);
    addShelters(Province::KPK, "Rescue 1122 KPK", 18);
    addShelters(Province::Balochistan, "Relief Balochistan", 18);
    addShelters(Province::GB, "Relief GB", 8);
    addShelters(Province::AJK, "Relief AJK", 10);

    // Place nodes compactly in province rectangles with Poisson-ish spacing
    std::mt19937 rng(123456);

    // Place cities
    {
        std::unordered_map<Province, std::vector<int>> provCities;
        for(int idx : app.g.cities) provCities[app.g.nodes[idx].prov].push_back(idx);

        for(auto& kv : provCities){
            Province p = kv.first;
            auto& idxs = kv.second;
            sf::FloatRect rr = regionRect(p);
            auto pts = scatterPointsInRect(rng, rr, (int)idxs.size(), 18.f);
            for(size_t i=0;i<idxs.size();i++) app.g.nodes[idxs[i]].pos = pts[i];
        }
    }

    // Place shelters (slightly wider spacing)
    {
        std::unordered_map<Province, std::vector<int>> provShel;
        for(int idx : app.g.shelters) provShel[app.g.nodes[idx].prov].push_back(idx);

        for(auto& kv : provShel){
            Province p = kv.first;
            auto& idxs = kv.second;
            sf::FloatRect rr = regionRect(p);
            auto pts = scatterPointsInRect(rng, rr, (int)idxs.size(), 26.f);
            for(size_t i=0;i<idxs.size();i++) app.g.nodes[idxs[i]].pos = pts[i];
        }
    }

    // Roads
    rebuildRoads(app.g, /*withinK*/3, /*shelterLinks*/2);
}

// --------------------------- Compute route ---------------------------
static AlgoResult runAlgo(const Graph& g, Algo algo, int start, int goal){
    if(algo==Algo::BFS) return BFS(g,start,goal);
    if(algo==Algo::DFS) return DFS(g,start,goal);
    return Dijkstra(g,start,goal,true);
}

static void compute(App& app){
    app.hasResult=false;
    app.last = AlgoResult{};
    app.visitedShown=0;
    app.stepsScroll=0;

    if(app.start < 0){
        app.status="Start city not set.";
        return;
    }

    // Apply disaster to graph
    applyDisaster(app.g, app.disaster, app.start);

    int goal = app.dest;

    // If AUTO destination: nearest shelter
    if(app.destAuto){
        goal = findNearestShelter(app.g, app.start, app.algo);
        app.dest = goal;
        if(goal < 0){
            app.status="No shelter reachable. Try enabling secondary roads or set disaster to none.";
            app.sp.say("No shelter reachable. Try enabling secondary roads or changing disaster type.");
            return;
        }
    }

    // compute
    app.last = runAlgo(app.g, app.algo, app.start, goal);
    app.last.dest = goal;
    app.hasResult=true;

    if(app.last.found){
        std::string dn = app.g.nodes[goal].name;
        app.status="Route ready. Destination: " + dn;
        app.sp.say("Route computed. Destination is " + dn);
    } else {
        app.status="No path found. Try toggling secondary roads or changing disaster.";
        app.sp.say("No path found.");
    }
}

// --------------------------- Picking ---------------------------
static int pickNode(const Graph& g, const sf::Vector2f& wpos, float radius){
    int best=-1;
    float bestD=radius*radius;
    for(int i=0;i<(int)g.nodes.size();i++){
        float d = dist2(g.nodes[i].pos, wpos);
        if(d < bestD){ bestD=d; best=i; }
    }
    return best;
}

// --------------------------- Drawing ---------------------------
static void drawText(sf::RenderWindow& win, sf::Font& font, const std::string& s, sf::Vector2f pos, int size, sf::Color col){
    sf::Text t(s, font, size);
    t.setFillColor(col);
    t.setPosition(pos);
    win.draw(t);
}

static void drawBackground(sf::RenderWindow& win){
    // “Satellite-like” dark professional background (no external images)
    sf::RectangleShape bg({1600.f,1000.f});
    bg.setPosition(0,0);
    bg.setFillColor(sf::Color(8,10,16));
    win.draw(bg);

    // subtle grid
    sf::VertexArray grid(sf::Lines);
    for(int x=480; x<=1550; x+=80){
        grid.append(sf::Vertex({(float)x, 30.f}, sf::Color(80,90,120,20)));
        grid.append(sf::Vertex({(float)x, 970.f}, sf::Color(80,90,120,20)));
    }
    for(int y=30; y<=970; y+=80){
        grid.append(sf::Vertex({480.f, (float)y}, sf::Color(80,90,120,20)));
        grid.append(sf::Vertex({1550.f, (float)y}, sf::Color(80,90,120,20)));
    }
    win.draw(grid);

    // province region boxes (faint)
    for(const auto& reg : regions()){
        sf::RectangleShape rr({reg.r.width, reg.r.height});
        rr.setPosition({reg.r.left, reg.r.top});
        rr.setFillColor(sf::Color(30,35,55,18));
        rr.setOutlineThickness(1.f);
        rr.setOutlineColor(sf::Color(110,120,160,50));
        win.draw(rr);
    }
}

static void drawEdges(sf::RenderWindow& win, const App& app){
    const Graph& g = app.g;

    bool showSecondary = app.showSecondary;
    if(app.autoHideSecondary && app.zoom > 1.55f) showSecondary = false; // zoomed out -> hide secondary

    for(int i=0;i<(int)g.nodes.size();i++){
        for(const auto& e : g.adj[i]){
            if(e.to < i) continue;
            if(!showSecondary && !e.highway) continue;

            const Node& a = g.nodes[i];
            const Node& b = g.nodes[e.to];

            // block tint
            bool blocked = ((a.type==NodeType::City && a.blocked) || (b.type==NodeType::City && b.blocked));

            // style
            float w = e.highway ? 2.9f : 1.4f;
            sf::Color core = e.highway ? sf::Color(170,180,210,150) : sf::Color(120,130,160,90);
            sf::Color glow = e.highway ? sf::Color(90,140,220,55)  : sf::Color(70,90,140,25);

            // shelter links
            if(a.type==NodeType::Shelter || b.type==NodeType::Shelter){
                w = 1.8f;
                core = sf::Color(110,210,200,120);
                glow = sf::Color(80,200,180,35);
            }

            if(blocked){
                core = sf::Color(200,70,70,120);
                glow = sf::Color(220,60,60,35);
            }

            drawLineGlow(win, a.pos, b.pos, w, core, glow);
        }
    }
}

static void drawVisited(sf::RenderWindow& win, const App& app){
    if(!app.hasResult || !app.showVisited) return;

    size_t count = std::min(app.visitedShown, app.last.visited.size());
    sf::CircleShape dot(2.4f);
    dot.setOrigin(2.4f,2.4f);
    dot.setFillColor(sf::Color(255,210,90,160));

    for(size_t i=0;i<count;i++){
        dot.setPosition(app.g.nodes[app.last.visited[i]].pos);
        win.draw(dot);
    }
}

static void drawArrow(sf::RenderWindow& win, sf::Vector2f from, sf::Vector2f to, sf::Color col){
    sf::Vector2f d = to-from;
    float len = std::sqrt(d.x*d.x + d.y*d.y);
    if(len < 1.f) return;
    sf::Vector2f u = d / len;

    sf::Vector2f tip = to;
    sf::Vector2f left = tip - u*14.f + sf::Vector2f(-u.y, u.x)*7.f;
    sf::Vector2f right= tip - u*14.f + sf::Vector2f(u.y, -u.x)*7.f;

    sf::ConvexShape tri(3);
    tri.setPoint(0, tip);
    tri.setPoint(1, left);
    tri.setPoint(2, right);
    tri.setFillColor(col);
    win.draw(tri);
}

static void drawPath(sf::RenderWindow& win, const App& app){
    if(!app.hasResult || !app.last.found || app.last.path.size()<2) return;

    sf::Color glow(0,220,170,70);
    sf::Color core(0,220,170,240);

    for(size_t i=1;i<app.last.path.size();i++){
        sf::Vector2f a = app.g.nodes[app.last.path[i-1]].pos;
        sf::Vector2f b = app.g.nodes[app.last.path[i]].pos;
        drawLineGlow(win, a, b, 5.2f, core, glow);
        if(i % 2 == 0) drawArrow(win, a, b, core);
    }
}

static void drawNodes(sf::RenderWindow& win, const App& app){
    const Graph& g=app.g;
    for(int i=0;i<(int)g.nodes.size();i++){
        const Node& n=g.nodes[i];
        if(n.type==NodeType::City){
            bool isStart = (i==app.start);
            sf::Color cityBlue = sf::Color(80,170,255,245);
            drawNodeCity(win, n.pos, cityBlue, isStart, n.blocked);
        } else {
            bool isDest = (i==app.dest && app.dest>=0);
            drawNodeShelter(win, n.pos, isDest);
        }
    }
}

static void drawHoverLabel(sf::RenderWindow& win, App& app){
    if(app.hovered < 0) return;
    const Node& n = app.g.nodes[app.hovered];

    std::string line = n.name;
    if(n.type==NodeType::City){
        line += "  ["; line += provinceName(n.prov); line += "]";
        if(n.blocked) line += "  (BLOCKED)";
    } else {
        line += "  [SHELTER]";
    }

    sf::Text t(line, app.font, 13);
    t.setFillColor(sf::Color::White);

    sf::Vector2f p = n.pos + sf::Vector2f(14.f, -22.f);
    t.setPosition(p);

    sf::FloatRect b = t.getLocalBounds();
    sf::RectangleShape bg({b.width+14.f, b.height+12.f});
    bg.setPosition(p + sf::Vector2f(-7.f, -6.f));
    bg.setFillColor(sf::Color(10,12,18,220));
    bg.setOutlineThickness(1.f);
    bg.setOutlineColor(sf::Color(120,140,200,120));

    win.draw(bg);
    win.draw(t);
}

static void drawAlwaysLabels(sf::RenderWindow& win, App& app){
    // Start label
    if(app.start>=0){
        std::string s = "START: " + app.g.nodes[app.start].name;
        drawText(win, app.font, s, app.g.nodes[app.start].pos + sf::Vector2f(12.f, -36.f), 14, sf::Color(190,245,255,255));
    }
    // Destination label
    if(app.dest>=0){
        std::string s = "DEST: " + app.g.nodes[app.dest].name;
        drawText(win, app.font, s, app.g.nodes[app.dest].pos + sf::Vector2f(12.f, -36.f), 14, sf::Color(255,220,190,255));
    }
}

static void drawButton(sf::RenderWindow& win, sf::Font& font, const Button& b){
    sf::RectangleShape r({b.rect.width, b.rect.height});
    r.setPosition({b.rect.left, b.rect.top});
    r.setFillColor(b.hovered ? sf::Color(70,75,95,255) : sf::Color(45,48,65,255));
    r.setOutlineThickness(1.f);
    r.setOutlineColor(sf::Color(120,130,160,150));
    win.draw(r);

    sf::Text t(b.text, font, 13);
    t.setFillColor(sf::Color::White);
    t.setPosition(b.rect.left+10.f, b.rect.top+9.f);
    win.draw(t);
}

static void drawHUD(sf::RenderWindow& win, App& app, const std::vector<Button>& buttons){
    sf::View old=win.getView();
    win.setView(win.getDefaultView());

    sf::RectangleShape panel({460.f, (float)win.getSize().y});
    panel.setFillColor(sf::Color(14,16,22,245));
    win.draw(panel);

    drawText(win, app.font, "National Disaster Evacuation System", {16, 12}, 18, sf::Color::White);
    drawText(win, app.font, "Professional Graph Visualization (2D)", {16, 38}, 13, sf::Color(190,200,220));

    for(const auto& b : buttons) drawButton(win, app.font, b);

    // Wizard box
    if(app.wizard){
        drawText(win, app.font, app.prompt, {16, 260}, 13, sf::Color(255,230,180));

        sf::RectangleShape box({420.f, 32.f});
        box.setPosition(16.f, 285.f);
        box.setFillColor(sf::Color(255,255,255,18));
        box.setOutlineThickness(1.f);
        box.setOutlineColor(sf::Color(160,170,210,140));
        win.draw(box);

        drawText(win, app.font, app.input.value, {26, 292}, 14, sf::Color::White);

        // Suggestions
        if(!app.suggestions.empty()){
            drawText(win, app.font, "Suggestions:", {16, 322}, 12, sf::Color(170,185,210));
            float y=340.f;
            for(size_t i=0;i<app.suggestions.size();i++){
                drawText(win, app.font, "- " + app.suggestions[i], {22, y}, 12, sf::Color(220,230,245));
                y += 18.f;
            }
        }
    }

    // Steps
    drawText(win, app.font, "Route Steps:", {16, 430}, 13, sf::Color(210,220,235));
    int y=452;
    int maxLines=12;
    if(app.hasResult && app.last.found){
        int startLine = std::max(0, app.stepsScroll);
        int endLine = std::min((int)app.last.path.size(), startLine + maxLines);
        for(int i=startLine;i<endLine;i++){
            std::string s = std::to_string(i+1) + ". " + app.g.nodes[app.last.path[i]].name;
            drawText(win, app.font, s, {16.f, (float)y}, 12, sf::Color(230,235,250));
            y += 18;
        }
        drawText(win, app.font, "Scroll steps: Up/Down", {16.f, (float)(y+6)}, 12, sf::Color(160,170,190));
    } else {
        drawText(win, app.font, "(Compute to see steps)", {16.f, (float)y}, 12, sf::Color(160,170,190));
    }

    // Info
    std::ostringstream info;
    info << "Cities: " << app.g.cities.size() << "\n";
    info << "Shelters: " << app.g.shelters.size() << "\n";
    info << "Algorithm: " << algoName(app.algo) << "\n";
    info << "Disaster: " << disasterName(app.disaster) << "\n";
    info << "Secondary roads: " << (app.showSecondary ? "ON" : "OFF") << "\n";
    info << "Auto-hide secondary: " << (app.autoHideSecondary ? "ON" : "OFF") << "\n";
    info << "Voice: " << (app.sp.enabled ? "ON" : "OFF") << "\n";
    info << "Zoom: " << app.zoom << "\n";
    if(app.hasResult){
        info << "\nResult: " << (app.last.found ? "Path Found" : "No Path") << "\n";
        info << "Visited: " << app.last.visited.size() << "\n";
        info << "Cost: " << app.last.cost << "\n";
    }
    drawText(win, app.font, info.str(), {16, 650}, 12, sf::Color(200,210,235));

    drawText(win, app.font, "Status: " + app.status, {16, (float)win.getSize().y - 28.f}, 13, sf::Color(190,235,200));

    win.setView(old);
}

// --------------------------- Wizard helpers ---------------------------
static void wizardPrompt(App& app, int step, const std::string& prompt, const std::string& speak){
    app.wizard=true;
    app.step=step;
    app.prompt=prompt;
    app.input.value.clear();
    app.input.active=true;
    app.suggestions.clear();
    app.status=prompt;
    if(!speak.empty()) app.sp.say(speak);
}

static void beginWizard(App& app){
    app.start=-1;
    app.dest=-1;
    app.destAuto=true;
    app.hasResult=false;
    app.stepsScroll=0;
    wizardPrompt(app, 0,
        "Step 1: Enter START city (or type: restart).",
        "National Disaster Evacuation System. Please enter your start city.");
}

// --------------------------- Main ---------------------------
int main(){
    sf::RenderWindow window(sf::VideoMode(1280,720), "National Disaster Evacuation System (Professional 2D)");
    window.setFramerateLimit(60);

    App app;

#ifdef _WIN32
    if(!app.font.loadFromFile("C:\\Windows\\Fonts\\arial.ttf")){
        std::cerr << "Failed to load Arial.\n";
    }
#else
    app.font.loadFromFile("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf");
#endif

    app.view = sf::View(sf::FloatRect(0,0,1280,720));
    app.input.rect = {16.f, 285.f, 420.f, 32.f};

    buildGraph(app);

    // Buttons
    std::vector<Button> buttons;
    auto addBtn=[&](float x,float y,float w,float h,const std::string& t){
        buttons.push_back(Button{{x,y,w,h}, t, false});
    };

    addBtn(16, 70, 130, 34, "Algo: BFS");
    addBtn(156,70, 130, 34, "Algo: DFS");
    addBtn(296,70, 150, 34, "Algo: Dijkstra");

    addBtn(16, 118, 220, 34, "Toggle Secondary Roads");
    addBtn(246,118, 200, 34, "AutoHide Secondary");

    addBtn(16, 166, 220, 34, "Disaster Cycle");
    addBtn(246,166, 200, 34, "Toggle Voice");

    addBtn(16, 214, 220, 34, "Rebuild Graph");
    addBtn(246,214, 200, 34, "Restart Wizard");

    beginWizard(app);

    while(window.isOpen()){
        sf::Event ev;
        while(window.pollEvent(ev)){
            if(ev.type==sf::Event::Closed) window.close();

            // Zoom
            if(ev.type==sf::Event::MouseWheelScrolled){
                float factor = (ev.mouseWheelScroll.delta > 0) ? 0.9f : 1.1f;
                app.zoom = clampf(app.zoom*factor, 0.55f, 2.9f);
                app.view.setSize(window.getDefaultView().getSize()*app.zoom);
            }

            // Text input (wizard only)
            if(ev.type==sf::Event::TextEntered && app.wizard && app.input.active){
                if(ev.text.unicode==13){
                    // Enter
                    std::string s = trim(app.input.value);
                    std::string sl = toLower(s);

                    if(sl=="restart"){
                        beginWizard(app);
                        continue;
                    }
                    if(sl=="back"){
                        // go one step back
                        if(app.step>0) app.step--;
                        if(app.step==0) wizardPrompt(app,0,"Step 1: Enter START city (or restart).","Please enter your start city.");
                        else if(app.step==1) wizardPrompt(app,1,"Step 2: Enter DESTINATION city OR type AUTO (free nearest shelter).","Enter destination city or type auto.");
                        else if(app.step==2) wizardPrompt(app,2,"Step 3: Disaster (1 none / 2 flood / 3 earthquake / 4 fire / 5 cyclone) or words.","Select disaster type.");
                        else if(app.step==3) wizardPrompt(app,3,"Step 4: Algorithm (1 BFS / 2 DFS / 3 Dijkstra) or words.","Select algorithm.");
                        continue;
                    }

                    // Step logic
                    if(app.step==0){
                        app.suggestions.clear();
                        int idx = resolveCitySmart(app.g, s, &app.suggestions);
                        if(idx < 0){
                            app.status="City not found. Try again (see suggestions).";
                            app.sp.say("City not found. Please try again.");
                        } else {
                            app.start = idx;
                            app.view.setCenter(app.g.nodes[idx].pos);
                            app.status="Start set: " + app.g.nodes[idx].name;
                            wizardPrompt(app, 1,
                                "Step 2: Enter DESTINATION city OR type AUTO (free nearest shelter).",
                                "Enter destination city, or type auto for nearest shelter.");
                        }
                    }
                    else if(app.step==1){
                        app.suggestions.clear();
                        if(toLower(s)=="auto"){
                            app.destAuto=true;
                            app.dest=-1;
                            app.status="Destination set to AUTO nearest shelter.";
                            wizardPrompt(app, 2,
                                "Step 3: Disaster (1 none / 2 flood / 3 earthquake / 4 fire / 5 cyclone) or words.",
                                "Select disaster type.");
                        } else {
                            int idx = resolveCitySmart(app.g, s, &app.suggestions);
                            if(idx < 0){
                                app.status="Destination city not found. Try again.";
                                app.sp.say("Destination city not found.");
                            } else {
                                app.destAuto=false;
                                app.dest=idx; // manual city destination
                                app.view.setCenter(app.g.nodes[idx].pos);
                                app.status="Destination set: " + app.g.nodes[idx].name;
                                wizardPrompt(app, 2,
                                    "Step 3: Disaster (1 none / 2 flood / 3 earthquake / 4 fire / 5 cyclone) or words.",
                                    "Select disaster type.");
                            }
                        }
                    }
                    else if(app.step==2){
                        Disaster d;
                        if(!parseDisaster(s, d)){
                            app.status="Invalid disaster. Use number 1..5 or words like flood.";
                            app.sp.say("Invalid disaster selection.");
                        } else {
                            app.disaster=d;
                            app.status=std::string("Disaster set: ") + disasterName(d);
                            wizardPrompt(app, 3,
                                "Step 4: Algorithm (1 BFS / 2 DFS / 3 Dijkstra) or words.",
                                "Select algorithm.");
                        }
                    }
                    else if(app.step==3){
                        Algo a;
                        if(!parseAlgo(s, a)){
                            app.status="Invalid algorithm. Use 1..3 or words bfs dfs dijkstra.";
                            app.sp.say("Invalid algorithm selection.");
                        } else {
                            app.algo=a;
                            app.wizard=false;
                            app.input.active=false;
                            app.status="Computing route...";
                            app.sp.say("Computing route now.");
                            compute(app);
                        }
                    }
                } else {
                    app.input.append(ev.text.unicode);
                }
            }

            // Mouse press
            if(ev.type==sf::Event::MouseButtonPressed){
                sf::Vector2i mp = sf::Mouse::getPosition(window);
                sf::Vector2f mps((float)mp.x,(float)mp.y);

                bool clickedUI=false;

                // Buttons
                for(auto& b : buttons){
                    if(b.hit(mps)){
                        clickedUI=true;

                        if(b.text=="Algo: BFS"){ app.algo=Algo::BFS; app.status="Algorithm: BFS"; }
                        else if(b.text=="Algo: DFS"){ app.algo=Algo::DFS; app.status="Algorithm: DFS"; }
                        else if(b.text=="Algo: Dijkstra"){ app.algo=Algo::Dijkstra; app.status="Algorithm: Dijkstra"; }

                        else if(b.text=="Toggle Secondary Roads"){
                            app.showSecondary = !app.showSecondary;
                            app.status = std::string("Secondary roads: ") + (app.showSecondary?"ON":"OFF");
                        }
                        else if(b.text=="AutoHide Secondary"){
                            app.autoHideSecondary = !app.autoHideSecondary;
                            app.status = std::string("Auto-hide secondary: ") + (app.autoHideSecondary?"ON":"OFF");
                        }
                        else if(b.text=="Disaster Cycle"){
                            if(app.disaster==Disaster::None) app.disaster=Disaster::Flood;
                            else if(app.disaster==Disaster::Flood) app.disaster=Disaster::Earthquake;
                            else if(app.disaster==Disaster::Earthquake) app.disaster=Disaster::Fire;
                            else if(app.disaster==Disaster::Fire) app.disaster=Disaster::Cyclone;
                            else app.disaster=Disaster::None;
                            app.status = std::string("Disaster: ") + disasterName(app.disaster);
                            if(!app.wizard && app.start>=0) compute(app);
                        }
                        else if(b.text=="Toggle Voice"){
                            app.sp.enabled=!app.sp.enabled;
                            app.status = std::string("Voice: ") + (app.sp.enabled?"ON":"OFF");
                            if(app.sp.enabled) app.sp.say("Voice enabled.");
                        }
                        else if(b.text=="Rebuild Graph"){
                            buildGraph(app);
                            beginWizard(app);
                        }
                        else if(b.text=="Restart Wizard"){
                            beginWizard(app);
                        }

                        // recompute if already running and not wizard
                        if(!app.wizard && app.start>=0 && app.hasResult){
                            // keep stable: only recompute on relevant changes
                        }
                    }
                }

                // Right click pan
                if(!clickedUI && ev.mouseButton.button==sf::Mouse::Right){
                    app.panning=true;
                    app.panStartMouse=mp;
                    app.panStartWorld=window.mapPixelToCoords(mp, app.view);
                }

                // Left click set new start (professional interaction)
                if(!clickedUI && ev.mouseButton.button==sf::Mouse::Left && !app.wizard){
                    sf::Vector2f wpos = window.mapPixelToCoords(mp, app.view);
                    int idx = pickNode(app.g, wpos, 14.f);
                    if(idx>=0 && app.g.nodes[idx].type==NodeType::City){
                        app.start=idx;
                        app.status="Start set by click: " + app.g.nodes[idx].name;
                        compute(app);
                    }
                }
            }

            if(ev.type==sf::Event::MouseButtonReleased){
                if(ev.mouseButton.button==sf::Mouse::Right) app.panning=false;
            }

            if(ev.type==sf::Event::KeyPressed){
                if(ev.key.code==sf::Keyboard::Up) app.stepsScroll = std::max(0, app.stepsScroll-1);
                if(ev.key.code==sf::Keyboard::Down) app.stepsScroll = app.stepsScroll+1;

                if(ev.key.code==sf::Keyboard::H){
                    app.sp.say("Help. Type back to go to previous step, restart to restart. Destination can be auto nearest shelter or manual city.");
                    app.status="Help spoken.";
                }
            }
        }

        // Hover
        {
            sf::Vector2i mp = sf::Mouse::getPosition(window);
            sf::Vector2f wpos = window.mapPixelToCoords(mp, app.view);
            app.hovered = pickNode(app.g, wpos, 12.f);
        }

        // Pan
        if(app.panning){
            sf::Vector2i mp = sf::Mouse::getPosition(window);
            sf::Vector2f now = window.mapPixelToCoords(mp, app.view);
            sf::Vector2f delta = app.panStartWorld - now;
            app.view.move(delta);
        }

        // Button hover
        {
            sf::Vector2i mp = sf::Mouse::getPosition(window);
            sf::Vector2f mps((float)mp.x,(float)mp.y);
            for(auto& b : buttons) b.hovered = b.hit(mps);
        }

        // Visited animation
        if(app.hasResult && app.showVisited){
            float t = app.animClock.getElapsedTime().asSeconds();
            if(t > 0.02f){
                app.animClock.restart();
                if(app.visitedShown < app.last.visited.size()) app.visitedShown += 4;
            }
        }

        // Draw
        window.clear(sf::Color(8,10,16));
        window.setView(app.view);

        drawBackground(window);
        drawEdges(window, app);
        drawVisited(window, app);
        drawPath(window, app);
        drawNodes(window, app);
        drawAlwaysLabels(window, app);
        drawHoverLabel(window, app);

        drawHUD(window, app, buttons);

        window.display();
    }

    return 0;
}
