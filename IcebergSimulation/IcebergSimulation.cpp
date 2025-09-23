#include <SFML/Graphics.hpp>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iostream>
#include <limits>

// Физические константы
static const double DAMP_ANG_BASE = 80.0;      
static const double DAMP_ANG_HEAVY = 200.0;    
static const double K_ALIGN_ANGLE = 120.0;     
static const double DAMP_X_BASE = 20.0;        
static const double DAMP_Y_BASE = 30.0;        
static const double DAMP_X_HEAVY = 35.0;       
static const double DAMP_Y_HEAVY = 50.0;       
static const double GRAVITY_MULTIPLIER = 2.5;  
static const double MAX_LIN_SPEED = 0.8;       
static const double MAX_ANG_SPEED = 0.1;       
static const double BOUNDARY_SOFTNESS = 0.3;   
static const double BOUNDARY_FORCE = 50.0;     
static const double SINKING_ACCELERATION = 1.8; 
static const double PI = 3.14159265358979323846;

struct Vec2 {
    double x, y;
    Vec2() : x(0), y(0) {}
    Vec2(double X, double Y) : x(X), y(Y) {}
    Vec2 operator+(const Vec2& o) const { return Vec2(x + o.x, y + o.y); }
    Vec2 operator-(const Vec2& o) const { return Vec2(x - o.x, y - o.y); }
    Vec2 operator*(double s) const { return Vec2(x * s, y * s); }
};

template <typename T>
static inline T clampVal(const T& v, const T& lo, const T& hi) {
    return (v < lo) ? lo : (v > hi ? hi : v);
}


// Нормализация угла в диапазон [-PI, PI]
static inline double wrapAngle(double a) {
    while (a > PI) a -= 2.0 * PI;
    while (a < -PI) a += 2.0 * PI;
    return a;
}

// Свойства айсберга: площадь, центр масс, момент инерции, масса
struct PolyProps {
    double area;
    Vec2 center;
    double I;
    double mass;
    std::vector<Vec2> points_ccw;  
    PolyProps() : area(0), center(0, 0), I(1), mass(1) {}
};

// Состояние : позиция, скорость, угол, угловая скорость
struct State {
    double x, y;
    double vx, vy;
    double angle;
    double angVel;
    State() : x(0), y(0), vx(0), vy(0), angle(0), angVel(0) {}
};

// Параметры: границы, уровень воды, плотности, гравитация
struct World {
    double xMin, xMax, yMin, yMax;
    double waterLevel;
    double densityWater;
    double densityIce;
    double g;
    World() :
        xMin(-10), xMax(10), yMin(-12), yMax(8),
        waterLevel(0), densityWater(1025.0), densityIce(917.0), g(9.81 * GRAVITY_MULTIPLIER) {}
};

// Вычисление площади айсберга
static double signedArea(const std::vector<Vec2>& pts) {
    size_t n = pts.size();
    if (n < 3) return 0.0;
    double s = 0.0;
    for (size_t i = 0; i < n; ++i) {
        const Vec2& a = pts[i];
        const Vec2& b = pts[(i + 1) % n];
        s += a.x * b.y - b.x * a.y;
    }
    return 0.5 * s;
}

// Вычисление центра масс айсберга
static Vec2 centroid(const std::vector<Vec2>& pts, double signedA) {
    size_t n = pts.size();
    double cx = 0.0, cy = 0.0;
    for (size_t i = 0; i < n; ++i) {
        const Vec2& p = pts[i];
        const Vec2& q = pts[(i + 1) % n];
        double cr = p.x * q.y - q.x * p.y;
        cx += (p.x + q.x) * cr;
        cy += (p.y + q.y) * cr;
    }
    double factor = 1.0 / (6.0 * signedA);
    return Vec2(cx * factor, cy * factor);
}

// Вычисление момента инерции
static double secondMomentSum_IxxPlusIyy_aboutOrigin(const std::vector<Vec2>& pts) {
    size_t n = pts.size();
    double Ixx = 0.0, Iyy = 0.0;
    for (size_t i = 0; i < n; ++i) {
        const Vec2& p = pts[i];
        const Vec2& q = pts[(i + 1) % n];
        double cr = p.x * q.y - q.x * p.y;
        Ixx += cr * (p.y * p.y + p.y * q.y + q.y * q.y);
        Iyy += cr * (p.x * p.x + p.x * q.x + q.x * q.x);
    }
    Ixx /= 12.0;
    Iyy /= 12.0;
    return Ixx + Iyy;
}

static void ensureCCW(std::vector<Vec2>& pts) {
    if (signedArea(pts) < 0) std::reverse(pts.begin(), pts.end());
}

// Отсечение айсберга ниже заданного уровня Y
static std::vector<Vec2> clipBelowY(const std::vector<Vec2>& verts, double yLevel) {
    std::vector<Vec2> out;
    size_t n = verts.size();
    if (n == 0) return out;
    Vec2 prev = verts[n - 1];
    bool prevInside = (prev.y <= yLevel);
    for (size_t i = 0; i < n; ++i) {
        Vec2 curr = verts[i];
        bool currInside = (curr.y <= yLevel);
        if (currInside) {
            if (!prevInside) {
                double dy = curr.y - prev.y;
                if (std::abs(dy) > 1e-12) {
                    double t = (yLevel - prev.y) / dy;
                    double ix = prev.x + t * (curr.x - prev.x);
                    out.push_back(Vec2(ix, yLevel));
                }
            }
            out.push_back(curr);
        }
        else if (prevInside) {
            double dy = curr.y - prev.y;
            if (std::abs(dy) > 1e-12) {
                double t = (yLevel - prev.y) / dy;
                double ix = prev.x + t * (curr.x - prev.x);
                out.push_back(Vec2(ix, yLevel));
            }
        }
        prev = curr;
        prevInside = currInside;
    }
    return out;
}

// Вычисление площади и центра масс погруженной части
static std::pair<double, Vec2> submergedAreaAndCentroid(const std::vector<Vec2>& verts, double waterLevel) {
    std::vector<Vec2> clipped = clipBelowY(verts, waterLevel);
    if (clipped.size() < 3) return std::make_pair(0.0, Vec2(0, 0));
    ensureCCW(clipped);
    double sA = signedArea(clipped);
    double A = std::abs(sA);
    if (A < 1e-9) return std::make_pair(0.0, Vec2(0, 0));
    Vec2 C = centroid(clipped, sA);
    return std::make_pair(A, C);
}

// Класс для преобразования координат
struct Mapper {
    World w;
    int width, height;
    Mapper(const World& world, int W, int H) : w(world), width(W), height(H) {}
    float mapX(double x) const {
        return static_cast<float>((x - w.xMin) / (w.xMax - w.xMin) * width);
    }
    float mapY(double y) const {
        return static_cast<float>(height - (y - w.yMin) / (w.yMax - w.yMin) * height);
    }
    sf::Vector2f mapPt(const Vec2& p) const { return sf::Vector2f(mapX(p.x), mapY(p.y)); }
};

// Вычисление физических свойств айсберга
static PolyProps calcPolyProps(const std::vector<Vec2>& pts, const World& world) {
    PolyProps r;
    if (pts.size() < 3) return r;
    std::vector<Vec2> P = pts;
    ensureCCW(P);
    double sA = signedArea(P);
    double A = sA;
    if (A < 1e-6) A = 1e-6;
    Vec2 C = centroid(P, sA);

    double I_area = secondMomentSum_IxxPlusIyy_aboutOrigin(P);
    double I_cent_area = I_area - A * (C.x * C.x + C.y * C.y);
    double density = world.densityIce;
    double I = density * (I_cent_area > 1e-6 ? I_cent_area : 1e-6);
    double mass = density * A;

    r.area = A;
    r.center = C;
    r.I = I;
    r.mass = mass;
    r.points_ccw = P;
    return r;
}

// Поворот точек айсберга на заданный угол
static std::vector<Vec2> rotatedPoints(const PolyProps& poly, double angle) {
    double c = std::cos(angle), s = std::sin(angle);
    std::vector<Vec2> out; out.reserve(poly.points_ccw.size());
    for (size_t i = 0; i < poly.points_ccw.size(); ++i) {
        Vec2 p = poly.points_ccw[i];
        Vec2 cp = p - poly.center;
        Vec2 rp(cp.x * c - cp.y * s, cp.x * s + cp.y * c);
        out.push_back(rp);
    }
    return out;
}

// Преобразование вершин айсберга
static std::vector<Vec2> transformedVertices(const PolyProps& poly, const State& st) {
    std::vector<Vec2> rp = rotatedPoints(poly, st.angle);
    for (size_t i = 0; i < rp.size(); ++i) {
        rp[i].x += st.x;
        rp[i].y += st.y;
    }
    return rp;
}

// Структура для хранения равновесного состояния
struct Equilibrium { double angle; double y; Equilibrium() : angle(0), y(0) {} };

// Поиск равновесного положения и угла
static Equilibrium findEquilibrium(const PolyProps& poly, const World& world) {
    struct GetXOffset {
        const PolyProps& poly;
        const World& world;
        std::pair<double, double> operator()(double angle) const {
            std::vector<Vec2> rp = rotatedPoints(poly, angle);
            double lowY = -20.0, highY = 20.0, midY = 0.0;
            const double targetSubmerged = poly.area * (world.densityIce / world.densityWater);
            for (int it = 0; it < 50; ++it) {
                midY = 0.5 * (lowY + highY);
                std::vector<Vec2> translated = rp;
                for (size_t i = 0; i < translated.size(); ++i) translated[i].y += midY;
                std::pair<double, Vec2> res = submergedAreaAndCentroid(translated, world.waterLevel);
                double A = res.first;
                if (A < targetSubmerged) highY = midY;
                else lowY = midY;
            }
            std::vector<Vec2> translated = rp;
            for (size_t i = 0; i < translated.size(); ++i) translated[i].y += midY;
            std::pair<double, Vec2> res = submergedAreaAndCentroid(translated, world.waterLevel);
            Vec2 C = res.second;
            Vec2 com(0.0, midY);
            double xoff = C.x - com.x;
            return std::make_pair(xoff, midY);
        }
    } getXOffset{ poly, world };

    const int steps = 36;
    std::vector<double> angles(steps);
    std::vector<double> offsets(steps);
    for (int i = 0; i < steps; ++i) {
        double a = (2.0 * PI) * i / steps;
        angles[i] = a;
        std::pair<double, double> r = getXOffset(a);
        offsets[i] = r.first;
    }

    std::vector<double> candidates;
    for (int i = 0; i < steps; ++i) {
        double o1 = offsets[i];
        double o2 = offsets[(i + 1) % steps];
        if (o1 == 0.0) candidates.push_back(angles[i]);
        if (o1 * o2 < 0.0) {
            double a1 = angles[i], a2 = angles[(i + 1) % steps];
            double frac = -o1 / (o2 - o1);
            candidates.push_back(a1 + frac * (a2 - a1));
        }
    }
    if (candidates.empty()) {
        std::pair<double, double> r = getXOffset(0.0);
        Equilibrium eq; eq.angle = 0.0; eq.y = r.second;
        return eq;
    }
    double eqAngle = candidates.front();
    std::pair<double, double> rr = getXOffset(eqAngle);
    Equilibrium eq; eq.angle = eqAngle; eq.y = rr.second;
    return eq;
}

// Проверка близости к равновесию
static bool isNearEquilibrium(const State& st, double targetAngle, double threshold = 0.1) {
    double angleError = std::abs(wrapAngle(st.angle - targetAngle));
    return angleError < (1.0 * PI / 180.0) &&
        std::abs(st.angVel) < 0.005 &&
        std::abs(st.vx) < 0.005 &&
        std::abs(st.vy) < 0.005;
}

// Обработка сил от границ мира
static Vec2 handleBoundaryForces(const State& st, const World& world, const PolyProps& poly) {
    Vec2 boundaryForce(0.0, 0.0);

    std::vector<Vec2> verts = transformedVertices(poly, st);

    double minX = std::numeric_limits<double>::max();
    double maxX = std::numeric_limits<double>::lowest();
    double minY = std::numeric_limits<double>::max();
    double maxY = std::numeric_limits<double>::lowest();

    for (const auto& v : verts) {
        minX = std::min(minX, v.x);
        maxX = std::max(maxX, v.x);
        minY = std::min(minY, v.y);
        maxY = std::max(maxY, v.y);
    }

    if (minX < world.xMin + BOUNDARY_SOFTNESS) {
        double penetration = (world.xMin + BOUNDARY_SOFTNESS) - minX;
        boundaryForce.x += penetration * BOUNDARY_FORCE;
    }
    if (maxX > world.xMax - BOUNDARY_SOFTNESS) {
        double penetration = maxX - (world.xMax - BOUNDARY_SOFTNESS);
        boundaryForce.x -= penetration * BOUNDARY_FORCE;
    }
    if (minY < world.yMin + BOUNDARY_SOFTNESS) {
        double penetration = (world.yMin + BOUNDARY_SOFTNESS) - minY;
        boundaryForce.y += penetration * BOUNDARY_FORCE;
    }
    if (maxY > world.yMax - BOUNDARY_SOFTNESS) {
        double penetration = maxY - (world.yMax - BOUNDARY_SOFTNESS);
        boundaryForce.y -= penetration * BOUNDARY_FORCE;
    }

    return boundaryForce;
}

// Вычисление центра рисования для айсберга
static Vec2 computeDrawingCenter(const std::vector<Vec2>& points) {
    if (points.empty()) return Vec2(0, 0);

    double sumX = 0.0, sumY = 0.0;
    for (const auto& p : points) {
        sumX += p.x;
        sumY += p.y;
    }
    return Vec2(sumX / points.size(), sumY / points.size());
}

// Вычисление суммарных сил и момента
static std::pair<Vec2, double> forcesAndTorque(const PolyProps& poly,
    const World& world,
    const State& st,
    double targetAngle)
{
    std::vector<Vec2> verts = transformedVertices(poly, st);
    std::pair<double, Vec2> res = submergedAreaAndCentroid(verts, world.waterLevel);
    double submergedArea = res.first;
    Vec2 buoyancyCenter = res.second;

    Vec2 centerOfMass(st.x, st.y);

    double buoyancyForce = world.densityWater * submergedArea * world.g;
    double gravityForce = poly.mass * world.g;
    double netVerticalForce = buoyancyForce - gravityForce;

    if (netVerticalForce < 0) {
        netVerticalForce *= SINKING_ACCELERATION;
    }

    Vec2 netForce(0.0, netVerticalForce);

    double dampX = DAMP_X_HEAVY;
    double dampY = DAMP_Y_HEAVY;
    netForce.x += -st.vx * dampX;
    netForce.y += -st.vy * dampY;

    Vec2 boundaryForce = handleBoundaryForces(st, world, poly);
    netForce = netForce + boundaryForce;

    double torque = (buoyancyCenter.x - centerOfMass.x) * buoyancyForce;

    double angleError = wrapAngle(st.angle - targetAngle);
    double alignmentStrength = K_ALIGN_ANGLE;
    torque += -alignmentStrength * angleError;

    double angDamp = DAMP_ANG_HEAVY;
    if (isNearEquilibrium(st, targetAngle)) {
        angDamp *= 8.0;
    }
    torque += -st.angVel * angDamp;

    return std::make_pair(netForce, torque);
}

// Вычисление производных
static void derivatives(const PolyProps& poly, const World& world, const State& st,
    double targetAngle, Vec2& dPos, Vec2& dVel, double& dAngle, double& dAngVel)
{
    std::pair<Vec2, double> FT = forcesAndTorque(poly, world, st, targetAngle);
    Vec2 F = FT.first;
    double M = FT.second;
    dPos = Vec2(st.vx, st.vy);
    dVel = Vec2(F.x / poly.mass, F.y / poly.mass);
    dAngle = st.angVel;
    dAngVel = M / poly.I;
}

// Рунге-Кутта
static void rk4Step(const PolyProps& poly, const World& world, State& st,
    double dt, double targetAngle) {
    Vec2 k1_pos, k1_vel, k2_pos, k2_vel, k3_pos, k3_vel, k4_pos, k4_vel;
    double k1_ang, k1_angVel, k2_ang, k2_angVel, k3_ang, k3_angVel, k4_ang, k4_angVel;

    derivatives(poly, world, st, targetAngle, k1_pos, k1_vel, k1_ang, k1_angVel);

    State s2 = st;
    s2.x += 0.5 * dt * k1_pos.x; s2.y += 0.5 * dt * k1_pos.y;
    s2.vx += 0.5 * dt * k1_vel.x; s2.vy += 0.5 * dt * k1_vel.y;
    s2.angle += 0.5 * dt * k1_ang; s2.angVel += 0.5 * dt * k1_angVel;
    derivatives(poly, world, s2, targetAngle, k2_pos, k2_vel, k2_ang, k2_angVel);

    State s3 = st;
    s3.x += 0.5 * dt * k2_pos.x; s3.y += 0.5 * dt * k2_pos.y;
    s3.vx += 0.5 * dt * k2_vel.x; s3.vy += 0.5 * dt * k2_vel.y;
    s3.angle += 0.5 * dt * k2_ang; s3.angVel += 0.5 * dt * k2_angVel;
    derivatives(poly, world, s3, targetAngle, k3_pos, k3_vel, k3_ang, k3_angVel);

    State s4 = st;
    s4.x += dt * k3_pos.x; s4.y += dt * k3_pos.y;
    s4.vx += dt * k3_vel.x; s4.vy += dt * k3_vel.y;
    s4.angle += dt * k3_ang; s4.angVel += dt * k3_angVel;
    derivatives(poly, world, s4, targetAngle, k4_pos, k4_vel, k4_ang, k4_angVel);

    st.x += (dt / 6.0) * (k1_pos.x + 2 * k2_pos.x + 2 * k3_pos.x + k4_pos.x);
    st.y += (dt / 6.0) * (k1_pos.y + 2 * k2_pos.y + 2 * k3_pos.y + k4_pos.y);
    st.vx += (dt / 6.0) * (k1_vel.x + 2 * k2_vel.x + 2 * k3_vel.x + k4_vel.x);
    st.vy += (dt / 6.0) * (k1_vel.y + 2 * k2_vel.y + 2 * k3_vel.y + k4_vel.y);
    st.angle += (dt / 6.0) * (k1_ang + 2 * k2_ang + 2 * k3_ang + k4_ang);
    st.angVel += (dt / 6.0) * (k1_angVel + 2 * k2_angVel + 2 * k3_angVel + k4_angVel);

    st.x = clampVal(st.x, world.xMin + 0.3, world.xMax - 0.3);
    st.y = clampVal(st.y, world.yMin + 0.3, world.yMax - 0.3);

    double speed = std::hypot(st.vx, st.vy);
    if (speed > MAX_LIN_SPEED) {
        double f = MAX_LIN_SPEED / speed;
        st.vx *= f; st.vy *= f;
    }
    if (std::abs(st.angVel) > MAX_ANG_SPEED) {
        st.angVel = (st.angVel > 0 ? 1 : -1) * MAX_ANG_SPEED;
    }
}

// Проверка достижения равновесия
static bool isEquilibrium(const State& st, double targetAngle) {
    return std::abs(st.vx) < 0.0001 && std::abs(st.vy) < 0.0001 &&
        std::abs(st.angVel) < 0.0001 &&
        std::abs(wrapAngle(st.angle - targetAngle)) < (0.1 * PI / 180.0);
}

static void drawPolyline(sf::RenderWindow& win, const Mapper& map, const std::vector<Vec2>& pts, sf::Color col, float thickness = 2.f, bool closed = false) {
    if (pts.size() < 2) return;
    sf::VertexArray va(sf::LineStrip, pts.size() + (closed ? 1 : 0));
    for (size_t i = 0; i < pts.size(); ++i) {
        va[i].position = map.mapPt(pts[i]);
        va[i].color = col;
    }
    if (closed) {
        va[pts.size()].position = map.mapPt(pts[0]);
        va[pts.size()].color = col;
    }
    win.draw(va);
}

static void drawFilledPolygon(sf::RenderWindow& win, const Mapper& map, const std::vector<Vec2>& pts, sf::Color col) {
    if (pts.size() < 3) return;
    sf::ConvexShape poly;
    poly.setPointCount(static_cast<unsigned int>(pts.size()));
    for (size_t i = 0; i < pts.size(); ++i) poly.setPoint(static_cast<unsigned int>(i), map.mapPt(pts[i]));
    poly.setFillColor(col);
    win.draw(poly);
}

int main() {
    World world;
    Mapper mapper(world, 1200, 800);
    sf::RenderWindow window(sf::VideoMode(mapper.width, mapper.height), "Iceberg Simulation - FAST SINKING with ORIGINAL STABILIZATION");
    window.setFramerateLimit(60);

    std::vector<Vec2> drawnPoints;  
    bool isDrawing = false;         
    bool shapeReady = false;        
    bool simRunning = false;        

    PolyProps iceberg;  
    State st;           
    double targetAngle = 0.0;  
    double dt = 1.0 / 60.0;    

    double lastX = 0, lastY = 0;  

    struct MouseToWorld {
        const World& world; const Mapper& mapper; const sf::RenderWindow& window;
        Vec2 operator()() const {
            sf::Vector2i m = sf::Mouse::getPosition(window);
            double x = world.xMin + (double)m.x / mapper.width * (world.xMax - world.xMin);
            double y = world.yMin + (1.0 - (double)m.y / mapper.height) * (world.yMax - world.yMin);
            return Vec2(x, y);
        }
    } worldFromMouse{ world, mapper, window };

    auto startSimulation = [&]() {
        if (!shapeReady) return;
        iceberg = calcPolyProps(drawnPoints, world);
        Equilibrium eq = findEquilibrium(iceberg, world);

        Vec2 drawingCenter = computeDrawingCenter(drawnPoints);

        st = State();
        st.x = drawingCenter.x;
        st.y = drawingCenter.y - 3.0;

        st.vx = 0.01;
        st.vy = 0.02;
        st.angle = 0.01;
        st.angVel = 0.005;

        targetAngle = eq.angle;

        simRunning = true;

        std::cout << "Simulation started with FAST SINKING mode.\n";
        std::cout << "Initial position: (" << st.x << ", " << st.y << ")\n";
        std::cout << "Target equilibrium angle: " << (targetAngle * 180.0 / PI) << " deg\n";
        std::cout << "Target equilibrium height: " << eq.y << "\n";
        std::cout << "Enhanced gravity: " << world.g << " m/s²\n";
        std::cout << "Sinking acceleration: " << SINKING_ACCELERATION << "x\n";
        std::cout << "Using ORIGINAL stabilization parameters\n";
        };

    double accumulator = 0.0;
    sf::Clock clock;

    std::cout << "FAST SINKING with ORIGINAL STABILIZATION\n";
    std::cout << "Controls:\n"
        << " - Draw with LMB, press Enter to start\n"
        << " - Fast sinking with enhanced gravity\n"
        << " - Original stabilization behavior\n"
        << " - Iceberg falls from higher position\n";

    while (window.isOpen()) {
        sf::Event ev;
        while (window.pollEvent(ev)) {
            if (ev.type == sf::Event::Closed) window.close();

            if (!simRunning) {
                if (ev.type == sf::Event::MouseButtonPressed && ev.mouseButton.button == sf::Mouse::Left) {
                    drawnPoints.clear();
                    isDrawing = true;
                    shapeReady = false;
                    Vec2 w = worldFromMouse();
                    drawnPoints.push_back(w);
                    lastX = w.x; lastY = w.y;
                }
                else if (ev.type == sf::Event::MouseButtonReleased && ev.mouseButton.button == sf::Mouse::Left) {
                    isDrawing = false;
                    if (drawnPoints.size() >= 3) {
                        shapeReady = true;
                    }
                }
                else if (ev.type == sf::Event::MouseMoved && isDrawing) {
                    Vec2 w = worldFromMouse();
                    double dx = w.x - lastX, dy = w.y - lastY;
                    if (std::hypot(dx, dy) > 0.1) {
                        drawnPoints.push_back(w);
                        lastX = w.x; lastY = w.y;
                    }
                }
                if (ev.type == sf::Event::KeyPressed && ev.key.code == sf::Keyboard::Enter) {
                    if (shapeReady) startSimulation();
                }
            }
        }

        double frame = clock.restart().asSeconds();
        accumulator += frame;
        if (simRunning) {
            while (accumulator >= dt) {
                rk4Step(iceberg, world, st, dt, targetAngle);
                if (isEquilibrium(st, targetAngle)) {
                    simRunning = false;
                    std::cout << "Equilibrium reached! Stabilization complete.\n";
                }
                accumulator -= dt;
            }
        }
        else {
            accumulator = 0.0;
        }

        window.clear(sf::Color(240, 240, 240));

        std::vector<Vec2> waterPoly;
        waterPoly.push_back(Vec2(world.xMin, world.yMin));
        waterPoly.push_back(Vec2(world.xMax, world.yMin));
        waterPoly.push_back(Vec2(world.xMax, world.waterLevel));
        waterPoly.push_back(Vec2(world.xMin, world.waterLevel));
        drawFilledPolygon(window, mapper, waterPoly, sf::Color(173, 216, 230, 160));

        std::vector<Vec2> horizon;
        horizon.push_back(Vec2(world.xMin, world.waterLevel));
        horizon.push_back(Vec2(world.xMax, world.waterLevel));
        drawPolyline(window, mapper, horizon, sf::Color(50, 100, 255, 255), 2.f, false);

        if (!simRunning) {
            if (!drawnPoints.empty()) {
                drawPolyline(window, mapper, drawnPoints, sf::Color::Red, 2.f, false);
                if (shapeReady) {
                    std::vector<Vec2> tmp = drawnPoints; ensureCCW(tmp);
                    drawFilledPolygon(window, mapper, tmp, sf::Color(255, 255, 255, 230));
                    drawPolyline(window, mapper, tmp, sf::Color(10, 10, 120, 200), 2.f, true);

                    Vec2 center = computeDrawingCenter(drawnPoints);
                    sf::CircleShape centerMarker(4);
                    centerMarker.setFillColor(sf::Color::Green);
                    centerMarker.setPosition(mapper.mapPt(center) - sf::Vector2f(4, 4));
                    window.draw(centerMarker);
                }
            }
        }
        else {
            std::vector<Vec2> verts = transformedVertices(iceberg, st);
            std::vector<Vec2> closed = verts; ensureCCW(closed);
            drawFilledPolygon(window, mapper, closed, sf::Color(255, 255, 255, 230));
            drawPolyline(window, mapper, closed, sf::Color(10, 10, 120, 255), 2.f, true);

            std::vector<Vec2> submerged = clipBelowY(verts, world.waterLevel);
            if (submerged.size() >= 3) {
                ensureCCW(submerged);
                drawFilledPolygon(window, mapper, submerged, sf::Color(0, 0, 139, 100));
            }

            if (isNearEquilibrium(st, targetAngle)) {
                sf::CircleShape stabilityIndicator(6);
                stabilityIndicator.setFillColor(sf::Color::Green);
                stabilityIndicator.setPosition(mapper.mapPt(Vec2(st.x, st.y)) - sf::Vector2f(6, 6));
                window.draw(stabilityIndicator);
            }

            sf::CircleShape comMarker(3);
            comMarker.setFillColor(sf::Color::Red);
            comMarker.setPosition(mapper.mapPt(Vec2(st.x, st.y)) - sf::Vector2f(3, 3));
            window.draw(comMarker);

            std::pair<double, Vec2> submergedInfo = submergedAreaAndCentroid(verts, world.waterLevel);
            if (submergedInfo.first > 0.01) {
                sf::CircleShape buoyMarker(3);
                buoyMarker.setFillColor(sf::Color::Blue);
                buoyMarker.setPosition(mapper.mapPt(submergedInfo.second) - sf::Vector2f(3, 3));
                window.draw(buoyMarker);
            }
        }

        window.display();
    }
    return 0;
}
