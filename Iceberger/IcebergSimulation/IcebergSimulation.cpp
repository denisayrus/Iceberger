// Красная линия для рисования, Enter — старт симуляции, R — сброс.
// Симуляция: падение -> погружение -> всплытие -> стабилизация.
// В симуляции: красная точка = центр масс, синяя точка = центр выталкивания.
// Сравнение методов: RK6 (основной), RK4 и Ралстон (для сравнения точности).
// Погрешности выводятся в консоль каждые 100 шагов в процентах.

#include <SFML/Graphics.hpp>
#include <vector>
#include <cmath>
#include <algorithm>
#include <random>
#include <limits>
#include <iostream>
#include <iomanip>
#include <sstream>

static const double PI = 3.14159265358979323846;

// ----- параметры физики -----
static const double GRAVITY_MULTIPLIER = 3.0;   // Множитель ускорения свободного падения
static const double DAMP_X = 20.0;              // Коэффициент демпфирования по горизонтали
static const double DAMP_Y = 30.0;              // Коэффициент демпфирования по вертикали
static const double DAMP_ANG = 60.0;            // Коэффициент демпфирования вращения
static const double MULT_DAMP_STEP = 0.98;      // Множитель дополнительного затухания на каждом шаге
static const double SINK_ACCEL = 2.0;           // Ускорение при погружении
static const double IMPACT_VEL_THRESHOLD = 1.0; // Порог скорости для удара о воду
static const double IMPACT_FACTOR = 0.8;        // Сила дополнительного удара
static const double MAX_LIN_SPEED = 10.0;       // Максимальная линейная скорость
static const double MAX_ANG_SPEED = 5.0;        // Максимальная угловая скорость
static const double EQUILIBRIUM_VEL = 0.02;     // Скорость, ниже которой считаем равновесие
static const double EQUILIBRIUM_ANGVEL = 0.005; // Угловая скорость, ниже которой считаем равновесие

// ----- вспомогательные типы -----
struct Vec2 { double x = 0, y = 0; Vec2() {} Vec2(double X, double Y) :x(X), y(Y) {} };
inline Vec2 operator+(const Vec2& a, const Vec2& b) { return Vec2(a.x + b.x, a.y + b.y); }
inline Vec2 operator-(const Vec2& a, const Vec2& b) { return Vec2(a.x - b.x, a.y - b.y); }
inline Vec2 operator*(const Vec2& a, double s) { return Vec2(a.x * s, a.y * s); }
inline double wrapAngle(double a) { while (a > PI) a -= 2 * PI; while (a < -PI) a += 2 * PI; return a; } // Приведение угла к [-π, π]

// Параметры мира (границы, уровень воды, плотности, гравитация)
struct World {
    double xMin = -10, xMax = 10, yMin = -12, yMax = 8;
    double waterLevel = 0.0;
    double densityWater = 1025.0;
    double densityIce = 917.0;
    double g = 9.81 * GRAVITY_MULTIPLIER;
};

// Свойства айсберга
struct PolyProps {
    double area = 0;            // площадь
    Vec2 center;                // центр масс
    double I = 1.0;             // момент инерции относительно центра масс
    double mass = 1.0;          // масса
    std::vector<Vec2> points_ccw; // вершины в порядке против часовой стрелки
};

// Состояние айсберга (положение, скорость, угол, угловая скорость)
struct State {
    double x = 0, y = 0;
    double vx = 0, vy = 0;
    double angle = 0, angVel = 0;
};

// ----- геометрические вычисления -----

// Вычисление ориентированной площади многоугольника
static double signedArea(const std::vector<Vec2>& pts) {
    size_t n = pts.size(); if (n < 3) return 0.0;
    double s = 0.0;
    for (size_t i = 0; i < n; i++) {
        const Vec2& a = pts[i], & b = pts[(i + 1) % n];
        s += a.x * b.y - b.x * a.y;
    }
    return 0.5 * s;
}

// Приведение порядка вершин к против часовой стрелки
static void ensureCCW(std::vector<Vec2>& pts) {
    if (signedArea(pts) < 0.0) std::reverse(pts.begin(), pts.end());
}

// Вычисление центра масс многоугольника
static Vec2 centroid(const std::vector<Vec2>& pts, double signedA) {
    size_t n = pts.size();
    double cx = 0, cy = 0;
    for (size_t i = 0; i < n; i++) {
        const Vec2& p = pts[i], & q = pts[(i + 1) % n];
        double cr = p.x * q.y - q.x * p.y;
        cx += (p.x + q.x) * cr;
        cy += (p.y + q.y) * cr;
    }
    double inv = 1.0 / (6.0 * signedA);
    return Vec2(cx * inv, cy * inv);
}

// Вычисление суммы вторых моментов площади (Ixx + Iyy) для последующего расчёта момента инерции
static double secondMomentSum(const std::vector<Vec2>& pts) {
    size_t n = pts.size();
    double Ixx = 0, Iyy = 0;
    for (size_t i = 0; i < n; i++) {
        const Vec2& p = pts[i], & q = pts[(i + 1) % n];
        double cr = p.x * q.y - q.x * p.y;
        Ixx += cr * (p.y * p.y + p.y * q.y + q.y * q.y);
        Iyy += cr * (p.x * p.x + p.x * q.x + q.x * q.x);
    }
    Ixx /= 12.0; Iyy /= 12.0;
    return Ixx + Iyy;
}

// Поворот локальных точек айсберга на угол angle
static std::vector<Vec2> rotatedPoints(const PolyProps& poly, double angle) {
    double c = cos(angle), s = sin(angle);
    std::vector<Vec2> out; out.reserve(poly.points_ccw.size());
    for (const auto& p : poly.points_ccw) {
        Vec2 cp = p - poly.center;
        out.emplace_back(cp.x * c - cp.y * s, cp.x * s + cp.y * c);
    }
    return out;
}

// Получение координат вершин айсберга в текущем состоянии
static std::vector<Vec2> transformedVertices(const PolyProps& poly, const State& st) {
    auto rp = rotatedPoints(poly, st.angle);
    for (auto& v : rp) { v.x += st.x; v.y += st.y; }
    return rp;
}

// Отсечение многоугольника горизонтальной линией y = yL (возвращает часть ниже линии)
static std::vector<Vec2> clipBelowY(const std::vector<Vec2>& verts, double yL) {
    std::vector<Vec2> out;
    if (verts.empty()) return out;
    Vec2 prev = verts.back(); bool pin = prev.y <= yL;
    for (const auto& cur : verts) {
        bool cin = cur.y <= yL;
        if (cin) {
            if (!pin) {
                double dy = cur.y - prev.y;
                if (std::abs(dy) > 1e-12) {
                    double t = (yL - prev.y) / dy;
                    out.emplace_back(prev.x + t * (cur.x - prev.x), yL);
                }
            }
            out.push_back(cur);
        }
        else if (pin) {
            double dy = cur.y - prev.y;
            if (std::abs(dy) > 1e-12) {
                double t = (yL - prev.y) / dy;
                out.emplace_back(prev.x + t * (cur.x - prev.x), yL);
            }
        }
        prev = cur; pin = cin;
    }
    return out;
}

// Площадь подводной части и её центр
static std::pair<double, Vec2> submergedAreaAndCentroid(const std::vector<Vec2>& verts, double yL) {
    auto c = clipBelowY(verts, yL);
    if (c.size() < 3) return { 0.0, Vec2(0,0) };
    ensureCCW(c);
    double sA = signedArea(c);
    if (std::abs(sA) < 1e-12) return { 0.0, Vec2(0,0) };
    return { std::abs(sA), centroid(c, sA) };
}

// Вычисление всех свойств айсберга (площадь, центр масс, момент инерции, масса)
static PolyProps calcPolyProps(const std::vector<Vec2>& pts, const World& w) {
    PolyProps r;
    if (pts.size() < 3) return r;
    std::vector<Vec2> P = pts; ensureCCW(P);
    double sA = signedArea(P);
    if (std::abs(sA) < 1e-12) sA = (sA >= 0 ? 1e-12 : -1e-12);
    Vec2 C = centroid(P, sA);
    double Iarea = secondMomentSum(P);
    double Icent = Iarea - sA * (C.x * C.x + C.y * C.y); // момент инерции относительно центра масс
    r.area = std::abs(sA);
    r.center = C;
    r.I = w.densityIce * (Icent > 1e-6 ? Icent : 1e-6);
    r.mass = w.densityIce * std::abs(sA);
    r.points_ccw = P;
    return r;
}

// ----- физика -----
static double g_prevSubmergedArea = 0.0; // запоминаем предыдущую погружённую площадь для эффекта удара

// Вычисление сил и момента действующих на айсберг
static std::pair<Vec2, double> forcesAndTorque(const PolyProps& poly, const World& w, const State& st, double elapsedTime) {
    auto verts = transformedVertices(poly, st);
    auto sub = submergedAreaAndCentroid(verts, w.waterLevel);
    double subA = sub.first;
    Vec2 buoyC = sub.second;

    double Fb = w.densityWater * subA * w.g; // сила Архимеда
    double Fg = poly.mass * w.g;             // сила тяжести
    double netY = Fb - Fg;
    if (netY < 0) netY *= SINK_ACCEL;        // ускоряем погружение
    Vec2 netF(0.0, netY);

    // Эффект удара о воду
    bool entered = (g_prevSubmergedArea < 1e-8) && (subA > 1e-8) && (st.vy < -IMPACT_VEL_THRESHOLD);
    if (entered) {
        double extraDown = -IMPACT_FACTOR * poly.mass * std::min(5.0, std::abs(st.vy));
        netF.y += extraDown;
    }

    // Демпфирование, увеличивающееся со временем
    double prog = std::min(1.0, elapsedTime / 3.0);
    double mult = 1.0 + prog * 6.0;
    netF.x += -st.vx * DAMP_X * mult;
    netF.y += -st.vy * DAMP_Y * mult;

    // Момент силм сила Архимеда приложена к центру подводной части создаёт вращение
    double torque = (buoyC.x - st.x) * Fb;
    double angErr = wrapAngle(st.angle);
    torque += -DAMP_ANG * (1.0 + prog * 4.0) * angErr;   // демпфирование по углу
    torque += -st.angVel * DAMP_ANG * (1.0 + prog * 5.0); // демпфирование угловой скорости

    return { netF, torque };
}

// Вычисление производных состояния скорости и ускорения
static void derivatives(const PolyProps& poly, const World& w, const State& st, double elapsedTime, Vec2& dPos, Vec2& dVel, double& dAng, double& dAngVel) {
    auto FT = forcesAndTorque(poly, w, st, elapsedTime);
    Vec2 F = FT.first; double M = FT.second;
    dPos = Vec2(st.vx, st.vy);               // производная позиции скорость
    dVel = Vec2(F.x / poly.mass, F.y / poly.mass); // производная скорости ускорение
    dAng = st.angVel;                       // производная угла угловая скорость
    dAngVel = M / poly.I;                   // производная угловой скорости угловое ускорение
}

// ----- методы интегрирования -----

// RK4
static void rk4Step(const PolyProps& poly, const World& w, State& st, double dt, double elapsedTime) {
    Vec2 k1p, k1v, k2p, k2v, k3p, k3v, k4p, k4v;
    double k1a, k1av, k2a, k2av, k3a, k3av, k4a, k4av;
    derivatives(poly, w, st, elapsedTime, k1p, k1v, k1a, k1av);
    State s2 = st;
    s2.x += 0.5 * dt * k1p.x; s2.y += 0.5 * dt * k1p.y;
    s2.vx += 0.5 * dt * k1v.x; s2.vy += 0.5 * dt * k1v.y;
    s2.angle += 0.5 * dt * k1a; s2.angVel += 0.5 * dt * k1av;
    derivatives(poly, w, s2, elapsedTime + 0.5 * dt, k2p, k2v, k2a, k2av);
    State s3 = st;
    s3.x += 0.5 * dt * k2p.x; s3.y += 0.5 * dt * k2p.y;
    s3.vx += 0.5 * dt * k2v.x; s3.vy += 0.5 * dt * k2v.y;
    s3.angle += 0.5 * dt * k2a; s3.angVel += 0.5 * dt * k2av;
    derivatives(poly, w, s3, elapsedTime + 0.5 * dt, k3p, k3v, k3a, k3av);
    State s4 = st;
    s4.x += dt * k3p.x; s4.y += dt * k3p.y;
    s4.vx += dt * k3v.x; s4.vy += dt * k3v.y;
    s4.angle += dt * k3a; s4.angVel += dt * k3av;
    derivatives(poly, w, s4, elapsedTime + dt, k4p, k4v, k4a, k4av);

    st.x += (dt / 6.0) * (k1p.x + 2 * k2p.x + 2 * k3p.x + k4p.x);
    st.y += (dt / 6.0) * (k1p.y + 2 * k2p.y + 2 * k3p.y + k4p.y);
    st.vx += (dt / 6.0) * (k1v.x + 2 * k2v.x + 2 * k3v.x + k4v.x);
    st.vy += (dt / 6.0) * (k1v.y + 2 * k2v.y + 2 * k3v.y + k4v.y);
    st.angle += (dt / 6.0) * (k1a + 2 * k2a + 2 * k3a + k4a);
    st.angVel += (dt / 6.0) * (k1av + 2 * k2av + 2 * k3av + k4av);

    // Дополнительное затухание и ограничения скорости
    st.vx *= MULT_DAMP_STEP;
    st.vy *= MULT_DAMP_STEP;
    st.angVel *= MULT_DAMP_STEP;

    double sp = std::hypot(st.vx, st.vy);
    if (sp > MAX_LIN_SPEED) { double f = MAX_LIN_SPEED / sp; st.vx *= f; st.vy *= f; }
    if (std::abs(st.angVel) > MAX_ANG_SPEED) st.angVel = (st.angVel > 0 ? MAX_ANG_SPEED : -MAX_ANG_SPEED);
}

// RK6
static void rk6Step(const PolyProps& poly, const World& w, State& st, double dt, double elapsedTime) {
    const int s = 7;
    double c[s] = { 0, 1.0 / 3.0, 2.0 / 5.0, 1.0, 2.0 / 3.0, 4.0 / 5.0, 1.0 };
    double a[s][s] = { {0} };
    a[1][0] = 1.0 / 3.0;
    a[2][0] = 4.0 / 25.0; a[2][1] = 6.0 / 25.0;
    a[3][0] = 1.0 / 4.0;  a[3][1] = -3.0;    a[3][2] = 4.0;
    a[4][0] = 6.0 / 81.0; a[4][1] = 90.0 / 81.0; a[4][2] = -50.0 / 81.0; a[4][3] = 8.0 / 81.0;
    a[5][0] = 6.0 / 75.0; a[5][1] = 36.0 / 75.0; a[5][2] = 10.0 / 75.0; a[5][3] = 8.0 / 75.0; a[5][4] = 0;
    a[6][0] = 1.0 / 20.0; a[6][1] = 0;         a[6][2] = 49.0 / 180.0; a[6][3] = 25.0 / 16.0; a[6][4] = 0; a[6][5] = 1.0 / 20.0;

    double b[s] = { 11.0 / 120.0, 0, 27.0 / 40.0, 27.0 / 40.0, 0, 4.0 / 15.0, 4.0 / 15.0 };
    double sum_b = 0;
    for (int i = 0; i < s; ++i) sum_b += b[i];
    double norm = 1.0 / sum_b;
    for (int i = 0; i < s; ++i) b[i] *= norm;

    Vec2 kp[s], kv[s];
    double ka[s], kav[s];
    State tmp;
    for (int i = 0; i < s; ++i) {
        if (i == 0) {
            derivatives(poly, w, st, elapsedTime + c[i] * dt, kp[i], kv[i], ka[i], kav[i]);
        }
        else {
            tmp = st;
            for (int j = 0; j < i; ++j) {
                tmp.x += dt * a[i][j] * kp[j].x;
                tmp.y += dt * a[i][j] * kp[j].y;
                tmp.vx += dt * a[i][j] * kv[j].x;
                tmp.vy += dt * a[i][j] * kv[j].y;
                tmp.angle += dt * a[i][j] * ka[j];
                tmp.angVel += dt * a[i][j] * kav[j];
            }
            derivatives(poly, w, tmp, elapsedTime + c[i] * dt, kp[i], kv[i], ka[i], kav[i]);
        }
    }

    st.x += dt * (kp[0].x * b[0] + kp[1].x * b[1] + kp[2].x * b[2] + kp[3].x * b[3] + kp[4].x * b[4] + kp[5].x * b[5] + kp[6].x * b[6]);
    st.y += dt * (kp[0].y * b[0] + kp[1].y * b[1] + kp[2].y * b[2] + kp[3].y * b[3] + kp[4].y * b[4] + kp[5].y * b[5] + kp[6].y * b[6]);
    st.vx += dt * (kv[0].x * b[0] + kv[1].x * b[1] + kv[2].x * b[2] + kv[3].x * b[3] + kv[4].x * b[4] + kv[5].x * b[5] + kv[6].x * b[6]);
    st.vy += dt * (kv[0].y * b[0] + kv[1].y * b[1] + kv[2].y * b[2] + kv[3].y * b[3] + kv[4].y * b[4] + kv[5].y * b[5] + kv[6].y * b[6]);
    st.angle += dt * (ka[0] * b[0] + ka[1] * b[1] + ka[2] * b[2] + ka[3] * b[3] + ka[4] * b[4] + ka[5] * b[5] + ka[6] * b[6]);
    st.angVel += dt * (kav[0] * b[0] + kav[1] * b[1] + kav[2] * b[2] + kav[3] * b[3] + kav[4] * b[4] + kav[5] * b[5] + kav[6] * b[6]);

    st.vx *= MULT_DAMP_STEP;
    st.vy *= MULT_DAMP_STEP;
    st.angVel *= MULT_DAMP_STEP;

    double sp = std::hypot(st.vx, st.vy);
    if (sp > MAX_LIN_SPEED) { double f = MAX_LIN_SPEED / sp; st.vx *= f; st.vy *= f; }
    if (std::abs(st.angVel) > MAX_ANG_SPEED) st.angVel = (st.angVel > 0 ? MAX_ANG_SPEED : -MAX_ANG_SPEED);
}

// Метод Ралстона
static void ralstonStep(const PolyProps& poly, const World& w, State& st, double dt, double elapsedTime) {
    Vec2 k1p, k1v; double k1a, k1av;
    derivatives(poly, w, st, elapsedTime, k1p, k1v, k1a, k1av);

    State s2 = st;
    s2.x += (2.0 / 3.0) * dt * k1p.x;
    s2.y += (2.0 / 3.0) * dt * k1p.y;
    s2.vx += (2.0 / 3.0) * dt * k1v.x;
    s2.vy += (2.0 / 3.0) * dt * k1v.y;
    s2.angle += (2.0 / 3.0) * dt * k1a;
    s2.angVel += (2.0 / 3.0) * dt * k1av;

    Vec2 k2p, k2v; double k2a, k2av;
    derivatives(poly, w, s2, elapsedTime + (2.0 / 3.0) * dt, k2p, k2v, k2a, k2av);

    st.x += dt * (0.25 * k1p.x + 0.75 * k2p.x);
    st.y += dt * (0.25 * k1p.y + 0.75 * k2p.y);
    st.vx += dt * (0.25 * k1v.x + 0.75 * k2v.x);
    st.vy += dt * (0.25 * k1v.y + 0.75 * k2v.y);
    st.angle += dt * (0.25 * k1a + 0.75 * k2a);
    st.angVel += dt * (0.25 * k1av + 0.75 * k2av);

    st.vx *= MULT_DAMP_STEP;
    st.vy *= MULT_DAMP_STEP;
    st.angVel *= MULT_DAMP_STEP;

    double sp = std::hypot(st.vx, st.vy);
    if (sp > MAX_LIN_SPEED) { double f = MAX_LIN_SPEED / sp; st.vx *= f; st.vy *= f; }
    if (std::abs(st.angVel) > MAX_ANG_SPEED) st.angVel = (st.angVel > 0 ? MAX_ANG_SPEED : -MAX_ANG_SPEED);
}

// ----- преобразование координат для отрисовки -----
struct Mapper {
    World w; int W, H;
    Mapper(const World& ww, int w_, int h_) : w(ww), W(w_), H(h_) {}
    sf::Vector2f mapPt(const Vec2& p) const {
        float mx = float((p.x - w.xMin) / (w.xMax - w.xMin) * W);
        float my = float(H - (p.y - w.yMin) / (w.yMax - w.yMin) * H);
        return sf::Vector2f(mx, my);
    }
};

// ----- отрисовка -----
static void drawFilledPoly(sf::RenderWindow& win, const Mapper& m, const std::vector<Vec2>& pts, const sf::Color& fill) {
    if (pts.size() < 3) return;
    sf::ConvexShape poly; poly.setPointCount(pts.size());
    for (size_t i = 0; i < pts.size(); ++i) poly.setPoint(i, m.mapPt(pts[i]));
    poly.setFillColor(fill); poly.setOutlineColor(sf::Color::Black); poly.setOutlineThickness(1.0f);
    win.draw(poly);
}
static void drawPolyline(sf::RenderWindow& win, const Mapper& m, const std::vector<Vec2>& pts, const sf::Color& col, bool closed) {
    if (pts.size() < 2) return;
    sf::VertexArray va(sf::LineStrip, pts.size() + (closed ? 1u : 0u));
    for (size_t i = 0; i < pts.size(); ++i) { va[i].position = m.mapPt(pts[i]); va[i].color = col; }
    if (closed) { va[pts.size()].position = m.mapPt(pts[0]); va[pts.size()].color = col; }
    win.draw(va);
}
static Vec2 computeDrawingCenter(const std::vector<Vec2>& points) {
    if (points.empty()) return Vec2(0, 0);
    double sx = 0, sy = 0;
    for (const auto& p : points) { sx += p.x; sy += p.y; }
    return Vec2(sx / points.size(), sy / points.size());
}

// ----- главная функция -----
int main() {
    World world;
    Mapper mapper(world, 1200, 800);
    sf::RenderWindow window(sf::VideoMode(mapper.W, mapper.H), "Iceberg Simulation (RK6)");
    window.setFramerateLimit(60);

    std::vector<Vec2> drawn;            // вершины, нарисованные пользователем
    bool isDrawing = false;              // идёт ли рисование
    bool shapeReady = false;             // готова ли фигура
    bool simRunning = false;             // выполняется ли симуляция
    PolyProps iceberg;                   // свойства айсберга
    State st, prevSt;                   // текущее состояние и предыдущее
    double simTime = 0.0;               // время симуляции
    double accumulator = 0.0;           // накопитель времени для фиксированного шага
    const double dt = 1.0 / 60.0;       // шаг интегрирования
    std::mt19937 rng(123456);            // генератор случайных чисел
    std::uniform_real_distribution<double> rndAng(-0.02, 0.02); // начальный разброс угла

    // Функция преобразования экранных координат мыши в мировые
    auto mouseToWorld = [&](const sf::RenderWindow& win) {
        sf::Vector2i m = sf::Mouse::getPosition(win);
        double x = world.xMin + double(m.x) / mapper.W * (world.xMax - world.xMin);
        double y = world.yMin + (1.0 - double(m.y) / mapper.H) * (world.yMax - world.yMin);
        return Vec2(x, y);
        };

    sf::Clock clock;
    g_prevSubmergedArea = 0.0;

    int step_counter = 0; // счётчик шагов для вывода погрешностей

    // Вывод заголовка в консоль
    std::cout << std::fixed << std::setprecision(6);
    std::cout << "Starting simulation with RK6 as reference.\n";
    std::cout << "Step\tTime\tRK4 pos err (%)\t\tRK4 ang err (%)\t\tRalston pos err (%)\t\tRalston ang err (%)\n";

    while (window.isOpen()) {
        // Обработка событий
        sf::Event ev;
        while (window.pollEvent(ev)) {
            if (ev.type == sf::Event::Closed) window.close();

            if (!simRunning) {
                // Режим рисования
                if (ev.type == sf::Event::MouseButtonPressed && ev.mouseButton.button == sf::Mouse::Left) {
                    drawn.clear(); isDrawing = true; shapeReady = false;
                    drawn.push_back(mouseToWorld(window));
                }
                else if (ev.type == sf::Event::MouseMoved && isDrawing) {
                    Vec2 p = mouseToWorld(window);
                    if (drawn.empty() || std::hypot(p.x - drawn.back().x, p.y - drawn.back().y) > 0.05)
                        drawn.push_back(p);
                }
                else if (ev.type == sf::Event::MouseButtonReleased && ev.mouseButton.button == sf::Mouse::Left) {
                    isDrawing = false;
                    if (drawn.size() >= 3) shapeReady = true;
                }
                else if (ev.type == sf::Event::KeyPressed && ev.key.code == sf::Keyboard::Enter && shapeReady) {
                    // Начать симуляцию
                    iceberg = calcPolyProps(drawn, world);
                    Vec2 dc = computeDrawingCenter(drawn);
                    st = State();
                    st.x = dc.x; st.y = dc.y;
                    st.angle = rndAng(rng); st.angVel = rndAng(rng);
                    prevSt = st;
                    simTime = 0; accumulator = 0;
                    simRunning = true;
                    auto verts = transformedVertices(iceberg, st);
                    g_prevSubmergedArea = submergedAreaAndCentroid(verts, world.waterLevel).first;
                    step_counter = 0;
                }
            }
            else {
                // Режим симуляции: сброс по R
                if (ev.type == sf::Event::KeyPressed && ev.key.code == sf::Keyboard::R) {
                    simRunning = false;
                    drawn.clear();
                    shapeReady = false;
                    g_prevSubmergedArea = 0.0;
                }
            }
        }

        // Обновление физики
        double ft = clock.restart().asSeconds();
        if (ft > 0.25) ft = 0.25;

        if (simRunning) {
            // Сохраняем предыдущую погружённую площадь для эффекта удара
            auto prevVerts = transformedVertices(iceberg, prevSt);
            g_prevSubmergedArea = submergedAreaAndCentroid(prevVerts, world.waterLevel).first;
            accumulator += ft;

            // Выполняем столько шагов, сколько накопилось
            while (accumulator >= dt) {
                State st_before = st;               // запоминаем состояние до шага
                rk6Step(iceberg, world, st, dt, simTime); // основной метод RK6

                // Сравниваем с RK4 и Ралстоном, начиная из того же состояния
                State st4 = st_before;
                rk4Step(iceberg, world, st4, dt, simTime);
                State stRal = st_before;
                ralstonStep(iceberg, world, stRal, dt, simTime);

                // Вычисляем абсолютные погрешности
                double delta_pos_rk4 = std::hypot(st.x - st4.x, st.y - st4.y);
                double delta_angle_rk4 = std::abs(wrapAngle(st.angle - st4.angle));
                double delta_pos_ral = std::hypot(st.x - stRal.x, st.y - stRal.y);
                double delta_angle_ral = std::abs(wrapAngle(st.angle - stRal.angle));

                // Относительные погрешности в процентах
                double ref_pos = std::hypot(st.x, st.y);
                double ref_angle = std::abs(st.angle);
                double perc_pos_rk4 = (ref_pos > 1e-6) ? (delta_pos_rk4 / ref_pos) * 100.0 : delta_pos_rk4;
                double perc_angle_rk4 = (ref_angle > 1e-6) ? (delta_angle_rk4 / ref_angle) * 100.0 : delta_angle_rk4;
                double perc_pos_ral = (ref_pos > 1e-6) ? (delta_pos_ral / ref_pos) * 100.0 : delta_pos_ral;
                double perc_angle_ral = (ref_angle > 1e-6) ? (delta_angle_ral / ref_angle) * 100.0 : delta_angle_ral;

                step_counter++;
                if (step_counter % 100 == 0) {
                    std::cout << step_counter << "\t"
                        << simTime << "\t"
                        << perc_pos_rk4 << "\t\t"
                        << perc_angle_rk4 << "\t\t"
                        << perc_pos_ral << "\t\t"
                        << perc_angle_ral << std::endl;
                }

                prevSt = st_before;
                simTime += dt;
                accumulator -= dt;

                // Обновление погружённой площади для следующего шага
                auto curVerts = transformedVertices(iceberg, st);
                g_prevSubmergedArea = submergedAreaAndCentroid(curVerts, world.waterLevel).first;
                // Останавливаем движение если скорости близки к нулю
                if (std::abs(st.vx) < EQUILIBRIUM_VEL && std::abs(st.vy) < EQUILIBRIUM_VEL && std::abs(st.angVel) < EQUILIBRIUM_ANGVEL) {
                    st.vx = st.vy = st.angVel = 0;
                }
            }
        }

        // Интерполяция для плавной отрисовки между кадрами
        State renderSt = st;
        if (simRunning) {
            double alpha = accumulator / dt;
            renderSt.x = prevSt.x + (st.x - prevSt.x) * alpha;
            renderSt.y = prevSt.y + (st.y - prevSt.y) * alpha;
            double da = wrapAngle(st.angle - prevSt.angle);
            renderSt.angle = prevSt.angle + da * alpha;
        }

        // ----- отрисовка -----
        window.clear(sf::Color(240, 240, 240));
        // Вода (заливка)
        std::vector<Vec2> water = { {world.xMin,world.yMin},{world.xMax,world.yMin},{world.xMax,world.waterLevel},{world.xMin,world.waterLevel} };
        drawFilledPoly(window, mapper, water, sf::Color(173, 216, 230, 160));

        if (!simRunning) {
            // Режим рисования: отображаем текущий контур
            if (drawn.size() >= 2) {
                drawPolyline(window, mapper, drawn, isDrawing ? sf::Color::Red : sf::Color(10, 10, 120), false);
            }
            if (shapeReady) {
                auto tmp = drawn; ensureCCW(tmp);
                drawFilledPoly(window, mapper, tmp, sf::Color(255, 255, 255, 230));
                drawPolyline(window, mapper, tmp, sf::Color(10, 10, 120), true);
                Vec2 c = computeDrawingCenter(drawn);
                sf::CircleShape cm(4.f); cm.setFillColor(sf::Color::Green); cm.setOrigin(4.f, 4.f);
                cm.setPosition(mapper.mapPt(c)); window.draw(cm);
            }
        }
        else {
            // Симуляция рисуем айсберг, подводную часть, центр масс и центр выталкивания
            auto verts = transformedVertices(iceberg, renderSt);
            if (verts.size() >= 3) {
                auto sh = verts; ensureCCW(sh);
                drawFilledPoly(window, mapper, sh, sf::Color(255, 255, 255, 230));
                drawPolyline(window, mapper, sh, sf::Color(10, 10, 120), true);
                auto sub = clipBelowY(sh, world.waterLevel);
                if (sub.size() >= 3) {
                    ensureCCW(sub);
                    drawFilledPoly(window, mapper, sub, sf::Color(0, 0, 139, 120));
                }
            }
            // Центр масс (красный)
            sf::CircleShape com(3.f); com.setFillColor(sf::Color::Red); com.setOrigin(3.f, 3.f);
            com.setPosition(mapper.mapPt(Vec2(renderSt.x, renderSt.y))); window.draw(com);
            // Центр выталкивания (синий)
            auto curVerts = verts;
            auto subInfo = submergedAreaAndCentroid(curVerts, world.waterLevel);
            if (subInfo.first > 1e-9) {
                Vec2 buoy = subInfo.second;
                sf::CircleShape bm(3.f); bm.setFillColor(sf::Color::Blue); bm.setOrigin(3.f, 3.f);
                bm.setPosition(mapper.mapPt(buoy)); window.draw(bm);
            }
        }
        window.display();
    }
    return 0;
}