"""Planar (2D) relaxation: body strip H = {0<=y<=1}; event j copy = Q_j(L) + o_j with Q_j in O(2),
|(Q_j y)_x| = s_j (8 choices per event), L = SX u Stub(c) (2D). Objective: max area of a connected component of
H n (n_j copies). Exploratory float code (not rigorous); the helpers are used by scan3.py (Remark 6.3).
Usage: python3 -I explore/planar2d.py NSTART s_1 s_2 ...  (s_j = sin of the angles; all 8 orientations per event).
"""
import numpy as np, itertools, sys
from scipy.optimize import minimize

C_STUB = 5.0; BIG = 60.0
def clip(poly, a, b):
    if len(poly) == 0: return poly
    s = poly @ a - b
    out = []
    n = len(poly)
    for i in range(n):
        p, q = poly[i], poly[(i+1) % n]; sp, sq = s[i], s[(i+1) % n]
        if sp <= 0: out.append(p)
        if (sp < 0 < sq) or (sq < 0 < sp):
            out.append(p + sp/(sp - sq)*(q - p))
    return np.array(out) if out else np.zeros((0, 2))
def area(P):
    if len(P) < 3: return 0.0
    x, y = P[:, 0], P[:, 1]
    return 0.5*abs(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))
def rect_hs(x0, x1, y0, y1):
    return [(np.array([1., 0.]), x1), (np.array([-1., 0.]), -x0), (np.array([0., 1.]), y1), (np.array([0., -1.]), -y0)]
L_PIECES = [rect_hs(-BIG, 0, 0, 1), rect_hs(0, 1, 0, C_STUB)]
def Qmat(theta, refl):
    c, s = np.cos(theta), np.sin(theta)
    R = np.array([[c, -s], [s, c]])
    return R @ np.diag([1., -1.]) if refl else R
def thetas(s):
    a = np.arcsin(s)
    return [a, -a, np.pi - a, np.pi + a]
def copy_hs(piece, Q, o):
    # {Q q + o : q in piece} = {p : a.(Q^T (p - o)) <= b} = {(Q a).p <= b + (Q a).o}
    return [(Q @ a, b + (Q @ a) @ o) for (a, b) in piece]
H0 = np.array([[-BIG, 0.], [BIG, 0.], [BIG, 1.], [-BIG, 1.]])
def polys_overlap(P, Q):
    # convex polygons share an interior point or touch: separating axis test (closed sets)
    for poly in (P, Q):
        n = len(poly)
        for i in range(n):
            e = poly[(i+1) % n] - poly[i]; nrm = np.array([e[1], -e[0]])
            a1 = P @ nrm; a2 = Q @ nrm
            if a1.max() < a2.min() - 1e-12 or a2.max() < a1.min() - 1e-12: return False
    return True
def region(copies):
    lists = [[(Q, o, piece) for piece in L_PIECES] for (Q, o) in copies]
    pieces = []
    for combo in itertools.product(*lists):
        P = H0
        for (Q, o, piece) in combo:
            for (a, b) in copy_hs(piece, Q, o):
                P = clip(P, a, b)
                if len(P) == 0: break
            if len(P) == 0: break
        ar = area(P)
        if ar > 1e-12: pieces.append((ar, P))
    if not pieces: return 0.0
    n = len(pieces); par = list(range(n))
    def f(i):
        while par[i] != i: par[i] = par[par[i]]; i = par[i]
        return i
    for i in range(n):
        for j in range(i+1, n):
            if f(i) != f(j) and polys_overlap(pieces[i][1], pieces[j][1]): par[f(i)] = f(j)
    comp = {}
    for i in range(n): comp[f(i)] = comp.get(f(i), 0) + pieces[i][0]
    return max(comp.values())
def objective(x, Qs):
    # x: anchor o = (x0, 0)?  anchor fixed at x-translation 0 by H's symmetry: o_0 = (0, x[0]); others (x[2j-1], x[2j])
    copies = [(Qs[0], np.array([0.0, x[0]]))]
    for j in range(1, len(Qs)):
        copies.append((Qs[j], np.array([x[2*j-1], x[2*j]])))
    return -region(copies)
def search(ss, nstart=20, seed=0, maxiter=2000, anchor_choices=((0, False), (1, False)), all_choices=True):
    rng = np.random.default_rng(seed)
    k = len(ss); results = []
    choice_list = [(ti, rf) for ti in range(4) for rf in (False, True)] if all_choices else [(0, False)]
    best_overall = (0, None, None)
    for anc in anchor_choices:
        for combo in itertools.product(choice_list, repeat=k-1):
            Qs = [Qmat(thetas(ss[0])[anc[0]], anc[1])] + [Qmat(thetas(ss[j+1])[c[0]], c[1]) for j, c in enumerate(combo)]
            best = (0, None)
            for it in range(nstart):
                x0 = rng.uniform(-3, 3, size=2*k-1)
                r = minimize(objective, x0, args=(Qs,), method='Nelder-Mead', options={'maxiter': maxiter, 'xatol': 1e-7, 'fatol': 1e-9, 'adaptive': True})
                if -r.fun > best[0]: best = (-r.fun, r.x)
            results.append((best[0], anc, combo))
            if best[0] > best_overall[0]: best_overall = (best[0], (anc, combo), best[1])
    results.sort(key=lambda t: -t[0])
    return best_overall, results[:6]
if __name__ == '__main__':
    nstart = int(sys.argv[1]); ss = [float(v) for v in sys.argv[2:]]
    # order: anchor = first listed tilt
    bo, top = search(ss, nstart=nstart)
    print(f"tilts={ss} angles={[round(np.degrees(np.arcsin(v)),2) for v in ss]} BEST={bo[0]:.5f} choice={bo[1]} x={np.round(bo[2],4).tolist()}")
    for t in top: print('   ', round(t[0], 5), t[1], t[2])
