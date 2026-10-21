"""Sign and roll choices in the several-time relaxation of Remark 6.3 of the paper (planar restriction).
Exploratory float code, not rigorous: best local maximum found by Nelder-Mead from random starts.

Body frame strip X = R x [0,1].  Event j: world motion h_j(p) = R(phi_j) D_j p + v_j, where phi_j is the
SIGNED projected angle of the body axis (e_x -> (cos phi_j, sin phi_j)) and D_j = I or diag(1,-1) (a roll of the
body by pi about its axis, which acts on the planar picture as this reflection).  Region:
X n h_1^{-1}(L) n ... , L = S_X u S_Y(c) (planar).  Objective: area of the largest connected component.
Event spec: '51' (phi = +51 deg), '-51', '51r' (with roll), '-51r'.
Usage: python3 -I explore/signs.py c nstarts seed spec1 spec2 ...   (for example: 5.0 40 1 51 -30r)
"""
import sys
import numpy as np
from itertools import product
from scipy.optimize import minimize, linprog

c = float(sys.argv[1])
nst = int(sys.argv[2])
rng = np.random.default_rng(int(sys.argv[3]))
specs = sys.argv[4:]
BIG = 60.0
evs = []
for sp in specs:
    refl = sp.endswith('r')
    ang = np.radians(float(sp.rstrip('r')))
    Rm = np.array([[np.cos(ang), -np.sin(ang)], [np.sin(ang), np.cos(ang)]])
    Lm = Rm @ (np.diag([1.0, -1.0]) if refl else np.eye(2))
    evs.append(Lm)
K = len(evs)
SXh = [(np.array([1.0, 0]), 0.0), (np.array([-1.0, 0]), BIG), (np.array([0, 1.0]), 1.0), (np.array([0, -1.0]), 0.0)]
SYh = [(np.array([1.0, 0]), 1.0), (np.array([-1.0, 0]), 0.0), (np.array([0, 1.0]), c), (np.array([0, -1.0]), 0.0)]
Xh = [(np.array([0, 1.0]), 1.0), (np.array([0, -1.0]), 0.0), (np.array([1.0, 0]), BIG), (np.array([-1.0, 0]), BIG)]


def pull(hs, Lm, v):
    # {p : a.(Lm p + v) <= b} = {(Lm^T a).p <= b - a.v}
    return [(Lm.T @ a, b - a @ v) for a, b in hs]


def clip(poly, a, b):
    out = []
    n = len(poly)
    for i in range(n):
        P, Q = poly[i], poly[(i + 1) % n]
        fp, fq = a @ P - b, a @ Q - b
        if fp <= 0:
            out.append(P)
        if fp * fq < 0:
            out.append(P + (Q - P) * (fp / (fp - fq)))
    return out


def area_of(hs):
    poly = [np.array([-2 * BIG, -2 * BIG]), np.array([2 * BIG, -2 * BIG]), np.array([2 * BIG, 2 * BIG]), np.array([-2 * BIG, 2 * BIG])]
    for a, b in hs:
        poly = clip(poly, a, b)
        if len(poly) < 3:
            return 0.0
    x = np.array([p[0] for p in poly]); y = np.array([p[1] for p in poly])
    return 0.5 * abs(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))


def meet(h1, h2):
    hs = h1 + h2
    A = np.array([a for a, b in hs]); bb = np.array([b for a, b in hs]) + 1e-9
    return linprog([0, 0], A_ub=A, b_ub=bb, bounds=[(None, None)] * 2, method='highs').status == 0


def best_component(v):
    Ls = [{'X': pull(SXh, evs[j], v[2 * j:2 * j + 2]), 'Y': pull(SYh, evs[j], v[2 * j:2 * j + 2])} for j in range(K)]
    pieces = []
    for combo in product('XY', repeat=K):
        hs = Xh + [h for j in range(K) for h in Ls[j][combo[j]]]
        ar = area_of(hs)
        if ar > 1e-12:
            pieces.append((ar, hs))
    if not pieces:
        return 0.0
    n = len(pieces)
    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for i in range(n):
        for j in range(i + 1, n):
            if find(i) != find(j) and meet(pieces[i][1], pieces[j][1]):
                parent[find(i)] = find(j)
    tot = {}
    for i in range(n):
        tot[find(i)] = tot.get(find(i), 0.0) + pieces[i][0]
    return max(tot.values())


best = (0, None)
for k in range(nst):
    v0 = np.concatenate([[rng.uniform(-4, 4), rng.uniform(-4, 4)] for j in range(K)])
    r = minimize(lambda v: -best_component(v), v0, method='Nelder-Mead',
                 options={'maxiter': 1500 * K, 'xatol': 1e-9, 'fatol': 1e-11, 'adaptive': True})
    if -r.fun > best[0]:
        best = (-r.fun, r.x)
print(f'c = {c}, events {specs}, {nst} starts, seed {sys.argv[3]}: best largest-component area = {best[0]:.6f} at v = {np.round(best[1], 4).tolist()}', flush=True)
