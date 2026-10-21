"""Exploratory float code (not rigorous) behind Remark 6.3 of the paper: local searches for the relaxation
with k times at which the projection of the body axis to the x-y plane has prescribed angles (alpha events),
with full 3D freedom
(out-of-plane axis component zeta = w_z with |zeta| <= 0.95 (clipped), roll psi free).
Anchor = event 0 (world frame). Event j: T_j with axis w_j = (sqrt(1-z^2) cos a_j, sqrt(1-z^2) sin a_j, z), roll psi_j,
offset (A_j, B_j) at y=0.5, shift sigma_j along w_j.  h_j maps anchor frame -> event frame (axis sign preserved).
Region R = T n L n (n_j h_j^{-1}(L)), L = SX u Stub(c).  Objective: largest connected component volume.  Stub height C_STUB = 5.0 = 1 + M for M = 4, from multi_ev.py.
Usage: python3 -I explore/multi_ev2.py NSTART MAXITER SEED ANGLE_DEG [ANGLE_DEG ...]   (first angle = anchor)
"""
import numpy as np, sys, itertools, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.optimize import minimize
from multi_ev import region_volume as _unused, L_pieces, inv_transform, feasible
from poly3 import *

def frame_alpha(a, zeta, psi):
    zeta = np.clip(zeta, -0.95, 0.95)
    r = np.sqrt(1 - zeta*zeta)
    w = np.array([r*np.cos(a), r*np.sin(a), zeta])
    e2 = np.array([0., 0., 1.]) - zeta*w; e2 /= np.linalg.norm(e2)
    e1 = np.cross(e2, w)
    return w, np.cos(psi)*e1 + np.sin(psi)*e2, -np.sin(psi)*e1 + np.cos(psi)*e2

def region3(params, angs):
    k = len(angs)
    z0, p0, A0, B0 = params[0:4]
    w, f1, f2 = frame_alpha(angs[0], z0, p0); rho = np.array([A0, 0.5, B0])
    T = tube(rho, f1, f2)
    lists = [[cat(T, P) for P in L_pieces()]]
    Src = np.column_stack([w, f1, f2])
    for j in range(1, k):
        zj, pj, Aj, Bj, sj = params[4+5*(j-1): 9+5*(j-1)]
        wj, g1, g2 = frame_alpha(angs[j], zj, pj); rhoj = np.array([Aj, 0.5, Bj])
        Dst = np.column_stack([wj, g1, g2])
        R = Dst @ Src.T; t = rhoj + sj*wj - R @ rho
        lists.append([inv_transform(P, R, t) for P in L_pieces()])
    pieces = []
    for combo in itertools.product(*lists):
        A, bb = cat(*combo)
        v = volume(A, bb)
        if v > 1e-9: pieces.append((v, A, bb))
    if not pieces: return 0.0
    n = len(pieces); par = list(range(n))
    def f(i):
        while par[i] != i: par[i] = par[par[i]]; i = par[i]
        return i
    for i in range(n):
        for j in range(i+1, n):
            if f(i) != f(j):
                A = np.vstack([pieces[i][1], pieces[j][1]]); bb = np.concatenate([pieces[i][2], pieces[j][2]])
                if feasible(A, bb + 1e-12): par[f(i)] = f(j)
    comp = {}
    for i in range(n): comp[f(i)] = comp.get(f(i), 0) + pieces[i][0]
    return max(comp.values())

if __name__ == '__main__':
    nstart = int(sys.argv[1]); maxiter = int(sys.argv[2]); seed = int(sys.argv[3])
    angs = [np.radians(float(v)) for v in sys.argv[4:]]
    k = len(angs); rng = np.random.default_rng(seed); best = (0, None)
    for it in range(nstart):
        x0 = [rng.uniform(-0.4, 0.4), rng.uniform(0, 2*np.pi), rng.uniform(-2.5, 0.5), rng.uniform(0, 1)]
        for j in range(k-1):
            x0 += [rng.uniform(-0.4, 0.4), rng.uniform(0, 2*np.pi), rng.uniform(-2.5, 0.5), rng.uniform(0, 1), rng.uniform(-2, 2)]
        r = minimize(lambda x: -region3(x, angs), np.array(x0), method='Nelder-Mead',
                     options={'maxiter': maxiter, 'xatol': 1e-6, 'fatol': 1e-8, 'adaptive': True})
        print(f"  start {it}: {-r.fun:.5f}  x={np.round(r.x,3).tolist()}", flush=True)
        if -r.fun > best[0]: best = (-r.fun, r.x)
    print(f"RESULT angles={sys.argv[4:]} best={best[0]:.5f} x={np.round(best[1],4).tolist()}", flush=True)
