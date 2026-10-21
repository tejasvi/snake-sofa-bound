"""Exploratory float code (not rigorous): k forced-tilt events in the first turn.  Its helpers
(L_pieces, inv_transform, feasible) are used by multi_ev2.py; its own search is not used in the paper.
World frame of the anchor event (last event, tilt s_k). Anchor tube T: axis w with |w.y| = s_k.
Event j<k: rigid motion h_j with h_j(T) = T_j, T_j a tube with |w_j.y| = s_j.  Body region:
   R = T n L n  ∩_j h_j^{-1}(L),   L = SX u Stub(c).
Objective: max volume of a connected component of R.
Planar restriction: all axes in the xy-plane, rolls 0, z-centred."""
import numpy as np, sys, itertools
from scipy.optimize import minimize, linprog
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from poly3 import *

C_STUB = 5.0

def tube_frame(s, phi, alpha):
    th = np.arccos(s)
    w = np.array([np.sin(th)*np.cos(phi), np.cos(th), np.sin(th)*np.sin(phi)])
    # reference perpendiculars: e2ref = z-ish so that alpha=0, phi=0 gives f2 = z (planar, aligned)
    e2 = np.array([0., 0., 1.]) - w[2]*w; e2 /= np.linalg.norm(e2)
    e1 = np.cross(e2, w)
    f1 = np.cos(alpha)*e1 + np.sin(alpha)*e2
    f2 = -np.sin(alpha)*e1 + np.cos(alpha)*e2
    return w, f1, f2

def make_h(Tparams, T1params, s, s1, sigma, flip):
    # anchor frame (rho, w, f1, f2) -> event frame (rho1 + sigma*w1, +-w1, f1', +-f2')
    phi, alpha, a, b = Tparams
    w, f1, f2 = tube_frame(s, phi, alpha); rho = np.array([a, 0.5, b])
    phi1, alpha1, a1, b1 = T1params
    w1, g1, g2 = tube_frame(s1, phi1, alpha1); rho1 = np.array([a1, 0.5, b1])
    sg = -1.0 if flip else 1.0
    Src = np.column_stack([w, f1, f2]); Dst = np.column_stack([sg*w1, g1, sg*g2])
    R = Dst @ Src.T
    t = rho1 + sigma*w1 - R @ rho
    return R, t, (rho, f1, f2)

def L_pieces():
    return [SX(), stub(C_STUB)]

def inv_transform(Ab, R, t):
    # h^{-1}(S) where h(p) = R p + t:  {p : h(p) in S} = {A (R p + t) <= b}
    A, b = Ab
    return A @ R, b - A @ t

def feasible(A, b):
    r = linprog(np.zeros(3), A_ub=A, b_ub=b, bounds=[(None, None)]*3, method='highs')
    return r.status == 0

def region_volume(Tparams, evs, s_anchor, connected=True):
    """evs: list of (s_j, T1params_j, sigma_j, flip_j)."""
    phi, alpha, a, b = Tparams
    w, f1, f2 = tube_frame(s_anchor, phi, alpha); rho = np.array([a, 0.5, b])
    T = tube(rho, f1, f2)
    lists = [[cat(T, P) for P in L_pieces()]]
    for (s1, T1p, sigma, flip) in evs:
        R, t, _ = make_h(Tparams, T1p, s_anchor, s1, sigma, flip)
        lists.append([inv_transform(P, R, t) for P in L_pieces()])
    pieces = []
    for combo in itertools.product(*lists):
        A, bb = cat(*combo)
        v = volume(A, bb)
        if v > 1e-9: pieces.append((v, A, bb))
    if not pieces: return 0.0
    if not connected: return sum(p[0] for p in pieces)
    n = len(pieces); parent = list(range(n))
    def find(i):
        while parent[i] != i: parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for i in range(n):
        for j in range(i+1, n):
            if find(i) != find(j):
                A = np.vstack([pieces[i][1], pieces[j][1]]); bb = np.concatenate([pieces[i][2], pieces[j][2]])
                if feasible(A, bb + 1e-12): parent[find(i)] = find(j)
    comp = {}
    for i in range(n): comp[find(i)] = comp.get(find(i), 0) + pieces[i][0]
    return max(comp.values())

def unpack(x, ss, planar):
    k = len(ss)
    if planar:
        # x = [a, (a1, sigma1, rollidx?) ...]: planar => phi=0, alpha=0 (or pi/2 multiples), b=0.5
        Tp = (0.0, 0.0, x[0], 0.5); evs = []
        for j in range(k-1):
            a1, sig = x[1+2*j], x[2+2*j]
            evs.append((ss[j], (0.0, 0.0, a1, 0.5), sig, False))
        return Tp, evs
    Tp = tuple(x[0:4]); evs = []
    for j in range(k-1):
        y = x[4+5*j: 9+5*j]
        evs.append((ss[j], tuple(y[0:4]), y[4], False))
    return Tp, evs

def objective(x, ss, planar):
    Tp, evs = unpack(x, ss, planar)
    return -region_volume(Tp, evs, ss[-1])

def search(ss, planar, nstart, seed, maxiter):
    rng = np.random.default_rng(seed)
    k = len(ss); best = (0, None)
    for it in range(nstart):
        if planar:
            x0 = np.concatenate([[rng.uniform(-2.5, 0.5)], np.ravel([[rng.uniform(-2.5, 0.5), rng.uniform(-2, 2)] for _ in range(k-1)])])
        else:
            parts = [rng.uniform(-0.6, 0.6), rng.uniform(-0.6, 0.6), rng.uniform(-2.5, 0.5), rng.uniform(0, 1)]
            for _ in range(k-1):
                parts += [rng.uniform(-0.6, 0.6), rng.uniform(-0.6, 0.6), rng.uniform(-2.5, 0.5), rng.uniform(0, 1), rng.uniform(-2, 2)]
            x0 = np.array(parts)
        r = minimize(objective, x0, args=(ss, planar), method='Nelder-Mead',
                     options={'maxiter': maxiter, 'xatol': 1e-6, 'fatol': 1e-8, 'adaptive': True})
        if -r.fun > best[0]:
            best = (-r.fun, r.x); print(f"  start {it}: {best[0]:.5f}", flush=True)
    return best

if __name__ == '__main__':
    planar = sys.argv[1] == 'planar'
    nstart = int(sys.argv[2]); maxiter = int(sys.argv[3])
    ss = [float(v) for v in sys.argv[4:]]
    best = search(ss, planar, nstart, 0, maxiter)
    print(f"RESULT planar={planar} tilts={ss} angles={[round(np.degrees(np.arcsin(v)),2) for v in ss]} best={best[0]:.5f} x={np.round(best[1],4).tolist()}", flush=True)
