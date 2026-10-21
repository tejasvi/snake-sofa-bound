"""The single-pose relaxation of Proposition 6.1 (the time t in the proof of Proposition 4.5).

For a unit-square tube T with axis w, |w.y| = s:
  V1 = vol(T n SX) + vol(T n Stub(c))      (what the body can occupy at t*)
  V2 = vol(T n X_w) + vol(T n Y_w)         (what the proof bounds)
  bound = 1/sin(th_x) + 1/sin(th_y)        (Lemma 3.3 twice)  <=  1/s + 1/sqrt(1-s^2)
Checks V1 <= V2 <= bound on random tubes (all s), and maximises V1 at s = 1/sqrt2 over
(azimuth phi of w about y, roll, centre offsets) with c = 4.5 (u = 3.5, M = 4).
Notation: SX, Stub(c), X_w, Y_w are S_X, S_Y(c), X, Y of the paper, and t* is the time t in
the proof of Proposition 4.5.
"""
import os
import sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import frame, tube, cat, volume, SX, stub, Xw, Yw

C = 4.5
rng = np.random.default_rng(11)


def tube_s(s, phi, roll, a, b):
    th = np.arccos(s)
    w = np.array([np.sin(th) * np.cos(phi), np.cos(th), np.sin(th) * np.sin(phi)])
    w, f1, f2 = frame(w, roll)
    rho = np.array([a, 0.5, b])   # every tube with w.y != 0 has a centre-line point with y = 1/2
    return w, tube(rho, f1, f2)


def vols(w, T):
    v_sx = volume(*cat(T, SX()))
    v_st = volume(*cat(T, stub(C)))
    v_x = volume(*cat(T, Xw()))
    v_y = volume(*cat(T, Yw()))
    bd = 1 / np.sqrt(1 - w[0] ** 2) + 1 / np.sqrt(1 - w[1] ** 2)
    return v_sx + v_st, v_x + v_y, bd


print('random tubes, all tilts: check V1 <= V2 <= bound')
viol = 0
worst = 0.0
for k in range(1500):
    s = rng.uniform(0.15, 0.95)
    w, T = tube_s(s, rng.uniform(-np.pi, np.pi), rng.uniform(0, np.pi / 2), rng.uniform(-2.5, 1.5), rng.uniform(-0.5, 1.5))
    V1, V2, bd = vols(w, T)
    if V1 > V2 + 1e-7 or V2 > bd + 1e-7:
        viol += 1
    worst = max(worst, V2 / bd)
print(f'  violations: {viol};  max V2/bound = {worst:.6f}')

s0 = 1 / np.sqrt(2)


def neg(x):
    w, T = tube_s(s0, *x)
    v1 = volume(*cat(T, SX())) + volume(*cat(T, stub(C)))
    return -v1


best = (0, None)
nst = int(sys.argv[1]) if len(sys.argv) > 1 else 40
for k in range(nst):
    x0 = np.array([rng.uniform(-np.pi, np.pi), rng.uniform(0, np.pi / 2), rng.uniform(-2.5, 1.0), rng.uniform(-0.3, 1.3)])
    r = minimize(neg, x0, method='Nelder-Mead', options={'maxiter': 3000, 'xatol': 1e-9, 'fatol': 1e-11, 'adaptive': True})
    if -r.fun > best[0]:
        best = (-r.fun, r.x)
    print(f'  start {k:2d}: V1 = {-r.fun:.8f}  x = {np.round(r.x, 4)}', flush=True)
w, T = tube_s(s0, *best[1])
V1, V2, bd = vols(w, T)
print(f'MAX V1 at s=1/sqrt2: {best[0]:.10f}  (2 sqrt2 = {2*np.sqrt(2):.10f});  at optimum V2 = {V2:.8f}, bound = {bd:.8f}, w = {np.round(w, 6)}')

print('sweep: max V1 over tubes with |w.y| = s (12 starts each) vs 1/s + 1/sqrt(1-s^2)')
for s in [0.3, 0.5, 0.6, 0.65, 0.7, 0.75, 0.8, 0.9]:
    bb = 0
    for k in range(12):
        x0 = np.array([rng.uniform(-np.pi, np.pi), rng.uniform(0, np.pi / 2), rng.uniform(-3.5, 1.0), rng.uniform(-0.3, 1.3)])
        f = lambda x: -(volume(*cat(tube_s(s, *x)[1], SX())) + volume(*cat(tube_s(s, *x)[1], stub(C))))
        r = minimize(f, x0, method='Nelder-Mead', options={'maxiter': 2000, 'xatol': 1e-8, 'fatol': 1e-10, 'adaptive': True})
        bb = max(bb, -r.fun)
    print(f'  s = {s:.3f}: max V1 = {bb:.6f}   planar bound = {1/s + 1/np.sqrt(1-s*s):.6f}', flush=True)
