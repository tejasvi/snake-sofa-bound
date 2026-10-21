"""Adversarial test of Lemma 3.3: vol(T n T') <= 1/sin(theta) for unit-square tubes.

(1) random general configurations (random rotations, offsets): exact polytope volume
    (qhull) vs the slicing formula (1/sin th) int l(g-r) l'(g-r') dg, and vol*sin(th);
(2) Monte-Carlo cross-check of the qhull volume on a few configurations;
(3) full 12-parameter Nelder-Mead maximization of vol*sin(th) from random starts;
(4) reduced 4-parameter grid (theta, roll, roll', n-offset) on the exact volume.
"""
import os
import sys
import numpy as np
from scipy.optimize import minimize
from scipy.spatial.transform import Rotation
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import tube, box, cat, volume, chord_len, BIG

if not __debug__:
    raise SystemExit("this script relies on assert statements; run it without -O")

rng = np.random.default_rng(2026)
BB = box([-BIG] * 3, [BIG] * 3)


def tube_from(R, rho):
    """T = R(X_w) + rho, X_w = R x [0,1]^2; returns (axis, f1, f2, centre, halfspaces)."""
    e = R @ np.array([1.0, 0, 0])
    f1 = R @ np.array([0, 1.0, 0])
    f2 = R @ np.array([0, 0, 1.0])
    cen = R @ np.array([0, 0.5, 0.5]) + rho
    return e, f1, f2, cen, tube(cen, f1, f2)


def pair_volume(R1, r1, R2, r2):
    e, f1, f2, c1, H1 = tube_from(R1, r1)
    e2, g1, g2, c2, H2 = tube_from(R2, r2)
    st = np.linalg.norm(np.cross(e, e2))
    v = volume(*cat(H1, H2, BB))
    return v, st, (e, f1, f2, c1, e2, g1, g2, c2)


def slicing(geo, ng=20001):
    e, f1, f2, c1, e2, g1, g2, c2 = geo
    n = np.cross(e, e2)
    st = np.linalg.norm(n)
    n /= st
    m = np.cross(n, e)
    m2 = np.cross(n, e2)
    r1, r2 = c1 @ n, c2 @ n
    lo = min(r1, r2) - 0.75
    hi = max(r1, r2) + 0.75
    gs = np.linspace(lo, hi, ng)
    l1 = np.array([chord_len(f1, f2, m, n, g - r1) for g in gs])
    l2 = np.array([chord_len(g1, g2, m2, n, g - r2) for g in gs])
    I = np.trapezoid(l1 * l2, gs) / st
    cs = np.sqrt(np.trapezoid(l1 ** 2, gs) * np.trapezoid(l2 ** 2, gs)) / st
    return I, cs


print('(1) random configurations')
worst_ratio, worst_rel = 0.0, 0.0
nz = 0
for k in range(600):
    R1 = Rotation.random(random_state=rng.integers(1 << 31)).as_matrix()
    R2 = Rotation.random(random_state=rng.integers(1 << 31)).as_matrix()
    r1 = rng.normal(size=3) * 0.4
    r2 = rng.normal(size=3) * 0.4
    v, st, geo = pair_volume(R1, r1, R2, r2)
    if st < 0.15:
        continue
    I, cs = slicing(geo, ng=4001)
    if v > 1e-6:
        nz += 1
        worst_rel = max(worst_rel, abs(I - v) / v)
    worst_ratio = max(worst_ratio, v * st)
    assert I <= cs + 1e-9
print(f'  {nz} nonempty pairs: max rel |slicing - qhull| = {worst_rel:.2e};  max vol*sin(th) = {worst_ratio:.6f}')

print('(2) Monte-Carlo cross-check of qhull volumes')
for k in range(4):
    while True:
        R1 = Rotation.random(random_state=rng.integers(1 << 31)).as_matrix()
        R2 = Rotation.random(random_state=rng.integers(1 << 31)).as_matrix()
        r1, r2 = rng.normal(size=3) * 0.2, rng.normal(size=3) * 0.2
        v, st, geo = pair_volume(R1, r1, R2, r2)
        if st > 0.4 and v > 0.2:
            break
    _, _, _, c1, _, _, _, c2 = geo
    H = cat(tube_from(R1, r1)[4], tube_from(R2, r2)[4])
    # bounding box: the intersection lies within distance sqrt(2)/2 + |chord| of both axes;
    # use a generous cube around the closest-approach point of the axes
    ctr = 0.5 * (c1 + c2)
    L = 1.5 / st + 2.0
    N = 4_000_000
    P = ctr + (rng.uniform(-1, 1, size=(N, 3)) * L)
    inside = np.all(P @ H[0].T <= H[1], axis=1)
    mc = inside.mean() * (2 * L) ** 3
    se = np.sqrt(inside.mean() * (1 - inside.mean()) / N) * (2 * L) ** 3
    # sanity: no inside point at the cube boundary layer
    edge = np.any(np.abs(P[inside] - ctr) > 0.98 * L, axis=1).sum() if inside.any() else 0
    print(f'  qhull {v:.5f}  MC {mc:.5f} +- {se:.5f}  sin {st:.3f}  inside-pts-near-cube-edge {edge}')

print('(3) 12-parameter Nelder-Mead maximisation of vol*sin(theta)')


def negobj(x):
    R1 = Rotation.from_rotvec(x[0:3]).as_matrix()
    R2 = Rotation.from_rotvec(x[6:9]).as_matrix()
    v, st, _ = pair_volume(R1, x[3:6], R2, x[9:12])
    if st < 0.05:
        return 0.0
    return -(v * st)


best = (0, None)
for k in range(int(sys.argv[1]) if len(sys.argv) > 1 else 24):
    x0 = np.concatenate([Rotation.random(random_state=rng.integers(1 << 31)).as_rotvec(), rng.normal(size=3) * 0.3,
                         Rotation.random(random_state=rng.integers(1 << 31)).as_rotvec(), rng.normal(size=3) * 0.3])
    r = minimize(negobj, x0, method='Nelder-Mead', options={'maxiter': 4000, 'maxfev': 4000, 'xatol': 1e-8, 'fatol': 1e-10, 'adaptive': True})
    val = -r.fun
    if val > best[0]:
        best = (val, r.x)
    print(f'  start {k:2d}: max vol*sin = {val:.8f}', flush=True)
print(f'  BEST over starts: {best[0]:.10f}')

print('(4) reduced grid: e=x, e2=(cos th, sin th, 0), rolls a, a2, n-offset d')
gmax = (0, None)
for th in np.linspace(0.2, np.pi / 2, 9):
    for a in np.linspace(0, np.pi / 4, 7):
        for a2 in np.linspace(0, np.pi / 4, 7):
            for d in np.linspace(-0.4, 0.4, 9):
                R1 = Rotation.from_rotvec([a, 0, 0]).as_matrix()
                R2 = Rotation.from_rotvec([0, 0, th]).as_matrix() @ Rotation.from_rotvec([a2, 0, 0]).as_matrix()
                # centre both cross-sections on z = 0 (+ offset d along n = z)
                r1 = -R1 @ np.array([0, 0.5, 0.5])
                r2 = -R2 @ np.array([0, 0.5, 0.5]) + np.array([0, 0, d])
                v, st, _ = pair_volume(R1, r1, R2, r2)
                if v * st > gmax[0]:
                    gmax = (v * st, (th, a, a2, d))
print(f'  grid max vol*sin = {gmax[0]:.8f} at (th, roll, roll2, d) = {np.round(gmax[1], 4)}')
