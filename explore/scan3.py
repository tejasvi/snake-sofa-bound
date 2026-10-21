"""Planar values of the several-time relaxation of Remark 6.3 with natural orientations (same rotation sense,
no reflection, no axis reversal), stub height c = C_STUB = 5.0 from planar2d.py: best local maximum found by
Nelder-Mead from 25 random starts (seed 0).
Exploratory float code, not rigorous.  Usage: python3 -I explore/scan3.py 51,30 51,38,22 ...  (angles in degrees)
"""
import numpy as np, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from planar2d import Qmat, thetas, objective
from scipy.optimize import minimize
def best_natural(angs, nstart=25, seed=0):
    ss = [np.sin(np.radians(a)) for a in angs]
    Qs = [Qmat(thetas(s)[1], False) for s in ss]
    rng = np.random.default_rng(seed); best = (0, None)
    for it in range(nstart):
        r = minimize(objective, rng.uniform(-3, 3, 2*len(ss)-1), args=(Qs,), method='Nelder-Mead',
                     options={'maxiter': 4000, 'xatol': 1e-7, 'fatol': 1e-9, 'adaptive': True})
        if -r.fun > best[0]: best = (-r.fun, r.x)
    return best
combos = [tuple(float(v) for v in c.split(',')) for c in sys.argv[1:]]
for c in combos:
    b = best_natural(c)
    print(f"angles={c} best local maximum found (natural orientation) = {b[0]:.5f}", flush=True)
