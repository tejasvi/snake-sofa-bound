"""Tighter Monte-Carlo cross-check of qhull two-tube volumes (bounding box from the
qhull vertices, enlarged by 25%, with a check that no sample inside the polytope lies in
the outer 5% shell of the box)."""
import os
import sys
import numpy as np
from scipy.spatial.transform import Rotation
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import tube, cat, volume

rng = np.random.default_rng(99)
for k in range(6):
    while True:
        R1 = Rotation.random(random_state=rng.integers(1 << 31)).as_matrix()
        R2 = Rotation.random(random_state=rng.integers(1 << 31)).as_matrix()
        r1, r2 = rng.normal(size=3) * 0.25, rng.normal(size=3) * 0.25
        H = []
        for R, rr in ((R1, r1), (R2, r2)):
            H.append(tube(R @ np.array([0, 0.5, 0.5]) + rr, R @ np.array([0, 1.0, 0]), R @ np.array([0, 0, 1.0])))
        A, b = cat(*H)
        st = np.linalg.norm(np.cross(R1[:, 0], R2[:, 0]))
        v = volume(A, b)
        if st > 0.3 and v > 0.2:
            break
    norms = np.linalg.norm(A, axis=1)
    res = linprog([0, 0, 0, -1], A_ub=np.hstack([A, norms[:, None]]), b_ub=b, bounds=[(None, None)] * 3 + [(0, None)], method='highs')
    V = HalfspaceIntersection(np.hstack([A, -b[:, None]]), res.x[:3]).intersections
    lo, hi = V.min(0), V.max(0)
    mid, half = 0.5 * (lo + hi), 0.5 * (hi - lo) * 1.25
    N, cnt, shell = 0, 0, 0
    for _ in range(8):
        P = mid + rng.uniform(-1, 1, size=(2_000_000, 3)) * half
        ins = np.all(P @ A.T <= b, axis=1)
        cnt += ins.sum()
        N += len(P)
        shell += np.any(np.abs(P[ins] - mid) > 0.95 * half, axis=1).sum()
    boxv = np.prod(2 * half)
    p = cnt / N
    print(f'qhull {v:.5f}   MC {p*boxv:.5f} +- {np.sqrt(p*(1-p)/N)*boxv:.5f}   (sin th {st:.3f}, inside samples in outer shell: {shell})', flush=True)
