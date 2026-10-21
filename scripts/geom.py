"""Geometry helpers for the sanity checks.

Convex polytopes are given as half-space lists A p <= b.  Volumes are computed by
qhull (scipy HalfspaceIntersection + ConvexHull) from a Chebyshev-centre interior
point found by linprog.  Floating point; used for exploration and adversarial
search, not as a proof.
"""
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection, ConvexHull

BIG = 200.0


def frame(w, roll):
    """Orthonormal (w, f1, f2) with f1, f2 spanning w^perp, rotated by `roll`."""
    w = np.asarray(w, float)
    w = w / np.linalg.norm(w)
    t = np.array([0.0, 0.0, 1.0]) if abs(w[2]) < 0.9 else np.array([1.0, 0.0, 0.0])
    e1 = np.cross(w, t)
    e1 /= np.linalg.norm(e1)
    e2 = np.cross(w, e1)
    f1 = np.cos(roll) * e1 + np.sin(roll) * e2
    f2 = -np.sin(roll) * e1 + np.cos(roll) * e2
    return w, f1, f2


def tube(rho, f1, f2):
    """Unit-square tube {p : |f1.(p-rho)| <= 1/2, |f2.(p-rho)| <= 1/2}."""
    f1 = np.asarray(f1, float)
    f2 = np.asarray(f2, float)
    rho = np.asarray(rho, float)
    A = np.vstack([f1, -f1, f2, -f2])
    b = np.array([0.5 + f1 @ rho, 0.5 - f1 @ rho, 0.5 + f2 @ rho, 0.5 - f2 @ rho])
    return A, b


def box(lo, hi):
    A = np.vstack([np.eye(3), -np.eye(3)])
    b = np.concatenate([np.asarray(hi, float), -np.asarray(lo, float)])
    return A, b


def cat(*sets):
    return np.vstack([s[0] for s in sets]), np.concatenate([s[1] for s in sets])


# World sets (corridor pieces and the two world tubes, truncated far away)
def SX():
    return box([-BIG, 0, 0], [0, 1, 1])


def stub(c):
    return box([0, 0, 0], [1, c, 1])


def Xw():
    return box([-BIG, 0, 0], [BIG, 1, 1])


def Yw():
    return box([0, -BIG, 0], [1, BIG, 1])


def volume(A, b, tol=1e-10):
    """Volume of {A p <= b} (assumed bounded; callers add a big box if needed)."""
    A = np.asarray(A, float)
    b = np.asarray(b, float)
    norms = np.linalg.norm(A, axis=1)
    # Chebyshev centre: max r s.t. A p + r |A_i| <= b
    c = np.zeros(4)
    c[3] = -1.0
    Aub = np.hstack([A, norms[:, None]])
    res = linprog(c, A_ub=Aub, b_ub=b, bounds=[(None, None)] * 3 + [(0, None)], method="highs")
    if res.status != 0 or res.x[3] < 1e-9:
        return 0.0
    p0 = res.x[:3]
    hs = np.hstack([A, -b[:, None]])
    try:
        hi = HalfspaceIntersection(hs, p0)
        return ConvexHull(hi.intersections).volume
    except Exception:
        return float("nan")


def chord_len(Qf1, Qf2, m, n, b):
    """Length of the chord {a : a m + b n in Q} of the centred unit square
    Q = {|xi.Qf1| <= 1/2, |xi.Qf2| <= 1/2} in the plane span(m, n)."""
    lo, hi = -np.inf, np.inf
    for f in (Qf1, Qf2):
        fm, fn = f @ m, f @ n
        # |a fm + b fn| <= 1/2
        if abs(fm) < 1e-15:
            if abs(b * fn) > 0.5:
                return 0.0
            continue
        a1 = (-0.5 - b * fn) / fm
        a2 = (0.5 - b * fn) / fm
        lo = max(lo, min(a1, a2))
        hi = min(hi, max(a1, a2))
    return max(0.0, hi - lo)
