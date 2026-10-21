"""Convex polytope volume from half-spaces A x <= b (exploratory float code, not rigorous).
Helper for multi_ev.py and multi_ev2.py."""
import numpy as np
from itertools import combinations
from scipy.spatial import ConvexHull

_comb_cache = {}
def _combs(m):
    if m not in _comb_cache:
        _comb_cache[m] = np.array(list(combinations(range(m), 3)), dtype=int)
    return _comb_cache[m]

def vertices(A, b, tol=1e-9):
    m = len(b)
    C = _combs(m)
    M = A[C]                      # (K,3,3)
    rhs = b[C]                    # (K,3)
    det = np.linalg.det(M)
    ok = np.abs(det) > 1e-12
    if not ok.any(): return np.zeros((0, 3))
    X = np.linalg.solve(M[ok], rhs[ok][..., None])[..., 0]
    feas = np.all(X @ A.T <= b + tol*(1 + np.abs(b)), axis=1)
    return X[feas]

def volume(A, b):
    V = vertices(A, b)
    if len(V) < 4: return 0.0
    try:
        return ConvexHull(V).volume
    except Exception:
        return 0.0

# ---- basic sets as half-space lists ----
BIG = 60.0
def box(lo, hi):
    A = np.vstack([np.eye(3), -np.eye(3)]); b = np.concatenate([np.array(hi, float), -np.array(lo, float)])
    return A, b

def SX():   return box([-BIG, 0, 0], [0, 1, 1])
def stub(c): return box([0, 0, 0], [1, c, 1])
def SY(yt): return box([0, 0, 0], [1, yt, 1])

def tube(rho, f1, f2):
    # |f_i.(p-rho)| <= 1/2
    A = np.vstack([f1, -f1, f2, -f2]); b = np.array([0.5 + f1@rho, 0.5 - f1@rho, 0.5 + f2@rho, 0.5 - f2@rho])
    return A, b

def transform(Ab, R, t):
    # image of {A x <= b} under p -> R p + t : {A R^T (q - t) <= b}
    A, b = Ab
    A2 = A @ R.T
    return A2, b + A2 @ t

def cat(*sets):
    return np.vstack([s[0] for s in sets]), np.concatenate([s[1] for s in sets])

def rotmat(axis, ang):
    axis = np.asarray(axis, float); axis = axis/np.linalg.norm(axis)
    K = np.array([[0, -axis[2], axis[1]], [axis[2], 0, -axis[0]], [-axis[1], axis[0], 0]])
    return np.eye(3) + np.sin(ang)*K + (1 - np.cos(ang))*K@K

if __name__ == '__main__':
    # tests: unit cube
    print(volume(*box([0,0,0],[1,1,1])))
    # two perpendicular aligned unit tubes -> unit cube volume 1
    X = tube(np.array([0,.5,.5]), np.array([0,1.,0]), np.array([0,0,1.]))
    Y = tube(np.array([.5,0,.5]), np.array([1.,0,0]), np.array([0,0,1.]))
    print(volume(*cat(X, Y, box([-BIG]*3,[BIG]*3))))
    # tube at 45 deg in xy-plane with SX: should be 1/sin45 * ... check against slicing
