"""The chain of inequalities in the proof of Theorem 1.1 on a concrete motion through both
turns: the 512-pose record path from Tang's repository.

Body: carve of the block [-4,0]x[0,1]^2 (body frame) along the path, motion = piecewise
linear translation + slerp rotation between the 512 recorded poses, SUB sub-steps each.
Pose convention (from the docstring of the path in Tang's repository; checked here on the
endpoint poses): R = Rotation.from_euler('zyx', [yaw,pitch,roll], degrees=True), world = R body + t.
Usage: python -I record_path.py PATH_TO_NPY [h] [SUB]
Notation: SX, Stub(c), X_w, Y_w are S_X, S_Y(c), X, Y of the paper, tau_c is the time tau of
Lemma 4.2, and t* is the time t in the proof of Proposition 4.5.
"""
import os
import sys
import numpy as np
from scipy.spatial.transform import Rotation, Slerp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import tube, cat, volume, SX, stub, Xw, Yw

if not __debug__:
    raise SystemExit("this script relies on assert statements; run it without -O")

path = sys.argv[1]
h = float(sys.argv[2]) if len(sys.argv) > 2 else 0.025
SUB = int(sys.argv[3]) if len(sys.argv) > 3 else 6
YT = 5.0
SQ2 = np.sqrt(2.0)

P = np.load(path, allow_pickle=False)
assert P.ndim == 2 and P.shape[1] == 6 and np.isfinite(P).all()
print('poses', P.shape, 'start', P[0], 'end', P[-1])
R_all = Rotation.from_euler('zyx', P[:, 3:], degrees=True)
T_all = P[:, :3]


def in_K(W, tol=0.0):
    x, y, z = W[:, 0], W[:, 1], W[:, 2]
    m1 = (x <= tol) & (y >= -tol) & (y <= 1 + tol) & (z >= -tol) & (z <= 1 + tol)
    m2 = (x >= -tol) & (x <= 1 + tol) & (y >= -tol) & (y <= YT + tol) & (z >= -tol) & (z <= 1 + tol)
    m3 = (x >= -tol) & (x <= 1 + tol) & (y >= YT - tol) & (y <= YT + 1 + tol) & (z >= -tol)
    return m1 | m2 | m3


corners = np.array([[x, y, z] for x in (-4, 0) for y in (0, 1) for z in (0, 1)], float)
W0 = corners @ R_all[0].as_matrix().T + T_all[0]
W1 = corners @ R_all[-1].as_matrix().T + T_all[-1]
print('start block in SX:', bool(np.all((W0[:, 0] <= 1e-9) & (W0[:, 1] >= -1e-9) & (W0[:, 1] <= 1 + 1e-9) & (W0[:, 2] >= -1e-9) & (W0[:, 2] <= 1 + 1e-9))))
print('end block in SZ  :', bool(np.all((W1[:, 0] >= -1e-9) & (W1[:, 0] <= 1 + 1e-9) & (W1[:, 1] >= YT - 1e-9) & (W1[:, 1] <= YT + 1 + 1e-9) & (W1[:, 2] >= -1e-9))))

# interpolated motion: times s in [0, 511], SUB sub-steps per segment
n = len(P)
times = np.linspace(0, n - 1, (n - 1) * SUB + 1)
slerp = Slerp(np.arange(n), R_all)


def pose(s):
    s = np.atleast_1d(s)
    Rm = slerp(s).as_matrix()
    i = np.clip(np.floor(s).astype(int), 0, n - 2)
    fr = (s - i)[:, None]
    tt = (1 - fr) * T_all[i] + fr * T_all[i + 1]
    return Rm, tt


Rm, tt = pose(times)
# carve
xs = np.arange(-4 + h / 2, 0, h)
ys = np.arange(h / 2, 1, h)
G = np.stack(np.meshgrid(xs, ys, ys, indexing='ij'), axis=-1).reshape(-1, 3)
alive = np.ones(len(G), bool)
for k in range(len(times)):
    idx = np.nonzero(alive)[0]
    Wp = G[idx] @ Rm[k].T + tt[k]
    alive[idx[~in_K(Wp)]] = False
B = G[alive]
volB = alive.sum() * h ** 3
print(f'carved body: {len(B)} cell centres, h = {h}, SUB = {SUB}, volume ~ {volB:.4f}')

w = Rm @ np.array([1.0, 0, 0])           # entry-tube axis w(t) = R_t R_0^{-1} x (R_0 = I)
mu = np.abs(w[:, 1])
My = np.array([(B @ Rm[k].T + tt[k])[:, 1].max() for k in range(len(times))])
my = np.array([(B @ Rm[k].T + tt[k])[:, 1].min() for k in range(len(times))])
print(f'M(0) = {My[0]:.4f}, M(end) = {My[-1]:.4f}, mu(0) = {mu[0]:.2e}')


def tube_at(Rk, tk):
    f1 = Rk @ np.array([0, 1.0, 0])
    f2 = Rk @ np.array([0, 0, 1.0])
    cen = Rk @ np.array([0, 0.5, 0.5]) + tk
    return tube(cen, f1, f2)


def mu_star(u):
    return (u * u - 2) / (u * u + 2)


print('\n-- events: tilt lemma / case split at tau_c --')
for c in [2.5, 3.0, 3.5, 4.0, 4.5, 4.9]:
    u = c - 1
    k = int(np.argmax(My >= c))
    case = 'ii (meets y<=1)' if my[k] <= 1 else 'i (all y>1)'
    need = mu_star(u) if my[k] <= 1 else (1 / SQ2 if volB > SQ2 else 0)
    print(f'c = {c}: tau index {k} (t = {times[k]:.3f}), M = {My[k]:.4f}, min y = {my[k]:.4f}, case {case}, '
          f'mu(tau) = {mu[k]:.4f}, required >= {need:.4f}: {"PASS" if mu[k] >= need else "FAIL"}')

print('\n-- t*: first time mu >= 1/sqrt2, refined by bisection on the slerp parameter --')
k1 = int(np.argmax(mu >= 1 / SQ2))
lo, hi = times[k1 - 1], times[k1]
for _ in range(60):
    mid = 0.5 * (lo + hi)
    Rmid, _t = pose(mid)
    if abs((Rmid[0] @ np.array([1.0, 0, 0]))[1]) >= 1 / SQ2:
        hi = mid
    else:
        lo = mid
ts = hi
Rs, tsv = pose(ts)
Rs, tsv = Rs[0], tsv[0]
ws = Rs @ np.array([1.0, 0, 0])
Bs = B @ Rs.T + tsv
print(f't* = {ts:.6f}; w(t*) = {np.round(ws, 6)}; |w.y| = {abs(ws[1]):.9f}; |w.x| = {abs(ws[0]):.6f}')
print(f'M(t*) = {Bs[:, 1].max():.4f} (must be <= c for every c in (3+sqrt2, 5)); min y = {Bs[:, 1].min():.4f}')
c = 4.5
inSX = (Bs[:, 0] <= 0) & (Bs[:, 1] >= 0) & (Bs[:, 1] <= 1) & (Bs[:, 2] >= 0) & (Bs[:, 2] <= 1)
inST = (Bs[:, 0] >= 0) & (Bs[:, 0] <= 1) & (Bs[:, 1] >= 0) & (Bs[:, 1] <= c) & (Bs[:, 2] >= 0) & (Bs[:, 2] <= 1)
bad = ~(inSX | inST)
if bad.any():
    # distance outside SX u Stub(c) (box distance) for the offenders
    def boxdist(Pp, lo_, hi_):
        d = np.maximum(np.maximum(lo_ - Pp, 0), np.maximum(Pp - hi_, 0))
        return np.linalg.norm(d, axis=1)
    dd = np.minimum(boxdist(Bs[bad], np.array([-1e9, 0, 0]), np.array([0, 1, 1])), boxdist(Bs[bad], np.array([0, 0, 0]), np.array([1, c, 1])))
    print(f'cells outside SX u Stub({c}) at t*: {bad.sum()} (max distance {dd.max():.2e}; interpolation artefact if tiny)')
else:
    print(f'all carved cells lie in SX u Stub({c}) at t*')
T = tube_at(Rs, tsv)
A_T, b_T = T
inT = np.all(Bs @ A_T.T <= b_T + 1e-9, axis=1)
print(f'all carved cells in T(t*): {bool(inT.all())}')
v_sx = volume(*cat(T, SX()))
v_st = volume(*cat(T, stub(c)))
v_x = volume(*cat(T, Xw()))
v_y = volume(*cat(T, Yw()))
sx_, sy_ = np.sqrt(1 - ws[0] ** 2), np.sqrt(1 - ws[1] ** 2)
print(f'vol B ~ {volB:.4f} <= vol(T n SX) + vol(T n Stub) = {v_sx:.4f} + {v_st:.4f} = {v_sx + v_st:.4f}')
print(f'   <= vol(T n X_w) + vol(T n Y_w) = {v_x:.4f} + {v_y:.4f} = {v_x + v_y:.4f}')
print(f'   <= 1/sin th_x + 1/sin th_y = {1/sx_:.4f} + {1/sy_:.4f} = {1/sx_ + 1/sy_:.4f} <= 2 sqrt2 = {2*SQ2:.4f}')
print(f'   carved mass split at t*: in SX {inSX.sum()*h**3:.4f}, in Stub {inST.sum()*h**3:.4f}')
