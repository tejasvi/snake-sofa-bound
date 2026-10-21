"""The chain of inequalities in the proof of Theorem 1.1 on the extruded Hammersley sofa
(volume pi/2 + 2/pi), moved by Hammersley's motion through the first turn, then straight up
the middle arm (M = 4).  Notation: SX, Stub(c), X_w, Y_w are S_X, S_Y(c), X, Y of the paper,
and t* is the time t in the proof of Proposition 4.5.

Body frame: strip 0 <= y <= 1 (x 2-D), z in [0,1].  Sofa = {0<=y<=1} n D_r(0,1)^c-notch
n disc(( r,1),1)-envelope n disc((-r,1),1)-envelope, r = 2/pi.
Rotation phase: g_phi(p) = R_phi (p - c(phi)) + (0,1,0), c(phi) = (r cos 2phi, 1 - r sin 2phi, 0),
phi in [0, pi/2]; before: translation in +x from far left; after: translation in +y.
"""
import os
import sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import tube, cat, volume, SX, stub, Xw, Yw

r = 2 / np.pi
YT = 5.0
SQ2 = np.sqrt(2)
h = float(sys.argv[1]) if len(sys.argv) > 1 else 0.01

# body as cell centres of a 2-D grid (z handled analytically: extrusion over [0,1])
xs = np.arange(-(1 + r) + h / 2, 1 + r, h)
ys = np.arange(h / 2, 1, h)
X, Y = np.meshgrid(xs, ys, indexing='ij')
X, Y = X.ravel(), Y.ravel()
inside = (X ** 2 + (Y - 1) ** 2 >= r ** 2)                      # notch removed
inside &= ~((X > r) & ((X - r) ** 2 + (Y - 1) ** 2 > 1))         # right quarter disc
inside &= ~((X < -r) & ((X + r) ** 2 + (Y - 1) ** 2 > 1))        # left quarter disc
Bx, By = X[inside], Y[inside]
area = inside.sum() * h * h
print(f'body area (grid h={h}) = {area:.5f}; exact pi/2 + 2/pi = {np.pi/2 + 2/np.pi:.5f}')


def world(phi):
    c = np.array([r * np.cos(2 * phi), 1 - r * np.sin(2 * phi)])
    cs, sn = np.cos(phi), np.sin(phi)
    px, py = Bx - c[0], By - c[1]
    return cs * px - sn * py, sn * px + cs * py + 1.0


def in_K2(x, y, tol=1e-9):
    # planar section of K (z in [0,1] is automatic for the extrusion)
    return ((x <= tol) & (y >= -tol) & (y <= 1 + tol)) | ((x >= -tol) & (x <= 1 + tol) & (y >= -tol) & (y <= YT + tol))


phis = np.linspace(0, np.pi / 2, 2001)
ok = all(in_K2(*world(p)).all() for p in phis)
My = np.array([world(p)[1].max() for p in phis])
print(f'motion stays in K for all {len(phis)} sampled phi (cell centres): {ok};  max y over the turn = {My.max():.4f}')
x0, y0 = world(0.0)
print(f'at phi=0 body x-range [{x0.min():.3f},{x0.max():.3f}], y-range [{y0.min():.3f},{y0.max():.3f}] (in the entry arm + corner cube; slides in from x=-inf)')

# entry tube T(phi) = g_phi(strip): axis (cos phi, sin phi, 0); mu(phi) = sin(phi); t*: phi = pi/4
ps = np.pi / 4
wx, wy = world(ps)
c = 4.5
print(f'tau_{c}: occurs in the final +y translation (M <= {My.max():.3f} < {c} during the turn), body all in y > 1 there -> case (i), mu(tau) = 1 >= 1/sqrt2')
print(f't*: phi = pi/4, mu = {np.sin(ps):.6f}; M(t*) = {wy.max():.4f} <= c; min y = {wy.min():.4f}')
inSX = (wx <= 0) & (wy >= 0) & (wy <= 1)
inST = (wx >= 0) & (wx <= 1) & (wy >= 0) & (wy <= c)
print(f'all cells in SX u Stub(c) at t*: {bool((inSX | inST).all())};  area split: SX {inSX.sum()*h*h:.4f}, Stub {inST.sum()*h*h:.4f}')
cc = np.array([r * np.cos(2 * ps), 1 - r * np.sin(2 * ps), 0.0])
R = np.array([[np.cos(ps), -np.sin(ps), 0], [np.sin(ps), np.cos(ps), 0], [0, 0, 1]])
f1, f2 = R @ np.array([0, 1.0, 0]), R @ np.array([0, 0, 1.0])
cen = R @ (np.array([0, 0.5, 0.5]) - cc) + np.array([0, 1.0, 0])
T = tube(cen, f1, f2)
# check body cells inside T (z = 0.5 representative; T is a z-extrusion here)
P3 = np.stack([wx, wy, np.full_like(wx, 0.5)], 1)
print(f'all cells in T(t*): {bool(np.all(P3 @ T[0].T <= T[1] + 1e-9))}')
v_sx, v_st = volume(*cat(T, SX())), volume(*cat(T, stub(c)))
v_x, v_y = volume(*cat(T, Xw())), volume(*cat(T, Yw()))
print(f'vol B = {area:.4f} <= vol(T n SX) + vol(T n Stub) = {v_sx:.4f} + {v_st:.4f} = {v_sx + v_st:.4f}'
      f' <= vol(T n X_w) + vol(T n Y_w) = {v_x:.4f} + {v_y:.4f} = {v_x + v_y:.4f} <= 2 sqrt2 = {2*SQ2:.4f}')
