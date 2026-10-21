"""Adversarial check of the tilt lemma (Lemma 4.3; Tang, Lemma 5.1).

A unit-square tube with axis w and roll al contains some q in W_c = [0,1]x{c}x[0,1] and
some p in W_1 = [0,1]x{1}x[0,1]  iff  the parallelogram A = {P_w(dx, u, dz) : |dx|,|dz| <= 1}
meets the square 2Q = [-1,1]^2 (coordinates along f1, f2 in w^perp)   (Q - Q = 2Q).
Decided exactly by the separating-axis test (4 axes).  We minimise mu = |w.y| over all
(w, roll) on a dense grid, refine locally, and compare with mu*(u) = (u^2-2)/(u^2+2).
"""
import sys
import numpy as np
from scipy.optimize import minimize


def frames(th, phi, al):
    """vectorised: w (polar th from y, azimuth phi), f1, f2 with roll al."""
    w = np.stack([np.sin(th) * np.cos(phi), np.cos(th), np.sin(th) * np.sin(phi)], -1)
    # reference e1 = w x z normalised (w never parallel to z on our grid: th in [0,pi/2],
    # and w = z only when th = pi/2, phi = pi/2 -- handled by switching reference)
    ref = np.where((np.abs(w[..., 2]) < 0.9)[..., None], np.array([0, 0, 1.0]), np.array([1.0, 0, 0]))
    e1 = np.cross(w, ref)
    e1 /= np.linalg.norm(e1, axis=-1, keepdims=True)
    e2 = np.cross(w, e1)
    ca, sa = np.cos(al)[..., None], np.sin(al)[..., None]
    f1 = ca * e1 + sa * e2
    f2 = -sa * e1 + ca * e2
    return w, f1, f2


def feasible(th, phi, al, u):
    w, f1, f2 = frames(th, phi, al)
    a0 = u * np.stack([f1[..., 1], f2[..., 1]], -1)
    g1 = np.stack([f1[..., 0], f2[..., 0]], -1)
    g2 = np.stack([f1[..., 2], f2[..., 2]], -1)
    ok = np.ones(th.shape, bool)
    axes = [np.broadcast_to(np.array([1.0, 0]), a0.shape), np.broadcast_to(np.array([0, 1.0]), a0.shape),
            np.stack([-g1[..., 1], g1[..., 0]], -1), np.stack([-g2[..., 1], g2[..., 0]], -1)]
    for nu in axes:
        lhs = np.abs((nu * a0).sum(-1))
        rhs = np.abs((nu * g1).sum(-1)) + np.abs((nu * g2).sum(-1)) + np.abs(nu[..., 0]) + np.abs(nu[..., 1])
        ok &= lhs <= rhs + 1e-12
    return ok


def grid_min(u, nth=721, nphi=181, nal=46):
    th = np.linspace(0, np.pi / 2, nth)
    phi = np.linspace(-np.pi, np.pi, nphi)
    al = np.linspace(0, np.pi / 2, nal)
    best, arg = 1.0, None
    for a in al:
        TH, PH = np.meshgrid(th, phi, indexing='ij')
        ok = feasible(TH, PH, np.full(TH.shape, a), u)
        if ok.any():
            mu = np.cos(TH)[ok]
            i = np.argmin(mu)
            if mu[i] < best:
                best, arg = mu[i], (TH[ok][i], PH[ok][i], a)
    return best, arg


def refine(u, arg):
    """maximise th over (th, phi, al) keeping feasibility: for fixed (phi, al) bisect on th
    starting from a feasible th; NM over (phi, al)."""
    def max_th(pa):
        phi, al = pa
        lo = 0.0
        # scan for the largest feasible th on a fine 1-D grid, then bisect
        ths = np.linspace(0, np.pi / 2, 4001)
        ok = feasible(ths, np.full(ths.shape, phi), np.full(ths.shape, al), u)
        if not ok.any():
            return 0.0
        j = np.nonzero(ok)[0].max()
        lo = ths[j]
        hi = ths[min(j + 1, len(ths) - 1)]
        if j == len(ths) - 1:
            return lo
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if feasible(np.array([mid]), np.array([phi]), np.array([al]), u)[0]:
                lo = mid
            else:
                hi = mid
        return lo
    r = minimize(lambda pa: -max_th(pa), np.array(arg[1:]), method='Nelder-Mead',
                 options={'xatol': 1e-10, 'fatol': 1e-13, 'maxiter': 600})
    return np.cos(-r.fun), r.x


for u in [float(a) for a in sys.argv[1:]] or [2.2, 2 + np.sqrt(2), 3.5]:
    m, arg = grid_min(u)
    mr, pa = refine(u, arg)
    ms = (u * u - 2) / (u * u + 2)
    print(f'u = {u:.8f}: grid min mu = {m:.6f}; refined min mu = {mr:.10f}; mu*(u) = {ms:.10f}; '
          f'refined - mu* = {mr - ms:+.2e}; at phi = {pa[0]:.4f}, roll = {pa[1]:.4f}', flush=True)
