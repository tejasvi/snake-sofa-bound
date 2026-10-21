"""The squared-chord integral of the unit square (Lemma 3.2), symbolically and numerically.

Square Q centred at 0 with sides along u1=(cos p, sin p), u2=(-sin p, cos p); chords are
taken along m=(1,0) at height b (n=(0,1)).  Claim (proof of Lemma 3.2):
  int l(b)^2 db = (cos p - sin(p)/3)/cos(p)^2 =: f(p) <= 1  for p in [0, pi/4],
and by symmetry for all p.
"""
import sympy as sp
import numpy as np

p, b, t = sp.symbols('p b t', real=True)
c, s = sp.cos(p), sp.sin(p)

# Exact chord on each piece for p in (0, pi/4): from the min/max formula
#   x in [(-1/2 - b s)/c, (1/2 - b s)/c] n [(b c - 1/2)/s, (b c + 1/2)/s]
lo1, hi1 = (-sp.Rational(1, 2) - b*s)/c, (sp.Rational(1, 2) - b*s)/c
lo2, hi2 = (b*c - sp.Rational(1, 2))/s, (b*c + sp.Rational(1, 2))/s
# For 0 <= b <= (c-s)/2: the u1-constraint is binding on both ends -> l = 1/c
# For (c-s)/2 <= b <= (c+s)/2: l = hi1 - lo2
plateau = sp.simplify(hi1 - lo1)
ramp = sp.simplify(hi1 - lo2)
print('plateau chord =', plateau)
print('ramp chord    =', sp.simplify(ramp))
b1, b2 = (c - s)/2, (c + s)/2
print('ramp at b1 - plateau =', sp.simplify(ramp.subs(b, b1) - plateau))
print('ramp at b2           =', sp.simplify(ramp.subs(b, b2)))
# check binding constraints at an interior sample point of each piece, symbolically at p = pi/7
for name, bb in [('plateau', (c - s)/4), ('ramp', (b1 + b2)/2)]:
    vals = [sp.N(e.subs(b, bb).subs(p, sp.pi/7), 30) for e in (lo1, hi1, lo2, hi2)]
    print(name, 'lo1 hi1 lo2 hi2 at p=pi/7:', [round(float(v), 6) for v in vals])

area = 2*(sp.integrate(plateau, (b, 0, b1)) + sp.integrate(ramp, (b, b1, b2)))
print('area =', sp.simplify(area))
I2 = 2*(sp.integrate(plateau**2, (b, 0, b1)) + sp.integrate(ramp**2, (b, b1, b2)))
f_claim = (c - s/3)/c**2
print('int l^2 - claim =', sp.simplify(sp.trigsimp(I2 - f_claim)))

# 1 - f >= 0 on [0, pi/4]: Weierstrass substitution t = tan(p/2)
cw, sw = (1 - t**2)/(1 + t**2), 2*t/(1 + t**2)
num = sp.factor(sp.simplify((cw**2 - cw + sw/3)*(1 + t**2)**2))
print('numerator of 1-f (times (1+t^2)^2), t=tan(p/2):', num)
cubic = sp.Poly(3*t**3 + t**2 - 3*t + 1, t)
print('check num == (2t/3)*cubic:', sp.simplify(num - sp.Rational(2, 3)*t*cubic.as_expr()) == 0)
print('real roots of cubic:', [sp.N(r, 15) for r in sp.real_roots(cubic)])
print('cubic at 0 and at tan(pi/8)=sqrt2-1:', cubic.eval(0), sp.nsimplify(sp.expand(cubic.as_expr().subs(t, sp.sqrt(2) - 1))))
print('f(pi/4) =', sp.nsimplify(sp.simplify(f_claim.subs(p, sp.pi/4))), '=', sp.N(f_claim.subs(p, sp.pi/4)))

# Numerical cross-check over all angles with the brute min/max chord formula
def chord(pp, bb):
    u1 = np.array([np.cos(pp), np.sin(pp)]); u2 = np.array([-np.sin(pp), np.cos(pp)])
    lo, hi = -np.inf, np.inf
    for u in (u1, u2):
        if abs(u[0]) < 1e-14:
            if abs(bb*u[1]) > 0.5:
                return 0.0
            continue
        a1, a2 = (-0.5 - bb*u[1])/u[0], (0.5 - bb*u[1])/u[0]
        lo, hi = max(lo, min(a1, a2)), min(hi, max(a1, a2))
    return max(0.0, hi - lo)

rng = np.random.default_rng(1)
worst = 0.0
fmax = 0.0
for k in range(400):
    pp = rng.uniform(0, 2*np.pi) if k > 3 else [0.0, np.pi/4, np.pi/2, 1.0][k]
    bs = np.linspace(-0.75, 0.75, 30001)
    ls = np.array([chord(pp, bb) for bb in bs])
    I = np.trapezoid(ls**2, bs)
    A = np.trapezoid(ls, bs)
    q = pp % (np.pi/2)
    q = min(q, np.pi/2 - q)
    fc = (np.cos(q) - np.sin(q)/3)/np.cos(q)**2
    worst = max(worst, abs(I - fc), abs(A - 1))
    fmax = max(fmax, I)
print(f'numeric: max |int l^2 - f(folded p)|, |area-1| over 400 angles = {worst:.2e};  max int l^2 = {fmax:.6f}')
