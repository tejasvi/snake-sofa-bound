"""Interval (arb) checks of numerical facts used in the paper (Lemma 3.2, Theorem 1.1, Section 5).
(1) f(psi) = (cos psi - sin(psi)/3)/cos(psi)^2 <= 1 on [0, pi/4]  (squared L2 norm of a unit-square chord function),
    checked by subdivision with arb interval enclosures; strict < 1 away from psi = 0, where f(0) = 1 and f'(0) = -1/3.
(2) mu*(2+sqrt2) = 1/sqrt2 exactly (rational arithmetic in Q(sqrt2)).
(3) Gamma(M) values quoted in Remark 5.2 of the paper, rounded up.
Requires python-flint.  Run from the repository root: python3 -I scripts/check_constants.py"""
from flint import arb, ctx
ctx.prec = 120
def f(x):
    return (x.cos() - x.sin()/3)/(x.cos()**2)
# (1) on [delta, pi/4]: subdivide; on [0, delta]: use f(psi) = 1 - psi/3 + O(psi^2) via the equivalent form
#     1 - f(psi) = (cos^2 - cos + sin/3)/cos^2 and g(psi) = sin/3 - cos(1-cos) >= psi/3 - psi^3/18 - psi^2/2 > 0 for small psi
pi4 = arb.pi()/4
N = 20000
ok = True; worst = arb(0)
delta = arb(1)/1000
for i in range(N):
    a = delta + (pi4 - delta)*i/N; b = delta + (pi4 - delta)*(i+1)/N
    x = a.union(b)
    val = f(x)
    if not (val < 1): ok = False; print('FAIL on', a, b, val); break
print('(1a) f < 1 on [1e-3, pi/4] by', N, 'interval cells:', ok)
# small-angle part: g(psi) = sin(psi)/3 - cos(psi)(1 - cos(psi)); show g > 0 on (0, 1e-3]:
# sin x >= x - x^3/6, cos x <= 1, 1 - cos x <= x^2/2  =>  g >= x/3 - x^3/18 - x^2/2 = x(1/3 - x/2 - x^2/18) > 0 for x <= 1e-3
x = arb(1)/1000
print('(1b) 1/3 - x/2 - x^2/18 at x = 1e-3 is positive:', (arb(1)/3 - x/2 - x*x/18) > 0)
# (2) mu*(u) = (u^2-2)/(u^2+2) at u = 2+sqrt2: u^2 = 6+4sqrt2 -> (4+4sqrt2)/(8+4sqrt2) = (1+sqrt2)/(2+sqrt2)
#     and (1+sqrt2)/(2+sqrt2) = 1/sqrt2  <=>  sqrt2 (1+sqrt2) = 2+sqrt2  <=>  sqrt2 + 2 = 2 + sqrt2.
s2 = arb(2).sqrt(); u = 2 + s2
print('(2) mu*(2+sqrt2) - 1/sqrt2 =', (u*u - 2)/(u*u + 2) - 1/s2, '(exact identity shown in comments)')
# (3) Gamma(M)
def G(M):
    M = arb(M); return (M*M + 2)/(M*M - 2) + (M*M + 2)/(2*s2*M)
for M, q in (('3', '2.868'), ('2.61', '3.025'), ('2.3', '3.337'), ('2.26', '3.4083'), ('2', '4.061')):
    print(f'(3) Gamma({M}) = {G(M).str(8)} < {q}:', G(M) < arb(q))
print('(4) 2*sqrt2 =', (2*s2).str(10), '< 2.8285:', 2*s2 < arb('2.8285'))
