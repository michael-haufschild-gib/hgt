# Gamma transport forces a complete half-log scattering classification

- **ID:** `suzuki-gamma-homogeneous-half-log-scattering-classification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / EXACT HOMOGENEOUS CORONA CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Input:** `suzuki-gamma-skew-frequency-flux-liouville.md`,
  `suzuki-support-pruned-selfadjoint-seam-carrier.md`

## 1. The exact frequency equation

Let \(X\) be a complex Hilbert space and let \(T\in\mathcal B(X)\) be bounded and self-adjoint.
Put

```text
r(eta)=psi(1+i eta)+psi(1-i eta)+2 EulerGamma
      =2 integral_0^infinity
         [1-cos(eta s)]/(exp(s)-1) ds.                  (1)
```

For real \(\eta\), \(r\) is real, even, nonnegative, and

```text
r(eta)=2 sum_(n>=1) eta^2/[n(n^2+eta^2)].               (2)
```

In particular, \(r\) is strictly increasing on \((0,\infty)\), \(r(0)=r'(0)=0\), and

```text
r(eta)=2 zeta(3) eta^2+O(eta^4)                         (3)
```

at zero.

Consider an \(X\)-valued tempered distribution \(f\) satisfying

```text
-2 eta f'(eta)-f(eta)
 +i eta [r(eta)I-T]f(eta)=0                             (4)
```

in distributions.  This is the exact Fourier equation of

```text
(2L I+R-T)F'(L)+F(L)=0,
f=Fourier(F),                                           (5)
```

with the literal Gamma jump remainder \(R\).

Define the unitary real-frequency transport

```text
Q(eta)
 =exp[(i/2) integral_0^eta r(s)ds] exp[-i eta T/2].      (6)
```

The scalar factor in `(6)` is exactly

```text
exp(i EulerGamma eta)
 [Gamma(1+i eta)/Gamma(1-i eta)]^(1/2),                 (7)
```

with the branch equal to one at zero.

## 2. Distributional classification

### Theorem 1

`[PROVED]` There are unique vectors \(c_+,c_-\in X\) such that, as a locally integrable
tempered function away from zero,

```text
f(eta)= eta^(-1/2)Q(eta)c_+,    eta>0,
f(eta)=(-eta)^(-1/2)Q(eta)c_-,  eta<0.                  (8)
```

There is no additional distribution supported at \(\eta=0\).

### Proof

On either frequency half-line, multiplication of `(4)` by \(-1/(2\eta)\) gives

```text
f'=[-1/(2eta)+(i/2)(rI-T)]f.                            (9)
```

The logarithmic derivative of
\(\eta^{-1/2}Q(\eta)\), respectively \((-\eta)^{-1/2}Q(\eta)\), is exactly the coefficient in
`(9)`.  Standard distributional regularity for a first-order ODE with smooth coefficients makes
the restriction of \(f\) smooth, and multiplication by the inverse propagator makes it constant.
This gives `(8)` and uniqueness of \(c_\pm\).

It remains to exclude a distribution supported at zero.  Such a distribution has finite order,
so it is \(\sum_{j=0}^N v_j\delta_0^{(j)}\).  Since

```text
eta delta_0^(j+1)=-(j+1)delta_0^j,
```

the principal operator in `(4)` sends

```text
delta_0^j -> (2j+1)delta_0^j.
```

The factor \(\eta r(\eta)\) vanishes to order three and \(\eta T\) lowers point-support order, so
the coefficient of the largest nonzero derivative remains \((2N+1)v_N\).  It cannot vanish.
Descending induction gives every \(v_j=0\). `QED`

This is stronger than the previous current theorem: no \(L^2\) hypothesis was used to classify
the homogeneous sector.

## 3. Exact half-log scattering map

Use

```text
F(L)=(1/(2pi)) integral_R f(eta) exp(i eta L)deta        (10)
```

as an oscillatory inverse Fourier integral.  Let

```text
beta(c_+,c_-)
 =1/(2 sqrt(pi))
   [exp(i pi/4)c_+ + exp(-i pi/4)c_-].                  (11)
```

### Theorem 2

`[PROVED]` Every solution `(8)` is represented by a continuous \(X\)-valued function on a
terminal positive \(L\)-half-line and

```text
F(L)=L^(-1/2) beta(c_+,c_-)+O_X(L^(-1))                 (12)
```

as \(L\to+\infty\).  If \(\beta(c_+,c_-)=0\), then

```text
F in L2((L_0,infinity);X).                              (13)
```

No conormality assumption on \(F\) is made: the exact Gamma ODE forces `(12)`.

### Low-frequency proof

Choose an even smooth cutoff \(\chi\) equal to one near zero.  By `(3)` and `(6)`,

```text
Q(eta)=I-i eta T/2+O_B(X)(eta^2)                        (14)
```

near zero; the scalar Gamma phase first changes the expansion at order \(\eta^3\).  The
Fourier--Watson integrals

```text
integral_0^infinity chi(eta) eta^(-1/2) exp(+i eta L)deta
 =sqrt(pi) exp(+i pi/4)L^(-1/2)+O(L^(-3/2)),

integral_0^infinity chi(eta) eta^(-1/2) exp(-i eta L)deta
 =sqrt(pi) exp(-i pi/4)L^(-1/2)+O(L^(-3/2))             (15)
```

give

```text
F_low(L)=L^(-1/2)beta(c_+,c_-)+O_X(L^(-3/2)).           (16)
```

For completeness, `(15)` follows by writing
\(\chi(\eta)=\chi(0)+\eta\chi_1(\eta)\), scaling \(u=L\eta\) in the first term, using
\(\int_0^\infty u^{-1/2}e^{\pm iu}du=\sqrt\pi e^{\pm i\pi/4}\) by Abel damping, and integrating
the compactly supported remainder once.  The operator expansion `(14)` is uniform in norm because
\(T\) is bounded.

### High-frequency proof

The high-frequency remainder is not discarded.  For \(\eta>0\), combine all oscillation into

```text
W_L(eta)
 =exp(i eta L)
  exp[(i/2)integral_0^eta r(s)ds]
  exp(-i eta T/2).                                      (17)
```

It obeys

```text
W_L'
 =i B_L(eta) W_L,
B_L(eta)=[L+r(eta)/2]I-T/2.                             (18)
```

For \(L>\|T\|/2+1\), \(B_L(\eta)\) is positive and

```text
||B_L(eta)^(-1)||<=1/[L-||T||/2].                       (19)
```

The series `(2)` gives \(r'(\eta)>0\) for \(\eta>0\).  Integrating by parts with

```text
W_L=(1/i)B_L^(-1)W_L'
```

on the support of \(1-\chi\), the boundary at infinity vanishes because
\(\eta^{-1/2}/[L+r(\eta)/2]\to0\).  The derivative terms satisfy

```text
integral_epsilon^infinity
 eta^(-3/2)||B_L^(-1)||deta =O(1/L),

integral_epsilon^infinity
 eta^(-1/2) r'(eta)||B_L^(-1)||^2deta
 <=epsilon^(-1/2)
   integral_epsilon^infinity
     r'(eta)/[L-||T||/2+r(eta)/2]^2 deta
 =O(1/L).                                               (20)
```

Hence the positive high-frequency integral is \(O_X(L^{-1})\).  For negative frequency put
\(\eta=-t\); evenness of \(r\) gives the identical estimate.  Combining with `(16)` proves
`(12)`.  When beta vanishes, `(16)` is \(O(L^{-3/2})\) and the two high-frequency pieces are
\(O(L^{-1})\); both are square integrable, proving `(13)`. `QED`

## 4. Sharpness and source meaning

The map `(11)` is the **half-log scattering map** from the two frequency channels to the physical
endpoint trace.  Its kernel is nontrivial:

```text
exp(i pi/4)c_+ + exp(-i pi/4)c_-=0.                     (21)
```

Thus one zero signed trace does not kill a homogeneous distribution.  It does something exact and
previously missing: it moves the homogeneous component from the critical
\(L^{-1/2}\) corona into \(L^2(dL)\).  The Gamma-current Liouville theorem can then kill that
component once the cutoff/forcing decomposition places it in the global \(L^2\) equation.

The exponent is sharp.  Without `(21)`, `(12)` has the nonintegrable square
\(\|\beta\|^2/L\).  With `(21)`, the bound \(O(L^{-1})\) is integrable after squaring.

## 5. Zero trace is exactly upper-strip Hardy gluing

There is a stronger consequence hidden in `(21)`.

### Theorem 3

`[PROVED]` The following are equivalent:

```text
beta(c_+,c_-)=0;
c_-=-i c_+;
the two real-frequency solutions in (8) are boundary values
of one holomorphic solution in 0<Im z<1.                 (23)
```

For this solution and every \(0<\sigma<1\),

```text
f_sigma(x)=f(x+i sigma) belongs to L2(R;X),              (24)
e^(sigma L) F(L) belongs to L2(R;X).                    (25)
```

Thus a zero-trace homogeneous seam has physical decay exponent \(\sigma\) for **every**
\(\sigma<1\), in particular for some \(\sigma>1/2\).  The first possible continuation
obstruction is the literal Gamma pole at \(z=i\).

### Proof

Equation `(11)` gives

```text
beta=0 iff c_-=-exp(i pi/2)c_+=-i c_+.                  (26)
```

Choose the branch of \(z^{-1/2}\) in the upper half-plane with positive boundary value on the
positive real axis.  Its upper boundary value on the negative axis is

```text
(-t+i0)^(-1/2)=-i t^(-1/2).                             (27)
```

The Gamma quotient in `(7)` is nonzero and holomorphic in
\(0<\operatorname{Im}z<1\): its first zero or pole on the upper imaginary axis occurs at
\(z=i\).  Hence

```text
f(z)=z^(-1/2)
     exp(i EulerGamma z)
     [Gamma(1+i z)/Gamma(1-i z)]^(1/2)
     exp(-i z T/2)c_+                                   (28)
```

is holomorphic in that strip.  Equations `(27)` and `(26)` say its two boundary values are
exactly `(8)`.  Conversely, any one holomorphic branch must obey `(27)`, so it forces `(26)`.
This proves `(23)`.

Uniform Stirling asymptotics on every closed substrip
\(0<\sigma_0\leq\operatorname{Im}z\leq\sigma_1<1\) give

```text
|Gamma(1+i(x+i sigma))/Gamma(1-i(x+i sigma))|^(1/2)
 =O_sigma(|x|^(-sigma)).                                (29)
```

Since

```text
||exp(-i(x+i sigma)T/2)||
 <=exp(sigma ||T||/2),                                  (30)
```

formula `(28)` yields

```text
||f(x+i sigma)||=O_sigma(|x|^(-1/2-sigma)).              (31)
```

This is square integrable at both frequency infinities for every \(\sigma>0\), and `(28)` is
bounded on the remaining compact part of the line.  This proves `(24)`.

The Fourier translation identity, first with Abel damping and then by \(L^2\) closure, is

```text
inverseFourier[f(.+i sigma)](L)=e^(sigma L)F(L).         (32)
```

Plancherel turns `(24)` into `(25)`. `QED`

The theorem explains why exponent one appeared in the earlier heuristic.  It is not a guessed
regular power jet: removing the half-log branch at \(z=0\) exposes the next actual singularity of
the exact Gamma transport, located at \(z=i\).  No intermediate homogeneous exponent can occur.

For the support-pruned carrier from
`suzuki-support-pruned-selfadjoint-seam-carrier.md`, take

```text
X=H_a,
T=T_a.
```

Bounded self-adjointness is now unconditional, so Theorems 1--3 close the formerly open abstract
implication

```text
zero half-log trace
 -> homogeneous prime--Gamma seam component lies in
    e^(-sigma L)L2 for every sigma<1.                    (33)
```

What remains source-bearing is not `(33)`: it is construction of the completed-domain
cutoff/forcing decomposition and proof that its particular forcing has corresponding upper-strip
Hardy regularity.  Homogeneous Gamma-strip gate itself is closed.

## 6. Hostile audit

1. **No \(L^2\) premise.**  Theorem 1 starts with a tempered homogeneous solution.  The
   \(L^2\) conclusion appears only after the explicit trace coefficient vanishes.
2. **No discarded high frequency.**  Estimate `(20)` retains the full Gamma phase and bounded
   self-adjoint \(T\).  A low-frequency Watson lemma alone would not control a nonconormal
   high-frequency escape.
3. **No false trace injectivity.**  One trace has kernel `(21)`.  Claiming it kills
   \(c_+,c_-\) would be false.  Its exact positive content is upper-strip gluing `(23)`.
4. **No source-domain assumption hidden in \(X\).**  The theorem applies after an
   \(H_a\)-valued tempered homogeneous component has been constructed.  It does not construct that
   component from Suzuki's completion.
5. **No forced-term deletion.**  Compact cutoff, regular polar terms, and endpoint injection are
   inhomogeneous.  The theorem classifies only the exact homogeneous summand.
6. **No RH claim.**  Forced strip, corona no-return, raw Evans positivity, and all-aperture
   injectivity remain open.

## 7. Novelty audit

The ODE integrating factor, Watson lemma, spectral functional calculus, and one integration by
parts are standard separately.  Corpus search found no prior combination yielding `(11)`--`(22)`
for the literal Suzuki Gamma remainder.  Targeted external searches found logarithmic-Laplacian
Dirichlet theory, extension theory, and generic Wiener--Hopf factorization, but no matching
Gamma-ratio half-log scattering classification.  Priority remains unverified.

## 8. Lean decision

The unconditional algebraic part—regular-singular current, two frequency channels, exact
trace-combination map, and cancellation-to-integrable power law—should be formalized only together
with the oscillatory-integral estimate `(20)`.  Formalizing merely `(21)` would be theorem theatre.
The current formal tree has Bochner integration and improper-integral estimates but no packaged
Hilbert-valued Watson lemma with the operator-valued Gamma propagator.  That infrastructure is now
the exact Lean target; no proposition equivalent to `(13)` will be assumed.
