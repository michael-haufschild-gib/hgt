# Theta-cusp Gaussian-aperture composite balance

- **ID:** `theta-cusp-gaussian-aperture-composite-balance`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE + THEOREM (paper) + THEOREM (Lean)
- **Scientific status:** `[NEW CANDIDATE MECHANISM] [LITERATURE NONCOLLISION] [NOT AN RH PROOF]`
- **Replaces as immediate target:** the two separate sufficient ratio gates and their two opposite
  first-atom window estimates.  Those gates remain correct sufficient conditions, but they are not
  the native source condition.
- **Statement:** Gaussian damping of the completed theta source produces one source-derived
  infinite Hilbert contraction.  The first nonconstant prime--Gamma Hankel gate is exactly the
  nonnegativity of one boundary composite Turan curvature along this aperture.

## Anti-theatre verdict

The Gaussian-deformed moments themselves are classical.  Csordas--Varga already studied

```text
b_j(lambda)=integral_0^infinity x^(2*j) exp(lambda*x^2) Phi(x) dx
```

and proved the ordinary weighted Turan inequalities for every real `lambda`.  The strict
concavity of `log Phi(sqrt(y))`, Gaussian deformation, and positivity of the separate defects are
therefore **not new** and are not claimed here.

The candidate surviving exact source and literature search is different:

```text
3*b_2*D_1-b_0*D_2,
D_1=b_1^2-(1/3)*b_0*b_2,
D_2=b_2^2-(3/5)*b_1*b_3.                               (1)
```

Equivalently, after gamma normalization, it is additive convexity of the first three consecutive
moment ratios, not ordinary log-concavity and not the classical double Turan inequality.  Exact
searches for `(1)`, the corresponding ratio curvature, and the multiplicative aperture functional
below found no primary-literature collision.  This is search noncollision, not a priority claim.

## The actual infinite contraction `[PROVED ON PAPER]`

Let `Phi=thetaCuspFullSource` on the positive half-line and, for `L>=0`, define

```text
(C_L u)(x)=exp(-L*x^2/2)*u(x)
```

on `L^2((0,infinity),Phi(x)dx)`.  Then

```text
||C_L u||^2
 = integral exp(-L*x^2)*|u(x)|^2*Phi(x) dx
 <= ||u||^2,
C_L C_M=C_(L+M).                                        (2)
```

This is a source-derived, height-localized, infinite-dimensional contraction.  It does not extend
an estimate to an HT-saturated source span and it does not sharpen a Fourier window past the
critical resolution boundary.  Its polynomial Gram entries are the completed aperture moments

```text
B_j(L)=2*integral_0^infinity
  x^(2*j)*exp(-L*x^2)*Phi(x) dx.                        (3)
```

Lean defines `(3)` as `thetaCuspGaussianApertureMoment (-L) j`.

## Exact unsplit source gate `[PROVED ON PAPER] [PROVED IN LEAN]`

Put `m_j=B_j(0)=thetaCuspRawEvenMoment j` and

```text
mu_j=m_(j+1)/m_j.
```

The raw source cubic has the exact factorization

```text
Q=3*m_0*m_1*m_3+15*m_1^2*m_2-10*m_0*m_2^2
 =m_0*m_1*m_2*(3*mu_2+15*mu_0-10*mu_1).                (4)
```

Since `m_0*m_1*m_2>0`, the first nonconstant prime--Gamma source Hankel condition is equivalent to
the single direct balance

```text
10*mu_1 <= 15*mu_0+3*mu_2.                             (5)
```

This is strictly weaker than requiring both old ratio gates.  It is an exact replacement, not a
new sufficient wrapper.

The same cubic is exactly

```text
Q=5*(3*m_2*D_1-m_0*D_2).                               (6)
```

If

```text
c_j(lambda)=b_j(lambda)/Gamma(j+1/2),
q_j(lambda)=c_(j+1)(lambda)/c_j(lambda),
```

then

```text
3*b_3/b_2+15*b_1/b_0-10*b_2/b_1
 =(15/2)*(q_0-2*q_1+q_2).                              (7)
```

Thus the missing property is the **boundary additive curvature of the gamma-normalized moment
ratios**.  Classical Turan theory only proves that `q_0>=q_1>=q_2`; it does not prove `(7)`.

Permanent Lean module:

```text
formal/GaloisForLFunctions/RHTower/PrimeArchThetaGaussianApertureBalance.lean
```

It defines the actual aperture moments, their multiplicative composite, the additive balance, and
the sixth-seam numerator, and proves `(4)`--`(6)`, the zero-aperture specialization, and the exact
equivalence of `(5)` with every real linear-polynomial prime--Gamma source Hankel test.

## One composite curvature window `[PROVED ON PAPER]`

For the tilted density

```text
f_lambda(x)=exp(lambda*x^2)*Phi(x),
V_lambda=-log(f_lambda),
E(x)=d/dx (V_lambda'(x)/x),
```

Gaussian tilt changes `V'(x)/x` only by the constant `-2*lambda`.  Therefore `E` is independent
of `lambda`.  The classical strict concavity of `log Phi(sqrt(y))` says exactly that `E(x)>0` for
`x>0`.

For the positive crossing windows

```text
K_(m,lambda)(t)
 =integral_(0<u<t<v)
    u^(2*m)*v^(2*m)*(v^2-u^2)*f_lambda(u)*f_lambda(v) du dv,
```

the slope-curvature identity gives

```text
D_(m,lambda)=1/(2*m+1)*integral E(t)*K_(m,lambda)(t) dt.
```

Combining the two adjacent defects before estimating them gives the exact single-window identity

```text
Q(lambda)/5
 =integral_0^infinity E(t)*L_lambda(t) dt,              (8)

L_lambda(t)
 =B_2(lambda)*K_(1,lambda)(t)
   -(B_0(lambda)/5)*K_(2,lambda)(t).                   (9)
```

The old route asked for two estimates of opposite orientation on `K_1` and `K_2`.  Equations
`(8)`--`(9)` show that only their forced composite is consumed.  Pointwise positivity is not the
target; the target is its exact balance against the fixed positive source curvature `E`.

## Exact one-crossing law `[PAPER-PROVED] [LEAN-PROVED]`

The sign geometry of the forced window is no longer conjectural.  Put

```text
M_j=B_j(lambda)/2,
A_j(t)=integral_0^t x^(2j) f_lambda(x) dx.
```

Fubini cancellation inside the crossing window gives

```text
K_(m,lambda)(t)=A_m(t)M_(m+1)-A_(m+1)(t)M_m,
K_(m,lambda)'(t)=f_lambda(t)t^(2m)(M_(m+1)-t^2 M_m).   (9a)
```

Consequently the composite derivative collapses exactly to

```text
L_lambda'(t)=2 f_lambda(t)t^2 P_lambda(t^2),

P_lambda(y)=M_2^2-(M_1 M_2+M_0 M_3/5)y+(M_0 M_2/5)y^2. (9b)
```

The discriminant of `P_lambda` is nonnegative by the ordinary source log-convexity
`M_2^2<=M_1 M_3`: writing `u=M_1 M_2` and `v=M_0 M_3/5`,

```text
(u+v)^2 >= 4uv >= 4(M_0 M_2/5)M_2^2.
```

It is in fact strictly positive.  If it vanished, `(9b)` would be a positive multiple of a
square, so `L_lambda` would be nondecreasing on the positive half-line.  But the exact endpoint
laws are

```text
L_lambda(0)=0,
lim_(t->infinity) L_lambda(t)=0,
```

while `(9b)` makes `L_lambda` strictly positive at an explicit source-derived small height.  This
is impossible.  Hence `P_lambda` has two distinct positive roots `r_-<r_+`; the derivative signs
are

```text
L_lambda'(t)>0  for 0<t<sqrt(r_-),
L_lambda'(t)<0  for sqrt(r_-)<t<sqrt(r_+),
L_lambda'(t)>0  for sqrt(r_+)<t.                         (9c)
```

The first turning value is positive and the second is negative because the final increasing tail
converges to zero.  Thus `L_lambda` has exactly one positive zero, lying strictly between the two
turning heights, for every `lambda<=0`.

Permanent Lean module
`PrimeArchThetaGaussianApertureCompositeWindow.lean` constructs the literal tilted theta density,
moment prefixes, crossing windows, and forced composite.  It proves `(9a)`--`(9c)`, strict
discriminant positivity, the two turning-value signs, and the global unique-positive-zero theorem
without extra hypotheses.  The result removes the former one-crossing open core; it does not by
itself sign the curvature-weighted integral `(8)`.  Its direct leaf check and exact module build
pass; the derivative, strict-discriminant, three-phase, and global one-crossing capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Completed seam cancellation and the first possible aperture sign

The dominant first atom has the positive boundary logarithmic slope

```text
s_1=9/2-2*pi+6/(2*pi-3)>0.                             (10)
```

Lean proves both `(10)` and

```text
Phi_1'(0)=s_1*Phi_1(0).
```

But using `(10)` as the completed-source boundary sign is false: modular reflection makes the full
source even, so all higher atoms cancel the first derivative exactly.

Let

```text
f_(2k)=Phi^(2k)(0),
N_6=f_0^2*f_6-15*f_0*f_2*f_4+30*f_2^3.                (11)
```

Taylor expansion at the seam followed by Watson's lemma gives, as `L->infinity`,

```text
B_j(L)
 =sum_(k=0)^3 [f_(2k)/(2k)!]
    Gamma(j+k+1/2)*L^(-j-k-1/2)
   +O(L^(-j-9/2)).                                     (12)
```

Substitution into the additive aperture balance cancels the universal Gaussian terms through
orders `L^-1`, `L^-2`, and `L^-3`, leaving

```text
3*B_3/B_2+15*B_1/B_0-10*B_2/B_1
 =N_6/(16*f_0^3)*L^-4+O(L^-5)
 =((log Phi)^(6)(0)/16)*L^-4+O(L^-5).                 (13)
```

Proof of `(12)`--`(13)`: split the integral at a fixed small `delta`; Taylor-expand the smooth even
source through order six with an order-eight remainder on `[0,delta]`; scale `x=y/sqrt(L)`; the
tail is smaller than every displayed power by the Gaussian factor.  The gamma recurrence reduces
the three ratios.  The coefficient identities

```text
15*(1/2)-10*(3/2)+3*(5/2)=0,
15*(1/2)^2-10*(3/2)^2+3*(5/2)^2=0,
15*(1/2)^3-10*(3/2)^3+3*(5/2)^3=15
```

give the three cancellations and `(13)`.  No numerical evidence enters.

This is the positive no-go survivor of the misleading first-atom boundary argument: completed
evenness does not kill the aperture route; it forces the first local obstruction to be the exact
sixth logarithmic seam jet `(11)`.  Lean records `(11)` as
`thetaCuspGaussianApertureSixthSeamNumerator` without assuming its sign.

## Bold conjecture

**Gaussian-aperture boundary Turan curvature (GABTC).** For every `L>=0`,

```text
3*B_3(L)/B_2(L)+15*B_1(L)/B_0(L)-10*B_2(L)/B_1(L) >= 0.   (14)
```

Equivalently, the multiplicative source observable

```text
A(lambda)=b_0(lambda)^15*b_2(lambda)^3/b_1(lambda)^10
```

is nondecreasing for `lambda<=0`; equivalently, the normalized ratios in `(7)` have nonnegative
boundary second difference; equivalently, the single fixed-curvature window integral `(8)` is
nonnegative.

At `L=0`, `(14)` proves the exact first nonconstant prime--Gamma source Hankel block.  This does not
by itself prove RH: the degree-at-least-two source cone or an independent leading-determinant
upgrade remains open.

## Hostile audit

- **Known parent removed:** Gaussian-deformed moments and all separate ordinary Turan inequalities
  are classical Csordas--Varga results.
- **Gaussian rigidity:** for a pure Gaussian source, every normalized ratio `q_j` is constant and
  `(14)` is equality.  The conjecture detects the first non-Gaussian boundary curvature.
- **Generic shape hypotheses fail:** the existing generalized-Gaussian and GHS counterfamilies show
  that log-concavity, a curvature floor, and scalar ferromagnetic convexity do not imply `(14)`.
- **First atom alone is not the completed boundary:** its positive slope is exactly cancelled by
  modular reflection.  The cheapest completed-source falsifier is the sign of `N_6` in `(11)`.
- **Ordinary Turan positivity is insufficient:** `D_1>0` and `D_2>0` do not compare
  `3*B_2*D_1` with `B_0*D_2`.
- **Classical double Turan is different:** it controls log-concavity of the sequence of Turan
  defects for interior indices.  Equation `(6)` is a boundary weighted comparison of the first two
  defects.
- **Finite-jet nonselection remains:** positivity of `N_6` cannot imply RH.  It only anchors the
  exact infinite aperture family `(14)`; the full `L`-continuum is essential.

## Self-dual modular elimination of the sixth seam `[PAPER-PROVED] [LEAN PARTIAL]`

The sixth-seam sign is no longer an unconstrained jet problem.  Put

```text
H(x)=exp(x/2) theta_3(i exp(2x)),
z=2 lambda-1,
R=pi H^4,
p=pi exp(2x) E_2(i exp(2x))-3.
```

The functional equation makes `H,R` even and `z,p` odd.  The modular-lambda derivative,
theta-nullwert logarithmic derivative, and Ramanujan identities give the autonomous system

```text
z'=-R(1-z^2),
R'=-(2/3)R(p+Rz),
p'=3-p^2/3+R^2(3+z^2)/12.                              (15)
```

Since `Phi=(H''-H/4)/2`, exact differentiation of `(15)` through order six eliminates every
seam jet except `R_0=R(0)`.  With `M=H(0)=theta_3(i)` and `X=R_0^2`, it gives

```text
N_6=M^3 Q(X)/131072,                                   (16)

Q(X)=99X^6+12X^5-3160X^4-544272X^3
     -1446144X^2-1509120X+276480.                      (17)
```

This is the coordinate-field collapse suggested by the HTGeometry development: the completed
source's first non-Gaussian local obstruction belongs to the one-coordinate self-dual modular
differential field, rather than requiring independent control of four theta jets.

The source scale is rigorously inside the positive chamber.  The first positive theta term and
rational exponential bounds prove

```text
exp(-pi)>431/10000,
M>5431/5000,
X=(pi M^4)^2>191/10.                                   (18)
```

Expanding at the rational threshold gives

```text
Q(191/10+y)
 =99y^6+(56787/5)y^5+(10794577/20)y^4
  +(652723289/50)y^3+(317839252857/2000)y^2
  +(38870479127747/50000)y+67989377597579/1000000,
```

so `Q(X)>0`, and `(16)` yields `N_6>0`.  Thus the cheapest large-aperture falsifier does not kill
GABTC.  This is a local survival theorem, not a proof of the full aperture balance and not an RH
criterion.

Permanent Lean
`PrimeArchThetaGaussianApertureSixthSeamChamber.lean` proves `(18)`, positivity of `(17)` on the
whole threshold chamber, and positivity of the source-specialized modular-closure value.  The
real-theta/modular-differential derivation of the equality `(16)` remains the exact formalization
gap; Lean does not yet identify that value with
`thetaCuspGaussianApertureSixthSeamNumerator`.  Its direct leaf and exact module build pass; the
four new capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

Exact-coefficient and conceptual searches found no primary-source statement of `(15)`--`(18)` in
this Gaussian-aperture context.  The modular identities used to derive `(15)` are classical; the
search result is noncollision, not a priority claim.

## Discrete curvature-flow reduction `[PAPER-PROVED] [LEAN-PROVED]`

The Gaussian aperture also evolves the entire degree sequence, not only the first balance.  For
`lambda=-L<0`, let `M_j` be the contracted half moments and put

```text
q_j=(M_(j+1)/M_j)/(j+1/2),
S_j=q_j-2q_(j+1)+q_(j+2).                              (19)
```

Differentiation under the literal theta integral and the quotient rule give

```text
M_j'=M_(j+1),
q_j'=q_j*((j+3/2)q_(j+1)-(j+1/2)q_j).                 (20)
```

The generic ratio equation belongs to the classical exponential-moment/one-sided Volterra
parent and is not a novelty claim.  Taking the second degree difference and completing a square
gives the source-facing parabolic--reaction law

```text
S_j'
 =4(q_j-q_(j+1))^2+(j+7/2)q_(j+2)S_(j+1)+R_j S_j,    (21)

R_j=-(j+9/2)q_j+(1/2-j)q_(j+1)+(j+9/2)q_(j+2).
```

At `S_j=0`, a wrong-way derivative therefore forces

```text
(j+7/2)q_(j+2)S_(j+1)<-4(q_j-q_(j+1))^2,             (22)
```

and hence `S_(j+1)<0`.  Since the physical balance is exactly

```text
GABTC(lambda)=(15/2)S_0(lambda),                       (23)
```

a first bad GABTC crossing cannot be born at a finite terminal degree.  It would have to be fed by
negative curvature farther out in the degree tail.

The cold-aperture expansion supplies a compatible fixed-degree seed.  With

```text
c1=Phi''(0)/(2 Phi(0)),
c2=Phi^(4)(0)/(24 Phi(0)),
c3=Phi^(6)(0)/(720 Phi(0)),
```

the second difference of the third ratio-correction coefficient is independent of `j`:

```text
2(c1^3-3c1c2+3c3)=N_6/(120 Phi(0)^3).                 (24)
```

Using `(12)` at arbitrary fixed `j` therefore gives

```text
S_j(-L)=N_6/(120 Phi(0)^3)L^-4+O_j(L^-5).             (25)
```

Thus the positive sixth seam seeds every fixed degree, not just GABTC.  The qualification
`fixed` is essential: `(25)` gives no uniform control when `j` grows with `L`.  The remaining
global obstruction is exactly a diagonal entrance from degree infinity.

The first theta atom exposes a candidate uniform tail mechanism.  Its exact large-height phase is

```text
x^(2j) exp(-pi exp(2x)),
```

so the leading saddle degree and normalized ratio profile are

```text
n(x)=pi*x*exp(2x),
r(x)=x/(pi*exp(2x))=x^2/n(x).                          (26)
```

Differentiating with respect to `n`, rather than `x`, gives the exact identity

```text
d^2r/dn^2
 =8*(2x^2-1)/(pi^3*exp(6x)*(2x+1)^3).                 (27)
```

Therefore the source tail model is strictly degree-convex as soon as `x^2>1/2`.  This is the
height-localized positive survivor at the degree boundary.  `Lean` proves both parametric degree
derivatives and the sign threshold for the exact profiles in `(26)`--`(27)`.

**Uniform saddle-transfer conjecture.**  Let `x_j>0` solve
`pi*x_j*exp(2*x_j)=j`.  On every compact `lambda`-interval contained in `(-infinity,0]`, the full
completed-source curvature should satisfy, uniformly in `lambda`,

```text
S_j(lambda)
 =8*x_j^3*(2*x_j^2-1)/(j^3*(2*x_j+1)^3)
   +o(x_j^2/j^3).                                      (28)
```

The aperture term `lambda*x^2` and the first-atom polynomial amplitude perturb the saddle below
the scale in `(28)`, and the `n>=2` theta atoms are exponentially separated at `x_j`.  Those scale
comparisons identify the proof shape, but the uniform error estimate in `(28)` is not yet proved.
If proved, `(28)` supplies eventual `S_j>0` uniformly on compact aperture intervals.  Together
with the fixed-degree cold seed `(25)` and the cooperative flow `(21)`, it excludes entrance from
infinity and yields GABTC.

Permanent Lean module
`PrimeArchThetaGaussianApertureCurvatureFlow.lean` proves `(20)`--`(24)` for the actual completed
theta source, including the literal differentiation-under-the-integral argument and the
quantitative cascade.  It formalizes the exact coefficient in `(25)`, not the analytic uniform
remainder that remains open.  The same module proves the exact saddle identities `(26)`--`(27)`;
it does not assume the transfer conjecture `(28)`.

## Exact open core

1. Formalize the real-theta/modular-differential bridge `(15)`--`(16)`, closing the compiled
   positive modular value against the literal source jet numerator.
2. Prove a source-specific large-degree boundary for the discrete curvature flow `(22)` above,
   strong enough to exclude negative curvature entering from degree infinity.  Fixed-degree cold
   asymptotics do not supply the necessary uniformity.
3. Alternatively, compare the negative tail of the proved one-crossing `L_lambda` with its
   positive core using the fixed curvature `E` and the exact theta reflection law.
4. Once either route proves `(14)`, formalize the missing curvature-window identity `(8)` if it is
   used, then return to the independent higher-degree source cone.  Do not advertise the
   degree-one block as RH.

## Literature boundary

- G. Csordas and R. S. Varga, *Moment Inequalities and the Riemann Hypothesis*, Constructive
  Approximation 4 (1988), 175--198,
  https://www.math.kent.edu/~varga/pub/paper_161.pdf.
- G. Csordas, *Convexity and the Riemann zeta-function*, Glasnik Matematicki 33 (1998), 37--50,
  https://web.math.hr/glasnik/33.1/33105.pdf.
- G. Csordas and D. K. Dimitrov, *Conjectures and theorems in the theory of entire functions*,
  https://www.dcce.ibilce.unesp.br/~dimitrov/papers/varga.pdf.

The first paper already contains `(3)` as a Gaussian-deformed moment family and proves its
ordinary Turan inequalities for all real deformation parameters.  The second sharpens classical
kernel convexity and Turan lower bounds.  The third formulates the separate double Turan problem.
None of these sources states `(6)`, `(7)`, `(8)`, the forced-window derivative and one-crossing
law `(9a)`--`(9c)`, `(13)`, or GABTC.  Targeted exact-coefficient and conceptual searches also
found no collision for `(9a)`--`(9c)`; this is search noncollision, not a priority claim.

## Gates

- [x] anti-theatre audit against the internal corpus
- [x] primary-literature audit of Gaussian-deformed and double Turan parents
- [x] exact direct mean balance and composite Turan identity
- [x] actual completed-source Gaussian aperture object in Lean
- [x] completed evenness cancellation identified
- [x] sixth-seam leading asymptotic proved on paper
- [x] self-dual modular elimination of `N_6` to one explicit polynomial
- [x] actual source scale proved to lie in the polynomial's positive chamber in Lean
- [x] forced composite window has exactly one positive zero for every `lambda<=0`, in Lean
- [x] literal aperture moments and normalized ratios satisfy the discrete curvature flow in Lean
- [x] identify GABTC with the first curvature coordinate and prove the finite-degree entrance
  cascade in Lean
- [x] prove the all-fixed-degree sixth-seam coefficient identity in Lean
- [x] derive and formalize the exact positive large-degree saddle-curvature profile
- [x] direct Lean leaf check, serialized exact module build, and capstone axiom audit
- [ ] formal equality of the modular-closure value with the literal `N_6`
- [ ] uniform saddle-transfer error estimate `(28)`
- [ ] uniform large-degree boundary excluding negative curvature entrance from infinity
- [ ] uniform composite-window balance `(8)` for `lambda<=0`
- [ ] exact aperture derivative and curvature-window identity formalized in Lean
- [ ] independent higher-degree source cone

## Log

- 2026-07-20 -- Created after the anti-theatre audit.  The literature search retired Gaussian
  deformation and ordinary Turan positivity as known parent theory.  The exact surviving target is
  the boundary composite ratio curvature `(6)`--`(9)`, with the sixth logarithmic seam jet as its
  cheapest source-specific falsifier.
- 2026-07-20 -- Self-dual modular elimination reduced the sixth seam to `(16)`--`(17)`.  A rigorous
  source enclosure places its scalar in the strict positive chamber, so the local large-aperture
  falsifier survives.  Lean proves the complete chamber theorem; the analytic identification
  `(16)` is the remaining formal bridge.
- 2026-07-20 -- The aperture derivative was reorganized as a one-sided discrete curvature flow.
  The raw ratio evolution has a classical Volterra-type parent; the new source-facing content is
  that GABTC is exactly its first curvature coordinate and any bad finite-degree boundary crossing
  forces a quantitatively negative successor.  The sixth seam is also the common cold coefficient
  at every fixed degree.  The open global core is therefore a uniform large-degree boundary, not
  another low-order Turan estimate.
