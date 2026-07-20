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
`(8)`--`(9)` show that only their forced composite is consumed.  `L_lambda` is positive near zero
and is expected to become negative in the far tail, so pointwise positivity is not the target; the
target is its exact balance against the fixed positive source curvature `E`.

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

## Exact open core

1. Prove or disprove `N_6>=0` symbolically from the modular theta source.  A negative sign retires
   global GABTC immediately while preserving `(4)`--`(13)`.
2. Prove the one-crossing structure of `L_lambda` in `(9)`, uniformly for `lambda<=0`, or identify
   its exact counterexample.  Do not split it back into two independent window estimates.
3. Compare the negative tail of `L_lambda` with its positive core using the fixed curvature `E` and
   the exact theta reflection law.  This is the sole analytic sign problem for `(14)`.
4. Once `(8)` is dependency-closed on paper, formalize that integral identity and the Gaussian
   aperture derivative in Lean.  The algebraic consumer is already compiled.
5. If `(14)` is proved, return to the independent higher-degree source cone.  Do not advertise the
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
None of these sources states `(6)`, `(7)`, `(8)`, `(13)`, or GABTC.

## Gates

- [x] anti-theatre audit against the internal corpus
- [x] primary-literature audit of Gaussian-deformed and double Turan parents
- [x] exact direct mean balance and composite Turan identity
- [x] actual completed-source Gaussian aperture object in Lean
- [x] completed evenness cancellation identified
- [x] sixth-seam leading asymptotic proved on paper
- [x] direct Lean leaf check, serialized exact module build, and capstone axiom audit
- [ ] symbolic sign of `N_6`
- [ ] uniform composite-window balance `(8)` for `lambda<=0`
- [ ] exact aperture derivative and curvature-window identity formalized in Lean
- [ ] independent higher-degree source cone

## Log

- 2026-07-20 -- Created after the anti-theatre audit.  The literature search retired Gaussian
  deformation and ordinary Turan positivity as known parent theory.  The exact surviving target is
  the boundary composite ratio curvature `(6)`--`(9)`, with the sixth logarithmic seam jet as its
  cheapest source-specific falsifier.
