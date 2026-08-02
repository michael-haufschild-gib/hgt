# The constrained prolate exterior leakage has a universal divisibility spectrum

- **ID:** `constrained-prolate-radial-leakage-divisibility-spectrum`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`,
  provisional pending independent proof and exact radial-PSWF literature comparison
- **Parent sources:** Dunster's uniform radial PSWF expansion, Fuchs fixed-mode concentration
  asymptotics, and `constrained-prolate-two-mode-ground-state.md`
- **Statement:** The exterior Fourier leakage measure of the constrained CCM `h_0`--`h_4` source
  converges to `(8/(11*pi))dx/(x*sqrt(x^2-1))` on `(1,infinity)`. Its fixed radial dilation Gram
  matrices become diagonal, with diagonal spectrum
  `(8/(11*pi*k))arcsin(1/k)`.

## Setup

Let

```text
g_lambda=(ell_1 e_(0,lambda)-ell_0 e_(4,lambda))
          /sqrt(ell_0^2+ell_1^2),
q_lambda=Fourier(g_lambda),
d_1(lambda)=1-chi_4(lambda)^2.                                    (1)
```

The source has unit norm and zero integral. Its exact exterior Fourier leakage is

```text
delta_lambda
 =integral_(|y|>lambda)|q_lambda(y)|^2dy
 =(ell_1^2 d_0+ell_0^2 d_1)/(ell_0^2+ell_1^2),                    (2)
```

and the constrained theorem gives

```text
delta_lambda/d_1(lambda)->8/11.                                   (3)
```

## Radial leakage measure theorem

`[PROVED HERE]` The finite measures on `[1,infinity)`

```text
d nu_lambda(x)
 =lambda*|q_lambda(lambda*x)|^2/d_1(lambda) dx                     (4)
```

converge weakly, with convergence of total masses, to

```text
d nu_infinity(x)
 =8/(11*pi) * dx/(x*sqrt(x^2-1)).                                 (5)
```

In particular,

```text
nu_infinity([1,infinity))=4/11,                                   (6)
```

which agrees with one half of `(3)` by evenness.

## Proof of the radial law

### 1. Single fixed mode

First take one normalized fixed even prolate mode `e_(m,lambda)` and put

```text
c=2*pi*lambda^2,
sigma_m(c)^2=O_m(c^(-1)).                                         (7)
```

The finite-Fourier/radial-PSWF connection and Dunster's uniform Bessel expansion give, for
`1<x<infinity`,

```text
Fourier(e_(m,lambda))(lambda*x)
 /Fourier(e_(m,lambda))(lambda)

 =A_(m,c)(x)
   *[J_0(c*xi_(m,c)(x))+O_m(c^(-1) envJ_0(c*xi_(m,c)(x)))],       (8)
```

uniformly on the whole radial interval, where

```text
xi_(m,c)(x)
 =integral_1^x sqrt((t^2-sigma_m(c)^2)/(t^2-1))dt,

A_(m,c)(x)
 =[xi_(m,c)(x)^2/((x^2-1)(x^2-sigma_m(c)^2))]^(1/4).              (9)
```

For fixed `x>1`,

```text
xi_(m,c)(x)->sqrt(x^2-1),
A_(m,c)(x)->x^(-1/2).                                             (10)
```

The large-argument Bessel expansion gives

```text
J_0(z)=sqrt(2/(pi*z))
       *[cos(z-pi/4)+O(z^(-1))].                                  (11)
```

Combining `(8)`--`(11)`, using `cos^2 theta=(1+cos(2theta))/2`, and applying
nonstationary phase on every compact subinterval of `(1,infinity)` yields the weak limit

```text
c * |Fourier(e_(m,lambda))(lambda*x)
      /Fourier(e_(m,lambda))(lambda)|^2 dx
 -> dx/(pi*x*sqrt(x^2-1)).                                       (12)
```

Dunster's envelope error is uniform at the Bessel endpoint and at infinity. It gives the bounds

```text
integral_1^(1+eta) (...) dx <=C sqrt(eta),
integral_R^infinity (...) dx <=C/R                               (13)
```

for the normalized measures in `(12)`, uniformly for large `c`. Hence no mass is lost at `x=1`
or infinity, and the compact-subinterval limit extends to weak convergence with total masses.

The endpoint-response identity gives

```text
|Fourier(e_(m,lambda))(lambda)|^2
 /(lambda*d_m(lambda))->2*pi,                                    (14)
```

because the compressed-Fourier eigenvalue tends to one. Since `c=2*pi*lambda^2`, multiplying
`(12)` by `(14)` proves the single-mode probability-density law

```text
lambda*|Fourier(e_(m,lambda))(lambda*x)|^2/d_m(lambda) dx
 ->dx/(pi*x*sqrt(x^2-1)).                                        (15)
```

Its total mass is `1/2`, exactly the positive half of the leakage.

### 2. Constrained source

The `m=0` exterior norm is smaller than the `m=4` exterior norm by

```text
sqrt(d_0/d_1)=O(lambda^(-4)).                                    (16)
```

Thus its contribution to `(4)`, and its cross term with the `m=4` mode, vanish by
Cauchy--Schwarz. The squared coefficient of the `m=4` mode in `(1)` tends to

```text
ell_0^2/(ell_0^2+ell_1^2)->8/11.                                 (17)
```

Multiplying `(15)` by `(17)` proves `(5)`. The identity

```text
integral_1^infinity dx/(x*sqrt(x^2-1))=pi/2                       (18)
```

proves `(6)`.

## Radial dilation Gram spectrum

For `k>=1`, define the radial components on the lower logarithmic tail by

```text
H_(lambda,k)(s)
 =sqrt(lambda*e^s)q_lambda(k*lambda*e^s),   s>=0,

G_lambda(j,k)
 =inner(H_(lambda,j),H_(lambda,k))_(L2(ds)).                      (19)
```

Then

```text
G_lambda(k,k)
 =1/k integral_(k*lambda)^infinity |q_lambda(y)|^2dy.             (20)
```

Using `(5)` and

```text
integral_k^infinity dx/(x*sqrt(x^2-1))=arcsin(1/k),               (21)
```

gives the exact diagonal limit

```text
G_lambda(k,k)/d_1(lambda)
 ->8/(11*pi*k)*arcsin(1/k).                                      (22)
```

`[PROVED HERE]` For every fixed pair `j!=k`,

```text
G_lambda(j,k)/d_1(lambda)->0.                                    (23)
```

### Off-diagonal proof

Insert the two radial expansions `(8)` in

```text
G_lambda(j,k)
 =lambda integral_1^infinity
    q_lambda(lambda*j*x)q_lambda(lambda*k*x)dx.                   (24)
```

Away from `x=1` and infinity, the product is a sum of phases

```text
c[xi_(4,c)(j*x)+-xi_(4,c)(k*x)].                                 (25)
```

The sum phase has no stationary point. For the difference phase, the limiting derivative can
vanish only when one index is one; in that case the unique critical point is

```text
x_*^2=1/j^2+1/k^2                                                (26)
```

and is nondegenerate. Nonstationary phase therefore gives `O(c^(-1))` away from such a point, and
one-dimensional stationary phase gives `O(c^(-1/2))` near it. The endpoint and infinite tails are
uniformly negligible by `(13)` and Cauchy--Schwarz. The Dunster envelope errors are `O(c^(-1))` in
the same normalized form. After the boundary normalization `(14)`, every contribution is
`o(d_1)`, proving `(23)`. The `m=0` constrained component is again negligible by `(16)`.

## Finite divisibility correlation law

Let

```text
B_(lambda,N)=sum_(1<=n<=N)H_(lambda,n).
```

The exact divisibility identity gives, for fixed positive integers `J,N,m`,

```text
m^(-1/2)
 inner(B_(lambda,J),B_(lambda,N)(.+log m))
 =sum_(1<=j<=J)sum_(1<=n<=N)G_lambda(j,mn).                        (27)
```

Equations `(22)`--`(23)` therefore prove

```text
lim_(lambda->infinity) 1/d_1(lambda) *m^(-1/2)
 inner(B_(lambda,J),B_(lambda,N)(.+log m))

 =sum_(1<=n<=N; mn<=J)
    8/(11*pi*m*n)*arcsin(1/(m*n)).                                (28)
```

This is the exact finite-rank multiplicative resonance law for the actual uniform radial-prolate
tail.

## Full diagonal von Mangoldt charge

Dunster's uniform radial envelope also gives the cofinal tail bound

```text
G_lambda(k,k)/d_1(lambda)<=C/k^2,   k>=1,                          (29)
```

with `C` independent of sufficiently large `lambda`. Indeed, the radial far-field bound is
`|q_lambda(lambda*x)|^2<=C d_1/(lambda*x^2)` uniformly for `x>=2`; inserting this in `(20)` gives
`(29)`, while the finitely many remaining `k` are absorbed into `C`.

Define the diagonal part of the raw radial prime pairing by

```text
DPrime_lambda
 =-2 sum_(m>=2)Lambda(m) sum_(n>=1)G_lambda(mn,mn).                (30)
```

The series is absolutely convergent by `(29)` and

```text
sum_(m>=2)Lambda(m)/m^2<infinity.
```

Dominated convergence and `(22)` give

```text
DPrime_lambda/d_1(lambda)
 ->-16/(11*pi)
    sum_(m>=2)Lambda(m)sum_(n>=1)
      arcsin(1/(mn))/(mn).                                        (31)
```

Writing `k=mn` and using the classical divisor identity

```text
sum_(m|k;m>=2)Lambda(m)=log k                                     (32)
```

collapses this to the exact all-prime constant

```text
DPrime_lambda/d_1(lambda)
 ->-16/(11*pi)
    sum_(k>=2) log(k)/k * arcsin(1/k).                            (33)
```

The series in `(33)` converges absolutely because `arcsin(1/k)=O(1/k)`. It is strictly negative.

The exact value transform in
`prolate-arcsine-zeta-derivative-transform.md` rewrites the diagonal constant as

```text
sum_(k>=2) log(k)/k*arcsin(1/k)
 =-sum_(j>=0) binom(2j,j)/(4^j(2j+1))*zeta'(2j+2),

DPrime_lambda/d_1(lambda)
 ->16/(11*pi)*sum_(j>=0) binom(2j,j)/(4^j(2j+1))*zeta'(2j+2).
```

Thus the solved diagonal charge is equivalently a positive-weight spectrum of even zeta
derivative values.

Equation `(33)` is the diagonal contribution to the exact prime form of the raw radial Poisson
sum. The full prime form also contains the weighted off-diagonal Gram sums and the inseparable
central correction from Poisson summation; no equality between `(33)` and the complete prime form
is asserted.

## Positive consequence for the CCM route

The theorem computes the full diagonal part of the radial divisibility carrier and proves that
every fixed off-diagonal interference disappears. The remaining cofinal theorem is now precise:

```text
combine the solved diagonal all-prime charge (33)
  with a cofinal weighted limit of every off-diagonal Gram term,
  while retaining the central correction in the closed graph domain.               (34)
```

This is the first actual radial-prolate input to the pointed prime/source incidence tensor. It is
strictly stronger than a scalar leakage estimate and is independent of the finite archimedean
Gamma boundary direction.

The theorem does not yet control the simultaneous weighted off-diagonal growth, the exact central
cancellation, or the true Weil Rayleigh/parity margin. Those are the remaining source-side
obligations.

## Novelty audit

### Parent overlap

- Dunster proves the uniform radial Bessel expansion `(8)` with errors.
- Fuchs and Slepian supply the fixed-mode concentration and endpoint normalizations.
- The constrained `8/11` coefficient is proved in the local pipeline.

### Candidate-new residue

No checked source states the weak leakage law `(5)`, the arcsine divisibility spectrum `(22)`, the
finite radial Gram diagonalization `(28)`, or the all-prime diagonal constant `(33)`. After
vocabulary erasure, the residue is a universal exterior-energy measure and dilation spectrum for a
constrained fixed-mode prolate combination.

### Significance

The result evaluates the diagonal and every fixed off-diagonal coordinate of the exact carrier at
the first unresolved analytic gate of the CCM route. Provisional significance: `8/10`. Placement
remains candidate-new until an independent proof and a formula-level audit of Slepian, Dunster,
Fuchs, and the signal-analysis literature are complete.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The algebraic core is already formalized (axiom-clean) by existing modules:

- The **exterior leakage** `(2)` `delta_lambda = (ell_1^2 d_0 + ell_0^2 d_1)/(ell_0^2 + ell_1^2)` is
  identically `GaloisForLFunctions.twoModeSecularRoot d_0 d_1 ell_0 ell_1`
  (`ProlateSecularEquation.lean`); `twoModeSecularRoot_mem_Ioo` gives `d_0 < delta_lambda < d_1`, and
  the limit `(3)` `delta_lambda/d_1 -> 8/11` is `ccm_groundState_weight_eq`.
- The **diagonal spectrum** value `(8/(11*pi*k)) arcsin(1/k)` is `(8/(11*pi))` times
  `GaloisForLFunctions.constrainedProlateArchSeriesTerm` (`ConstrainedProlateExteriorWeil.lean`),
  whose nonnegativity, summability, and positive total are already proved
  (`constrainedProlateArchSeriesTerm_nonneg/_le`, `summable_...`, `tsum_..._pos`).
- The exact von Mangoldt divisor collapse `(32)` is
  `constrainedProlate_sum_vonMangoldt_divisors_ge_two`; it proves
  `sum_(m|k, m>=2) Lambda(m) = log k` in the filtered form used by the radial diagonal charge.
  The same module proves convergence and strict negativity of the resulting prime coefficient via
  `summable_constrainedProlatePrimeSeriesTerm` and `constrainedProlatePrimeConstant_neg`.

The **limiting measure `nu_infinity` and all of its tail slices are now formalized** in
`GaloisForLFunctions/RHTower/RadialLeakageArcsineMeasure.lean`.  The density
`radialLeakageDensity x = 1/(x sqrt(x^2-1))` has the elementary antiderivative `-arcsin(1/x)` on
`(1,infinity)` (`RHTower.hasDerivAt_neg_arcsin_one_div`), which is continuous at the endpoint and
tends to `0` at infinity, so `RHTower.integral_Ioi_radialLeakageDensity` proves

```text
integral_(Ioi a) dx/(x sqrt(x^2-1)) = arcsin(1/a)   for every a >= 1.
```

A single statement therefore covers both `(21)` for every dilation `k >= 1` and `(18)` at `a = 1`
(`RHTower.integral_Ioi_one_radialLeakageDensity`, total mass `pi/2`).  Integrability at the inverse
square-root endpoint singularity is obtained from the monotone antiderivative, so the improper
integral is genuine, not a principal value.

Three consequences are formalized on top of it.  `RHTower.radialLeakageMeasure_total_mass` proves
`nu_infinity([1,infinity)) = 4/11` exactly, upgrading the previous inequality
`constrainedProlateArchConstant_ge_four_div_eleven` to the identity `(6)`.
`RHTower.radialGramDiagonal_eq_measure_slice` proves that the diagonal spectrum `(22)`
`8 arcsin(1/k)/(11 pi k)` is the `1/k`-scaled `k`-tail of the density, i.e. exactly `(20)`--`(21)`.
`RHTower.constrainedProlateArchSeriesTerm_eq_measure_slice` identifies every summand of the already
formalized archimedean coefficient with such a tail, so the arcsine spectrum is now a family of tail
integrals of one density rather than a formal series.  All are axiom-clean.

The **reduction of the weak convergence to pointwise density asymptotics is now formalized**, in
`formal/GaloisForLFunctions/HTGeometry/ScheffeLemma.lean`.  Scheffe's lemma is absent from mathlib;
it is proved here by applying dominated convergence to the positive part `(g - f)^+`, which the
limit density itself dominates.  With it, `(4)` follows from just two analytic inputs: pointwise
a.e. convergence of the densities, and convergence of the total masses -- whose target value
`4/11` is already formalized exactly.  A companion theorem converts the resulting `L^1` convergence
into convergence of integrals against every bounded weight, which is the form weak convergence is
used in.

`formal/GaloisForLFunctions/RHTower/RadialLeakageWeakConvergence.lean` pins the limiting object
down exactly: it names the density `nuInfinityDensity = (8/(11 pi)) radialLeakageDensity` and
proves its integrability and its exact total mass `4/11`.  The concrete finite density and exact
convergence interface now live in
`formal/GaloisForLFunctions/RHTower/RadialLeakageWeakConvergenceTransfer.lean`:
`nuLambdaDensity λ d q x = λ‖q(λx)‖²/d` is literally `(4)`,
`nuLambdaDensity_tendsto_L1` upgrades a.e. density convergence plus total-mass convergence to
`L¹`, and `nuLambdaDensity_tendsto_bounded_test` gives convergence against every bounded measurable
test.  `integral_Ioi_nuInfinityDensity` evaluates every normalized tail, while
`nuLambdaDensity_tendsto_indicator_tail` specializes the bounded-test result to every `Ioi k` and
`nuLambdaDensity_tendsto_radialGramDiagonal` includes the exact `1/k` dilation factor to yield
`8 arcsin(1/k)/(11 pi k)`, the right side of `(22)`.  Thus the complete unconditional
a.e.-density-plus-mass implication through the literal finite density to the diagonal limit is in
Lean.  `formal/GaloisForLFunctions/RHTower/RadialLeakageMassNormalization.lean` now discharges
the mass input exactly: positive dilation and evenness identify the positive radial mass with one
half of the normalized exterior leakage, so `delta_lambda/d_1 -> 8/11` gives `4/11` without any
PSWF asymptotic.  Its capstone `nuLambdaDensity_tendsto_L1_of_exterior_ratio` leaves only the
actual PSWF pointwise density asymptotic.  Weak convergence itself is not assumed.  All
axiom-clean.

The actual-mode normalization feeding that mass transfer is now also formalized in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlatePointwiseRepresentative.lean`.  For every
nonzero actual signed prolate value, Lean constructs the canonical even compact source, proves
unit total `L²` mass, global `C^∞` regularity of its Fourier representative, interior `C^∞`
regularity of the literal source, exact all-order Fourier-moment derivative formulas, and the
exact exterior identity `mass_outside[-a,a] = 1 - σ_n(a)²`.  Thus the remaining weak-limit gate is
the genuine Dunster/Fuchs asymptotic comparison, not representative choice, regularity, or mass
normalization.

Two further pieces of the radial asymptotic argument are now formalized.  In
`formal/GaloisForLFunctions/RHTower/DunsterSigmaComparisonLimits.lean`,
`radialPSWFTurningPhase_div_free_tendsto_one` and
`radialPSWFAmplitudePow4_turning_ratio_tendsto_one` prove the two fixed-`x` limits `(10)` directly
from the exact turning-point-uniform comparison whenever `sigma -> 0`; the bundled theorem is
`radialPSWFTurning_liouville_data_tendsto_free`.  No PSWF solution asymptotic is assumed.

`formal/GaloisForLFunctions/RHTower/RadialPSWFLocalWeakLimit.lean` proves the compact-interval
oscillatory averaging step used between `(11)` and `(12)`.  For every `C^1` weight, arbitrary
constant phase shift, any turning-parameter family in `[0,1]`, and every bandwidth tending to
infinity, `tendsto_integral_weight_mul_cos_sq_radialPhase_add` proves that the exact radial
Liouville `cos^2` factor averages to `1/2`; its pointwise predecessor records the explicit
variation-budget-over-bandwidth error.  Thus compact nonstationary averaging is closed.  Remaining
analytic gap is transfer from the actual radial PSWF solution to this leading oscillatory model.
Axiom audits of both modules contain only `propext`, `Classical.choice`, and `Quot.sound`.

`formal/GaloisForLFunctions/RHTower/RadialPSWFLeadingTightness.lean` now constructs the exact
leading squared-Bessel density after the nonsingular arclength substitution
`t = sqrt(x^2-1)`.  Its phase is proved equal to Dunster's turning-point-anchored phase, its speed
has the exact positive derivative, and the density is globally integrable.  Whenever
`sigma^2 <= 3/4`, `radialPSWFLeadingArclengthDensity_le_integrableEnvelope` gives the uniform
integrable majorant `4/(pi(1+t^2))`; the resulting endpoint and tail bounds are formalized as
`integral_Ioc_radialPSWFLeadingArclengthDensity_le` (`O(eta)`) and
`integral_Ioi_radialPSWFLeadingArclengthDensity_le` (the exact arctangent tail).  Thus endpoint and
far-tail tightness are closed for the literal leading Dunster model.  The compact weak limit now
also includes its varying Liouville amplitude:
`tendsto_integral_weight_mul_radialPSWFLeadingArclengthDensity` proves convergence against every
`C^1` weight on `[a,b]` to `pi^(-1) dt/(1+t^2)`, while
`abs_integral_weight_mul_leadingArclengthDensity_sub_free_le` gives the explicit `O(sigma^2)`
amplitude-freezing error.  Finally,
`tendsto_integral_Ioi_weight_mul_radialPSWFLeadingArclengthDensity` glues compact convergence to
the exact endpoint/tail envelope and proves the full-ray weak limit against every globally bounded
`C^1` test.  Tightness and weak convergence are therefore unconditional for the literal leading
Dunster model; remaining input is only uniform error transfer from the actual PSWF solution to that
model.

What is still not formalized is the **weak convergence** `(4)` of the finite-aperture measures
`nu_lambda` to this limit, and the off-diagonal vanishing `(23)`.

**Correction, 2026-07-27.**  This paragraph previously read "the formal tree has no radial PSWF,
Bessel-envelope asymptotics, or oscillatory-measure interface".  The first clause is **false**: the
tree carries a radial PSWF interface — `RHTower/RadialPSWFExteriorPhase.lean` (Dunster's exterior
Liouville coordinate, its exact derivative, and the uniform nonstationary lower bound on the
exterior ray), `RHTower/RadialPSWFInteractionPicture.lean` (the exact interaction-picture
amplitudes and their transport laws for `W'' + c²W = psi·W`), and
`RHTower/RadialPSWFSpeedMonotone.lean`.  What is genuinely absent is the **estimate layer**:
bounds on the interaction potential `psi`, the resulting bounded-variation control, Bessel-envelope
asymptotics, stationary/nonstationary phase, and an oscillatory-measure interface.  The present
work fixes the target of that convergence exactly; it does not prove the convergence.

## Gates

- [x] uniform radial leakage measure proved
- [x] total mass matched to constrained leakage
- [x] diagonal divisibility spectrum computed
- [x] every fixed off-diagonal Gram entry eliminated
- [x] finite radial divisibility correlation law proved
- [x] full diagonal von Mangoldt charge computed
- [x] arcsine tail law `(21)` and total mass `(18)` formalized in Lean for every `a >= 1`
- [x] exact total mass `nu_infinity([1,infinity)) = 4/11` formalized in Lean
- [x] diagonal spectrum `(22)` identified in Lean with the `1/k`-scaled measure tail
- [x] fixed-radius phase and Liouville--Green amplitude limits `(10)` formalized in Lean
- [x] compact-interval `cos^2` weak averaging for exact radial Liouville phase formalized in Lean,
  uniformly over turning parameters in `[0,1]`
- [x] exact leading squared-Bessel density in nonsingular arclength coordinates, with uniform
  integrable envelope and explicit endpoint/far-tail tightness, formalized in Lean
- [x] full-ray bounded-`C^1` weak convergence of the literal leading Dunster density formalized in
  Lean by compact averaging plus its exact uniform tail envelope
- [x] finite-aperture density `(4)` defined and exact a.e.+mass-to-`L¹`/bounded-test transfer
  formalized in Lean
- [x] finite radial mass convergence to `4/11` reduced exactly to evenness and the normalized
  exterior-leakage ratio, with no PSWF asymptotic input
- [x] exact bounded-test-to-tail and `1/k`-scaled diagonal-limit `(22)` transfer formalized in Lean
- [ ] weak convergence `nu_lambda -> nu_infinity` `(4)` in Lean
- [ ] fixed off-diagonal vanishing `(23)` in Lean
- [x] simultaneous weighted off-diagonal limit — **completed elsewhere**, in
  `../not_new_scientific_knowledge/ccm-exact-radial-nonstationary-sector-bound.md`,
  equations `(8)`--`(10)`: the uniform bound `|G_lambda(j,k)| <= C d_1/(c j k |j-k|)` for
  `j,k >= 2`, the row estimate `sum_(j>=2;j!=k) 1/(j k |j-k|) <= C(1+log k)/k^2`, and the
  divisor-weighted total `O(d_1/c) = o(d_1)`.  The surviving sector is only the first row
  `-2 sum_(k>=2) log(k) G_lambda(1,k)`, whose hybrid transfer uniform through `k/c` is the
  live item.  The arithmetic-summation layer is formalized in
  `RHTower/RadialGramOffDiagonalDecay.lean` (axiom-clean).
  This gate was left stale and caused one duplicated attack; see
  `../../5-failed/ccm-radial-offdiagonal-rediscovery-and-stale-gate.md`.
- [ ] exact central graph-domain cancellation
- [ ] true Weil Rayleigh-excess and parity transfer
