# Non-CCM RH proof-chain working map

## Purpose

Current best model of what Lean corpus proves, what it rules out, and which exact proof-chain
cuts remain open. This is a state document, not a chronological log. Replace stale conclusions
when evidence changes.

Scope: `HTGeometry`, `RHTower`, and `HilbertMetric`. CCM routes are excluded from active search.
Route status comes from declaration statements and proof bodies, not filenames, generated
summaries, or prose labels.

## Fixed endpoint

Mathlib defines

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0)
    (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
    s.re = 1 / 2
```

Lean proves:

```lean
RHTower.rh_iff_xi_ne_zero_right :
  RiemannHypothesis ↔ ∀ s ∈ rightHalf, xi s ≠ 0
```

Source: `formal/GaloisForLFunctions/RHTower/RiemannTower.lean`.

Consequence: a complete route must produce absence of right-half `xi` zeros, or prove a
condition already connected to that absence. An equivalence `P ↔ RiemannHypothesis` makes `P`
an exact proof target. It does not close or discredit the route. What still must be audited is
whether the proposed proof of `P` supplies independent structure, merely invokes RH, or passes
the same unresolved condition through a renaming.

Current direct-conclusion scan over the three scoped Lean trees finds no declaration of syntactic
form

```lean
theorem name : RiemannHypothesis := ...
```

Every direct RH theorem currently found has at least one premise. Full chain is not already closed.

## Classification rule

`P ↔ RiemannHypothesis` is a connector, not a no-go. It establishes that `P` is a complete
proof target: an independent proof of `P` is a proof of RH.

Route-level retirement requires substantially more:

- `P` itself is disproved;
- the proposed derivation of `P` assumes RH or an equivalent statement;
- Lean proves that the proposed transformation conserves the unresolved datum, so that mechanism
  cannot supply `P`; or
- a theorem rules out the claimed representation/class of producers.

The last three retire only the named mechanism. They do not retire other possible proofs of `P`.
All route statuses below use this distinction.

## Current producer-strength ranking

This ranking measures how much of a candidate starts from an unconditional, source-defined Lean
object. It does not measure logical strength: every exact target below is RH-strength.

1. **Theta--Cassini boundary/Markov route.** Actual positive theta carrier, exact nonlinear
   response, analytic continuation, and unique entire source are unconditional. Missing step is a
   fixed positive source representation or the equivalent boundary-saturation inequality.
2. **Möbius--Laplace/Gamma--Hankel route.** Actual Möbius finite sections, their exact
   Mellin--Plancherel limit, and the diagonal/off-diagonal energy split are unconditional. Missing
   step is only arbitrarily large bounded returns of the upper-signed off-diagonal covariance at
   exponents cofinal above one. The additive-triangle formulation exposes the same source at a
   less localized scale.
3. **Hedenmalm center-mixed route.** Actual positive center-mixed density, large sign chambers,
   exact completed-source product-fibre current, all-order cofinal seam cancellation, and a
   universal incomplete-Gamma shell coordinate are unconditional. Existing shell derivatives and
   ordered current terms are rewritten exactly in that coordinate. For every higher shell, Lean
   proves both remainder quadrants and both reflected horizontal derivative directions. Ground
   derivative failure is confined to an explicit compact head with strictly positive tail.
   Missing steps are compact ground domination, transverse derivative control, and cofinal
   reflected product-fibre orientation.
4. **Xi prime-seam route.** Actual Euler coefficient energy, prime-pair asymptotic, and coercivity
   are unconditional. Missing step is a source-built all-prime/Sonin operator estimate on Xi
   fibres.
5. **Prime--Gamma Hankel, Taylor-current, and bounded-source targets.** Exact source formulas and
   sharp target reductions exist, but no independent global positivity/dissipation producer has
   yet emerged.
6. **Hurwitz--Arakelov and power-orbit targets.** Consumers are exact, but the required
   Xi-fibre algebraicity, capture, or divisor-preserving operation has no unconditional producer.

## Open route: Möbius--Laplace bounded-return covariance

**Route status:** `[OPEN CORE; EXACT FINITE ARITHMETIC SOURCE]`.

Lean starts from the actual Möbius coefficients, not a zero-indexed surrogate:

```lean
mobiusDiscreteLaplaceFiniteSection N x
  = finiteMobiusLaplacePencil N x.
```

For every finite aperture and `sigma > 0`, its logarithmic Mellin-line energy is exactly

```text
Gamma(2 sigma) *
  sum_(m,n <= N) mu(m) mu(n) / (m+n)^(2 sigma).
```

Lean splits this positive full energy into diagonal mass plus the signed quantity

```lean
finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma).
```

For `sigma > 1/2`, the diagonal has an aperture-independent summable ceiling and positivity gives
an aperture-independent lower floor for the off-diagonal term. Therefore only its **upper**
behavior is open. Uniform control at every aperture is unnecessary. The weakest finite source
target presently exposed is

```lean
def MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded : Prop :=
  ∀ ε > 0, ∃ sigma C,
    1 / 2 < sigma ∧ sigma < 1 / 2 + ε ∧
      ∃ᶠ N in atTop,
        finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) ≤ C.
```

Lean proves this target implies finite logarithmic source energy on cofinally many strict-right
lines, propagates that energy to the whole strict-right half-plane, obtains Mellin continuation,
and concludes RH:

```lean
mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_implies_riemannHypothesis
```

A hypothetical zeta zero on or right of one such line forces this covariance to tend to
`+∞`; sparse bounded returns cannot survive it. This implication validates bounded return as a
complete proof target. It does not close the route.

The additive formulation is exact but coarser. Lean proves

```text
MöbiusLaplace(x)^2
  = (1 - exp(-x)) * sum_N mobiusAdditiveTriangle(N) exp(-x N),
```

so a one-sided linear upper bound for the cumulative additive triangle gives critical half-decay
and RH (with simple critical zeros in the sharper endpoint theorem). After one more Cesàro
integration,

```text
mobiusAdditiveTriangleSecondCesaro(N)
  = sum_(a+b=N) M(a) M(b),
```

and the all-`ε` bound `O(N^(2+ε))` implies RH. Given the classical Littlewood converse, this
second-Cesàro target is RH-equivalent. The equivalence again makes it an exact target; it does not
retire it.

**Killed mechanisms, not killed route:**

- fixed-order Gowers uniformity yields only logarithmic savings from the natural cubic
  antidiagonal scale, not the missing full power;
- one-prime Euler removal gives a positive tent, but every attempted second fixed-prime removal
  has a proved negative lobe;
- exact ternary insertion through Dirichlet inversion uniquely pays divisor weights of too much
  mass;
- Lambert ternary lifting either collapses coefficientwise back to the binary source or loses two
  powers when fibres are separated;
- blockwise LCM/cubical positivity is impossible because positive semiprime blocks alone have
  cubic-over-logarithmic mass.

**Positive survivors:**

- the saturated LCM bulk is harmless and all source difficulty is localized to the supercritical
  LCM boundary;
- the Gamma--Hankel form removes every diagonal and lower-sign obligation;
- bounded returns, rather than a uniform all-aperture estimate, are enough.

**Exact open core:** prove cofinal bounded returns of the actual upper-signed Möbius
Gamma--Hankel covariance using a nonlocal, all-prime cancellation law. This is sharper than
restating full binary Chowla-scale cancellation, but no unconditional producer for those returns
is yet present.

Sources:

- `formal/GaloisForLFunctions/RHTower/MobiusLaplaceMellinPlancherelBridge.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusLaplaceGammaHankelWall.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusAdditiveTriangleSourceUniversalityLaw.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusMertensSelfConvolutionCriterion.lean`
- `docs/drafts/pipeline/1-in-progress/mobius-additive-frontier-research-ledger.md`

## Open route: Taylor-tail raw current

**Route status:** `[OPEN CORE]`.

**Killed mechanism:** `CIRCULAR` finite-arithmetic remainder-decay shortcut.

Unconditional Lean inputs:

```lean
xiCTaylorOddThetaTailCanonicalSchedule_spec :
  XiCTaylorOddThetaTailSuperaccurateSchedule
    xiCTaylorOddThetaTailCanonicalSchedule

xiCTaylorThetaTailCoreCurrentFiniteArithmeticTwoTermBridge :
  XiCTaylorThetaTailCoreCurrentTwoTermBridge ...
```

The tempting final premise is the same-parameter bound on combined finite-arithmetic remainder.
Lean proves exact identities

```text
J = (1/8) prefix + (1/4) remainder
remainder = topRow + survivingTranslation = 4J - (1/2) prefix
```

and proves the combined remainder is invariant under admissible Haar-depth refinement. As source
cutoff tends to infinity, it tends to `4J`, not zero.

Killing theorems:

```lean
xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_coreCurrentSublinearUpper
xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis
```

Sources:

- `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCurrentCapstone.lean`
- `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCurrentRemainderEquivalence.lean`
- `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCurrentEquivalence.lean`

Positive survivor, already Lean-proved: exact Haar-refinement conservation and cofinal survivor
law. New insight: refinement redistributes unresolved current between top row and translation
survivor; it does not dissipate it.

Do not reattempt: bounding combined remainder using only existing prefix/top-row decay.

Live exact target: an unconditional theorem orienting or dissipating raw core current `J` itself.
Its RH equivalence means that proving it by independent source structure would be a valid complete
RH proof. Equivalence is not evidence against the route; conservation only rules out the specific
Haar-refinement shortcut.

## Closed route: moving completed-source polynomial even factorization

**Verdict:** `FALSIFIED`.

Unconditional Lean input:

```lean
completedOddLogDerivMomentFarRightAsymptotic :
  CompletedOddLogDerivMomentFarRightAsymptotic
```

Lean then proves far-right positivity for every nonzero integer-polynomial moving Hankel test.
Proposed remaining premise was:

```lean
CompletedOddLogDerivPolynomialRightEvenFactorization
```

Killing mechanism: for `P = X`, moving test is second normalized odd completed
logarithmic-derivative moment. Paper proof gives positive value at `1/2`, negative value at `10`,
and eventual positivity. Hence it has at least two odd-multiplicity right-real crossings and
cannot admit required even factorization.

Source card:
`docs/drafts/pipeline/5-failed/completed-prime-gamma-polynomial-even-factorization-to-rh.md`.

Positive survivor: four-crossing law for second completed moment, paper-proved and recorded in
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/completed-prime-gamma-second-moment-four-crossing-law.md`.

Do not reattempt: global even real-root factorization of moving polynomial tests.

Representation lesson: far-right positivity is real source information; parity propagation back
to center is false. A replacement must use signed crossing structure rather than erase crossings.

## Open route: degree-two prime--Gamma Hankel tail

**Route status:** `[OPEN CORE]`.

**Redundant mechanism:** low theta-moment inequalities do not weaken the true target.

The apparent chain uses:

```lean
ThetaCuspUpperAdjacentRatioSeparation
ThetaCuspRelaxedFourthMomentConcentration
PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative
```

Lean proves the third premise alone is exactly RH:

```lean
primeArchSourceTraceHankelIntDegreeTwoTailNonnegative_iff_riemannHypothesis :
  PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative ↔ RiemannHypothesis
```

This does not kill the route. It identifies the degree-two tail as an exact RH target: any
independent proof of it is a complete proof of RH. The proof of equivalence is not a naming
equivalence. Opposite high-degree perturbations `N p ± X^d` cancel
cross terms in the quadratic form; any negative omitted test dominates the fixed high-degree
probe for large `N`. Therefore positivity above any fixed degree reconstructs the full countable
prime--Gamma source cone.

Stronger Lean-proved survivor: positivity on any infinite set of exact degrees is RH-equivalent,
even after restricting tests to monic polynomials or to the fixed monic 2-Eisenstein chamber.

Source:
`formal/GaloisForLFunctions/RHTower/PrimeArchThetaHankelDegreeTail.lean`.

Do not reattempt: using low theta moments to portray the degree-two or cofinal-degree tail as a
smaller gap. Live target is an independent source proof of positivity on one cofinal test family.
The tail carrying full RH information is expected, not disqualifying.

## Active open route: theta--Cassini boundary saturation

**Route status:** `[OPEN CORE; STRONGEST UNCONDITIONAL SOURCE PRODUCER]`.

Lean constructs one aperture-independent positive half-line carrier

```lean
thetaCuspCassiniLikelihoodBaseDensity x
```

and proves, for every `x > 0`, both strict positivity and strict positive definiteness of every
latent spectral moment Hankel block. For every `0 < t < 1`, the genuine inward Cassini response is
the exact nonlinear ratio

```text
thetaCuspCassiniInwardCoordinateResponse (1 - t^2)
  = thetaCuspCassiniLikelihoodFlux t
      / (t * thetaCuspCassiniLikelihoodPartition t).
```

This is not a formal analogue: the proof body identifies the carrier with twice the actual theta
source on the positive half-line and rewrites its flux and partition integrals.

The response has a unique analytic germ at the Euler-safe Cassini point. Lean proves that any
normalized entire function with this one-sided logarithmic derivative is the canonical entire
Cassini source. Thus the source-to-divisor continuation step is already unconditional.

The exact complete target is

```lean
thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis :
  ThetaCuspCassiniInwardBoundarySaturated ↔ RiemannHypothesis
```

where saturation compares the global power-64 Jensen mass of that same entire source with the
normalized degree-63 jet of its inward response. Proving this inequality from independent theta
structure would be a full RH proof.

Lean also exposes a compact positive Markov route:

```text
local fixed compact positive measure at the theta boundary
  -> analytic transport along the zero-free Cassini segment
  -> centered completed-seam moment representation
  -> RH.
```

The transport and RH consumer are closed. The source measure is not.

**Killed mechanisms, not killed target:**

- The raw reciprocal square-gap pushforward of the seam likelihood carrier cannot be the fixed
  Markov measure. Its mass is strictly greater than one, while analytic transport forces the
  canonical zeroth source moment, which is strictly less than one.
- Deleting the origin atom and scalar-calibrating the genuine higher-tail reciprocal pushforward
  repairs degree zero but fails strictly at degree one.  If `mu_1` is that calibrated carrier,
  the corpus-derived paper theorem gives

  ```text
  normalizedPrimeArchMoment 1
    + (19413/160000) * normalizedPrimeArchMoment 0
      < integral x dmu_1(x).
  ```

  Hence `ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching` is false already at `k=1`.
  This kills the fixed reciprocal map `t ↦ t⁻¹`, not compact Markov representation itself.
- The original normalized seam likelihood law is not infinitely divisible: it has an atom at
  square gap `3` but none at `6 = 3 + 3`. Hence a one-particle compound-Poisson/Thorin
  identification of that carrier is impossible.

**Positive survivors:**

- Let `nu` be the genuine higher-tail seam measure and

  ```text
  F(alpha) = integral t^(-alpha) dnu(t) / nu(R).
  ```

  Corpus bounds give

  ```text
  0 < m1/m0 < 29/1250 < 37/256 < F(1).
  ```

  Support `t ≥ 3` makes `F` continuous, strictly decreasing, and convergent to zero.  Therefore
  there is a unique source-selected `alpha_* > 1` with `F(alpha_*) = m1/m0`.  The calibrated
  pushforward through `t ↦ t^(-alpha_*)` is positive, supported strictly below `1/3`, and matches
  source moments of degrees zero and one exactly.  Its first honest open test is degree two.
- The old fixed-exponent interface

  ```lean
  ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching
  ```

  still implies RH as a logical connector, but its concrete `alpha=1` producer is now disproved.
- The self-convolution of the seam carrier has a nonzero atom at `6`; a two-particle completion
  repairs the exact additive-support defect that kills the one-particle infinitely-divisible
  model. No theorem yet identifies its transform with the Cassini response.

**Exact open core:** first test the unique two-moment-calibrated power-reciprocal carrier at degree
two.  If it survives, continue the moment tower; if it fails, its signed degree-two defect becomes
the next source constraint.  Independently, construct one fixed positive compact measure from the
coupled theta completion whose shifted Markov transform equals the actual nonlinear Cassini
response near the Euler-safe boundary, or prove the boundary-saturation Jensen/jet inequality
directly. Positivity of the moving Gibbs measure or latent raw moment Hankel blocks alone does not
discharge this: normalized prime--Gamma moments are logarithmic cumulants, not those raw moments.

Sources:

- `formal/GaloisForLFunctions/RHTower/ThetaCuspCassiniHyperbolicSourceLaw.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspCassiniMarkovBoundaryTransport.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodAtomicNondivisibility.lean`
- `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniResolventSourceLaw.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/theta-cusp-calibrated-power-reciprocal-first-moment-law.md`

## Open route: Hedenmalm center-mixed Fourier positivity

**Route status:** `[OPEN CORE]`.

The actual theta source provides a positive spatial density:

```lean
thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity
thetaCuspHorizontalAutocorrelationTangent_pos
```

Its Fourier sign is an exact complete target:

```lean
thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis :
  ThetaCuspCenterMixedFourierNonnegative ↔ RiemannHypothesis
```

One arbitrary positive Gaussian temperature is already complete:

```lean
hedenmalmGaussianHankelCone_iff_riemannHypothesis :
  HedenmalmGaussianHankelCone tau ↔ RiemannHypothesis
```

Unconditional Lean structure reaches the target on substantial proper subregions:

- every exterior aperture `1 / 2 ≤ a < 1`;
- every interior aperture in central frequency band `|b| ≤ 218 / 25`;
- every nondegenerate two-node matrix;
- far and locally coalesced order-three chambers, with remaining order-three failure confined to a
  bounded core;
- strict fourth reflection-jet Hankel determinant positivity.

Exact open core: prove Fourier-current nonnegativity for the interior high-frequency corner
`0 < a < 1 / 2`, `|b| > 218 / 25`, uniformly in all nodes/equivalently pointwise in frequency.
Order-three positivity alone is not a connector to RH; complete positive definiteness or an exact
source factorization is required.

Mechanisms already ruled out, without retiring the target:

- generic even positive Schwartz shape, strict log-concavity, or any fixed local differential
  order: an explicit positive strictly log-concave counterfamily has off-axis transform zeros;
- finite constant-coefficient local differential autocorrelation frames;
- positivity of the ambient rank-two pure-state tangent, whose inertia is exactly `(1, 1)`;
- automatic inward perturbation from the boundary, because available boundary positivity has no
  uniform margin at frequency infinity.
- diagonal-shell positivity and every fixed finite canonical shell truncation. Lean now proves
  the exact seam law

  ```text
  phi_n'(0) < 0                       for n >= 2,
  sum_(n>=1) phi_n'(0) = 0,
  (sum_(1<=n<=N) phi_n)'(0) > 0       for every N >= 1.
  ```

  Thus no finite prefix is even. After even reflection, its nonzero cusp coefficient gives a
  strictly negative high-frequency Hedenmalm current. The full source removes this coefficient
  only through the infinite negative-slope tail.

Paper-level reduction still open: a Poisson/resolvent decomposition leaves one phase-current
inequality for the actual theta source. Its proof must use exact modular/prime completion; generic
shape information cannot prove it.

Lean now completes the source-faithful cofinal regrouping:

```lean
thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber
```

The current is an absolutely convergent sum of actual completed-source product fibres. This is not
the previously formalized auxiliary `4T''` density. If `d_r(n)=phi_n^(2r+1)(0)` and

```text
C_(r,s)(k)=sum_(mn=k) d_r(m)d_s(n),
```

then Lean proves

```text
sum_k C_(r,s)(k)=0
```

for every `r,s`. The first coefficient has `C_(0,0)(1)>0`, every prime coefficient is negative,
and their complete sum is zero. Paper-level fixed-fibre integration by parts makes the
high-frequency current coefficient `-16 C_(0,0)(k)`. Thus the ground fibre is eventually
negative, prime fibres are eventually positive, and every algebraic endpoint order cancels only
cofinally. No finite-order endpoint asymptotic can determine the completed current.

Lean also proves the exact nonperturbative coordinate. For each positive shell,

```text
t=n^2 exp(2x)
```

turns its phase transform into one universal incomplete-Gamma tail cut at `n^2`, multiplied by
the Dirichlet prefactor

```text
exp(-log(n)/2) * spectralTranslationPhase(-log(n), z).
```

On a product fibre `mn=k`, the two cuts multiply to `k^2`. The universal tail amplitude is
positive above every shell cut, and its norm and the prefactor norm are independent of `Re z`.
The high-frequency mechanism is therefore a complex incomplete-Gamma saddle/cut transition, not
a real stationary point of the Gaussian damping phase.

Lean further removes the source polynomial by an exact integrated Gamma recurrence. Every positive
branch is

```text
2*pi*n^2*exp(-pi*n^2) + pi*(i*z-1/2)*R_n(z),
```

where the first term is real and independent of `z`; Mellin amplitude and shell character cancel
exactly at the moving cut. Actual even shell values are two such boundaries plus the reflected
remainders. The base remainder satisfies the uniform absolute estimate

```text
|R_n(z)| <= exp((Im(z)-1/2)*log n) * exp(-2*n^2)/2
```

for `|Im z|<1`, independent of `Re z`. Absolute far-shell control is therefore closed.

The spectral-derivative connector is now closed in Lean. Differentiation under the universal tail
gives the literal logarithmic insertion

```text
d/dz H_z(N)
  = integral_(N,infinity) i*log(t)/2 * G_z(t) dt,
```

and shell-character differentiation combines with it as

```text
R'_n(z)
  = prefactor_n(z) *
      integral_(n^2,infinity) i*log(t/n^2)/2 * G_z(t) dt.
```

Lean proves that pre-existing corpus object
`thetaCuspShellEvenPhaseSpectralDerivativeValue` is actual derivative of pre-existing shell value,
then proves its exact Gamma formula

```text
D_n(z)
  = pi * (i R_n(z) + (iz-1/2) R'_n(z))
    - pi * (i R_n(-z) + (i(-z)-1/2) R'_n(-z)).
```

Consequently every ordered term of actual Hedenmalm current has a checked formula using only
positive Gaussian boundary, `R_n`, and `R'_n`. No assumed analyticity or placeholder `deriv`
remains between incomplete-Gamma analysis and RH-equivalent current.

The recurrence has a second, positive-density form. Define

```text
W_n(z) = integral_(0,infinity)
           thetaCuspWardGibbsAtom(n,x) * exp(i*x*z) dx.
```

Lean proves, away from the noncritical zero of the recurrence coefficient,

```text
R_n(z) = 2 W_n(z).
```

For `z=b-ia`, put

```text
f_(a,n)(x) = exp(a*x) * thetaCuspWardGibbsAtom(n,x).
```

Its exact logarithmic score is

```text
f'_(a,n)(x) / f_(a,n)(x)
  = a + 5/2 - 2*pi*n^2*exp(2x) < 0
```

when `a<1/2`, `n>=1`, and `x>=0`. Integration by parts against `1-cos(bx)` then gives

```text
b * integral_(0,infinity) f_(a,n)(x) sin(bx) dx
  = integral_(0,infinity) (-f'_(a,n)(x)) (1-cos(bx)) dx > 0.
```

Therefore Lean proves the new uniform sector law

```text
Im R_n(b-ia) > 0
```

for every `0<a<1/2`, `b>0`, and positive shell `n`. This closes one component of the previously
open phase problem without asymptotics and uniformly through the moving-cut transition.

The sector law is holomorphic, not merely pointwise. After the exact shift

```text
u = b + i(1/2-a),
```

the map `u ↦ R_n(u-i/2)` sends a full first-quadrant neighborhood into the upper half-plane.
Applying the Cayley transform and Schwarz lemma on its maximal vertical ball gives the checked
Ward--Schwarz derivative cone

```text
(1/2-a) |R'_n(b-ia)| <= 2 Im R_n(b-ia)                (WS)
```

whenever `b>1/2-a`. In particular `(WS)` holds automatically throughout the unresolved region
`b>218/25`, uniformly in `n`. This is the first quantitative joint `R_n,R'_n` theorem that
survives the moving-cut transition and all shell numbers.

Lean also computes exact normalized second derivative of tilted Ward density:

```text
f''_(a,n)(x) / f_(a,n)(x)
  = (a+5/2-2*pi*n^2*exp(2x))^2
      -4*pi*n^2*exp(2x).
```

For every `a<1/2`, `x>=0`, and `n>=2`, this curvature is strictly positive. Consequently all
higher-shell tilted Ward densities are strictly convex on positive half-line. Ground shell `n=1`
is unique possible curvature defect. A second integration by parts now turns this curvature into
the exact cosine identity

```text
b^2 * integral_(0,infinity) f_(a,n)(x) cos(bx) dx
  = integral_(0,infinity) f''_(a,n)(x) (1-cos(bx)) dx > 0      (n >= 2).
```

Lean therefore proves the genuinely stronger phase law

```text
Re R_n(b-ia) > 0  and  Im R_n(b-ia) > 0                       (n >= 2).
```

Thus every higher-shell Gamma remainder lies in the strict first quadrant at every positive
frequency. This is source-specific new knowledge forced by exact theta curvature, not a generic
positive-density principle. Ground shell `n=1` is now the only shell whose remainder can leave
that quadrant.

Higher-shell derivative rotation is now closed. Lean proves the universal positive kernel

```text
K3(u) = u(2+cos u)-3 sin u > 0                         (u>0)
```

and the exact identity, now exported for every positive shell,

```text
b^4 integral_(0,infinity) x f_(a,n)(x) sin(bx) dx
  = -integral_(0,infinity) f'''_(a,n)(x) K3(bx) dx.     (21)
```

For `n>=2`, exact score algebra gives `f'''_(a,n)<0` on the whole positive half-line. Hence

```text
Re R'_n(b-ia) < 0                                      (n>=2).  (22)
```

The reflected branch has the opposite horizontal derivative direction. At `z=b-ia`, every higher
shell therefore satisfies the checked four-direction cone

```text
Re R_n(z)>0,  Im R_n(z)>0,  Re R'_n(z)<0,
Re R_n(-z)>0, Im R_n(-z)<0, Re R'_n(-z)>0.             (23)
```

Lean also expands both real components of the actual reflected even-shell derivative. Those
formulas show precisely what `(23)` does not sign: the two transverse components
`Im R'_n(z)` and `Im R'_n(-z)`.

Ground-shell failure of the same proof has now been classified exactly. For every
`0<a<1/2`, Lean proves a unique transition `tau(a) in (0,1/2)` such that

```text
f'''_(a,1)(x)>0 for 0<=x<tau(a),
f'''_(a,1)(tau(a))=0,
f'''_(a,1)(x)<0 for x>tau(a).                           (24)
```

Thus third-order identity has exactly one negative compact head and one positive cofinal tail:

```text
b^4 integral x f_(a,n)(x) sin(bx) dx
  = integral_(0,tau] -f'''_(a,1)(x)K3(bx) dx
    + integral_(tau,infinity) -f'''_(a,1)(x)K3(bx) dx,

first term < 0, second term > 0.                         (25)
```

Lean also evaluates signed masses and total variations exactly from boundary data at `tau`.
Writing `f=f_(a,1)`:

```text
integral_(tau,infinity) f'''       = -f''(tau),
integral_(0,tau] f'''              = f''(tau)-f''(0),
integral_(tau,infinity) x f'''     = -tau f''(tau)+f'(tau),
integral_(0,tau] x f'''            = f'(0)+tau f''(tau)-f'(tau),
integral_(0,infinity) |f'''|       = 2f''(tau)-f''(0),
integral_(0,infinity) x|f'''|      = f'(0)+2tau f''(tau)-2f'(tau).  (26)
```

One further exact integration by parts isolates actual high-frequency main term:

```text
b^4 integral_(0,infinity) x f(x) sin(bx) dx
  = -2b f'(0) + integral_(0,infinity) (4f'''(x)+x f''''(x)) sin(bx) dx.  (27)
```

Since `f'(0)<0`, define nonoscillatory threshold

```text
B4(a) =
  integral |4f'''+x f''''| / (-2f'(0)).
```

Lean proves `b>B4(a)` implies `Re R'_1(b-ia)<0`. The active quantitative theorem is now

```text
forall 0<a<1/2, B4(a) <= 218/25.                        (28)
```

Lean now decides `(28)`: it is false. The exact fourth derivative is a shifted quartic in

```text
r = 2*pi*exp(2x) - (a+5/2).
```

The quartic has exactly two roots and sign pattern `+,-,+`. More strongly, the Wronskian between
the shifted cubic and quartic is strictly positive for every `5/2<c<3`, `r>3`. Therefore the
root phase

```text
2x + 8*C3(x)/C4(x)
```

is strictly increasing away from quartic roots. This proves the boundary remainder
`4f'''+x f''''` has exactly two roots `sigma1<sigma2`, with global sign pattern `+,-,+`.
For

```text
H(x)=3f''(x)+x f'''(x)
```

Lean proves the exact total variation identity

```text
integral_(0,infinity) |4f'''+x f''''|
  = 2H(sigma1)-2H(sigma2)-H(0).                         (28a)
```

Exact rational exponential and pi enclosures at the symbolic witness `(a,x)=(1/4,1/5)` give

```text
218/25 < B4(1/4).                                        (28b)
```

Thus taking absolute value of the fourth-order remainder destroys too much cancellation to reach
the verified central-band cutoff. This disproves only that sufficient criterion. It does not
disprove ground horizontal orientation or close the Hedenmalm route.

**Exact open core:** prove actual current nonnegativity for `0<a<1/2`, `|b|>218/25`. Current
unchecked analytic data are:

1. signed ground-shell cancellation in `(25)` or `(27)`, without replacing the oscillatory
   remainder by total variation; the uniform absolute budget `(28)` is formally impossible;
2. transverse derivatives, now exactly
   `Im R'_n(b-ia)=2 integral x f_(a,n)(x) cos(bx) dx`, and reflected analogue;
3. cofinal reflected product-fibre compensation after all endpoint orders cancel.

Higher-shell value quadrants, horizontal derivative directions, reflected directions, derivative
magnitude, analyticity, and far-shell absolute convergence are closed. They do not by themselves
sign the ordered-current sum.

Sources:

- `formal/GaloisForLFunctions/RHTower/HedenmalmAutocorrelationPath.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmCenterMixedOrientationBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmGaussianHankelRH.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmExteriorGaussianHankel.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmCentralBandGaussianHankel.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmLocalFrameObstruction.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspFiniteShellSeamCancellation.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspShellHedenmalmCurrent.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspShellIncompleteGammaCoordinate.lean`
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-cusp-finite-shell-seam-cancellation.md`
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-cusp-source-product-fibre-seam-spectrum.md`
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/theta-cusp-shell-incomplete-gamma-coordinate.md`

## Open route: Xi prime-seam submass

**Route status:** `[OPEN CORE]`.

Lean identifies a concrete Euler-source energy with the horizontal prime-seam reflection defect:

```lean
degreeOneEulerFEFirstCoefficientEnergy_eq_primeSeamWeightedNormSq
```

and proves the unconditional asymptotic

```text
primePairDifferenceEnergy / primeReciprocalMass
  → 2 * degreeOneEulerFEFirstCoefficientEnergy
```

together with coercivity

```text
(rho.re - 1/2)^2 * (log 2)^4
  ≤ degreeOneEulerFEFirstCoefficientEnergy rho.
```

On each strip point, submass growth is exactly the critical-line equation. Globally:

```lean
xiPrimeSeamPairEnergySubmass_iff_riemannHypothesis :
  XiPrimeSeamPairEnergySubmass ↔ RiemannHypothesis
```

This is another complete target, not a closed route. Exact open core: derive submass growth, or
zero first-coefficient energy, on actual Xi-divisor fibres from the actual Sonin/all-prime
operator without using zero location. Current Lean source identity and asymptotic expose the
quantity but do not orient it on Xi fibres.

Sources:

- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairAsymptotics.lean`
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamEulerZeroTangent.lean`

## Open-route audit queue

These are candidates exposed by actual theorem premises. None is active or endorsed until its
definition, all producers, reverse implications, and failed cards are checked.

1. **Exterior Cauchy/Hurwitz positivity at verified band**

   Lean unconditionally proves:

   ```lean
   xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths :
     XiOffLineQuartetAccretiveBand (218 / 25)
   ```

   RH consumers still require positivity/passivity on a Cauchy subspace. Must inspect whether
   HilbertMetric or HTGeometry proves matching positivity with identical carrier and quadratic
   form, rather than a formally similar one. Its equivalence to RH makes this an exact target,
   not a closed route.

2. **Taylor full-density transfer current**

   Corpus contains unconditional schedule/finite-arithmetic bridges. Must first test reverse
   implication and conservation identities. An RH-equivalent remaining current is a valid exact
   target; retire only a proposed transfer mechanism proved unable to change or control it.

3. **Height-adaptive census collisions**

   Corpus supplies unconditional zero-count envelope. RH consumers require adaptive census or
   Kummer-root predicates. Must inspect whether any producer reduces the missing condition to a
   source theorem rather than multiplicity divisibility equivalent to right-half zero absence.

## Open route: positive-frequency source boundedness above four

**Status:** `[OPEN CORE]`.

Lean proves the source-pure verified-height certificate

```lean
rhVerifiedThrough_nine_halves :
  RHVerifiedThrough (9 / 2)
```

and therefore closes the centered band corresponding to `|Re z| ≤ 4`. The weakest exact remaining
target currently exposed by theorem bodies asks for no sign:

```lean
def ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove (R : ℝ) : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → R < z.re →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      (continuedPrimeArchSourceRelativeTrace z).im ≤ C
```

At the unconditional threshold four:

```lean
continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_four_iff_rh :
  ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove 4 ↔ RiemannHypothesis
```

This equivalence validates boundedness as a complete RH target. The sharper sign target
`ContinuedPrimeArchPositiveFrequencyAbove 4` and exterior Cauchy passivity targets remain valid
too, but boundedness is strictly less structure to prove on its face.

Lean also proves the exact positive failure law: if RH is false, then for every finite `C` there
is an admissible positive-frequency point above four where the source imaginary part exceeds
`C`. Thus an unconditional analytic upper bound—of any finite size—would close the full chain.

Current mechanism audit:

- exact quartet budget proves central-band sign and excludes off-line zeros only below a fixed
  height; it cannot self-propagate above that height;
- universal one-state finite-KMS closure is not an independent producer: its imaginary response
  closure is the whole nonpositive half-line, so membership is exactly the desired sign;
- a concrete source-derived KMS/positive-kernel realization remains a valid possible proof.

Sources:

- `formal/GaloisForLFunctions/RHTower/PrimeArchVerifiedHeightAccretivity.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchHighFrequencyAccretivity.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchExactOffLineQuartetAccretivity.lean`

Next action: compare every existing producer or local bound for
`continuedPrimeArchSourceRelativeTrace` against Hedenmalm high-frequency orientation and the
prime-seam source energy. Select an active conjecture only after the remaining HTGeometry
connectors have been traced by theorem body.

## Open route: Hurwitz--Arakelov collisions

**Route status:** `[OPEN TARGETS; SOURCE PRODUCERS MISSING]`.

HTGeometry supplies a real differential-matroid classification:

```lean
continuedHurwitzDifferentiallyDependentOverAnchors_iff_exists_monoScalar_eq
```

for nonintegral, monodromy-separated finite anchor families. RHTower connects character collision
to the critical line through several exact targets, including:

```lean
xiHurwitzAnchorJetProjectiveReflectionLaw_iff_riemannHypothesis
```

and Gelfond--Schneider collisions between the Arakelov coordinate
`arakelovW rho = 1 - 1 / rho` and Hurwitz monodromy character.

These targets remain valid. Current theorem-body trace finds no unconditional producer for any of
the Xi-zero-indexed source premises:

- integral/algebraic `arakelovW rho`;
- finite algebraic-anchor differential capture of the actual continued Hurwitz function;
- all-order projective reflection of its anchor jet.

The differential-matroid theorem classifies what capture would mean; it does not prove capture on
Xi fibres. Until a source theorem supplies one of these premises, this route is farther from a
closed chain than the Hedenmalm and prime-seam routes.

## Promotion rule

An active conjecture is selected only after:

1. exact Lean endpoint and all premises are written here;
2. unconditional corpus producers are connected by exact types;
3. reverse implications and equivalence theorems are searched;
4. prior failed/formalized cards are read;
5. remaining implication is stated as one falsifiable `[OPEN CORE]`;
6. external literature audit is completed for that exact statement.

## Active frontier: fully coupled Hedenmalm cone current

**Status:** `[OPEN CORE] [EXACT LEAN NORMAL FORM COMPILED]`.

Lean now proves, for `0 ≤ a < 1/2` and every real `b`,

```text
thetaCuspCenterMixedFourierCurrent a b
  = 16 * ∫_{u>t>0}
      thetaCuspFullSource (u+t) * thetaCuspFullSource (u-t)
      * (
          u*sinh(2*a*u)*cos(2*b*t)
        + t*sinh(2*a*t)*cos(2*b*u)
        ).
```

The ambient measure is
`(volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))`; the strict cone is
`thetaCuspPositiveLowerCone = {p | p.2 < p.1}`.

Compiled connectors in
`ThetaCuspWignerProductFiberNormalForm.lean`:

```text
thetaCuspCenterMixedFourierCurrent_eq_cosine
thetaCuspCenterMixedFourierCurrent_eq_positiveQuadrant
thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_positiveQuadrantCoupled
thetaCuspPositiveQuadrantCoupledKernel_add_swap
thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_coupledCone
```

What is known now:

- product-fibre/divisor summation is completed before sign inspection;
- transverse conjugates are combined before sign inspection;
- radial substitution `r = 2u` and all constants are Lean-checked;
- diagonal has zero product measure and upper/lower triangles are exchanged by the exact swap
  map;
- pointwise positivity is false: the cofinal cone kernel has a strict negative interior witness
  for every `a,b>0`;
- therefore the remaining statement is genuinely integrated source-mass cancellation.

Theater audit:

- this normal form is infrastructure, not new scientific knowledge;
- rewriting it as an aperture derivative of `|Xi|²` returns the RH-equivalent current and produces
  no sign;
- generic log-concavity, finite moment inequalities, or fixed local derivative orders cannot be
  relabeled as a solution;
- any novelty claim now requires a Lean-proved source-specific inequality for this exact coupled
  integral, or a rigorous counterexample to a proposed source-specific mechanism.

Current attack: derive and test a source-specific cofinal summation law strong enough to control
the two oscillatory transverse terms jointly.  Shellwise sign is not the target; higher shells
must be allowed to cancel the exceptional ground-shell defect before the sign is read.
