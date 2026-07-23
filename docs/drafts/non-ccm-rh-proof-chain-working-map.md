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

Paper-level reduction still open: a Poisson/resolvent decomposition leaves one phase-current
inequality for the actual theta source. Its proof must use exact modular/prime completion; generic
shape information cannot prove it.

Sources:

- `formal/GaloisForLFunctions/RHTower/HedenmalmAutocorrelationPath.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmCenterMixedOrientationBoundary.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmGaussianHankelRH.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmExteriorGaussianHankel.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmCentralBandGaussianHankel.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmLocalFrameObstruction.lean`

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
