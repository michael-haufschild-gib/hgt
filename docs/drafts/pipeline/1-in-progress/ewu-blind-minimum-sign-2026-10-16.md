# EWU: sign of the attained blind minimum

Status: in progress. Exact target: at every positive aperture, determine the
sign of the actual minimum in `EvenSector.BlindUnitSource`, unconditionally.
Attainment and its exact Gamma integral are already proved in
`EvenSectorBlindVariationalAttainment`; neither is a sign proof.

## Constraints

Use current Lean corpus and its research search. No web, external novelty
audit, numerical experiments, added axioms, proof holes, RH premise, assumed
Weil positivity, or replacement of the target by a criterion. Final new
theorems require leaf olean builds, direct `lake env lean` audits, axiom
inspection, umbrella wiring, and formal lint. Preserve concurrent work.

## Conjecture ledger

1. **Arithmetic blindness forces nonnegative Gamma energy.** Exact universal
   target: for every positive aperture `a` and every `u : BlindUnitSource a`,
   `0 ≤ ccmRestrictedWeilSourceQuadratic a u.1`. This would determine the
   minimum's sign. [OPEN CORE] Derive the sign from the actual correlations,
   parity, polar moments, and Gamma multiplier, without assumed positivity.
2. **Blindness can be replaced by support avoidance or source nonnegativity.**
   Rejected as a proof strategy: the feasible domain permits cancellation,
   and a nonzero even polar source cannot be nonnegative. Existing separated
   bump and nonnegative-cone theorems therefore do not settle the target.
3. **A minimizing profile admits an arithmetic variation that rules out
   negative Gamma energy.** Investigating exact admissible variations,
   including pointwise products and normalization. Need prove preservation
   of actual source, window, poles, and all integer constraints before using
   a variational argument.
   - Pointwise squaring preserves the integer zeros but gives a nonnegative
     nonzero physical profile. Its Laplace integral at the polar point is
     then positive, so it cannot be the autocorrelation of an even polar
     source. This proposed variation is inadmissible.
   - Integer compression `P(h) ↦ P(k h)` preserves integer zeros because
     `k log n = log(n^k)`, but moves the required polar evaluation from
     `i/2` to `i/(2k)`. The original polar zero does not supply that zero.
4. **Aperture continuation rules out a first zero minimum.** Existing
   `WeilConeNullEnergyBlindTestCarrier` requires a globally Weil-positive
   system. Existing `compact_source_eq_zero_of_re_W_eq_zero` requires RH.
   Neither follows from nonnegativity at one finite aperture. Using either
   here would be circular. This mechanism has not excluded a first zero.
5. **Prime-power phase periodization settles the Gamma sign.** The exact
   corpus fold in `BlindSymbolSlackPrimePowerPeriodization` retains negative
   slack. Its hypotheses do not use the polar source constraint. This is a
   useful diagnosis of the missing coupling, not a sign proof.
6. **Prove the Gamma sign on the larger blind cone first.** Rejected by an
   existing unconditional theorem, not by a numerical experiment:
   `BlindArchimedeanNodeTwoCertificate.not_blindSymbolSlack_of_nonpos`
   proves that this larger cone has negative symbol energy. The theorem
   does not give a counterexample in `BlindUnitSource`: the even-polar
   constraint cannot be dropped.
7. **Apply the existing exact fibre descent to the minimizer.**
   `EvenSectorCompactBoundaryRigidity.exists_full_mixture_strict_descent`
   preserves every integer trace and lowers unnormalized energy, but
   supplies neither the same mass nor the same aperture. Therefore it
   does not contradict a minimum on the fixed-window unit slice. No
   normalization-preserving, blind, even-polar descent has been proved.
8. **Transport the source through the Mellin/cosine-Fourier picture.**
   Dilation intertwining suggests an orthogonality-preserving transport.
   No bridge has been established that also preserves the original
   compact multiplicative window and log-even polar source class. The
   bounded scattering commutator in `CCMGammaSoninNormalForm` is not the
   unbounded Gamma multiplier being minimized.
9. **Use the exact Phi ground-state cancellation as positivity.**
   `WeilPhiDoobGroundStateCancellationAndShortSupportNoGo` supplies a
   genuine decomposition with nonnegative prime jump terms, but retains
   a negative weighted mass term. Its Poincare inequality is not proved
   unconditionally there. Dropping that term would change the objective.
10. **Treat all integer translates as an orthogonal family.** This is an
    invalid strengthening of blindness. Pairings of two such translates
    involve `log(m/n)`; the constraints only specify `log n` for integers.
    No conclusion about nonintegral rational ratios is available from
    the defining constraints alone.
11. **Avenue A — Paley–Wiener factor `(r^2 + 1/4)^2` as an all-aperture sign
    producer.** Audited and formalized in
    `GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity`.
    - **Positive survivor (`[L]`):** Up to and slightly past the first prime
      `2` (`a.1 ≤ (Real.log 2 + 1 / 50) / 2`), the blind minimum is
      unconditionally strictly positive with a uniform floor:
      `one_twentieth_le_evenBlindMinimum_of_le_primeTwo` proves
      `1 / 20 ≤ evenBlindMinimum a` (and `0 < evenBlindMinimum a`). Moreover,
      `evenBlindMinimum_antitone` proves `a.1 ≤ b.1 → evenBlindMinimum b ≤ evenBlindMinimum a`,
      and `riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo`
      reduces `RiemannHypothesis` to `0 ≤ evenBlindMinimum a` for apertures
      `a.1 > (Real.log 2 + 1 / 50) / 2`.
    - **Why Avenue A fails asymptotically (`a → ∞`):** On `BlindUnitSource a`,
      the unit normalization is `‖f‖_{L^2}^2 = (2π)^{-1} ∫ (r^2 + 1/4)^2 |ĝ(r)|^2 dr = 1`,
      so the factor `(r^2 + 1/4)^2 > 0` appears in both numerator and
      denominator of the Rayleigh quotient. At small aperture `a`, the
      Dirichlet ground eigenvalue `(π/(2a))^2 + 1/4` of `-∂^2 + 1/4` forces
      frequency support above the negative well `{|r| < 6.2898}` of `γ(r)`.
      As `a → ∞`, `(π/(2a))^2 + 1/4 → 1/4`, allowing normalized smooth even
      polar profiles `f = (∂^2 - 1/4)g` to concentrate inside the negative
      well unless prevented by a genuine multi-prime + polar positivity law.
12. **Avenue B — Transporting the OWU Farkas-shifted ground operator and
    paired root-division apparatus to EWU.** Refuted as a sign producer by
    exact shift-gauge invariance, formalized in
    `GaloisForLFunctions.RHTower.EvenSectorBlindGroundShiftInvariance`.
    - **Exact obstruction (`[L]`):** Under any constant shift `C ∈ ℝ` of the
      archimedean symbol (`shiftedSourceQuadratic a C u = Q_a(u) - C ‖J_a u‖^2`),
      every `u : BlindUnitSource a` has `‖J_a u‖ = 1`, so the objective on
      `BlindUnitSource a` shifts by the constant `-C`
      (`shiftedSourceQuadratic_blindUnit`). Thus the set of blind minimizers
      is identically unchanged (`isMin_shiftedSourceQuadratic_iff`), while the
      blind minimum shifts to `evenBlindMinimum a - C` (which is strictly
      negative whenever `C > evenBlindMinimum a`,
      `shifted_evenBlindMinimum_neg_of_gt`). When forming the nonnegative
      residual form by subtracting `(evenBlindMinimum a - C) ‖J_a u‖^2`, the
      constant `C` cancels identically across the entire form domain
      `CCMArchimedeanFormDomain a`
      (`shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq`,
      `shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq`,
      `oddSector_shifted_arithmeticForm_sub_shiftedBlindMinimum_eq`,
      `shifted_multiplier_inequality_iff`). Hence the Farkas multipliers,
      shifted nonnegative operator, ground eigenspace, paired-division
      closure, and de Branges polynomial generator are completely blind to
      `C` and cannot distinguish `evenBlindMinimum a ≥ 0` from
      `evenBlindMinimum a < 0`.
13. **Avenue C — Multi-prime joint cosine periodization of `γ(r)` on arbitrary
    nonnegative spectral densities `G(r) ≥ 0`.** Unconditionally refuted in
    `GaloisForLFunctions.RHTower.EvenSectorMultiPrimePeriodizationNoGo`.
    - **Exact refutation (`[L]`):** On even polar tests (`f̂(i/2) = 0`), the
      `β`-weighted archimedean functional equals the `β = 0` pure archimedean
      functional (`poleWeightArchRe_evenPolar_eq_weilArchRe`). However, on
      general even tests (`G(r) = |f̂(r)|^2 ≥ 0` without `f̂(i/2) = 0`),
      `not_weilPositiveEvenAt_of_lt_one` and `not_weilPositiveEvenAt_zero`
      prove `∀ lam : ℕ → ℝ, ¬ WeilPositiveEvenAt 0 lam`, and
      `exists_even_blind_mixture_zeroPole_neg` exhibits a finite nonnegative
      even mixture that is simultaneously blind at **every** integer `n ≥ 2`
      (all primes and composite prime products) and has strictly negative pure
      archimedean energy `c.sum (fun f t => t * poleWeightArchRe 0 f.1) < 0`.
    - **Positive structural survivor (`[L]`):**
      `exists_nonpolar_support_of_poleWeightArchRe_ne` proves that any even
      mixture on which the `β`-weighted archimedean energy differs from the
      `β = 1` archimedean energy must contain an active component with
      `paperFT f.1.1 (I / 2) ≠ 0`. Thus the off-axis complex zero `f̂(±i/2) = 0`
      is strictly indispensable.

## No-go closure for the Avenue A/B/C sign-producer programme

- **Exact killing theorems/mechanisms:**
  1. Avenue A: `‖J_a u‖ = 1` normalizes `(r^2 + 1/4)^2 |ĝ(r)|^2` in both
     numerator and denominator; as `a → ∞`, the Dirichlet spectral gap of
     `-∂^2 + 1/4` on `[-a, a]` shrinks to `1/4`, inside the negative well of `γ(r)`.
  2. Avenue B: `shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq` and
     `shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq` prove exact
     shift-gauge invariance of the subtracted ground form and its kernel under
     `γ ↦ γ - C/2`.
  3. Avenue C: `not_weilPositiveEvenAt_zero` and
     `exists_even_blind_mixture_zeroPole_neg` prove that even full all-integer
     blindness (`n ≥ 2`) leaves the `β = 0` pure archimedean form strictly
     negative on even tests without `f̂(i/2) = 0`.
- **Strongest positive survivors:**
  1. `one_twentieth_le_evenBlindMinimum_of_le_primeTwo`,
     `evenBlindMinimum_antitone`, and
     `riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo` in
     `GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity`.
  2. `shiftedSourceQuadratic_sub_shiftedEvenBlindMinimum_eq`,
     `shiftedRestrictedWeilForm_sub_shiftedEvenBlindMinimum_eq`, and
     `oddSector_shifted_arithmeticForm_sub_shiftedBlindMinimum_eq` in
     `GaloisForLFunctions.RHTower.EvenSectorBlindGroundShiftInvariance`.
  3. `poleWeightArchRe_evenPolar_eq_weilArchRe`,
     `not_weilPositiveEvenAt_of_lt_one`,
     `exists_even_blind_mixture_zeroPole_neg`, and
     `exists_nonpolar_support_of_poleWeightArchRe_ne` in
     `GaloisForLFunctions.RHTower.EvenSectorMultiPrimePeriodizationNoGo`.

## Current structural question

Can the full integer-log orthogonality and the actual polar zero jointly
exclude a low-frequency negative Gamma contribution for `a.1 > (Real.log 2 + 1 / 50) / 2`?
Avenues A, B, and C from `docs/reports/ewu-review.md` are now formally closed:
Avenue A closes small apertures `a.1 ≤ (Real.log 2 + 1 / 50) / 2` unconditionally
(`1 / 20 ≤ evenBlindMinimum a`) and proves global antitonicity of `evenBlindMinimum`,
while Avenues B and C are unconditionally obstructed as sign producers by
shift-gauge invariance and the `β = 0` all-integer blind counterexample.

## Verification and progress

Three new leaf modules have been built with `lake --old build`, audited with
`lake env lean` and `#print axioms` (depend only on `propext`,
`Classical.choice`, `Quot.sound`), and wired into
`formal/GaloisForLFunctions/RHTower.lean`:
- `GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity`
- `GaloisForLFunctions.RHTower.EvenSectorMultiPrimePeriodizationNoGo`
- `GaloisForLFunctions.RHTower.EvenSectorBlindGroundShiftInvariance`

The large-aperture sign statement (`0 ≤ evenBlindMinimum a` for
`a.1 > (Real.log 2 + 1 / 50) / 2`) remains open and is formally equivalent to
`RiemannHypothesis` (`riemannHypothesis_iff_evenBlindMinimum_nonneg_beyond_primeTwo`).
Do not label this card solved until the unconditional large-aperture sign
statement is proved and audited.

