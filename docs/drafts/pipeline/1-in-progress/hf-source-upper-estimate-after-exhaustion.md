# HF: arithmetic sign after source-work exhaustion

- **ID:** hf-source-upper-estimate-after-exhaustion
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / direct source-sign investigation
- **Parent goal:** unconditional Lean closure of HF, unchanged.
- **Statement:** Obtain an actual arithmetic upper bound on the completed source
  work below the off-line quantum, or prove the corresponding full-source sign.

## Current evidence

The preceding card `hf-global-selberg-work-exhaustion` is formalized: compact
Laurent-residue works converge to nonnegative damped work, then to the full
multiplicity-copy transverse energy in `[0,∞]`. This supplies no upper estimate.
The current frontier still marks full Weil positivity, Hecke-defect annihilation,
and the arithmetic field/work bound open.

No new RH criterion, multiplicity comparison, zero-side lower bound, or improved
constant is the target of this cycle. A successful subtheorem must prove an
actual signed arithmetic estimate with every prime, Gamma and polar contribution
accounted for.

## Corpus audit and rejected shortcuts

- `TheTowerFormOfAPrime`: positive Kac–Murdock–Szegő form, but the prime form
  subtracts its diagonal. Local positivity does not supply full source positivity.
- `TheHeckeMomentProblem`: Hankel positivity is for the collided depth measure;
  its first moment remains an unbounded, nonnegative Hecke defect.
- `WeilPhiDoobGroundStateCancellationAndShortSupportNoGo`: the theta ground-state
  cancellation and full Doob decomposition are already proved. Reproving them
  would not move the sign frontier.
- ACT's two-moment law excludes a positive decaying folded supersolution.
  Its exact light-cone identity leaves the signed prime anti-diagonal contribution.
  No Perron–Frobenius conclusion on the odd sector is available.

## Direct attacks

1. **Global source work.** Seek a nonpositive arithmetic upper estimate for
   `xiDampedSourceWork R`, `R≥4`, using the actual source rather than its zero-side
   representation. `[OPEN CORE]`: signed prime–Gamma cancellation at the zeros;
   coefficient positivity on `Re s>1` does not control Laurent residues inside.
2. **Source compensation.** Investigate the actual shifted-theta variation form
   `2 S_a(u) - D_a(u) + V_a(u)`. The full target is payment of prime anti-diagonals
   by same-side primes plus the exact light-cone continuum term. `[OPEN CORE]`:
   no independent all-profile payment estimate.
3. **Structured profiles.** Audit ACT's open monotone-profile question as a possible
   substantive all-scale source inequality. This is not permission to replace
   the parent goal or to report a restated criterion as progress. Establish the
   exact statement and test it against existing fold/variance obstructions before
   attempting a proof.

## Proof status

No new source sign or upper estimate is proved. No paper theorem is being
claimed, and no assumption interface has been added in Lean. Every dependency-
closed paper theorem will be followed directly by formalization.

## Direct-source investigation checkpoint

The following checks did **not** discharge the upper estimate. They are research
notes, not new impossibility theorems or reasons to retire HF.

1. **Monotone shifted-theta profiles.** Read
   `ShiftedGroundStateMonotoneFoldDomination`,
   `ShiftedGroundStateFoldExcessThresholdAndOddProfileDomination`, and
   `ShiftedGroundStateCollarDeficitAndHalfCollarPeak` in ACT. Their unconditional
   estimate retains the positive fold-excess weight. The support-localized
   positivity result explicitly assumes the weight bound; neither dual-threshold
   annihilation nor discarded collar mass supplies it. The ACT README already
   records failure of the global weight criterion at large shifts. An argument
   must retain additional same-side energy, not reuse that criterion.
2. **Complete light-cone formula.**
   `LightConeAntisymmetricVariationLaw.zeroForm_shiftedGroundState_eq_antisymmetric_weilJumpDensity_add_prime`
   includes the polar contribution in the continuum kernel. Its continuum term
   is nonnegative; its remaining prime term is signed. No all-profile payment
   estimate was found or proved. Rewriting the formula is not progress on its sign.
3. **Exterior prime field.** Read the newly available
   `ArithmeticElectrostatics/TheExternalFieldIsAPrimeSum`. Its prime upper bound
   holds at `Re s > 1` and follows from a *lower* bound on the zero field there.
   It does not upper-bound the regular source field at an interior zero or the
   damped source work. The finite-energy escape corollary still assumes transverse
   equilibrium.
4. **Discrete Gibbs bound.** Read the proof in
   `RHTower/CriticalGibbsPerronPolarization`. Its actual diagonal bound is
   `log k + mertensPartial (N / k)`, subsequently bounded by `log N + C`.
   The proof does not identify this diagonal with the completed Gamma--polar
   contribution or give a bound on the polar complement. The finite divisor
   estimate cannot be substituted for full Weil positivity.
5. **Selberg source cancellation.** Corpus contains `SelbergSymmetryFormula`,
   `SelbergSymmetryCore`, and the asymptotic for the summatory `Lambda * Lambda`
   in `CCMFUSuzukiSecondGradeAsymptotic`. These statements concern integer
   summatory functions. No theorem transferring their bounds to the required
   signed interior Laurent residues was found. Such a transfer remains an
   analytic obligation, not an inferred consequence of coefficient positivity.
6. **Ground-state localization.**
   `CCMFullGroundZeroSideEigen.riemannHypothesis_of_localizedFullGrounds`
   retains an exponential-moment localization premise. The corpus supplies
   real-rooted ground states and their eigen-equation, but that theorem does not
   discharge the localization bound. No substitution of this criterion for the
   requested producer was made.

**Batch verdict:** no new mathematical result; no Lean file changed or compiled.
The earlier source-work exhaustion remains the last completed bridge. HF and
this card remain in progress. External search, novelty checks, numerical
experiments and new assumption interfaces were not used.

**Continuation obligation:** attack the literal signed arithmetic estimate.
Choose an explicit prime--Gamma--polar cancellation or source inequality before
further implementation; check its first unproved sign on paper. Do not count
another equivalent criterion, a positive collided form, an exterior field
identity, or a smaller constant as discharging the open core.

## Log

- 2026-10-27 — revalidated the previous source exhaustion theorem and current HF
  frontier; researched actual upper estimates, tower forms, depth moments and
  the complete theta ground-state decomposition. External search, novelty audits
  and numerical experiments remain excluded by the user.
