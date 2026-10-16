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

## Current structural question

Can the full integer-log orthogonality and the actual polar zero jointly
exclude a low-frequency negative Gamma contribution? Separately, neither
prime-power phase uniformity nor the polar constraint supplies the sign.
Need an actual coupled identity or admissible variational descent. A new
equivalence, shifted positive Gamma symbol, bound, or assumed spectral
measure will not close this question.

## Verification and progress

No new sign theorem or Lean code. The searches and mechanism checks above
have not determined the minimum's sign. No leaf build, axiom audit, or
umbrella change is claimed for this attempt. The previously audited
attainment theorem remains an attainment theorem only. Do not label this
card solved until the unconditional sign statement is proved and audited.
