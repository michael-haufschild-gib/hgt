# Centered Bregman evenization, fibre current, and jet reconstruction — Lean certificate

- **ID:** ULF-RFCM-1-LEAN
- **Stage:** 3 — formalized in Lean 4
- **Paper parent:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/relative-formation-completion-mechanics/centered-bregman-evenization-fibre-current-and-jet-reconstruction-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveRelativeFormationCompletion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED] [AFFINE-QUOTIENT COMPLETE] [JOINT RECONSTRUCTION]
  [EVENIZATION LOSS CLASSIFIED] [NO SORRY] [NOT RH]`

## Certified theorem surface

The module defines a four-coordinate centered endpoint jet, its two directed Bregman works, affine
gauge action, relative formation current, and reflection evenization. It proves:

1. `reconstruct`: even value, symmetric response, longitudinal response, and formation current
   reconstruct all four endpoint values and slopes;
2. `leftRightWork_eq`, `rightLeftWork_eq`, `work_sum_eq`, and `work_difference_eq`: symmetric
   response and current jointly reconstruct both directed works, with current exactly one quarter
   of work asymmetry;
3. `affinelyEquivalent_iff`: two jets are affine-gauge equivalent exactly when symmetric response
   and formation current agree, so this pair is the complete affine quotient;
4. `nonnegative_works_iff`: positivity of both directed works is exactly the closed wedge
   `0 ≤ S` and `|H| ≤ a S`;
5. `formationCurrent_evenize`, `evenize_idempotent`, and `evenize_directed_works`: reflection
   evenization is an idempotent projection preserving symmetric response and killing exactly the
   directed current;
6. `relativeFormationCompletion_capstone`: packages quotient completeness, directed-work
   conservation, evenization loss, and the positive-work wedge in one theorem.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or numerical computation is used.

## Exact selection consequence

Even completion does not select a center. It is the quotient `(S,H) ↦ (S,0)`. Any selection proof
must therefore construct, before specialization, a source-normal relative current and prove that
the completed comparison preserves enough directed work to force `H = 0`. This certificate proves
the finite mechanism and blocks replacing that missing source comparison by symmetry rhetoric.
