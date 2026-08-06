# Coframe card CLOSED at stage 3-formalized (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` — **moved to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/`**, gate `2 → 3` ticked.
Modules **56–57** completed the encoding.  Supersedes the "not done" status in
[[research/scheme_local_degree_expansion_2026_08_06]].

## Final two modules

- `NumericalClassExpansion.lean` — **`one_lt_of_eigen_class`** (a positive-integer eigenvalue of a
  map all of whose eigenvalues exceed one in modulus exceeds one) and
  **`forall_one_lt_of_numerical_class`** (hence every horizon component is ramified).
- `SchemeTheoremAComplete.lean` — **`scheme_eigenvolume_horizon_theorem_of_numerical_class`**:
  Theorem A's conclusions (2)–(6) in one statement.

## Why this closes the card (the judgement call, recorded)

Step 4 of the paper proof consumes two facts that the paper itself **imports from the literature**:
the numerical class of a prime divisor is nonzero (positivity against an ample `(r−1)`-fold
product), and an int-amplified endomorphism has all eigenvalues of modulus > 1 on `N¹` (Meng).
`formal/CLAUDE.md` prescribes: *"Represent missing analytic inputs as explicit hypotheses or `Prop`
interfaces."*  So encoding them as hypotheses and proving the deduction **is** the required
formalization — not a shortfall.  Int-amplification is a *hypothesis* of Theorem A, never a
conclusion.

Guard against over-claiming: `EigenvolumeHypothesisSharpness` (module 35) proves the expansion
input is not removable, so it is load-bearing, not an artefact.  In dimension one it is
unnecessary (`one_lt_ramification_of_one_lt_finrank`).

## What is genuinely proved, not assumed

Steps 1, 2, 3, 5 in full; the `e − 1` of equation (8) **from the definition of the different**
(`differentIdeal_eq_span_pow`), with monogenicity, the Eisenstein presentation, the rank and
completeness all derived; the toric model verified unconditionally
(`toric_eigenvolume_certificate`).

## Status of all four loop cards

All four are now at **3-formalized**: shilov-envelope-correlation-law,
universal-static-choi-complexity-plateau, field-one-spherical-weyl-multiplier-bridge (whose
`Stage:` field was stale at `2-fully-proven` and was corrected), stable-coframe-log-calabi-yau-rigidity.

Remaining for this card is only gate `3 → 4` (publication-ready: novelty review, extension from
coframes to arbitrary tails) and Corollary B, which the card explicitly defers to MMP literature.
