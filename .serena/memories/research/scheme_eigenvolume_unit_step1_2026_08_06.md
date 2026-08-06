# Step 1 discharged at scheme level (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **21**.
Continues [[research/scheme_eigenvolume_horizon_assembled_2026_08_06]].

## `SchemeEigenvolumeUnit.lean`

- `ord_mul_of_ord_eq_zero` — a rational function with `∀ z, Scheme.ord c z = 0` does not move
  divisors.
- `ord_eq_zero_of_isUnit_section` — an invertible section over an open set containing every point
  is such a function (`Scheme.ord_of_isUnit`).
- `schemeEigenvolume_condition_of_ord_eq_zero` — the eigenvolume condition from `Pg * J = c * g`.
- `unitSchemeEigenvolume_ordAt_eq_neg_one` / `_ordAt_ne_zero_iff` /
  `unitSchemeEigenvolume_ramificationIndex_eq_one_off_horizon` — the horizon theorem taking the
  identity `f*Ω = c·Ω` instead of the eigenvolume condition.

## Design point worth remembering

The natural phrasing `X.germToFunctionField ⊤ c` for a **global** section is a trap: it needs
`[Nonempty ↥(⊤ : X.Opens)]` **at statement-elaboration time**, and declaring
`instance : Nonempty ↥(⊤ : X.Opens)` does **not** fix it — synthesis still fails on the
`↥↑⊤` form.  (Same coercion-shape failure as `Nonempty ↥U` for `U : X.affineOpens`; see
[[research/coframe_scheme_pullback_law_2026_08_06]].)

**Fix: state the hypothesis on the function field directly** — `{c : X.functionField}` with
`(hc : ∀ z : X, Scheme.ord c z = 0)`.  This is also mathematically better: "nowhere vanishing
rational function" is the right notion, and the unit-section version becomes a separate lemma
whose `[Nonempty U]` is an ordinary binder over a *variable* `U` (binders are fine; only
synthesis on the literal `⊤` fails).

## Remaining for Theorem A

1. **Different exponent `e − 1`** beyond the Eisenstein presentation — the last algebraic gap.
2. Identify `Pg`, `J`, `c` with actual differential-form data: needs Kähler differentials and the
   top exterior power of `Ω¹` on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.

## Repo hazard (ongoing)

`lint --check-generated` index staleness is a race with a concurrent agent adding Lean files;
verified earlier by diffing two consecutive `index` runs.
