# C5 Jensen perturbation IVT and sign-transfer core

- **ID:** c5-jensen-perturbation-ivt-sign-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (Lean), split from `c5-jensen-perturbation-lemma.md`
- **Priority:** FOUNDATIONAL
- **Source:** corrected total-witness branch and IVT/sign-transfer steps of `c5-jensen-perturbation-lemma.md`
- **Statement:** The elementary real-analysis pieces used by the localized Jensen perturbation proof are formally certified: the zero-slope closed-interval witness branch, the closed symmetric interval distance bound, the two IVT sign-orientation lemmas, endpoint-dominance-to-zero lemmas, strict sign transfer under absolute closeness, and the resulting opposite-sign transfer.

## Paper Proof

For the zero-slope branch, if the window radius is nonnegative and `|D'(y)| <= 0` throughout the window, then in particular `|D'(x)| <= 0`, so `D'(x)=0`. If also `epsilon=0` and `C'(x)=0`, then `x` belongs to `[x-epsilon, x+epsilon]` and `(C'+D')(x)=0`, giving the closed-interval witness.

For the interval bound, membership `x' in [x-epsilon, x+epsilon]` is exactly the pair of inequalities `x-epsilon <= x'` and `x' <= x+epsilon`; rewriting gives `-epsilon <= x'-x <= epsilon`, hence `|x'-x| <= epsilon`.

For the IVT branches, continuity on `[a,b]` and endpoint inequalities `f(a) <= 0 <= f(b)` or `f(b) <= 0 <= f(a)` put `0` in the closed interval between the endpoint values. The intermediate value theorem gives a point `c in [a,b]` with `f(c)=0`.

Endpoint dominance is elementary order algebra: if `c <= -B` and `|d| <= B`, then `d <= B`, so `c+d <= 0`; if `B <= c` and `|d| <= B`, then `-B <= d`, so `0 <= c+d`. Combining these inequalities with the IVT branches gives the positive- and negative-orientation endpoint-dominance zero lemmas.

For strict sign transfer, `|y-c| < |c|` first implies `c != 0`. If `c > 0`, the left side of `abs_lt` gives `0 < y`; if `c < 0`, the right side gives `y < 0`. Thus `y` has the same strict sign as `c`, encoded as `0 < y*c`. If both `y` and `z` have the same strict signs as `c` and `d`, while `c*d < 0`, then `y*z < 0`. Applying this twice gives the absolute-closeness opposite-sign lemma.

## Lean Certificate

Lean file: `formal/GaloisForLFunctions/RHTower/C5JensenPerturbation.lean`

Audited theorem names:

- `windowSlope_zero_at_center`
- `jensenClosedWitness_of_zeroEpsilon`
- `abs_sub_center_le_of_mem_Icc_sub_add`
- `exists_zero_Icc_of_nonpos_of_nonneg`
- `exists_zero_Icc_of_nonneg_of_nonpos`
- `add_nonpos_of_le_neg_bound_of_abs_le`
- `add_nonneg_of_bound_le_of_abs_le`
- `exists_zero_Icc_of_endpoint_abs_bounds_pos`
- `exists_zero_Icc_of_endpoint_abs_bounds_neg`
- `exists_zero_Icc_of_endpoint_product_neg`
- `same_sign_product_pos_of_abs_sub_lt_abs`
- `opposite_sign_product_neg_of_same_sign_products`
- `opposite_sign_product_neg_of_abs_sub_lt_abs`

These prove only the elementary IVT and sign-transfer core. They do not formalize the full polynomial hyperbolicity theorem, the Hermite barrier, or the C5 carrier hand-off.

## Gates

- [x] 0 -> 1 in-progress: exact real-analysis sublemmas isolated from the Jensen perturbation card.
- [x] 1 -> 2 fully-proven: paper proof above, using order algebra and IVT.
- [x] 2 -> 3 formalized: Lean theorem package in `C5JensenPerturbation.lean`; imported by `GaloisForLFunctions`; included in `scripts/check_axioms.sh`.
- [ ] 3 -> 4 publication-ready: include as the formal real-analysis core for the Jensen perturbation note.

## Log

- 2026-06-19 — Leaner added this split certificate for the audited IVT/sign-transfer infrastructure. Parent card `c5-jensen-perturbation-lemma.md` remains in `2-fully-proven` until the full polynomial hyperbolicity and Hermite-barrier statement is formalized.
