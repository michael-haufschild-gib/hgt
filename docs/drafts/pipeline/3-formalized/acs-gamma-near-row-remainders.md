# Uniform nearby Gamma endpoint losses

- **ID:** acs-gamma-near-row-remainders
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [coarse Gamma recovery](../1-in-progress/acs-coarse-gamma-recovery.md)
- **Statement:** Both nearby nonadjacent rows of logarithmic-cell endpoint losses have universal bounds, independent of source index.

## Exact result

Write `w_b=log(b+1)-log b` and `k=archLevyDensity`. For every integer `a≥1`, Lean proves

`Σ_(b=a+2..2a) w_b*[k(log b-log(a+1))-k(log(b+1)-log a)] ≤ 6*exp(1/2)`

and

`Σ_(1≤b≤a-2, a≤2b) w_b*[k(log a-log(b+1))-k(log(a+1)-log b)] ≤ 2*exp(1/2)`.

The upper sum is encoded with `b=a+2+n`, `n<a-1`. Empty rows are included.

## Matched proof

For the upper row set `G_n=k(log(a+2+n)-log(a+1))`. Monotonicity and `b≤2a` show that each far reading dominates `G_(n+4)`. Since `w_b≤1/a`, four telescoping shifts bound the row by `4*G_0/a`. The width lower bound and `k(t)≤exp(1/2)/(2t)` give `G_0≤exp(1/2)*(a+2)/2`, hence the stated constant.

For the lower row set `G_0=0` and `G_b=k(log a-log(min(b,a-2)+1))` for positive `b`. This sequence is nonnegative and increasing. Each far reading dominates `G_(b-2)`, and the selected widths satisfy `w_b≤2/a`. Extending the nonnegative sum and telescoping leaves at most `2*G_(a-2)`. The same kernel and width bounds give `G_(a-2)≤exp(1/2)*a/2`. The cases `a≤2` are empty.

## Lean evidence

[LogCellGammaRemainderRows.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/LogCellGammaRemainderRows.lean):

- `gammaCellNearUpperRemainder_le`
- `gammaCellNearLowerRemainder_le`

Exact project check: `lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/LogCellGammaRemainderRows.lean`. Both transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`; no warnings. Log: `/tmp/acs-logcell-gamma-remainder-rows-final.log`. Umbrella import is wired; no umbrella build.

## Remaining parent obligation

These discrete endpoint bounds do not yet recover the integrated coarse Gamma energy. [Whole-interval averaging loss and its integrated-pair decomposition](acs-gamma-interval-averaging-loss.md) are now formalized. Finite row assembly and the final energy comparison remain on the parent card. Mixed prime and pole payment is also open.

## Log

- 2026-10-28 — Both exact Lean proofs audited; recorded directly in stage 3.

## Adjacent and distant cell geometry

[LogCellGammaRowGeometry.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/LogCellGammaRowGeometry.lean) passed its exact project check and four transitive axiom audits, without warnings. Log: `/tmp/acs-logcell-gamma-row-geometry-final.log`.

Writing `wₐ=logCellWidth a`, `k=archLevyDensity`, and `E=exp(1/2)`, the checked bounds are:

- `gamma_logCellWidth_le`: `k(wₐ)≤E*(a+1)/2` for `a≥1`.
- `gamma_upper_adjacent_far_mass_le`: `w_(a+1)*k(wₐ)≤E/2`.
- `gamma_lower_adjacent_far_mass_le`: `w_(a-1)*k(wₐ)≤3E/2` for `a≥2`.
- `logCell_distant_subset`: if `2b<a` or `2a<b`, the whole open cell `b` lies beyond the two boundaries `log a-log(3/2)` and `log(a+1)+log(3/2)`.

The first estimate combines `wₐ≥1/(a+1)` with `k(w)≤E/(2w)` for `w≤1`. Multiplication by the adjacent upper width bounds gives the next two estimates. For the gap, the integer inequalities imply `(b+1)*3/2≤a` on the lower side or `(a+1)*3/2≤b` on the upper side; taking logarithms proves the interval inclusions. These estimates retain the actual nonuniform logarithmic widths.

Both modules have six clean audits, with only `propext`, `Classical.choice`, `Quot.sound`. The uniform bound for the complete integrated error row remains a separate open assembly step.

## Actual finite nearby rows

[LogCellGammaNearFiniteRows.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/LogCellGammaNearFiniteRows.lean) passed its exact project check and all four transitive audits without warnings. Log: `/tmp/acs-logcell-gamma-near-finite-final.log`.

For any common translation `s`, let `Rₐᵦ` be the actual integrated farthest-endpoint replacement loss between `s+(log a,log(a+1))` and `s+(log b,log(b+1))`. For arbitrary finite index subsets:

- If every `b` satisfies `a+2≤b≤2a`, then `Σ_b Rₐᵦ≤ofReal(6*exp(1/2)*wₐ)` (`gamma_logCell_nearUpper_sum_le`).
- If every `b` satisfies `1≤b`, `b+2≤a`, and `a≤2b`, then `Σ_b Rₐᵦ≤ofReal(2*exp(1/2)*wₐ)` (`gamma_logCell_nearLower_sum_le`).

The endpoint losses are nonnegative, so a finite subset costs no more than its complete nearby row. An explicit finite reindexing identifies the upper interval with the already checked shifted range; the lower subset sits inside the checked filtered row. The actual pair-error endpoint inequality then gives each integrated term, and exact common-translation invariance removes `s`. All sums pass through `ofReal` only after their real summands are proved nonnegative.

`gammaCellNearUpper_subset_le` and `gammaCellNearLower_subset_le` prove the intermediate real endpoint-row estimates. All three modules now have ten clean standard-axiom audits. The distant row, touching row, and full row assembly remain open.
