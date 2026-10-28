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
