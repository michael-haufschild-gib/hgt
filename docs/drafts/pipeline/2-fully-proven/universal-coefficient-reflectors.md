# Universal coefficient-cone reflectors are positive monomials

- **ID:** universal-coefficient-reflectors
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Arithmetic Local Divisor Geometry; exact local factor transitions
- **Statement:** For a real polynomial `Q`, multiplication by `Q` preserves and reflects coefficient nonnegativity on every real polynomial iff `Q=cX^a` for some `c>0` and natural `a`.

## Goal

Classify which exact divisor factors may be canceled from a coefficient-cone statement without extra information. Central multiplicities and positive normalization scalars are precisely the universal reversible transitions. A nonmonomial positive shell may conceal a coefficient defect.

## Complete paper proof [PROVED HERE]

Let `C(P)` mean that every coefficient of `P` is nonnegative. Suppose

`∀P, C(PQ) ↔ C(P)`.

Taking `P=1` proves `C(Q)`. Taking `P=−1` rules out `Q=0`.

Suppose the support of `Q` contains at least two indices. Write `D=deg Q`, `q_i=[X^i]Q`, `S=Σ_(i=0)^D q_i`, and `M=max_(0≤i≤D) q_i`. Nonnegativity and at least two positive coefficients give `0<M<S`. Put

`b=(S+M)/(2M)>1`,

`R=Σ_(j=0)^(2D) X^j − bX^D`.

Then `[X^D]R=1−b<0`. Nevertheless every coefficient of `QR` is nonnegative:

- Outside `D≤k≤2D`, the coefficient of the subtracted polynomial `bX^D Q` is zero. The remaining product has nonnegative coefficients.
- Inside that interval write `k=D+i`, `0≤i≤D`. For each `0≤j≤D`, the index `D+i−j` lies in `[0,2D]`. Hence the coefficient at `k` of `Q·Σ_(j=0)^(2D) X^j` is exactly `S`. The coefficient of `QR` is therefore `S−bq_i≥S−bM=(S−M)/2>0`.

Thus `C(QR)` but not `C(R)`, a contradiction. The support of `Q` is a singleton, so `Q=cX^a` with `c>0`.

Conversely, if `Q=cX^a` and `c>0`, coefficients of `PQ` below `a` vanish and the coefficient at `a+j` is `c[X^j]P`. Their signs are exactly those of `P`. This proves both directions.

The proof is constructive once `Q` is supplied: a witness of degree at most `2deg Q` defeats reflection for every nonmonomial coefficient-positive `Q`. It uses no numerical experiment and no root hypothesis.

## No-go closure

- **Killed mechanism:** Universal cancellation of a nonmonomial coefficient-positive finite shell.
- **Strongest positive survivor:** Exact classification of all universally reversible multipliers as positive monomials, with a bounded-degree counterexample for every other positive multiplier.
- **New insight:** Central zero powers and positive scalars may be removed exactly; positive remote factors require additional signed information. The head-to-tail implication cannot be inverted merely because its tail lies in the coefficient cone.
- **Status:** Complete elementary paper proof above; Lean formalization pending. This does not retire WD or exclude source-specific cancellation laws.

## Audit

Corpus queries: `coefficient nonnegative monomial multiplier`, `CoeffNonneg cancel`. No worldwide novelty claim. The classification must be checked against returned corpus results before being advertised as corpus-new.

## Gates

- [x] Complete dependency-closed paper proof.
- [ ] Corpus duplication audit completed.
- [ ] Exact classification and constructive witness formalized.
- [ ] Foreground module check and transitive axiom audit.
