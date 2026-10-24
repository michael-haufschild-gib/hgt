# Universal coefficient-cone reflectors are positive monomials

- **ID:** universal-coefficient-reflectors
- **Stage:** 3-formalized
- **Type:** THEOREM
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

### The degree bound is sharp

For every `D≥1`, take `Q=1+X^D`. If `deg P<2D` and `PQ` has nonnegative coefficients, then every coefficient of `P` is nonnegative: below index `D` it is read directly from `PQ`; at index `j≥D` it is read at index `j+D`, where the coefficient of `P` itself vanishes. Thus no witness of degree below `2D` exists for this shell.

At degree `2D`, the witness `P=X^(2D)−X^D+1` works exactly:

`(1+X^D)P=1+X^(3D)`.

It has a negative coefficient at index `D` and is strictly positive on the entire real axis because `P(y)=(y^D−1/2)²+3/4`. Therefore the degree bound `2deg Q` is optimal even with strict value positivity imposed. The factor identity is elementary; the contribution is its role as the extremal case of the universal reflection classification.

### Stronger witness: positivity on the entire nonnegative axis

The same witness satisfies `R(y)>0` for every `y≥0`. Indeed `D≥1`, and `S≤(D+1)M` gives `b≤(D+2)/2<2D+1`. The exact identity

`Σ_(j=0)^(2D) y^j − (2D+1)y^D = Σ_(k=0)^(D−1) y^k (y^(D−k)−1)²`

is nonnegative for `y≥0`. Thus for `y>0`, `R(y)≥(2D+1−b)y^D>0`; at zero, `R(0)=1`. In particular `R(x²)>0` for every real `x`. The obstruction to universal cancellation therefore survives restriction to real-axis-positive local slice polynomials, rather than depending on an arbitrary sign-changing value polynomial.

## No-go closure

- **Killed mechanism:** Universal cancellation of a nonmonomial coefficient-positive finite shell.
- **Strongest positive survivor:** Exact classification of all universally reversible multipliers as positive monomials, with a strictly positive-on-the-nonnegative-axis counterexample for every other positive multiplier and an optimal universal degree bound `2deg Q`.
- **New insight:** Central zero powers and positive scalars may be removed exactly; positive remote factors require additional signed information. The head-to-tail implication cannot be inverted merely because its tail lies in the coefficient cone.
- **Status:** Paper proof and exact Lean formalization complete. Plain module check passed; transitive dependencies use only `propext`, `Classical.choice`, and `Quot.sound`. This does not retire WD or exclude source-specific cancellation laws.

## Audit

Corpus queries `coefficient nonnegative monomial multiplier` and `CoeffNonneg cancel` returned no declarations. A broader polynomial-multiplier query returned unrelated polynomial-clock and spectral results. This supports a local duplication check, not a worldwide novelty claim.

## Gates

- [x] Complete dependency-closed paper proof.
- [x] Corpus duplication audit completed; no equivalent classification located.
- [x] Exact classification, constructive positive witness, and sharp degree bound formalized.
- [x] Foreground module check and transitive axiom audit.

## Lean declarations

Module: `formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/UniversalReflectors.lean`.

- `universal_coefficient_reflector_iff`: exact positive-monomial classification.
- `exists_positive_reflection_counterexample`: strictly positive-on-the-nonnegative-axis witness with degree at most `2deg Q`.
- `coeffNonneg_mul_one_add_X_pow_iff_of_degree_lt`: sparse shells reflect coefficient signs below the sharp degree boundary.
- `sparseReflectionWitness_mul`, `sparseReflectionWitness_eval_pos`, `sparseReflectionWitness_not_nonneg`, `sparseReflectionWitness_natDegree`: exact extremizer and optimality.

The final plain command `lake --old env lean GaloisForLFunctions/ArithmeticLocalDivisorGeometry/UniversalReflectors.lean` exited 0 with all requested axiom checks standard-only. Temporary print commands were removed afterward; proof declarations were unchanged. The programme umbrella imports this leaf and was not compiled.
