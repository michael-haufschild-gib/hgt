# Finite-index Haar carriers split modulo polynomial kernels

- **ID:** HAAR-RELATIVE-PONTRYAGIN-SPLITTING
- **Stage:** 1-in-progress
- **Type:** THEOREM
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** Every Hermitian finite-index kernel `k` on `Aff(ℚ)` with integer Haar successor admits `k=p+ψ∘slope+Q`, where `p` is positive definite with the same successor, `ψ` is a Hermitian slope kernel, and `Q` has finite column rank and vanishes on both translations and dilations.

## Canonical decomposition

The dilation reading of `k` equals that of `p+ψ∘slope`. If it is continuous at identity, the existing separable-carrier theorem gives infinite index for `p+ψ∘slope`; a finite-rank perturbation cannot remove infinitely many negative directions. The splitting identifies the mixed polynomial component of the continuous-dilation obstruction.

The [canonical polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) constructs `Q` and proves finite negative index of the bi-integer-invariant remainder. Its unique positive-plus-slope decomposition gives the full relative triple. `exists_unique_haar_relative_split` in `AdelicKreinGeometry/Haar/RelativeSplit.lean` passed its direct audit with transitive axioms exactly `propext`, `Classical.choice`, and `Quot.sound`. The complete index classification remains pending.

The paper proof combines the polynomial correction with the invariant factorial moving-form limit. It uses the actual column representation throughout.

The [finite affine orbit of period defects](../3-formalized/haar-period-defects-have-a-finite-affine-orbit.md) is formalized from unipotence and the isotropic fixed kernel. It supplies a covariant finite-dimensional correction space.

The [cyclic averaging decomposition](../3-formalized/bi-integer-invariant-haar-kernels-split-into-positive-and-slope-parts.md) gives a unique positive Haar and Hermitian slope pair for the corrected carrier, preserving its negative index.

## Uniqueness

The finite-rank term must equal the canonical polynomial correction: finite column rank gives polynomial translation fibres, while the positive Haar and slope terms are integer-invariant. The correction's difference and zero dilation reading determine it uniquely.

After fixing this term, suppose `p+ψ∘slope=p′+ψ′∘slope`. The exact index law applied to `p′=p+(ψ−ψ′)∘slope` makes `ψ−ψ′` positive definite, since `p′` has index zero. Its value at identity is zero because both positive Haar terms have value one there. The positive-kernel norm bound forces `ψ=ψ′`, and hence `p=p′`. This gives the uniqueness clause of `exists_unique_haar_relative_split`; `haar_split_correction_unique` separately identifies the finite-rank correction.

## Converse and complete classification

The converse requires no new analytic input. For a finite-rank kernel `Q` of column dimension `d`, the matrix rank perturbation inequality, applied with both signs, gives

`κ(k−Q) ≤ κ(k)+d`, `κ(k) ≤ κ(k−Q)+d`.

Hence any decomposition `k=p+ψ∘slope+Q` with positive Haar `p` and Hermitian `ψ` satisfies `κ(k)<∞ ↔ κ(ψ)<∞`. If `Q` is Hermitian and zero on both axes and `ψ(1)=0`, then `k` is Hermitian with the Haar successor. These conditions, together with finite index of `ψ`, therefore characterize the kernels in the statement; the full equivalence remains pending Lean audit.

`HeckeKreinToeplitz/Index/FiniteRankStability.lean` formalizes both rank bounds and preservation of finite index, with a direct audit and standard axiom closure. The complete equivalence remains pending.

A [polynomial quadrature argument](../3-formalized/haar-addition-preserves-index-on-polynomial-translation-fibres.md) further gives the exact residual law `κ(k)=κ(ψ∘slope+Q)` and the sharper lower bound `κ(ψ)≤κ(k)` on paper. It reproduces polynomial Gram entries while the positive Haar matrix tends to zero. These stronger statements remain pending Lean verification; no index additivity between `ψ` and `Q` is asserted.
