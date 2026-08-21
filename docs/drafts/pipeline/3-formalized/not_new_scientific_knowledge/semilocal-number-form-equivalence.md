# Semilocal number-form equivalence

- **ID:** semilocal-number-form-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM / DOMAIN BRIDGE (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** normalized archimedean and finite semilocal cyclic measures

## Statement

Let `P` be a finite prime set. Identify the archimedean and semilocal cyclic spectral spaces by the
cyclic transition `J_P`, which is the identity on functions. Their probability measures satisfy

`c_P dmu_infinity <= dnu_P <= C_P dmu_infinity`             (1)

for explicit constants `0<c_P<=C_P<infinity`.

Let `N_infinity,N_P` be the two number operators associated to the common polynomial filtration

`E_n={polynomials of degree <=n}`.

Then their closed quadratic-form domains coincide under `J_P`:

`Dom(N_infinity^(1/2))=Dom(N_P^(1/2))`,                    (2)

and their number forms are quantitatively equivalent:

`c_P <f,N_infinity f>_infinity
 <= <f,N_Pf>_P
 <= C_P <f,N_infinity f>_infinity`.                         (3)

After harmless adjustment of the constants for the two Hilbert norms, the energy spaces

`Dom(D) intersect Dom(N_infinity^(1/2))`

and

`Dom(D) intersect Dom(N_P^(1/2))`

are the same topological vector space. Therefore the archimedean and genuine cyclic semilocal formal
prolate forms have a canonical common energy domain under `eta_P`, despite the algebraic-core
disjointness of the different `theta_P`-transported control.

## Proof

The Euler density bounds give (1). For any of the two Hilbert norms, let `Pi_n` be the orthogonal
projection onto `E_n`. If

`f=sum_(j>=0)c_j p_j`

in the corresponding orthonormal Jacobi basis, then

`dist(f,E_n)^2=||(1-Pi_n)f||^2=sum_(j>n)|c_j|^2`.

Summing in `n` and exchanging the nonnegative sums gives

`sum_(n>=0)dist(f,E_n)^2
 =sum_(j>=1)j|c_j|^2
 =<f,Nf>`.                                                  (4)

The expression may be infinite; finiteness is exactly membership in the number-form domain.

For every polynomial `q in E_n`, equation (1) gives

`c_P||f-q||_infinity^2<=||f-q||_P^2<=C_P||f-q||_infinity^2`.

Taking the infimum over `q in E_n` yields

`c_P dist_infinity(f,E_n)^2
 <=dist_P(f,E_n)^2
 <=C_P dist_infinity(f,E_n)^2`.

Summing and using (4) proves (2)--(3).

The scaling operator `D` is multiplication by the same variable under the cyclic spectral identity,
and the two `L^2` norms are equivalent by (1). Hence its form domain is the same set with equivalent
graph norms. Intersecting with (2) proves the energy-space statement.

## Canonical bounded energy representative

For `lambda>0`, define the positive closed energy form

`a_(lambda,P)(f)=||Df||_P^2+lambda^2<N_P^(1/2)f,N_P^(1/2)f>_P+||f||_P^2`

and the formal prolate form

`q_(lambda,P)(f)=-||Df||_P^2+lambda^2<N_P^(1/2)f,N_P^(1/2)f>_P`.

On the common energy space,

`|q_(lambda,P)(f)|<=a_(lambda,P)(f)`.

Thus Riesz representation gives a canonical bounded self-adjoint contraction `C_(lambda,P)` on the
energy completion satisfying

`q_(lambda,P)(f,g)=a_(lambda,P)(f,C_(lambda,P)g)`.           (5)

This bounded representative exists without selecting a self-adjoint extension of the indefinite
formal prolate operator.

## Route consequence

- `[PROVED]` The direct cyclic comparison through `eta_P` has a canonical common number-form and
  energy domain.
- `[PROVED]` The `theta_P` core-disjointness theorem and this result are compatible: they concern two
  different source transports. `theta_P` preserves Sonin spaces; `eta_P` preserves cyclic polynomial
  filtrations.
- `[PROVED]` The indefinite prolate constraint has the canonical bounded energy representative (5).
- `[LIMIT]` A bounded representative on the energy completion is not a self-adjoint prolate operator
  on the original `L^2` space. Recovering one requires a gap/domain/boundary theorem for the form.
- `[OPEN CORE]` Determine whether `C_(lambda,P)` has a source-selected zero-gap structure compatible
  with the exact Sonin sector, or whether the absence of a gap obstructs every closed `L^2`
  realization.

## Novelty audit

The distance-to-filtration identity and equivalence-of-forms argument are standard Hilbert-space
approximation theory. Their application repairs the exact domain bookkeeping for Route B but is a
BRIDGE, not new scientific knowledge.

## Lean formalization — COMPLETE

Module: `formal/GaloisForLFunctions/HTGeometry/FiltrationNumberForm.lean`
(wired into `GaloisForLFunctions.HTGeometry`; `#print axioms` gives exactly
`propext, Classical.choice, Quot.sound` on every capstone).

The card is formalized in the generality in which its proof actually works: an abstract filtration,
an abstract nonnegative cost, and two Hilbert realizations of the same filtered space.

| Card item | Lean declaration |
|---|---|
| distance to `E_n` | `filtCost` (`= sInf` over `q ∈ E_n` of `Q (f - q)`) |
| the number form `∑_n dist(f, E_n)²` | `filtForm` (an `ℝ≥0∞`-valued `tsum`, so no summability side condition) |
| the two-sided density bound `(1)` descends to distances | `mul_filtCost_le`, `filtCost_le_mul` |
| `(3)` quantitative equivalence of the number forms | `mul_filtForm_le`, `filtForm_le_mul` |
| `(2)` equality of the form domains | `filtForm_ne_top_iff` |
| `(2)`+`(3)` packaged | `filtForm_equivalence` |
| transport along the cyclic transition `η_P` | `filtCost_comp_addMonoidHom`, `filtForm_comp_addMonoidHom` |
| `dist(f, E_n)² = ∑_{j>n} |c_j|²` | `filtCost_normSq_basisFiltration` |
| `(4)` `∑_n dist(f, E_n)² = ∑_j j |c_j|² = ⟨f, N f⟩` | `filtForm_normSq_basisFiltration` |
| the whole statement for two comparable realizations | `number_form_equivalence` |
| `|q_{λ,P}| ≤ a_{λ,P}` forces a bounded form bound | `abs_bilin_le_of_abs_diagonal_le` |
| `(5)` the canonical bounded self-adjoint contraction `C_{λ,P}` | `exists_energy_contraction` |

Details of the three proof mechanisms, all unconditional:

1. **Distance comparison.** `filtCost` is the infimum of the cost over the displacement set, so a
   pointwise bound `c·Q₁ ≤ Q₂ ≤ C·Q₁` transfers by `le_csInf`/`csInf_le` alone. Summing in `n` inside
   `ℝ≥0∞` (`mul_filtForm_le`, `filtForm_le_mul`) needs no convergence hypothesis, and
   `filtForm_ne_top_iff` reads off the equality of the finiteness domains from the two-sided bound —
   exactly the card's `Dom(N_∞^{1/2}) = Dom(N_P^{1/2})`.

2. **The spectral identity `(4)`.** `repr_eq_zero_of_mem_basisFiltration` shows every vector of
   `basisFiltration b n = span {b_j : j ≤ n}` has vanishing coordinates past `n`, giving the lower
   bound `∑_{j>n}|c_j|² ≤ ‖f - q‖²`; the truncation `basisTruncation` attains it, so
   `filtCost_normSq_basisFiltration` is an equality. Summing and exchanging the two nonnegative sums
   with `ENNReal.tsum_comm` replaces `#{n : n < j}` by `j`, which is
   `filtForm_normSq_basisFiltration`. Parseval enters only through `norm_sq_eq_tsum_repr`.

3. **The bounded energy representative `(5)`.** For a symmetric continuous bilinear form,
   `4·B(u,v) = B(u+v,u+v) − B(u−v,u−v)` plus the parallelogram law gives
   `|B(u,v)| ≤ (‖u‖²+‖v‖²)/2`; rescaling `u ↦ t u`, `v ↦ t⁻¹ v` with `t = √(‖v‖/‖u‖)` sharpens this to
   `|B(u,v)| ≤ ‖u‖‖v‖` (`abs_bilin_le_of_abs_diagonal_le`). The Riesz map `formRiesz` then represents
   `B` by a genuine contraction, self-adjoint because `B` is symmetric — no self-adjoint extension of
   the indefinite prolate operator is used anywhere, matching the card's `[LIMIT]` remark.

The two `[OPEN CORE]` items of the card (the source-selected zero-gap structure of `C_{λ,P}`, and the
limit-point/limit-circle alternative) are explicitly outside the stated theorem and are untouched.
