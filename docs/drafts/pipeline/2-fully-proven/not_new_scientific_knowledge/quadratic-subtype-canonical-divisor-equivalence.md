# Quadratic-Subtype Growth Equals Sublogarithmic Canonical Divisor Density

- **ID:** quadratic-subtype-canonical-divisor-equivalence
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / CONSTRAINT REDUCTION
- **Scientific status:** `[BRIDGE]` — an exact repackaging of Jensen's formula, Hadamard factorization, and genus-zero canonical-product estimates
- **Statement:** An entire function with `log M(r)=o((log r)^2)` is, up to a monomial and a constant, a genus-zero canonical product whose zero count is `o(log r)`; conversely every such canonical product has this growth.

## Goal

Replace the coefficient-size formulation of the super-Gaussian DA problem by its intrinsic divisor constraint. The resulting open question asks whether finite algebraic-differential constraint requires a positive logarithmic density of zeros at ordinary order zero.

## Gates

- [x] Complete unconditional paper proof.
- [x] Both directions proved.
- [x] DA status shown to be determined by the canonical divisor in this class.
- [x] Parent-theory gate: **FAILS scientific novelty.** Every ingredient is classical entire-function theory.
- [ ] Formalization: not attempted. The card cannot enter `3-formalized` without a complete unconditional Lean proof of the whole theorem.

## Theorem `[PROVED HERE] [BRIDGE]`

Let `f` be a nonzero entire function and let `n_f(r)` count its nonzero zeros in `|z|<=r`, with multiplicity.

### Forward direction

If

`log M_f(r)=o((log r)^2)`,                                                     `(1)`

then `f` has ordinary order zero and admits the factorization

`f(z)=c z^m product_k (1-z/z_k)`,                                             `(2)`

where `c!=0`, `m>=0`, and the product has genus zero. Moreover,

`n_f(r)=o(log r)`.                                                            `(3)`

### Converse direction

If `(z_k)` is a nonzero divisor with

`n(r)=#{k:|z_k|<=r}=o(log r)`,                                                `(4)`

then the genus-zero canonical product

`P(z)=product_k(1-z/z_k)`

converges and satisfies

`log M_P(r)=o((log r)^2)`.                                                     `(5)`

Consequently, inside the class (1), differential algebraicity of `f` over `C(z)` is equivalent to differential algebraicity of its canonical product `P`: the factors `c z^m` are rational and DA.

## Proof

### 1. Growth subtype implies genus zero

Condition (1) implies

`limsup_(r->infinity) log log M_f(r)/log r=0`,

so `f` has ordinary order zero. Hadamard factorization therefore has genus zero and its exponential polynomial has degree zero. Removing the zero at the origin gives (2).

### 2. Jensen forces sublogarithmic zero counting

After dividing by `z^m`, assume `f(0)!=0`. Jensen's formula gives

`N_f(R):=sum_(0<|z_k|<R) log(R/|z_k|) <= log M_f(R)-log|f(0)|`.                `(6)`

For `r>1`, monotonicity of `n_f` yields

`N_f(r^2)-N_f(r)=integral_r^(r^2) n_f(t) dt/t >= n_f(r) log r`.               `(7)`

By (1) and (6), `N_f(r^2)=o((log(r^2))^2)=o((log r)^2)`. Hence (7) gives

`n_f(r)=o(log r)`.

### 3. Sublogarithmic counting gives a genus-zero product

From (4), for every `alpha>0`,

`sum_k |z_k|^(-alpha) < infinity`.

Indeed, Stieltjes integration reduces the tail to

`alpha integral_T^infinity n(t)t^(-alpha-1)dt`,

which converges because `n(t)=o(log t)`. Thus the exponent of convergence is zero and the genus-zero product `P` converges.

### 4. The canonical-product estimate recovers quadratic subtype zero

For `r>=1`,

`log M_P(r) <= sum_k log(1+r/|z_k|)`

`             = r integral_0^infinity n(t)/(t(t+r))dt`.                       `(8)`

The finitely many zeros below a fixed `T` contribute `O(log r)`. On `[T,r]`, the kernel is at most `1/t`, and (4) gives

`integral_T^r n(t)dt/t=o((log r)^2)`.                                         `(9)`

On `[r,infinity)`, the kernel is at most `r/t^2`; uniformly for sufficiently large `r`,

`r integral_r^infinity n(t)dt/t^2=o(log r)`.                                 `(10)`

Combining (8)-(10) proves (5). The DA equivalence follows from (2) and closure of the DA field under multiplication and division by nonzero rational functions. `square`

## Constraint reformulation

The arbitrary-order super-Gaussian coefficient conjecture is equivalent to the following divisor law:

> `[CONJECTURE — logarithmic divisor-density floor]` Every transcendental DA entire function of ordinary order zero has
>
> `limsup_(r->infinity) n_f(r)/log r > 0`.

Equivalently, a DA entire function with `n_f(r)=o(log r)` must be a polynomial.

The equivalence uses this theorem together with the following elementary lemma. If a zero-free entire function `F` satisfies (1), write `F=exp(g)` with `g` entire. Then

`max_(|z|<=R) Re g(z)=log M_F(R)=o((log R)^2)`.

Borel-Caratheodory on the concentric disks of radii `R` and `2R` gives `M_g(R)=o((log R)^2)`. Cauchy's estimate then gives `g^(k)(0)=0` for every `k>=1`, so `g` and `F` are constant. Thus a nonpolynomial function in (1) necessarily has an infinite canonical divisor, and the two conjectural formulations are exact.

## Literature boundary

1. Steven B. Bank, *On Certain Canonical Products which Cannot Satisfy Algebraic Differential Equations*, Funkcial. Ekvac. 23 (1980), 335-349, explicitly treats zero sequences as carriers of hypertranscendence for finite-order entire functions.
2. Bank records Wittich's hypertranscendence result for the geometric divisor `(lambda^n)` and Valiron's contrasting DA result for the inversion-symmetrized divisor `(lambda^n+lambda^(-n))`. Thus zero sparsity alone is not a sufficient classification invariant at the critical `log^2 r` scale.
3. The equivalence (1)-(5) is classical Jensen-Hadamard theory and is not claimed as scientific novelty.

## Exact heat consequence

For a jointly entire one-sided periodic heat orbit, the multiplicative anchor has `log M(r)=o((log r)^2)`. Therefore its zero divisor has `n(r)=o(log r)`. Proving the logarithmic divisor-density floor would make every infinite-spectrum anchor HT, independently of coefficient arithmetic and ADE order.

This remains a no-go theorem only for implementations factoring through that entire-complex-time multiplicative anchor. It does not exclude the continuous de Bruijn-Newman deformation or RH methods using different data.


## Lean formalization — IN PROGRESS (2026-08-17)

Module: `formal/GaloisForLFunctions/HTGeometry/QuadraticSubtypeCanonicalDivisor.lean`
(namespace `GaloisForLFunctions.QuadraticSubtypeDivisor`, wired into the
`GaloisForLFunctions.HTGeometry` umbrella; builds green, every result below axiom-clean).

**Proved.**

| Card step | Lean name |
|---|---|
| the growth class `(1)` | `QuadraticSubtypeZero` |
| `(1) ⟹ ordinary order zero` (step 1, first half) | `orderZero_of_quadraticSubtypeZero` |
| **step 2**, Jensen ⟹ `n_f(r) = o(log r)` — i.e. `(3)` | `divisorCount_le_of_quadraticSubtypeZero` |
| **step 3**, exponent of convergence zero: `∑ ‖a k‖^{-α} < ∞` ∀α>0 | `summable_rpow_neg`, `summable_inv_norm` |
| the genus-zero product converges | `multipliable_genusZero`, `multipliable_genusZero_of_sublogDensity` |
| **step 4**, the estimate (8)–(10) | `logSum_le` |
| **the converse direction `(4) ⟹ (5)`** | `logNorm_genusZeroProduct_le_of_sublogDensity` |
| the constraint-reformulation lemma (zero-free + `(1)` ⟹ constant) | `entire_reBound_sq_imp_const` |

Supporting: `divisorSeqCount`, `SublogDensity`, `succ_le_divisorSeqCount`,
`eventually_mul_le_log_norm` (the counting bound `n(r) = o(log r)` converted into the per-index
bound `C·k ≤ log‖a k‖` for every `C`, which replaces the card's Stieltjes integrals by plain series
manipulation), `genusZeroProduct`, `summable_logOnePlus`, `log_norm_genusZeroProduct_le`,
`log_le_eight_rpow`.

**Still open: the Hadamard factorization `(2)`.**  Two sub-tasks remain.

1. *An enumeration of the zero divisor.*  The current estimates are stated for a divisor presented
   as a sequence of nondecreasing modulus.  For the forward direction the divisor comes from `f`,
   so it must be produced.  The clean route is to drop the ordering and index the product by the
   countable type `Σ (w : {w // w ≠ 0 ∧ f w = 0}), Fin (analyticOrderAt f w).toNat` — a definition
   with no recursion and no choice — and to redo `summable_rpow_neg` and `logSum_le` for a general
   countable index by dyadic bucketing.  The replacement for `logSum_le` is a three-bucket split
   `‖a i‖ ≤ √r`, `√r < ‖a i‖ ≤ r²`, `‖a i‖ > r²`: the first two buckets are counted by
   `n(√r) ≤ (ε/2)log r` and `n(r²) ≤ 2ε log r`, and the third is bounded by the convergent
   `∑ ‖a i‖^{-1/2}` because `log(1+r/t) ≤ r/t ≤ t^{-1/2}` there.  This needs neither monotonicity
   nor Abel summation.
2. *The quotient is constant.*  The textbook proof needs a minimum-modulus (Cartan/Boutroux)
   estimate for the canonical product, which neither mathlib nor this tree has — the tree's own
   ξ-Hadamard chain takes the corresponding real-part bound as a hypothesis
   (`RHTower/XiHadamardFactorization.lean`, `xiHadamardQuotient_constant_of_log_reBound`).  The
   route that avoids it is to bound the **Nevanlinna characteristic** of `h = f · P⁻¹` instead of
   its modulus.  mathlib carries the toolkit in `Mathlib/Analysis/Complex/ValueDistribution/`:
   `characteristic_mul_top_le` gives `T(r,h) ≤ T(r,f) + T(r,P⁻¹)`, the first main theorem
   (`characteristic_sub_characteristic_inv_le`) gives `T(r,P⁻¹) = T(r,P) + O(1)`, and
   `T ≤ log⁺M` (`HTGeometry/NevanlinnaEntireCharacteristic.lean`,
   `characteristic_top_le_posLog_of_bound`) makes both `o((log r)²)` — the second one *because of*
   `logNorm_genusZeroProduct_le_of_sublogDensity` above.  Then `log M_h(r) ≲ T(2r,h)`
   (`HTGeometry/PoissonJensenUpperBound.lean`, `log_norm_le_proximity_and_count_of_entire`) feeds
   `entire_reBound_sq_imp_const`, which is already proved.

The card stays in stage 2 until `(2)` is closed.

## Log

- 2026-07-11 — Proved the exact quadratic-subtype/sublogarithmic-divisor equivalence and isolated the logarithmic divisor-density floor as the intrinsic open law.
