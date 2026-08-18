# Quadratic-Subtype Growth Equals Sublogarithmic Canonical Divisor Density

- **ID:** quadratic-subtype-canonical-divisor-equivalence
- **Stage:** 3-formalized / not new scientific knowledge
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
- [x] Formalization: complete.  Both directions, the Hadamard factorization `(2)`, and the constraint-reformulation lemma are unconditional and axiom-clean in Lean.

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

### Sub-task 1 is closed (2026-08-18)

New module `formal/GaloisForLFunctions/HTGeometry/CountableDivisorConvergenceExponent.lean`
(namespace `GaloisForLFunctions.CountableDivisor`, wired into the `HTGeometry` umbrella, builds
green, every result axiom-clean) redoes the whole converse direction for a divisor presented over
an **arbitrary index type** — no ordering, no enumeration, no monotonicity — exactly the shape the
zero divisor of `f` comes in.

| Content | Lean name |
|---|---|
| general bucket criterion for summability | `summable_of_bucket` |
| the divisor data: counting function, local finiteness, sublogarithmic density | `divisorIdxCount`, `LocallyFiniteDivisor`, `SublogDensityIdx` |
| `n(r) ≤ ε log r` eventually | `eventually_count_le` |
| the logarithmic bucket and its fibers | `logBucket`, `finite_logBucket_fiber`, `ncard_logBucket_fiber_le` |
| **exponent of convergence zero**: `∑_i ‖a i‖^{-α} < ∞` for every `α > 0` | `summable_rpow_neg_idx` |
| the genus-zero product converges | `summable_inv_norm_idx`, `multipliable_genusZeroIdx` |
| `log ‖P(z)‖ ≤ ∑_i log(1 + ‖z‖/‖a i‖)` | `log_norm_genusZeroProductIdx_le` |
| the divisor is bounded away from `0` | `exists_pos_lower_bound` |
| **the three-bucket estimate** | `tsum_log_le` |
| **`∑_i log(1 + r/‖a i‖) = o((log r)²)`** | `logSum_isLittleO_sq` |
| **the converse direction `(4) ⟹ (5)`** for an arbitrary index | `quadraticSubtypeZero_genusZeroProductIdx` |
| the product converges locally uniformly and is entire | `genusZeroProductIdx_hasProdLocallyUniformlyOn`, `genusZeroProductIdx_analytic` |
| no accidental zeros | `genusZeroProductIdx_ne_zero` |
| the multiplicity fiber is finite | `finite_fiber` |
| splitting off a subset of the index | `genusZeroProductIdx_split`, `tprod_fiber_eq`, `genusZeroProductIdx_eq_pow_mul` |
| **the divisor of the product**: `ord_w P = #{i : a i = w}` | `analyticOrderAt_genusZeroProductIdx` |

The Stieltjes integrals of the paper proof are replaced throughout by finite-sum manipulations:
`summable_rpow_neg_idx` buckets the index by `⌊log ‖a i‖⌋` (bucket `n` sits inside the disc of
radius `e^{n+1}`, so it has at most `n+1` points once `n` is large), and `tsum_log_le` bounds every
*finite* partial sum by splitting it with `Finset.filter` into `‖a i‖ ≤ √r`, `√r < ‖a i‖ ≤ r²`, and
`‖a i‖ > r²`; the first two are counted by `n(√r) ≤ (ε/2)log r` and `n(r²) ≤ 2ε log r`, and the
third is dominated by the convergent `∑_i ‖a i‖^{-1/2}` because `log(1+r/t) ≤ r/t ≤ t^{-1/2}` when
`t > r²`.

### Two more bricks landed (2026-08-18)

`formal/GaloisForLFunctions/HTGeometry/EntireQuotientNormalForm.lean`
(namespace `GaloisForLFunctions.EntireQuotient`) — **equal divisors force an entire nonvanishing
quotient**.  For entire `f`, `g` with `analyticOrderAt f z = analyticOrderAt g z` at every point and
`f` nowhere locally zero, `exists_entire_nonvanishing_quotient` produces an entire nowhere-zero `h`
with `f = h · g`.  The raw quotient `f / g` has meromorphic order zero everywhere but the wrong
*value* at each zero of `g`; `toMeromorphicNFOn` fills those removable singularities, and the
identity theorem propagates the product identity from a neighbourhood of one point where `g ≠ 0`.
This is the general form of the corpus's `xiHadamardQuotient` construction and is the exact tool
step `(2)` needs once the product's divisor is known.

`formal/GaloisForLFunctions/HTGeometry/EntireZeroDivisorIndex.lean`
(namespace `GaloisForLFunctions.EntireZeroDivisor`) — the zero divisor of an entire function indexed
with multiplicity: `ZeroSupport`, `ZeroCopy`, `zeroCopyPoint`, together with
`locallyFinite_zeroCopyPoint` (every disc meets the index in a finite set, from finiteness of the
divisor support on a compact set), `zeroCopyPoint_ne_zero` (when `f (0) ≠ 0`), and
`ncard_zeroCopy_fiber` (the fiber over `w` has exactly `(div f) w` elements).

### The forward direction is closed (2026-08-18)

`formal/GaloisForLFunctions/HTGeometry/QuadraticSubtypeHadamard.lean`
(namespace `GaloisForLFunctions.QuadraticSubtypeHadamard`) completes step `(2)`.

| Card step | Lean name |
|---|---|
| growth in class `(1)` bounds the proximity | `proximity_le_of_growth` |
| the divisor of a disc, restricted and global | `divisor_ball_apply`, `divisor_ball_apply_of_notMem` |
| **the zero-copy count is the divisor mass of the disc** | `divisorIdxCount_eq` |
| `n_f(r) = o(log r)` in indexed form | `sublogDensity_zeroCopyPoint` |
| **the canonical product realizes the divisor of `f`** | `analyticOrderAt_genusZeroProduct_eq` |
| **`f = c · P`** when `f (0) ≠ 0` | `exists_const_mul_genusZeroProduct` |
| splitting off the monomial preserves the growth class | `quadraticSubtypeZero_of_monomial_quotient` |
| **the card's equation `(2)`: `f = c z^m ∏ (1 - z/z_k)`** | `exists_monomial_const_mul_genusZeroProduct` |

Supporting bricks in `HTGeometry/EntireQuotientNormalForm.lean`: `entireQuotient_analytic_of_nonneg`,
`entireQuotient_mul_of_analytic`, `analyticOrderAt_monomial`, `exists_monomial_factorization`;
and in `HTGeometry/QuotientProximityBound.lean`: `proximity_quotient_le`,
`log_norm_le_three_mul_proximity`, `const_of_zeroFree_of_proximity_le_logSq`.

The textbook minimum-modulus (Cartan/Boutroux) estimate is never used.  The quotient `h = f / P` is
handled entirely in value-distribution terms: the first main theorem bounds `T(r, P⁻¹)` by
`T(r, P) + O(1)`, so `m(r, h) ≤ m(r, f) + m(r, P) + O(1)`, and both proximities are `o((log r)²)` —
the second one *because of* the converse direction proved earlier.  The Poisson bound then converts
that into `log |h(z)| ≤ B (log (2 + |z|))²`, and `entire_reBound_sq_imp_const` finishes.

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for every declaration
above; all modules are wired into the `GaloisForLFunctions.HTGeometry` umbrella and build.

## Log

- 2026-07-11 — Proved the exact quadratic-subtype/sublogarithmic-divisor equivalence and isolated the logarithmic divisor-density floor as the intrinsic open law.
