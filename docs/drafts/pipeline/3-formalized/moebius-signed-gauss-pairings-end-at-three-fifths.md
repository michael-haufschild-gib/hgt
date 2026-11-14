# Classification of Möbius-signed Gauss pairings and the universal three-fifths barrier

- **ID:** moebius-signed-gauss-pairings-end-at-three-fifths
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1311/obstacles-summary.md` §2.5 & §2.11
- **Statement:** No Möbius-signed Gauss/Jacobi monomial pairing `(c, k)` across all arities `r ≥ 1`, character orders `m_i ≥ 2`, splits `r = a + d` into `a` completed Gauss-sum factors and `d` Poisson row twists, and admissible periods `k` satisfies `c / (k - 1) < 3 / 5`, and none reaches the critical line (`c ≤ (k - 1) / 2`). Every valid Möbius-signed pairing satisfies `(c + 1) / k ≥ 2 / 3`, `c / (k - 1) ≥ 3 / 5` (`sInf {c / (k - 1)} = 3 / 5`, attained on `ZMod 7`), and `(c + 1/2) / k ≥ 7 / 12`, with `c / (k - 1) = 3 / 5` attained if and only if `(c, k) = (3, 6)` — uniquely realized among reduced row probes (`m_i ≥ 3`, `d ≥ 1`) by the canonical cubic-sextic pairing `(a, d) = (1, 1)`, `m_comp = 3`, `n_row = 6`, `k = 6`.

## Exact mathematical laws

Let `F` be a finite field of cardinality `Q = #F`, `ψ : AddChar F R` a primitive additive character with values in an integral domain `R`, and `χ₁, …, χ_r : MulChar F R` (`r ≥ 1`) nontrivial multiplicative characters (`χ_i ≠ 1`) with product `Π = ∏_{i=1}^r χ_i`. Put `δ_Π = 0` if `Π = 1` and `δ_Π = 1` if `Π ≠ 1`.

1. **Universal Jacobi conservation and Möbius parity law for Gauss monomials.**
   - *Exact factorization in `R`:* Repeated application of `g(α) g(β) = J(α, β) g(α β)` (`α β ≠ 1`) and `g(α) g(α⁻¹) = α(-1) Q` (`α β = 1`) factors the monomial in `R` as
     `∏_{i=1}^r g(χ_i) = ε · Q^P · (∏_{u=1}^{J_#} J(α_u, β_u)) · g_Π`,
     where `g_Π = 1` if `Π = 1` and `g_Π = g(Π)` if `Π ≠ 1`, `ε² = 1` (`ε = 1` whenever all `χ_i(-1) = 1`), every `(α_u, β_u)` is nontrivial (`α_u, β_u, α_u β_u ≠ 1`), and the exponents satisfy the exact conservation law
     `r = J_# + 2 P + δ_Π` (`P ≥ 1` whenever `Π = 1`).
   - *Congruence modulo `(μ - 1)²`:* If `χ_i^n = 1` for an integer `n > 2` with `n ∣ Q - 1` and `μ ∈ R` is a primitive `n`-th root of unity, each nontrivial Jacobi factor lies in `-1 + (μ - 1)² ℤ[μ]`, so there exists `z ∈ ℤ[μ]` such that
     `∏_{i=1}^r g(χ_i) = ε · ((-1)^{r - δ_Π} + z (μ - 1)²) · Q^P · g_Π`.
   - *Non-degeneracy of the congruence sign and Hasse–Davenport reduction:* For every odd prime power `n = p^{k+1}`, `N_{ℚ(ζ_{p^{k+1}})/ℚ}(ζ_{p^{k+1}} - 1) = p` is odd, hence `2 ∉ (ζ_{p^{k+1}} - 1) ℤ[ζ_{p^{k+1}}]` in any characteristic-zero integral domain `R`, so `-1` and `+1` are strictly distinct modulo `(ζ_{p^{k+1}} - 1)²`. For every odd-order character `χ` (`Odd m`, `χ^m = 1`, `χ ≠ 1`, `ringChar F ≠ 2`) paired with `χ⁻¹ q` (`q` quadratic, order `2 m`, including `(3, 6)`), Hasse–Davenport reduces `g(χ) g(χ⁻¹ q) = χ(4) J(χ, χ) g(q)` (`J(χ, χ⁻¹ q) = χ(4) J(χ, χ)`) directly to the odd-order Jacobi sum `J(χ, χ)`.
   - *Elimination of higher-order Gauss sums and Möbius parity criterion:* Eliminating uncompleted higher-order Gauss sums from `g_Π` requires `Π² = 1` (`Π = 1` or `Π` quadratic, since `g(χ₂)² = χ₂(-1) Q`), and carrying the odd Jacobi sign `(-1)^{J_#} = -1` requires `Odd J_#`, equivalently `Odd (r - δ_Π)`, i.e.,
     `(Π = 1 ∧ Odd r) ∨ (Π ≠ 1 ∧ Π² = 1 ∧ Even r)`.
   - *Quadratic stripping and character-order trichotomy:* Because `Fˣ` is cyclic, `MulChar F R` has at most one character of order `2`. Stripping all factors of order `2` (`S = {i | orderOf χ_i ≥ 3}`) preserves `Π_S² = 1` and `(Π_S = 1 ∧ Odd #S) ∨ (Π_S ≠ 1 ∧ Even #S)`, forcing `#S ≥ 2`. When `#S = 2` (`χ₁ χ₂ = χ_quad` of order `2`, `m_i = orderOf χ_i ≥ 3`), the orders `(m₁, m₂)` satisfy `m₂ ≥ 3`, `Even lcm(m₁, m₂)`, `4 ≤ lcm(m₁, m₂)`, and the exact trichotomy:
     - `Odd m₁ ⟹ m₂ = 2 m₁` and `lcm(m₁, m₂) = 2 m₁`;
     - `m₁ = 2 m₀` with `Odd m₀` (`m₀ ≥ 3`) `⟹ m₂ = m₀` and `lcm(m₁, m₂) = 2 m₀`;
     - `4 ∣ m₁ ⟹ m₂ = m₁` and `lcm(m₁, m₂) = m₁`.

2. **Universal `2/3` uncoupled, `3/5` coupled, and `7/12` GRH barriers across all Gauss pairings.**
   For any valid Möbius-signed tuple `(χ₁, …, χ_r)` (`m_i = orderOf χ_i ≥ 2`, primitive period `k₀ = lcm(m₁, …, m_r)`) realized with `a` completed `m_i`-th order Gauss-sum factors (`i ∈ A`, contributing `(1/2 - 1/m_i) k` from Kubota's normalizing factor `ζ_K(m_i w - (m_i - 2)/2)` under `w ↔ 1 - w`, i.e., completion periodicity `β_{m_i} = (m_i - 2)/2`) and `d` Poisson row twists (`j ∈ D`, `a + d = r`, each contributing `k/2 - 1`), at any admissible period `k` (`k = k₀` if `d = 0`; any multiple `k₀ ∣ k` with `k ≥ k₀` if `d ≥ 1`):
   `c = ∑_{i ∈ A} (1/2 - 1/m_i) k + d (k / 2 - 1)`.
   - *Universal inequalities:* Since `m_j ∣ k` implies `k / m_j ≥ 1`, `k/2 - 1 ≥ (1/2 - 1/m_j) k` (`d > 0` never lowers `c` below its `d = 0` counterpart at period `k`). Across all valid tuples and periods `k`:
     `c ≥ (2/3) k - 1`, `(c + 1) / k ≥ 2 / 3`, `c / (k - 1) ≥ 3 / 5`, and `(c + 1/2) / k ≥ 7 / 12`.
     In particular, `c / (k - 1) < 3 / 5` and `c ≤ (k - 1) / 2` have **no solution**, and `sInf {c / (k - 1)} = 3 / 5`.
   - *Equality rigidity:* `c / (k - 1) = 3 / 5` holds if and only if `(c, k) = (3, 6)`. Among reduced row probes (`m_i ≥ 3` for all `i` and `d ≥ 1`), `c / (k - 1) = 3 / 5` holds **if and only if** `compChars = [χ]` (`orderOf χ = 3`), `rowChars = [φ]` (`orderOf φ = 6`), and `period = 6`.

3. **Analytic and exponent-budget obstructions outside `(2, 6)`.**
   - *`GL₁` / unfactored Jacobi Liouville obstruction:* On the open unit disc `‖X‖ < 1`, the completely multiplicative local series with `-1` prime sign sums to `∑_{t ≥ 0} (-X)^t = (1 - X) / (1 - X²)`, introducing the denominator `1 - X²` (`L(2s, η²)`), whereas a holomorphic `GL₁` Hecke Euler product `(1 - ψ_J X)⁻¹` places `1 - ψ_J X` in the denominator rather than the numerator.
   - *Multi-row and higher-conductor positive-form obstructions:* For `d ≥ 2` row twists of order `n ≥ 3`, `lowBoundaryDesign d n ≥ 1` and `thetaDesign d n ≥ n / (n - 1) > 1`. By Kazhdan–Patterson, `GL̃_r` carries distinguished theta representations with prime Gauss-sum Whittaker coefficients only at `r = m` or `r = m - 1` (`GL̃₂` only for `m ∈ {2, 3}`), so any `m`-th order Gauss-sum theta row has conductor exponent `κ ≥ m - 1`. For `d = 1` row variable, the unslotted balanced corner for any `κ ≥ 5/2` and `n ≥ 1` satisfies
     `max(lowUnslotted κ n M, floorUnslotted n M) ≥ (3/2 - 1/n) (2κ - 1) / (2κ + 1)`
     for all `M ∈ ℝ`, with equality at `M = 4 / (2κ + 1)`. Combining `κ ≥ m - 1` with the order trichotomy (`m = 4 ⟹ n = 4`; `m ≥ 5 ⟹ κ ≥ 4, n ≥ 3`), **every** quadratic-product Gauss-sum probe with `m ≥ 4` satisfies
     `max(lowUnslotted κ n M, floorUnslotted n M) ≥ 25 / 28 > 7 / 8`
     and effective twist exponent
     `positiveFormTheta n (max(lowUnslotted κ n M, floorUnslotted n M)) ≥ 22 / 21 > 1`
     for all `M ∈ ℝ`.

4. **General `(c, k)` coupled-tower contraction and universal `3/5` floor.**
   For any real parameters `c` and `k > 1`, `pairingStep c k b = (c + b) / k` has unique fixed point `b_* = c / (k - 1)` and `R`-fold iterate `(pairingStep c k)^[R] b₀ = b_* + (b₀ - b_*) / k^R`. Any bounded sequence `Θ r ≤ 1` satisfying `Θ r ≤ max(σ₀, (c + Θ (r + 1)) / k)` (`c ≤ k - 1`) satisfies `Θ 0 ≤ max(σ₀, c / (k - 1))`, while `Θ r = c / (k - 1)` is a stationary solution whenever `σ₀ ≤ c / (k - 1)`. Combined with `c / (k - 1) ≥ 3 / 5`, every coupled continuation tower driven by a Möbius-signed Gauss-sum pairing has unconditional asymptotic floor `≥ 3 / 5 > 1 / 2` and GRH single-step floor `(c + 1/2) / k ≥ 7 / 12 > 1 / 2`.

## Lean 4 modules (`GaloisForLFunctions.FamilyContinuationTheory`)

1. `formal/GaloisForLFunctions/FamilyContinuationTheory/TheMoebiusParityOfAGaussMonomial.lean`
   - `gaussSum_mul_inv_eq_sign_card`, `GaussMonomialFactorization`, `gaussMonomialFactorization`, `exists_gaussMonomial_eq_mod_sub_one_sq`, `odd_jacobiPairs_length_iff`, `not_dvd_two_sub_one_of_odd_prime_pow`, `neg_one_ne_one_mod_sub_one_sq_of_odd_prime_pow`, `jacobiSum_quadraticChar_eq`, `gaussSum_mul_inv_mul_quadraticChar_eq`, `HasUniqueOrderTwo`, `mulChar_hasUniqueOrderTwo`, `MulChar.two_le_orderOf_iff_ne_one`, `IsMoebiusSignedTuple`, `isMoebiusSignedTuple_iff_gaussFactorization`, `nonQuadraticPart`, `nonQuadraticPart_moebius_parity`, `two_le_length_nonQuadraticPart`, `three_le_orderOf_mem_nonQuadraticPart`, `three_orders_of_prod_eq_one`, `quadratic_product_order_trichotomy`, `even_and_four_le_lcm_of_quadratic_product`.
2. `formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean`
   - `tupleOrderLcm`, `tupleOrderLcm_eq_or_lcm_two`, `MoebiusGaussPairing`, `MoebiusGaussPairing.pairingC`, `MoebiusGaussPairing.uncoupledBoundary`, `MoebiusGaussPairing.coupledBarrier`, `MoebiusGaussPairing.grhStepBoundary`, `MoebiusGaussPairing.three_le_period`, `MoebiusGaussPairing.alpha_sum_mul_period_le_pairingC`, `MoebiusGaussPairing.two_thirds_mul_period_sub_one_le_pairingC`, `MoebiusGaussPairing.two_thirds_le_uncoupledBoundary`, `MoebiusGaussPairing.three_fifths_le_coupledBarrier`, `MoebiusGaussPairing.seven_twelfths_le_grhStepBoundary`, `MoebiusGaussPairing.coupledBarrier_eq_three_fifths_iff`, `MoebiusGaussPairing.reduced_row_probe_eq_three_fifths_iff`, `not_exists_moebiusGaussPairing_lt_three_fifths`, `not_exists_moebiusGaussPairing_reaching_critical_line`, `exists_zmod_seven_canonical_pairing`, `sInf_coupledBarrier_eq_three_fifths`, `hasSum_liouville_local_series`, `corner_unslotted_ge_closedForm`, `corner_unslotted_attained`, `higher_order_quadratic_pair_budget_obstruction`, `multi_row_probe_budget_obstruction`, `pairingStep`, `pairingStep_fixedPoint_iff`, `iterate_pairingStep_eq`, `tendsto_iterate_pairingStep`, `abscissa_le_max_fixedPoint_of_tower`, `stationary_sequence_achieves_fixedPoint`, `moebiusGaussPairing_tower_floor_ge_three_fifths`, `moebius_signed_gauss_pairings_complete_solution`.

## Gates
- [x] 0 → 1  in-progress: well-posed classification problem from `obstacles-summary.md` §2.5 & §2.11
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof
- [x] 2 → 3  formalized: unconditional Lean 4 modules in `GaloisForLFunctions.FamilyContinuationTheory`, wired into `FamilyContinuationTheory.lean`, direct `lake --old env lean` source audits and `#print axioms` (`{propext, Classical.choice, Quot.sound}` only) PASS

## No-go closure
- **Failed claim:** Existence of a Möbius-signed Gauss/Jacobi pairing `(c, k)` with `c / (k - 1) < 3 / 5`, or reaching the critical line `c ≤ (k - 1) / 2`.
- **Exact killing theorem/mechanism:** In any finite field `F`, multiplying `r` nontrivial Gauss sums satisfies `r = J_# + 2 P + δ_Π`; eliminating higher-order Gauss sums (`Π² = 1`) while retaining an odd number `J_#` of `-1` Jacobi factors forces `#S ≥ 2` characters of order `≥ 3` with `(Π_S = 1 ∧ Odd #S) ∨ (Π_S ≠ 1 ∧ Even #S)`, while Kubota completion of an `m`-th order Gauss sum costs `(1/2 - 1/m) k` (`(m - 2)/2` periodicity) and each Poisson twist costs `k/2 - 1`. Across all valid orders and periods this locks `c ≥ (2/3) k - 1`, `(c + 1)/k ≥ 2/3`, and `c / (k - 1) ≥ 3 / 5`.
- **Strongest positive survivor:** Complete algebraic and analytic classification of all Möbius-signed Gauss-monomial pairings: (1) universal conservation and modulo-`(μ - 1)²` sign law `(-1)^{r - δ_Π}` with odd-prime-power non-degeneracy and universal Hasse–Davenport `(m, 2m)` reduction; (2) cyclic quadratic stripping and exact `(m, 2m)` / `(2m₀, m₀)` / `(4u, 4u)` order trichotomy; (3) sharp universal bounds `(c + 1)/k ≥ 2/3`, `c/(k - 1) ≥ 3/5` (`sInf = 3/5`), `(c + 1/2)/k ≥ 7/12` with unique `(3, 6)` / cubic-sextic equality rigidity; (4) `GL₁` Liouville `(1 - X)/(1 - X²)` obstruction, `d ≥ 2` multi-row design barrier `≥ 1`, and universal `m ≥ 4` budget barriers `σ_* ≥ 25/28 > 7/8`, `θ_* ≥ 22/21 > 1`; and (5) general `(c, k)` coupled-tower contraction and stationary optimality.
- **New insight:** Establishes unconditionally that `(c, k) = (3, 6)` (`m = 3, n = 6` on `GL̃₂` over `ℚ(ω)`) is the unique global optimum of the entire Gauss/Jacobi monomial producer class both in frame reach (`3/5`) and in positive-form twist budget (`θ < 1`), and proves that any producer reaching `Re s = 1/2` cannot be a Gauss-sum pairing — its Möbius sign must arise from a genuinely non-Gauss mechanism (`s < 1` pole, trace formula, or pre-Cauchy–Schwarz bilinear cancellation).
- **Status:** Unconditionally formalized in Lean 4 across `TheMoebiusParityOfAGaussMonomial.lean` and `MoebiusSignedGaussPairingsEndAtThreeFifths.lean` (`moebius_signed_gauss_pairings_complete_solution`), wired into `formal/GaloisForLFunctions/FamilyContinuationTheory.lean`.
