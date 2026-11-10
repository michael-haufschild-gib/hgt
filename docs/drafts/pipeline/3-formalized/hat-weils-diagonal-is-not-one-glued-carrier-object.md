# Weil's diagonal is not the finite part of one glued carrier object: refutation of (G) and exact structural invariants

- **ID:** hat-weils-diagonal-is-not-one-glued-carrier-object
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0911/fable.md` §5.3 (Question **(G)**), §9.4 C, §11.6; B133, B88
- **Statement:** Question **(G)** of `fable.md` §5.3 is **false**: no normalization of the coupled orbit sum on `X = Γ \ (ℍ³ × Π'_p PGL₂(ℚ_p)/PGL₂(ℤ_p))`, invariant under the rational torus and determined by `Δ_{ℍ³}` and `{A_p}_p` alone, has Weil's form (off-diagonal contacts plus jets, and packet diagonal equal to the Robin-normalized scattering tower with no further counterterm) as its finite part.

## Goal
Resolve Question **(G)** of `fable.md` §5.3 unconditionally in Lean 4, establishing both the exact positive structural bridges (foliation duality on `X`, the `AdelicGroup`-invariant critical Green product and its closed rational torus formula, and the archimedean digamma–Robin–coupled-orbit constant identity) and the four independent obstructions separating the arithmetic square, the adelic carrier `X`, and the modular scattering tower.

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional identities and obstructions
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3  formalized: Lean modules under `formal/GaloisForLFunctions/HyperbolicArakelovTheory/`, plain `lake --old env lean` PASS, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## Lean Declarations

- `GaloisForLFunctions.HyperbolicArakelovTheory.TheLeafAndHeckeSeparationOfTheAdelicCarrier` (`namespace CarrierSeparation`):
  - `same_finite_leaf_iff_isSquare`
  - `same_arch_orbit_iff_sum_two_squares`
  - `primeWord_eq_zero_and_weilDeltaKernel_pos`
  - `primeWord_indicator_degree_eq_zero_of_mod_four`
  - `primeOperator_indicator_degree_eq_zero`
- `GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledLocalProductObstructsOffDiagonalAndTorusInvariance` (`namespace CoupledProductObstruction`):
  - `adelicCriticalProduct_smul`
  - `localFactor_upperDegree_eq_treeGreen`
  - `adelicDegreeShift_smul_one`, `adelicDegreeShift_comm_torus`, `adelicCriticalProduct_torus_diag_eq`
  - `adelicCriticalProduct_torus_pos_rat`, `adelicCriticalProduct_degree_eq`, `adelicCriticalProduct_one_degree_eq`
  - `offDiag_torus_arch_collision`
  - `adelicCriticalProduct_pell_gt_half_inv`, `adelicCriticalProduct_one_two_pell_eq`, `not_summable_adelicCriticalProduct_torus_noncolliding`
  - `weilHeight_mul_prime_of_one_lt`, `weilHeight_ball_mul_prime_ssubset`
- `GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledOrbitDensityMatchesTheArchimedeanConstants` (`namespace ArchimedeanConstantBridge`):
  - `four_mul_regularMean_eq`, `gammaHardyPhaseRate_zero_eq_regularMean_add_robin`, `two_mul_gammaHardyPhaseRate_zero_eq`
  - `geometricWeilEnergy_shift`, `tendsto_geometricWeilEnergy_re_weilQuad`, `tendsto_geometricWeilEnergy_shift_re_weilQuad`
- `GaloisForLFunctions.HyperbolicArakelovTheory.WeilsDiagonalIsNotOneGluedCarrierObject` (`namespace GluedCarrierNoGo`):
  - `local_invariant_torus_diagonal_const`, `local_invariant_primitive_diagonal_const`
  - `dyadicNormalizedPairing_le_of_log_diag`, `tendsto_atBot_dyadicNormalizedPairing`, `torus_invariant_local_glued_form_diverges_from_tower`
  - `gramLocked_sub_scatteringTower_eq_neg_discriminant`, `gramLocked_sub_scatteringTower_prime_cube_jump`
  - `refutation_of_glued_carrier_question_G`

## Theorems and Proofs `[PROVED HERE]`

Let `V = Π'_p PGL₂(ℚ_p)/K_p` (`K_p = integralPGL p`), `GlobalSpace = ℍ³ × V`, `Γ = J⁻¹ SL₂(ℚ) J` (`J = (1, (w)_p)`), `X = Γ \ GlobalSpace`, and `x_n = (z_n, (diag(n, 1) K_p)_p)` for `n ∈ ℕ+`. Let `T(ℚ) = {γ_q = conjugateEmbedding(diag(q, q⁻¹)) : q ∈ ℚˣ} ≤ Γ` be the rational split torus.

### 1. Foliation duality and Hecke separation on `X` (`TheLeafAndHeckeSeparationOfTheAdelicCarrier`)

**Definition (Local determinant parity).** On `LocalGL p`, define `EvenPadicNorm p α := ∃ k : ℤ, ‖α‖_p = (p : ℝ) ^ (2 * k)`. Because `det(g · scalar c) = det g · c²` and `‖det(integralMap p h)‖_p = 1`, `EvenPadicNorm p g.val.det` descends to `EvenVertex p : LocalVertex p → Prop`.

**Theorem 1.1 (Foliation classification of `ℍ³`-leaves and archimedean orbits).**
1. `EvenVertex p` is invariant under `conjugateEmbedding g` for all `g ∈ SL₂(ℚ)`, satisfies `EvenVertex p (x_n.2.1 p) ↔ Even (n.factorization p)`, and flips under every tree adjacency `w ∈ neighbors p v` (`det(neighborRep p none) = p`, `‖p‖_p = p⁻¹`).
2. `(∃ γ ∈ Γ, (γ • x_n).2 = x_m.2) ↔ IsSquare ((m : ℕ) * n)` (`same_finite_leaf_iff_isSquare`).
   *(⇒)* Equal finite coordinates give `Even (n.factorization p) ↔ Even (m.factorization p)` for all primes `p`.
   *(⇐)* If `m * n = k²` (`k > 0`), `q = (k : ℚ) / m ∈ ℚˣ` satisfies `diag(q⁻¹, q) · diag(n, 1) = diag(m, 1) · scalar(q)`.
3. `(∃ γ ∈ Γ, (γ • x_n).1 = x_m.1) ↔ ∃ x y : ℕ, (m : ℕ) * n = x ^ 2 + y ^ 2` (`same_arch_orbit_iff_sum_two_squares`).
   *(⇒)* `g • z_n = z_m` (`g ∈ SL₂(ℚ)`) forces `g_{10}² + g_{11}² = 1 / m`, `g_{00} = -m n g_{11}`, `g_{01} = n g_{10}`, and `det g = 1` gives `n / m = (n g_{10})² + (n g_{11})²`, hence `m * n` is a rational and therefore integral sum of two squares (`Nat.eq_sq_add_sq_of_isSquare_mod_four`).
   *(⇐)* Conversely `m * n = x² + y²` yields explicit `g ∈ SL₂(ℚ)` sending `z_n ↦ z_m`.

**Theorem 1.2 (Unbounded place-rank obstruction, `primeWord_eq_zero_and_weilDeltaKernel_pos`).** For any finite set `S` of `≥ 2` primes, `N = ∏_{p ∈ S} p`, and any word `L` of length `< S.card`, `primeWord L 1_{[x_N]} ([x_1]) = 0` because each `primeOperator q` flips parity at `q` and preserves parity at all `r ≠ q`, while `weilDeltaKernel 1 N > 0` (`Λ(N) = 0` and `N ≥ 6 > ρ` past the plastic crossing).

**Theorem 1.3 (Single-step Hecke disjointness at all primes; full Hecke algebra disjointness at `p ≡ 3 mod 4`).**
1. For **every** prime `p`, `primeOperator p 1_{[x_p]} ([x_1]) = 0` (`primeOperator_indicator_degree_eq_zero`). Any collision `γ_g • replacePoint p x_1 v = x_p` (`v ∈ neighbors p (baseVertex p)`) forces `‖g_{10}‖_q, ‖g_{11}‖_q ≤ 1` for all `q ≠ p` and `(neighborRep p none)⁻¹ g_p u_p (neighborRep p none) ∈ GL₂(ℤ_p)` (`u_p ∈ GL₂(ℤ_p)`), giving `‖g_{10}‖_p ≤ p⁻¹ < 1` and `‖g_{11}‖_p ≤ 1`, hence `g_{10}, g_{11} ∈ ℤ`, contradicting `g_{10}² + g_{11}² = 1 / p`.
2. For every prime `p` with `p % 4 = 3` and every word `L`, `primeWord L 1_{[x_p]} ([x_1]) = 0` (`primeWord_indicator_degree_eq_zero_of_mod_four`).

### 2. The global `AdelicGroup`-invariant critical Green product (`TheCoupledLocalProductObstructsOffDiagonalAndTorusInvariance`)

**Definition (`adelicCriticalProduct`).** On `GL₂(ℚ_p)`, `glFactor p g := Real.sqrt ‖g.val.det‖ / matrixMaxNorm p g.val` is invariant under `scalar u` and `GL₂(ℤ_p)` on both sides, descending to `localFactor p : LocalVertex p → LocalVertex p → ℝ` with `localFactor_upperDegree_eq_treeGreen : localFactor p (x_m.2.1 p) (x_n.2.1 p) = treeGreen p (1/2) |v_p(m) - v_p(n)| / treeGreen p (1/2) 0 = p^{-|v_p(m) - v_p(n)|/2}`. Set `adelicCriticalProduct x y := archProfile (h3Dist x.1 y.1) * ∏ᶠ p, localFactor p (x.2.1 p) (y.2.1 p)`.

**Theorem 2.1 (`AdelicGroup` invariance, closed rational torus formula, and contact erasure).**
1. `adelicCriticalProduct (g • x) (g • y) = adelicCriticalProduct x y` for all `g ∈ AdelicGroup` (`adelicCriticalProduct_smul`).
2. For `a, b ∈ ℕ+` with `m * b² ≠ n * a²` and `q = (a : ℚ) / b`,
   `adelicCriticalProduct x_m (γ_q • x_n) = (Nat.gcd (n * b²) (m * a²) : ℝ) * max (m * b²) (n * a²) / |((n * a² : ℕ) : ℝ)² - ((m * b² : ℕ) : ℝ)²|` (`adelicCriticalProduct_torus_pos_rat`).
3. At `q = 1` (`m ≠ n`), `adelicCriticalProduct x_m x_n = gcd(m, n) * max(m, n) / |n² - m²|` (`adelicCriticalProduct_degree_eq`), and `adelicCriticalProduct x_1 x_n = n / (n² - 1)` for `n > 1` (`adelicCriticalProduct_one_degree_eq`), erasing `Λ(n)` by the product formula `∏_p p^{-v_p(n)/2} = n^{-1/2}`.

**Theorem 2.2 (Diagonal `n`-independence, off-diagonal collisions, Pell divergence, and height non-invariance).**
1. **Diagonal orbit isomorphism:** `adelicDegreeShift n = (diagSL2 √n, (diag(n, 1))_p) ∈ AdelicGroup` satisfies `adelicDegreeShift n • x_1 = x_n` and commutes with `torusElem q hq`, so `adelicCriticalProduct x_n (γ_q • x_n) = adelicCriticalProduct x_1 (γ_q • x_1)` (`adelicCriticalProduct_torus_diag_eq`), matching `CoupledOrbit.term 2` on `Primitive` (`adelicCriticalProduct_primitive_eq_term_two`).
2. **Off-diagonal square collisions (`offDiag_torus_arch_collision`):** For `k ≥ 2`, `[x_m] ≠ [x_{m k²}]`, `(γ_{1/k} • x_{m k²}).1 = x_m.1`, and `finiteGreenProduct = k⁻² > 0`.
3. **Off-diagonal Pell non-decay and universal non-summability:** Whenever `X² = 1 + m n Y²`, `q = (m Y : ℚ) / X` gives `adelicCriticalProduct x_m (γ_q • x_n) > 1 / (2 m)` (`adelicCriticalProduct_pell_gt_half_inv`), equal to `2 X² / (2 X² - 1) > 1` at `(1, 2)` (`adelicCriticalProduct_one_two_pell_eq`). For **all** `m, n ∈ ℕ+`, `q ↦ adelicCriticalProduct x_m (γ_q • x_n)` is not summable on `NonCollidingTorus m n` (`not_summable_adelicCriticalProduct_torus_noncolliding`).
4. **Height non-invariance under `T(ℚ)` (`weilHeight_mul_prime_of_one_lt`, `weilHeight_ball_mul_prime_ssubset`):** For `q > 1` and prime `p`, `weilHeight (p * q) = if p ∣ q.den then weilHeight q else p * weilHeight q`, so `{q > 1 | weilHeight (p * q) < N} ⊂ {q > 1 | weilHeight q < N}` for every `N ≥ 5`.

### 3. Archimedean constant bridge and tower shift invariance (`TheCoupledOrbitDensityMatchesTheArchimedeanConstants`)

**Theorem 3.1 (Density-row constant identity, `four_mul_regularMean_eq`, `gammaHardyPhaseRate_zero_eq_regularMean_add_robin`).**
`4 * CoupledOrbit.regularMean = -2 * gammaHardyPhaseRate 0 - (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)` and `gammaHardyPhaseRate 0 = -2 * regularMean + (robinCounterterm (1 / 2)).re - Real.eulerMascheroniConstant / 2`.

**Theorem 3.2 (Scattering-tower real packet limit and scale invariance, `geometricWeilEnergy_shift`, `tendsto_geometricWeilEnergy_shift_re_weilQuad`).**
For `F ∈ C_c²(ℝ)` and `c ∈ ℝ`, `(geometricWeilEnergy (fun u => (F (u - c) : ℂ)) N).re` equals `(geometricWeilEnergy (fun u => (F u : ℂ)) N).re` for every `N` and converges as `N → ∞` to `weilQuad F`.

### 4. Master refutation of (G) (`WeilsDiagonalIsNotOneGluedCarrierObject`)

**Theorem 4.1 (Constant-diagonal rigidity, `local_invariant_torus_diagonal_const`).**
For **every** `AdelicGroup`-invariant kernel `K₀ : GlobalSpace → GlobalSpace → ℝ` and **every** torus-orbit functional `ℛ : (ℚˣ → ℝ) → ℝ`, `ℛ(fun q => K₀ x_n (γ_q • x_n)) = ℛ(fun q => K₀ x_1 (γ_q • x_1))` is independent of `n`.

**Theorem 4.2 (`-¼ N log N` dyadic divergence against the scattering tower, `dyadicNormalizedPairing_le_of_log_diag`, `tendsto_atBot_dyadicNormalizedPairing`, `torus_invariant_local_glued_form_diverges_from_tower`).**
Every `B : ℕ → ℕ → ℝ` matching `weilDeltaKernel` off-diagonal with `B n n ≤ C * (1 + log n)` satisfies `dyadicNormalizedPairing B N ≤ 2 |C| (1 + log(2N)) + (17 / 4) N - (1 / 4) N log N → -∞` as `N → ∞`, whereas on shifted `C_c²` packets `F₀(u - log N)` the scattering-tower limit is identically `weilQuad F₀`.

**Theorem 4.3 (Exact discriminant defect and universal prime-cube jump on separated smooth packets, `gramLocked_sub_scatteringTower_eq_neg_discriminant`, `gramLocked_sub_scatteringTower_prime_cube_jump`).**
On separated `C_c²` packets `f = atomicTest N x g`, at `c₀ = -4 * regularMean - (log(4π) + γ) = 2 * gammaHardyPhaseRate 0`, `(lim_{r → 1⁻} gramLockedPacket) - (lim_{M → ∞} geometricWeilEnergy) = -(∫ g²) ∑_{n=1}^N x_n² selfIntersection n`. For **every** `c ∈ ℝ`, prime `p`, `N ≥ p³`, and `0 < ∫ g²`, `separatedPacketTowerDiscrepancy` jumps between `unitAtom p` and `unitAtom (p³)` by `-2 (∫ g²) log p < 0`, so at least one is nonzero.

## Log
- 2026-11-10 — Paper proof and unconditional Lean 4 formalization completed across four HAT modules (`refutation_of_glued_carrier_question_G`).
