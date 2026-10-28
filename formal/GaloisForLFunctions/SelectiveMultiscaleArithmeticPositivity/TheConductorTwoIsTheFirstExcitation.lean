import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints

/-!
# The conductor two is the first excitation

The Ramanujan profile of conductor `m` is a quasimode of the full prime matrix `P_N` at energy
`log N − E_m`, `E_m = γ + log m + τ(m)`, `τ(m) = Σ_{p ∣ m} log p/(p − 1)` the tame different
(RenormalizedArithmeticPotentialTheory). The conductor `1` is the pole, `E_1 = γ`. Two facts locate the
next level.

* **The prime 2 is the bottleneck** (`two_mul_log_two_lt_log_add_tameDifferent`,
  `ramanujanAdjunctionEnergy_sub_one_ge`): `log m + τ(m) ≥ 2 log 2` for every `m ≥ 2`, with
  equality only at `m = 2`. So `E_m − E_1 ≥ 2 log 2 = E_2 − E_1`: the conductor `2` is the unique
  first excitation, and its excitation energy is the one-prime tower gap `p log p/(p − 1)` at `p = 2`.
* **The pole-hyperplane gap is at most `2 log 2`** (`eventually_exists_harmonic_atomicWeilForm_ge`):
  for every `ε > 0`, eventually in `N` some nonzero `x` with `Σ_{n ≤ N} x_n/√n = 0` has
  `P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`. The actual eigenvectors at `log N − E_1` and
  `log N − E_2` span a plane, and every plane meets the hyperplane.

So the uniform gap `g` of the prime form below its pole on the harmonic hyperplane
(`ThePrimeFormHasASpectralGapBelowItsPole`) satisfies `g ≤ 2 log 2`: the conjectured sharp value
`2 log 2` is an upper bound, attained by the `2`-adic excitation.
-/

noncomputable section

open Finset Filter Matrix

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticIntersectionTheory GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

/-! ### The adjunction energies above the pole -/

theorem tameDifferent_one : tameDifferent 1 = 0 := by simp [tameDifferent]

theorem tameDifferent_two : tameDifferent 2 = Real.log 2 := by
  rw [tameDifferent, Nat.Prime.primeFactors Nat.prime_two, sum_singleton]
  norm_num

theorem ramanujanAdjunctionEnergy_one : ramanujanAdjunctionEnergy 1 = γ := by
  simp [ramanujanAdjunctionEnergy, tameDifferent_one]

theorem ramanujanAdjunctionEnergy_two : ramanujanAdjunctionEnergy 2 = γ + 2 * Real.log 2 := by
  rw [ramanujanAdjunctionEnergy, tameDifferent_two]
  push_cast
  ring

theorem tameDifferent_nonneg (m : ℕ) : 0 ≤ tameDifferent m :=
  sum_nonneg fun p hp => div_nonneg (Real.log_natCast_nonneg p)
    (by have := (Nat.prime_of_mem_primeFactors hp).two_le; have : (2 : ℝ) ≤ p := by exact_mod_cast this
        linarith)

/-- A single prime factor's contribution bounds the tame different from below. -/
theorem log_div_le_tameDifferent {m p : ℕ} (hp : p ∈ m.primeFactors) :
    Real.log p / ((p : ℝ) - 1) ≤ tameDifferent m :=
  single_le_sum (f := fun q : ℕ => Real.log q / ((q : ℝ) - 1))
    (fun q hq => div_nonneg (Real.log_natCast_nonneg q)
      (by have := (Nat.prime_of_mem_primeFactors hq).two_le; have : (2 : ℝ) ≤ q := by exact_mod_cast this
          linarith)) hp

/-- **The prime 2 is the bottleneck**: `log m + τ(m) > 2 log 2` for every `m ≥ 3`. -/
theorem two_mul_log_two_lt_log_add_tameDifferent {m : ℕ} (hm : 3 ≤ m) :
    2 * Real.log 2 < Real.log m + tameDifferent m := by
  set p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd m, by omega⟩
  have hτ := log_div_le_tameDifferent hpm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogp : Real.log p ≤ Real.log m :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast Nat.minFac_le (by omega))
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by
      have h2 := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd (h ▸ hp) (by decide)
      · exact Or.inr (Or.inr h)) with h | h | h
  · -- `m` is even and at least `3`, so `m ≥ 4`
    have h4 : 4 ≤ m := by
      have h2m : 2 ∣ m := h ▸ Nat.minFac_dvd m
      omega
    have hlog4 : Real.log 4 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast h4)
    have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h] at hτ
    norm_num at hτ
    linarith
  · -- `3 log 3 > 4 log 2` since `27 > 16`
    rw [h] at hτ hlogp
    norm_num at hτ hlogp
    have h27 : Real.log 16 < Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
    have e16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have e27 : Real.log 27 = 3 * Real.log 3 := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  · -- `log p ≥ log 5 > log 4 = 2 log 2`
    have h5 : Real.log 5 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast h)
    have h45 : Real.log 4 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
    have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [tameDifferent_nonneg m]

/-- **The conductor two is the unique first excitation**: `E_m − E_1 ≥ 2 log 2` for every
`m ≥ 2`, with equality exactly at `m = 2`. -/
theorem ramanujanAdjunctionEnergy_sub_one_ge {m : ℕ} (hm : 2 ≤ m) :
    2 * Real.log 2 ≤ ramanujanAdjunctionEnergy m - ramanujanAdjunctionEnergy 1 ∧
      (ramanujanAdjunctionEnergy m - ramanujanAdjunctionEnergy 1 = 2 * Real.log 2 ↔ m = 2) := by
  rw [ramanujanAdjunctionEnergy_one, ramanujanAdjunctionEnergy]
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · have e : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [tameDifferent_two, e]
    exact ⟨by linarith, ⟨fun _ => rfl, fun _ => by ring⟩⟩
  · have := two_mul_log_two_lt_log_add_tameDifferent h3
    exact ⟨by linarith, ⟨fun h => by linarith, fun h => by omega⟩⟩

/-! ### Horizon vectors and the atomic form -/

/-- Zero extension of a vector on the integer horizon `[1, N]` to all of `ℕ`. -/
def horizonExtend {N : ℕ} (x : PrimeHorizonIndex N → ℝ) (n : ℕ) : ℝ :=
  if h : n ∈ Icc 1 N then x ⟨n, h⟩ else 0

@[simp] theorem horizonExtend_coe {N : ℕ} (x : PrimeHorizonIndex N → ℝ) (i : PrimeHorizonIndex N) :
    horizonExtend x i = x i := by
  simp [horizonExtend, i.2]

theorem sum_horizonExtend {N : ℕ} (x : PrimeHorizonIndex N → ℝ) (F : ℕ → ℝ → ℝ) :
    ∑ n ∈ Icc 1 N, F n (horizonExtend x n) = ∑ i : PrimeHorizonIndex N, F i (x i) := by
  rw [← Finset.sum_coe_sort (Icc 1 N)]
  simp only [horizonExtend_coe]

/-- The atomic prime form of a horizon vector is its quadratic form under the full prime matrix. -/
theorem atomicWeilForm_horizonExtend {N : ℕ} (x : PrimeHorizonIndex N → ℝ) :
    atomicWeilForm N (horizonExtend x) = x ⬝ᵥ (fullPrimeMatrix N *ᵥ x) := by
  unfold atomicWeilForm
  rw [← Finset.sum_coe_sort (Icc 1 N)]
  simp only [dotProduct, mulVec]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort (Icc 1 N), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [horizonExtend_coe, fullPrimeMatrix]
  ring

/-! ### Two eigenvectors meet the hyperplane -/

/-- Real eigenvectors of the full prime matrix are orthonormal. -/
theorem sum_eigenvector_mul {N : ℕ} (i j : PrimeHorizonIndex N) :
    ∑ k, ((fullPrimeMatrix_isHermitian N).eigenvectorBasis i) k *
        ((fullPrimeMatrix_isHermitian N).eigenvectorBasis j) k =
      if i = j then 1 else 0 := by
  have h := congrFun ((fullPrimeMatrix_isHermitian N).star_eigenvectorUnitary_mulVec j) i
  simp only [Matrix.mulVec, dotProduct, Matrix.star_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, star_trivial, Pi.single_apply] at h
  rw [h]

/-- On the plane of two eigenvectors the quadratic form is diagonal:
`Q(a e_i + b e_j) = a² λ_i + b² λ_j` and `|a e_i + b e_j|² = a² + b²` for `i ≠ j`. -/
theorem quadratic_eigenvector_plane {N : ℕ} {i j : PrimeHorizonIndex N} (hij : i ≠ j) (a b : ℝ) :
    let e := (fullPrimeMatrix_isHermitian N).eigenvectorBasis
    let lam := (fullPrimeMatrix_isHermitian N).eigenvalues
    (a • ⇑(e i) + b • ⇑(e j)) ⬝ᵥ (fullPrimeMatrix N *ᵥ (a • ⇑(e i) + b • ⇑(e j))) =
        a ^ 2 * lam i + b ^ 2 * lam j ∧
      ∑ k, (a • ⇑(e i) + b • ⇑(e j)) k ^ 2 = a ^ 2 + b ^ 2 := by
  intro e lam
  have hii := sum_eigenvector_mul i i
  have hjj := sum_eigenvector_mul j j
  have hij' := sum_eigenvector_mul i j
  have hji := sum_eigenvector_mul j i
  simp only [if_true, if_neg hij, if_neg (Ne.symm hij)] at hii hjj hij' hji
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    (fullPrimeMatrix_isHermitian N).mulVec_eigenvectorBasis,
    (fullPrimeMatrix_isHermitian N).mulVec_eigenvectorBasis]
  constructor
  · simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpt : ∀ k, (a * e i k + b * e j k) * (a * (lam i * e i k) + b * (lam j * e j k)) =
        (a ^ 2 * lam i) * (e i k * e i k) + (a * b * lam j) * (e i k * e j k) +
          (b * a * lam i) * (e j k * e i k) + (b ^ 2 * lam j) * (e j k * e j k) := fun k => by ring
    rw [sum_congr rfl fun k _ => hpt k]
    simp only [sum_add_distrib, ← mul_sum]
    rw [hii, hjj, hij', hji]
    ring
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpt : ∀ k, (a * e i k + b * e j k) ^ 2 =
        a ^ 2 * (e i k * e i k) + (2 * a * b) * (e i k * e j k) + b ^ 2 * (e j k * e j k) :=
      fun k => by ring
    rw [sum_congr rfl fun k _ => hpt k]
    simp only [sum_add_distrib, ← mul_sum]
    rw [hii, hjj, hij']
    ring

/-- **The pole-hyperplane gap of the prime form is at most `2 log 2`.** For every `ε > 0`,
eventually in `N` some nonzero `x` with `Σ_{n ≤ N} x_n/√n = 0` has
`P_N(x) ≥ (log N − γ − 2 log 2 − ε)|x|²`. -/
theorem eventually_exists_harmonic_atomicWeilForm_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧
      0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
      (Real.log N - γ - 2 * Real.log 2 - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set δ := min ε (Real.log 2 / 2)
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδl : δ ≤ Real.log 2 / 2 := min_le_right _ _
  filter_upwards [eventually_fullPrimeMatrix_eigenvalue_near one_pos hδ,
    eventually_fullPrimeMatrix_eigenvalue_near two_pos hδ] with N h₁ h₂
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  rw [ramanujanAdjunctionEnergy_one] at hi
  rw [ramanujanAdjunctionEnergy_two] at hj
  set lam := (fullPrimeMatrix_isHermitian N).eigenvalues
  set e := (fullPrimeMatrix_isHermitian N).eigenvectorBasis
  have hi' := abs_lt.mp hi
  have hj' := abs_lt.mp hj
  have hij : i ≠ j := fun h => by rw [h] at hi'; linarith
  -- both eigenvalues lie above `log N − γ − 2 log 2 − ε`
  have hli : Real.log N - γ - 2 * Real.log 2 - ε ≤ lam i := by linarith
  have hlj : Real.log N - γ - 2 * Real.log 2 - ε ≤ lam j := by linarith
  -- the harmonic coordinate of a horizon vector
  set ℓ : (PrimeHorizonIndex N → ℝ) → ℝ := fun v => ∑ k : PrimeHorizonIndex N, v k / Real.sqrt k
  -- choose the combination killing the harmonic coordinate
  obtain ⟨a, b, hab, hℓ⟩ : ∃ a b : ℝ, 0 < a ^ 2 + b ^ 2 ∧ a * ℓ ⇑(e i) + b * ℓ ⇑(e j) = 0 := by
    by_cases h0 : ℓ ⇑(e i) = 0
    · exact ⟨1, 0, by norm_num, by rw [h0]; ring⟩
    · exact ⟨ℓ ⇑(e j), -ℓ ⇑(e i), by positivity, by ring⟩
  obtain ⟨hQ, hM⟩ := quadratic_eigenvector_plane hij a b
  set v := a • ⇑(e i) + b • ⇑(e j)
  refine ⟨horizonExtend v, ?_, ?_, ?_⟩
  · rw [sum_horizonExtend v (fun n t => t / Real.sqrt n)]
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div, sum_add_distrib, mul_div_assoc,
      ← mul_sum]
    exact hℓ
  · rw [sum_horizonExtend v (fun _ t => t ^ 2), hM]
    exact hab
  · rw [sum_horizonExtend v (fun _ t => t ^ 2), hM, atomicWeilForm_horizonExtend, hQ]
    nlinarith [mul_le_mul_of_nonneg_left hli (sq_nonneg a), mul_le_mul_of_nonneg_left hlj (sq_nonneg b)]

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
