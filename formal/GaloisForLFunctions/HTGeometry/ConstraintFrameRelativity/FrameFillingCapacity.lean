import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ValuatedPluckerGram

/-!
# Filling capacity of a finite frame

The minimum-norm solution of an underdetermined constraint `T x = y` is `x₀ = T* G⁻¹ y` with
`G = T T*`, and its energy is the Gram form `⟪y, G⁻¹ y⟫`.  The Pythagoras identity
`‖x‖² = ‖x₀‖² + ‖x - x₀‖²` makes the minimum exact and its attainer unique.

Determinant magnitude controls the smallest eigenvalue only with an upper bound on the spectrum:
`λ_min ≥ det G / M^{r-1}` when every eigenvalue lies in `(0, M]`.

Cofinal strictness is a separate coordinate: uniform filling across an aperture system is exactly
a positive uniform lower bound on the least singular values, and a diagonal frame whose entries
tend to zero has every finite restriction onto while failing that bound.  Event depth and cofinal
strictness therefore determine one another in neither direction.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Matrix Finset

/-! ## The finite Hermitian form -/

variable {r n : ℕ}

/-- The Hermitian inner product of two coordinate vectors. -/
def frameInner (x y : Fin n → ℂ) : ℂ := ∑ k, (starRingEnd ℂ) (x k) * y k

/-- The squared norm of a coordinate vector. -/
def frameNormSq (x : Fin n → ℂ) : ℝ := ∑ k, Complex.normSq (x k)

theorem frameInner_self (x : Fin n → ℂ) : frameInner x x = ((frameNormSq x : ℝ) : ℂ) := by
  rw [frameInner, frameNormSq, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun _ _ => by
    rw [Complex.normSq_eq_conj_mul_self]

theorem frameNormSq_nonneg (x : Fin n → ℂ) : 0 ≤ frameNormSq x :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem frameNormSq_eq_zero {x : Fin n → ℂ} (h : frameNormSq x = 0) : x = 0 := by
  funext k
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ Complex.normSq (x j) :=
    fun j _ => Complex.normSq_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h k (Finset.mem_univ k)
  exact Complex.normSq_eq_zero.mp this

theorem frameInner_conj (x y : Fin n → ℂ) :
    frameInner y x = (starRingEnd ℂ) (frameInner x y) := by
  rw [frameInner, frameInner, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, Complex.conj_conj]; ring

theorem frameInner_add_left (x y z : Fin n → ℂ) :
    frameInner (x + y) z = frameInner x z + frameInner y z := by
  rw [frameInner, frameInner, frameInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Pi.add_apply, map_add]
    ring

theorem frameInner_add_right (x y z : Fin n → ℂ) :
    frameInner x (y + z) = frameInner x y + frameInner x z := by
  rw [frameInner, frameInner, frameInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Pi.add_apply]
    ring

/-- **The adjoint identity.**  The conjugate transpose is the adjoint of the frame. -/
theorem frameInner_conjTranspose (T : Matrix (Fin r) (Fin n) ℂ) (x : Fin n → ℂ)
    (z : Fin r → ℂ) : frameInner x (Tᴴ *ᵥ z) = frameInner (T *ᵥ x) z := by
  rw [frameInner, frameInner]
  have hleft : ∀ k : Fin n, (starRingEnd ℂ) (x k) * (Tᴴ *ᵥ z) k
      = ∑ i : Fin r, (starRingEnd ℂ) (x k) * ((starRingEnd ℂ) (T i k) * z i) := by
    intro k
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Matrix.conjTranspose_apply]
      rfl
  have hright : ∀ i : Fin r, (starRingEnd ℂ) ((T *ᵥ x) i) * z i
      = ∑ k : Fin n, (starRingEnd ℂ) (x k) * ((starRingEnd ℂ) (T i k) * z i) := by
    intro i
    rw [Matrix.mulVec_apply_eq_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_mul]
      ring
  rw [Finset.sum_congr rfl fun k _ => hleft k, Finset.sum_congr rfl fun i _ => hright i,
    Finset.sum_comm]

/-! ## The exact minimum filling energy -/

/-- **The exact minimum filling energy.**  With `G = T T*` invertible, `x₀ = T* G⁻¹ y` is the
unique minimum-norm solution of `T x = y`, and its energy is the Gram form `⟪y, G⁻¹ y⟫`. -/
theorem min_filling_energy (T : Matrix (Fin r) (Fin n) ℂ)
    (hG : IsUnit (T * Tᴴ).det) (y : Fin r → ℂ) :
    T *ᵥ (Tᴴ *ᵥ ((T * Tᴴ)⁻¹ *ᵥ y)) = y
      ∧ ((frameNormSq (Tᴴ *ᵥ ((T * Tᴴ)⁻¹ *ᵥ y)) : ℝ) : ℂ)
          = frameInner y ((T * Tᴴ)⁻¹ *ᵥ y)
      ∧ (∀ x : Fin n → ℂ, T *ᵥ x = y →
          frameNormSq (Tᴴ *ᵥ ((T * Tᴴ)⁻¹ *ᵥ y)) ≤ frameNormSq x)
      ∧ (∀ x : Fin n → ℂ, T *ᵥ x = y →
          frameNormSq x = frameNormSq (Tᴴ *ᵥ ((T * Tᴴ)⁻¹ *ᵥ y)) →
            x = Tᴴ *ᵥ ((T * Tᴴ)⁻¹ *ᵥ y)) := by
  classical
  set G : Matrix (Fin r) (Fin r) ℂ := T * Tᴴ with hGdef
  set z : Fin r → ℂ := G⁻¹ *ᵥ y with hz
  set x₀ : Fin n → ℂ := Tᴴ *ᵥ z with hx₀
  have hGz : G *ᵥ z = y := by
    have h1 : G *ᵥ (G⁻¹ *ᵥ y) = (G * G⁻¹) *ᵥ y := Matrix.mulVec_mulVec y G G⁻¹
    rw [hz, h1, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec]
  have hsol : T *ᵥ x₀ = y := by
    have h1 : T *ᵥ (Tᴴ *ᵥ z) = (T * Tᴴ) *ᵥ z := Matrix.mulVec_mulVec z T Tᴴ
    rw [hx₀, h1, ← hGdef, hGz]
  have hperp : ∀ x : Fin n → ℂ, T *ᵥ x = y → frameInner (x - x₀) x₀ = 0 := by
    intro x hx
    rw [hx₀, frameInner_conjTranspose]
    have hzero : T *ᵥ (x - x₀) = 0 := by
      rw [Matrix.mulVec_sub, hx, hsol, sub_self]
    rw [hzero, frameInner]
    simp
  have hsplit : ∀ x : Fin n → ℂ, T *ᵥ x = y →
      frameNormSq x = frameNormSq x₀ + frameNormSq (x - x₀) := by
    intro x hx
    have hx_eq : x = x₀ + (x - x₀) := by ring
    have hcross := hperp x hx
    have hcross' : frameInner x₀ (x - x₀) = 0 := by
      have := frameInner_conj (x - x₀) x₀
      rw [hcross, map_zero] at this
      exact this
    have hexp : frameInner x x = frameInner x₀ x₀ + frameInner (x - x₀) (x - x₀) := by
      conv_lhs => rw [hx_eq]
      rw [frameInner_add_left, frameInner_add_right, frameInner_add_right, hcross, hcross']
      ring
    rw [frameInner_self, frameInner_self, frameInner_self] at hexp
    exact_mod_cast hexp
  refine ⟨hsol, ?_, ?_, ?_⟩
  · rw [← frameInner_self, hx₀, frameInner_conjTranspose, hsol]
  · intro x hx
    rw [hsplit x hx]
    linarith [frameNormSq_nonneg (x - x₀)]
  · intro x hx heq
    have h := hsplit x hx
    rw [heq] at h
    have hzero : frameNormSq (x - x₀) = 0 := by linarith
    have hx' : x - x₀ = 0 := frameNormSq_eq_zero hzero
    exact sub_eq_zero.mp hx'

/-! ## Determinant magnitude controls the least eigenvalue only with a spectral bound -/

/-- **The determinant bound on the least eigenvalue.**  If every eigenvalue lies in `(0, M]`, the
least one is at least `det / M^{r-1}`. -/
theorem least_ge_prod_div {N : ℕ} (lam : Fin N → ℝ) (hpos : ∀ i, 0 < lam i) {M : ℝ}
    (hM : ∀ i, lam i ≤ M) (i₀ : Fin N) :
    (∏ i, lam i) ≤ lam i₀ * M ^ (N - 1) := by
  classical
  have hMpos : 0 < M := lt_of_lt_of_le (hpos i₀) (hM i₀)
  have hsplit : ∏ i, lam i = lam i₀ * ∏ i ∈ Finset.univ.erase i₀, lam i := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀)]
    ring
  have hcard : (Finset.univ.erase i₀).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hbound : ∏ i ∈ Finset.univ.erase i₀, lam i ≤ M ^ (N - 1) := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ => le_of_lt (hpos i)) fun i _ => hM i
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hbound (le_of_lt (hpos i₀))

/-! ## Cofinal strictness -/

/-- **Uniform filling is a uniform lower bound on the least singular values.** -/
theorem uniform_filling_iff (s : ℕ → ℝ) (hs : ∀ N, 0 < s N) :
    (∃ ε > 0, ∀ N, ε ≤ s N) ↔ ∃ C : ℝ, ∀ N, (s N)⁻¹ ^ 2 ≤ C := by
  constructor
  · rintro ⟨ε, hε, hle⟩
    refine ⟨(ε⁻¹) ^ 2, fun N => ?_⟩
    have h1 : (s N)⁻¹ ≤ ε⁻¹ := by
      exact inv_anti₀ hε (hle N)
    have h2 : 0 ≤ (s N)⁻¹ := le_of_lt (inv_pos.mpr (hs N))
    exact pow_le_pow_left₀ h2 h1 2
  · rintro ⟨C, hC⟩
    have hCpos : 0 < C := by
      have h0 := hC 0
      have hp : 0 < ((s 0)⁻¹) ^ 2 := pow_pos (inv_pos.mpr (hs 0)) 2
      linarith
    have hsqrtpos0 : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCpos
    refine ⟨(Real.sqrt C)⁻¹, inv_pos.mpr hsqrtpos0, fun N => ?_⟩
    have hsq : ((s N)⁻¹) ^ 2 ≤ C := hC N
    have hle : (s N)⁻¹ ≤ Real.sqrt C := by
      have h2 : Real.sqrt (((s N)⁻¹) ^ 2) ≤ Real.sqrt C := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (le_of_lt (inv_pos.mpr (hs N)))] at h2
    have hsqrtpos : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCpos
    have := inv_anti₀ (inv_pos.mpr (hs N)) hle
    rwa [inv_inv] at this

/-- **A vanishing diagonal has no uniform lower bound**, although every entry is nonzero. -/
theorem diagonal_not_bounded_below (lam : ℕ → ℂ) (hne : ∀ j, lam j ≠ 0)
    (hinf : Filter.Tendsto (fun j => ‖lam j‖) Filter.atTop (nhds 0)) :
    (∀ j, 0 < ‖lam j‖) ∧ ¬ ∃ ε > 0, ∀ j, ε ≤ ‖lam j‖ := by
  refine ⟨fun j => norm_pos_iff.mpr (hne j), ?_⟩
  rintro ⟨ε, hε, hle⟩
  have hev := hinf.eventually_lt_const hε
  obtain ⟨j, hj⟩ := hev.exists
  exact absurd (hle j) (not_le.mpr hj)

/-! ## Event depth and cofinal strictness are independent -/

open PowerSeries

/-- The scalar event family `t · I_N` has depth `N`. -/
theorem depth_scalar_family (N : ℕ) :
    (∀ i < N, coeff i (frameMinor
        ((PowerSeries.X : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
        (id : Fin N → Fin N)) = 0)
      ∧ coeff N (frameMinor
        ((PowerSeries.X : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
        (id : Fin N → Fin N)) = 1 := by
  have hdet : frameMinor
      ((PowerSeries.X : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
      (id : Fin N → Fin N) = (PowerSeries.X : PowerSeries ℂ) ^ N := by
    rw [frameMinor, Matrix.submatrix_id_id, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
  rw [hdet]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [PowerSeries.coeff_X_pow]
    exact if_neg (by omega)
  · rw [PowerSeries.coeff_X_pow, if_pos rfl]

/-- The constant family `τ · I_N` has depth zero, whatever `N`. -/
theorem depth_constant_family (N : ℕ) {τ : ℂ} (hτ : τ ≠ 0) :
    coeff 0 (frameMinor
      ((PowerSeries.C τ : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
      (id : Fin N → Fin N)) = τ ^ N ∧ (τ : ℂ) ^ N ≠ 0 := by
  refine ⟨?_, pow_ne_zero N hτ⟩
  have hdet : frameMinor
      ((PowerSeries.C τ : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
      (id : Fin N → Fin N) = (PowerSeries.C τ : PowerSeries ℂ) ^ N := by
    rw [frameMinor, Matrix.submatrix_id_id, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
  rw [hdet, ← map_pow, PowerSeries.coeff_zero_C]

/-- The strictness of a real diagonal frame is the least entry: the exact two-sided Rayleigh
bound. -/
theorem diagonal_strictness {N : ℕ} (lam : Fin N → ℝ) {i₀ : Fin N} (hmin : ∀ i, lam i₀ ≤ lam i)
    (hpos : ∀ i, 0 < lam i) (x : Fin N → ℂ) :
    (lam i₀) ^ 2 * frameNormSq x
      ≤ frameNormSq (fun i => (lam i : ℂ) * x i) := by
  rw [frameNormSq, frameNormSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have h1 : (lam i₀) ^ 2 ≤ lam i * lam i := by
    have := hmin i
    nlinarith [hpos i₀]
  exact mul_le_mul_of_nonneg_right h1 (Complex.normSq_nonneg _)

/-- The strictness bound is attained at a coordinate vector. -/
theorem diagonal_strictness_attained {N : ℕ} (lam : Fin N → ℝ) (i₀ : Fin N) :
    frameNormSq (fun i => (lam i : ℂ) * (Pi.single i₀ (1 : ℂ) : Fin N → ℂ) i)
      = (lam i₀) ^ 2 * frameNormSq (Pi.single i₀ (1 : ℂ) : Fin N → ℂ) := by
  classical
  rw [frameNormSq, frameNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  · rw [Pi.single_eq_of_ne h, mul_zero]
    simp

/-- **Event depth and cofinal strictness do not determine one another.**  The scalar event family
`t·I_N` has depth `N` and strictness `1`; the constant family `τ·I_N` has depth `0` and the same
strictness; and a diagonal family with entries tending to zero has every finite restriction onto
yet no uniform strictness. -/
theorem depth_strictness_independent (N : ℕ) {τ : ℂ} (hτ : τ ≠ 0)
    (lam : ℕ → ℂ) (hne : ∀ j, lam j ≠ 0)
    (hinf : Filter.Tendsto (fun j => ‖lam j‖) Filter.atTop (nhds 0)) :
    (∀ i < N, coeff i (frameMinor
        ((PowerSeries.X : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
        (id : Fin N → Fin N)) = 0)
      ∧ coeff N (frameMinor
        ((PowerSeries.X : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
        (id : Fin N → Fin N)) = 1
      ∧ coeff 0 (frameMinor
        ((PowerSeries.C τ : PowerSeries ℂ) • (1 : Matrix (Fin N) (Fin N) (PowerSeries ℂ)))
        (id : Fin N → Fin N)) ≠ 0
      ∧ (∀ j, 0 < ‖lam j‖)
      ∧ ¬ ∃ ε > 0, ∀ j, ε ≤ ‖lam j‖ := by
  obtain ⟨hlow, htop⟩ := depth_scalar_family N
  obtain ⟨hconst, hne0⟩ := depth_constant_family N hτ
  obtain ⟨hpos, hnb⟩ := diagonal_not_bounded_below lam hne hinf
  exact ⟨hlow, htop, by rw [hconst]; exact hne0, hpos, hnb⟩

end HTGeometry.ConstraintFrameRelativity
