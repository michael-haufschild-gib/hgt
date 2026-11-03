import GaloisForLFunctions.WindowTowerOfSpecZ.TheSecondStageIsAWeightedPath

/-!
# The second-stage path is attained

The path `x + ℓ₂ —2— x —3— x + ℓ₃ —2— x + ℓ₃ − ℓ₂` (`ℓ_n = log n`) fits in every window of length
`log 3 < A < log 4`. Four narrow bumps at its vertices, with the alternating amplitudes
`(α, −1, 1, −α)`, give the second-stage form the value `2(1 − α² − β)‖φ‖²`, negative as soon as
`α² + β > 1`
(`exists_neg_secondStage`): the path Picone bound of `TheSecondStageIsAWeightedPath` is sharp.

* **The exact second-stage form** (`secondStage_nonneg_iff`): for `α, β ≥ 0`,
  `‖H‖² + 2αc₂(H) + 2βc₃(H) ≥ 0` for every window test iff `α² + β ≤ 1`.
* **The exact Tate horizon of the second stage** (`tateFunction_nonneg_iff_secondStage`): for `k ≥ 0`,
  `ρ_A(J_k) ≥ 0` iff `((2^k − 1)/(2√2))² + (3^k − 1)/(2√3) ≤ 1`, i.e. iff `k ≤ 1.19966…`.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory MeasureTheory Set

variable {A : ℝ}

/-- Translates of a bump at distance at least `2r` have disjoint supports. -/
theorem bump_mul_eq_zero {r : ℝ} (φ : ContDiffBump (0 : ℝ)) (hr : φ.rOut = r) {a b : ℝ}
    (h : 2 * r ≤ b - a ∨ 2 * r ≤ a - b) (u : ℝ) : φ (u - a) * φ (u - b) = 0 := by
  by_contra hne
  have hs : ∀ v, φ v ≠ 0 → |v| < r := fun v hv => by
    have : v ∈ Function.support φ := hv
    rw [φ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, hr] at this
    exact this
  have h1 := abs_lt.mp (hs _ (left_ne_zero_of_mul hne))
  have h2 := abs_lt.mp (hs _ (right_ne_zero_of_mul hne))
  rcases h with h | h <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The path is attained**: on a second-stage window, if `α > 0` and `α² + β > 1`, some window test has
`‖H‖² + 2αc₂ + 2βc₃ < 0`. -/
theorem exists_neg_secondStage (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4) {α β : ℝ}
    (hc : 1 < α ^ 2 + β) :
    ∃ H, IsWindowTest A H ∧ (∫ u, H u ^ 2) + 2 * α * (∫ u, H u * H (u + Real.log 2)) +
      2 * β * (∫ u, H u * H (u + Real.log 3)) < 0 := by
  obtain ⟨h2, h23, h89, h4⟩ := log_facts
  rw [h4] at hA4
  set ℓ₂ := Real.log 2
  set ℓ₃ := Real.log 3
  set r := (A - ℓ₃) / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  have hro : φ.rOut = r := rfl
  set x := -A + 2 * r
  -- the four vertices of the path
  set p₁ := x + ℓ₂
  set p₂ := x
  set p₃ := x + ℓ₃
  set p₄ := x + ℓ₃ - ℓ₂
  set H : ℝ → ℝ := fun u => α * φ (u - p₁) - φ (u - p₂) + φ (u - p₃) - α * φ (u - p₄)
  have hgap : 4 * r < 2 * ℓ₂ - ℓ₃ := by rw [hrdef]; linarith
  have hφc : Continuous φ := φ.continuous
  have hsupp : ∀ v, φ v ≠ 0 → |v| < r := fun v hv => by
    have : v ∈ Function.support φ := hv
    rw [φ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, hro] at this
    exact this
  have hvan : ∀ p y, (y < -A ∨ 0 < y) → x ≤ p → p ≤ x + ℓ₃ → φ (y - p) = 0 := fun p y hy hp1 hp2 => by
    by_contra hne
    have := abs_lt.mp (hsupp _ hne)
    rcases hy with hy | hy <;> linarith [this.1, this.2]
  have hH : IsWindowTest A H := by
    refine ⟨?_, fun y hy => ?_⟩
    · have hd : ∀ p : ℝ, ContDiff ℝ 2 fun u => φ (u - p) := fun p =>
        φ.contDiff.comp (contDiff_id.sub contDiff_const)
      exact (((contDiff_const.mul (hd p₁)).sub (hd p₂)).add (hd p₃)).sub (contDiff_const.mul (hd p₄))
    · have hy' : y < -A ∨ 0 < y := by
        by_contra h; push Not at h; exact hy ⟨h.1, h.2⟩
      simp only [H, hvan p₁ y hy' (by linarith) (by linarith), hvan p₂ y hy' le_rfl (by linarith),
        hvan p₃ y hy' (by linarith) le_rfl, hvan p₄ y hy' (by linarith) (by linarith)]
      ring
  -- disjointness facts
  have z : ∀ a b, (2 * r ≤ b - a ∨ 2 * r ≤ a - b) → ∀ u, φ (u - a) * φ (u - b) = 0 :=
    fun a b h u => bump_mul_eq_zero φ hro h u
  have hsq : ∀ u, H u ^ 2 =
      α ^ 2 * φ (u - p₁) ^ 2 + φ (u - p₂) ^ 2 + φ (u - p₃) ^ 2 + α ^ 2 * φ (u - p₄) ^ 2 := fun u => by
    have z12 := z p₁ p₂ (Or.inr (by linarith)) u
    have z13 := z p₁ p₃ (Or.inl (by linarith)) u
    have z14 := z p₁ p₄ (Or.inr (by linarith)) u
    have z23 := z p₂ p₃ (Or.inl (by linarith)) u
    have z24 := z p₂ p₄ (Or.inl (by linarith)) u
    have z34 := z p₃ p₄ (Or.inr (by linarith)) u
    simp only [H]
    linear_combination (-2 * α) * z12 + (2 * α) * z13 + (-2 * α ^ 2) * z14 + (-2) * z23 +
      (2 * α) * z24 + (-2 * α) * z34
  -- the fold by `ℓ₂` links `p₂ → p₁` and `p₄ → p₃`
  have hc2 : ∀ u, H u * H (u + ℓ₂) = -α * φ (u - p₂) ^ 2 - α * φ (u - p₄) ^ 2 := fun u => by
    have e1 : u + ℓ₂ - p₁ = u - p₂ := by simp only [p₁, p₂]; ring
    have e2 : u + ℓ₂ - p₂ = u - (p₂ - ℓ₂) := by ring
    have e3 : u + ℓ₂ - p₃ = u - p₄ := by simp only [p₃, p₄]; ring
    have e4 : u + ℓ₂ - p₄ = u - (p₄ - ℓ₂) := by ring
    simp only [H, e1, e2, e3, e4]
    have a1 := z p₁ p₂ (Or.inr (by linarith)) u
    have a2 := z p₁ (p₂ - ℓ₂) (Or.inr (by linarith)) u
    have a3 := z p₁ p₄ (Or.inr (by linarith)) u
    have a4 := z p₁ (p₄ - ℓ₂) (Or.inr (by linarith)) u
    have b2 := z p₂ (p₂ - ℓ₂) (Or.inr (by linarith)) u
    have b3 := z p₂ p₄ (Or.inl (by linarith)) u
    have b4 := z p₂ (p₄ - ℓ₂) (Or.inr (by linarith)) u
    have c1 := z p₃ p₂ (Or.inr (by linarith)) u
    have c2 := z p₃ (p₂ - ℓ₂) (Or.inr (by linarith)) u
    have c3 := z p₃ p₄ (Or.inr (by linarith)) u
    have c4 := z p₃ (p₄ - ℓ₂) (Or.inr (by linarith)) u
    have d1 := z p₄ p₂ (Or.inr (by linarith)) u
    have d2 := z p₄ (p₂ - ℓ₂) (Or.inr (by linarith)) u
    have d4 := z p₄ (p₄ - ℓ₂) (Or.inr (by linarith)) u
    linear_combination α ^ 2 * a1 - α * a2 + α * a3 - α ^ 2 * a4 + b2 - b3 + α * b4 + α * c1
      - c2 + c3 - α * c4 - α ^ 2 * d1 + α * d2 + α ^ 2 * d4
  -- the fold by `ℓ₃` links `p₂ → p₃`
  have hc3 : ∀ u, H u * H (u + ℓ₃) = -φ (u - p₂) ^ 2 := fun u => by
    have e1 : u + ℓ₃ - p₁ = u - (p₁ - ℓ₃) := by ring
    have e2 : u + ℓ₃ - p₂ = u - (p₂ - ℓ₃) := by ring
    have e3 : u + ℓ₃ - p₃ = u - p₂ := by simp only [p₃, p₂]; ring
    have e4 : u + ℓ₃ - p₄ = u - (p₄ - ℓ₃) := by ring
    simp only [H, e1, e2, e3, e4]
    have a1 := z p₁ (p₁ - ℓ₃) (Or.inr (by linarith)) u
    have a2 := z p₁ (p₂ - ℓ₃) (Or.inr (by linarith)) u
    have a3 := z p₁ p₂ (Or.inr (by linarith)) u
    have a4 := z p₁ (p₄ - ℓ₃) (Or.inr (by linarith)) u
    have b1 := z p₂ (p₁ - ℓ₃) (Or.inr (by linarith)) u
    have b2 := z p₂ (p₂ - ℓ₃) (Or.inr (by linarith)) u
    have b4 := z p₂ (p₄ - ℓ₃) (Or.inr (by linarith)) u
    have c1 := z p₃ (p₁ - ℓ₃) (Or.inr (by linarith)) u
    have c2 := z p₃ (p₂ - ℓ₃) (Or.inr (by linarith)) u
    have c3 := z p₃ p₂ (Or.inr (by linarith)) u
    have c4 := z p₃ (p₄ - ℓ₃) (Or.inr (by linarith)) u
    have d1 := z p₄ (p₁ - ℓ₃) (Or.inr (by linarith)) u
    have d2 := z p₄ (p₂ - ℓ₃) (Or.inr (by linarith)) u
    have d3 := z p₄ p₂ (Or.inr (by linarith)) u
    have d4 := z p₄ (p₄ - ℓ₃) (Or.inr (by linarith)) u
    linear_combination α ^ 2 * a1 - α * a2 + α * a3 - α ^ 2 * a4 - α * b1 + b2 + α * b4 + α * c1
      - c2 + c3 - α * c4 - α ^ 2 * d1 + α * d2 - α * d3 + α ^ 2 * d4
  -- integrals of translated bumps
  have iφ : Integrable fun u => φ u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq hφc
    φ.hasCompactSupport
  have iφp : ∀ p, Integrable fun u => φ (u - p) ^ 2 := fun p => iφ.comp_sub_right p
  have hφp : ∀ p, ∫ u, φ (u - p) ^ 2 = ∫ u, φ u ^ 2 := fun p =>
    integral_sub_right_eq_self (μ := volume) (fun u => φ u ^ 2) p
  have hI : 0 < ∫ u, φ u ^ 2 := by
    rw [integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _) iφ]
    have : Function.support (fun u => φ u ^ 2) = Metric.ball (0 : ℝ) r := by
      rw [← hro, ← φ.support_eq]
      ext u
      simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero]
    rw [this, Real.volume_ball]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  set I := ∫ u, φ u ^ 2
  have hN : ∫ u, H u ^ 2 = (2 * α ^ 2 + 2) * I := by
    simp_rw [hsq]
    have i1 : Integrable fun u => α ^ 2 * φ (u - p₁) ^ 2 := (iφp p₁).const_mul _
    have i12 : Integrable fun u => α ^ 2 * φ (u - p₁) ^ 2 + φ (u - p₂) ^ 2 := i1.add (iφp p₂)
    have i123 : Integrable fun u => α ^ 2 * φ (u - p₁) ^ 2 + φ (u - p₂) ^ 2 + φ (u - p₃) ^ 2 :=
      i12.add (iφp p₃)
    have i4 : Integrable fun u => α ^ 2 * φ (u - p₄) ^ 2 := (iφp p₄).const_mul _
    rw [integral_add i123 i4, integral_add i12 (iφp p₃), integral_add i1 (iφp p₂),
      integral_const_mul, integral_const_mul, hφp, hφp, hφp, hφp]
    ring
  have hC2 : ∫ u, H u * H (u + ℓ₂) = -2 * α * I := by
    simp_rw [hc2]
    rw [integral_sub (((iφp p₂).const_mul _)) ((iφp p₄).const_mul _), integral_const_mul,
      integral_const_mul, hφp, hφp]
    ring
  have hC3 : ∫ u, H u * H (u + ℓ₃) = -I := by
    simp_rw [hc3]
    rw [integral_neg, hφp]
  refine ⟨H, hH, ?_⟩
  rw [hN, hC2, hC3]
  -- the value is `2(1 − α² − β) I`
  nlinarith [mul_pos (sub_pos.mpr hc) hI]

/-- **The exact second-stage form**: for `α, β ≥ 0`, `‖H‖² + 2αc₂ + 2βc₃ ≥ 0` on every window test of
length `log 3 < A < log 4` iff `α² + β ≤ 1`. -/
theorem secondStage_nonneg_iff (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (∀ H, IsWindowTest A H → 0 ≤ (∫ u, H u ^ 2) + 2 * α * (∫ u, H u * H (u + Real.log 2)) +
      2 * β * (∫ u, H u * H (u + Real.log 3))) ↔ α ^ 2 + β ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨H, hH, hneg⟩ := exists_neg_secondStage hA3 hA4 hc
    exact absurd (h H hH) (not_le.mpr hneg)
  · intro hc H hH
    have key := two_mul_abs_autocorr_add_le hA3 hA4 hH hα hβ hc
    have c2 := neg_abs_le (∫ u, H u * H (u + Real.log 2))
    have c3 := neg_abs_le (∫ u, H u * H (u + Real.log 3))
    nlinarith [mul_le_mul_of_nonneg_left c2 (by linarith : 0 ≤ 2 * α),
      mul_le_mul_of_nonneg_left c3 (by linarith : 0 ≤ 2 * β)]

/-- The Tate function on a second-stage window. -/
theorem tateFunction_secondStage (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) (k : ℝ) :
    tateFunction A H k = (∫ u, H u ^ 2) +
      2 * (((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2)) * (∫ u, H u * H (u + Real.log 2)) +
      2 * (((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3)) * (∫ u, H u * H (u + Real.log 3)) := by
  have hlev := windowLevel_eq_three hA3.le hA4
  rw [tateFunction_eq hH, hlev, show Finset.Icc 1 3 = {1, 2, 3} by decide,
    Finset.sum_insert (by decide), Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3), jordanTotient_one]
  have h2 : jordanTotient k 2 = (2 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_two k (a := 1) le_rfl
  have h3 : jordanTotient k 3 = (3 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_three k (a := 1) le_rfl
  rw [h2, h3]
  simp only [Nat.cast_one, Real.sqrt_one, div_one, one_mul, Real.log_one, add_zero, Nat.cast_ofNat]
  have e1 : ∫ u, H u * H u = ∫ u, H u ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])
  rw [e1]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring

/-- **The exact Tate horizon of the second stage**: for `k ≥ 0`, `ρ_A(J_k)` is a positive form on a
window of length `log 3 < A < log 4` iff `((2^k − 1)/(2√2))² + (3^k − 1)/(2√3) ≤ 1`. -/
theorem tateFunction_nonneg_iff_secondStage (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4) {k : ℝ}
    (hk : 0 ≤ k) :
    (∀ H, IsWindowTest A H → 0 ≤ tateFunction A H k) ↔
      (((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2)) ^ 2 + ((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3) ≤ 1 := by
  have ha : 0 ≤ ((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hk)) (by positivity)
  have hb : 0 ≤ ((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hk)) (by positivity)
  rw [← secondStage_nonneg_iff hA3 hA4 ha hb]
  exact forall₂_congr fun H hH => by rw [tateFunction_secondStage hA3 hA4 hH k]

end GaloisForLFunctions.WindowTowerOfSpecZ
