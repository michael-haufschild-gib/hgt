import GaloisForLFunctions.RHTower.XiCosineShiftIsolatedDeepZero

/-!
# The cosine producer reads isolated zeros down to the near-double scale

Let `ζ₀ = γ₀ + iδ` be the spectral point of a zero copy of `ξ` with `δ > 0`.

**Theorem** (`exists_zero_cosShiftXi_of_depth_sq_log`). There is `L_c > 0`, and for every
multiplicity bound `M` a constant `T_c`, with the following property. Suppose `δ² log γ₀ ≥ T_c`, at
most `M` copies sit at `ζ₀` or `ζ̄₀`, and every other copy within horizontal distance `L_c/δ` of
`ζ₀` has `|Im| ≤ δ/4`. Then `cos((δ/4)D)Ξ` vanishes within `δ/4` of `ζ₀ − iδ/4`, above height
`δ/4`.

The governing parameter is `ν = δ² log γ₀`. The Riemann–von Mangoldt count certifies `≍ log γ₀`
shallow neighbours only in windows of length `≍ 1`, because its remainder is `O(log γ₀)`. On a
shift of size `h ≍ δ`, each such neighbour contracts the modulus by a factor `1 − κ` with `κ ≍ δ²`.
The certified crowd therefore beats the bounded losses once `ν` is large. This is a limit of
resolution, not of the cosine ladder: a crowd certified at a smaller scale `w`, with error
`o(w log γ₀)`, would give the same conclusion down to `δ ≍ 1/(w log γ₀)`.

The same parameter appears in the near-double problem: an isolated pair `½ ± δ + iγ` moves a zero
of `ζ'` by `½ log(γ/2π)·δ²`, and the first Laguerre inequality is open for `ν ≲ 1`.

**Proof.** Specialize `exists_zero_cosShiftXi_of_isolated_explicit` to `h = r = s₀ = η = δ/4`. The
crowding constant is `κ ≍ δ²`, so the isolation window is `O(1/δ)`. The constant term of the
growth comparison stays bounded, so the threshold height is `exp(O(1/δ²))`.
-/

open Complex ComplexConjugate Filter Topology Set Polynomial Metric

namespace RHTower.CosineNearDoubleScale

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn RHTower.CosineDefectBudget
  RHTower.CrowdedPersistence RHTower.CosineCrowdedPersistence RHTower.CosineIsolatedDeepZero

noncomputable section

theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

/-- The crowding constant at `h = r = s₀ = δ/4` is between `δ²/(4K₀)` and `1`, where
`K₀ = (H + 1)² + 4`. -/
theorem isoKappa_quarter_bounds {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    δ ^ 2 / (4 * ((isoH C + 1) ^ 2 + 4)) ≤ isoKappa C (δ / 4) (δ / 4) (δ / 4) ∧
      isoKappa C (δ / 4) (δ / 4) (δ / 4) ≤ 1 := by
  have hH : 1 ≤ isoH C := by rw [isoH]; have := Real.pi_pos; nlinarith
  have hden0 : 0 < (isoH C + δ / 4) ^ 2 + (1 + δ / 4) ^ 2 := by positivity
  have hden : (isoH C + δ / 4) ^ 2 + (1 + δ / 4) ^ 2 ≤ (isoH C + 1) ^ 2 + 4 := by
    have h1 : isoH C + δ / 4 ≤ isoH C + 1 := by linarith
    have h2 : 1 + δ / 4 ≤ 2 := by linarith
    have := pow_le_pow_left₀ (by linarith) h1 2
    have := pow_le_pow_left₀ (by linarith) h2 2
    linarith
  have hnum : 4 * (δ / 4) * (δ / 4) = δ ^ 2 / 4 := by ring
  rw [isoKappa, hnum]
  constructor
  · rw [show δ ^ 2 / (4 * ((isoH C + 1) ^ 2 + 4)) = δ ^ 2 / 4 / ((isoH C + 1) ^ 2 + 4) by
      rw [div_div]]
    exact div_le_div_of_nonneg_left (by positivity) hden0 hden
  · rw [div_le_one hden0]
    have : 1 ≤ (1 + δ / 4) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (isoH C + δ / 4)]

/-- The isolation window at `h = r = s₀ = δ/4` is at most `(H + 2 + 256πK₀)/δ`. -/
theorem isoL_quarter_le {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    isoL C (δ / 4) (δ / 4) (δ / 4) ≤
      (isoH C + 2 + 256 * Real.pi * ((isoH C + 1) ^ 2 + 4)) / δ := by
  obtain ⟨hκl, -⟩ := isoKappa_quarter_bounds hC hδ hδ1
  set κ := isoKappa C (δ / 4) (δ / 4) (δ / 4) with hκ
  set K₀ := (isoH C + 1) ^ 2 + 4 with hK₀
  have hK₀0 : 0 < K₀ := by positivity
  have hpi := Real.pi_pos
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκl
  have hH : 0 ≤ isoH C := by rw [isoH]; positivity
  have h1 : 256 * (δ / 4) / (κ * Real.pi⁻¹) ≤ 256 * Real.pi * K₀ / δ := by
    rw [div_le_div_iff₀ (by positivity) hδ]
    have := mul_le_mul_of_nonneg_left hκl (by positivity : (0 : ℝ) ≤ 256 * Real.pi * K₀ * Real.pi⁻¹)
    have e1 : 256 * Real.pi * K₀ * Real.pi⁻¹ * (δ ^ 2 / (4 * K₀)) = 256 * (δ / 4) * δ := by
      field_simp
    nlinarith
  have h2 : isoH C + 2 * (δ / 4) + 1 ≤ (isoH C + 2) / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  rw [isoL, add_div]
  linarith

/-- The constant term at `h = r = s₀ = δ/4` is bounded independently of `δ`. -/
theorem isoA_quarter_le {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (M : ℕ) :
    isoA C (δ / 4) (δ / 4) (δ / 4) M ≤
      ((M : ℝ) + 1) * Real.log 3 + |xiLineTwoLogDerivConstant + Real.log 3| +
        ((2 * C + Real.pi⁻¹) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) / 2 + 1 := by
  obtain ⟨hκl, hκu⟩ := isoKappa_quarter_bounds hC hδ hδ1
  set κ := isoKappa C (δ / 4) (δ / 4) (δ / 4) with hκ
  have hpi := Real.pi_pos
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκl
  have hip1 : Real.pi⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hL := isoL_pos (r := δ / 4) hC (by positivity : (0 : ℝ) < δ / 4) (by positivity)
    (by positivity : (0 : ℝ) < δ / 4)
  set L := isoL C (δ / 4) (δ / 4) (δ / 4) with hL_def
  have hLge : 256 * (δ / 4) / (κ * Real.pi⁻¹) ≤ L := by
    have : L = isoH C + 2 * (δ / 4) + 1 + 256 * (δ / 4) / (κ * Real.pi⁻¹) := rfl
    have hH : 0 ≤ isoH C := by rw [isoH]; positivity
    rw [this]; linarith
  have hu : 64 * (δ / 4) / L ≤ 1 := by
    rw [div_le_one hL]
    have h1 : 256 * (δ / 4) / (κ * Real.pi⁻¹) ≥ 256 * (δ / 4) := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      have : κ * Real.pi⁻¹ ≤ 1 := by nlinarith
      nlinarith
    nlinarith
  have hu0 : 0 ≤ 64 * (δ / 4) / L := by positivity
  have hlog : Real.log ((2 * (δ / 4) + δ / 4) / (δ / 4)) = Real.log 3 := by
    congr 1; field_simp; ring
  have hW : 0 ≤ (2 * C + Real.pi⁻¹) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M := by
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have t2 : 64 * (δ / 4) / L * (xiLineTwoLogDerivConstant + Real.log 3) ≤
      |xiLineTwoLogDerivConstant + Real.log 3| := by
    calc 64 * (δ / 4) / L * (xiLineTwoLogDerivConstant + Real.log 3)
        ≤ 64 * (δ / 4) / L * |xiLineTwoLogDerivConstant + Real.log 3| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hu0
      _ ≤ 1 * |xiLineTwoLogDerivConstant + Real.log 3| :=
          mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      _ = _ := one_mul _
  have t3 := mul_le_mul_of_nonneg_right hκu hW
  have t4 : κ * Real.pi⁻¹ / 4 ≤ 1 := by nlinarith
  rw [isoA, hlog]
  nlinarith

/-- The threshold height at `h = r = s₀ = δ/4` is at most `exp(T_c/δ²)`. -/
theorem isoT_quarter_le {C T₁ δ : ℝ} (hC : 0 < C) (hT₁ : 4 ≤ T₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (M : ℕ) :
    isoT C T₁ (δ / 4) (δ / 4) (δ / 4) M ≤ Real.exp
      ((max (T₁ + (isoH C + 2 + 256 * Real.pi * ((isoH C + 1) ^ 2 + 4)) + 4 + 4 * isoH C)
        (16 * Real.pi * ((isoH C + 1) ^ 2 + 4) *
          (((M : ℝ) + 1) * Real.log 3 + |xiLineTwoLogDerivConstant + Real.log 3| +
            ((2 * C + Real.pi⁻¹) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) / 2 + 1)) +
          1) / δ ^ 2) := by
  obtain ⟨hκl, -⟩ := isoKappa_quarter_bounds hC hδ hδ1
  set κ := isoKappa C (δ / 4) (δ / 4) (δ / 4) with hκ
  set K₀ := (isoH C + 1) ^ 2 + 4 with hK₀
  set Lc := isoH C + 2 + 256 * Real.pi * K₀ with hLc
  set A₀ := ((M : ℝ) + 1) * Real.log 3 + |xiLineTwoLogDerivConstant + Real.log 3| +
    ((2 * C + Real.pi⁻¹) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) / 2 + 1 with hA₀
  set B₀ := T₁ + Lc + 4 + 4 * isoH C with hB₀
  set Ka := 16 * Real.pi * K₀ * A₀ with hKa
  have hpi := Real.pi_pos
  have hK₀0 : 0 < K₀ := by positivity
  have hH : 0 ≤ isoH C := by rw [isoH]; positivity
  have hA₀0 : 0 ≤ A₀ := by
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκl
  have hδ2 : 1 ≤ 1 / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hδ1' : 1 / δ ≤ 1 / δ ^ 2 := by
    rw [div_le_div_iff₀ hδ (by positivity)]; nlinarith
  -- the exponent
  have hexp : isoA C (δ / 4) (δ / 4) (δ / 4) M / (κ * Real.pi⁻¹ / 4) ≤ Ka / δ ^ 2 := by
    have hA := isoA_quarter_le hC hδ hδ1 M
    have hden : δ ^ 2 * Real.pi⁻¹ / (16 * K₀) ≤ κ * Real.pi⁻¹ / 4 := by
      have := mul_le_mul_of_nonneg_right hκl (by positivity : (0 : ℝ) ≤ Real.pi⁻¹ / 4)
      calc δ ^ 2 * Real.pi⁻¹ / (16 * K₀) = δ ^ 2 / (4 * K₀) * (Real.pi⁻¹ / 4) := by ring
        _ ≤ κ * (Real.pi⁻¹ / 4) := this
        _ = κ * Real.pi⁻¹ / 4 := by ring
    calc isoA C (δ / 4) (δ / 4) (δ / 4) M / (κ * Real.pi⁻¹ / 4)
        ≤ A₀ / (κ * Real.pi⁻¹ / 4) := div_le_div_of_nonneg_right hA (by positivity)
      _ ≤ A₀ / (δ ^ 2 * Real.pi⁻¹ / (16 * K₀)) :=
          div_le_div_of_nonneg_left hA₀0 (by positivity) hden
      _ = Ka / δ ^ 2 := by rw [hKa]; field_simp
  have hL := isoL_quarter_le hC hδ hδ1
  have hsum : isoT C T₁ (δ / 4) (δ / 4) (δ / 4) M ≤ B₀ / δ ^ 2 + Real.exp (Ka / δ ^ 2) := by
    have e : isoT C T₁ (δ / 4) (δ / 4) (δ / 4) M = T₁ + isoL C (δ / 4) (δ / 4) (δ / 4) + 4 +
        4 * isoH C + Real.exp (isoA C (δ / 4) (δ / 4) (δ / 4) M / (κ * Real.pi⁻¹ / 4)) := rfl
    rw [e]
    have h1 : Real.exp (isoA C (δ / 4) (δ / 4) (δ / 4) M / (κ * Real.pi⁻¹ / 4)) ≤
        Real.exp (Ka / δ ^ 2) := Real.exp_le_exp.mpr hexp
    have h2 : Lc / δ ≤ Lc / δ ^ 2 := by
      have : 0 ≤ Lc := by positivity
      calc Lc / δ = Lc * (1 / δ) := by ring
        _ ≤ Lc * (1 / δ ^ 2) := mul_le_mul_of_nonneg_left hδ1' this
        _ = Lc / δ ^ 2 := by ring
    have h3 : T₁ + 4 + 4 * isoH C ≤ (T₁ + 4 + 4 * isoH C) / δ ^ 2 := by
      have : 0 ≤ T₁ + 4 + 4 * isoH C := by linarith
      calc T₁ + 4 + 4 * isoH C = (T₁ + 4 + 4 * isoH C) * 1 := (mul_one _).symm
        _ ≤ (T₁ + 4 + 4 * isoH C) * (1 / δ ^ 2) := mul_le_mul_of_nonneg_left hδ2 this
        _ = (T₁ + 4 + 4 * isoH C) / δ ^ 2 := by ring
    have h4 : B₀ / δ ^ 2 = (T₁ + 4 + 4 * isoH C) / δ ^ 2 + Lc / δ ^ 2 := by
      rw [hB₀]; ring
    linarith
  set m := max B₀ Ka with hm
  have hB : B₀ / δ ^ 2 ≤ m / δ ^ 2 :=
    div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hK : Ka / δ ^ 2 ≤ m / δ ^ 2 :=
    div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  have h5 : B₀ / δ ^ 2 + Real.exp (Ka / δ ^ 2) ≤ 2 * Real.exp (m / δ ^ 2) := by
    have := (le_exp_self _).trans (Real.exp_le_exp.mpr hB)
    have := Real.exp_le_exp.mpr hK
    linarith
  have h6 : 2 * Real.exp (m / δ ^ 2) ≤ Real.exp ((m + 1) / δ ^ 2) := by
    have h2e : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    have : Real.exp 1 * Real.exp (m / δ ^ 2) ≤ Real.exp ((m + 1) / δ ^ 2) := by
      rw [← Real.exp_add, Real.exp_le_exp, add_div]
      linarith
    nlinarith [Real.exp_pos (m / δ ^ 2)]
  exact hsum.trans (h5.trans h6)

/-- **Isolated zeros are read down to the near-double scale.** There is `L_c > 0` and, for every
multiplicity bound `M`, a constant `T_c` such that: if `ζ₀ = γ₀ + iδ` with `δ > 0` and
`γ₀ ≥ exp(T_c/δ²)`, at most `M` copies sit at `ζ₀` or `ζ̄₀`, and every other copy within horizontal
distance `L_c/δ` has `|Im| ≤ δ/4`, then `cos((δ/4)D)Ξ` vanishes within `δ/4` of `ζ₀ − iδ/4`, above
height `δ/4`. -/
theorem exists_zero_cosShiftXi_of_depth_sq_log :
    ∃ Lc : ℝ, 0 < Lc ∧ ∀ M : ℕ, ∃ Tc : ℝ, ∀ q₀ : XiZeroCopy, 0 < (xiSpectralPoint q₀).im →
      Real.exp (Tc / (xiSpectralPoint q₀).im ^ 2) ≤ (xiSpectralPoint q₀).re →
      (∀ G : Finset XiZeroCopy, (∀ q ∈ G, xiSpectralPoint q = xiSpectralPoint q₀ ∨
        xiSpectralPoint q = conj (xiSpectralPoint q₀)) → G.card ≤ M) →
      (∀ q, |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤
          Lc / (xiSpectralPoint q₀).im →
        xiSpectralPoint q ≠ xiSpectralPoint q₀ → xiSpectralPoint q ≠ conj (xiSpectralPoint q₀) →
        |(xiSpectralPoint q).im| ≤ (xiSpectralPoint q₀).im / 4) →
      ∃ z, ‖z - (xiSpectralPoint q₀ - ((xiSpectralPoint q₀).im / 4 : ℝ) * I)‖ ≤
          (xiSpectralPoint q₀).im / 4 ∧ (xiSpectralPoint q₀).im / 4 < z.im ∧
        cosShiftXi ((xiSpectralPoint q₀).im / 4) z = 0 := by
  obtain ⟨C, T₁, hC, hT₁, hwin⟩ := exists_window_lower_count
  have hpi := Real.pi_pos
  have hH : 0 ≤ isoH C := by rw [isoH]; positivity
  refine ⟨isoH C + 2 + 256 * Real.pi * ((isoH C + 1) ^ 2 + 4), by positivity, fun M => ?_⟩
  refine ⟨max (T₁ + (isoH C + 2 + 256 * Real.pi * ((isoH C + 1) ^ 2 + 4)) + 4 + 4 * isoH C)
    (16 * Real.pi * ((isoH C + 1) ^ 2 + 4) *
      (((M : ℝ) + 1) * Real.log 3 + |xiLineTwoLogDerivConstant + Real.log 3| +
        ((2 * C + Real.pi⁻¹) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) / 2 + 1)) + 1,
    fun q₀ hδ hT hmult hiso => ?_⟩
  set δ := (xiSpectralPoint q₀).im with hδ_def
  have hδ1 : δ ≤ 1 / 2 := (le_abs_self _).trans (abs_xiSpectralPoint_im_le q₀)
  have hq : (0 : ℝ) < δ / 4 := by positivity
  exact exists_zero_cosShiftXi_of_isolated_explicit hC hT₁ hwin hq hq hq M q₀ (δ / 4) hq.le
    (by linarith) ((isoT_quarter_le hC hT₁ hδ hδ1 M).trans hT) hmult
    fun q hq' hne1 hne2 => hiso q (hq'.trans (isoL_quarter_le hC hδ hδ1)) hne1 hne2

end

end RHTower.CosineNearDoubleScale
