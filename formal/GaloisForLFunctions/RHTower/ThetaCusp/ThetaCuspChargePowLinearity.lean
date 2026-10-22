import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargePowLowerOrder
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeHardyRigidity

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ### Growth and decay for every basis form -/

theorem exists_basis_source_cubic (j : ℕ) (hj : j ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      ‖modSource (thetaGroupBasis j) x‖ ≤ K * Real.exp (-|x| ^ 3 - |x|) := by
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay j
  replace hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis j τ‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; have := hM τ hτ; simpa [thetaGroupBasisCusp, hj] using this
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis j τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM τ hτ
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hF := differentiableOn_thetaGroupBasis j
  set X₃ : ℝ := Real.log 3 / 2 with hX₃
  have hX₃0 : 0 < X₃ := by have := Real.log_pos (by norm_num : (1:ℝ) < 3); positivity
  obtain ⟨xM, hxM, hmax⟩ := (isCompact_Icc (a := 0) (b := X₃)).exists_isMaxOn
    (nonempty_Icc.mpr hX₃0.le) (continuous_modSource hF).norm.continuousOn
  set B : ℝ := ‖modSource (thetaGroupBasis j) xM‖
  set K : ℝ := max (B * Real.exp (X₃ ^ 3 + X₃)) (20 * M * Real.exp π)
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨K, le_max_of_le_left (by positivity), ?_⟩
  have hpos : ∀ x : ℝ, 0 ≤ x →
      ‖modSource (thetaGroupBasis j) x‖ ≤ K * Real.exp (-x ^ 3 - x) := by
    intro x hx
    rcases le_or_gt x X₃ with hxX | hxX
    · have h1 : ‖modSource (thetaGroupBasis j) x‖ ≤ B := hmax ⟨hx, hxX⟩
      have h2 : 1 ≤ Real.exp (X₃ ^ 3 + X₃) * Real.exp (-x ^ 3 - x) := by
        rw [← Real.exp_add]; apply Real.one_le_exp
        have : x ^ 3 ≤ X₃ ^ 3 := pow_le_pow_left₀ hx hxX 3
        linarith
      calc ‖modSource (thetaGroupBasis j) x‖ ≤ B * (Real.exp (X₃ ^ 3 + X₃) * Real.exp (-x ^ 3 - x)) :=
            le_trans h1 (le_mul_of_one_le_right hB h2)
        _ = B * Real.exp (X₃ ^ 3 + X₃) * Real.exp (-x ^ 3 - x) := by ring
        _ ≤ K * Real.exp (-x ^ 3 - x) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have hy : 3 ≤ Real.exp (2 * x) := by
        have : Real.exp (2 * X₃) = 3 := by
          rw [hX₃, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
        rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
      have hub := norm_modSource_le_of_cuspDecay hF hM' hy
      set y := Real.exp (2 * x) with hydef
      have hy1 : 1 ≤ y := by linarith
      have hq : 3 * y + 2 * y ^ 2 ≤ 5 * y ^ 2 := by nlinarith
      have hy2 : Real.exp (x / 2) * y ^ 2 = Real.exp (9 * x / 2) := by
        rw [hydef, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      have hcube := nine_halves_sub_pi_exp_le hx
      calc ‖modSource (thetaGroupBasis j) x‖
          ≤ 4 * M * Real.exp π * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y) := hub
        _ ≤ 4 * M * Real.exp π * Real.exp (x / 2) * (5 * y ^ 2) * Real.exp (-π * y) := by gcongr
        _ = 20 * M * Real.exp π * Real.exp (9 * x / 2 - π * y) := by
            rw [Real.exp_sub, ← hy2, show -π * y = -(π * y) by ring, Real.exp_neg]; ring
        _ ≤ 20 * M * Real.exp π * Real.exp (-x ^ 3 - x) := by
            gcongr
        _ ≤ K * Real.exp (-x ^ 3 - x) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  intro x
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact hpos x hx
  · have h := hpos (-x) (by linarith)
    rw [modSource_neg hF (thetaGroupBasis_axis j)] at h
    rw [abs_of_nonpos hx]; exact h

/-! ### Order-`3/2` growth -/

theorem norm_thetaGroupXi_growth (j : ℕ) (hj : j ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖thetaGroupXi j z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨K, hK, henv⟩ := exists_basis_source_cubic j hj
  refine ⟨2 * K + 2, by positivity, fun z => ?_⟩
  set Y : ℝ := |z.im|
  have hY : 0 ≤ Y := abs_nonneg _
  set E : ℝ := Real.exp ((1 + Y) ^ (3 / 2 : ℝ)) with hE
  have hmaj : Integrable (fun x : ℝ => K * E * Real.exp (-(1 * |x|))) :=
    (integrable_exp_neg_mul_abs' one_pos).const_mul _
  have hpt : ∀ x : ℝ, ‖modXiIntegrand (thetaGroupBasis j) z x‖ ≤ K * E * Real.exp (-(1 * |x|)) := by
    intro x
    rw [norm_modXiIntegrand]
    have h1 : Real.exp (z.im * x) ≤ Real.exp (Y * |x|) :=
      Real.exp_le_exp.mpr (by
        have := abs_mul z.im x; have := le_abs_self (z.im * x); nlinarith [abs_nonneg x])
    have h2 : Y * |x| - |x| ^ 3 ≤ (1 + Y) ^ (3 / 2 : ℝ) := linear_sub_cube_le_rpow hY (abs_nonneg x)
    calc Real.exp (z.im * x) * ‖modSource (thetaGroupBasis j) x‖
        ≤ Real.exp (Y * |x|) * (K * Real.exp (-|x| ^ 3 - |x|)) :=
          mul_le_mul h1 (henv x) (norm_nonneg _) (Real.exp_pos _).le
      _ = K * Real.exp (Y * |x| - |x| ^ 3) * Real.exp (-(1 * |x|)) := by
          rw [mul_comm, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ K * E * Real.exp (-(1 * |x|)) := by
          gcongr
          rw [hE]; exact Real.exp_le_exp.mpr h2
  have hint : ‖thetaGroupXi j z‖ ≤ 2 * K * E := by
    unfold thetaGroupXi modXi
    calc ‖∫ x : ℝ, modXiIntegrand (thetaGroupBasis j) z x‖
        ≤ ∫ x : ℝ, ‖modXiIntegrand (thetaGroupBasis j) z x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, K * E * Real.exp (-(1 * |x|)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hmaj
            (Eventually.of_forall hpt)
      _ = 2 * K * E := by rw [integral_const_mul, integral_exp_neg_mul_abs_eq one_pos]; ring
  have hYz : 1 + Y ≤ 1 + ‖z‖ := by linarith [Complex.abs_im_le_norm z]
  have hr : (1 + Y) ^ (3 / 2 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hYz (by norm_num)
  have hr1 : 1 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  refine le_trans hint ?_
  have h2K : 2 * K ≤ Real.exp (2 * K) := by have := Real.add_one_le_exp (2 * K); linarith
  calc 2 * K * E ≤ Real.exp (2 * K) * Real.exp ((1 + ‖z‖) ^ (3 / 2 : ℝ)) :=
        mul_le_mul h2K (Real.exp_le_exp.mpr hr) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * K + (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by rw [Real.exp_add]
    _ ≤ Real.exp ((2 * K + 2) * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr; nlinarith


theorem tendsto_thetaGroupXi_atTop (j : ℕ) :
    Tendsto (fun r : ℝ => ‖thetaGroupXi j (r : ℂ)‖) atTop (𝓝 0) := by
  set k : ℝ → ℂ := modSource (thetaGroupBasis j) with hk
  have hRL := Real.tendsto_integral_exp_smul_cocompact k
  have hlin : Tendsto (fun r : ℝ => r / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have h := (hRL.comp hlin).norm
  rw [norm_zero] at h
  refine h.congr (fun r => ?_)
  simp only [Function.comp]
  congr 1
  unfold thetaGroupXi modXi modXiIntegrand
  congr 1; funext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1; congr 1
  push_cast; field_simp

theorem tendsto_thetaGroupXi_atTop_neg (j : ℕ) (hj : j ≠ 0) :
    Tendsto (fun r : ℝ => ‖thetaGroupXi j ((-r : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  refine (tendsto_thetaGroupXi_atTop j).congr (fun r => ?_)
  rw [Complex.ofReal_neg]; unfold thetaGroupXi
  rw [modXi_neg (differentiableOn_thetaGroupBasis j) (thetaGroupBasis_axis j)]


/-! ### Linearity over the basis -/

theorem modSource_zero_fun (x : ℝ) : modSource (fun _ : ℂ => (0 : ℂ)) x = 0 := by
  unfold modSource; simp

theorem modXi_sum_basis (a : ℕ → ℂ) (N : ℕ) (w : ℂ) :
    DifferentiableOn ℂ (fun τ => ∑ j ∈ Finset.range N, a j * thetaGroupBasis j τ) modUpperSet ∧
      Integrable (modXiIntegrand (fun τ => ∑ j ∈ Finset.range N, a j * thetaGroupBasis j τ) w) ∧
      modXi (fun τ => ∑ j ∈ Finset.range N, a j * thetaGroupBasis j τ) w =
        ∑ j ∈ Finset.range N, a j * thetaGroupXi j w := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    refine ⟨differentiableOn_const _, ?_, ?_⟩
    · have : modXiIntegrand (fun _ : ℂ => (0 : ℂ)) w = fun _ => 0 := by
        funext x; unfold modXiIntegrand; rw [modSource_zero_fun, mul_zero]
      rw [this]; exact integrable_zero _ _ _
    · unfold modXi
      have : modXiIntegrand (fun _ : ℂ => (0 : ℂ)) w = fun _ => 0 := by
        funext x; unfold modXiIntegrand; rw [modSource_zero_fun, mul_zero]
      rw [this]; simp
  | succ N ih =>
    obtain ⟨hd, hi, he⟩ := ih
    have hfun : (fun τ => ∑ j ∈ Finset.range (N + 1), a j * thetaGroupBasis j τ) =
        fun τ => (1 : ℂ) * (∑ j ∈ Finset.range N, a j * thetaGroupBasis j τ) +
          a N * thetaGroupBasis N τ := by
      funext τ; rw [Finset.sum_range_succ]; ring
    have hbN := differentiableOn_thetaGroupBasis N
    have hbNi := integrable_thetaGroupXiIntegrand N w
    rw [hfun]
    refine ⟨(hd.const_mul 1).add (hbN.const_mul (a N)), ?_, ?_⟩
    · have heq : modXiIntegrand (fun τ => (1 : ℂ) * (∑ j ∈ Finset.range N, a j * thetaGroupBasis j τ) +
          a N * thetaGroupBasis N τ) w = fun x =>
          (1 : ℂ) * modXiIntegrand (fun τ => ∑ j ∈ Finset.range N, a j * thetaGroupBasis j τ) w x +
            a N * modXiIntegrand (thetaGroupBasis N) w x := by
        funext x; unfold modXiIntegrand
        rw [modSource_linear_comb hd hbN]; ring
      rw [heq]; exact (hi.const_mul 1).add (hbNi.const_mul (a N))
    · rw [modXi_two_comb 1 (a N) hd hbN w hi hbNi, he, Finset.sum_range_succ]
      unfold thetaGroupXi; ring

theorem thetaGroupForm_map_eq_sum (P : Polynomial ℝ) (τ : ℂ) :
    thetaGroupForm (P.map (algebraMap ℝ ℂ)) τ =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℂ) * thetaGroupBasis j τ := by
  unfold thetaGroupForm
  rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_map, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.coeff_map]
  unfold thetaGroupBasis
  simp; ring

/-- **Linearity:** the transform of `θ₃P(h)` is `∑ cⱼ Ξⱼ`. -/
theorem modXi_thetaGroupForm_map (P : Polynomial ℝ) (w : ℂ) :
    modXi (thetaGroupForm (P.map (algebraMap ℝ ℂ))) w =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℂ) * thetaGroupXi j w := by
  have e : thetaGroupForm (P.map (algebraMap ℝ ℂ)) =
      fun τ => ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℂ) * thetaGroupBasis j τ :=
    funext (thetaGroupForm_map_eq_sum P)
  rw [e]
  exact (modXi_sum_basis (fun j => (P.coeff j : ℂ)) (P.natDegree + 1) w).2.2

end RHTower
