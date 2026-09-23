import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualWeightHeightDerivative

/-!
# Conductor-scale variation of the exact square-dual weight

The squared neutral chi carrier has derivative scale `O((1+tau)(1+|v|)^(5 : ℕ))`.  Gaussian
integration therefore gives `O((1+tau)/Y)` height variation for the exact square-dual weight.
At the natural square-AFE scale `Y = n x`, `x` comparable to height, this becomes the summable
coefficientwise gain `O(1/n)`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- A quintic polynomial is integrable against the standard Gaussian. -/
theorem integrable_one_add_abs_pow_five_mul_exp_neg_sq :
    Integrable (fun v : ℝ => (1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) := by
  have hk (k : ℕ) :
      Integrable (fun v : ℝ => |v| ^ k * Real.exp (-(v ^ 2))) := by
    have hraw := integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 : ℝ)) (s := (k : ℝ)) (by norm_num)
        (by have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using hraw.norm
  have h0 : Integrable (fun v : ℝ => Real.exp (-(v ^ 2))) := by
    simpa using hk 0
  have hsum := (((((h0.add ((hk 1).const_mul 5)).add
    ((hk 2).const_mul 10)).add ((hk 3).const_mul 10)).add
      ((hk 4).const_mul 5)).add (hk 5))
  refine hsum.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply]
  ring

/-- The squared neutral carrier gives a pointwise Gaussian majorant with only
one conductor power. -/
theorem exists_norm_smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y → ∀ v : ℝ,
      ‖smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y v‖ ≤
        (K * (1 + tau) / Y) *
          ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) := by
  obtain ⟨D, hD, hsharp⟩ :=
    exists_norm_deriv_smoothAFEZetaChiShiftRatioSq_le_global
  let K : ℝ := 3 * D
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro tau Y htau hY v
  have hsquare := hsharp htau v
  rw [(hasDerivAt_smoothAFEZetaChiShiftRatioSq tau v).deriv] at hsquare
  have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
    (show (0 : ℝ) < 1 by norm_num) v
  have hm' :
      ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
        (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
    simpa [Real.rpow_neg_one] using hm
  have hexp1 : Real.exp (1 : ℝ) ≤ 3 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  unfold smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand
  rw [norm_mul]
  calc
    ‖smoothAFEZetaChiShiftRatioSqHeightDerivative tau v‖ *
        ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
      ≤ (D * (1 + tau) * (1 + |v|) ^ 5) *
          ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
    _ ≤ (D * (1 + tau) * (1 + |v|) ^ 5) *
          ((Y⁻¹ * 3) * Real.exp (-(v ^ 2))) := by gcongr
    _ = (K * (1 + tau) / Y) *
          ((1 + |v|) ^ 5 * Real.exp (-(v ^ 2))) := by
        dsimp only [K]
        rw [inv_eq_one_div]
        ring

/-- At square-conductor scale, the exact square-dual weight changes at rate
`O((1+tau)/Y)`. -/
theorem exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_conductor_div_scale :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        A * (1 + tau) / Y := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand_le
  let q : ℝ → ℝ := fun v =>
    (1 + |v|) ^ 5 * Real.exp (-(v ^ 2))
  let M : ℝ := ∫ v : ℝ, q v
  let a : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := a * K * M
  have hq : Integrable q :=
    integrable_one_add_abs_pow_five_mul_exp_neg_sq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by
    dsimp only [q]
    positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact integral_nonneg hq0
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro tau Y htau hY
  have hcoef : 0 ≤ K * (1 + tau) / Y := by positivity
  have hboundInt : Integrable
      (fun v : ℝ => (K * (1 + tau) / Y) * q v) :=
    hq.const_mul (K * (1 + tau) / Y)
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y v‖ ≤
        ∫ v : ℝ, (K * (1 + tau) / Y) * q v := by
    apply norm_integral_le_of_norm_le hboundInt
    exact Filter.Eventually.of_forall fun v => hpoint htau hY v
  rw [(hasDerivAt_smoothAFEZetaSquareDualWeight hY tau).deriv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∫ v : ℝ,
          smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y v‖
      ≤ a * ∫ v : ℝ, (K * (1 + tau) / Y) * q v := by gcongr
    _ = a * ((K * (1 + tau) / Y) * M) := by
      rw [integral_const_mul]
    _ = A * (1 + tau) / Y := by
      dsimp only [A]
      ring

/-- On a dyadic height block, the exact square-dual carrier freezes with the
sharp conductor-over-scale Lipschitz constant. -/
theorem exists_norm_smoothAFEZetaSquareDualWeight_sub_le_dyadic :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {T Y tau u : ℝ}, 4 ≤ T → 0 < Y →
        tau ∈ Set.Icc T (2 * T) → u ∈ Set.Icc T (2 * T) →
        ‖smoothAFEZetaSquareDualWeight tau Y -
            smoothAFEZetaSquareDualWeight u Y‖ ≤
          (A * (1 + 2 * T) / Y) * |tau - u| := by
  obtain ⟨A, hA, hderiv⟩ :=
    exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_conductor_div_scale
  refine ⟨A, hA, ?_⟩
  intro T Y tau u hT hY htau hu
  let f : ℝ → ℂ := fun y => smoothAFEZetaSquareDualWeight y Y
  let C : ℝ := A * (1 + 2 * T) / Y
  have hdiff : ∀ y ∈ Set.Icc T (2 * T), DifferentiableAt ℝ f y := by
    intro y hy
    exact (hasDerivAt_smoothAFEZetaSquareDualWeight hY y).differentiableAt
  have hbound : ∀ y ∈ Set.Icc T (2 * T), ‖deriv f y‖ ≤ C := by
    intro y hy
    have hy4 : 4 ≤ y := hT.trans hy.1
    have hyupper : 1 + y ≤ 1 + 2 * T := by linarith [hy.2]
    have hraw := hderiv hy4 hY
    dsimp only [f, C] at hraw ⊢
    calc
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) y‖
        ≤ A * (1 + y) / Y := hraw
      _ ≤ A * (1 + 2 * T) / Y := by gcongr
  have hmvt := (convex_Icc T (2 * T)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound hu htau
  dsimp only [f, C] at hmvt ⊢
  simpa [Real.norm_eq_abs] using hmvt

/-- The square-dual weight gains one reciprocal smoothing scale while retaining
the expected square-conductor size. -/
theorem exists_norm_smoothAFEZetaSquareDualWeight_le_invScale :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (tau : ℝ) {Y : ℝ}, 0 < Y →
      ‖smoothAFEZetaSquareDualWeight tau Y‖ ≤
        K * (1 + |tau|) ^ 2 / Y := by
  let q : ℝ → ℝ := fun v =>
    (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))
  let M : ℝ := ∫ v : ℝ, q v
  let a : ℝ := 1 / (2 * Real.pi)
  let K : ℝ := a * 3 * M
  have hq : Integrable q := integrable_one_add_abs_sq_mul_exp_neg_sq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by
    dsimp only [q]
    positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact integral_nonneg hq0
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro tau Y hY
  let C : ℝ := 3 * (1 + |tau|) ^ 2 / Y
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hboundInt : Integrable (fun v : ℝ => C * q v) := hq.const_mul C
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaChiShiftRatioSq tau v *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        ∫ v : ℝ, C * q v := by
    apply norm_integral_le_of_norm_le hboundInt
    exact Filter.Eventually.of_forall fun v => by
      have hratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
        (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      have hexp1 : Real.exp (1 : ℝ) ≤ 3 := by
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      unfold smoothAFEZetaChiShiftRatioSq
      rw [norm_mul, norm_pow]
      calc
        ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ^ 2 *
              ‖smoothAFEMellinIntegrand Y
                (↑(1 : ℝ) + ↑v * I)‖
          ≤ ((1 + |tau|) * (1 + |v|)) ^ 2 *
              ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ ≤ ((1 + |tau|) * (1 + |v|)) ^ 2 *
              ((Y⁻¹ * 3) * Real.exp (-(v ^ 2))) := by gcongr
        _ = C * q v := by
          dsimp only [C, q]
          rw [inv_eq_one_div]
          ring
  unfold smoothAFEZetaSquareDualWeight
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∫ v : ℝ,
          smoothAFEZetaChiShiftRatioSq tau v *
            smoothAFEMellinIntegrand Y
              (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ a * ∫ v : ℝ, C * q v := by gcongr
    _ = a * (C * M) := by rw [integral_const_mul]
    _ = K * (1 + |tau|) ^ 2 / Y := by
      dsimp only [K, C]
      ring

end RHTower
