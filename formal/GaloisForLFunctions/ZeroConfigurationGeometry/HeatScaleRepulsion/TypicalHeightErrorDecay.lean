import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SmallHeatErrorBounds
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightSourceEnvelopes

/-!
# Vanishing error envelopes for typical-height heat flow

The local variation tends to zero at the Gaussian scale. The lower tail
decays at a fixed linear exponential rate, and the far tail retains a
quadratic rate. Their envelopes depend only on the saddle slope.
-/

open Filter Topology
open _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

def typicalModelEnvelope (η α : ℝ) : ℝ :=
  2 * (typicalSlopeEnvelope η α / Real.sqrt α) *
    Real.exp ((1 + typicalSlopeEnvelope η α / Real.sqrt α) ^ 2)

def typicalFarConstant (η : ℝ) : ℝ :=
  4 * Real.exp 1 * (1 / (16 * η) + 2) + 1 / (8 * η)

def typicalFarEnvelope (η α : ℝ) : ℝ :=
  typicalFarConstant η * α * Real.exp (α - α ^ 2)

def typicalMainEnvelope (η α : ℝ) : ℝ :=
  2 * Real.exp (-(24 * η ^ 2 * α)) + Real.exp (-α ^ 2 + 5 / 8) +
    typicalModelEnvelope η α + typicalFarEnvelope η α

def typicalSlopeNormalizedEnvelope (η α : ℝ) : ℝ :=
  (2 + 3 / (16 * η)) * Real.exp (-(24 * η ^ 2 * α)) + typicalFarEnvelope η α +
    (typicalSlopeEnvelope η α / α) * (1 + typicalModelEnvelope η α)

def typicalOppositeEnvelope (η α : ℝ) : ℝ :=
  Real.exp (-(η * α)) + Real.exp (-(8 * η ^ 2 * α)) *
    (1 + typicalModelEnvelope η α) + typicalFarEnvelope η α

theorem typicalModelEnvelope_nonneg {η α : ℝ} (hα : 1 ≤ α) :
    0 ≤ typicalModelEnvelope η α := by
  unfold typicalModelEnvelope
  have := typicalSlopeEnvelope_nonneg (η := η) hα
  positivity

theorem typicalFarConstant_pos {η : ℝ} (hη : 0 < η) : 0 < typicalFarConstant η := by
  unfold typicalFarConstant
  positivity

theorem typicalFarEnvelope_nonneg {η α : ℝ} (hη : 0 < η) (hα : 0 ≤ α) :
    0 ≤ typicalFarEnvelope η α := by
  unfold typicalFarEnvelope
  have := (typicalFarConstant_pos hη).le
  positivity

theorem tendsto_typicalModelEnvelope (η : ℝ) :
    Tendsto (typicalModelEnvelope η) atTop (𝓝 0) := by
  have hq := tendsto_typicalSlopeEnvelope_div_sqrt η
  have he : Tendsto (fun α => Real.exp ((1 + typicalSlopeEnvelope η α / Real.sqrt α) ^ 2))
      atTop (𝓝 (Real.exp 1)) := by
    have hp := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hq).pow 2
    simpa only [Function.comp_def, add_zero, one_pow] using Real.continuous_exp.continuousAt.tendsto.comp hp
  unfold typicalModelEnvelope
  simpa only [mul_zero, zero_mul] using (hq.const_mul 2).mul he

private theorem tendsto_one_add_typicalModelEnvelope (η : ℝ) :
    Tendsto (fun α : ℝ => 1 + typicalModelEnvelope η α) atTop (𝓝 1) := by
  simpa only [add_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add
      (tendsto_typicalModelEnvelope η)

theorem tendsto_typicalFarEnvelope {η : ℝ} (hη : 0 < η) :
    Tendsto (typicalFarEnvelope η) atTop (𝓝 0) := by
  refine tendsto_of_le_mul_exp_quadratic (typicalFarConstant η) (c := 1) one_pos 2 0
    ((eventually_ge_atTop (0 : ℝ)).mono fun α hα => typicalFarEnvelope_nonneg hη hα) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with α hα
  have ha : α ≤ Real.exp α := by linarith only [Real.add_one_le_exp α]
  have hK := (typicalFarConstant_pos hη).le
  unfold typicalFarEnvelope
  calc
    _ ≤ typicalFarConstant η * Real.exp α * Real.exp (α - α ^ 2) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem tendsto_exp_neg_positive_linear {k : ℝ} (hk : 0 < k) :
    Tendsto (fun α : ℝ => Real.exp (-(k * α))) atTop (𝓝 0) := by
  have hh : Tendsto (fun α : ℝ => -(k * α)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hk)
  exact Real.tendsto_exp_atBot.comp hh

theorem tendsto_typicalMainEnvelope {η : ℝ} (hη : 0 < η) :
    Tendsto (typicalMainEnvelope η) atTop (𝓝 0) := by
  have hl := (tendsto_exp_neg_positive_linear (show 0 < 24 * η ^ 2 by positivity)).const_mul 2
  have hu : Tendsto (fun α : ℝ => Real.exp (-α ^ 2 + 5 / 8)) atTop (𝓝 0) := by
    simpa only [one_mul, zero_mul, add_zero, zero_add, sub_eq_add_neg, add_comm] using
      tendsto_mul_exp_quadratic 1 (c := 1) one_pos 0 (5 / 8)
  unfold typicalMainEnvelope
  simpa only [mul_zero, add_zero] using
    ((hl.add hu).add (tendsto_typicalModelEnvelope η)).add (tendsto_typicalFarEnvelope hη)

theorem tendsto_typicalSlopeNormalizedEnvelope {η : ℝ} (hη : 0 < η) :
    Tendsto (typicalSlopeNormalizedEnvelope η) atTop (𝓝 0) := by
  have hl := (tendsto_exp_neg_positive_linear (show 0 < 24 * η ^ 2 by positivity)).const_mul
    (2 + 3 / (16 * η))
  have hb : Tendsto (fun α : ℝ => typicalSlopeEnvelope η α / α) atTop (𝓝 0) := by
    have hh := tendsto_affineLog_div_self (96 / η ^ 2)
      ((96 * Real.log 8 + 216) / η ^ 2 + 4)
    convert hh using 1
    ext α
    unfold typicalSlopeEnvelope
    ring
  have hm := hb.mul (tendsto_one_add_typicalModelEnvelope η)
  unfold typicalSlopeNormalizedEnvelope
  simpa only [mul_zero, zero_mul, add_zero] using
    (hl.add (tendsto_typicalFarEnvelope hη)).add hm

theorem tendsto_typicalOppositeEnvelope {η : ℝ} (hη : 0 < η) :
    Tendsto (typicalOppositeEnvelope η) atTop (𝓝 0) := by
  have hl := tendsto_exp_neg_positive_linear hη
  have hm := (tendsto_exp_neg_positive_linear (show 0 < 8 * η ^ 2 by positivity)).mul
    (tendsto_one_add_typicalModelEnvelope η)
  unfold typicalOppositeEnvelope
  simpa only [zero_mul, add_zero] using
    (hl.add hm).add (tendsto_typicalFarEnvelope hη)

/-- Uniform comparison of the three actual error expressions with vanishing envelopes. -/
theorem typicalHalfGaussErrors_le_envelopes {η T τ α : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hα : 8 ≤ α)
    (hscale : 1 + Real.log (4 * T) ≤ 8 * α)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8)
    (hc : 16 * η ≤ 2 * τ * α) (hc2 : 2 * τ * α ≤ 2)
    (hb : typicalSlopeEnvelope η α ≤ 2 / 9 * α)
    (hlogC : typicalTailLogEnvelope η α ≤ η ^ 2 * α) :
    typicalHalfGaussError η T τ α ≤ typicalMainEnvelope η α ∧
    typicalHalfGaussSlopeError η T τ α ≤ α * typicalSlopeNormalizedEnvelope η α ∧
    typicalHalfGaussOppositeError η T τ α ≤ typicalOppositeEnvelope η α := by
  let B := typicalXiSlopeError η T
  let C := typicalXiTailFactor η T
  let b := typicalSlopeEnvelope η α
  let M := typicalModelEnvelope η α
  let F := typicalFarEnvelope η α
  let R := Real.exp (-(24 * η ^ 2 * α))
  have hα1 : 1 ≤ α := by linarith only [hα]
  have hα0 : 0 < α := by linarith only [hα]
  have hB : 0 ≤ B := (typicalXiSlopeError_pos (by linarith only [hT])).le
  have hC : 0 ≤ C := (typicalXiTailFactor_pos η T).le
  have hBb : B ≤ b := typicalXiSlopeError_le_envelope hη hT hα1 hscale
  have hb0 : 0 ≤ b := typicalSlopeEnvelope_nonneg hα1
  have hb' : b ≤ 2 / 9 * α := hb
  have hM0 : 0 ≤ M := typicalModelEnvelope_nonneg hα1
  have hF0 : 0 ≤ F := typicalFarEnvelope_nonneg hη hα0.le
  have hCexp : C ≤ Real.exp (η ^ 2 * α) :=
    (typicalXiTailFactor_le_envelope hη hT hα1 hscale).trans (Real.exp_le_exp.mpr hlogC)
  have hτα : τ * α ≤ 1 := by linarith only [hc2]
  have hdτ : 8 * η ≤ τ * α := by linarith only [hc]
  have hmodel : gaussianSaddleModelError B τ ≤ M :=
    gaussianSaddleModelError_le_inverse_scale hτ hα0 hB hBb hτα
  have hjoin : Real.exp (9 / 2 * B) ≤ Real.exp α := by
    apply Real.exp_le_exp.mpr
    linarith only [hBb, hb']
  have hfar0 := kklRC_add_kklRB_le_small_heat (show 0 < 8 * η by positivity)
    hτ hτ8 hdτ hα
  have hfar : Real.exp (9 / 2 * B) * (kklRC τ α + kklRB τ α) ≤ F := by
    calc
      _ ≤ Real.exp α *
          ((4 * Real.exp 1 * (1 / (2 * (8 * η)) + 2) + 1 / (8 * η)) *
            α * Real.exp (-α ^ 2)) :=
        mul_le_mul hjoin hfar0 (add_nonneg (kklRC_nonneg hτ hα0.le) (kklRB_nonneg hτ))
          (Real.exp_pos α).le
      _ = F := by
        dsimp only [F, typicalFarEnvelope, typicalFarConstant]
        rw [show Real.exp (α - α ^ 2) = Real.exp α * Real.exp (-α ^ 2) by
          rw [← Real.exp_add]; congr 1]
        ring
  have hfarC : Real.exp (9 / 2 * B) * kklRC τ α ≤ F :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (kklRB_nonneg hτ))
      (Real.exp_pos _).le).trans hfar
  have htail := exp_neg_div_heat_le (show 0 ≤ 25 * η ^ 2 by positivity) hτ hτα
  have hlower : C * Real.exp (-(25 * η ^ 2 / τ)) ≤ R := by
    calc
      _ ≤ Real.exp (η ^ 2 * α) * Real.exp (-(25 * η ^ 2 * α)) :=
        mul_le_mul hCexp htail (Real.exp_pos _).le (Real.exp_pos _).le
      _ = R := by dsimp only [R]; rw [← Real.exp_add]; congr 1; ring
  have htailR : Real.exp (-(25 * η ^ 2 / τ)) ≤ R := by
    refine htail.trans (Real.exp_le_exp.mpr ?_)
    nlinarith only [mul_nonneg (sq_nonneg η) hα0.le]
  have hpre := gaussian_slope_prefactor_le (show 0 < 8 * η by positivity) hτ hτ8 hdτ hα1
  have hslopeLower : C * (1 / (2 * τ) + α + 1 +
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ))) * Real.exp (-(25 * η ^ 2 / τ)) ≤
        α * ((2 + 3 / (16 * η)) * R) := by
    calc
      _ = (C * Real.exp (-(25 * η ^ 2 / τ))) *
          (1 / (2 * τ) + α + 1 + (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ R * ((2 + 3 / (2 * (8 * η))) * α) :=
        mul_le_mul hlower hpre (by positivity) (Real.exp_pos _).le
      _ = _ := by ring
  have hslopeModel : B * (1 + gaussianSaddleModelError B τ) ≤ b * (1 + M) :=
    mul_le_mul hBb (add_le_add le_rfl hmodel)
      (by have := gaussianSaddleModelError_nonneg (t := τ) hB; positivity) hb0
  have hopposite : C * Real.exp (-(8 * η * α)) ≤ Real.exp (-(η * α)) := by
    calc
      _ ≤ Real.exp (η ^ 2 * α) * Real.exp (-(8 * η * α)) :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le
      _ = Real.exp ((η ^ 2 - 8 * η) * α) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh : η ^ 2 - 8 * η ≤ -η := by
          nlinarith only [mul_le_mul_of_nonneg_left hη8 hη.le, hη]
        nlinarith only [mul_le_mul_of_nonneg_right hh hα0.le]
  have hoppositeMid : Real.exp (-(8 * η ^ 2 / τ)) * (1 + gaussianSaddleModelError B τ) ≤
      Real.exp (-(8 * η ^ 2 * α)) * (1 + M) :=
    mul_le_mul (exp_neg_div_heat_le (by positivity) hτ hτα) (add_le_add le_rfl hmodel)
      (by have := gaussianSaddleModelError_nonneg (t := τ) hB; positivity) (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_⟩
  · have hlow : (1 + C) * Real.exp (-(25 * η ^ 2 / τ)) ≤ 2 * R := by
      nlinarith only [htailR, hlower]
    exact add_le_add (add_le_add (add_le_add hlow (kklR2_le_small_heat hτ8)) hmodel) hfarC
  · calc
      _ ≤ α * ((2 + 3 / (16 * η)) * R) + F + b * (1 + M) :=
        add_le_add (add_le_add hslopeLower hfar) hslopeModel
      _ ≤ α * ((2 + 3 / (16 * η)) * R) + α * F + b * (1 + M) := by
        have hh := mul_le_mul_of_nonneg_right hα1 hF0
        linarith only [hh]
      _ = α * typicalSlopeNormalizedEnvelope η α := by
        dsimp only [typicalSlopeNormalizedEnvelope, R, F, b, M]
        field_simp [hα0.ne']
  · exact add_le_add (add_le_add hopposite hoppositeMid) hfarC

/-- The actual error expressions are uniformly small throughout the inverse-slope heat interval. -/
theorem eventually_typicalHalfGaussErrors_small {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ α : ℝ in atTop, ∀ T τ : ℝ, 8 ≤ T →
      1 + Real.log (4 * T) ≤ 8 * α → 0 < τ → τ ≤ 1 / 8 →
      16 * η ≤ 2 * τ * α → 2 * τ * α ≤ 2 →
      typicalHalfGaussError η T τ α ≤ 1 / 5 ∧
      typicalHalfGaussSlopeError η T τ α < 18 / 25 * α ∧
      typicalHalfGaussOppositeError η T τ α ≤ 1 / 2 := by
  have hb := eventually_affineLog_le_linear (96 / η ^ 2)
    ((96 * Real.log 8 + 216) / η ^ 2 + 4) (by norm_num : (0 : ℝ) < 2 / 9)
  have hC := eventually_typicalTailLogEnvelope_le (η := η) (show 0 < η ^ 2 by positivity)
  have hM := (tendsto_typicalMainEnvelope hη).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 5))
  have hS := (tendsto_typicalSlopeNormalizedEnvelope hη).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 18 / 25))
  have hO := (tendsto_typicalOppositeEnvelope hη).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hb, hC, hM, hS, hO, eventually_ge_atTop (8 : ℝ)]
    with α hb hC hM hS hO hα
  intro T τ hT hscale hτ hτ8 hc hc2
  have hb' : typicalSlopeEnvelope η α ≤ 2 / 9 * α := by
    unfold typicalSlopeEnvelope
    linarith only [hb]
  obtain ⟨he, hs, ho⟩ := typicalHalfGaussErrors_le_envelopes hη hη8 hT hα hscale
    hτ hτ8 hc hc2 hb' hC
  refine ⟨he.trans hM, ?_, ho.trans hO⟩
  calc
    _ ≤ α * typicalSlopeNormalizedEnvelope η α := hs
    _ < α * (18 / 25) := mul_lt_mul_of_pos_left hS (by linarith only [hα])
    _ = _ := by ring

#print axioms eventually_typicalHalfGaussErrors_small

end

end GaloisForLFunctions.ZeroConfigurationGeometry
