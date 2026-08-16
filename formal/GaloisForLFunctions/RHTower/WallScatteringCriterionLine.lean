import GaloisForLFunctions.RHTower.WallInwardScatteringCriterion

/-!
# `(47)` on the whole line

The two rays carry the two charges; the compact middle carries nothing.  A continuous profile has
finite squared mass on any bounded interval, so the line statement is exactly the conjunction of the
two ray statements.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
/-- A continuous profile has finite squared mass on a bounded interval. -/
theorem lintegral_sq_enorm_Icc_ne_top {f : ℝ → X} (hf : Continuous f) (a b : ℝ) :
    (∫⁻ x in Icc a b, ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hf.continuousOn
  have hbd : ∀ x ∈ Icc a b, ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (max C 0 ^ 2) := by
    intro x hx
    have h1 : ‖f x‖ ≤ max C 0 := le_trans (hC x hx) (le_max_left _ _)
    have h2 : ‖f x‖ₑ ≤ ENNReal.ofReal (max C 0) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal h1
    calc ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (max C 0) ^ 2 := pow_le_pow_left' h2 2
      _ = ENNReal.ofReal (max C 0 ^ 2) := (ENNReal.ofReal_pow (le_max_right _ _) 2).symm
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Icc hbd)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Real.volume_Icc])

variable [Nontrivial X]

set_option maxHeartbeats 1000000 in
/-- **`(47)`: the Gamma derivative scattering criterion on the whole line.**  The frequency-weighted
profile is square integrable exactly when both outgoing charges vanish. -/
theorem lintegral_sq_freq_forcedProfile_line_ne_top_iff {σ Y μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 < K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (c : X) (hY : 1 ≤ Y) (hfloor : ∀ x : ℝ, Y ≤ |x| → μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x : ℝ, ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2) ≠ ⊤
      ↔ wallScatteringCharge E T g c m σ Y = 0
        ∧ wallScatteringChargeNeg E T g c m σ (-Y) = 0 := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hfloorPos : ∀ x ∈ Ici Y, μ₀ - m ≤ wallFloor T σ x := by
    intro x hx
    refine hfloor x ?_
    have hxY : Y ≤ x := hx
    rw [abs_of_pos (lt_of_lt_of_le hY0 hxY)]
    exact hxY
  have hfloorNeg : ∀ x ∈ Iic (-Y), μ₀ - m ≤ wallFloor T σ x := by
    intro x hx
    refine hfloor x ?_
    have hxY : x ≤ -Y := hx
    rw [abs_of_neg (by linarith : x < 0)]
    linarith
  have hpos := lintegral_sq_freq_forcedProfile_ray_ne_top_iff hEdiff hE hEne hT hσ0 hσ1 hμ
    hb₁ hK₁ hb₂ hK₂ hgd hg2 hgm hg'2 hsupp hg hg' c hY hfloorPos
  have hneg := lintegral_sq_freq_forcedProfile_negRay_ne_top_iff hEdiff hE hEne hT hσ0 hσ1 hμ
    hb₁ hK₁ hb₂ hK₂ hgd hg2 hgm hg'2 hsupp hg hg' c hY hfloorNeg
  have hcont : Continuous fun x : ℝ => x • forcedProfile E T (blockSource g m) c σ x :=
    continuous_id.smul (continuous_forcedProfile_blockSource hEdiff hE hEne hσ0 hσ1 hg c)
  have hmid := lintegral_sq_enorm_Icc_ne_top hcont (-Y) Y
  have hcover : (Iio (-Y) ∪ (Icc (-Y) Y ∪ Ioi Y)) = (univ : Set ℝ) := by
    rw [Icc_union_Ioi_eq_Ici (by linarith : (-Y : ℝ) ≤ Y), Iio_union_Ici]
  constructor
  · intro htot
    refine ⟨hpos.mp ?_, hneg.mp ?_⟩
    · exact ne_top_of_le_ne_top htot (setLIntegral_le_lintegral _ _)
    · exact ne_top_of_le_ne_top htot (setLIntegral_le_lintegral _ _)
  · rintro ⟨hp, hn⟩
    have h1 := hpos.mpr hp
    have h2 := hneg.mpr hn
    have hle : (∫⁻ x : ℝ, ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
        ≤ (∫⁻ x in Iio (-Y), ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
          + ((∫⁻ x in Icc (-Y) Y, ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
            + ∫⁻ x in Ioi Y, ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2) := by
      rw [← setLIntegral_univ, ← hcover]
      exact le_trans (lintegral_union_le _ _ _)
        (add_le_add le_rfl (lintegral_union_le _ _ _))
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨h2, ENNReal.add_ne_top.mpr ⟨hmid, h1⟩⟩) hle

end GaloisForLFunctions.RHTower
