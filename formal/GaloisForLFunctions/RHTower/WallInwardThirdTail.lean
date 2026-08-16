import GaloisForLFunctions.RHTower.WallTailOperatorRegularity
import GaloisForLFunctions.HTGeometry.PowerTailBochnerBoundInward

/-!
# The three-fold remainder on the inward ray

The mirror of `WallTailOperatorRegularity` and of `(48)`.  Every ingredient is even: the amplitude
bound `‖∂D₂(t)‖ ≤ C(1+|t|)^{-3}` and the two propagator bounds are stated in `|t|`, so the inward
statements are the outward ones with the endpoint reflected.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [CompleteSpace X] [InnerProductSpace ℂ X] in
/-- An initial ray splits at any interior point. -/
theorem integral_Iic_eq_intervalIntegral_add_tail {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {f : ℝ → Y} {a b : ℝ} (hab : a ≤ b) (hint : IntegrableOn f (Iic b)) :
    (∫ t in Iic b, f t) = (∫ t in a..b, f t) + ∫ t in Iic a, f t := by
  have hunion : Iic b = Iic a ∪ Ioc a b := (Iic_union_Ioc_eq_Iic hab).symm
  have hdisj : Disjoint (Iic a) (Ioc a b) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht'.1 (not_lt.mpr ht)
  have h1 : IntegrableOn f (Iic a) := hint.mono_set (by rw [hunion]; exact subset_union_left)
  have h2 : IntegrableOn f (Ioc a b) := hint.mono_set (by rw [hunion]; exact subset_union_right)
  rw [hunion, setIntegral_union hdisj measurableSet_Ioc h1 h2,
    intervalIntegral.integral_of_le hab]
  exact add_comm _ _

theorem abs_ge_one_of_mem_Iic {x t : ℝ} (hx : x ≤ -1) (ht : t ∈ Iic x) : (1 : ℝ) ≤ |t| := by
  have htx : t ≤ x := ht
  have : t ≤ -1 := le_trans htx hx
  rw [abs_of_neg (by linarith)]
  linarith

/-- The three-fold remainder integrand is integrable on an initial ray below the threshold. -/
theorem integrableOn_wallThirdIntegrandNeg {σ L μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {x : ℝ} (hx : x ≤ -1) (hfloor : ∀ t ∈ Iic x, μ₀ ≤ wallFloor T σ t + L) :
    IntegrableOn (fun t : ℝ => wallPhaseMap E T σ L t * invFamilyProduct2Deriv
      (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
      (wallGeneratorD3 X σ) t) (Iic x) := by
  have hcont := continuousOn_wallThirdIntegrand (T := T) hEdiff hE hEne hσ0 hσ1
    (S := Iic x) (fun t ht => lt_of_lt_of_le hμ (hfloor t ht))
  refine integrableOn_of_powerTail_bound_Iic (q := 3 - (1 / 2 + σ))
    (C := K₂ * wallAmplitude3Const μ₀) (by linarith) (by linarith)
    (hcont.aestronglyMeasurable measurableSet_Iic) (fun t ht => ?_)
  exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ (abs_ge_one_of_mem_Iic hx ht)
    (hfloor t ht)

/-- The three-fold remainder accumulated on the initial ray below the threshold. -/
def wallTailOperatorNeg (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ L W : ℝ) : X →L[ℂ] X :=
  ∫ t in Iic W, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
    (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t

/-- **The inward ray remainder is continuous in the frequency.** -/
theorem continuousOn_wallTailOperatorNeg_position {σ W μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {S : Set ℝ} (hW : W ≤ -1)
    (hgap : ∀ L ∈ S, ∀ t ∈ Iic W, μ₀ ≤ wallFloor T σ t + L) :
    ContinuousOn (fun L : ℝ => wallTailOperatorNeg E T σ L W) S := by
  have hq : (1 : ℝ) < 3 - (1 / 2 + σ) := by linarith
  have hbase : IntegrableOn (fun ξ : ℝ => |ξ| ^ (-(3 - (1 / 2 + σ)))) (Iic W) volume := by
    have h := integrableOn_powerTail_Iic (t := -W) (p := 3 - (1 / 2 + σ)) (by linarith) hq
    rwa [neg_neg] at h
  refine continuousOn_of_dominated
    (bound := fun t : ℝ => (K₂ * wallAmplitude3Const μ₀) * |t| ^ (-(3 - (1 / 2 + σ)))) ?_ ?_ ?_ ?_
  · intro L hL
    exact (continuousOn_wallThirdIntegrand (T := T) hEdiff hE hEne hσ0 hσ1
      (S := Iic W) (fun t ht => lt_of_lt_of_le hμ (hgap L hL t ht))).aestronglyMeasurable
      measurableSet_Iic
  · intro L hL
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ (abs_ge_one_of_mem_Iic hW ht)
      (hgap L hL t ht)
  · exact hbase.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have hWc : ContinuousOn (fun L : ℝ => wallPhaseMap E T σ L t) S :=
      (continuousOn_wallPhaseMap_position E T σ t).continuousOn
    have hA : ContinuousOn (fun L : ℝ => invFamilyProduct2Deriv (wallGeneratorShift T σ L)
        (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t) S :=
      continuousOn_invFamilyProduct2Deriv_position (T := T) hσ0 hσ1
        (fun L hL => lt_of_lt_of_le hμ (hgap L hL t ht))
    exact hWc.mul hA

/-- **The inward ray remainder is uniformly bounded below the threshold.** -/
theorem norm_wallTailOperatorNeg_le {σ L W μ₀ K₂ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂) (hW : W ≤ -1)
    (hgap : ∀ t ∈ Iic W, μ₀ ≤ wallFloor T σ t + L) :
    ‖wallTailOperatorNeg E T σ L W‖
      ≤ (K₂ * wallAmplitude3Const μ₀)
        * ((-W) ^ (1 - (3 - (1 / 2 + σ))) / ((3 - (1 / 2 + σ)) - 1)) := by
  refine norm_integral_Iic_le_powerTail (q := 3 - (1 / 2 + σ))
    (C := K₂ * wallAmplitude3Const μ₀) (by linarith) (by linarith) (fun t ht => ?_)
  exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ (abs_ge_one_of_mem_Iic hW ht) (hgap t ht)

/-- **`(48)` on the inward ray: the transported three-fold remainder is `O(|x|^{-2})`.** -/
theorem norm_wallThirdTailNeg_transported_le {σ L μ₀ K₁ K₂ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {x : ℝ} (hx : x ≤ -1) (hfloor : ∀ t ∈ Iic x, μ₀ ≤ wallFloor T σ t + L) :
    ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) * wallTailOperatorNeg E T σ L x‖
      ≤ (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * (-x) ^ (-(2 : ℝ)) := by
  have hx0 : (0 : ℝ) < -x := by linarith
  have hxabs : |x| = -x := abs_of_neg (by linarith)
  have hC3 : 0 ≤ wallAmplitude3Const μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitude3Const]
    positivity
  have hH : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (-x) ^ (-(1 / 2 + σ)) := by
    have hb := hb₁ x
    rw [hxabs] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hK₁)
    exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have hM := norm_wallTailOperatorNeg_le (E := E) hσ0 hσ1 hμ hb₂ hK₂ hx hfloor
  have hMnn : (0 : ℝ) ≤ (K₂ * wallAmplitude3Const μ₀)
      * ((-x) ^ (1 - (3 - (1 / 2 + σ))) / ((3 - (1 / 2 + σ)) - 1)) := by
    have hd : (0 : ℝ) < (3 - (1 / 2 + σ)) - 1 := by linarith
    have hp : (0 : ℝ) < (-x) ^ (1 - (3 - (1 / 2 + σ))) := Real.rpow_pos_of_pos hx0 _
    positivity
  refine le_trans (norm_mul_le _ _) ?_
  refine le_trans (mul_le_mul hH hM (norm_nonneg _) (by positivity)) (le_of_eq ?_)
  have hexp : (-x) ^ (-(1 / 2 + σ)) * (-x) ^ (1 - (3 - (1 / 2 + σ))) = (-x) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hden : (3 - (1 / 2 + σ)) - 1 = 2 - (1 / 2 + σ) := by ring
  rw [hden]
  calc K₁ * (-x) ^ (-(1 / 2 + σ))
        * ((K₂ * wallAmplitude3Const μ₀)
          * ((-x) ^ (1 - (3 - (1 / 2 + σ))) / (2 - (1 / 2 + σ))))
      = (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
        * ((-x) ^ (-(1 / 2 + σ)) * (-x) ^ (1 - (3 - (1 / 2 + σ)))) := by ring
    _ = (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * (-x) ^ (-(2 : ℝ)) := by
        rw [hexp]

/-- **The moving inward remainder is the difference of two fixed ray remainders.** -/
theorem wallIntervalNeg_eq_tail_sub {σ L W x μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂) (hW : W ≤ -1) (hxW : x ≤ W)
    (hgap : ∀ t ∈ Iic W, μ₀ ≤ wallFloor T σ t + L) :
    (∫ t in W..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
        (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t)
      = wallTailOperatorNeg E T σ L x - wallTailOperatorNeg E T σ L W := by
  have hint := integrableOn_wallThirdIntegrandNeg (T := T) hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hW hgap
  have hsplit := integral_Iic_eq_intervalIntegral_add_tail hxW hint
  rw [wallTailOperatorNeg, wallTailOperatorNeg, hsplit, intervalIntegral.integral_symm x W]
  abel

end GaloisForLFunctions.RHTower
