import GaloisForLFunctions.RHTower.WallThirdBlockDecomposition
import GaloisForLFunctions.RHTower.WallFinitePart
import GaloisForLFunctions.HTGeometry.InverseFamilyContinuityFromResolvent

/-!
# The three-fold remainder on a terminal ray, as a function of the frequency

The charge `(46)` is a block average of the three-fold remainder over a terminal ray.  For that
average to exist, the ray integral must depend measurably on the frequency.  It does more: it
depends *continuously* on it, because the integrand is dominated on the ray by a frequency-free
power tail and is continuous in the frequency for each position.  The resolvent supplies that
continuity, and the amplitudes inherit it because they are polynomial in the resolvent.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **The three-fold amplitude is continuous in the frequency.**  It is a polynomial expression in
the block resolvent and the fixed symbol jets, so it inherits the resolvent's continuity. -/
theorem continuousOn_invFamilyProduct2Deriv_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x : ℝ} {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ => invFamilyProduct2Deriv (wallGeneratorShift T σ L)
      (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) x) S := by
  have hD : ContinuousOn (invFamily (fun L : ℝ => wallGeneratorShift T σ L x)) S :=
    continuousOn_invFamily_position (T := T) hσ0 hσ1 hgap
  have h := continuousOn_invFamilyProduct2Deriv_of_resolvent
    (C := fun L : ℝ => wallGeneratorShift T σ L x)
    (C₁ := fun _ : ℝ => wallGeneratorD1 X σ x) (C₂ := fun _ : ℝ => wallGeneratorD2 X σ x)
    (C₃ := fun _ : ℝ => wallGeneratorD3 X σ x) (S := S) hD continuousOn_const continuousOn_const
    continuousOn_const
  exact h

/-- The three-fold remainder accumulated on the terminal ray past the threshold. -/
def wallTailOperator (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ L Y : ℝ) : X →L[ℂ] X :=
  ∫ t in Ioi Y, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
    (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t

/-- **The ray remainder is continuous in the frequency.**  The power tail dominating the integrand
does not depend on the frequency, so continuity passes under the integral. -/
theorem continuousOn_wallTailOperator_position {σ Y μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {S : Set ℝ} (hY : 1 ≤ Y)
    (hgap : ∀ L ∈ S, ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L) :
    ContinuousOn (fun L : ℝ => wallTailOperator E T σ L Y) S := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hq : (1 : ℝ) < 3 - (1 / 2 + σ) := by linarith
  have habs : ∀ t ∈ Ioi Y, (1 : ℝ) ≤ |t| := by
    intro t ht
    have hty : Y < t := ht
    rw [abs_of_pos (lt_trans hY0 hty)]
    linarith
  refine continuousOn_of_dominated
    (bound := fun t : ℝ => (K₂ * wallAmplitude3Const μ₀) * |t| ^ (-(3 - (1 / 2 + σ)))) ?_ ?_ ?_ ?_
  · intro L hL
    exact (continuousOn_wallThirdIntegrand (T := T) hEdiff hE hEne hσ0 hσ1
      (S := Ioi Y) (fun t ht => lt_of_lt_of_le hμ (hgap L hL t ht))).aestronglyMeasurable
      measurableSet_Ioi
  · intro L hL
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ (habs t ht) (hgap L hL t ht)
  · exact (integrableOn_powerTail_Ioi hY0 hq).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hW : ContinuousOn (fun L : ℝ => wallPhaseMap E T σ L t) S :=
      (continuousOn_wallPhaseMap_position E T σ t).continuousOn
    have hA : ContinuousOn (fun L : ℝ => invFamilyProduct2Deriv (wallGeneratorShift T σ L)
        (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t) S :=
      continuousOn_invFamilyProduct2Deriv_position (T := T) hσ0 hσ1
        (fun L hL => lt_of_lt_of_le hμ (hgap L hL t ht))
    exact hW.mul hA

/-- **The ray remainder is uniformly bounded past the threshold.** -/
theorem norm_wallTailOperator_le {σ L Y μ₀ K₂ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂) (hY : 1 ≤ Y)
    (hgap : ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L) :
    ‖wallTailOperator E T σ L Y‖
      ≤ (K₂ * wallAmplitude3Const μ₀)
        * (Y ^ (1 - (3 - (1 / 2 + σ))) / ((3 - (1 / 2 + σ)) - 1)) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hq : (1 : ℝ) < 3 - (1 / 2 + σ) := by linarith
  refine norm_integral_Ioi_le_powerTail hq hY0 (fun t ht => ?_)
  have hty : Y < t := ht
  have habs : (1 : ℝ) ≤ |t| := by
    rw [abs_of_pos (lt_trans hY0 hty)]
    linarith
  exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ habs (hgap t ht)

/-- **The moving remainder is the difference of two ray remainders.** -/
theorem wallInterval_eq_tail_sub {σ L Y x μ₀ K₂ : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂) (hY : 1 ≤ Y) (hYx : Y ≤ x)
    (hgap : ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L) :
    (∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
        (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t)
      = wallTailOperator E T σ L Y - wallTailOperator E T σ L x := by
  have hint := integrableOn_wallThirdIntegrand (T := T) hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hY hgap
  have hsplit := integral_Ioi_eq_intervalIntegral_add_tail hYx hint
  rw [wallTailOperator, wallTailOperator, hsplit]
  abel

end GaloisForLFunctions.RHTower
