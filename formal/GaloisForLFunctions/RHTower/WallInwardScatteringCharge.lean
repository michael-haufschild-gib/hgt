import GaloisForLFunctions.RHTower.WallInwardThirdTail
import GaloisForLFunctions.RHTower.WallScatteringCharge

/-!
# `(46)` on the inward ray: the incoming derivative scattering charge

The mirror of `WallScatteringCharge`.  The expansion itself is sign-agnostic — it only ever sees
`|x|` and `|Y|` — so only the bookkeeping of the ray remainder changes: on the inward side the
moving interval is `[x,W]` rather than `[W,x]`, and the difference of ray remainders comes out with
the opposite sign.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The block average of the inward ray remainder. -/
def wallTailVectorNeg (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ W : ℝ) : X :=
  ∫ L in Icc m (m + 1), wallTailOperatorNeg E T σ L W (g L)

theorem integrableOn_wallTailOperatorNeg_apply {σ W μ₀ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) (hW : W ≤ -1)
    (hgap : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic W, μ₀ ≤ wallFloor T σ t + L) :
    IntegrableOn (fun L : ℝ => wallTailOperatorNeg E T σ L W (g L)) (Icc m (m + 1)) := by
  have h := integrableOn_phase_apply_of_continuousOn
    (A := fun L : ℝ => wallTailOperatorNeg E T σ L W) (S := Icc m (m + 1)) measurableSet_Icc
    (continuousOn_wallTailOperatorNeg_position hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hW hgap)
    (fun L hL => norm_wallTailOperatorNeg_le hσ0 hσ1 hμ hb₂ hK₂ hW (hgap L hL)) hg
    (φ := fun _ => (1 : ℂ)) continuous_const (fun _ => by simp)
  simpa using h

/-- **The moving inward block remainder is the difference of two fixed ray remainders.** -/
theorem wallRemainderVector_eq_sub_neg {σ W x μ₀ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) (hW : W ≤ -1) (hxW : x ≤ W)
    (hgap : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic W, μ₀ ≤ wallFloor T σ t + L) :
    wallRemainderVector E T g m σ W x
      = wallTailVectorNeg E T g m σ x - wallTailVectorNeg E T g m σ W := by
  have hx : x ≤ -1 := le_trans hxW hW
  have hgapx : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic x, μ₀ ≤ wallFloor T σ t + L := by
    intro L hL t ht
    exact hgap L hL t (le_trans ht hxW)
  have hIW := integrableOn_wallTailOperatorNeg_apply hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hW hgap
  have hIx := integrableOn_wallTailOperatorNeg_apply hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hx hgapx
  have hpt : ∀ L ∈ Icc m (m + 1),
      (∫ t in W..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
          (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t) (g L)
        = wallTailOperatorNeg E T σ L x (g L) - wallTailOperatorNeg E T σ L W (g L) := by
    intro L hL
    rw [wallIntervalNeg_eq_tail_sub hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hW hxW
      (fun t ht => hgap L hL t ht)]
    rfl
  rw [wallRemainderVector, setIntegral_congr_fun measurableSet_Icc hpt,
    integral_sub hIx hIW, wallTailVectorNeg, wallTailVectorNeg]

/-- **`(46)` on the inward ray: the incoming Gamma derivative scattering charge.** -/
def wallScatteringChargeNeg (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (c : X) (m σ W : ℝ) : X :=
  thresholdDatum E T (blockSource g m) c σ W
    + (-(Complex.I) / 2 : ℂ) • (-(thresholdVector E T g m σ W)
        + (Complex.I : ℂ) • thirdThresholdVector E T g m σ W
        - (Complex.I : ℂ) • wallTailVectorNeg E T g m σ W)

/-- Everything in the inward profile that still depends on the evaluation point. -/
def wallScatteringRemainderNeg (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  (-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • firstBoundaryBlock T g m σ x
      + secondBoundary T g m σ x
      - (Complex.I : ℂ) • thirdBoundary T g m σ x
      + (Complex.I : ℂ) • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallTailVectorNeg E T g m σ x))

variable [Nontrivial X]

set_option maxHeartbeats 1000000 in
/-- **The forced profile is the propagated inward charge plus point-dependent terms.** -/
theorem forcedProfile_eq_chargeNeg_add_remainderNeg {σ W x μ₀ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) (c : X) (hW : W ≤ -1) (hxW : x ≤ W)
    (hgapx : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapW : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ W + L)
    (hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc W x, 0 < wallFloor T σ t + L)
    (hgapR : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic W, μ₀ ≤ wallFloor T σ t + L) :
    forcedProfile E T (blockSource g m) c σ x
      = stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallScatteringChargeNeg E T g c m σ W)
        + wallScatteringRemainderNeg E T g m σ x := by
  have hx : x ≤ -1 := le_trans hxW hW
  have hx1 : (1 : ℝ) ≤ |x| := by
    rw [abs_of_neg (by linarith : x < 0)]
    linarith
  have hW1 : (1 : ℝ) ≤ |W| := by
    rw [abs_of_neg (by linarith : W < 0)]
    linarith
  rw [forcedProfile_split (E := E) (T := T) (blockSource g m) c
      (intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg 0 W)
      (intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg W x),
    stripPropagator_movingTail_decomposition_abs hEdiff hE hEne hT hσ0 hσ1 hg hx1 hW1 hμ
      hgapx hgapW hgapI,
    tailRemainder_third_decomposition hEdiff hE hEne hT hσ0 hσ1 hg hx1 hW1 hμ hgapx hgapW hgapI,
    wallRemainderVector_eq_sub_neg hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hW hxW hgapR,
    wallScatteringChargeNeg, wallScatteringRemainderNeg, thresholdDatum]
  simp only [map_add, map_smul, map_sub, map_neg]
  module

end GaloisForLFunctions.RHTower
