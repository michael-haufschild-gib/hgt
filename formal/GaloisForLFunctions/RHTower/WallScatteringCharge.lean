import GaloisForLFunctions.RHTower.WallVectorDerivativeWall
import GaloisForLFunctions.RHTower.WallForcedProfileRay

/-!
# `(46)`: the Gamma derivative scattering charge on a ray

Three integrations by parts split the transported source into terms that depend on the evaluation
point and terms that do not.  The point-dependent terms are the three boundary amplitudes at the
moving endpoint and the absolutely convergent tail past it; everything else is a fixed vector, and
that vector — the datum accumulated below the threshold, corrected by the three endpoint terms and
the ray remainder at the threshold — is the outgoing charge.

Writing the profile as `H(x)d_+ + (point-dependent terms)` is what makes the criterion `(47)`
a statement about `d_+` alone.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The block average of the ray remainder. -/
def wallTailVector (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ Y : ℝ) : X :=
  ∫ L in Icc m (m + 1), wallTailOperator E T σ L Y (g L)

theorem integrableOn_wallTailOperator_apply {σ Y μ₀ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) (hY : 1 ≤ Y)
    (hgap : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L) :
    IntegrableOn (fun L : ℝ => wallTailOperator E T σ L Y (g L)) (Icc m (m + 1)) := by
  have h := integrableOn_phase_apply_of_continuousOn
    (A := fun L : ℝ => wallTailOperator E T σ L Y) (S := Icc m (m + 1)) measurableSet_Icc
    (continuousOn_wallTailOperator_position hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hY hgap)
    (fun L hL => norm_wallTailOperator_le hσ0 hσ1 hμ hb₂ hK₂ hY (hgap L hL)) hg
    (φ := fun _ => (1 : ℂ)) continuous_const (fun _ => by simp)
  simpa using h

/-- **The moving block remainder is the difference of two fixed ray remainders.** -/
theorem wallRemainderVector_eq_sub {σ Y x μ₀ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) (hY : 1 ≤ Y) (hYx : Y ≤ x)
    (hgap : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L) :
    wallRemainderVector E T g m σ Y x
      = wallTailVector E T g m σ Y - wallTailVector E T g m σ x := by
  have hx : 1 ≤ x := le_trans hY hYx
  have hgapx : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L := by
    intro L hL t ht
    exact hgap L hL t (lt_of_le_of_lt hYx ht)
  have hIY := integrableOn_wallTailOperator_apply hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hY hgap
  have hIx := integrableOn_wallTailOperator_apply hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hx hgapx
  have hpt : ∀ L ∈ Icc m (m + 1),
      (∫ t in Y..x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
          (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t) (g L)
        = wallTailOperator E T σ L Y (g L) - wallTailOperator E T σ L x (g L) := by
    intro L hL
    rw [wallInterval_eq_tail_sub hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hY hYx
      (fun t ht => hgap L hL t ht)]
    rfl
  rw [wallRemainderVector, setIntegral_congr_fun measurableSet_Icc hpt,
    integral_sub hIY hIx, wallTailVector, wallTailVector]

/-! ## The charge and the point-dependent remainder -/

/-- **`(46)`: the outgoing Gamma derivative scattering charge on the positive ray.**  It is the datum
accumulated below the threshold, corrected by the three endpoint terms the expansion deposits there
and by the absolutely convergent remainder past it. -/
def wallScatteringCharge (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (c : X) (m σ Y : ℝ) : X :=
  thresholdDatum E T (blockSource g m) c σ Y
    + (-(Complex.I) / 2 : ℂ) • (-(thresholdVector E T g m σ Y)
        + (Complex.I : ℂ) • thirdThresholdVector E T g m σ Y
        + (Complex.I : ℂ) • wallTailVector E T g m σ Y)

/-- Everything in the profile that still depends on the evaluation point. -/
def wallScatteringRemainder (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  (-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • firstBoundaryBlock T g m σ x
      + secondBoundary T g m σ x
      - (Complex.I : ℂ) • thirdBoundary T g m σ x
      - (Complex.I : ℂ) • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallTailVector E T g m σ x))

variable [Nontrivial X]

/-- **The forced profile is the propagated charge plus point-dependent terms.** -/
theorem forcedProfile_eq_charge_add_remainder {σ Y x μ₀ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) (c : X) (hY : 1 ≤ Y) (hYx : Y ≤ x)
    (hgapx : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapY : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ Y + L)
    (hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc Y x, 0 < wallFloor T σ t + L)
    (hgapR : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L) :
    forcedProfile E T (blockSource g m) c σ x
      = stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallScatteringCharge E T g c m σ Y)
        + wallScatteringRemainder E T g m σ x := by
  have hx1 : (1 : ℝ) ≤ |x| := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
    linarith
  have hY1 : (1 : ℝ) ≤ |Y| := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y)]
    exact hY
  rw [forcedProfile_split (E := E) (T := T) (blockSource g m) c
      (intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg 0 Y)
      (intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg Y x),
    stripPropagator_movingTail_decomposition hEdiff hE hEne hT hσ0 hσ1 hg hYx hY hμ
      hgapx hgapY hgapI,
    tailRemainder_third_decomposition hEdiff hE hEne hT hσ0 hσ1 hg hx1 hY1 hμ hgapx hgapY hgapI,
    wallRemainderVector_eq_sub hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hY hYx hgapR,
    wallScatteringCharge, wallScatteringRemainder, thresholdDatum]
  simp only [map_add, map_smul, map_sub, map_neg]
  module

end GaloisForLFunctions.RHTower
