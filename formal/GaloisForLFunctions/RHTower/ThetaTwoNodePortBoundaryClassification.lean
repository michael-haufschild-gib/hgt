import GaloisForLFunctions.RHTower.ThetaTwoNodePortTransversality
import GaloisForLFunctions.RHTower.ThetaTailTwoPointPositivity

/-! Exact source-port boundary classification. The coefficients here are arbitrary;
the positive-anchor counterexample does not claim to satisfy Schur projection. -/

noncomputable section

namespace RHTower.ThetaPortBoundary

def sourcePort (x₁ x₂ y c₁ c₂ : ℝ) : ℝ :=
  thetaCuspFullSource y - c₁*thetaCuspFullSource x₁ - c₂*thetaCuspFullSource x₂

def coordinatePort (x₁ x₂ y c₁ c₂ : ℝ) : ℝ :=
  y*thetaCuspFullSource y - c₁*x₁*thetaCuspFullSource x₁ - c₂*x₂*thetaCuspFullSource x₂

def freeSource (x₁ x₂ y c₁ c₂ : ℝ) : ℝ :=
  deriv thetaCuspFullSource y - c₁*deriv thetaCuspFullSource x₁ - c₂*deriv thetaCuspFullSource x₂

def freeCoordinate (x₁ x₂ y c₁ c₂ : ℝ) : ℝ :=
  y*deriv thetaCuspFullSource y - c₁*x₁*deriv thetaCuspFullSource x₁ -
    c₂*x₂*deriv thetaCuspFullSource x₂

def slopeSecant (x₁ x₂ : ℝ) : ℝ :=
  (thetaCuspLogDecaySlope x₂-thetaCuspLogDecaySlope x₁)/(x₂-x₁)

def slopeIntercept (x₁ x₂ : ℝ) : ℝ :=
  (x₁*thetaCuspLogDecaySlope x₂-x₂*thetaCuspLogDecaySlope x₁)/(x₂-x₁)

def slopeReserve (x₁ x₂ y : ℝ) : ℝ :=
  thetaCuspLogDecaySlope y - ((x₂-y)/(x₂-x₁))*thetaCuspLogDecaySlope x₁ -
    ((y-x₁)/(x₂-x₁))*thetaCuspLogDecaySlope x₂

def coordinateReserve (x₁ x₂ y : ℝ) : ℝ :=
  ThetaPort.weightedSlope y - ((x₂-y)/(x₂-x₁))*ThetaPort.weightedSlope x₁ -
    ((y-x₁)/(x₂-x₁))*ThetaPort.weightedSlope x₂

private theorem source_deriv_eq (z : ℝ) :
    deriv thetaCuspFullSource z = -thetaCuspLogDecaySlope z * thetaCuspFullSource z := by
  have h : iteratedDeriv 1 thetaCuspLogSource z =
      deriv thetaCuspFullSource z / thetaCuspFullSource z := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource z).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all z).ne']

theorem slopeSecant_pos {x₁ x₂ : ℝ} (h12 : x₁ < x₂) : 0 < slopeSecant x₁ x₂ := by
  have hp : thetaCuspLogDecaySlope x₁ < thetaCuspLogDecaySlope x₂ := by
    simp only [thetaCuspLogDecaySlope, iteratedDeriv_one]
    exact neg_lt_neg (strictAnti_deriv_thetaCuspLogSource h12)
  exact div_pos (sub_pos.mpr hp) (sub_pos.mpr h12)

theorem slopeIntercept_pos {x₁ x₂ : ℝ} (hx : 0 < x₁) (h12 : x₁ < x₂) :
    0 < slopeIntercept x₁ x₂ := by
  have hp := ThetaTailTwoPoint.strictMonoOn_decaySlope_div hx (hx.trans h12) h12
  have h := (div_lt_div_iff₀ hx (hx.trans h12)).mp hp
  apply div_pos _ (sub_pos.mpr h12)
  nlinarith only [h]

theorem reserves_pos {x₁ x₂ y : ℝ} (hx : 0 ≤ x₁) (h12 : x₁ < x₂) (h2y : x₂ < y) :
    0 < slopeReserve x₁ x₂ y ∧ 0 < coordinateReserve x₁ x₂ y := by
  obtain ⟨h₁,h₂⟩ := ThetaPort.two_node_extrapolation_defects_neg hx h12 h2y
  constructor <;> dsimp [slopeReserve, coordinateReserve] <;> linarith

/-- Exact affine source law; no projection equation is assumed. -/
theorem freeSource_eq {x₁ x₂ : ℝ} (h12 : x₁ < x₂) (y c₁ c₂ : ℝ) :
    freeSource x₁ x₂ y c₁ c₂ =
      slopeIntercept x₁ x₂ * sourcePort x₁ x₂ y c₁ c₂ -
        slopeSecant x₁ x₂ * coordinatePort x₁ x₂ y c₁ c₂ -
        thetaCuspFullSource y * slopeReserve x₁ x₂ y := by
  simp only [freeSource, source_deriv_eq, slopeIntercept, sourcePort,
    slopeSecant, coordinatePort, slopeReserve]
  field_simp [sub_ne_zero.mpr h12.ne']
  ring

/-- Exact affine coordinate-source law; its coefficient of the source port is positive
when both earlier nodes are positive. -/
theorem freeCoordinate_eq {x₁ x₂ : ℝ} (h12 : x₁ < x₂) (y c₁ c₂ : ℝ) :
    freeCoordinate x₁ x₂ y c₁ c₂ =
      x₁*x₂*slopeSecant x₁ x₂ * sourcePort x₁ x₂ y c₁ c₂ -
        ((ThetaPort.weightedSlope x₂-ThetaPort.weightedSlope x₁)/(x₂-x₁)) *
          coordinatePort x₁ x₂ y c₁ c₂ - thetaCuspFullSource y * coordinateReserve x₁ x₂ y := by
  simp only [freeCoordinate, source_deriv_eq, sourcePort, slopeSecant,
    coordinatePort, coordinateReserve, ThetaPort.weightedSlope]
  field_simp [sub_ne_zero.mpr h12.ne']
  ring

/-- The first free source derivative is negative on the whole nonnegative second-port axis. -/
theorem freeSource_neg_on_source_axis {x₁ x₂ y c₁ c₂ : ℝ}
    (hx : 0 ≤ x₁) (h12 : x₁ < x₂) (h2y : x₂ < y)
    (hA : sourcePort x₁ x₂ y c₁ c₂ = 0) (hB : 0 ≤ coordinatePort x₁ x₂ y c₁ c₂) :
    freeSource x₁ x₂ y c₁ c₂ < 0 := by
  rw [freeSource_eq h12, hA, mul_zero]
  have h₁ := mul_nonneg (slopeSecant_pos h12).le hB
  have h₂ := mul_pos (thetaCuspFullSource_pos_all y) (reserves_pos hx h12 h2y).1
  linarith

/-- At a center-anchored coordinate-port zero both free derivatives are negative,
with no restriction on the first port. -/
theorem center_free_derivatives_neg {x₂ y c₁ c₂ : ℝ}
    (hx : 0 < x₂) (hy : x₂ < y) (hB : coordinatePort 0 x₂ y c₁ c₂ = 0) :
    freeSource 0 x₂ y c₁ c₂ < 0 ∧ freeCoordinate 0 x₂ y c₁ c₂ < 0 := by
  have hp0 : thetaCuspLogDecaySlope 0 = 0 := by
    simp only [thetaCuspLogDecaySlope,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]
  have hj : slopeIntercept 0 x₂ = 0 := by simp [slopeIntercept, hp0]
  obtain ⟨hE,hF⟩ := reserves_pos (le_refl (0:ℝ)) hx hy
  rw [freeSource_eq hx, freeCoordinate_eq hx, hB, hj]
  constructor
  · nlinarith only [mul_pos (thetaCuspFullSource_pos_all y) hE]
  · nlinarith only [mul_pos (thetaCuspFullSource_pos_all y) hF]

private theorem realize_ports {x₁ x₂ : ℝ} (h12 : x₁ < x₂) (y T : ℝ) :
    ∃ c₁ c₂, sourcePort x₁ x₂ y c₁ c₂ = T ∧ coordinatePort x₁ x₂ y c₁ c₂ = 0 := by
  refine ⟨((x₂-y)*thetaCuspFullSource y-x₂*T)/((x₂-x₁)*thetaCuspFullSource x₁),
    ((y-x₁)*thetaCuspFullSource y+x₁*T)/((x₂-x₁)*thetaCuspFullSource x₂), ?_, ?_⟩ <;>
    simp only [sourcePort, coordinatePort] <;>
    field_simp [sub_ne_zero.mpr h12.ne', (thetaCuspFullSource_pos_all x₁).ne',
      (thetaCuspFullSource_pos_all x₂).ne'] <;> ring

/-- For every strictly positive ordered triple, the actual source admits a coordinate-port
zero with positive first port and both free derivatives positive. These coefficients are not
claimed to be kernel projection coefficients. -/
theorem exists_positive_anchor_reversed_free_derivatives {x₁ x₂ y : ℝ}
    (hx : 0 < x₁) (h12 : x₁ < x₂) (hy : x₂ < y) :
    ∃ c₁ c₂, 0 < sourcePort x₁ x₂ y c₁ c₂ ∧ coordinatePort x₁ x₂ y c₁ c₂ = 0 ∧
      0 < freeSource x₁ x₂ y c₁ c₂ ∧ 0 < freeCoordinate x₁ x₂ y c₁ c₂ := by
  let U := thetaCuspFullSource y * slopeReserve x₁ x₂ y
  let V := thetaCuspFullSource y * coordinateReserve x₁ x₂ y
  let j := slopeIntercept x₁ x₂
  let r := x₁*x₂*slopeSecant x₁ x₂
  have hj : 0 < j := slopeIntercept_pos hx h12
  have hr : 0 < r := mul_pos (mul_pos hx (hx.trans h12)) (slopeSecant_pos h12)
  have hU : 0 < U := mul_pos (thetaCuspFullSource_pos_all y) (reserves_pos hx.le h12 hy).1
  have hV : 0 < V := mul_pos (thetaCuspFullSource_pos_all y) (reserves_pos hx.le h12 hy).2
  let T := U/j + V/r + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hUT : U < j*T := by
    have ht : U/j < T := by dsimp [T]; linarith [div_pos hV hr]
    have h := (div_lt_iff₀ hj).mp ht
    nlinarith only [h]
  have hVT : V < r*T := by
    have ht : V/r < T := by dsimp [T]; linarith [div_pos hU hj]
    have h := (div_lt_iff₀ hr).mp ht
    nlinarith only [h]
  obtain ⟨c₁,c₂,hA,hB⟩ := realize_ports h12 y T
  refine ⟨c₁,c₂,by rwa [hA],hB,?_,?_⟩
  · rw [freeSource_eq h12, hA, hB]
    change 0 < j*T - _*0 - U
    linarith only [hUT]
  · rw [freeCoordinate_eq h12, hA, hB]
    change 0 < r*T - _*0 - V
    linarith only [hVT]

end RHTower.ThetaPortBoundary
