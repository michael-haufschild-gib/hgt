import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamAngularJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamRadialFields

/-! Actual stream metric fields and their full coordinate two-jets. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMScalarLinearEquation D4BMVectorStream
noncomputable section

/-- Actual temporal component of the radial stream reconstruction. -/
def streamTimeBlock (w a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  ((x 1 : ℂ)*(x 1 : ℂ)+(-1))*streamRadialDerivative w a square x

/-- Actual radial component of the same reconstruction. -/
def streamRadiusBlock (w a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  (w*streamRadialField w a square x)*((x 1 : ℂ)*(x 1 : ℂ)+(-1))⁻¹

/-- The full symmetric forced stream metric as an actual field. -/
def streamMetricField (w a : ℂ) (square : Bool) (V : Covector) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let T := streamTimeBlock w a square x
  let R := streamRadiusBlock w a square x
  let A := V 0 (angularPoint x)
  let C := V 1 (angularPoint x)
  !![0,0,T*A,T*C; 0,0,R*A,R*C; T*A,R*A,0,0; T*C,R*C,0,0]

/-- The entire metric-jet table, with every angular slot read from the actual field. -/
def streamActualMetricJet (w r B : ℂ) (square : Bool) (V : Covector) (z : Point) : CoordinateMetricTwoJet 4 ℂ :=
  D4BMVectorStream.metricJet w r (streamRadialValue w r B square)
    (streamRadialFirst w r B square) (streamRadialSecond w r B square) (streamRadialThird w r B square)
    (V 0 z) (V 1 z) (coordDeriv 0 (V 0) z) (coordDeriv 1 (V 0) z) (coordDeriv 0 (V 1) z)
    (coordDeriv 0 (coordDeriv 0 (V 0)) z) (coordDeriv 0 (coordDeriv 1 (V 0)) z)
    (coordDeriv 0 (coordDeriv 0 (V 1)) z) (coordDeriv 1 (coordDeriv 1 (V 0)) z)

private theorem radius_smooth (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt

private theorem factor_ne_zero (p : D4BMBackground.ExteriorPoint) :
    (p.val 1 : ℂ)*(p.val 1 : ℂ)+(-1) ≠ 0 := by
  have h : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  simpa only [← pow_two,← sub_eq_add_neg] using h

private theorem block_smooth (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (streamTimeBlock w a square) p.val ∧
      ContDiffAt ℝ 2 (streamRadiusBlock w a square) p.val := by
  have hR := radius_smooth p
  have hF : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)*(x 1 : ℂ)+(-1)) p.val :=
    (hR.mul hR).add contDiffAt_const
  exact ⟨hF.mul (streamRadialFields_smooth w a square p 2).2,
    (contDiffAt_const.mul (streamRadialFields_smooth w a square p 2).1).mul
      (hF.inv (factor_ne_zero p))⟩

private theorem block_jets (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    let r := (p.val 1 : ℂ)
    let B := D4BMFundamentalScalarMetric.envelope w a p.val
    let R := coord r 1
    let F := (R.mul R).add (constant (-1))
    ofField (streamTimeBlock w a square) p.val =
      F.mul (radialJet w (streamRadialFirst w r B square) (streamRadialSecond w r B square)
        (streamRadialThird w r B square)) ∧
    ofField (streamRadiusBlock w a square) p.val =
      ((constant w).mul (radialJet w (streamRadialValue w r B square) (streamRadialFirst w r B square)
        (streamRadialSecond w r B square))).mul F.inv := by
  have hR := radius_smooth p
  have hF : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)*(x 1 : ℂ)+(-1)) p.val :=
    (hR.mul hR).add contDiffAt_const
  have hjR : ofField (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val = coord (p.val 1) 1 :=
    D4BMFundamentalScalarMetric.coordinate_jet p.val 1
  have hjF : ofField (fun x : Fin 4 → ℝ => (x 1 : ℂ)*(x 1 : ℂ)+(-1)) p.val =
      ((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1)) := by
    rw [ofField_add (hR.mul hR) contDiffAt_const,ofField_mul hR hR,ofField_constant,hjR]
  constructor
  · unfold streamTimeBlock
    rw [ofField_mul hF (streamRadialFields_smooth w a square p 2).2,hjF,streamRadialDerivative_jet]
  · have hFi : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => ((x 1 : ℂ)*(x 1 : ℂ)+(-1))⁻¹) p.val :=
      hF.inv (factor_ne_zero p)
    unfold streamRadiusBlock
    rw [ofField_mul ((contDiffAt_const (c := w)).mul (streamRadialFields_smooth w a square p 2).1)
      hFi,ofField_mul (contDiffAt_const (c := w)) (streamRadialFields_smooth w a square p 2).1,
      ofField_constant,ofField_inv hF (factor_ne_zero p),hjF,streamRadialField_jet]

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) : CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,fun k l i j => (J i j).second k l⟩

/-- Every prescribed stream-metric value and ordered derivative is an actual coordinate derivative. -/
theorem streamMetricField_jet (w a : ℂ) (square : Bool) (V : Covector)
    (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → divergence V z = 0) :
    ofMetricField (streamMetricField w a square V) p.val =
      streamActualMetricJet w (p.val 1) (D4BMFundamentalScalarMetric.envelope w a p.val) square V
        (angularPoint p.val) := by
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (k : Fin 2) : ContDiffAt ℝ 2 (fun x => V k (angularPoint x)) p.val :=
    (hV k).comp p.val hu.contDiffAt
  have ht (k : Fin 2) := ofField_mul (block_smooth w a square p).1 (hLift k)
  have hr (k : Fin 2) := ofField_mul (block_smooth w a square p).2 (hLift k)
  simp_rw [(block_jets w a square p).1,streamAngularJet_actual V p hV hD] at ht
  simp_rw [(block_jets w a square p).2,streamAngularJet_actual V p hV hD] at hr
  change assemble _ = assemble _
  congr 1
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first | exact ofField_constant 0 p.val | exact ht 0 | exact ht 1 | exact hr 0 | exact hr 1

/-- The actual reconstructed stream field is twice continuously differentiable on the exterior. -/
theorem streamMetricField_smooth (w a : ℂ) (square : Bool) (V : Covector)
    (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val)) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => streamMetricField w a square V x i j) p.val := by
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (k : Fin 2) : ContDiffAt ℝ 2 (fun x => V k (angularPoint x)) p.val :=
    (hV k).comp p.val hu.contDiffAt
  fin_cases i <;> fin_cases j
  all_goals first | exact contDiffAt_const | exact (block_smooth w a square p).1.mul (hLift 0) |
    exact (block_smooth w a square p).1.mul (hLift 1) | exact (block_smooth w a square p).2.mul (hLift 0) |
    exact (block_smooth w a square p).2.mul (hLift 1)

end
end RHTower.D4BMModularCore
