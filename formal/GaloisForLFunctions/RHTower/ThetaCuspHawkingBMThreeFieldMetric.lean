import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThreeFieldTensor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMetricLinearCombination
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamHarmonicField

/-! The complete literal scalar--scalar reconstruction as an actual sourced metric field. -/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open GaloisForLFunctions.HTGeometry.TwistedRadial
open scoped ContDiff
namespace RHTower.D4BMThreeFieldMetric
open D4BMScalarStream D4BMScalarSourceIdentification D4BMThreeFieldReconstruction
open D4BMThreeFieldRows D4BMThreeFieldTensor D4BMMetricReconstruction D4BMModularCore
open D4BMFundamentalScalarMetric
noncomputable section
set_option autoImplicit false

def angularJets (Y : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) : AngularJet :=
  ![Y z,coordDeriv 0 Y z,coordDeriv 1 Y z,
    coordDeriv 0 (coordDeriv 0 Y) z,coordDeriv 0 (coordDeriv 1 Y) z,
    coordDeriv 1 (coordDeriv 1 Y) z]

def columnMetric (s a : ℂ) (k : Fin 3) (Y : (Fin 2 → ℝ) → ℂ) :=
  harmonicMetricField s (a^(2 : ℕ)) (radialColumn s k 0) (radialColumn s k 1)
    (radialColumn s k 2) (radialColumn s k 3) Y

/-- Each original column defines an actual twice differentiable metric field. -/
theorem columnMetric_smooth (s a : ℂ) (k : Fin 3) (Y : (Fin 2 → ℝ) → ℂ)
    (p : D4BMBackground.ExteriorPoint) (hY : ContDiffAt ℝ 2 Y (angularPoint p.val))
    (i j : Fin 4) : ContDiffAt ℝ 2 (fun x => columnMetric s a k Y x i j) p.val := by
  have hrad (m : Fin 4) : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => radialColumn s k m (x 1)) p.val := by
    have h := (radialColumn_smooth s k m).contDiffAt (isOpen_Ioi.mem_nhds p.property.1)
    exact ((contDiffAt_infty.mp h) 2).comp p.val (contDiff_apply ℝ ℝ 1).contDiffAt
  have hw : ContDiffAt ℝ 2 angularWeight p.val := by
    have hy : (p.val 3:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
    exact (contDiffAt_const.mul ((coordinate_contDiffAt 1 p.val).mul
      (coordinate_contDiffAt 1 p.val))).mul
      (((coordinate_contDiffAt 3 p.val).inv hy).mul ((coordinate_contDiffAt 3 p.val).inv hy))
  have hb := (envelope_contDiffAt (2*s) (a^(2 : ℕ)) p 2).mul
    (hY.comp p.val angularPoint_contDiff.contDiffAt)
  have h0 := hb.mul (hrad 0)
  have h1 := hb.mul (hrad 1)
  have h2 := hb.mul (hrad 2)
  have h3 := hb.mul (hw.mul (hrad 3))
  fin_cases i <;> fin_cases j <;>
    simp only [columnMetric,harmonicMetricField,Fin.reduceFinMk,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons]
  · exact h0
  · exact h1
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact h1
  · exact h2
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact h3
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact h3

private theorem rowOperator_scale (s r μ c : ℂ) (i : Fin 7) (J : RowJet) :
    rowOperator s r μ i (fun j n => c*J j n)=c*rowOperator s r μ i J := by
  fin_cases i <;> simp [rowOperator,harmonicTT,harmonicTR,harmonicRR,harmonicT,
    harmonicR,harmonicTF,harmonicL,div_eq_mul_inv] <;> ring

private theorem operatorMatrix_scale (s r y c : ℂ) (J : RowJet) (P : AngularJet) (i j : Fin 4) :
    operatorMatrix s r y (fun j n => c*J j n) P i j=c*operatorMatrix s r y J P i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [operatorMatrix,readRow,operatorSlope,rowOperator_scale,Fin.reduceFinMk,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] <;> ring

/-- The full Einstein action on one actual angular field, including its actual Laplacian and Hessian. -/
theorem columnMetric_equation (s a : ℂ) (k : Fin 3) (Y : (Fin 2 → ℝ) → ℂ)
    (p : D4BMBackground.ExteriorPoint) (hY : ContDiffAt ℝ 2 Y (angularPoint p.val)) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField (columnMetric s a k Y) p.val) (-3) i j =
      (envelope s a p.val)^(2 : ℕ)*operatorMatrix s (p.val 1) (p.val 3)
        (radialJets s (radialColumn s k) (p.val 1)) (angularJets Y (angularPoint p.val)) i j := by
  rw [D4BMBackground.actualJet_eq]
  unfold columnMetric
  rw [harmonicMetricField_jet s (a^(2 : ℕ)) (radialColumn_smooth s k 0) (radialColumn_smooth s k 1)
    (radialColumn_smooth s k 2) (radialColumn_smooth s k 3) Y p hY]
  change CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
    (jetFor s (p.val 1) (p.val 3)
      (fun j n => envelope (2*s) (a^(2 : ℕ)) p.val*radialJets s (radialColumn s k) (p.val 1) j n)
      (angularJets Y (angularPoint p.val))) (-3) i j = _
  obtain ⟨hr,hf⟩ := exterior_ne (p.val 1) p.property.1
  have hy : (p.val 3:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  rw [jetFor_cosmological _ _ _ _ _ hr hy hf,operatorMatrix_scale,envelope_double]

private theorem cosmological_field_add (p : D4BMBackground.ExteriorPoint)
    (F G : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun x => F x i j) p.val)
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun x => G x i j) p.val) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField (fun x i j => F x i j+G x i j) p.val) (-3) i j =
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField F p.val) (-3) i j+
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField G p.val) (-3) i j := by
  have hj := ofMetricField_combination (-1) F G p.val hF hG
  simp only [neg_mul,one_mul,sub_neg_eq_add] at hj
  have hc := cosmological_metricJetCombination (D4BMBackground.actualJet p)
    (ofMetricField F p.val) (ofMetricField G p.val)
    (D4BMBackground.exterior_metric_det_ne_zero p) (-1) (-3) i j
  have he := congrArg (fun K => CoordinateMetricTwoJet.Linearization.cosmological
    (D4BMBackground.actualJet p) K (-3) i j) hj
  exact he.trans (by simpa only [neg_mul,one_mul,sub_neg_eq_add] using hc)

/-- The normalized second constructed inverse has precisely the original reconstruction denominator. -/
def normalizedResponse (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  (2/targetShift (physicalRate q branch))*fullAngularField q branch z

def literalProfile (q : XiZeroCopy) (branch : Bool) : Fin 3 → (Fin 2 → ℝ) → ℂ :=
  ![squareSource q,D4BMAngularTwo.coordinateResponse q,normalizedResponse q branch]

theorem literalProfile_smooth (q : XiZeroCopy) (branch : Bool) (k : Fin 3)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) : ContDiffAt ℝ 2 (literalProfile q branch k) z := by
  fin_cases k
  · exact (D4BMLiteralCusp.scalar_contDiffAt _ 2 z hz).pow 2
  · exact (contDiffAt_infty.mp (D4BMAngularTwo.coordinateResponse_smooth q z hz)) 2
  · exact contDiffAt_const.mul ((contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 2)

theorem literalProfile_equations (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    lapJet (z 1) (angularJets (literalProfile q branch 1) z)=
      2*literalProfile q branch 1 z-literalProfile q branch 0 z ∧
    lapJet (z 1) (angularJets (literalProfile q branch 2) z)=
      targetShift (physicalRate q branch)*literalProfile q branch 2 z+literalProfile q branch 0 z := by
  constructor
  · have h := D4BMAngularTwo.coordinateResponse_equation q z hz
    change D4BMAngularSeries.hyperbolicLaplacian (D4BMAngularTwo.coordinateResponse q) z =
      2*D4BMAngularTwo.coordinateResponse q z-squareSource q z
    change 2*D4BMAngularTwo.coordinateResponse q z-_ = squareSource q z at h
    linear_combination -h
  · change D4BMAngularSeries.hyperbolicLaplacian
      (fun w => (2/targetShift (physicalRate q branch))*fullAngularField q branch w) z = _
    rw [D4BMAngularSeries.hyperbolicLaplacian_const_mul
      ((contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 2)]
    have h := fullAngularField_equation q branch z hz
    rw [D4BMHorizon.scalarLaplacian_eq _ z hz,parameter_physicalRate] at h
    change D4BMAngularSeries.hyperbolicLaplacian (fullAngularField q branch) z =
      targetShift (physicalRate q branch)*fullAngularField q branch z+
      (targetShift (physicalRate q branch)/2)*squareSource q z at h
    rw [h]
    change _ = targetShift (physicalRate q branch)*
      ((2/targetShift (physicalRate q branch))*fullAngularField q branch z)+squareSource q z
    have hd := (physical_shifts q branch).2.1
    field_simp

private theorem angularJets_hessian (Y : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) (k : Fin 2) :
    hessJet (z 1) (angularJets Y z) k=D4BMAngularTwoTensor.hessianTensor Y z 0 k := by
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  fin_cases k
  · simp only [hessJet,angularJets,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    simp [D4BMAngularTwoTensor.hessianTensor,D4BMHorizon.covariant_eq _ z hz,
      D4BMHorizon.scalarLaplacian_eq _ z hz,D4BMHorizon.covariantFormula,D4BMHorizon.metric]
    field_simp
    ring
  · simp [hessJet,angularJets,D4BMAngularTwoTensor.hessianTensor,D4BMHorizon.covariant_eq _ z hz,
      D4BMHorizon.covariantFormula,D4BMHorizon.metric,div_eq_mul_inv,mul_comm]

private theorem sourceMatrix_scale (s r y B F LF Fx Fy J0 J1 : ℂ) (i j : Fin 4) :
    sourceMatrix s r y B F LF Fx Fy J0 J1 i j =
      B^(2 : ℕ)*sourceMatrix s r y 1 F LF Fx Fy J0 J1 i j := by
  simp only [sourceMatrix,Matrix.smul_apply,smul_eq_mul,one_pow,one_mul]

/-- The actual metric reconstructed from the complete source and its two constructed inverses. -/
def literalMetric (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ := fun i j =>
  columnMetric (physicalRate q branch) a 0 (literalProfile q branch 0) x i j+
    columnMetric (physicalRate q branch) a 1 (literalProfile q branch 1) x i j+
    columnMetric (physicalRate q branch) a 2 (literalProfile q branch 2) x i j

/-- Every metric derivative in the full nonseparated reconstruction exists on the exterior. -/
theorem literalMetric_smooth (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => literalMetric q branch a x i j) p.val := by
  have h (k : Fin 3) := columnMetric_smooth (physicalRate q branch) a k
    (literalProfile q branch k) p (literalProfile_smooth q branch k _ p.property.2) i j
  exact ((h 0).add (h 1)).add (h 2)

private theorem literalMetric_action (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField (literalMetric q branch a) p.val) (-3) i j =
    (envelope (physicalRate q branch) a p.val)^(2 : ℕ)*
      (operatorMatrix (physicalRate q branch) (p.val 1) (p.val 3)
        (radialJets (physicalRate q branch) (radialColumn (physicalRate q branch) 0) (p.val 1))
        (angularJets (literalProfile q branch 0) (angularPoint p.val)) i j+
      operatorMatrix (physicalRate q branch) (p.val 1) (p.val 3)
        (radialJets (physicalRate q branch) (radialColumn (physicalRate q branch) 1) (p.val 1))
        (angularJets (literalProfile q branch 1) (angularPoint p.val)) i j+
      operatorMatrix (physicalRate q branch) (p.val 1) (p.val 3)
        (radialJets (physicalRate q branch) (radialColumn (physicalRate q branch) 2) (p.val 1))
        (angularJets (literalProfile q branch 2) (angularPoint p.val)) i j) := by
  let F (k : Fin 3) := columnMetric (physicalRate q branch) a k (literalProfile q branch k)
  have h (k : Fin 3) := columnMetric_smooth (physicalRate q branch) a k
    (literalProfile q branch k) p (literalProfile_smooth q branch k _ p.property.2)
  change CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
    (ofMetricField (fun x i j => F 0 x i j+F 1 x i j+F 2 x i j) p.val) (-3) i j = _
  rw [cosmological_field_add p (fun x i j => F 0 x i j+F 1 x i j) (F 2)
    (fun i j => (h 0 i j).add (h 1 i j)) (h 2),
    cosmological_field_add p (F 0) (F 1) (h 0) (h 1)]
  have he (k : Fin 3) := columnMetric_equation (physicalRate q branch) a k
    (literalProfile q branch k) p (literalProfile_smooth q branch k _ p.property.2) i j
  rw [show F 0=columnMetric (physicalRate q branch) a 0 (literalProfile q branch 0) from rfl,
    show F 1=columnMetric (physicalRate q branch) a 1 (literalProfile q branch 1) from rfl,
    show F 2=columnMetric (physicalRate q branch) a 2 (literalProfile q branch 2) from rfl,
    he 0,he 1,he 2]
  ring

/-- The full original scalar--scalar Einstein equation holds for the actual reconstructed metric.
Both physical branches retain the complete literal source and both constructed angular inverses. -/
theorem literalMetric_einstein (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.actualJet p)
      (ofMetricField (literalMetric q branch a) p.val) (-3) i j+
      D4BMQuadraticConservation.physicalQuadraticSource q branch a 0 p.val i j=0 := by
  let s := physicalRate q branch
  let z := angularPoint p.val
  let B := envelope s a p.val
  let J := fun k => radialJets s (radialColumn s k) (p.val 1)
  let P := fun k => angularJets (literalProfile q branch k) z
  obtain ⟨hQ,hR⟩ := literalProfile_equations q branch z p.property.2
  have hm := assembled_matrix s (p.val 1) (p.val 3) J (P 0) (P 1) (P 2)
    (fun i j => physical_rowCoefficients_zero q branch p.property.1 i j) hQ hR i j
  have hs : literalSourceTensor q branch (p.val 1) B z i j =
      B^(2 : ℕ)*sourceMatrix s (p.val 1) (p.val 3) 1 (P 0 0) (lapJet (p.val 3) (P 0))
        (P 0 1) (P 0 2)
        (hessJet (p.val 3) (P 0) 0+(s+1)*(s+2)*hessJet (p.val 3) (P 1) 0)
        (hessJet (p.val 3) (P 0) 1+(s+1)*(s+2)*hessJet (p.val 3) (P 1) 1) i j := by
    have hess (k : Fin 2) (n : Fin 3) : hessJet (p.val 3) (P n) k =
        D4BMAngularTwoTensor.hessianTensor (literalProfile q branch n) z 0 k :=
      angularJets_hessian (literalProfile q branch n) z p.property.2 k
    rw [hess 0 0,hess 0 1,hess 1 0,hess 1 1]
    unfold literalSourceTensor
    rw [D4BMHorizon.scalarLaplacian_eq _ z p.property.2,eigenvalue_physicalRate,sourceMatrix_scale]
    rfl
  rw [literalMetric_action q branch a p i j,physical_scalar_source q branch a p,hs]
  change B^(2 : ℕ)*(operatorMatrix s (p.val 1) (p.val 3) (J 0) (P 0) i j+
    operatorMatrix s (p.val 1) (p.val 3) (J 1) (P 1) i j+
    operatorMatrix s (p.val 1) (p.val 3) (J 2) (P 2) i j)+_ = 0
  linear_combination B^(2 : ℕ)*hm

end
end RHTower.D4BMThreeFieldMetric
