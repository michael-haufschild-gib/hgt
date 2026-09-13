import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThreeFieldRows
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamEinsteinLower

/-! Free-angular-jet lifting of the original sourced radial reconstruction. -/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open GaloisForLFunctions.HTGeometry.TwistedRadial
open scoped ContDiff
namespace RHTower.D4BMThreeFieldTensor
open D4BMScalarStream D4BMScalarSourceIdentification D4BMThreeFieldReconstruction
open D4BMThreeFieldRows D4BMMetricReconstruction D4BMModularCore
open D4BMFundamentalScalarMetric
noncomputable section
set_option autoImplicit false

abbrev AngularJet := Fin 6 → ℂ

def lapJet (y : ℂ) (P : AngularJet) : ℂ := y^2*(P 3+P 5)
def hessJet (y : ℂ) (P : AngularJet) : Fin 2 → ℂ :=
  ![(P 3-P 5)/2-P 2/y,P 4+P 1/y]

def readRow (s r : ℂ) (i : Fin 7) (J : RowJet) (P LP : ℂ) : ℂ :=
  rowOperator s r 0 i J*P+operatorSlope s r i J*LP

def operatorMatrix (s r y : ℂ) (J : RowJet) (P : AngularJet) : Matrix (Fin 4) (Fin 4) ℂ :=
  let TT := readRow s r 0 J (P 0) (lapJet y P)
  let TR := readRow s r 1 J (P 0) (lapJet y P)
  let RR := readRow s r 2 J (P 0) (lapJet y P)
  let tx := rowOperator s r 0 3 J*P 1
  let ty := rowOperator s r 0 3 J*P 2
  let rx := rowOperator s r 0 4 J*P 1
  let ry := rowOperator s r 0 4 J*P 2
  let L := readRow s r 6 J (P 0) (lapJet y P)/y^2
  let A := rowOperator s r 0 5 J*hessJet y P 0
  let C := rowOperator s r 0 5 J*hessJet y P 1
  !![TT,TR,tx,ty;TR,RR,rx,ry;tx,rx,L+A,C;ty,ry,C,L-A]

def jetFor (s r y : ℂ) (J : RowJet) (P : AngularJet) : CoordinateMetricTwoJet 4 ℂ :=
  metricJet (2*s) r y (J 0 0) (J 0 1) (J 0 2) (J 1 0) (J 1 1) (J 1 2)
    (J 2 0) (J 2 1) (J 2 2) (J 3 0) (J 3 1) (J 3 2)
    (P 0) (P 1) (P 2) (P 3) (P 4) (P 5)

private theorem jetFor_component_0_0 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 0 0 = operatorMatrix s r y J P 0 0 := by
  unfold jetFor
  rw [metricJet_cosmological_0_0 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_0_1 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 0 1 = operatorMatrix s r y J P 0 1 := by
  unfold jetFor
  rw [metricJet_cosmological_0_1 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_0_2 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 0 2 = operatorMatrix s r y J P 0 2 := by
  unfold jetFor
  rw [metricJet_cosmological_0_2 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_0_3 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 0 3 = operatorMatrix s r y J P 0 3 := by
  unfold jetFor
  rw [metricJet_cosmological_0_3 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_1_0 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 1 0 = operatorMatrix s r y J P 1 0 := by
  unfold jetFor
  rw [metricJet_cosmological_1_0 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_1_1 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 1 1 = operatorMatrix s r y J P 1 1 := by
  unfold jetFor
  rw [metricJet_cosmological_1_1 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_1_2 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 1 2 = operatorMatrix s r y J P 1 2 := by
  unfold jetFor
  rw [metricJet_cosmological_1_2 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_1_3 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 1 3 = operatorMatrix s r y J P 1 3 := by
  unfold jetFor
  rw [metricJet_cosmological_1_3 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_2_0 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 2 0 = operatorMatrix s r y J P 2 0 := by
  unfold jetFor
  rw [metricJet_cosmological_2_0 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_2_1 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 2 1 = operatorMatrix s r y J P 2 1 := by
  unfold jetFor
  rw [metricJet_cosmological_2_1 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_2_2 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 2 2 = operatorMatrix s r y J P 2 2 := by
  unfold jetFor
  rw [metricJet_cosmological_2_2 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_2_3 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 2 3 = operatorMatrix s r y J P 2 3 := by
  unfold jetFor
  rw [metricJet_cosmological_2_3 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_3_0 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 3 0 = operatorMatrix s r y J P 3 0 := by
  unfold jetFor
  rw [metricJet_cosmological_3_0 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_3_1 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 3 1 = operatorMatrix s r y J P 3 1 := by
  unfold jetFor
  rw [metricJet_cosmological_3_1 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp

private theorem jetFor_component_3_2 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 3 2 = operatorMatrix s r y J P 3 2 := by
  unfold jetFor
  rw [metricJet_cosmological_3_2 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

private theorem jetFor_component_3_3 (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) 3 3 = operatorMatrix s r y J P 3 3 := by
  unfold jetFor
  rw [metricJet_cosmological_3_3 hr hy hf]
  simp [operatorMatrix,readRow,operatorSlope,rowOperator,lapJet,hessJet,
    harmonicTT,harmonicTR,harmonicRR,harmonicT,harmonicR,harmonicTF,harmonicL,div_eq_mul_inv]
  field_simp
  ring

/-- The actual free-angular-jet Einstein operator, with no eigenfunction assumption. -/
theorem jetFor_cosmological (s r y : ℂ) (J : RowJet) (P : AngularJet)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^2-1 ≠ 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet r y)
      (jetFor s r y J P) (-3) i j = operatorMatrix s r y J P i j := by
  fin_cases i <;> fin_cases j
  · exact jetFor_component_0_0 s r y J P hr hy hf
  · exact jetFor_component_0_1 s r y J P hr hy hf
  · exact jetFor_component_0_2 s r y J P hr hy hf
  · exact jetFor_component_0_3 s r y J P hr hy hf
  · exact jetFor_component_1_0 s r y J P hr hy hf
  · exact jetFor_component_1_1 s r y J P hr hy hf
  · exact jetFor_component_1_2 s r y J P hr hy hf
  · exact jetFor_component_1_3 s r y J P hr hy hf
  · exact jetFor_component_2_0 s r y J P hr hy hf
  · exact jetFor_component_2_1 s r y J P hr hy hf
  · exact jetFor_component_2_2 s r y J P hr hy hf
  · exact jetFor_component_2_3 s r y J P hr hy hf
  · exact jetFor_component_3_0 s r y J P hr hy hf
  · exact jetFor_component_3_1 s r y J P hr hy hf
  · exact jetFor_component_3_2 s r y J P hr hy hf
  · exact jetFor_component_3_3 s r y J P hr hy hf

/-- Substitution of the two forced angular equations into one affine radial row. -/
theorem assembled_read (s r : ℂ) (i : Fin 7) (J : Fin 3 → RowJet)
    (hc : ∀ a, rowCoefficients s r i J a=0) (F U V LF : ℂ) :
    readRow s r i (J 0) F LF+readRow s r i (J 1) U (2*U-F)+
      readRow s r i (J 2) V (targetShift s*V+F)+
      sourceConstant s r i*F+sourceSlope s r i*LF+sourceResidue s r i*U = 0 := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  simp only [rowCoefficients,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2 h3
  unfold readRow
  linear_combination LF*h0+F*h1+U*h2+V*h3

private theorem mixed_read (s r : ℂ) (i : Fin 7) (hi : i=3 ∨ i=4 ∨ i=5)
    (J : RowJet) (P LP : ℂ) : readRow s r i J P LP=rowOperator s r 0 i J*P := by
  rcases hi with rfl | rfl | rfl <;>
    simp [readRow,operatorSlope,rowOperator,harmonicT,harmonicR,harmonicTF]

/-- All sixteen free-angular-jet equations follow from the original coefficient equations. -/
theorem assembled_matrix (s r y : ℂ) (J : Fin 3 → RowJet) (P Q R : AngularJet)
    (hc : ∀ i a, rowCoefficients s r i J a=0)
    (hQ : lapJet y Q=2*Q 0-P 0) (hR : lapJet y R=targetShift s*R 0+P 0)
    (i j : Fin 4) :
    operatorMatrix s r y (J 0) P i j+operatorMatrix s r y (J 1) Q i j+
      operatorMatrix s r y (J 2) R i j+
      sourceMatrix s r y 1 (P 0) (lapJet y P) (P 1) (P 2)
        (hessJet y P 0+(s+1)*(s+2)*hessJet y Q 0)
        (hessJet y P 1+(s+1)*(s+2)*hessJet y Q 1) i j=0 := by
  have horb (k : Fin 7) := assembled_read s r k J (hc k) (P 0) (Q 0) (R 0) (lapJet y P)
  rw [← hQ,← hR] at horb
  have hm (k : Fin 7) (hk : k=3 ∨ k=4 ∨ k=5) (a b c : ℂ) :=
    assembled_read s r k J (hc k) a b c 0
  have htx := hm 3 (Or.inl rfl) (P 1) (Q 1) (R 1)
  have hty := hm 3 (Or.inl rfl) (P 2) (Q 2) (R 2)
  have hrx := hm 4 (Or.inr (Or.inl rfl)) (P 1) (Q 1) (R 1)
  have hry := hm 4 (Or.inr (Or.inl rfl)) (P 2) (Q 2) (R 2)
  have hA := hm 5 (Or.inr (Or.inr rfl)) (hessJet y P 0) (hessJet y Q 0) (hessJet y R 0)
  have hB := hm 5 (Or.inr (Or.inr rfl)) (hessJet y P 1) (hessJet y Q 1) (hessJet y R 1)
  simp [mixed_read s r 3 (Or.inl rfl),mixed_read s r 4 (Or.inr (Or.inl rfl)),
    mixed_read s r 5 (Or.inr (Or.inr rfl)),sourceConstant,sourceSlope,sourceResidue] at htx hty hrx hry hA hB
  have hTT := horb 0
  have hTR := horb 1
  have hRR := horb 2
  have hL := horb 6
  simp [sourceConstant,sourceSlope,sourceResidue] at hTT hTR hRR hL
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply,Fin.reduceFinMk,operatorMatrix,sourceMatrix,affineRead,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
      Matrix.smul_apply,smul_eq_mul,one_pow,one_mul]
  · linear_combination hTT
  · linear_combination hTR
  · linear_combination htx
  · linear_combination hty
  · linear_combination hTR
  · linear_combination hRR
  · linear_combination hrx
  · linear_combination hry
  · linear_combination htx
  · linear_combination hrx
  · linear_combination hL/y^2+hA
  · linear_combination hB
  · linear_combination hty
  · linear_combination hry
  · linear_combination hB
  · linear_combination hL/y^2-hA

end
end RHTower.D4BMThreeFieldTensor
