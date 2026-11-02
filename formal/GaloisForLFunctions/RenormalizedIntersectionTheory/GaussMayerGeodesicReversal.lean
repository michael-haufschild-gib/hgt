import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerClosedGeodesics
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerInverseCycles

/-! Actual time reversal on periodic modular geodesics is right multiplication
by a quarter-turn. Under primitive-cycle coding it is integral matrix inversion. -/

open Matrix
open scoped MatrixGroups UpperHalfPlane
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerGeodesicFlow MayerGeodesicCentralizer MayerPrimitiveGeodesicReturns
open MayerClosedGeodesics MayerInverseCycles MayerOrientation
open MayerGaussCoding MayerCycleIndex MayerOrbitWords MayerHyperbolicLength
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicReversal

/-- The determinant-one half-turn of tangent direction at the imaginary unit. -/
def quarterTurn : Frame := ⟨!![0,-1;1,0],by norm_num [Matrix.det_fin_two]⟩

theorem quarterTurn_sq : quarterTurn*quarterTurn= -1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [quarterTurn,Matrix.mul_apply,Fin.sum_univ_two]

/-- Right multiplication by the quarter-turn reverses diagonal time. -/
theorem quarterTurn_flow (t : ℝ) : quarterTurn*diagonalFlow t=diagonalFlow (-t)*quarterTurn := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurn,diagonalFlow,Matrix.mul_apply,Fin.sum_univ_two]

private theorem flow_quarterTurn (t : ℝ) :
    diagonalFlow t*quarterTurn=quarterTurn*diagonalFlow (-t) := by
  simpa only [neg_neg] using (quarterTurn_flow (-t)).symm

private theorem quarterTurn_smul_I : quarterTurn • UpperHalfPlane.I=UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [quarterTurn,UpperHalfPlane.I]

/-- The quarter-turn reverses the actual unit-speed Poincaré lift. -/
theorem axis_reversed (C : Frame) (t : ℝ) : axis (C*quarterTurn) t=axis C (-t) := by
  rw [axis_eq_flow_basepoint,axis_eq_flow_basepoint,mul_assoc,quarterTurn_flow,
    ← mul_assoc,mul_smul,quarterTurn_smul_I]

/-- Reversing an axis replaces its return matrix by its inverse, preserving positive time. -/
theorem return_reversed (C : Frame) (γ : IntegralFrame) (t : ℝ)
    (hC : integralMap γ*C=C*diagonalFlow t) :
    integralMap γ⁻¹*(C*quarterTurn)=(C*quarterTurn)*diagonalFlow t := by
  apply mul_left_cancel (a := integralMap γ)
  rw [map_inv,mul_inv_cancel_left]
  symm
  calc
    integralMap γ*((C*quarterTurn)*diagonalFlow t)
        = ((integralMap γ*C)*quarterTurn)*diagonalFlow t := by simp only [mul_assoc]
    _ = ((C*diagonalFlow t)*quarterTurn)*diagonalFlow t := by rw [hC]
    _ = C*((diagonalFlow t*quarterTurn)*diagonalFlow t) := by simp only [mul_assoc]
    _ = C*((quarterTurn*diagonalFlow (-t))*diagonalFlow t) := by rw [flow_quarterTurn]
    _ = C*(quarterTurn*(diagonalFlow (-t)*diagonalFlow t)) := by rw [mul_assoc]
    _ = C*quarterTurn := by rw [← diagonalFlow_add,neg_add_cancel,diagonalFlow_zero,mul_one]

def reversePeriodic (C : PeriodicFrame) : PeriodicFrame :=
  ⟨C.val*quarterTurn,by
    obtain ⟨t,ht,hp⟩ := C.property
    obtain ⟨γ,hγ⟩ := (mem_periods_frame C.val t).mp hp
    exact ⟨t,ht,(mem_periods_frame _ t).mpr ⟨γ⁻¹,return_reversed C.val γ t hγ⟩⟩⟩

private theorem phase_reversed {C D : Frame} (h : Phase C D) :
    Phase (C*quarterTurn) (D*quarterTurn) := by
  obtain ⟨t,ht⟩ := h
  rw [flow_frame] at ht
  obtain ⟨γ,hγ⟩ := (frame_eq_iff (C*diagonalFlow t) D).mp ht.symm
  refine ⟨-t,?_⟩
  rw [flow_frame]
  apply Eq.symm
  apply (frame_eq_iff _ _).mpr
  refine ⟨γ,?_⟩
  calc
    integralMap γ*((C*quarterTurn)*diagonalFlow (-t))
        = integralMap γ*(C*(quarterTurn*diagonalFlow (-t))) := by rw [mul_assoc]
    _ = integralMap γ*(C*(diagonalFlow t*quarterTurn)) := by rw [quarterTurn_flow,neg_neg]
    _ = (integralMap γ*(C*diagonalFlow t))*quarterTurn := by simp only [mul_assoc]
    _ = D*quarterTurn := by rw [hγ]

/-- Orientation reversal defined on the actual periodic-flow quotient. -/
def reverse : ClosedGeodesic → ClosedGeodesic :=
  Quotient.map reversePeriodic (fun _ _ h => phase_reversed h)

theorem reverse_involutive : Function.Involutive reverse := by
  intro g
  refine Quotient.inductionOn g (fun C => ?_)
  apply Quotient.sound
  refine ⟨0,?_⟩
  rw [flow_zero]
  change frame C.val=frame ((C.val*quarterTurn)*quarterTurn)
  rw [mul_assoc,quarterTurn_sq,mul_neg,mul_one,frame_neg]

/-- The certified inverse-cycle map is the actual geometric reversal involution. -/
theorem reverse_ofCycle (c : Orbit) : reverse (ofCycle c)=ofCycle (inverseCycle c) := by
  obtain ⟨η,hηdet,hηraw⟩ :=
    (inverseCycle_eq_iff_inverse_conjugacy c (inverseCycle c)).mp rfl
  let ηI : IntegralFrame := ⟨η,hηdet⟩
  have hspec := actualPairedMatrix_inverse_spec (representative c).val
  let B : IntegralFrame := ⟨integralInverse (actualPairedMatrix (representative c).val),hspec.1⟩
  have hB : B*cycleReturn c=1 := Subtype.ext hspec.2.1
  have hBi : B=(cycleReturn c)⁻¹ := by
    calc
      B=(B*cycleReturn c)*(cycleReturn c)⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = _ := by rw [hB,one_mul]
  have hη : ηI*(cycleReturn c)⁻¹=cycleReturn (inverseCycle c)*ηI := by
    rw [← hBi]
    exact Subtype.ext hηraw
  apply Quotient.sound
  exact phase_of_conjugate_returns (cycleFrame c*quarterTurn) (cycleFrame (inverseCycle c))
    (cycleReturn c)⁻¹ (cycleReturn (inverseCycle c)) ηI
    (orbitTranslationLength_pos c) (orbitTranslationLength_pos (inverseCycle c))
    (return_reversed _ _ _ (cycleFrame_return c)) (cycleFrame_return (inverseCycle c)) hη

theorem length_reverse (g : ClosedGeodesic) : MayerClosedGeodesics.length (reverse g)=MayerClosedGeodesics.length g := by
  obtain ⟨c,rfl⟩ := ofCycle_surjective g
  rw [reverse_ofCycle,length_ofCycle,length_ofCycle,orbitTranslationLength_inverseCycle]

/-- Self-inverse integral classes are exactly the geometrically self-reversing closed orbits. -/
theorem reverse_ofCycle_eq_iff (c : Orbit) : reverse (ofCycle c)=ofCycle c ↔ inverseCycle c=c := by
  rw [reverse_ofCycle]
  exact ofCycle_injective.eq_iff

#print axioms quarterTurn_flow
#print axioms axis_reversed
#print axioms return_reversed
#print axioms reverse_involutive
#print axioms reverse_ofCycle
#print axioms length_reverse
#print axioms reverse_ofCycle_eq_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicReversal
