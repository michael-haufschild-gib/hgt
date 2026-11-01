import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Topology.Algebra.Order.Archimedean

/-! The modular geodesic flow on the integral left quotient of real frames.
The diagonal flow has unit-speed Poincaré lifts. Integral return traces
force every return-time subgroup to be trivial or a positive cyclic lattice. -/

open Matrix
open scoped MatrixGroups UpperHalfPlane
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicFlow

abbrev Frame := SL(2, ℝ)
abbrev IntegralFrame := SL(2, ℤ)

def integralMap : IntegralFrame →* Frame := SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- Unit-speed diagonal geodesic evolution. -/
def diagonalFlow (t : ℝ) : Frame :=
  ⟨!![Real.exp (t/2),0;0,Real.exp (-t/2)],by
    rw [Matrix.det_fin_two]
    change Real.exp (t/2)*Real.exp (-t/2)-0*0=1
    rw [← Real.exp_add]
    simp only [show t/2+-t/2=0 by ring,Real.exp_zero,mul_zero,sub_zero]⟩

theorem diagonalFlow_zero : diagonalFlow 0=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalFlow]

theorem diagonalFlow_add (s t : ℝ) : diagonalFlow (s+t)=diagonalFlow s*diagonalFlow t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow,Matrix.mul_apply,Fin.sum_univ_two,add_div,Real.exp_add,mul_comm]

theorem diagonalFlow_neg (t : ℝ) : diagonalFlow (-t)=(diagonalFlow t)⁻¹ := by
  apply mul_left_cancel (a := diagonalFlow t)
  rw [← diagonalFlow_add,add_neg_cancel,diagonalFlow_zero,mul_inv_cancel]

def integralFrameSetoid : Setoid Frame where
  r C D := ∃ γ : IntegralFrame, integralMap γ*C=D
  iseqv := by
    refine ⟨fun C => ⟨1,by rw [map_one,one_mul]⟩,?_,?_⟩
    · rintro C D ⟨γ,hγ⟩
      refine ⟨γ⁻¹,?_⟩
      rw [map_inv,← hγ,inv_mul_cancel_left]
    · rintro C D E ⟨γ,hγ⟩ ⟨δ,hδ⟩
      refine ⟨δ*γ,?_⟩
      rw [map_mul,mul_assoc,hγ,hδ]

/-- The actual integral left quotient of real determinant-one frames. -/
def ModularFrame := Quotient integralFrameSetoid

def frame (C : Frame) : ModularFrame := Quotient.mk integralFrameSetoid C

theorem frame_eq_iff (C D : Frame) :
    frame C=frame D ↔ ∃ γ : IntegralFrame, integralMap γ*C=D := by
  change Quotient.mk integralFrameSetoid C=Quotient.mk integralFrameSetoid D ↔
    integralFrameSetoid.r C D
  exact Quotient.eq_iff_equiv

/-- Right diagonal evolution descends through the integral left action. -/
def flow (t : ℝ) : ModularFrame → ModularFrame :=
  Quotient.map (fun C => C*diagonalFlow t) (by
    rintro C D ⟨γ,hγ⟩
    exact ⟨γ,by rw [← mul_assoc,hγ]⟩)

theorem flow_frame (t : ℝ) (C : Frame) : flow t (frame C)=frame (C*diagonalFlow t) := rfl

theorem flow_zero (x : ModularFrame) : flow 0 x=x := by
  refine Quotient.inductionOn x (fun C => ?_)
  change frame (C*diagonalFlow 0)=frame C
  rw [diagonalFlow_zero,mul_one]

theorem flow_add (s t : ℝ) (x : ModularFrame) : flow (s+t) x=flow t (flow s x) := by
  refine Quotient.inductionOn x (fun C => ?_)
  change frame (C*diagonalFlow (s+t))=frame ((C*diagonalFlow s)*diagonalFlow t)
  rw [diagonalFlow_add,mul_assoc]

/-- Return times of the actual modular flow. -/
def periods (x : ModularFrame) : AddSubgroup ℝ where
  carrier := {t | flow t x=x}
  zero_mem' := flow_zero x
  add_mem' := by
    intro s t hs ht
    change flow (s+t) x=x
    rw [flow_add,hs,ht]
  neg_mem' := by
    intro t ht
    have h := congrArg (flow (-t)) ht
    rw [← flow_add,add_neg_cancel,flow_zero] at h
    exact h.symm

theorem mem_periods_frame (C : Frame) (t : ℝ) :
    t ∈ periods (frame C) ↔ ∃ γ : IntegralFrame, integralMap γ*C=C*diagonalFlow t := by
  change flow t (frame C)=frame C ↔ _
  rw [flow_frame,eq_comm,frame_eq_iff]

/-- The vertical unit-speed geodesic before applying a real frame. -/
def vertical (t : ℝ) : ℍ := ⟨⟨0,Real.exp t⟩,Real.exp_pos t⟩

def axis (C : Frame) (t : ℝ) : ℍ := C • vertical t

theorem isometry_axis (C : Frame) : Isometry (axis C) :=
  (isometry_smul ℍ C).comp (UpperHalfPlane.isometry_vertical_line 0)

private theorem coe_diagonal_action (t : ℝ) (z : ℍ) :
    ((diagonalFlow t • z : ℍ) : ℂ) = (Real.exp t : ℂ)*(z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change ((Real.exp (t/2) : ℂ)*(z : ℂ)+0)/(0*(z : ℂ)+(Real.exp (-t/2) : ℂ)) = _
  simp only [add_zero,zero_mul,zero_add]
  have hr : Real.exp (t/2)/Real.exp (-t/2)=Real.exp t := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hc : (Real.exp (t/2) : ℂ)/(Real.exp (-t/2) : ℂ)=(Real.exp t : ℂ) := by
    exact_mod_cast hr
  calc
    _ = ((Real.exp (t/2) : ℂ)/(Real.exp (-t/2) : ℂ))*(z : ℂ) := by ring
    _ = _ := by rw [hc]

theorem diagonalFlow_smul_I (t : ℝ) : diagonalFlow t • UpperHalfPlane.I=vertical t := by
  apply UpperHalfPlane.ext
  rw [coe_diagonal_action]
  apply Complex.ext
  · change Real.exp t*0-0*1=0
    ring
  · change Real.exp t*1+0*0=Real.exp t
    ring

/-- The flow projects to the actual unit-speed Poincaré geodesic. -/
theorem axis_eq_flow_basepoint (C : Frame) (t : ℝ) :
    axis C t=(C*diagonalFlow t) • UpperHalfPlane.I := by
  rw [mul_smul,diagonalFlow_smul_I]
  rfl

private def realTrace (A : Frame) : ℝ := (A : Matrix (Fin 2) (Fin 2) ℝ).trace

private theorem realTrace_mul_comm (A B : Frame) : realTrace (A*B)=realTrace (B*A) :=
  Matrix.trace_mul_comm _ _

/-- Every return matrix has the diagonal-flow trace, in its literal integral entries. -/
theorem return_trace (C : Frame) (t : ℝ) (γ : IntegralFrame)
    (hγ : integralMap γ*C=C*diagonalFlow t) :
    ((γ 0 0+γ 1 1 : ℤ) : ℝ)=Real.exp (t/2)+Real.exp (-t/2) := by
  have he : integralMap γ=C*diagonalFlow t*C⁻¹ := by
    calc
      integralMap γ=(integralMap γ*C)*C⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = _ := by rw [hγ]
  have ht : realTrace (integralMap γ)=realTrace (diagonalFlow t) := by
    calc
      _ = realTrace ((C*diagonalFlow t)*C⁻¹) := congrArg realTrace he
      _ = realTrace (C⁻¹*(C*diagonalFlow t)) := realTrace_mul_comm _ _
      _ = _ := by rw [inv_mul_cancel_left]
  simp only [realTrace,Matrix.trace_fin_two] at ht
  change (γ 0 0 : ℝ)+(γ 1 1 : ℝ)=Real.exp (t/2)+Real.exp (-t/2) at ht
  simpa only [Int.cast_add] using ht

private theorem trace_bounds {t : ℝ} (ht : 0 < t) (htδ : t < 2*Real.log 2) :
    2 < Real.exp (t/2)+Real.exp (-t/2) ∧
      Real.exp (t/2)+Real.exp (-t/2) < 3 := by
  have hx : 1 < Real.exp (t/2) := Real.one_lt_exp_iff.mpr (by linarith only [ht])
  have hxy : Real.exp (t/2)*Real.exp (-t/2)=1 := by
    rw [← Real.exp_add,show t/2+-t/2=0 by ring,Real.exp_zero]
  have hx2 : Real.exp (t/2) < 2 := by
    calc
      Real.exp (t/2) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (by linarith only [htδ])
      _ = 2 := Real.exp_log (by norm_num)
  have hy1 : Real.exp (-t/2) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [ht])
  constructor
  · by_contra hn
    have hsum : Real.exp (t/2)+Real.exp (-t/2) ≤ 2 := le_of_not_gt hn
    have hp := mul_nonneg (Real.exp_pos (t/2)).le (sub_nonneg.mpr hsum)
    have hs := sq_pos_of_pos (sub_pos.mpr hx)
    nlinarith only [hp,hs,hxy]
  · linarith only [hx2,hy1]

/-- Integrality excludes uniformly small positive periods at every modular frame. -/
theorem positive_period_lower_bound (x : ModularFrame) (t : ℝ)
    (hp : t ∈ periods x) (ht : 0 < t) : 2*Real.log 2 ≤ t := by
  revert hp
  refine Quotient.inductionOn x (fun C hp => ?_)
  by_contra hδ
  obtain ⟨γ,hγ⟩ := (mem_periods_frame C t).mp hp
  have htrace := return_trace C t γ hγ
  obtain ⟨hlo,hhi⟩ := trace_bounds ht (lt_of_not_ge hδ)
  rw [← htrace] at hlo hhi
  have hlow : (2 : ℤ) < γ 0 0+γ 1 1 := by exact_mod_cast hlo
  have hhigh : γ 0 0+γ 1 1 < (3 : ℤ) := by exact_mod_cast hhi
  omega

theorem periods_not_dense (x : ModularFrame) : ¬ Dense (periods x : Set ℝ) := by
  intro hd
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨t,hp,ht,hδ⟩ := hd.exists_mem_open (U := Set.Ioo 0 (2*Real.log 2))
    isOpen_Ioo ⟨Real.log 2,hlog,by linarith only [hlog]⟩
  exact (not_lt_of_ge (positive_period_lower_bound x t hp ht)) hδ

/-- Every modular geodesic has either no nonzero return or a positive cyclic period group. -/
theorem periods_eq_bot_or_positive_lattice (x : ModularFrame) :
    periods x=⊥ ∨ ∃ T : ℝ, 0 < T ∧ periods x=AddSubgroup.zmultiples T := by
  obtain ⟨a,ha⟩ := (AddSubgroup.dense_or_cyclic (periods x)).resolve_left (periods_not_dense x)
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  rcases lt_trichotomy a 0 with hn | hz | hp
  · exact Or.inr ⟨-a,neg_pos.mpr hn,by rw [AddSubgroup.zmultiples_neg]; exact ha⟩
  · subst a
    left
    rw [ha]
    ext t
    simp
  · exact Or.inr ⟨a,hp,ha⟩

#print axioms flow_zero
#print axioms flow_add
#print axioms mem_periods_frame
#print axioms isometry_axis
#print axioms axis_eq_flow_basepoint
#print axioms return_trace
#print axioms positive_period_lower_bound
#print axioms periods_not_dense
#print axioms periods_eq_bot_or_positive_lattice

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicFlow
