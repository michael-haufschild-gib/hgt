import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveGeodesicReturns
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerGeodesicCentralizer

/-! Primitive pair cycles classify the periodic orbits of the actual modular
geodesic flow. The classification preserves least positive geometric period. -/

open Matrix
open scoped MatrixGroups UpperHalfPlane
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerGeodesicFlow MayerGeodesicCentralizer MayerPrimitiveGeodesicReturns
open MayerCoding MayerHyperbolic MayerGaussCoding MayerPairMultiplier
open MayerPrimitiveCycles MayerCycleIndex MayerOrbitWords MayerHyperbolicLength
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerClosedGeodesics

private theorem flow_neg_cancel (t : ℝ) (x : ModularFrame) : flow (-t) (flow t x)=x := by
  rw [← flow_add,add_neg_cancel,flow_zero]

private theorem flow_comm (s t : ℝ) (x : ModularFrame) :
    flow s (flow t x)=flow t (flow s x) := by
  rw [← flow_add,← flow_add,add_comm]

/-- A time shift leaves the exact return-time subgroup unchanged. -/
theorem periods_flow (t : ℝ) (x : ModularFrame) : periods (flow t x)=periods x := by
  ext s
  change (flow s (flow t x)=flow t x) ↔ flow s x=x
  constructor
  · intro h
    rw [flow_comm] at h
    have he := congrArg (flow (-t)) h
    simpa only [flow_neg_cancel] using he
  · intro h
    rw [flow_comm,h]

/-- Frames on the same oriented modular geodesic, with arbitrary origins of time. -/
def Phase (C D : Frame) : Prop := ∃ t : ℝ, frame D=flow t (frame C)

theorem phase_refl (C : Frame) : Phase C C := ⟨0,(flow_zero _).symm⟩

theorem phase_symm {C D : Frame} (h : Phase C D) : Phase D C := by
  obtain ⟨t,ht⟩ := h
  exact ⟨-t,by rw [ht,flow_neg_cancel]⟩

theorem phase_trans {C D E : Frame} (h : Phase C D) (k : Phase D E) : Phase C E := by
  obtain ⟨s,hs⟩ := h
  obtain ⟨t,ht⟩ := k
  exact ⟨s+t,by rw [flow_add,← hs,← ht]⟩

theorem phase_periods {C D : Frame} (h : Phase C D) : periods (frame C)=periods (frame D) := by
  obtain ⟨t,ht⟩ := h
  rw [ht,periods_flow]

/-- A periodic frame is defined by actual modular return, independently of word coding. -/
def PeriodicFrame := {C : Frame // ∃ t : ℝ, 0 < t ∧ t ∈ periods (frame C)}

def periodicPhaseSetoid : Setoid PeriodicFrame where
  r C D := Phase C.val D.val
  iseqv := ⟨fun C => phase_refl C.val,fun h => phase_symm h,fun h k => phase_trans h k⟩

/-- Oriented closed geodesics are the periodic orbits of the actual diagonal flow. -/
def ClosedGeodesic := Quotient periodicPhaseSetoid

def geodesic (C : PeriodicFrame) : ClosedGeodesic := Quotient.mk periodicPhaseSetoid C

def periodicCycle (c : Orbit) : PeriodicFrame :=
  ⟨cycleFrame c,orbitTranslationLength c,orbitTranslationLength_pos c,
    (cycleFrame_least_period c).1.1⟩

def ofCycle (c : Orbit) : ClosedGeodesic := geodesic (periodicCycle c)

private theorem rotated_iff_split (u v : List (ℕ × ℕ)) :
    List.IsRotated u v ↔ ∃ a b : List (ℕ × ℕ), u=a++b ∧ v=b++a := by
  constructor
  · intro h
    obtain ⟨n,hn,he⟩ := List.isRotated_iff_mod.mp h
    refine ⟨u.take n,u.drop n,(List.take_append_drop n u).symm,?_⟩
    rw [List.rotate_eq_drop_append_take hn] at he
    exact he.symm
  · rintro ⟨a,b,rfl,rfl⟩
    exact List.isRotated_append

private theorem pairReturn_conjugacy_iff (u v : List (ℕ × ℕ)) (hu : u ≠ []) (hv : v ≠ []) :
    (∃ γ : IntegralFrame, γ*pairReturn u=pairReturn v*γ) ↔ List.IsRotated u v := by
  rw [rotated_iff_split,← actualPairedMatrix_conjugacy_iff u v hu hv]
  constructor
  · rintro ⟨γ,hγ⟩
    exact ⟨γ,γ.property,congrArg (fun A : IntegralFrame => (A : Matrix (Fin 2) (Fin 2) ℤ)) hγ⟩
  · rintro ⟨γ,hdet,hγ⟩
    exact ⟨⟨γ,hdet⟩,Subtype.ext hγ⟩

/-- Integral conjugacy of the actual primitive return matrices is exactly cycle equality. -/
theorem cycleReturn_conjugacy_iff (c d : Orbit) :
    (∃ γ : IntegralFrame, γ*cycleReturn c=cycleReturn d*γ) ↔ c=d := by
  change (∃ γ : IntegralFrame, γ*pairReturn (representative c).val=
    pairReturn (representative d).val*γ) ↔ c=d
  rw [pairReturn_conjugacy_iff _ _ (representative c).property.1 (representative d).property.1]
  constructor
  · intro h
    have he : Quotient.mk (primitiveSetoid (ℕ × ℕ)) (representative c)=
        Quotient.mk (primitiveSetoid (ℕ × ℕ)) (representative d) := Quotient.sound h
    exact (Quotient.out_eq c).symm.trans (he.trans (Quotient.out_eq d))
  · rintro rfl
    exact List.IsRotated.refl _

private theorem positive_trace_time_injective {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : Real.exp (s/2)+Real.exp (-s/2)=Real.exp (t/2)+Real.exp (-t/2)) : s=t := by
  have hx : 1 < Real.exp (s/2) := Real.one_lt_exp_iff.mpr (by linarith only [hs])
  have hy : 1 < Real.exp (t/2) := Real.one_lt_exp_iff.mpr (by linarith only [ht])
  have hx0 := Real.exp_pos (s/2)
  have hy0 := Real.exp_pos (t/2)
  have hxy : 1 < Real.exp (s/2)*Real.exp (t/2) := by
    have hp := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)
    nlinarith only [hx,hy,hp]
  rw [show -s/2= -(s/2) by ring,show -t/2= -(t/2) by ring,Real.exp_neg,Real.exp_neg] at he
  have hp : (Real.exp (s/2)-Real.exp (t/2))*(Real.exp (s/2)*Real.exp (t/2)-1)=0 := by
    calc
      _ = (Real.exp (s/2)+(Real.exp (s/2))⁻¹-
          (Real.exp (t/2)+(Real.exp (t/2))⁻¹))*(Real.exp (s/2)*Real.exp (t/2)) := by
            field_simp [hx0.ne',hy0.ne']
            ring
      _ = 0 := by rw [he,sub_self,zero_mul]
  have hxyEq : Real.exp (s/2)=Real.exp (t/2) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_pos.mpr hxy).ne')
  have h := Real.exp_injective hxyEq
  linarith only [h]

private theorem positive_return_trace (C : Frame) (γ : IntegralFrame) {t : ℝ}
    (ht : 0 < t) (hγ : integralMap γ*C=C*diagonalFlow t) : 2 < γ 0 0+γ 1 1 := by
  have hx : 1 < Real.exp (t/2) := Real.one_lt_exp_iff.mpr (by linarith only [ht])
  have hxy : Real.exp (t/2)*Real.exp (-t/2)=1 := by
    rw [← Real.exp_add,show t/2+-t/2=0 by ring,Real.exp_zero]
  have htr : 2 < Real.exp (t/2)+Real.exp (-t/2) := by
    by_contra hn
    have hp := mul_nonneg (Real.exp_pos (t/2)).le (sub_nonneg.mpr (le_of_not_gt hn))
    have hs := sq_pos_of_pos (sub_pos.mpr hx)
    nlinarith only [hp,hs,hxy]
  rw [← return_trace C t γ hγ] at htr
  exact_mod_cast htr

private theorem phase_of_common_positive_return (C D : Frame) (γ : IntegralFrame)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hC : integralMap γ*C=C*diagonalFlow s)
    (hD : integralMap γ*D=D*diagonalFlow t) : Phase C D := by
  have he := positive_trace_time_injective hs ht
    ((return_trace C s γ hC).symm.trans (return_trace D t γ hD))
  subst t
  exact common_return_phase C D hs.ne' γ hC hD

private theorem return_left_translate (C : Frame) (γ δ η : IntegralFrame) (t : ℝ)
    (hC : integralMap γ*C=C*diagonalFlow t) (hη : η*γ=δ*η) :
    integralMap δ*(integralMap η*C)=(integralMap η*C)*diagonalFlow t := by
  calc
    _ = integralMap (δ*η)*C := by rw [map_mul,mul_assoc]
    _ = integralMap (η*γ)*C := by rw [hη]
    _ = integralMap η*(integralMap γ*C) := by rw [map_mul,mul_assoc]
    _ = _ := by rw [hC,mul_assoc]

private theorem frame_left_translate (η : IntegralFrame) (C : Frame) :
    frame (integralMap η*C)=frame C :=
  ((frame_eq_iff C (integralMap η*C)).mpr ⟨η,rfl⟩).symm

/-- Positive integral returns in the same conjugacy class determine the same oriented geodesic. -/
theorem phase_of_conjugate_returns (C D : Frame) (γ δ η : IntegralFrame)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hC : integralMap γ*C=C*diagonalFlow s)
    (hD : integralMap δ*D=D*diagonalFlow t) (hη : η*γ=δ*η) : Phase C D := by
  obtain ⟨u,hu⟩ := phase_of_common_positive_return (integralMap η*C) D δ hs ht
    (return_left_translate C γ δ η s hC hη) hD
  exact ⟨u,by simpa only [frame_left_translate] using hu⟩

private theorem return_pow (C : Frame) (γ : IntegralFrame) (t : ℝ)
    (hC : integralMap γ*C=C*diagonalFlow t) (n : ℕ) :
    integralMap (γ^n)*C=C*diagonalFlow ((n : ℝ)*t) := by
  have h : SemiconjBy C (diagonalFlow t) (integralMap γ) := hC.symm
  simpa only [map_pow,diagonalFlow_nat_mul] using Eq.symm (h.pow_right n)

/-- Equal geometric orbits force conjugate primitive return matrices, hence equal pair cycles. -/
theorem ofCycle_injective : Function.Injective ofCycle := by
  intro c d hcd
  have hp : Phase (cycleFrame c) (cycleFrame d) := Quotient.exact hcd
  have hperiod := phase_periods hp
  have hc := cycleFrame_least_period c
  have hd := cycleFrame_least_period d
  rw [hperiod] at hc
  have hL : orbitTranslationLength c=orbitTranslationLength d := hc.unique hd
  obtain ⟨t,ht⟩ := hp
  rw [flow_frame] at ht
  obtain ⟨η,hη⟩ := (frame_eq_iff (cycleFrame c*diagonalFlow t) (cycleFrame d)).mp ht.symm
  apply (cycleReturn_conjugacy_iff c d).mp
  refine ⟨η,?_⟩
  have hreal : integralMap (η*cycleReturn c)*(cycleFrame c*diagonalFlow t)=
      integralMap (cycleReturn d*η)*(cycleFrame c*diagonalFlow t) := by
    rw [map_mul,map_mul]
    calc
      (integralMap η*integralMap (cycleReturn c))*(cycleFrame c*diagonalFlow t)
          = integralMap η*((integralMap (cycleReturn c)*cycleFrame c)*diagonalFlow t) := by simp only [mul_assoc]
      _ = integralMap η*((cycleFrame c*diagonalFlow (orbitTranslationLength c))*diagonalFlow t) := by rw [cycleFrame_return]
      _ = (integralMap η*(cycleFrame c*diagonalFlow t))*diagonalFlow (orbitTranslationLength d) := by
        rw [hL]
        simp only [mul_assoc,← diagonalFlow_add]
        rw [add_comm]
      _ = cycleFrame d*diagonalFlow (orbitTranslationLength d) := by rw [hη]
      _ = integralMap (cycleReturn d)*cycleFrame d := (cycleFrame_return d).symm
      _ = (integralMap (cycleReturn d)*integralMap η)*(cycleFrame c*diagonalFlow t) := by rw [mul_assoc,hη]
  exact SpecialLinearGroup.map_intCast_injective (mul_right_cancel hreal)

private theorem pairReturn_wordPower (u : List (ℕ × ℕ)) (n : ℕ) :
    pairReturn (wordPower u n)=(pairReturn u)^n := Subtype.ext (actualPairedMatrix_wordPower u n)

/-- Any actual periodic frame is on the geometric orbit of a primitive pair cycle. -/
theorem exists_cycle_phase (C : PeriodicFrame) : ∃ c : Orbit, Phase C.val (cycleFrame c) := by
  obtain ⟨t,ht,htp⟩ := C.property
  obtain ⟨γ,hγ⟩ := (mem_periods_frame C.val t).mp htp
  have htr := positive_return_trace C.val γ ht hγ
  obtain ⟨ps,hps,η,hηdet,hηraw⟩ := exists_actualPairedMatrix_intertwiner γ γ.property htr
  let ηI : IntegralFrame := ⟨η,hηdet⟩
  have hη : ηI*γ=pairReturn ps*ηI := Subtype.ext hηraw
  obtain ⟨v,n,hv,hn,hpsv⟩ := exists_primitive_root ps hps
  let c : Orbit := Quotient.mk (primitiveSetoid (ℕ × ℕ)) ⟨v,hv⟩
  have hrot : List.IsRotated v (representative c).val :=
    (Quotient.exact (Quotient.out_eq c)).symm
  obtain ⟨δ,hδ⟩ := (pairReturn_conjugacy_iff v (representative c).val hv.1
    (representative c).property.1).mpr hrot
  change δ*pairReturn v=cycleReturn c*δ at hδ
  have hpδ : δ*(pairReturn v)^n=(cycleReturn c)^n*δ :=
    (show SemiconjBy δ (pairReturn v) (cycleReturn c) from hδ).pow_right n
  have hconj : (δ*ηI)*γ=(cycleReturn c)^n*(δ*ηI) := by
    rw [mul_assoc,hη,hpsv,pairReturn_wordPower,← mul_assoc,hpδ,mul_assoc]
  refine ⟨c,phase_of_conjugate_returns C.val (cycleFrame c) γ ((cycleReturn c)^n)
    (δ*ηI) ht ?_ hγ (return_pow _ _ _ (cycleFrame_return c) n) hconj⟩
  exact mul_pos (by exact_mod_cast hn) (orbitTranslationLength_pos c)

theorem ofCycle_surjective : Function.Surjective ofCycle := by
  intro g
  refine Quotient.inductionOn g (fun C => ?_)
  obtain ⟨c,hc⟩ := exists_cycle_phase C
  exact ⟨c,Quotient.sound (phase_symm hc)⟩

/-- Primitive pair cycles and genuine oriented closed modular geodesics are equivalent. -/
def cycleEquiv : Orbit ≃ ClosedGeodesic :=
  Equiv.ofBijective ofCycle ⟨ofCycle_injective,ofCycle_surjective⟩

/-- Return-time subgroup of a closed geodesic, independent of its phase representative. -/
def geodesicPeriods : ClosedGeodesic → AddSubgroup ℝ :=
  Quotient.lift (fun C : PeriodicFrame => periods (frame C.val))
    (fun _ _ h => phase_periods h)

/-- Geometric length is the infimum of the positive actual return times. -/
def length (g : ClosedGeodesic) : ℝ := sInf {t : ℝ | t ∈ geodesicPeriods g ∧ 0 < t}

/-- The intrinsic least return length agrees with the displacement-defined cycle length. -/
theorem length_ofCycle (c : Orbit) : length (ofCycle c)=orbitTranslationLength c :=
  (cycleFrame_least_period c).csInf_eq

theorem length_isLeast (g : ClosedGeodesic) :
    IsLeast {t : ℝ | t ∈ geodesicPeriods g ∧ 0 < t} (length g) := by
  obtain ⟨c,rfl⟩ := ofCycle_surjective g
  rw [length_ofCycle]
  exact cycleFrame_least_period c

theorem length_pos (g : ClosedGeodesic) : 0 < length g := (length_isLeast g).1.2

#print axioms periods_flow
#print axioms cycleReturn_conjugacy_iff
#print axioms phase_of_conjugate_returns
#print axioms ofCycle_injective
#print axioms exists_cycle_phase
#print axioms ofCycle_surjective
#print axioms cycleEquiv
#print axioms length_ofCycle
#print axioms length_isLeast
#print axioms length_pos

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerClosedGeodesics
