import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockSourceCore
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem clock_factor_second (P Q : Poly) (hPQ : P=X Coord.U*Q) (r z : ℂ) :
    2*eval (basePoint 0 r z) (pderiv Coord.U Q)=
      eval (basePoint 0 r z) (pderiv Coord.U (pderiv Coord.U P)) := by
  rw [hPQ]
  simp [pderiv_X,Pi.single_eq_same,basePoint]
  ring

theorem defectLift_second_zero (P : Poly) (r z : ℂ) :
    eval (basePoint 0 r z) (pderiv Coord.U (pderiv Coord.U (defectLift P)))=
      eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U P))-
        2*r*eval (basePoint 0 9 z) (pderiv Coord.K P) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  rw [defectLift_pderiv]
  simp only [map_sub,pderiv_mul,defectLift_pderiv]
  norm_num [pderiv_X,Pi.single_apply,basePoint,hUK,defectLift_eval]

def clearMoment6SecondClockNorm (z : ℂ) : {c : ℂ // eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment6))=c} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have he : eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment6))=eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment6)) := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6,clearMoment6Part0,clearMoment6Part1,clearMoment6Part2,clearMoment6Part3,clearMoment6Part4,clearMoment6Part5,clearMoment6Part6,clearMoment6Part7,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKU,hKJ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment6FirstDriftNorm (z : ℂ) : {c : ℂ // eval (basePoint 0 9 z) (pderiv Coord.K clearMoment6)=c} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have he : eval (basePoint 0 9 z) (pderiv Coord.K clearMoment6)=eval (basePoint 0 9 z) (pderiv Coord.K clearMoment6) := rfl
  conv at he =>
    rhs
    norm_num [clearMoment6,clearMoment6Part0,clearMoment6Part1,clearMoment6Part2,clearMoment6Part3,clearMoment6Part4,clearMoment6Part5,clearMoment6Part6,clearMoment6Part7,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKU,hKJ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def defectMoment6CoreFirstNorm (r z : ℂ) : {c : ℂ // eval (basePoint 0 r z) (pderiv Coord.U defectMoment6Core)=c} := by
  have h2 := clock_factor_second _ _ defectMoment6_factor r z
  rw [defectLift_second_zero,(clearMoment6SecondClockNorm z).property,
    (clearMoment6FirstDriftNorm z).property] at h2
  have he : eval (basePoint 0 r z) (pderiv Coord.U defectMoment6Core)=(1/2:ℂ)*
      ((clearMoment6SecondClockNorm z).val-2*r*(clearMoment6FirstDriftNorm z).val) := by
    linear_combination (1/2:ℂ)*h2
  conv at he =>
    rhs
    dsimp only [clearMoment6SecondClockNorm,clearMoment6FirstDriftNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8SecondClockNorm (z : ℂ) : {c : ℂ // eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment8))=c} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have he : eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment8))=eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment8)) := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8,clearMoment8Part0,clearMoment8Part1,clearMoment8Part2,clearMoment8Part3,clearMoment8Part4,clearMoment8Part5,clearMoment8Part6,clearMoment8Part7,clearMoment8Part8,clearMoment8Part9,clearMoment8Part10,clearMoment8Part11,clearMoment8Part12,clearMoment8Part13,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKU,hKJ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment8FirstDriftNorm (z : ℂ) : {c : ℂ // eval (basePoint 0 9 z) (pderiv Coord.K clearMoment8)=c} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have he : eval (basePoint 0 9 z) (pderiv Coord.K clearMoment8)=eval (basePoint 0 9 z) (pderiv Coord.K clearMoment8) := rfl
  conv at he =>
    rhs
    norm_num [clearMoment8,clearMoment8Part0,clearMoment8Part1,clearMoment8Part2,clearMoment8Part3,clearMoment8Part4,clearMoment8Part5,clearMoment8Part6,clearMoment8Part7,clearMoment8Part8,clearMoment8Part9,clearMoment8Part10,clearMoment8Part11,clearMoment8Part12,clearMoment8Part13,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKU,hKJ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def defectMoment8CoreFirstNorm (r z : ℂ) : {c : ℂ // eval (basePoint 0 r z) (pderiv Coord.U defectMoment8Core)=c} := by
  have h2 := clock_factor_second _ _ defectMoment8_factor r z
  rw [defectLift_second_zero,(clearMoment8SecondClockNorm z).property,
    (clearMoment8FirstDriftNorm z).property] at h2
  have he : eval (basePoint 0 r z) (pderiv Coord.U defectMoment8Core)=(1/2:ℂ)*
      ((clearMoment8SecondClockNorm z).val-2*r*(clearMoment8FirstDriftNorm z).val) := by
    linear_combination (1/2:ℂ)*h2
  conv at he =>
    rhs
    dsimp only [clearMoment8SecondClockNorm,clearMoment8FirstDriftNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment10SecondClockNorm (z : ℂ) : {c : ℂ // eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment10))=c} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have he : eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment10))=eval (basePoint 0 9 z) (pderiv Coord.U (pderiv Coord.U clearMoment10)) := rfl
  conv at he =>
    rhs
    norm_num [clearMoment10,clearMoment10Part0,clearMoment10Part1,clearMoment10Part2,clearMoment10Part3,clearMoment10Part4,clearMoment10Part5,clearMoment10Part6,clearMoment10Part7,clearMoment10Part8,clearMoment10Part9,clearMoment10Part10,clearMoment10Part11,clearMoment10Part12,clearMoment10Part13,clearMoment10Part14,clearMoment10Part15,clearMoment10Part16,clearMoment10Part17,clearMoment10Part18,clearMoment10Part19,clearMoment10Part20,clearMoment10Part21,clearMoment10Part22,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKU,hKJ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def clearMoment10FirstDriftNorm (z : ℂ) : {c : ℂ // eval (basePoint 0 9 z) (pderiv Coord.K clearMoment10)=c} := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := Ne.symm hUK
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have he : eval (basePoint 0 9 z) (pderiv Coord.K clearMoment10)=eval (basePoint 0 9 z) (pderiv Coord.K clearMoment10) := rfl
  conv at he =>
    rhs
    norm_num [clearMoment10,clearMoment10Part0,clearMoment10Part1,clearMoment10Part2,clearMoment10Part3,clearMoment10Part4,clearMoment10Part5,clearMoment10Part6,clearMoment10Part7,clearMoment10Part8,clearMoment10Part9,clearMoment10Part10,clearMoment10Part11,clearMoment10Part12,clearMoment10Part13,clearMoment10Part14,clearMoment10Part15,clearMoment10Part16,clearMoment10Part17,clearMoment10Part18,clearMoment10Part19,clearMoment10Part20,clearMoment10Part21,clearMoment10Part22,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ,hKU,hKJ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def defectMoment10CoreFirstNorm (r z : ℂ) : {c : ℂ // eval (basePoint 0 r z) (pderiv Coord.U defectMoment10Core)=c} := by
  have h2 := clock_factor_second _ _ defectMoment10_factor r z
  rw [defectLift_second_zero,(clearMoment10SecondClockNorm z).property,
    (clearMoment10FirstDriftNorm z).property] at h2
  have he : eval (basePoint 0 r z) (pderiv Coord.U defectMoment10Core)=(1/2:ℂ)*
      ((clearMoment10SecondClockNorm z).val-2*r*(clearMoment10FirstDriftNorm z).val) := by
    linear_combination (1/2:ℂ)*h2
  conv at he =>
    rhs
    dsimp only [clearMoment10SecondClockNorm,clearMoment10FirstDriftNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticCrossCoreZeroNorm (r z : ℂ) :
    {c : ℂ // eval (basePoint 0 r z) kineticCrossCore=c} := by
  have he := clock_factor_first _ _ kineticCross_factor r z
  conv at he =>
    rhs
    simp only [kineticCross,pderiv_mul,pderiv_pow,
      map_sub,map_add,map_mul,map_pow,map_ofNat]
    rw [(defectMoment6CoreFirstNorm r z).property,(defectMoment10CoreFirstNorm r z).property,
      (defectMoment8CoreFirstNorm r z).property,defectMoment6Core_zero,
      defectMoment8Core_zero,defectMoment10Core_zero]
    dsimp only [defectMoment6CoreFirstNorm,defectMoment8CoreFirstNorm,defectMoment10CoreFirstNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def compactMinorZeroNorm (r z : ℂ) :
    {c : ℂ // eval (basePoint 0 r z) compactMinor=c} := by
  have he : eval (basePoint 0 r z) compactMinor=eval (basePoint 0 r z) compactMinor := rfl
  conv at he =>
    rhs
    simp only [compactMinor,map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,defectLift_eval]
    norm_num only [mul_zero,sub_zero]
    rw [clearMoment2_zero,(kineticCrossCoreZeroNorm r z).property,defectMoment4Core_zero,
      defectMoment6Core_zero,defectMoment8Core_zero,defectMoment10Core_zero]
    dsimp only [kineticCrossCoreZeroNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem defectLie_clock_zero_congr (P Q : Poly)
    (hPQ : ∀ r z : ℂ, eval (basePoint 0 r z) P=eval (basePoint 0 r z) Q)
    (r z : ℂ) :
    eval (basePoint 0 r z) (defectLie P)=eval (basePoint 0 r z) (defectLie Q) := by
  obtain ⟨R,hR⟩ := clock_factor_of_zero (P-Q) (by
    intro r z
    simp only [map_sub,hPQ,sub_self])
  have he := congrArg (fun A : Poly => eval (basePoint 0 r z) (defectLie A)) hR
  simp only [defectLie,flow_sub75,flow_mul,flow_X,map_sub,map_add,map_mul,
    eval_X,basePoint] at he
  rw [(defectField_zero r z).1] at he
  simpa only [defectLie,zero_mul,zero_add,sub_eq_zero] using he

theorem compactSlope_zero_lie (r z : ℂ) :
    eval (basePoint 0 r z) compactSlope=6*eval (basePoint 0 r z) (defectLie compactMinor) := by
  simp [compactSlope,basePoint]

end
end HTGeometry.ThetaRatioKineticContraction
