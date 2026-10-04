import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityMinor
import Mathlib.Algebra.Polynomial.Div

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare


def axisCoord : Coord → Polynomial ℂ
  | .U => Polynomial.X
  | .K => 0
  | .J => 0

def axis : Poly →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C axisCoord

@[simp] theorem axis_C (a : ℂ) : axis (C a)=Polynomial.C a := by simp [axis]
@[simp] theorem axis_X (i : Coord) : axis (X i)=axisCoord i := by simp [axis]

theorem axis_eval (P : Poly) (h : ℂ) :
    Polynomial.eval h (axis P)=eval (basePoint h 0 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,axisCoord,basePoint]

theorem axisMoment8_coeff_zero : (axis scaledMoment8).coeff 0=0 := by
  have he := axis_eval scaledMoment8 0
  simpa [scaledMoment8_zero,Polynomial.coeff_zero_eq_eval_zero] using he

theorem axisMoment10_coeff_zero : (axis scaledMoment10).coeff 0=0 := by
  have he := axis_eval scaledMoment10 0
  simpa [scaledMoment10_zero,Polynomial.coeff_zero_eq_eval_zero] using he

def axisMoment8Norm : {P : Polynomial ℂ // axis scaledMoment8=P} := by
  have he : axis scaledMoment8=axis scaledMoment8 := rfl
  conv at he =>
    rhs
    norm_num [axis,axisCoord,scaledMoment8,low8,midScaled8,upperScaled8,driftSquare,deficit,scaled8Part0Low,scaled8Part1Low,scaled8Part2Low,scaled8Part3Low,scaled8Part4Low,scaled8Part5Low,scaled8Part6Low,scaled8Part7Low,scaled8Part8Low,scaled8Part9Low,scaled8Part10Low,scaled8Part11Low,scaled8Part12Low,scaled8Part13Low,Finset.sum_range_succ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMoment10Norm : {P : Polynomial ℂ // axis scaledMoment10=P} := by
  have he : axis scaledMoment10=axis scaledMoment10 := rfl
  conv at he =>
    rhs
    norm_num [axis,axisCoord,scaledMoment10,low10,midScaled10,upperScaled10,driftSquare,deficit,scaled10Part0Low,scaled10Part1Low,scaled10Part2Low,scaled10Part3Low,scaled10Part4Low,scaled10Part5Low,scaled10Part6Low,scaled10Part7Low,scaled10Part8Low,scaled10Part9Low,scaled10Part10Low,scaled10Part11Low,scaled10Part12Low,scaled10Part13Low,scaled10Part14Low,scaled10Part15Low,scaled10Part16Low,scaled10Part17Low,scaled10Part18Low,scaled10Part19Low,scaled10Part20Low,scaled10Part21Low,scaled10Part22Low,Finset.sum_range_succ]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


theorem axisMoment8_coeff_one : (axis scaledMoment8).coeff 1=(6:ℂ)^10*105*24^4 := by
  rw [axisMoment8Norm.property]
  norm_num [axisMoment8Norm,← Polynomial.C_pow,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]

theorem axisMoment10_coeff_one : (axis scaledMoment10).coeff 1=0 := by
  rw [axisMoment10Norm.property]
  norm_num [axisMoment10Norm,← Polynomial.C_pow,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]

theorem axisMoment10_coeff_two : (axis scaledMoment10).coeff 2= -(6:ℂ)^12*945*24^5 := by
  rw [axisMoment10Norm.property]
  norm_num [axisMoment10Norm,← Polynomial.C_pow,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]


end
end HTGeometry.ThetaRatioInfinity
