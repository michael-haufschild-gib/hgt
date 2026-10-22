import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSquareSlope
import Mathlib.Algebra.MvPolynomial.Division
namespace HTGeometry.ThetaRatioSquare
noncomputable section
open MvPolynomial ThetaRatioSource

def seamResetCoord : Coord → Poly
  | .U => 0
  | .K => X .K
  | .J => X .J
def seamReset : Poly →+* Poly := eval₂Hom C seamResetCoord
@[simp] theorem seamReset_C (c : ℂ) : seamReset (C c)=C c := by simp [seamReset]
@[simp] theorem seamReset_X (i : Coord) : seamReset (X i)=seamResetCoord i := by simp [seamReset]

theorem seamReset_division (P : Poly) : ∃ Q : Poly, P=X Coord.U*Q+seamReset P := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0,by simp⟩
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    refine ⟨a+b,?_⟩
    rw [map_add]
    conv_lhs => rw [ha,hb]
    ring
  | mul_X p i hp =>
    obtain ⟨a,ha⟩ := hp
    cases i with
    | U => exact ⟨p,by simp [seamResetCoord]; ring⟩
    | K =>
      refine ⟨a*X Coord.K,?_⟩
      simp only [map_mul,seamReset_X,seamResetCoord]
      conv_lhs => rw [ha]
      ring
    | J =>
      refine ⟨a*X Coord.J,?_⟩
      simp only [map_mul,seamReset_X,seamResetCoord]
      conv_lhs => rw [ha]
      ring

theorem seamReset_eval (P : Poly) (v : Coord → ℂ) :
    eval v (seamReset P)=eval (fun i => if i=Coord.U then 0 else v i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,seamResetCoord]

theorem square_eval_seam (P : Poly) (v : Coord → ℂ) (hv : v .U=0) :
    eval v (square P)=eval v P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,squareCoord,hv]

theorem slope_eval_seam (v : Coord → ℂ) (hv : v .U=0) : eval v slope=0 := by
  have he := congrArg (eval v) slope_eq
  rw [square_eval_seam slope v hv] at he
  simpa only [map_mul,eval_X,hv,zero_mul] using he.symm

theorem slope_seamReset : seamReset slope=0 := by
  apply MvPolynomial.funext
  intro v
  rw [seamReset_eval,slope_eval_seam (fun i => if i=Coord.U then 0 else v i) (by simp)]
  simp

def reducedSlope : Poly := slope.divMonomial (Finsupp.single Coord.U 1)

theorem slope_seam_factor : slope=X Coord.U*reducedSlope := by
  obtain ⟨Q,hQ⟩ := seamReset_division slope
  rw [slope_seamReset,add_zero] at hQ
  have hQ' : Q=reducedSlope := by
    apply eq_divMonomial_single (r := 0) (by simpa using hQ)
    simp
  rwa [hQ'] at hQ

theorem reducedSlope_seam_value (v : Coord → ℂ) (hv : v .U=0) :
    eval v reducedSlope=eval v (pderiv Coord.U slope) := by
  conv_rhs => rw [slope_seam_factor]
  simp [pderiv_X,hv]

end
end HTGeometry.ThetaRatioSquare
