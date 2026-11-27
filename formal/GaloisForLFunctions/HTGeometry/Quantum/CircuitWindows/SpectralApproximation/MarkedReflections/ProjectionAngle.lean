import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Norm of a difference of two projections with scalar compressions -/
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
noncomputable section
variable {A : Type*} [CStarAlgebra A]

private theorem selfadjoint_square (T : A) (h : star T=T) : ‖T*T‖=‖T‖^2 := by
  simpa only [h,pow_two] using CStarRing.norm_star_mul_self T

/-- If each projection compresses the other to p times itself, their
difference satisfies a cubic. Its squared norm is at most 1 − p. -/
theorem projection_angle (P Q : A) (hP : P*P=P) (hQ : Q*Q=Q) (hsP : star P=P) (hsQ : star Q=Q)
    {p : ℝ} (hp : p≤1) (hPQ : P*Q*P=p • P) (hQP : Q*P*Q=p • Q) :
    ‖P-Q‖^2 ≤ 1-p := by
  let T := P-Q
  have hs : star T=T := by simp only [T,star_sub,hsP,hsQ]
  have hthree : T*T*T=(1-p) • T := by
    calc
      _ = (P*P)*P-(P*P)*Q-P*Q*P+P*(Q*Q)-Q*(P*P)+Q*P*Q+(Q*Q)*P-(Q*Q)*Q := by
        dsimp only [T]
        noncomm_ring
      _ = _ := by
        simp only [hP,hQ,hPQ,hQP,T,sub_smul,one_smul,smul_sub]
        abel
  have hfour : (T*T)*(T*T)=(1-p) • (T*T) := by rw [←mul_assoc (T*T) T T,hthree,smul_mul_assoc]
  have hs₂ : star (T*T)=T*T := by rw [star_mul,hs]
  have h : ‖T*T‖^2=(1-p)*‖T*T‖ := by
    rw [←selfadjoint_square (T*T) hs₂,hfour,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hp)]
  change ‖T‖^2 ≤ 1-p
  rw [←selfadjoint_square T hs]
  by_contra! hh
  have hpos := (sub_nonneg.mpr hp).trans_lt hh
  nlinarith only [h,mul_pos hpos (sub_pos.mpr hh)]

#print axioms projection_angle
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
