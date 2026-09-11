import GaloisForLFunctions.HTGeometry.PolynomialSignedPoissonSourceTransform
import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource

/-! # Literal theta atoms in the exact signed Poisson clock

Every atom index and every derivative order use the same source transform,
including the complete theta seed. No source sign is assumed.
-/

open Polynomial
namespace HTGeometry.SignedPoisson
noncomputable section

/-- A literal Gaussian theta-clock frame, for every polynomial clock observable. -/
def atomMomentFrame (p : ℝ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  Real.exp (x/2-p*Real.exp (2*x))*(negativePoissonPolynomial P).eval (p*Real.exp (2*x))

/-- Theta differentiation is exactly multiplication by 2 J + 1/2 in the signed clock. -/
theorem hasDerivAt_atomMomentFrame (p : ℝ) (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (atomMomentFrame p P) (atomMomentFrame p (thetaClockMultiply P) x) x := by
  have hq : HasDerivAt (fun y : ℝ => p*Real.exp (2*y)) (2*(p*Real.exp (2*x))) x := by
    simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm,id_eq] using
      (((hasDerivAt_id x).const_mul (2 : ℝ)).exp.const_mul p)
  have hg := (((hasDerivAt_id x).div_const 2).sub hq).exp
  have hp := ((negativePoissonPolynomial P).hasDerivAt (p*Real.exp (2*x))).comp x hq
  have hm := hg.mul hp
  convert hm using 1
  all_goals try rfl
  all_goals simp only [atomMomentFrame,thetaClockMultiply]
  all_goals rw [map_add,map_smul,map_smul,negativePoissonPolynomial_X_mul]
  all_goals simp only [eval_add,eval_smul,eval_mul,eval_sub,eval_X,smul_eq_mul,Pi.sub_apply,Function.comp_apply,id_eq]
  all_goals ring

/-- Every derivative retains the same polynomial clock, with no finite-order truncation. -/
theorem iteratedDeriv_atomMomentFrame (p : ℝ) (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (atomMomentFrame p P) = atomMomentFrame p ((thetaClockMultiply^[n]) P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext x
    exact (hasDerivAt_atomMomentFrame p ((thetaClockMultiply^[n]) P) x).deriv

/-- The clock construction is the actual nth theta source atom, including its full seed. -/
theorem atomMomentFrame_thetaClockSeed_eq_source (n : ℕ) (x : ℝ) :
    atomMomentFrame (Real.pi*(n : ℝ)^2) thetaClockSeed x = RHTower.thetaCuspSourceTerm x n := by
  have he : Real.exp (2*x) = Real.exp x^2 := by
    rw [show 2*x=x+x by ring,Real.exp_add]
    ring
  have hq : (Real.pi*(n : ℝ)^2)*Real.exp (2*x) = Real.pi*((n : ℝ)*Real.exp x)^2 := by
    rw [he]
    ring
  unfold atomMomentFrame thetaClockSeed
  rw [negativePoissonPolynomial_thetaSeed]
  simp only [eval_sub,eval_mul,eval_pow,eval_ofNat,eval_X]
  rw [hq,sub_eq_add_neg,Real.exp_add]
  unfold RHTower.thetaCuspSourceTerm RHTower.thetaCuspSeed
  simp only [neg_mul]
  ring

/-- All literal theta-atom jets admit the same source-identified signed-clock formula. -/
theorem iteratedDeriv_thetaCuspSourceTerm_eq_atomMomentFrame (n k : ℕ) :
    iteratedDeriv k (fun x : ℝ => RHTower.thetaCuspSourceTerm x n) =
      atomMomentFrame (Real.pi*(n : ℝ)^2) ((thetaClockMultiply^[k]) thetaClockSeed) := by
  have he : (fun x : ℝ => RHTower.thetaCuspSourceTerm x n) =
      atomMomentFrame (Real.pi*(n : ℝ)^2) thetaClockSeed := by
    funext x
    exact (atomMomentFrame_thetaClockSeed_eq_source n x).symm
  rw [he]
  exact iteratedDeriv_atomMomentFrame _ _ _


end
end HTGeometry.SignedPoisson
