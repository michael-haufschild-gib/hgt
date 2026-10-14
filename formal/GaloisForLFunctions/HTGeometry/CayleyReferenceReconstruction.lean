import GaloisForLFunctions.HTGeometry.OperatorReferenceObservation
import GaloisForLFunctions.HTGeometry.LpObservationModulus
import GaloisForLFunctions.HTGeometry.PaperCayleySourceBounds

/-! # Literal Cayley source reconstruction from two reference responses

Distances to one and to the imaginary unit recover a circle point. Singleton
histories transfer this identity to every diagonal Cayley source operator.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

def circleFromReferenceNorms (r s : ℝ) : ℂ :=
  ((1 - r ^ 2 / 2 : ℝ) : ℂ) + ((1 - s ^ 2 / 2 : ℝ) : ℂ) * Complex.I

theorem circleFromReferenceNorms_apply (z : Circle) :
    circleFromReferenceNorms ‖(z : ℂ) - 1‖ ‖(z : ℂ) - Complex.I‖ = (z : ℂ) := by
  have h0 := Complex.sq_norm (z : ℂ)
  rw [Circle.norm_coe, one_pow, Complex.normSq_apply] at h0
  have h1 := Complex.sq_norm ((z : ℂ) - 1)
  have hi := Complex.sq_norm ((z : ℂ) - Complex.I)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, sub_zero] at h1 hi
  apply Complex.ext
  · simp only [circleFromReferenceNorms, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    nlinarith
  · simp only [circleFromReferenceNorms, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]
    nlinarith

variable {I : Type*} [DecidableEq I]

theorem operatorReferenceNorm_coordinate_single
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (z : ℂ) (j : I) :
    operatorReferenceNorm T z (lp.single 2 j (1 : ℂ)) = ‖w j - z‖ := by
  rw [operatorReferenceNorm, coordinate_mul_single T w hT]
  have hs : z • lp.single (E := fun _ : I => ℂ) 2 j (1 : ℂ) =
      lp.single (E := fun _ : I => ℂ) 2 j z := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : I => ℂ) 2 j z (1 : ℂ)).symm
  rw [hs, ← lp.single_sub]
  exact lp.norm_single (E := fun _ : I => ℂ) (by norm_num : (0 : ENNReal) < 2) j (w j - z)

def lpReferencePhase
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (j : I) : ℂ :=
  circleFromReferenceNorms (operatorReferenceNorm T 1 (lp.single 2 j (1 : ℂ)))
    (operatorReferenceNorm T Complex.I (lp.single 2 j (1 : ℂ)))

theorem lpReferencePhase_eq_circle
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → Circle)
    (hT : ∀ y i, T y i = (w i : ℂ) * y i) (j : I) :
    lpReferencePhase T j = (w j : ℂ) := by
  rw [lpReferencePhase, operatorReferenceNorm_coordinate_single T _ hT,
    operatorReferenceNorm_coordinate_single T _ hT, circleFromReferenceNorms_apply]

def lpReferenceSource
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (j : I) : ℝ :=
  paperRealCayleyInverse (lpReferencePhase T j)

theorem lpReferenceSource_eq
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → ℝ)
    (hT : ∀ y i, T y i = realCayley (w i) * y i) (j : I) :
    lpReferenceSource T j = w j := by
  rw [lpReferenceSource, lpReferencePhase_eq_circle T (fun i => circleCayley (w i)) hT]
  exact paperRealCayleyInverse_apply _

end
end GaloisForLFunctions.HTGeometry
