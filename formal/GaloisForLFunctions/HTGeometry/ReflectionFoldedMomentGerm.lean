import Mathlib

/-!
# Affine reflection folded moment germs

An anti-invariant source under an affine reflection becomes an ordinarily reflected normalized
divided-difference germ.  Consequently its jets split by parity and every Hankel matrix formed
from the even jets is invariant under reflection of the base point.

This is a source-independent constraint.  No positivity, measure representation, differential
equation, or Riemann-hypothesis input is assumed.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- The centered spectral trace attached to a source `T` at base point `sigma`. -/
def affineRelativeTrace (T : ℂ → ℂ) (sigma z : ℂ) : ℂ :=
  Complex.I * (T (sigma + z * Complex.I) - T sigma)

/-- Normalized division of the centered trace by the spectral coordinate. -/
def reflectionFoldedMomentGerm (T : ℂ → ℂ) (sigma : ℂ) : ℂ → ℂ :=
  fun z => -dslope (affineRelativeTrace T sigma) 0 z

/-- Affine anti-reflection of the source reflects the relative trace with one minus sign. -/
theorem affineRelativeTrace_reflection
    (T : ℂ → ℂ) (kappa sigma z : ℂ)
    (hreflect : ∀ w, T (kappa - w) = -T w) :
    affineRelativeTrace T (kappa - sigma) z =
      -affineRelativeTrace T sigma (-z) := by
  rw [affineRelativeTrace, affineRelativeTrace]
  have hz := hreflect (sigma - z * Complex.I)
  have hs := hreflect sigma
  have harg : kappa - (sigma - z * Complex.I) =
      kappa - sigma + z * Complex.I := by ring
  rw [harg] at hz
  have hnegarg : sigma + -z * Complex.I = sigma - z * Complex.I := by ring
  rw [hnegarg, hz, hs]
  ring

/-- Normalized divided difference converts `-T(-z)` into ordinary reflection. -/
private theorem neg_dslope_neg_comp (T : ℂ → ℂ) (z : ℂ) :
    -dslope (fun w => -T (-w)) 0 z = -dslope T 0 (-z) := by
  by_cases hz : z = 0
  · subst z
    rw [neg_zero, dslope_same, dslope_same]
    have hcomp := iteratedDeriv_comp_neg 1 T (0 : ℂ)
    have hneg := iteratedDeriv_neg 1 (fun w : ℂ => T (-w)) (0 : ℂ)
    rw [iteratedDeriv_one, iteratedDeriv_one, neg_zero] at hcomp
    rw [iteratedDeriv_one, iteratedDeriv_one] at hneg
    have hfun : (fun w : ℂ => -T (-w)) = -(fun w : ℂ => T (-w)) := rfl
    rw [hfun, hneg, hcomp]
    ring
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [dslope_of_ne _ hz, dslope_of_ne _ hnz,
      slope_def_module, slope_def_module]
    simp only [neg_zero]
    ring

/-- **Reflection-folding law.**  An affine anti-reflection of the source becomes ordinary
reflection of the normalized moment germ. -/
theorem reflectionFoldedMomentGerm_reflection
    (T : ℂ → ℂ) (kappa sigma z : ℂ)
    (hreflect : ∀ w, T (kappa - w) = -T w) :
    reflectionFoldedMomentGerm T (kappa - sigma) z =
      reflectionFoldedMomentGerm T sigma (-z) := by
  have htrace : affineRelativeTrace T (kappa - sigma) =
      fun w => -affineRelativeTrace T sigma (-w) := by
    funext w
    exact affineRelativeTrace_reflection T kappa sigma w hreflect
  rw [reflectionFoldedMomentGerm, reflectionFoldedMomentGerm, htrace]
  exact neg_dslope_neg_comp (affineRelativeTrace T sigma) z

/-- Every folded jet has the parity forced by base reflection. -/
theorem iteratedDeriv_reflectionFoldedMomentGerm_reflection
    (T : ℂ → ℂ) (kappa sigma : ℂ)
    (hreflect : ∀ w, T (kappa - w) = -T w) (n : ℕ) :
    iteratedDeriv n (reflectionFoldedMomentGerm T (kappa - sigma)) 0 =
      (-1 : ℂ) ^ n * iteratedDeriv n (reflectionFoldedMomentGerm T sigma) 0 := by
  have hgerm : reflectionFoldedMomentGerm T (kappa - sigma) =
      fun z => reflectionFoldedMomentGerm T sigma (-z) := by
    funext z
    exact reflectionFoldedMomentGerm_reflection T kappa sigma z hreflect
  rw [hgerm, iteratedDeriv_comp_neg]
  simp

/-- Even folded jets are invariant under reflection of the base point. -/
theorem iteratedDeriv_reflectionFoldedMomentGerm_even_reflection
    (T : ℂ → ℂ) (kappa sigma : ℂ)
    (hreflect : ∀ w, T (kappa - w) = -T w) (n : ℕ) :
    iteratedDeriv (2 * n) (reflectionFoldedMomentGerm T (kappa - sigma)) 0 =
      iteratedDeriv (2 * n) (reflectionFoldedMomentGerm T sigma) 0 := by
  rw [iteratedDeriv_reflectionFoldedMomentGerm_reflection T kappa sigma hreflect]
  have heven : (-1 : ℂ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven, one_mul]

/-- Hankel matrix of the even folded jets at a moving base point. -/
def reflectionFoldedHankelMatrix
    (T : ℂ → ℂ) (n : ℕ) (sigma : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => iteratedDeriv (2 * ((i : ℕ) + (j : ℕ)))
    (reflectionFoldedMomentGerm T sigma) 0

/-- The complete even-jet Hankel matrix is invariant under affine reflection of its base. -/
theorem reflectionFoldedHankelMatrix_reflection
    (T : ℂ → ℂ) (kappa sigma : ℂ)
    (hreflect : ∀ w, T (kappa - w) = -T w) (n : ℕ) :
    reflectionFoldedHankelMatrix T n (kappa - sigma) =
      reflectionFoldedHankelMatrix T n sigma := by
  ext i j
  exact iteratedDeriv_reflectionFoldedMomentGerm_even_reflection
    T kappa sigma hreflect ((i : ℕ) + (j : ℕ))

/-- Every leading even-jet Hankel determinant is reflection invariant. -/
theorem det_reflectionFoldedHankelMatrix_reflection
    (T : ℂ → ℂ) (kappa sigma : ℂ)
    (hreflect : ∀ w, T (kappa - w) = -T w) (n : ℕ) :
    (reflectionFoldedHankelMatrix T n (kappa - sigma)).det =
      (reflectionFoldedHankelMatrix T n sigma).det := by
  rw [reflectionFoldedHankelMatrix_reflection T kappa sigma hreflect]

end

end HTGeometry
