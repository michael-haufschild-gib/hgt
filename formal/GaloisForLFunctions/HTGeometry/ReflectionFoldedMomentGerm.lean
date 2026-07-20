import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference

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

/-- Analyticity of the source at the base point discharges analyticity of its centered affine
trace at the spectral origin. -/
theorem analyticAt_affineRelativeTrace
    {T : ℂ → ℂ} {sigma : ℂ} (hT : AnalyticAt ℂ T sigma) :
    AnalyticAt ℂ (affineRelativeTrace T sigma) 0 := by
  unfold affineRelativeTrace
  have hinner : AnalyticAt ℂ (fun z : ℂ => sigma + z * Complex.I) 0 := by
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hcomp : AnalyticAt ℂ (fun z : ℂ => T (sigma + z * Complex.I)) 0 :=
    hT.comp_of_eq hinner (by simp)
  exact analyticAt_const.mul (hcomp.sub analyticAt_const)

/-- **Folded-germ/source jet law.**  Every folded germ jet is the next centered affine-trace jet,
with the exact removable-division factor.  This identifies the entries of all folded Hankel
matrices with shifted source jets instead of leaving them as opaque divided-difference jets. -/
theorem iteratedDeriv_reflectionFoldedMomentGerm_eq
    {T : ℂ → ℂ} {sigma : ℂ} (hT : AnalyticAt ℂ T sigma) (n : ℕ) :
    iteratedDeriv n (reflectionFoldedMomentGerm T sigma) 0 =
      -iteratedDeriv (n + 1) (affineRelativeTrace T sigma) 0 / (n + 1 : ℂ) := by
  change iteratedDeriv n (-(dslope (affineRelativeTrace T sigma) 0)) 0 = _
  rw [iteratedDeriv_neg]
  rw [iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div
    (analyticAt_affineRelativeTrace hT) n]
  ring

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
  have h := dslope_neg_comp_neg (affineRelativeTrace T sigma) 0 z
  simpa using congrArg Neg.neg h

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
