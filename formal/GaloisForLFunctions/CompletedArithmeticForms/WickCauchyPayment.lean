import GaloisForLFunctions.CompletedArithmeticForms.GaussianRelativeKernel

/-!+# Mixed Cauchy payment in Gaussian polynomial coordinates

Two independent contour radii control the complete mixed jet of an entire source.
The first-atom application retains the mixed exponential and the quartic source
error, so the radii can be matched separately to the two Hermite degrees.
-/

noncomputable section

open Metric
open scoped ContDiff

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- First-coordinate differentiation before restricting the second coordinate. -/
def firstComplexPartial (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  deriv (fun z => F (z, p.2)) p.1

private theorem firstComplexPartial_eq_fderiv {F : ℂ × ℂ → ℂ}
    (hF : ContDiff ℂ ∞ F) (p : ℂ × ℂ) :
    firstComplexPartial F p = fderiv ℂ F p (1, 0) :=
  ((hF.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem contDiff_firstComplexPartial {F : ℂ × ℂ → ℂ} (hF : ContDiff ℂ ∞ F) :
    ContDiff ℂ ∞ (firstComplexPartial F) := by
  rw [show firstComplexPartial F = fun p => fderiv ℂ F p (1, 0) from
    funext (firstComplexPartial_eq_fderiv hF)]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (hF.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- Arbitrary first-coordinate jet as a joint entire function. -/
def firstComplexJet (F : ℂ × ℂ → ℂ) : ℕ → ℂ × ℂ → ℂ
  | 0 => F
  | n + 1 => firstComplexPartial (firstComplexJet F n)

theorem contDiff_firstComplexJet {F : ℂ × ℂ → ℂ} (hF : ContDiff ℂ ∞ F) (n : ℕ) :
    ContDiff ℂ ∞ (firstComplexJet F n) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact contDiff_firstComplexPartial ih

theorem firstComplexJet_eq_iteratedDeriv (F : ℂ × ℂ → ℂ) (n : ℕ) (p : ℂ × ℂ) :
    firstComplexJet F n p = iteratedDeriv n (fun z => F (z, p.2)) p.1 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    change deriv (fun z => firstComplexJet F n (z, p.2)) p.1 = _
    congr 1
    funext z
    exact ih (z, p.2)

/-- Mixed derivative at the origin, with its two orders kept separate. -/
def mixedKernelJet (F : ℂ × ℂ → ℂ) (i j : ℕ) : ℂ :=
  iteratedDeriv j (fun w => firstComplexJet F i (0, w)) 0

/-- The mixed Gaussian kernel has precisely the Hermite factorial diagonal. -/
theorem mixedKernelJet_gaussian (i j : ℕ) :
    mixedKernelJet (fun p : ℂ × ℂ => Complex.exp (8 * p.1 * p.2)) i j =
      if i = j then (8 : ℂ) ^ i * (i.factorial : ℂ) else 0 := by
  have he : (fun w : ℂ => firstComplexJet
      (fun p : ℂ × ℂ => Complex.exp (8 * p.1 * p.2)) i (0, w)) =
      fun w : ℂ => (8 : ℂ) ^ i * w ^ i := by
    funext w
    rw [firstComplexJet_eq_iteratedDeriv]
    have hs : (fun z : ℂ => Complex.exp (8 * z * w)) =
        fun z : ℂ => Complex.exp ((8 * w) * z) := by
      funext z
      congr 1
      ring
    rw [hs, iteratedDeriv_cexp_const_mul]
    simp only [mul_zero, Complex.exp_zero, mul_one, mul_pow]
  rw [mixedKernelJet, he, _root_.iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  by_cases hij : i = j
  · subst j
    simp
  · simp only [hij, Ne.symm hij, if_false, Nat.cast_zero, mul_zero]

/-- Mixed jets preserve subtraction on their full analytic domain. -/
theorem mixedKernelJet_sub {F G : ℂ × ℂ → ℂ}
    (hF : ContDiff ℂ ∞ F) (hG : ContDiff ℂ ∞ G) (i j : ℕ) :
    mixedKernelJet (fun p => F p - G p) i j =
      mixedKernelJet F i j - mixedKernelJet G i j := by
  have hfirst : (fun w : ℂ => firstComplexJet (fun p => F p - G p) i (0, w)) =
      fun w : ℂ => firstComplexJet F i (0, w) - firstComplexJet G i (0, w) := by
    funext w
    simp only [firstComplexJet_eq_iteratedDeriv]
    have hf : Differentiable ℂ (fun z : ℂ => F (z, w)) :=
      (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    have hg : Differentiable ℂ (fun z : ℂ => G (z, w)) :=
      (hG.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    exact iteratedDeriv_fun_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt
  have hf : Differentiable ℂ (fun w : ℂ => firstComplexJet F i (0, w)) :=
    ((contDiff_firstComplexJet hF i).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hg : Differentiable ℂ (fun w : ℂ => firstComplexJet G i (0, w)) :=
    ((contDiff_firstComplexJet hG i).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  unfold mixedKernelJet
  rw [hfirst]
  exact iteratedDeriv_fun_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt

/-- Independent radii pay exactly one factorial and one contour power per coordinate. -/
theorem norm_mixedKernelJet_le {F : ℂ × ℂ → ℂ} (hF : ContDiff ℂ ∞ F)
    {r s M : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hM : ∀ z ∈ sphere (0 : ℂ) r, ∀ w ∈ sphere (0 : ℂ) s, ‖F (z, w)‖ ≤ M)
    (i j : ℕ) :
    ‖mixedKernelJet F i j‖ ≤ (i.factorial : ℝ) * (j.factorial : ℝ) * M /
      (r ^ i * s ^ j) := by
  have hg : ContDiff ℂ ∞ (fun w : ℂ => firstComplexJet F i (0, w)) :=
    (contDiff_firstComplexJet hF i).comp (contDiff_const.prodMk contDiff_id)
  have hbound : ∀ w ∈ sphere (0 : ℂ) s,
      ‖firstComplexJet F i (0, w)‖ ≤ (i.factorial : ℝ) * M / r ^ i := by
    intro w hw
    rw [firstComplexJet_eq_iteratedDeriv]
    have hf : ContDiff ℂ ∞ (fun z : ℂ => F (z, w)) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hr
      (hf.differentiable (by simp)).diffContOnCl (fun z hz => hM z hz w hw)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hs
    (hg.differentiable (by simp)).diffContOnCl hbound
  change ‖mixedKernelJet F i j‖ ≤ _ at h
  calc
    _ ≤ (j.factorial : ℝ) * ((i.factorial : ℝ) * M / r ^ i) / s ^ j := h
    _ = _ := by ring

/-- Literal first-atom error in the joint Gaussian polynomial kernel. -/
def firstAtomWickError (x : ℝ) (p : ℂ × ℂ) : ℂ :=
  firstAtomWickKernel x p.1 p.2 - Complex.exp (8 * p.1 * p.2)

theorem contDiff_firstAtomWickError (x : ℝ) : ContDiff ℂ ∞ (firstAtomWickError x) := by
  have hf : ContDiff ℂ ∞ (firstAtomNormalizedRotatedPair x) :=
    (firstAtomNormalizedRotatedPair_entire x).contDiff
  unfold firstAtomWickError firstAtomWickKernel
  fun_prop

/-- Every mixed first-atom jet has a factored bound on separately chosen contours. -/
theorem firstAtomWickError_mixed_jet_le {x r s R : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hR : 1 ≤ R) (hrs : r + s ≤ R) (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hRq : 4 * R ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hR4q : R ^ 4 ≤ thetaCuspSingleAtomReflectionScale 1 x) (i j : ℕ) :
    ‖mixedKernelJet (firstAtomWickError x) i j‖ ≤
      (i.factorial : ℝ) * (j.factorial : ℝ) *
        (gaussianRelativeErrorConstant * R ^ 4 /
          thetaCuspSingleAtomReflectionScale 1 x * Real.exp (8 * r * s)) /
        (r ^ i * s ^ j) := by
  apply norm_mixedKernelJet_le (contDiff_firstAtomWickError x) hr hs
  intro z hz w hw
  have hzn : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hwn : ‖w‖ = s := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
  have hzw : ‖z + w‖ ≤ R := by
    apply (norm_add_le z w).trans
    simpa only [hzn, hwn] using hrs
  simpa only [firstAtomWickError, hzn, hwn] using
    firstAtomWickKernel_error_le hq hR hRq hR4q hzw

#print axioms norm_mixedKernelJet_le
#print axioms mixedKernelJet_gaussian
#print axioms mixedKernelJet_sub
#print axioms firstAtomWickError_mixed_jet_le

end GaloisForLFunctions.CompletedArithmeticForms
