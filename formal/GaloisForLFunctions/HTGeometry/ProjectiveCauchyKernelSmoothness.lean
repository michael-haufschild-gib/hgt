import GaloisForLFunctions.HTGeometry.ProjectiveCauchyKernelContinuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.ContinuousMap.Units

/-!
# Smoothness of the projective Cauchy kernel in its pole

Continuity is not enough for parametric transversality.  This module realizes the projective
resolvent as a rational expression in the Banach algebra `C(OnePoint ℝ, ℂ)`.  A fixed Cayley
coordinate removes the apparent singularity at projective infinity.  Banach-algebra inversion is
smooth on the unit group, so the actual projective resolvent—and all of its positive powers—varies
smoothly with an upper-half-plane pole in the sup norm.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open scoped OnePoint

noncomputable section

/-- The continuous complex-linear embedding of scalars as constant functions on the projective
real line. -/
def projectiveContinuousMapConstCLM :
    ℂ →L[ℂ] C(OnePoint ℝ, ℂ) :=
  (Algebra.linearMap ℂ C(OnePoint ℝ, ℂ)).mkContinuous 1 (fun x => by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg x)).2
    intro t
    simp)

@[simp]
theorem projectiveContinuousMapConstCLM_apply (x : ℂ) (t : OnePoint ℝ) :
    projectiveContinuousMapConstCLM x t = x := by
  rfl

/-- The real Cayley coordinate `(t-i)/(t+i)`, continuously completed by the value `1` at
infinity. -/
def projectiveCayleyContinuousMap : C(OnePoint ℝ, ℂ) :=
  ⟨fun t => 1 - 2 * Complex.I * projectiveCauchyPower (-Complex.I) 0 t,
    continuous_const.sub
      (continuous_const.mul
        (continuous_projectiveCauchyPower (-Complex.I) (by norm_num) 0))⟩

@[simp]
theorem projectiveCayleyContinuousMap_infty :
    projectiveCayleyContinuousMap ∞ = 1 := by
  simp [projectiveCayleyContinuousMap]

@[simp]
theorem projectiveCayleyContinuousMap_coe (t : ℝ) :
    projectiveCayleyContinuousMap (t : OnePoint ℝ) =
      1 - 2 * Complex.I * ((t : ℂ) + Complex.I)⁻¹ := by
  simp [projectiveCayleyContinuousMap]

/-- Cayley denominator for the projective resolvent. -/
def projectiveResolventBanachDenominator (x : ℂ) : C(OnePoint ℝ, ℂ) :=
  projectiveContinuousMapConstCLM (Complex.I - x) +
    projectiveContinuousMapConstCLM (Complex.I + x) * projectiveCayleyContinuousMap

/-- The Cayley denominator is a unit exactly where needed: every upper-half-plane pole. -/
theorem projectiveResolventBanachDenominator_isUnit
    (x : ℂ) (hx : 0 < x.im) :
    IsUnit (projectiveResolventBanachDenominator x) := by
  rw [ContinuousMap.isUnit_iff_forall_ne_zero]
  intro t
  cases t with
  | infty =>
      simp [projectiveResolventBanachDenominator]
  | coe t =>
      have htI : (t : ℂ) + Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        norm_num at hi
      have htx : (t : ℂ) - x ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
        linarith
      have hformula :
          projectiveResolventBanachDenominator x (t : OnePoint ℝ) =
            2 * Complex.I * (((t : ℂ) - x) / ((t : ℂ) + Complex.I)) := by
        simp only [projectiveResolventBanachDenominator, ContinuousMap.add_apply,
          ContinuousMap.mul_apply, projectiveContinuousMapConstCLM_apply,
          projectiveCayleyContinuousMap_coe]
        field_simp [htI]
        ring
      rw [hformula]
      exact mul_ne_zero (by norm_num [Complex.ext_iff]) (div_ne_zero htx htI)

/-- Banach-algebra realization of the projective resolvent.  `Ring.inverse` is a total operation;
on the upper half-plane the preceding theorem proves that it is the genuine inverse. -/
def projectiveResolventBanach (x : ℂ) : C(OnePoint ℝ, ℂ) :=
  (1 - projectiveCayleyContinuousMap) *
    Ring.inverse (projectiveResolventBanachDenominator x)

/-- On the upper half-plane, the Banach-algebra formula is the literal projective resolvent. -/
theorem projectiveResolventBanach_apply
    (x : ℂ) (hx : 0 < x.im) (t : OnePoint ℝ) :
    projectiveResolventBanach x t = projectiveCauchyPower x 0 t := by
  have hunit := projectiveResolventBanachDenominator_isUnit x hx
  have hden : projectiveResolventBanachDenominator x t ≠ 0 :=
    (ContinuousMap.isUnit_iff_forall_ne_zero
      (projectiveResolventBanachDenominator x)).mp hunit t
  have hinverse :
      Ring.inverse (projectiveResolventBanachDenominator x) t =
        (projectiveResolventBanachDenominator x t)⁻¹ := by
    have hmul := congrArg (fun f : C(OnePoint ℝ, ℂ) => f t)
      (Ring.inverse_mul_cancel (projectiveResolventBanachDenominator x) hunit)
    change Ring.inverse (projectiveResolventBanachDenominator x) t *
      projectiveResolventBanachDenominator x t = 1 at hmul
    exact eq_inv_of_mul_eq_one_left hmul
  cases t with
  | infty =>
      simp [projectiveResolventBanach]
  | coe t =>
      have htI : (t : ℂ) + Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        norm_num at hi
      have htx : (t : ℂ) - x ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
        linarith
      have hformula :
          projectiveResolventBanachDenominator x (t : OnePoint ℝ) =
            2 * Complex.I * (((t : ℂ) - x) / ((t : ℂ) + Complex.I)) := by
        simp only [projectiveResolventBanachDenominator, ContinuousMap.add_apply,
          ContinuousMap.mul_apply, projectiveContinuousMapConstCLM_apply,
          projectiveCayleyContinuousMap_coe]
        field_simp [htI]
        ring
      simp only [projectiveResolventBanach, ContinuousMap.mul_apply,
        ContinuousMap.sub_apply, ContinuousMap.one_apply, hinverse,
        projectiveCayleyContinuousMap_coe, projectiveCauchyPower_coe,
        Nat.zero_add, pow_one, hformula]
      field_simp [htI, htx]
      ring

/-- The Cayley denominator depends smoothly (over the reals) on its complex pole. -/
theorem contDiff_projectiveResolventBanachDenominator :
    ContDiff ℝ ⊤ projectiveResolventBanachDenominator := by
  let C : ℂ →L[ℝ] C(OnePoint ℝ, ℂ) :=
    projectiveContinuousMapConstCLM.restrictScalars ℝ
  have hminus : ContDiff ℝ ⊤ (fun x : ℂ => C (Complex.I - x)) :=
    C.contDiff.comp (contDiff_const.sub contDiff_id)
  have hplus : ContDiff ℝ ⊤ (fun x : ℂ => C (Complex.I + x)) :=
    C.contDiff.comp (contDiff_const.add contDiff_id)
  simpa only [projectiveResolventBanachDenominator, C] using!
    hminus.add (hplus.mul contDiff_const)

/-- Banach-algebra inversion of the denominator is smooth on the open upper half-plane. -/
theorem contDiffOn_projectiveResolventBanachDenominator_inverse :
    ContDiffOn ℝ ⊤
      (fun x : ℂ => Ring.inverse (projectiveResolventBanachDenominator x))
      {x | 0 < x.im} := by
  intro x hx
  have hunit := projectiveResolventBanachDenominator_isUnit x hx
  let u : C(OnePoint ℝ, ℂ)ˣ := hunit.unit
  have hu : (u : C(OnePoint ℝ, ℂ)) = projectiveResolventBanachDenominator x :=
    hunit.unit_spec
  have hinv : ContDiffAt ℝ ⊤ Ring.inverse
      (projectiveResolventBanachDenominator x) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hinv.comp_contDiffWithinAt x
    contDiff_projectiveResolventBanachDenominator.contDiffWithinAt

/-- The actual projective resolvent is a smooth sup-norm family on the upper half-plane. -/
theorem contDiffOn_projectiveResolventBanach :
    ContDiffOn ℝ ⊤ projectiveResolventBanach {x : ℂ | 0 < x.im} := by
  exact contDiffOn_const.mul
    contDiffOn_projectiveResolventBanachDenominator_inverse

/-- Every positive projective Cauchy power is a smooth sup-norm family of its upper-half-plane
pole. -/
theorem contDiffOn_projectiveCauchyPowerBanach (k : ℕ) :
    ContDiffOn ℝ ⊤
      (fun x : ℂ => (projectiveResolventBanach x) ^ (k + 1))
      {x | 0 < x.im} :=
  contDiffOn_projectiveResolventBanach.pow (k + 1)

end

end GaloisForLFunctions.HTGeometry
