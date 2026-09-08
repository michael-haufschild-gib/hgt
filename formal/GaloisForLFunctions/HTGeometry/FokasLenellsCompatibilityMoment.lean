import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseTraceFormula
import GaloisForLFunctions.HTGeometry.FokasLenellsGlobalSmallScattering
import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianSmoothing

/-!
# Auditing the initial-data moment in Proposition 3.8

Equation (3.52) of arXiv:2607.19649 displays twice the integral of
q - i q(x) q(-x) q'(x). Equation (3.53) makes it vanish by invoking the
evolution equation. The following exact Schwartz calculations isolate the
extra compatibility condition: on even data this moment is precisely the
mass. Every scaled normalized Gaussian realizes its scale as the moment.

This audits the displayed integral cancellation. It does not identify the
integral with a Taylor coefficient of the corpus's actual scattering map.
-/

open MeasureTheory Complex Filter Topology
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def compatibilityMoment (q : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, q x-I*q x*q (-x)*deriv (q : ℝ → ℂ) x

def evenInitialPart (q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (1/2 : ℂ) • (q+RHTower.negSchwartz' q)

def oddInitialPart (q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (1/2 : ℂ) • (q-RHTower.negSchwartz' q)

@[simp] theorem evenInitialPart_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    evenInitialPart q x = (q x+q (-x))/2 := by
  simp only [evenInitialPart,_root_.smul_apply,_root_.add_apply,
    RHTower.negSchwartz'_apply,smul_eq_mul]
  ring

@[simp] theorem oddInitialPart_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    oddInitialPart q x = (q x-q (-x))/2 := by
  simp only [oddInitialPart,_root_.smul_apply,_root_.sub_apply,
    RHTower.negSchwartz'_apply,smul_eq_mul]
  ring

theorem evenInitialPart_reflection (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    evenInitialPart q (-x) = evenInitialPart q x := by simp; ring

theorem oddInitialPart_reflection (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    oddInitialPart q (-x) = -oddInitialPart q x := by simp; ring

theorem initialParts_sum (q : SchwartzMap ℝ ℂ) : evenInitialPart q+oddInitialPart q = q := by
  ext x
  simp only [_root_.add_apply,evenInitialPart_apply,oddInitialPart_apply]
  ring

theorem integral_evenInitialPart (q : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, evenInitialPart q x = ∫ x : ℝ, q x := by
  have hr : Integrable (fun x : ℝ => q (-x)) := (RHTower.negSchwartz' q).integrable
  simp only [evenInitialPart_apply]
  rw [integral_div,integral_add q.integrable hr,
    integral_neg_eq_self (q : ℝ → ℂ) volume]
  ring

theorem integral_oddInitialPart (q : SchwartzMap ℝ ℂ) : ∫ x : ℝ, oddInitialPart q x = 0 := by
  have hr : Integrable (fun x : ℝ => q (-x)) := (RHTower.negSchwartz' q).integrable
  simp only [oddInitialPart_apply]
  rw [integral_div,integral_sub q.integrable hr,
    integral_neg_eq_self (q : ℝ → ℂ) volume]
  simp

/-- The cubic total derivative has zero integral, by the existing CCM Schwartz trace lemma. -/
theorem integral_cubic_derivative (q : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (q x)^2*deriv (q : ℝ → ℂ) x = 0 := by
  let g := mulS (mulS q q) q
  have he : (g : ℝ → ℂ) = fun x => (q x)^3 := by
    funext x
    simp only [g,mulS_apply]
    ring
  have hd (x : ℝ) : deriv (g : ℝ → ℂ) x = (3 : ℂ)*((q x)^2*deriv (q : ℝ → ℂ) x) := by
    rw [he]
    convert! ((q.hasDerivAt x).pow 3).deriv using 1
    ring
  have hi := RHTower.integral_deriv_schwartz_eq_zero g
  simp_rw [hd] at hi
  rw [integral_const_mul] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by norm_num)

theorem compatibilityCubic_integrable (q : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => q x*q (-x)*deriv (q : ℝ → ℂ) x) := by
  have hi : Integrable (fun x : ℝ => mulS (mulS q (RHTower.negSchwartz' q)) (SchwartzMap.derivCLM ℂ ℂ q) x) :=
    (mulS (mulS q (RHTower.negSchwartz' q)) (SchwartzMap.derivCLM ℂ ℂ q)).integrable
  simpa only [mulS_apply,RHTower.negSchwartz'_apply,SchwartzMap.derivCLM_apply] using hi

/-- The displayed compatibility moment separates into mass and a convergent cubic integral. -/
theorem compatibilityMoment_eq (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment q = (∫ x : ℝ, q x)-I*(∫ x : ℝ, q x*q (-x)*deriv (q : ℝ → ℂ) x) := by
  have he (x : ℝ) : q x-I*q x*q (-x)*deriv (q : ℝ → ℂ) x =
      q x-I*(q x*q (-x)*deriv (q : ℝ → ℂ) x) := by ring
  unfold compatibilityMoment
  simp_rw [he]
  rw [integral_sub q.integrable ((compatibilityCubic_integrable q).const_mul I),integral_const_mul]

private theorem compatibilityMoment_of_even (q : SchwartzMap ℝ ℂ) (he : ∀ x, q (-x) = q x) :
    compatibilityMoment q = ∫ x : ℝ, q x := by
  rw [compatibilityMoment_eq]
  simp_rw [he,← pow_two]
  rw [integral_cubic_derivative,mul_zero,sub_zero]

/-- On the entire even projection of the initial-data space, compatibility is exactly zero mass. -/
theorem compatibilityMoment_evenInitialPart (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (evenInitialPart q) = ∫ x : ℝ, q x := by
  rw [compatibilityMoment_of_even _ (evenInitialPart_reflection q),integral_evenInitialPart]

theorem compatibilityMoment_evenInitialPart_zero_iff (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (evenInitialPart q) = 0 ↔ (∫ x : ℝ, q x) = 0 := by
  rw [compatibilityMoment_evenInitialPart]

/-- Odd projected data satisfy the displayed compatibility moment automatically. -/
theorem compatibilityMoment_oddInitialPart (q : SchwartzMap ℝ ℂ) :
    compatibilityMoment (oddInitialPart q) = 0 := by
  rw [compatibilityMoment_eq,integral_oddInitialPart]
  have he (x : ℝ) : oddInitialPart q x*oddInitialPart q (-x)*deriv (oddInitialPart q : ℝ → ℂ) x =
      -((oddInitialPart q x)^2*deriv (oddInitialPart q : ℝ → ℂ) x) := by
    rw [oddInitialPart_reflection]
    ring
  simp_rw [he]
  rw [integral_neg,integral_cubic_derivative]
  simp

/-- A positive-width normalized Gaussian, with no external width assumption. -/
def compatibilityGaussian (a : ℝ) : SchwartzMap ℝ ℂ :=
  RiemannGaussian.complexifySchwartz
    (RiemannGaussian.normalizedGaussianSchwartz ⟨Real.exp a,Real.exp_pos a⟩)

theorem compatibilityGaussian_reflection (a x : ℝ) :
    compatibilityGaussian a (-x) = compatibilityGaussian a x := by
  simp only [compatibilityGaussian,RiemannGaussian.complexifySchwartz_apply,
    RiemannGaussian.normalizedGaussianSchwartz_even]

theorem integral_compatibilityGaussian (a : ℝ) : ∫ x : ℝ, compatibilityGaussian a x = 1 := by
  simp only [compatibilityGaussian,RiemannGaussian.complexifySchwartz_apply]
  rw [integral_complex_ofReal,RiemannGaussian.integral_normalizedGaussianSchwartz]
  rfl

/-- Every complex number occurs as the displayed moment of a smooth rapidly decreasing initial datum. -/
theorem compatibilityMoment_scaledGaussian (a : ℝ) (c : ℂ) :
    compatibilityMoment (c • compatibilityGaussian a) = c := by
  have he (x : ℝ) : (c • compatibilityGaussian a) (-x) = (c • compatibilityGaussian a) x := by
    simp only [_root_.smul_apply,compatibilityGaussian_reflection]
  rw [compatibilityMoment_of_even _ he]
  simp only [_root_.smul_apply,smul_eq_mul]
  rw [integral_const_mul,integral_compatibilityGaussian,mul_one]

theorem compatibilityMoment_gaussian (a : ℝ) : compatibilityMoment (compatibilityGaussian a) = 1 := by
  simpa only [one_smul] using compatibilityMoment_scaledGaussian a 1

/-- The same nonzero moment survives the explicit small-data normalization used by the actual scattering construction. -/
theorem compatibilityMoment_globalSmallGaussian (a : ℝ) :
    compatibilityMoment (globalSmallScatteringPotential (compatibilityGaussian a)) =
      (globalScatteringScale (compatibilityGaussian a) : ℂ) :=
  compatibilityMoment_scaledGaussian a _

theorem compatibilityMoment_globalSmallGaussian_ne_zero (a : ℝ) :
    compatibilityMoment (globalSmallScatteringPotential (compatibilityGaussian a)) ≠ 0 := by
  rw [compatibilityMoment_globalSmallGaussian]
  exact_mod_cast ne_of_gt (globalScatteringScale_pos (compatibilityGaussian a))

/-- The integral vanishing step cannot hold for unrestricted Schwartz initial data. -/
theorem compatibilityMoment_not_identically_zero : ¬ ∀ q : SchwartzMap ℝ ℂ, compatibilityMoment q = 0 := by
  intro h
  have hh := h (compatibilityGaussian 0)
  rw [compatibilityMoment_gaussian] at hh
  exact one_ne_zero hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
