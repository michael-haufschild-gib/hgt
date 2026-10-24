import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Complexification of real positive kernels

The energy of a complex coefficient packet against a real kernel is the sum of
the energies of its real and imaginary parts. Real packet positivity and
contraction estimates therefore pass to the complex Gram Hilbert space.
-/

noncomputable section
set_option autoImplicit false

open Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*}

/-- Complex packet energy splits into its two real coefficient energies. -/
theorem kernelForm_real_re_eq (K : X → X → ℝ) (c : X →₀ ℂ) :
    (kernelForm (fun x y => (K x y : ℂ)) c c).re =
      (∑ x ∈ c.support, ∑ y ∈ c.support, (c x).re * (c y).re * K x y) +
        ∑ x ∈ c.support, ∑ y ∈ c.support, (c x).im * (c y).im * K x y := by
  classical
  change (∑ y ∈ c.support, ∑ x ∈ c.support,
    conj (c y) * c x * (K x y : ℂ)).re = _
  rw [sum_comm]
  simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun y _ => by ring

/-- A symmetric real kernel positive on real packets is positive on complex packets. -/
theorem isPSDKernel_of_real_packet_nonneg (K : X → X → ℝ)
    (hsym : ∀ x y, K x y = K y x)
    (hpos : ∀ (S : Finset X) (c : X → ℝ),
      0 ≤ ∑ x ∈ S, ∑ y ∈ S, c x * c y * K x y) :
    IsPSDKernel (fun x y => (K x y : ℂ)) := by
  refine ⟨fun x y => ?_, fun c => ?_⟩
  · simp only [Complex.conj_ofReal, hsym x y]
  · change 0 ≤ (kernelForm (fun x y => (K x y : ℂ)) c c).re
    rw [kernelForm_real_re_eq]
    exact add_nonneg (hpos c.support fun x => (c x).re)
      (hpos c.support fun x => (c x).im)

/-- Any real quadratic-form comparison extends to complex coefficient packets. -/
theorem kernelForm_real_re_le {K L : X → X → ℝ} {b : ℝ}
    (h : ∀ (S : Finset X) (c : X → ℝ),
      (∑ x ∈ S, ∑ y ∈ S, c x * c y * L x y) ≤
        b * (∑ x ∈ S, ∑ y ∈ S, c x * c y * K x y)) (c : X →₀ ℂ) :
    (kernelForm (fun x y => (L x y : ℂ)) c c).re ≤
      b * (kernelForm (fun x y => (K x y : ℂ)) c c).re := by
  rw [kernelForm_real_re_eq, kernelForm_real_re_eq, mul_add]
  exact add_le_add (h c.support fun x => (c x).re)
    (h c.support fun x => (c x).im)

end GaloisForLFunctions.HTGeometry
