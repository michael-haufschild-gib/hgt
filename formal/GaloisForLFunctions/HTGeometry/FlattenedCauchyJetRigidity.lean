import GaloisForLFunctions.HTGeometry.SignedCauchyJetDetection
import GaloisForLFunctions.HTGeometry.RealFunctionalJetCoefficients

/-!
# Cauchy-jet rigidity in flattened index form

The Cauchy-jet detectors are stated with a dependent coefficient packet `(i : ι) → Fin (n i) → ℂ`,
one block per node.  A control map into a jet space instead lands in a plain function space on the
flattened index `Σ i, Fin (n i)`.

This module reconciles the two.  The pairing of a flattened coefficient vector with the kernel
vector is the dependent Cauchy-jet form of its curried packet, so coefficient rigidity transfers
verbatim.  The flattened statement is exactly the hypothesis consumed by
`surjective_of_forall_coefficients_eq_zero`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The flattened jet index: one coordinate per node and jet order. -/
abbrev jetIndex (n : ι → ℕ) : Type _ := Σ i : ι, Fin (n i)

/-- The Cauchy kernel vector at a real point, in flattened index form. -/
def cauchyJetKernel (x : ι → ℂ) (n : ι → ℕ) (t : ℝ) : jetIndex n → ℂ :=
  fun s => (((t : ℝ) : ℂ) - x s.1)⁻¹ ^ (s.2.1 + 1)

omit [DecidableEq ι] in
/-- Pairing a flattened coefficient vector with the kernel vector is the dependent jet form of the
curried packet. -/
theorem sum_cauchyJetKernel_eq_cauchyJetForm
    (x : ι → ℂ) (n : ι → ℕ) (c : jetIndex n → ℂ) (t : ℝ) :
    ∑ s : jetIndex n, c s * cauchyJetKernel x n t s =
      cauchyJetForm x n (fun i j => c ⟨i, j⟩) t := by
  rw [cauchyJetForm, Fintype.sum_sigma]
  rfl

/-- **Flattened coefficient rigidity.**  If every set integral of the flattened kernel pairing has
vanishing real part, the flattened coefficient vector is zero. -/
theorem flattened_coeff_eq_zero_of_forall_setIntegral_re_eq_zero
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (c : jetIndex n → ℂ)
    (hpair : ∀ S : Set ℝ, MeasurableSet S →
      (∫ t in S, (∑ s : jetIndex n, c s * cauchyJetKernel x n t s) ∂μ).re = 0) :
    ∀ s : jetIndex n, c s = 0 := by
  have hcurried : ∀ i j, (fun i j => c ⟨i, j⟩) i j = 0 := by
    apply cauchyJet_coeff_eq_zero_of_forall_setIntegral_re_eq_zero hsupp x hx hupper n
    intro S hS
    have hrw : ∀ t : ℝ, cauchyJetForm x n (fun i j => c ⟨i, j⟩) t =
        ∑ s : jetIndex n, c s * cauchyJetKernel x n t s :=
      fun t => (sum_cauchyJetKernel_eq_cauchyJetForm x n c t).symm
    simp only [hrw]
    exact hpair S hS
  intro s
  exact hcurried s.1 s.2

/-- **Surjectivity of a controllable jet map.**  A real-linear map into the flattened jet space
whose pairings are kernel integrals against a measure of infinite support is surjective.  This is
the exact form the Baire pullback consumes. -/
theorem surjective_of_setIntegral_pairing
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (L : X →ₗ[ℝ] (jetIndex n → ℂ))
    (hrepr : ∀ (c : jetIndex n → ℂ),
      (∀ u : X, (∑ s, c s * L u s).re = 0) →
        ∀ S : Set ℝ, MeasurableSet S →
          (∫ t in S, (∑ s : jetIndex n, c s * cauchyJetKernel x n t s) ∂μ).re = 0) :
    Function.Surjective L := by
  classical
  apply surjective_of_forall_coefficients_eq_zero L
  intro c hc
  exact flattened_coeff_eq_zero_of_forall_setIntegral_re_eq_zero hsupp x hx hupper n c
    (hrepr c hc)

end

end GaloisForLFunctions.HTGeometry
