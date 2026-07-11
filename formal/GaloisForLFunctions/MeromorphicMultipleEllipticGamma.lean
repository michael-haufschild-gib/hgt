import GaloisForLFunctions.MultipleEllipticGammaProduct
import GaloisForLFunctions.MeromorphicEllipticGamma

/-!
# Actual all-order multiple elliptic gamma in the global meromorphic field

The all-order forward and backward entire products are embedded in the analytic germ domain.  Their
parity-dependent product or quotient is a nonzero element of the global meromorphic differential
field, with its genuine quotient-rule logarithmic derivative.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

variable {ι : Type} [Fintype ι]

local instance multipleEllipticGammaUnivDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- Forward entire product in the global analytic germ domain. -/
def multipleEllipticGammaForwardAnalytic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (multipleEllipticGammaForwardProduct τ),
    ⟨_, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      exact differentiable_multipleEllipticGammaForwardProduct hτ, rfl⟩⟩

/-- Backward entire product in the global analytic germ domain. -/
def multipleEllipticGammaBackwardAnalytic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (multipleEllipticGammaBackwardProduct τ),
    ⟨_, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      exact differentiable_multipleEllipticGammaBackwardProduct hτ, rfl⟩⟩

theorem multipleEllipticGammaForwardAnalytic_ne_zero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaForwardAnalytic τ hτ ≠ 0 := by
  obtain ⟨z, hzF, _⟩ := exists_multipleEllipticGammaProducts_ne_zero hτ
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [multipleEllipticGammaForwardAnalytic, ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ) (multipleEllipticGammaForwardProduct τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  exact hzF (eventually_principal.mp hv z (Set.mem_univ z))

theorem multipleEllipticGammaBackwardAnalytic_ne_zero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaBackwardAnalytic τ hτ ≠ 0 := by
  obtain ⟨z, _, hzB⟩ := exists_multipleEllipticGammaProducts_ne_zero hτ
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [multipleEllipticGammaBackwardAnalytic, ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ) (multipleEllipticGammaBackwardProduct τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  exact hzB (eventually_principal.mp hv z (Set.mem_univ z))

/-- Genuine parity-dependent multiple elliptic gamma as a global meromorphic-field element. -/
def multipleEllipticGammaMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : meroField Set.univ :=
  if Even (Fintype.card ι) then
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (multipleEllipticGammaForwardAnalytic τ hτ) /
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (multipleEllipticGammaBackwardAnalytic τ hτ)
  else
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (multipleEllipticGammaForwardAnalytic τ hτ) *
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (multipleEllipticGammaBackwardAnalytic τ hτ)

theorem multipleEllipticGammaMero_ne_zero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaMero τ hτ ≠ 0 := by
  have hmapF : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (multipleEllipticGammaForwardAnalytic τ hτ) ≠ 0 :=
    fun hz => multipleEllipticGammaForwardAnalytic_ne_zero τ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  have hmapB : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (multipleEllipticGammaBackwardAnalytic τ hτ) ≠ 0 :=
    fun hz => multipleEllipticGammaBackwardAnalytic_ne_zero τ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  by_cases hcard : Even (Fintype.card ι)
  · simp only [multipleEllipticGammaMero, hcard, if_true]
    exact div_ne_zero hmapF hmapB
  · simp only [multipleEllipticGammaMero, hcard, if_false]
    exact mul_ne_zero hmapF hmapB

/-- Quotient-rule logarithmic derivative of the actual all-order multiple elliptic gamma. -/
def multipleEllipticGammaLogDerivMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : meroField Set.univ := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  exact Differential.logDeriv (multipleEllipticGammaMero τ hτ)

/-- The field logarithmic derivative splits with the same parity as the genuine product. -/
theorem multipleEllipticGammaLogDerivMero_eq_forward_parity
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivMero τ hτ =
      if Even (Fintype.card ι) then
        analyticLogDerivMero (multipleEllipticGammaForwardAnalytic τ hτ) -
          analyticLogDerivMero (multipleEllipticGammaBackwardAnalytic τ hτ)
      else
        analyticLogDerivMero (multipleEllipticGammaForwardAnalytic τ hτ) +
          analyticLogDerivMero (multipleEllipticGammaBackwardAnalytic τ hτ) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  have hmapF : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (multipleEllipticGammaForwardAnalytic τ hτ) ≠ 0 :=
    fun hz => multipleEllipticGammaForwardAnalytic_ne_zero τ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  have hmapB : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (multipleEllipticGammaBackwardAnalytic τ hτ) ≠ 0 :=
    fun hz => multipleEllipticGammaBackwardAnalytic_ne_zero τ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  by_cases hcard : Even (Fintype.card ι)
  · simp only [multipleEllipticGammaLogDerivMero, multipleEllipticGammaMero,
      hcard, if_true]
    exact Differential.logDeriv_div _ _ hmapF hmapB
  · simp only [multipleEllipticGammaLogDerivMero, multipleEllipticGammaMero,
      hcard, if_false]
    exact Differential.logDeriv_mul _ _ hmapF hmapB

end

end GaloisForLFunctions
