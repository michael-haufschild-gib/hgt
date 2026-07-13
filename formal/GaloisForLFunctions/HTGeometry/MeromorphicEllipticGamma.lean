import GaloisForLFunctions.HTGeometry.EllipticGammaProduct
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect

/-!
# The actual elliptic gamma product in the global meromorphic differential field

The two entire double products are embedded in the analytic germ domain. Their nonvanishing as
functions makes the quotient a nonzero element of the global meromorphic fraction field. Its
quotient-rule logarithmic derivative is the field element corresponding to the additive
elliptic-gamma logarithmic kernel.
-/

open Filter Topology Set Function Complex

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticGammaUnivDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- Entire numerator product as an element of the global analytic germ domain. -/
def ellipticGammaForwardAnalytic (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (ellipticGammaForwardProduct σ τ),
    ⟨_, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      exact differentiable_ellipticGammaForwardProduct hσ hτ, rfl⟩⟩

/-- Entire denominator product as an element of the global analytic germ domain. -/
def ellipticGammaBackwardAnalytic (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (ellipticGammaBackwardProduct σ τ),
    ⟨_, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      exact differentiable_ellipticGammaBackwardProduct hσ hτ, rfl⟩⟩

/-- The numerator analytic germ is nonzero. -/
theorem ellipticGammaForwardAnalytic_ne_zero
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaForwardAnalytic σ τ hσ hτ ≠ 0 := by
  obtain ⟨z, hzF, _⟩ := exists_ellipticGammaProducts_ne_zero hσ hτ
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [ellipticGammaForwardAnalytic, ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ) (ellipticGammaForwardProduct σ τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  exact hzF (eventually_principal.mp hv z (Set.mem_univ z))

/-- The denominator analytic germ is nonzero. -/
theorem ellipticGammaBackwardAnalytic_ne_zero
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaBackwardAnalytic σ τ hσ hτ ≠ 0 := by
  obtain ⟨z, _, hzB⟩ := exists_ellipticGammaProducts_ne_zero hσ hτ
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [ellipticGammaBackwardAnalytic, ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ) (ellipticGammaBackwardProduct σ τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  exact hzB (eventually_principal.mp hv z (Set.mem_univ z))

/-- The actual elliptic-gamma product as a quotient in the global meromorphic field. -/
def ellipticGammaMero (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (ellipticGammaForwardAnalytic σ τ hσ hτ) /
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (ellipticGammaBackwardAnalytic σ τ hσ hτ)

/-- The elliptic-gamma meromorphic-field element is nonzero. -/
theorem ellipticGammaMero_ne_zero
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaMero σ τ hσ hτ ≠ 0 := by
  apply div_ne_zero
  · exact fun hz => ellipticGammaForwardAnalytic_ne_zero σ τ hσ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  · exact fun hz => ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))

/-- Quotient-rule logarithmic derivative of the actual elliptic-gamma field element. -/
def ellipticGammaLogDerivMero (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    meroField (Set.univ : Set ℂ) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  exact Differential.deriv (ellipticGammaMero σ τ hσ hτ) /
    ellipticGammaMero σ τ hσ hτ

/-- Algebraic logarithmic derivative of an entire analytic germ, embedded in the global
meromorphic differential field. -/
def analyticLogDerivMero (a : analyticSubring Set.univ) :
    meroField (Set.univ : Set ℂ) :=
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  Differential.logDeriv
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a)

/-- The elliptic-gamma logarithmic derivative splits as the numerator logarithmic derivative
minus the denominator logarithmic derivative. -/
theorem ellipticGammaLogDerivMero_eq_forward_sub_backward
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaLogDerivMero σ τ hσ hτ =
      analyticLogDerivMero (ellipticGammaForwardAnalytic σ τ hσ hτ) -
        analyticLogDerivMero (ellipticGammaBackwardAnalytic σ τ hσ hτ) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  rw [ellipticGammaLogDerivMero]
  change Differential.logDeriv (ellipticGammaMero σ τ hσ hτ) = _
  rw [ellipticGammaMero]
  apply Differential.logDeriv_div
  · exact fun hz => ellipticGammaForwardAnalytic_ne_zero σ τ hσ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  · exact fun hz => ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))

/-- Translation commutes with the algebraic logarithmic derivative of an embedded entire germ. -/
theorem addTranslationMeroEquiv_analyticLogDerivMero
    (q : ℂ) (a : analyticSubring Set.univ) :
    addTranslationMeroEquiv q (analyticLogDerivMero a) =
      analyticLogDerivMero (addTranslationAnalyticEquiv q a) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  rw [analyticLogDerivMero, analyticLogDerivMero, Differential.logDeriv,
    map_div₀, addTranslationMeroEquiv_deriv]
  simp_rw [addTranslationMeroEquiv_algebraMap]
  rfl

/-- Entire cross numerator representing the elliptic-gamma logarithmic derivative. -/
def ellipticGammaLogDerivNumeratorAnalytic
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) : analyticSubring Set.univ :=
  analyticSubringDeriv isOpen_univ (ellipticGammaForwardAnalytic σ τ hσ hτ) *
      ellipticGammaBackwardAnalytic σ τ hσ hτ -
    ellipticGammaForwardAnalytic σ τ hσ hτ *
      analyticSubringDeriv isOpen_univ (ellipticGammaBackwardAnalytic σ τ hσ hτ)

/-- Entire product denominator representing the elliptic-gamma logarithmic derivative. -/
def ellipticGammaLogDerivDenominatorAnalytic
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) : analyticSubring Set.univ :=
  ellipticGammaForwardAnalytic σ τ hσ hτ *
    ellipticGammaBackwardAnalytic σ τ hσ hτ

/-- The logarithmic-derivative denominator germ is nonzero. -/
theorem ellipticGammaLogDerivDenominatorAnalytic_ne_zero
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ ≠ 0 := by
  exact mul_ne_zero (ellipticGammaForwardAnalytic_ne_zero σ τ hσ hτ)
    (ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ)

/-- Concrete one-fraction presentation of the actual elliptic-gamma logarithmic derivative. -/
theorem ellipticGammaLogDerivMero_eq_div
    (σ τ : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    ellipticGammaLogDerivMero σ τ hσ hτ =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (ellipticGammaLogDerivNumeratorAnalytic σ τ hσ hτ) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  have hmap_ne {a : analyticSubring Set.univ} (ha : a ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a ≠ 0 :=
    fun hz => ha ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hAF := hmap_ne (ellipticGammaForwardAnalytic_ne_zero σ τ hσ hτ)
  have hAB := hmap_ne (ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ)
  rw [ellipticGammaLogDerivMero_eq_forward_sub_backward]
  simp only [analyticLogDerivMero, Differential.logDeriv]
  simp_rw [meroFieldDifferential_algebraMap]
  simp only [ellipticGammaLogDerivNumeratorAnalytic,
    ellipticGammaLogDerivDenominatorAnalytic, map_sub, map_mul]
  field_simp [hAF, hAB]

end

end GaloisForLFunctions
