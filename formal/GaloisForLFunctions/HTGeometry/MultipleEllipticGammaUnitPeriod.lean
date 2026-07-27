import GaloisForLFunctions.HTGeometry.MeromorphicMultipleEllipticGamma
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFaceHierarchy
import GaloisForLFunctions.HTGeometry.MeromorphicFieldRealization

/-!
# The unit period of the multiple elliptic gamma hierarchy

Every factor of the all-order products depends on the point only through the exponential coordinate
`exp(2 pi i z)`, which is unchanged by the translation `z ↦ z + 1`.  So the entire products, the
meromorphic element, its logarithmic derivative and every face coordinate of the hierarchy are
fixed by the unit translation.

This is the third structural direction the descending face-lifting argument needs: together with two
surviving parameters `tau_q, tau_u` it makes the joint fixed field of the acting group the constants,
by the rank-three nondiscreteness theorem.

* `multipleEllipticGammaCoordinate_add_one`, `..._Product_add_one`;
* **`addTranslationMeroEquiv_one_multipleEllipticGammaMero`**;
* **`addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero`** and
  **`addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero`**.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance multipleEllipticGammaUnitPeriodDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance multipleEllipticGammaUnitPeriodDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Pointwise unit periodicity -/

theorem multipleEllipticGammaCoordinate_add_one (z : ℂ) :
    multipleEllipticGammaCoordinate (z + 1) = multipleEllipticGammaCoordinate z := by
  have h : (2 * (Real.pi : ℂ) * I) * (z + 1) = (2 * (Real.pi : ℂ) * I) * z + 2 * Real.pi * I := by
    ring
  rw [multipleEllipticGammaCoordinate, multipleEllipticGammaCoordinate, h, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

omit [DecidableEq ι] in
theorem multipleEllipticGammaForwardFactor_add_one (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    multipleEllipticGammaForwardFactor τ n (z + 1) =
      multipleEllipticGammaForwardFactor τ n z := by
  rw [multipleEllipticGammaForwardFactor, multipleEllipticGammaForwardFactor,
    multipleEllipticGammaCoordinate_add_one]

omit [DecidableEq ι] in
theorem multipleEllipticGammaBackwardFactor_add_one (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    multipleEllipticGammaBackwardFactor τ n (z + 1) =
      multipleEllipticGammaBackwardFactor τ n z := by
  rw [multipleEllipticGammaBackwardFactor, multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaCoordinate_add_one]

omit [DecidableEq ι] in
theorem multipleEllipticGammaForwardProduct_add_one (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaForwardProduct τ (z + 1) =
      multipleEllipticGammaForwardProduct τ z := by
  rw [multipleEllipticGammaForwardProduct, multipleEllipticGammaForwardProduct]
  exact tprod_congr fun n => multipleEllipticGammaForwardFactor_add_one τ n z

omit [DecidableEq ι] in
theorem multipleEllipticGammaBackwardProduct_add_one (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaBackwardProduct τ (z + 1) =
      multipleEllipticGammaBackwardProduct τ z := by
  rw [multipleEllipticGammaBackwardProduct, multipleEllipticGammaBackwardProduct]
  exact tprod_congr fun n => multipleEllipticGammaBackwardFactor_add_one τ n z

/-! ## Unit periodicity of the germs -/

omit [DecidableEq ι] in
theorem addTranslationAnalyticEquiv_one_multipleEllipticGammaForwardAnalytic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    addTranslationAnalyticEquiv 1 (multipleEllipticGammaForwardAnalytic τ hτ) =
      multipleEllipticGammaForwardAnalytic τ hτ := by
  have hrep : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ))
      (multipleEllipticGammaForwardProduct τ) =
      ((multipleEllipticGammaForwardAnalytic τ hτ : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := rfl
  have h := HTGeometry.addTranslationAnalyticEquiv_rep 1 hrep
  apply Subtype.ext
  rw [← h, ← hrep]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z =>
    multipleEllipticGammaForwardProduct_add_one τ z

omit [DecidableEq ι] in
theorem addTranslationAnalyticEquiv_one_multipleEllipticGammaBackwardAnalytic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    addTranslationAnalyticEquiv 1 (multipleEllipticGammaBackwardAnalytic τ hτ) =
      multipleEllipticGammaBackwardAnalytic τ hτ := by
  have hrep : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ))
      (multipleEllipticGammaBackwardProduct τ) =
      ((multipleEllipticGammaBackwardAnalytic τ hτ : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := rfl
  have h := HTGeometry.addTranslationAnalyticEquiv_rep 1 hrep
  apply Subtype.ext
  rw [← h, ← hrep]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z =>
    multipleEllipticGammaBackwardProduct_add_one τ z

/-! ## Unit periodicity in the meromorphic field -/

omit [DecidableEq ι] in
/-- **The all-order multiple elliptic gamma has the unit period.** -/
theorem addTranslationMeroEquiv_one_multipleEllipticGammaMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    addTranslationMeroEquiv 1 (multipleEllipticGammaMero τ hτ) =
      multipleEllipticGammaMero τ hτ := by
  rw [multipleEllipticGammaMero]
  split
  · rw [map_div₀, addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
      addTranslationAnalyticEquiv_one_multipleEllipticGammaForwardAnalytic,
      addTranslationAnalyticEquiv_one_multipleEllipticGammaBackwardAnalytic]
  · rw [map_mul, addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
      addTranslationAnalyticEquiv_one_multipleEllipticGammaForwardAnalytic,
      addTranslationAnalyticEquiv_one_multipleEllipticGammaBackwardAnalytic]

omit [DecidableEq ι] in
/-- **The logarithmic derivative inherits the unit period.** -/
theorem addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    addTranslationMeroEquiv 1 (multipleEllipticGammaLogDerivMero τ hτ) =
      multipleEllipticGammaLogDerivMero τ hτ := by
  show addTranslationMeroEquiv 1 (Differential.logDeriv (multipleEllipticGammaMero τ hτ)) = _
  rw [Differential.logDeriv, map_div₀, addTranslationMeroEquiv_deriv,
    addTranslationMeroEquiv_one_multipleEllipticGammaMero]
  rfl

/-- **Every face coordinate of the hierarchy has the unit period.** -/
theorem addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    addTranslationMeroEquiv 1 (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      multipleEllipticGammaLogDerivFaceMero τ hτ J :=
  addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero
    (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i)

end

end GaloisForLFunctions
