import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFieldHierarchy
import GaloisForLFunctions.HTGeometry.MeroFieldShiftStableSpace

/-!
# The terminal multiple elliptic-Gamma face

With no surviving nomes, parity cancels the two elementary factors and the logarithmic derivative
is the constant `-2πi`.  This is the terminal value that makes common-step face descent genuinely
nilpotent.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeComplexAlgebra

local instance multipleEllipticGammaTerminalDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance multipleEllipticGammaTerminalDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- On its regular locus, the zero-nome additive logarithmic kernel is the constant `-2πi`. -/
theorem multipleEllipticGammaAdditiveLogKernel_isEmpty
    {ι : Type} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (τ : ι → ℂ) (z : ℂ) (hz : multipleEllipticGammaCoordinate z ≠ 1) :
    multipleEllipticGammaAdditiveLogKernel τ z =
      -(2 * Real.pi * I) := by
  rw [multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaLogKernel, tsum_fintype]
  let n0 : ι → ℕ := fun i => isEmptyElim i
  have huniv : (Finset.univ : Finset (ι → ℕ)) = {n0} := by
    ext n
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [huniv, Finset.sum_singleton]
  simp [n0, multipleEllipticGammaLogSummand,
    multipleEllipticGammaForwardArgument,
    multipleEllipticGammaBackwardArgument,
    multipleEllipticGammaLogSign, ellipticGammaLogAtom]
  have hx := multipleEllipticGammaCoordinate_ne_zero z
  have h1 : 1 - multipleEllipticGammaCoordinate z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hz)
  have h2 : -1 + multipleEllipticGammaCoordinate z ≠ 0 := by
    intro h
    apply hz
    linear_combination h
  have h3 : multipleEllipticGammaCoordinate z - 1 ≠ 0 :=
    sub_ne_zero.mpr hz
  field_simp [hx, h1, h2]
  field_simp [h3]
  ring

/-- **Terminal-face identity.** The logarithmic derivative of the genuine zero-nome multiple
elliptic Gamma is the embedded constant `-2πi`. -/
theorem multipleEllipticGammaLogDerivMero_isEmpty
    {ι : Type} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivMero τ hτ =
      algebraMap ℂ (meroField (Set.univ : Set ℂ))
        (-(2 * Real.pi * I)) := by
  let N := multipleEllipticGammaLogDerivNumeratorAnalytic τ hτ
  let D := multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ
  have hD : D ≠ 0 :=
    multipleEllipticGammaLogDerivDenominatorAnalytic_ne_zero τ hτ
  have hmapD : algebraMap (analyticSubring Set.univ) (meroField Set.univ) D ≠ 0 :=
    fun hz => hD ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  show multipleEllipticGammaLogDerivMero τ hτ =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ (-(2 * Real.pi * I)))
  rw [multipleEllipticGammaLogDerivMero_eq_div]
  rw [div_eq_iff hmapD, ← map_mul]
  rw [(IsFractionRing.injective (analyticSubring Set.univ)
    (meroField Set.univ)).eq_iff]
  obtain ⟨z₀, hz₀⟩ := exists_univGermEval_ne_zero_of_ne_zero hD
  apply analyticSubring_eq_of_eventually_eval_eq (z₀ := z₀)
  filter_upwards [eventually_univGermEval_ne_zero hz₀] with z hzD
  have hzFB :
      multipleEllipticGammaForwardProduct τ z ≠ 0 ∧
        multipleEllipticGammaBackwardProduct τ z ≠ 0 := by
    dsimp [D] at hzD
    simp only [multipleEllipticGammaLogDerivDenominatorAnalytic,
      univGermEval_analyticSubring_mul,
      univGermEval_multipleEllipticGammaForwardAnalytic,
      univGermEval_multipleEllipticGammaBackwardAnalytic] at hzD
    exact mul_ne_zero_iff.mp hzD
  have hzcoord : multipleEllipticGammaCoordinate z ≠ 1 := by
    intro hz
    apply hzFB.2
    rw [multipleEllipticGammaBackwardProduct, tprod_fintype]
    let n0 : ι → ℕ := fun i => isEmptyElim i
    have huniv : (Finset.univ : Finset (ι → ℕ)) = {n0} := by
      ext n
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    rw [huniv, Finset.prod_singleton]
    simp [n0, multipleEllipticGammaBackwardFactor,
      multipleEllipticGammaBackwardArgument, hz]
  have hk := univGermEval_multipleEllipticGammaLogDeriv_div_eq_additiveKernel
    hτ hzFB.1 hzFB.2
  rw [multipleEllipticGammaAdditiveLogKernel_isEmpty τ z hzcoord] at hk
  have hcross := (div_eq_iff hzD).mp hk
  dsimp [N, D]
  change
    univGermEval z
        (multipleEllipticGammaLogDerivNumeratorAnalytic τ hτ :
          Germ (𝓟 Set.univ) ℂ) =
      (-(2 * Real.pi * I)) *
        univGermEval z
          (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ :
            Germ (𝓟 Set.univ) ℂ)
  exact hcross

/-- Every translation fixes the terminal logarithmic-derivative face. -/
theorem addTranslationMeroEquiv_multipleEllipticGammaLogDerivMero_isEmpty
    {ι : Type} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (β : ℂ) :
    addTranslationMeroEquiv β (multipleEllipticGammaLogDerivMero τ hτ) =
      multipleEllipticGammaLogDerivMero τ hτ := by
  rw [multipleEllipticGammaLogDerivMero_isEmpty τ hτ,
    HTGeometry.addTranslationMeroEquiv_algebraMap_complex_self]

end

end GaloisForLFunctions
