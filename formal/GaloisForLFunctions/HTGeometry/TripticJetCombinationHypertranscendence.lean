import GaloisForLFunctions.HTGeometry.EllipticGammaJetRealization
import GaloisForLFunctions.HTGeometry.TripticJetRowFreeness
import GaloisForLFunctions.HTGeometry.TripticGammaCorrection
import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase

/-!
# A nonzero jet combination is hypertranscendental

The weights of a jet combination assemble into one constant-coefficient differential-operator row
for each base point.  Applied to the translation packet of the elliptic gamma source those rows
produce a hypertranscendental germ whenever they are not all zero, and the jet combination realizes
exactly that germ.  Since the rational coordinate is a differentially algebraic extension of the
constants, the function cannot satisfy an algebraic differential equation either.

* `jetRowPoly`, `differentialOperatorApply_jetRowPoly`;
* `not_differentiallyAlgebraic_jetCombination`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase relativeGaugeCharZero

/-- The differential-operator row a weight family attaches to a base point. -/
def jetRowPoly (c : ℂ → ℕ → ℂ) (q : ℂ) (J : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range J, Polynomial.monomial j (c q j)

theorem differentialOperatorApply_finsetSum {ι : Type*} (s : Finset ι) (Pl : ι → Polynomial ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    differentialOperatorApply (∑ i ∈ s, Pl i) y = ∑ i ∈ s, differentialOperatorApply (Pl i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, differentialOperatorApply_add, ih]

theorem differentialOperatorApply_jetRowPoly (c : ℂ → ℕ → ℂ) (q : ℂ) (J : ℕ)
    (y : meroField (Set.univ : Set ℂ)) :
    differentialOperatorApply (jetRowPoly c q J) y
      = ∑ j ∈ Finset.range J,
          algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c q j) * differentialJet j y := by
  simp only [jetRowPoly]
  rw [differentialOperatorApply_finsetSum]
  exact Finset.sum_congr rfl fun j _ ↦ differentialOperatorApply_monomial j (c q j) y

theorem jetRowPoly_ne_zero_of_coeff {c : ℂ → ℕ → ℂ} {q : ℂ} {J j : ℕ} (hj : j < J)
    (h : c q j ≠ 0) : jetRowPoly c q J ≠ 0 := by
  intro hzero
  apply h
  have hcoeff := congrArg (fun p : Polynomial ℂ ↦ p.coeff j) hzero
  simpa [jetRowPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.mem_range.mpr hj] using hcoeff

/-- **A nonzero jet combination is not differentially algebraic.** -/
theorem not_differentiallyAlgebraic_jetCombination {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (P : Finset ℂ) (J : ℕ) (c : ℂ → ℕ → ℂ)
    (hnonres : ∀ q ∈ P, ThetaTranslationNonresonant σ τ (-(gammaPresentationShift σ) - q))
    (hsep : ∀ q ∈ P, ∀ q' ∈ P, q ≠ q' → ThetaTranslationNonresonant σ τ (q - q'))
    {q₀ : ℂ} (hq₀ : q₀ ∈ P) {j₀ : ℕ} (hj₀ : j₀ < J) (hc : c q₀ j₀ ≠ 0) :
    ¬ DifferentiallyAlgebraic
        (toMeromorphicNFOn (jetCombination τ σ c P J) (Set.univ : Set ℂ)) := by
  classical
  set hs : {x // x ∈ P} → ℂ := fun q ↦ -(gammaPresentationShift σ) - (q : ℂ) with hhs
  set v : {x // x ∈ P} → Polynomial ℂ := fun q ↦ jetRowPoly c (q : ℂ) J with hvdef
  have hvne : v ≠ 0 := by
    intro hzero
    exact jetRowPoly_ne_zero_of_coeff hj₀ hc (congrFun hzero ⟨q₀, hq₀⟩)
  have hnonres' : ∀ i, ThetaTranslationNonresonant σ τ (hs i) := fun i ↦ hnonres (i : ℂ) i.2
  have hsep' : ∀ i j : {x // x ∈ P}, i ≠ j →
      ThetaTranslationNonresonant σ τ (hs j - hs i) := by
    intro i j hij
    have hval : hs j - hs i = (i : ℂ) - (j : ℂ) := by
      simp only [hhs]
      ring
    rw [hval]
    exact hsep (i : ℂ) i.2 (j : ℂ) j.2 (fun hh ↦ hij (Subtype.ext hh))
  have hHT := hypertranscendentalOver_ellipticGammaTranslateRow hτ hσ hperiods hs hnonres' hsep'
    v hvne
  -- the jet combination realizes the operator row
  have hreal : RealizesMero
      (∑ i, differentialOperatorApply (v i) (ellipticGammaTranslateFamily hs τ σ hτ hσ i))
      (jetCombination τ σ c P J) := by
    have hrow : ∀ i : {x // x ∈ P},
        RealizesMero (differentialOperatorApply (v i)
            (ellipticGammaTranslateFamily hs τ σ hτ hσ i))
          (∑ j ∈ Finset.range J, fun z ↦ c (i : ℂ) j * gammaJetSource τ σ (i : ℂ) j z) := by
      intro i
      simp only [hvdef]
      rw [differentialOperatorApply_jetRowPoly]
      refine realizesMero_sum _ _ _ fun j _ ↦ ?_
      have hbase : RealizesMero
          (differentialJet j (ellipticGammaTranslateFamily hs τ σ hτ hσ i))
          (gammaJetSource τ σ (i : ℂ) j) := by
        have h := realizesMero_gammaJetSource hτ hσ (hs i) j
        have hpt : -(gammaPresentationShift σ + hs i) = (i : ℂ) := by
          simp only [hhs]
          ring
        rw [hpt] at h
        exact h
      exact realizesMero_const_mul _ hbase
    have hsum := realizesMero_sum (Finset.univ : Finset {x // x ∈ P})
      (fun i ↦ differentialOperatorApply (v i) (ellipticGammaTranslateFamily hs τ σ hτ hσ i))
      (fun i ↦ ∑ j ∈ Finset.range J, fun z ↦ c (i : ℂ) j * gammaJetSource τ σ (i : ℂ) j z)
      fun i _ ↦ hrow i
    have hfun : (∑ i : {x // x ∈ P},
          ∑ j ∈ Finset.range J, fun z ↦ c (i : ℂ) j * gammaJetSource τ σ (i : ℂ) j z)
        = jetCombination τ σ c P J := by
      rw [jetCombination]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_coe_sort P
        (fun q ↦ ∑ j ∈ Finset.range J, fun z ↦ c q j * gammaJetSource τ σ q j z)
    rw [hfun] at hsum
    exact hsum
  intro hDA
  exact hHT (differentialAlgebraicOver_complex_of_ratFunc
    (differentialAlgebraicOver_of_realizesMero hreal hDA))

end

end GaloisForLFunctions.HTGeometry
