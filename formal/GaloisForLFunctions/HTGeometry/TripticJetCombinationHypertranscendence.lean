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


/-- **A nonzero jet combination is not differentially algebraic**, in the form that admits the base
class of the source itself.  One class of base points — the one carrying the untranslated source —
is not a nonresonant translate; it is the extra element of the translation packet, and its
representative is the point `-(τ/2 + 1/2)`. -/
theorem exists_realizesMero_jetCombination_option {τ σ : ℂ} (hτ : 0 < τ.im)
    (hσ : 0 < σ.im) (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (P₀ : Finset ℂ) (J : ℕ) (c : ℂ → ℕ → ℂ)
    (hnonres : ∀ q ∈ P₀, ThetaTranslationNonresonant σ τ (-(gammaPresentationShift σ) - q))
    (hsep : ∀ q ∈ P₀, ∀ q' ∈ P₀, q ≠ q' → ThetaTranslationNonresonant σ τ (q - q'))
    {q₀ : ℂ} (hq₀ : q₀ ∈ insert (-(gammaPresentationShift σ)) P₀) {j₀ : ℕ} (hj₀ : j₀ < J)
    (hc : c q₀ j₀ ≠ 0) :
    ∃ X : meroField (Set.univ : Set ℂ),
      RealizesMero X (jetCombination τ σ c (insert (-(gammaPresentationShift σ)) P₀) J) ∧
      HypertranscendentalOver ℂ X := by
  classical
  set s : ℂ := gammaPresentationShift σ with hsdef
  have hbase : (-s) ∉ P₀ := by
    intro hmem
    have h := hnonres (-s) hmem
    exact h ⟨0, 0, 0, by push_cast; ring⟩
  set hs : {x // x ∈ P₀} → ℂ := fun q ↦ -s - (q : ℂ) with hhs
  set v : Option {x // x ∈ P₀} → Polynomial ℂ :=
    fun i ↦ i.elim (jetRowPoly c (-s) J) (fun q ↦ jetRowPoly c (q : ℂ) J) with hvdef
  have hvne : v ≠ 0 := by
    intro hzero
    rcases Finset.mem_insert.mp hq₀ with rfl | hq₀'
    · exact jetRowPoly_ne_zero_of_coeff hj₀ hc (congrFun hzero none)
    · exact jetRowPoly_ne_zero_of_coeff hj₀ hc (congrFun hzero (some ⟨q₀, hq₀'⟩))
  have hnonres' : ∀ i, ThetaTranslationNonresonant σ τ (hs i) := fun i ↦ hnonres (i : ℂ) i.2
  have hsep' : ∀ i j : {x // x ∈ P₀}, i ≠ j →
      ThetaTranslationNonresonant σ τ (hs j - hs i) := by
    intro i j hij
    have hval : hs j - hs i = (i : ℂ) - (j : ℂ) := by
      simp only [hhs]
      ring
    rw [hval]
    exact hsep (i : ℂ) i.2 (j : ℂ) j.2 (fun hh ↦ hij (Subtype.ext hh))
  have hHT := hypertranscendentalOver_ellipticGammaTranslateRow_option hτ hσ hperiods hs
    hnonres' hsep' v hvne
  have hrow : ∀ i : Option {x // x ∈ P₀},
      RealizesMero (differentialOperatorApply (v i)
          (ellipticGammaTranslateFamily (optionShift hs) τ σ hτ hσ i))
        (∑ j ∈ Finset.range J, fun z ↦
          c (-(gammaPresentationShift σ + optionShift hs i)) j
            * gammaJetSource τ σ (-(gammaPresentationShift σ + optionShift hs i)) j z) := by
    intro i
    have hpt : -(gammaPresentationShift σ + optionShift hs i)
        = i.elim (-s) (fun q ↦ (q : ℂ)) := by
      rw [← hsdef]
      cases i with
      | none => show -(s + 0) = -s; ring
      | some q => show -(s + (-s - (q : ℂ))) = (q : ℂ); ring
    have hvi : v i = jetRowPoly c (i.elim (-s) (fun q ↦ (q : ℂ))) J := by
      cases i with
      | none => rfl
      | some q => rfl
    rw [hpt, hvi, differentialOperatorApply_jetRowPoly]
    refine realizesMero_sum _ _ _ fun j _ ↦ ?_
    refine realizesMero_const_mul _ ?_
    have h := realizesMero_gammaJetSource hτ hσ (optionShift hs i) j
    rw [hpt] at h
    exact h
  have hsum := realizesMero_sum (Finset.univ : Finset (Option {x // x ∈ P₀}))
    (fun i ↦ differentialOperatorApply (v i)
      (ellipticGammaTranslateFamily (optionShift hs) τ σ hτ hσ i))
    (fun i ↦ ∑ j ∈ Finset.range J, fun z ↦
      c (-(gammaPresentationShift σ + optionShift hs i)) j
        * gammaJetSource τ σ (-(gammaPresentationShift σ + optionShift hs i)) j z)
    fun i _ ↦ hrow i
  have hfun : (∑ i : Option {x // x ∈ P₀}, ∑ j ∈ Finset.range J, fun z ↦
        c (-(gammaPresentationShift σ + optionShift hs i)) j
          * gammaJetSource τ σ (-(gammaPresentationShift σ + optionShift hs i)) j z)
      = jetCombination τ σ c (insert (-(gammaPresentationShift σ)) P₀) J := by
    have hptnone : -(gammaPresentationShift σ + optionShift hs none) = -s := by
      rw [← hsdef]
      show -(s + 0) = -s
      ring
    have hptsome : ∀ q : {x // x ∈ P₀},
        -(gammaPresentationShift σ + optionShift hs (some q)) = (q : ℂ) := by
      intro q
      rw [← hsdef]
      show -(s + (-s - (q : ℂ))) = (q : ℂ)
      ring
    rw [jetCombination]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_insert hbase, Fintype.sum_option]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [hptnone]
    · rw [← Finset.sum_coe_sort P₀
        (fun q ↦ ∑ j ∈ Finset.range J, fun z ↦ c q j * gammaJetSource τ σ q j z)]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hptsome i]
  rw [hfun] at hsum
  exact ⟨_, hsum, hHT⟩

/-- **A nonzero jet combination is not differentially algebraic**, base class included. -/
theorem not_differentiallyAlgebraic_jetCombination_option {τ σ : ℂ} (hτ : 0 < τ.im)
    (hσ : 0 < σ.im) (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (P₀ : Finset ℂ) (J : ℕ) (c : ℂ → ℕ → ℂ)
    (hnonres : ∀ q ∈ P₀, ThetaTranslationNonresonant σ τ (-(gammaPresentationShift σ) - q))
    (hsep : ∀ q ∈ P₀, ∀ q' ∈ P₀, q ≠ q' → ThetaTranslationNonresonant σ τ (q - q'))
    {q₀ : ℂ} (hq₀ : q₀ ∈ insert (-(gammaPresentationShift σ)) P₀) {j₀ : ℕ} (hj₀ : j₀ < J)
    (hc : c q₀ j₀ ≠ 0) :
    ¬ DifferentiallyAlgebraic (toMeromorphicNFOn
        (jetCombination τ σ c (insert (-(gammaPresentationShift σ)) P₀) J)
        (Set.univ : Set ℂ)) := by
  obtain ⟨X, hX, hHT⟩ := exists_realizesMero_jetCombination_option hτ hσ hperiods P₀ J c hnonres
    hsep hq₀ hj₀ hc
  intro hDA
  exact hHT (differentialAlgebraicOver_complex_of_ratFunc
    (differentialAlgebraicOver_of_realizesMero hX hDA))

end

end GaloisForLFunctions.HTGeometry
