import GaloisForLFunctions.HTGeometry.InitialIdealDegeneration
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AssociatedGradedPresentation

/-!
The source's highest-weight initial ideal agrees, after negating the weights,
with the native lowest-form initial ideal. This connects the exact source
degeneration to the existing corpus interface, including its actual Rees
associated graded algebra.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial StableCoordinate

variable {σ K : Type*} [Field K]

theorem paperWeight_neg (w : σ → ℤ) (m : σ →₀ ℕ) :
    Finsupp.weight (-w) m = -Finsupp.weight w m := by
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem paperWeightedComponent_neg (w : σ → ℤ) (d : ℤ) (p : MvPolynomial σ K) :
    weightedHomogeneousComponent (-w) (-d) p =
      weightedHomogeneousComponent w d p := by
  classical
  ext m
  simp only [coeff_weightedHomogeneousComponent, paperWeight_neg, neg_inj]

theorem paperMinWeight_neg_of_topDegree {w : σ → ℤ} {p : MvPolynomial σ K} {d : ℤ}
    (hp : WeightedInitial.IsTopDegree w p d) : minWeight (-w) p = -d := by
  classical
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hp.2
  rw [coeff_weightedHomogeneousComponent] at hm
  have hmd : Finsupp.weight w m = d := by
    by_contra h
    simp [h] at hm
  have hpm : p.coeff m ≠ 0 := by simpa only [if_pos hmd] using hm
  apply le_antisymm
  · simpa only [paperWeight_neg, hmd] using
      (minWeight_le (w := -w) (mem_support_iff.mpr hpm))
  · apply le_minWeight hp.ne_zero
    intro n hn
    rw [paperWeight_neg]
    have h := hp.1 n (mem_support_iff.mp hn)
    omega

theorem paperLowestForm_neg_of_topDegree {w : σ → ℤ} {p : MvPolynomial σ K} {d : ℤ}
    (hp : WeightedInitial.IsTopDegree w p d) :
    lowestForm (-w) p = weightedHomogeneousComponent w d p := by
  rw [lowestForm, paperMinWeight_neg_of_topDegree hp, paperWeightedComponent_neg]

/-- The two existing initial-ideal conventions agree after reversing weights. -/
theorem paperHighestInitialIdeal_eq_native (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) :
    WeightedInitial.initialIdeal w I = initialIdeal (-w) I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro v ⟨p, hp, d, hd, rfl⟩
    rw [← paperLowestForm_neg_of_topDegree hd]
    exact lowestForm_mem_initialIdeal hp hd.ne_zero
  · intro p hp
    change p ∈ Submodule.span K (initialFormSet (-w) I) at hp
    change p ∈ (WeightedInitial.initialIdeal w I).restrictScalars K
    refine (show Submodule.span K (initialFormSet (-w) I) ≤
        (WeightedInitial.initialIdeal w I).restrictScalars K from ?_) hp
    apply Submodule.span_le.mpr
    rintro v ⟨q, hqI, hq, rfl⟩
    obtain ⟨d, hd, ht⟩ := WeightedInitial.exists_top (w := w) hq
    rw [paperLowestForm_neg_of_topDegree ⟨hd, ht⟩]
    exact Ideal.subset_span ⟨q, hqI, d, ⟨hd, ht⟩, rfl⟩

/-- The literal source relation has the expected initial form in the native convention. -/
theorem paperNativeInitialForm_sourceRelation :
    lowestForm (-Obstruction.presentationWeight) (Obstruction.H ℂ) =
      Obstruction.Hstar ℂ := by
  rw [paperLowestForm_neg_of_topDegree (PrincipalInitialRelation.H_isTopDegree ℂ),
    Obstruction.H_degree_one_component]

/-- The source's exact initial-ideal theorem now applies to the native degeneration API. -/
theorem paperNativeInitialIdeal_sourceRelation :
    initialIdeal (-Obstruction.presentationWeight) (Obstruction.idealA ℂ) =
      Obstruction.idealG ℂ := by
  rw [← paperHighestInitialIdeal_eq_native, PrincipalInitialRelation.initialIdeal_idealA]

/-- None of the five independent source variables is lost in this degeneration. -/
theorem paperNativeInitialIdeal_generator_survives (i : Fin 5) :
    X i ∉ initialIdeal (-Obstruction.presentationWeight) (Obstruction.idealA ℂ) := by
  rw [paperNativeInitialIdeal_sourceRelation]
  intro h
  exact Obstruction.gX_ne_zero ℂ i (Ideal.Quotient.eq_zero_iff_mem.mpr h)

/-- The native initial-ideal quotient is the actual Rees associated graded algebra. -/
def paperNativeInitialQuotientEquiv :
    (Obstruction.P ℂ 5 ⧸
      initialIdeal (-Obstruction.presentationWeight) (Obstruction.idealA ℂ)) ≃ₐ[ℂ]
        AssociatedGradedPresentation.associatedGraded ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ paperNativeInitialIdeal_sourceRelation).trans
    (AssociatedGradedPresentation.associatedGradedEquiv ℂ)

theorem paperNativeInitialQuotientEquiv_mk (p : Obstruction.P ℂ 5) :
    paperNativeInitialQuotientEquiv
      (Ideal.Quotient.mk
        (initialIdeal (-Obstruction.presentationWeight) (Obstruction.idealA ℂ)) p) =
      AssociatedGradedPresentation.gradedPresentationMap ℂ p := rfl

end GaloisForLFunctions.HTGeometry
