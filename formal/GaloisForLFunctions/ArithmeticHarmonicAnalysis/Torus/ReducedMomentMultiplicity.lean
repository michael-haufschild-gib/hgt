import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LinearMomentQuotient
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.BoundedWeightMultiplicity

/-!
# Exact cut multiplicities after moment-map reduction

For `N` paired variables and a linear relation space `L` of rank `r`, the
weight-`q` image in the moment quotient has bounded cut multiplicity
`choose (N-r+D-S(q)) (D-S(q))` when `D ≥ S(q)`, and zero below the slack.
Its first admissible component is always one-dimensional.

These are dimensions of actual images in the polynomial quotient. The proof
first removes the minimal weight monomial, then transports the bounded-degree
space through the linear moment quotient. Counting the surviving monomial
basis gives the algebraic multiplicity mechanism of Brown's Theorem 6.1,
*Equivariant Quantisation of Hypertoric Varieties via Symplectic Cuts*.

For the explicit diagonal equation `∑ zᵢwᵢ = 0`, one neutral coordinate is
removed. With two variable pairs the multiplicity is `D-S(q)+1` above the cut.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Removing and reinserting the forced weight exponents recovers every monomial. -/
theorem normalWeightExponent_neutral (d : (ι ⊕ ι) →₀ ℕ) :
    normalWeightExponent (pairedWeight d) (neutralExponent d) = d := by
  ext (i | i)
  · simp only [normalWeightExponent_inl, neutralExponent_apply, pairedWeight]
    omega
  · simp only [normalWeightExponent_inr, neutralExponent_apply, pairedWeight]
    omega

/-- The bounded polynomial weight space, mapped into the actual neutral-relation quotient. -/
def reducedBoundedPairedWeightSpace (q : ι → ℤ) (J : Ideal (MvPolynomial ι K)) (D : ℕ) :
    Submodule K (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  (boundedPairedWeightSpace K q D).map
    (Ideal.Quotient.mkₐ K (J.map (invariantSubstitution K))).toLinearMap

/-- Removing the minimal monomial shifts the cut bound by exactly the weight slack. -/
theorem reducedBoundedPairedWeightSpace_at_slack (q : ι → ℤ)
    (J : Ideal (MvPolynomial ι K)) (D : ℕ) :
    reducedBoundedPairedWeightSpace K q J (weightSlack q + D) =
      (restrictTotalDegree ι K D).map (pairedWeightQuotientMap K q J) := by
  rw [reducedBoundedPairedWeightSpace, boundedPairedWeightSpace,
    restrictTotalDegree, restrictSupport_eq_span, restrictSupport_eq_span,
    Submodule.map_span, Submodule.map_span, Set.image_image, Set.image_image]
  apply congrArg (Submodule.span K)
  ext P
  constructor
  · rintro ⟨d, ⟨hw, hd⟩, rfl⟩
    refine ⟨neutralExponent d, ?_, ?_⟩
    · change (neutralExponent d).sum (fun _ n => n) ≤ D
      have he := normalWeightExponent_neutral d
      rw [hw] at he
      rw [← he, cutDegree_normalWeightExponent] at hd
      rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
      omega
    · change pairedWeightQuotientMap K q J (monomial (neutralExponent d) 1) = _
      change Ideal.Quotient.mk _ (pairedWeightSpaceEquiv K q _).1 = _
      rw [pairedWeightSpaceEquiv_monomial, ← hw, normalWeightExponent_neutral]
      rfl
  · rintro ⟨s, hs, rfl⟩
    refine ⟨normalWeightExponent q s, ⟨pairedWeight_normal q s, ?_⟩, ?_⟩
    · rw [cutDegree_normalWeightExponent]
      apply Nat.add_le_add_left
      change s.sum (fun _ n => n) ≤ D at hs
      rwa [Finsupp.sum_fintype _ _ (by intro i; rfl)] at hs
    · change _ = Ideal.Quotient.mk _ (pairedWeightSpaceEquiv K q _).1
      rw [pairedWeightSpaceEquiv_monomial]
      rfl

/-- Bounded-degree polynomials on a finite variable set have the stars-and-bars dimension. -/
theorem finrank_restrictTotalDegree (D : ℕ) :
    Module.finrank K (restrictTotalDegree ι K D) = (Fintype.card ι + D).choose D := by
  let e : {s : ι →₀ ℕ // s.sum (fun _ n => n) ≤ D} ≃
      {s : ι → ℕ // ∑ i, s i ≤ D} := {
    toFun := fun s => ⟨s.1, by
      have hs := s.2
      rwa [Finsupp.sum_fintype _ _ (by intro i; rfl)] at hs⟩
    invFun := fun s => ⟨Finsupp.equivFunOnFinite.symm s.1, by
      rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
      simpa using s.2⟩
    left_inv := fun s => by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply s.1
    right_inv := fun s => by apply Subtype.ext; exact Finsupp.equivFunOnFinite.apply_symm_apply s.1 }
  change Module.finrank K (restrictSupport K {s : ι →₀ ℕ | s.sum (fun _ n => n) ≤ D}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {s : ι →₀ ℕ // s.sum (fun _ n => n) ≤ D} = _
  rw [Nat.card_congr e, card_bounded_compositions]

/-- Embed surviving neutral coordinates into a reduced weight component. -/
def momentWeightCoordinateEmbedding (q : ι → ℤ) (L : Submodule K (ι → K)) :
    MvPolynomial (Fin (Module.finrank K ((ι → K) ⧸ L))) K →ₗ[K]
      (MvPolynomial (ι ⊕ ι) K ⧸ (momentLinearIdeal K L).map (invariantSubstitution K)) :=
  (reducedPairedWeightSpace K q (momentLinearIdeal K L)).subtype.comp
    (reducedMomentWeightEquiv K q L).toLinearMap

theorem momentWeightCoordinateEmbedding_injective (q : ι → ℤ)
    (L : Submodule K (ι → K)) :
    Function.Injective (momentWeightCoordinateEmbedding K q L) :=
  Subtype.val_injective.comp (reducedMomentWeightEquiv K q L).injective

/-- Polynomial coordinates factor the actual quotient normal-form map. -/
theorem momentWeightCoordinateEmbedding_map (q : ι → ℤ)
    (L : Submodule K (ι → K)) (f : MvPolynomial ι K) :
    momentWeightCoordinateEmbedding K q L (momentCoordinateMap K L f) =
      pairedWeightQuotientMap K q (momentLinearIdeal K L) f := by
  change (reducedPairedWeightEquiv K q (momentLinearIdeal K L)
    ((momentQuotientPolynomialEquiv K L).symm
      (momentQuotientPolynomialEquiv K L (Ideal.Quotient.mk _ f)))).1 = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- The true bounded weight image has exactly the surviving bounded monomial basis. -/
theorem reducedMomentWeightSpace_at_slack_eq_map (q : ι → ℤ)
    (L : Submodule K (ι → K)) (D : ℕ) :
    reducedBoundedPairedWeightSpace K q (momentLinearIdeal K L) (weightSlack q + D) =
      (restrictTotalDegree (Fin (Module.finrank K ((ι → K) ⧸ L))) K D).map
        (momentWeightCoordinateEmbedding K q L) := by
  have he : pairedWeightQuotientMap K q (momentLinearIdeal K L) =
      (momentWeightCoordinateEmbedding K q L).comp (momentCoordinateMap K L).toLinearMap := by
    apply LinearMap.ext
    intro f
    exact (momentWeightCoordinateEmbedding_map K q L f).symm
  rw [reducedBoundedPairedWeightSpace_at_slack, he, Submodule.map_comp,
    momentCoordinateMap_restrictTotalDegree]

/-- After the slack, each additional cut unit is distributed among surviving coordinates. -/
theorem finrank_reducedMomentWeightSpace_at_slack (q : ι → ℤ)
    (L : Submodule K (ι → K)) (D : ℕ) :
    Module.finrank K
      (reducedBoundedPairedWeightSpace K q (momentLinearIdeal K L) (weightSlack q + D)) =
      (Module.finrank K ((ι → K) ⧸ L) + D).choose D := by
  rw [reducedMomentWeightSpace_at_slack_eq_map]
  have he := Submodule.equivMapOfInjective (momentWeightCoordinateEmbedding K q L)
    (momentWeightCoordinateEmbedding_injective K q L)
    (restrictTotalDegree (Fin (Module.finrank K ((ι → K) ⧸ L))) K D)
  rw [← he.finrank_eq, finrank_restrictTotalDegree, Fintype.card_fin]

/-- No weight polynomial exists below its forced slack, regardless of neutral relations. -/
theorem reducedBoundedPairedWeightSpace_eq_bot_below_slack (q : ι → ℤ)
    (J : Ideal (MvPolynomial ι K)) (D : ℕ) (hD : D < weightSlack q) :
    reducedBoundedPairedWeightSpace K q J D = ⊥ := by
  have hs : {d : (ι ⊕ ι) →₀ ℕ | pairedWeight d = q ∧ cutDegree d ≤ D} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro d ⟨hw, hd⟩
    have h := weightSlack_le_cutDegree d
    rw [hw] at h
    omega
  rw [reducedBoundedPairedWeightSpace, boundedPairedWeightSpace, hs,
    restrictSupport_eq_span, Set.image_empty, Submodule.span_empty, Submodule.map_bot]

/-- Exact reduced cut multiplicity: only the rank of the moment equations changes the binomial. -/
theorem finrank_reducedMomentWeightSpace (q : ι → ℤ)
    (L : Submodule K (ι → K)) (D : ℕ) :
    Module.finrank K (reducedBoundedPairedWeightSpace K q (momentLinearIdeal K L) D) =
      if weightSlack q ≤ D then
        (Fintype.card ι - Module.finrank K L + (D - weightSlack q)).choose (D - weightSlack q)
      else 0 := by
  by_cases h : weightSlack q ≤ D
  · rw [if_pos h]
    have hd : weightSlack q + (D - weightSlack q) = D := Nat.add_sub_of_le h
    rw [← hd, finrank_reducedMomentWeightSpace_at_slack, momentQuotient_variable_count]
    simp only [Nat.add_sub_cancel_left]
  · rw [if_neg h, reducedBoundedPairedWeightSpace_eq_bot_below_slack K q _ D
      (Nat.lt_of_not_ge h)]
    simp

/-- The minimal monomial spans the first admissible reduced component. -/
theorem finrank_reducedMomentWeightSpace_first (q : ι → ℤ)
    (L : Submodule K (ι → K)) :
    Module.finrank K
      (reducedBoundedPairedWeightSpace K q (momentLinearIdeal K L) (weightSlack q)) = 1 := by
  simpa only [Nat.add_zero, Nat.choose_zero_right] using
    finrank_reducedMomentWeightSpace_at_slack K q L 0

/-- The constant coefficient relation becomes the diagonal bilinear moment equation. -/
theorem diagonalMomentIdeal_extended :
    (momentLinearIdeal K (Submodule.span K {(1 : ι → K)})).map (invariantSubstitution K) =
      Ideal.span {(∑ i, X (Sum.inl i) * X (Sum.inr i) : MvPolynomial (ι ⊕ ι) K)} := by
  have he : momentLinearIdeal K (Submodule.span K {(1 : ι → K)}) =
      Ideal.span {(∑ i, X i : MvPolynomial ι K)} := by
    have h := momentLinearIdeal_span_range K (fun _ : Unit => (1 : ι → K))
    simpa only [Set.range_const, momentLinearForm_apply, Pi.one_apply, one_smul] using h
  rw [he, Ideal.map_span, Set.image_singleton]
  simp only [map_sum, invariantSubstitution, eval₂Hom_X']

omit [Fintype ι] in
/-- The diagonal relation removes exactly one coordinate on a nonempty variable set. -/
theorem finrank_diagonalMomentRelations [Nonempty ι] :
    Module.finrank K (Submodule.span K {(1 : ι → K)}) = 1 :=
  finrank_span_singleton (show (1 : ι → K) ≠ 0 from one_ne_zero)

/-- Exact weight multiplicities in the quotient by the explicit equation `∑ zᵢwᵢ = 0`. -/
theorem finrank_diagonalMomentWeightSpace [Nonempty ι] (q : ι → ℤ) (D : ℕ) :
    Module.finrank K ((boundedPairedWeightSpace K q D).map
      (Ideal.Quotient.mkₐ K (Ideal.span
        {(∑ i, X (Sum.inl i) * X (Sum.inr i) : MvPolynomial (ι ⊕ ι) K)})).toLinearMap) =
      if weightSlack q ≤ D then
        (Fintype.card ι - 1 + (D - weightSlack q)).choose (D - weightSlack q) else 0 := by
  rw [← diagonalMomentIdeal_extended K]
  change Module.finrank K (reducedBoundedPairedWeightSpace K q
    (momentLinearIdeal K (Submodule.span K {(1 : ι → K)})) D) = _
  rw [finrank_reducedMomentWeightSpace, finrank_diagonalMomentRelations]

/-- Two pairs with one diagonal moment equation give linear multiplicity growth. -/
theorem finrank_twoPairMomentWeightSpace (q : Fin 2 → ℤ) (D : ℕ) :
    Module.finrank K ((boundedPairedWeightSpace K q D).map
      (Ideal.Quotient.mkₐ K (Ideal.span
        {(∑ i : Fin 2, X (Sum.inl i) * X (Sum.inr i) : MvPolynomial (Fin 2 ⊕ Fin 2) K)})).toLinearMap) =
      if weightSlack q ≤ D then D - weightSlack q + 1 else 0 := by
  rw [finrank_diagonalMomentWeightSpace]
  simp only [Fintype.card_fin, show 2 - 1 = 1 from rfl]
  split
  · rw [← Nat.choose_symm_add, Nat.choose_one_right, Nat.add_comm]
  · rfl

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_reducedMomentWeightSpace
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_reducedMomentWeightSpace_first
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_diagonalMomentWeightSpace
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_twoPairMomentWeightSpace
