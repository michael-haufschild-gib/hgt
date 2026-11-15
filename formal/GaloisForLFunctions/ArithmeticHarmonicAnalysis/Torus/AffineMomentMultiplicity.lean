import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentQuotient
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.ReducedMomentMultiplicity

/-!
# Weight multiplicities are independent of the affine moment level

For a relation space `L` and any level functional on `L`, the actual bounded
weight image in the affine moment quotient has the same slack-shifted binomial
dimension as at zero level. Translation preserves the neutral degree
filtration, so the result concerns the original bounded polynomial images.

The explicit diagonal fibers `∑ zᵢwᵢ = t` lose one neutral coordinate at every
value of `t`. For one variable pair, every weight has dimension one once its
slack is reached, including the reducible fiber `zw = 0`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Surviving polynomial coordinates parametrize each weight at any affine moment level. -/
def reducedAffineMomentWeightEquiv (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    MvPolynomial (Fin (Module.finrank K ((ι → K) ⧸ L))) K ≃ₗ[K]
      reducedPairedWeightSpace K q (affineMomentIdeal K L ℓ) :=
  (affineMomentPolynomialEquiv K L ℓ).symm.toLinearEquiv.trans
    (reducedPairedWeightEquiv K q (affineMomentIdeal K L ℓ))

/-- Embed polynomial coordinates into the actual affine quotient weight component. -/
def affineMomentWeightCoordinateEmbedding (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    MvPolynomial (Fin (Module.finrank K ((ι → K) ⧸ L))) K →ₗ[K]
      (MvPolynomial (ι ⊕ ι) K ⧸ (affineMomentIdeal K L ℓ).map (invariantSubstitution K)) :=
  (reducedPairedWeightSpace K q (affineMomentIdeal K L ℓ)).subtype.comp
    (reducedAffineMomentWeightEquiv K q L ℓ).toLinearMap

theorem affineMomentWeightCoordinateEmbedding_injective (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    Function.Injective (affineMomentWeightCoordinateEmbedding K q L ℓ) :=
  Subtype.val_injective.comp (reducedAffineMomentWeightEquiv K q L ℓ).injective

/-- The affine coordinate embedding factors the actual normal-form quotient map. -/
theorem affineMomentWeightCoordinateEmbedding_map (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (f : MvPolynomial ι K) :
    affineMomentWeightCoordinateEmbedding K q L ℓ (affineMomentCoordinateMap K L ℓ f) =
      pairedWeightQuotientMap K q (affineMomentIdeal K L ℓ) f := by
  rw [← affineMomentCoordinateMap_mk]
  change (reducedPairedWeightEquiv K q (affineMomentIdeal K L ℓ)
    ((affineMomentPolynomialEquiv K L ℓ).symm
      (affineMomentPolynomialEquiv K L ℓ (Ideal.Quotient.mk _ f)))).1 = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Bounded affine weight images are exactly the embedded bounded coordinate polynomials. -/
theorem reducedAffineMomentWeightSpace_at_slack_eq_map (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (D : ℕ) :
    reducedBoundedPairedWeightSpace K q (affineMomentIdeal K L ℓ) (weightSlack q + D) =
      (restrictTotalDegree (Fin (Module.finrank K ((ι → K) ⧸ L))) K D).map
        (affineMomentWeightCoordinateEmbedding K q L ℓ) := by
  have he : pairedWeightQuotientMap K q (affineMomentIdeal K L ℓ) =
      (affineMomentWeightCoordinateEmbedding K q L ℓ).comp
        (affineMomentCoordinateMap K L ℓ).toLinearMap := by
    apply LinearMap.ext
    intro f
    exact (affineMomentWeightCoordinateEmbedding_map K q L ℓ f).symm
  rw [reducedBoundedPairedWeightSpace_at_slack, he, Submodule.map_comp,
    affineMomentCoordinateMap_restrictTotalDegree]

/-- The slack-shifted binomial count is unchanged by the affine level. -/
theorem finrank_reducedAffineMomentWeightSpace_at_slack (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (D : ℕ) :
    Module.finrank K
      (reducedBoundedPairedWeightSpace K q (affineMomentIdeal K L ℓ) (weightSlack q + D)) =
      (Module.finrank K ((ι → K) ⧸ L) + D).choose D := by
  rw [reducedAffineMomentWeightSpace_at_slack_eq_map]
  have he := Submodule.equivMapOfInjective (affineMomentWeightCoordinateEmbedding K q L ℓ)
    (affineMomentWeightCoordinateEmbedding_injective K q L ℓ)
    (restrictTotalDegree (Fin (Module.finrank K ((ι → K) ⧸ L))) K D)
  rw [← he.finrank_eq, finrank_restrictTotalDegree, Fintype.card_fin]

/-- Exact filtered multiplicity at every affine moment level, including below the cutoff. -/
theorem finrank_reducedAffineMomentWeightSpace (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (D : ℕ) :
    Module.finrank K (reducedBoundedPairedWeightSpace K q (affineMomentIdeal K L ℓ) D) =
      if weightSlack q ≤ D then
        (Fintype.card ι - Module.finrank K L + (D - weightSlack q)).choose (D - weightSlack q)
      else 0 := by
  by_cases h : weightSlack q ≤ D
  · rw [if_pos h]
    have hd : weightSlack q + (D - weightSlack q) = D := Nat.add_sub_of_le h
    rw [← hd, finrank_reducedAffineMomentWeightSpace_at_slack, momentQuotient_variable_count]
    simp only [Nat.add_sub_cancel_left]
  · rw [if_neg h, reducedBoundedPairedWeightSpace_eq_bot_below_slack K q _ D
      (Nat.lt_of_not_ge h)]
    simp

/-- Filtered weight multiplicities depend on the relation space but not on its level functional. -/
theorem finrank_reducedAffineMomentWeightSpace_level_independent (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ₁ ℓ₂ : L →ₗ[K] K) (D : ℕ) :
    Module.finrank K (reducedBoundedPairedWeightSpace K q (affineMomentIdeal K L ℓ₁) D) =
      Module.finrank K (reducedBoundedPairedWeightSpace K q (affineMomentIdeal K L ℓ₂) D) := by
  rw [finrank_reducedAffineMomentWeightSpace, finrank_reducedAffineMomentWeightSpace]

/-- Every affine level has the same filtered weight dimensions as the homogeneous moment quotient. -/
theorem finrank_reducedAffineMomentWeightSpace_eq_zeroLevel (q : ι → ℤ)
    (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) (D : ℕ) :
    Module.finrank K (reducedBoundedPairedWeightSpace K q (affineMomentIdeal K L ℓ) D) =
      Module.finrank K (reducedBoundedPairedWeightSpace K q (momentLinearIdeal K L) D) := by
  rw [finrank_reducedAffineMomentWeightSpace, finrank_reducedMomentWeightSpace]

/-- A level taking the diagonal relation to the prescribed scalar. -/
def diagonalMomentLevel (i : ι) (t : K) : (Submodule.span K {(1 : ι → K)}) →ₗ[K] K :=
  t • (LinearMap.proj i).comp (Submodule.span K {(1 : ι → K)}).subtype

/-- A relation space generated by one vector gives one affine equation. -/
theorem affineMomentIdeal_span_one (ℓ : (Submodule.span K {(1 : ι → K)}) →ₗ[K] K) :
    affineMomentIdeal K (Submodule.span K {(1 : ι → K)}) ℓ =
      Ideal.span {momentLinearForm K (1 : ι → K) -
        C (ℓ ⟨1, Submodule.subset_span (Set.mem_singleton 1)⟩)} := by
  let v : Submodule.span K {(1 : ι → K)} := ⟨1, Submodule.subset_span (Set.mem_singleton 1)⟩
  apply le_antisymm
  · rw [affineMomentIdeal, Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp c.2
    have hc : c = r • v := Subtype.ext hr.symm
    rw [hc]
    have he : momentLinearForm K (r • v).1 - C (ℓ (r • v)) =
        r • (momentLinearForm K v.1 - C (ℓ v)) := by
      rw [Submodule.coe_smul, map_smul, map_smul, smul_sub]
      congr 1
      simpa only [smul_eq_mul, smul_eq_C_mul] using map_mul C r (ℓ v)
    change (momentLinearForm K (r • v).1 - C (ℓ (r • v))) ∈ _
    rw [he]
    exact (Ideal.span {momentLinearForm K (1 : ι → K) - C (ℓ v)}).restrictScalars K
      |>.smul_mem r (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_le]
    rintro f rfl
    exact Ideal.subset_span ⟨v, rfl⟩

/-- The diagonal level is the explicit equation `∑ zᵢwᵢ = t`. -/
theorem diagonalAffineMomentIdeal_extended (i : ι) (t : K) :
    (affineMomentIdeal K (Submodule.span K {(1 : ι → K)}) (diagonalMomentLevel K i t)).map
      (invariantSubstitution K) =
      Ideal.span {(∑ j, X (Sum.inl j) * X (Sum.inr j) : MvPolynomial (ι ⊕ ι) K) - C t} := by
  rw [affineMomentIdeal_span_one, Ideal.map_span, Set.image_singleton]
  simp [diagonalMomentLevel, momentLinearForm_apply, invariantSubstitution]

/-- The explicit diagonal moment fiber has the same multiplicities at every scalar value. -/
theorem finrank_diagonalAffineMomentWeightSpace (i : ι) (t : K) (q : ι → ℤ) (D : ℕ) :
    Module.finrank K ((boundedPairedWeightSpace K q D).map
      (Ideal.Quotient.mkₐ K (Ideal.span
        {(∑ j, X (Sum.inl j) * X (Sum.inr j) : MvPolynomial (ι ⊕ ι) K) - C t})).toLinearMap) =
      if weightSlack q ≤ D then
        (Fintype.card ι - 1 + (D - weightSlack q)).choose (D - weightSlack q) else 0 := by
  letI : Nonempty ι := ⟨i⟩
  rw [← diagonalAffineMomentIdeal_extended K i t]
  change Module.finrank K (reducedBoundedPairedWeightSpace K q
    (affineMomentIdeal K (Submodule.span K {(1 : ι → K)}) (diagonalMomentLevel K i t)) D) = _
  rw [finrank_reducedAffineMomentWeightSpace, finrank_diagonalMomentRelations]

/-- In `K[z,w]/(zw-t)`, each weight has dimension one above its forced slack, for every `t`. -/
theorem finrank_singlePairAffineMomentWeightSpace (t : K) (q : Fin 1 → ℤ) (D : ℕ) :
    Module.finrank K ((boundedPairedWeightSpace K q D).map
      (Ideal.Quotient.mkₐ K (Ideal.span
        {(X (Sum.inl 0) * X (Sum.inr 0) - C t : MvPolynomial (Fin 1 ⊕ Fin 1) K)})).toLinearMap) =
      if weightSlack q ≤ D then 1 else 0 := by
  have h := finrank_diagonalAffineMomentWeightSpace K (0 : Fin 1) t q D
  have he : (∑ j : Fin 1, X (Sum.inl j) * X (Sum.inr j) : MvPolynomial (Fin 1 ⊕ Fin 1) K) =
      X (Sum.inl 0) * X (Sum.inr 0) := Fin.sum_univ_one _
  rw [he] at h
  simpa only [Fintype.card_fin, Nat.sub_self, Nat.zero_add,
    Nat.choose_self] using h

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_reducedAffineMomentWeightSpace
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_diagonalAffineMomentWeightSpace
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_singlePairAffineMomentWeightSpace
