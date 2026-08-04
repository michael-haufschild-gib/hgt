import GaloisForLFunctions.HTGeometry.RatioFieldReciprocity

/-!
# A single low-rank relation forces a single generator

The differential Lüroth conclusion for an intermediate field `G` of a free scalar differential field
follows from one numerical fact: that some element `w` of `G` outside the base admits a relation of
`y` over `F⟨w⟩` whose rank does not exceed the rank of the characteristic over `G`.  Rank
monotonicity then squeezes the characteristic over `F⟨w⟩` to exactly that rank, and the reciprocity
theorem identifies the two fields.

The relation supplied by Ritt's argument is the cross-relation of two coefficients of the
characteristic, so the second theorem here packages the criterion for a ratio of two differential
polynomials over the base.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F] [Differential E]
  [DifferentialAlgebra F E] [CharZero E]

omit [Differential F] [DifferentialAlgebra F E] [CharZero E] in
/-- A nonzero relation of `y` is nonconstant: a nonzero constant does not vanish at `y`. -/
theorem vars_nonempty_of_relation {B : IntermediateField F E} {y : E}
    {Q : DifferentialPolynomial Unit B}
    (hQmem : Q ∈ differentialIntermediateRelationIdeal B y) (hQne : Q ≠ 0) :
    Q.vars.Nonempty := by
  classical
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp h
  have hc : Q.coeff 0 ≠ 0 := by
    intro h0
    exact hQne (by rw [hC, h0, map_zero])
  rw [mem_differentialIntermediateRelationIdeal_iff, hC] at hQmem
  simp only [differentialPolynomialEvalOver_C] at hQmem
  exact hc ((algebraMap B E).injective (by simpa using hQmem))

/-- **The Lüroth criterion.**  If an element `w` of the intermediate field admits a relation of `y`
over the differential field it generates whose rank does not exceed the rank of the characteristic,
then `w` generates the whole intermediate field. -/
theorem eq_differentialAdjoin_of_relation_rank_le
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hGy : G ≤ differentialAdjoin F ({y} : Set E))
    {P : DifferentialPolynomial Unit G}
    (hPmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    {w : E} (hw : w ∈ G)
    {Q : DifferentialPolynomial Unit (differentialAdjoin F ({w} : Set E))}
    (hQmem : Q ∈ differentialIntermediateRelationIdeal (differentialAdjoin F ({w} : Set E)) y)
    (hQne : Q ≠ 0)
    (hQorder : scalarDifferentialPolynomialOrder Q ≤ scalarDifferentialPolynomialOrder P)
    (hQdeg : scalarDifferentialPolynomialOrder Q = scalarDifferentialPolynomialOrder P →
      scalarDifferentialPolynomialLeaderDegree Q ≤ scalarDifferentialPolynomialLeaderDegree P) :
    differentialAdjoin F ({w} : Set E) = G := by
  classical
  have hRG : differentialAdjoin F ({w} : Set E) ≤ G := by
    refine differentialAdjoin_le F ?_ hGclosed
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hw
  have hRclosed : DerivationClosed (differentialAdjoin F ({w} : Set E)) :=
    derivationClosed_differentialAdjoin F _
  have hQvars : Q.vars.Nonempty := vars_nonempty_of_relation hQmem hQne
  -- a characteristic over the generated field
  have hI0 : differentialIntermediateRelationIdeal (differentialAdjoin F ({w} : Set E)) y ≠ ⊥ := by
    intro h0
    exact hQne (by simpa [h0, Ideal.mem_bot] using hQmem)
  obtain ⟨P₁, hP₁min⟩ := Ideal.exists_minimal_scalarDifferentialPolynomialRank_ne_zero hI0
    (differentialIntermediateRelationIdeal_ne_top (differentialAdjoin F ({w} : Set E)) y)
  -- it has rank at most that of the supplied relation
  have h1 := hP₁min.2.2.2 (SetLike.mem_coe.mpr hQmem) hQne hQvars
  -- and at least that of the characteristic over the bigger field
  have hinj : Function.Injective
      ((IntermediateField.inclusion hRG :
        differentialAdjoin F ({w} : Set E) →ₐ[F] G).toRingHom) :=
    (IntermediateField.inclusion hRG).injective
  have hmap := mem_differentialIntermediateRelationIdeal_map hRG y hP₁min.1
  have hmapne : MvPolynomial.map
      (IntermediateField.inclusion hRG :
        differentialAdjoin F ({w} : Set E) →ₐ[F] G).toRingHom P₁ ≠ 0 := by
    intro h0
    exact hP₁min.2.1 (MvPolynomial.map_injective _ hinj (by simpa using h0))
  have hmapvars : (MvPolynomial.vars (MvPolynomial.map
      (IntermediateField.inclusion hRG :
        differentialAdjoin F ({w} : Set E) →ₐ[F] G).toRingHom P₁)).Nonempty := by
    rw [MvPolynomial.vars_map_of_injective _ hinj]
    exact hP₁min.2.2.1
  have h2 := hPmin.2.2.2 hmap hmapne hmapvars
  have hmaporder : scalarDifferentialPolynomialOrder
      (MvPolynomial.map (IntermediateField.inclusion hRG :
        differentialAdjoin F ({w} : Set E) →ₐ[F] G).toRingHom P₁)
      = scalarDifferentialPolynomialOrder P₁ :=
    scalarDifferentialPolynomialOrder_map hinj P₁
  have hmapleader : scalarDifferentialPolynomialLeaderDegree
      (MvPolynomial.map (IntermediateField.inclusion hRG :
        differentialAdjoin F ({w} : Set E) →ₐ[F] G).toRingHom P₁)
      = scalarDifferentialPolynomialLeaderDegree P₁ :=
    scalarDifferentialPolynomialLeaderDegree_map hinj P₁
  -- the two ranks coincide
  have horder : scalarDifferentialPolynomialOrder P₁ = scalarDifferentialPolynomialOrder P := by
    have hle : scalarDifferentialPolynomialOrder P ≤ scalarDifferentialPolynomialOrder P₁ := by
      rw [← hmaporder]
      exact h2.1
    have := h1.1
    omega
  have hQorderEq : scalarDifferentialPolynomialOrder Q = scalarDifferentialPolynomialOrder P := by
    have := h1.1
    omega
  have hleader : scalarDifferentialPolynomialLeaderDegree P₁ =
      scalarDifferentialPolynomialLeaderDegree P := by
    have hge : scalarDifferentialPolynomialLeaderDegree P ≤
        scalarDifferentialPolynomialLeaderDegree P₁ := by
      rw [← hmapleader]
      exact h2.2.1 (by rw [hmaporder, horder])
    have hle : scalarDifferentialPolynomialLeaderDegree P₁ ≤
        scalarDifferentialPolynomialLeaderDegree Q := h1.2.1 (by omega)
    have := hQdeg hQorderEq
    omega
  exact (eq_of_characteristic_rank_eq hRG hRclosed hGy hPmin hP₁min horder hleader).symm

/-- **The Lüroth criterion for a ratio of two differential polynomials over the base.**  If the
ratio of the values of `H` and `K` at `y` lies in the intermediate field but not in the base, and if
`H` and `K` have no jets above the order of the characteristic and no larger degree in that jet,
then that ratio generates the intermediate field. -/
theorem eq_differentialAdjoin_of_ratio_rank_le
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hGy : G ≤ differentialAdjoin F ({y} : Set E))
    {P : DifferentialPolynomial Unit G}
    (hPmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    {H K : DifferentialPolynomial Unit F}
    (hK : differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) K ≠ 0)
    (hwG : differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) H /
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) K ∈ G)
    (hwF : differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) H /
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) K ∉
      (⊥ : IntermediateField F E))
    (hHord : ∀ q ∈ H.vars, q.2 ≤ scalarDifferentialPolynomialOrder P)
    (hKord : ∀ q ∈ K.vars, q.2 ≤ scalarDifferentialPolynomialOrder P)
    (hHdeg : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder P) H ≤
      scalarDifferentialPolynomialLeaderDegree P)
    (hKdeg : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder P) K ≤
      scalarDifferentialPolynomialLeaderDegree P) :
    differentialAdjoin F
        ({differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) H /
          differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) K} : Set E) = G := by
  classical
  set hE := differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) H with hHE
  set kE := differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) K with hKE
  set w := hE / kE with hwdef
  set R := differentialAdjoin F ({w} : Set E) with hR
  have hwR : w ∈ R := subset_differentialAdjoin F _ rfl
  -- the cross-relation of the two polynomials over the field generated by the ratio
  set Q : DifferentialPolynomial Unit R :=
    MvPolynomial.C (⟨w, hwR⟩ : R) * MvPolynomial.map (algebraMap F R) K -
      MvPolynomial.map (algebraMap F R) H with hQ
  have hmapeval : ∀ p : DifferentialPolynomial Unit F,
      differentialPolynomialEvalOver (K := R) (fun _ : Unit ↦ y)
          (MvPolynomial.map (algebraMap F R) p) =
        differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) p := by
    intro p
    exact differentialPolynomialEvalOver_map_intermediate R y p
  have hQmem : Q ∈ differentialIntermediateRelationIdeal R y := by
    rw [mem_differentialIntermediateRelationIdeal_iff, hQ]
    simp only [map_sub, map_mul, differentialPolynomialEvalOver_C, hmapeval]
    have hval : (algebraMap R E) (⟨w, hwR⟩ : R) = w := rfl
    rw [hval, hwdef, div_mul_cancel₀ _ hK, sub_self]
  -- it is nonzero, because the ratio is not in the base
  have hQne : Q ≠ 0 := by
    intro h0
    have hcoeff : ∀ μ : (Unit × ℕ) →₀ ℕ,
        (⟨w, hwR⟩ : R) * (algebraMap F R) (K.coeff μ) = (algebraMap F R) (H.coeff μ) := by
      intro μ
      have := congrArg (fun r : DifferentialPolynomial Unit R => MvPolynomial.coeff μ r) h0
      rw [hQ] at this
      simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
        MvPolynomial.coeff_zero] at this
      exact sub_eq_zero.1 this
    have hK0 : K = 0 := by
      by_contra hKne
      obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.1 hKne
      have hval := hcoeff μ
      have hwmem : w ∈ (⊥ : IntermediateField F E) := by
        have hKμ : (algebraMap F E) (K.coeff μ) ≠ 0 := by
          simpa using (algebraMap F E).injective.ne hμ
        have hEeq : w * (algebraMap F E) (K.coeff μ) = (algebraMap F E) (H.coeff μ) :=
          congrArg (fun r : R => (r : E)) hval
        have : w = (algebraMap F E) (H.coeff μ / K.coeff μ) := by
          rw [map_div₀, eq_div_iff hKμ, hEeq]
        rw [this]
        exact IntermediateField.algebraMap_mem _ _
      exact hwF hwmem
    exact hK (by rw [hKE, hK0, map_zero])
  -- rank bounds
  have hQvarsle : ∀ q ∈ Q.vars, q.2 ≤ scalarDifferentialPolynomialOrder P := by
    intro q hq
    rw [hQ] at hq
    rcases Finset.mem_union.1 (MvPolynomial.vars_sub_subset (R := R) _ hq) with h1 | h2
    · rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ h1) with hc | hm
      · exact absurd hc (by simp)
      · rw [MvPolynomial.vars_map_of_injective _ (algebraMap F R).injective] at hm
        exact hKord q hm
    · rw [MvPolynomial.vars_map_of_injective _ (algebraMap F R).injective] at h2
      exact hHord q h2
  have hQorder : scalarDifferentialPolynomialOrder Q ≤ scalarDifferentialPolynomialOrder P :=
    Finset.sup_le fun q hq => hQvarsle q hq
  have hQdeg : scalarDifferentialPolynomialOrder Q = scalarDifferentialPolynomialOrder P →
      scalarDifferentialPolynomialLeaderDegree Q ≤
        scalarDifferentialPolynomialLeaderDegree P := by
    intro hEq
    have hdegmap : ∀ p : DifferentialPolynomial Unit F,
        MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder P)
            (MvPolynomial.map (algebraMap F R) p)
          = MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder P) p := by
      intro p
      rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
        MvPolynomial.support_map_of_injective _ (algebraMap F R).injective]
    rw [scalarDifferentialPolynomialLeaderDegree, scalarDifferentialPolynomialLeader, hEq, hQ]
    refine le_trans (MvPolynomial.degreeOf_sub_le _ _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (MvPolynomial.degreeOf_C_mul_le _ _ _) ?_
      rw [hdegmap]
      exact hKdeg
    · rw [hdegmap]
      exact hHdeg
  exact eq_differentialAdjoin_of_relation_rank_le G hGclosed hGy hPmin hwG hQmem hQne hQorder hQdeg

end

end GaloisForLFunctions
