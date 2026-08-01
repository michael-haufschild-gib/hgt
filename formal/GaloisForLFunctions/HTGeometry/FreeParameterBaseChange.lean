import GaloisForLFunctions.HTGeometry.BaseChangeRelativeClosure
import GaloisForLFunctions.HTGeometry.FractionRingConstantsEmbedding

/-!
# Adjoining a free parameter does not change the Galois group

Take the rational functions in one variable over a splitting field.  The rational functions over the
base sit inside them, and together with the splitting field they generate everything: the constants
and the variable generate every polynomial, hence every quotient of two.

The rational functions over the base carry no algebraic element beyond the base, so they meet the
splitting field in the base and restriction is an isomorphism.  So the Galois group of a separable
polynomial is unchanged when a free parameter is adjoined to the base.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The rational functions over the base, inside the rational functions over the splitting field. -/
noncomputable def fracSub (F E : Type*) [Field F] [Field E] [Algebra F E] :
    IntermediateField F (FractionRing (Polynomial E)) :=
  (fracEmbed F E).fieldRange

theorem fracEmbed_fracX : fracEmbed F E (fracX F) = fracX E := by
  show fracEmbedRingHom F E
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) = _
  rw [fracEmbedRingHom_algebraMap, Polynomial.map_X]
  rfl

theorem fracX_mem_fracSub : fracX E ∈ fracSub F E :=
  ⟨fracX F, fracEmbed_fracX⟩

/-! ## Generation -/

theorem algebraMap_polynomial_mem
    {S : IntermediateField F (FractionRing (Polynomial E))}
    (hE : ∀ a : E, algebraMap E (FractionRing (Polynomial E)) a ∈ S)
    (hX : fracX E ∈ S) (f : Polynomial E) :
    algebraMap (Polynomial E) (FractionRing (Polynomial E)) f ∈ S := by
  have himg : algebraMap (Polynomial E) (FractionRing (Polynomial E)) f =
      ∑ i ∈ f.support,
        algebraMap E (FractionRing (Polynomial E)) (f.coeff i) * (fracX E) ^ i := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    congr 1
  rw [himg]
  exact sum_mem fun i _ => mul_mem (hE _) (pow_mem hX i)

/-- **The constants and the variable generate the rational functions.** -/
theorem eq_top_of_mem_of_mem {S : IntermediateField F (FractionRing (Polynomial E))}
    (hE : ∀ a : E, algebraMap E (FractionRing (Polynomial E)) a ∈ S)
    (hX : fracX E ∈ S) : S = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial E) x
  exact div_mem (algebraMap_polynomial_mem hE hX f) (algebraMap_polynomial_mem hE hX g)

/-! ## The splitting field inside the rational functions -/

theorem algebraMap_mem_rootSet {p : Polynomial F} (hp : p ≠ 0) {x : E}
    (hx : x ∈ p.rootSet E) :
    algebraMap E (FractionRing (Polynomial E)) x ∈
      p.rootSet (FractionRing (Polynomial E)) := by
  rw [Polynomial.mem_rootSet] at hx ⊢
  refine ⟨hp, ?_⟩
  rw [Polynomial.aeval_algebraMap_apply, hx.2, map_zero]

/-- **The splitting field lies in the root field of the ambient rational functions.** -/
theorem algebraMap_mem_rootField {p : Polynomial F} (hp : p ≠ 0)
    (hgen : IntermediateField.adjoin F (p.rootSet E) = ⊤) (a : E) :
    algebraMap E (FractionRing (Polynomial E)) a ∈
      rootField F (L := FractionRing (Polynomial E)) p := by
  have hle : IntermediateField.adjoin F (p.rootSet E) ≤
      IntermediateField.comap
        (IsScalarTower.toAlgHom F E (FractionRing (Polynomial E)))
        (rootField F (L := FractionRing (Polynomial E)) p) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    exact IntermediateField.subset_adjoin _ _ (algebraMap_mem_rootSet hp hx)
  rw [hgen] at hle
  exact hle (IntermediateField.mem_top (x := a))

/-- **The splitting field and the small rational functions generate everything.** -/
theorem rootField_sup_fracSub_eq_top {p : Polynomial F} (hp : p ≠ 0)
    (hgen : IntermediateField.adjoin F (p.rootSet E) = ⊤) :
    rootField F (L := FractionRing (Polynomial E)) p ⊔ fracSub F E = ⊤ :=
  eq_top_of_mem_of_mem
    (fun a => SetLike.le_def.mp le_sup_left (algebraMap_mem_rootField hp hgen a))
    (SetLike.le_def.mp le_sup_right fracX_mem_fracSub)

theorem splits_map_fractionRing {p : Polynomial F}
    (hsplit : (p.map (algebraMap F E)).Splits) :
    (p.map (algebraMap F (FractionRing (Polynomial E)))).Splits := by
  have h := hsplit.map (algebraMap E (FractionRing (Polynomial E)))
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h

theorem rootSet_map_fracSub {p : Polynomial F} :
    (p.map (algebraMap F (fracSub F E))).rootSet (FractionRing (Polynomial E)) =
      p.rootSet (FractionRing (Polynomial E)) := by
  simp only [Polynomial.rootSet, Polynomial.aroots, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- **The ambient rational functions are a splitting field over the small ones.** -/
theorem isSplittingField_fracSub {p : Polynomial F} (hp : p ≠ 0)
    (hsplit : (p.map (algebraMap F E)).Splits)
    (hgen : IntermediateField.adjoin F (p.rootSet E) = ⊤) :
    Polynomial.IsSplittingField (fracSub F E) (FractionRing (Polynomial E))
      (p.map (algebraMap F (fracSub F E))) := by
  constructor
  · have h := splits_map_fractionRing (E := E) hsplit
    rwa [show Polynomial.map (algebraMap F (FractionRing (Polynomial E))) p =
        Polynomial.map (algebraMap (fracSub F E) (FractionRing (Polynomial E)))
          (Polynomial.map (algebraMap F (fracSub F E)) p) from by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]] at h
  · have hadj : IntermediateField.adjoin (fracSub F E)
        (p.rootSet (FractionRing (Polynomial E))) = ⊤ := by
      refine IntermediateField.restrictScalars_injective F ?_
      rw [IntermediateField.restrictScalars_top]
      refine eq_top_of_mem_of_mem (fun a => ?_) ?_
      · have h1 : algebraMap E (FractionRing (Polynomial E)) a ∈
            rootField F (L := FractionRing (Polynomial E)) p :=
          algebraMap_mem_rootField hp hgen a
        have h2 : rootField F (L := FractionRing (Polynomial E)) p ≤
            (IntermediateField.adjoin (fracSub F E)
              (p.rootSet (FractionRing (Polynomial E)))).restrictScalars F := by
          rw [rootField, IntermediateField.adjoin_le_iff]
          exact IntermediateField.subset_adjoin _ _
        exact h2 h1
      · exact (IntermediateField.adjoin (fracSub F E)
          (p.rootSet (FractionRing (Polynomial E)))).algebraMap_mem
            (⟨fracX E, fracX_mem_fracSub⟩ : fracSub F E)
    have halg : ∀ x ∈ (p.map (algebraMap F (fracSub F E))).rootSet
        (FractionRing (Polynomial E)), IsAlgebraic (fracSub F E) x := by
      intro x hx
      rw [Polynomial.mem_rootSet] at hx
      exact ⟨_, hx.1, hx.2⟩
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, rootSet_map_fracSub, hadj]
    exact IntermediateField.top_toSubalgebra

/-- **Adjoining a free parameter does not change the Galois group.**  The rational functions over
the base meet the splitting field in the base and generate the ambient field together with it, so
restriction is an isomorphism onto the Galois group over the base. -/
noncomputable def freeParameterBaseChange {p : Polynomial F} (hp : p ≠ 0) (hsep : p.Separable)
    (hsplit : (p.map (algebraMap F E)).Splits)
    (hgen : IntermediateField.adjoin F (p.rootSet E) = ⊤) :
    (FractionRing (Polynomial E) ≃ₐ[fracSub F E] FractionRing (Polynomial E)) ≃*
      (rootField F (L := FractionRing (Polynomial E)) p ≃ₐ[F]
        rootField F (L := FractionRing (Polynomial E)) p) := by
  haveI := isSplittingField_fracSub hp hsplit hgen
  haveI : FiniteDimensional (fracSub F E) (FractionRing (Polynomial E)) :=
    Polynomial.IsSplittingField.finiteDimensional _ (p.map (algebraMap F (fracSub F E)))
  haveI : IsGalois (fracSub F E) (FractionRing (Polynomial E)) :=
    IsGalois.of_separable_splitting_field
      (p := Polynomial.map (algebraMap F (fracSub F E)) p) hsep.map
  exact baseChangeRelativelyClosed hsep (splits_map_fractionRing (E := E) hsplit)
    (fun _ hx halg => mem_bot_of_mem_fieldRange_of_isAlgebraic hx halg)
    (rootField_sup_fracSub_eq_top hp hgen)

/-- **The permutation identification survives a free parameter.**  If the Galois group of a
separable polynomial over its splitting field is identified with a permutation group, the same
identification holds over the rational functions in one free variable. -/
noncomputable def freeParameterPermEquiv {p : Polynomial F} (hp : p ≠ 0) (hsep : p.Separable)
    (hsplit : (p.map (algebraMap F E)).Splits)
    (hgen : IntermediateField.adjoin F (p.rootSet E) = ⊤)
    {γ : Type*} [Polynomial.IsSplittingField F E p] (ψ : (E ≃ₐ[F] E) ≃* Equiv.Perm γ) :
    (FractionRing (Polynomial E) ≃ₐ[fracSub F E] FractionRing (Polynomial E)) ≃*
      Equiv.Perm γ :=
  (freeParameterBaseChange hp hsep hsplit hgen).trans
    (rootFieldPermEquiv (F := F) (p := p) (L := E)
      (L' := FractionRing (Polynomial E))
      (splits_map_fractionRing (E := E) hsplit) ψ)

end GaloisForLFunctions.HTGeometry
