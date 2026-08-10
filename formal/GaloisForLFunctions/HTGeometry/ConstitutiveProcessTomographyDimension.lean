import Mathlib

/-!
# The hidden constitutive dimension of a product instrument family

A product instrument family fixes, in every slot, a subspace of allowed interventions; the joint
intervention space it spans is the tensor product of the slot subspaces.  Its dual annihilator —
the blind sector of the tomography theorem — therefore has dimension exactly

`∏ᵢ dim Eᵢ − ∏ᵢ dim Vᵢ`,

and the family reconstructs every process precisely when every slot family spans.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-! ## The dimension of a finite tensor product -/

theorem finrank_piTensorProduct [∀ i, FiniteDimensional K (E i)] :
    finrank K (PiTensorProduct K (fun i => E i)) = ∏ i, finrank K (E i) := by
  classical
  let b : (i : ι) → Basis (Fin (finrank K (E i))) K (E i) := fun i => Module.finBasis K (E i)
  have hb := Basis.piTensorProduct b
  rw [finrank_eq_card_basis hb, Fintype.card_pi]
  simp

instance finiteDimensional_piTensorProduct [∀ i, FiniteDimensional K (E i)] :
    FiniteDimensional K (PiTensorProduct K (fun i => E i)) := by
  classical
  let b : (i : ι) → Basis (Fin (finrank K (E i))) K (E i) := fun i => Module.finBasis K (E i)
  exact Module.Finite.of_basis (Basis.piTensorProduct b)

/-! ## Injectivity of the slotwise tensor map -/

omit [Fintype ι] in
theorem piTensorProduct_map_injective {F : ι → Type*} [∀ i, AddCommGroup (F i)]
    [∀ i, Module K (F i)] (f : (i : ι) → F i →ₗ[K] E i)
    (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  choose g hg using fun i =>
    LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.mpr (hf i))
  have hcomp : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map f)
      = (LinearMap.id : PiTensorProduct K (fun i => F i) →ₗ[K] _) := by
    rw [← PiTensorProduct.map_comp]
    have hfun : (fun i => g i ∘ₗ f i) = fun i => (LinearMap.id : F i →ₗ[K] F i) := by
      funext i
      exact hg i
    rw [hfun, PiTensorProduct.map_id]
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  have := congrArg (fun L => L x) hcomp
  simpa using this

/-! ## The product instrument space -/

/-- The joint intervention space spanned by all product interventions with slot `i` drawn from
`V i`. -/
def productInterventionSpace (V : (i : ι) → Submodule K (E i)) :
    Submodule K (PiTensorProduct K (fun i => E i)) :=
  LinearMap.range (PiTensorProduct.map fun i => (V i).subtype)

omit [Fintype ι] in
theorem productInterventionSpace_eq_span (V : (i : ι) → Submodule K (E i)) :
    productInterventionSpace V
      = Submodule.span K
        (Set.range fun v : (i : ι) → V i =>
          PiTensorProduct.tprod K (fun i => ((v i : E i)))) := by
  rw [productInterventionSpace, LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, by rw [PiTensorProduct.map_tprod]; rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨PiTensorProduct.tprod K v, ⟨v, rfl⟩, by rw [PiTensorProduct.map_tprod]; rfl⟩

theorem finrank_productInterventionSpace [∀ i, FiniteDimensional K (E i)]
    (V : (i : ι) → Submodule K (E i)) :
    finrank K (productInterventionSpace V) = ∏ i, finrank K (V i) := by
  have hinj : Function.Injective (PiTensorProduct.map fun i => (V i).subtype) :=
    piTensorProduct_map_injective _ fun i => Submodule.injective_subtype (V i)
  rw [productInterventionSpace, LinearMap.finrank_range_of_inj hinj]
  exact finrank_piTensorProduct

/-- **Equation (7).**  The hidden constitutive dimension of a product instrument family. -/
theorem finrank_dualAnnihilator_productInterventionSpace [∀ i, FiniteDimensional K (E i)]
    (V : (i : ι) → Submodule K (E i)) :
    finrank K (productInterventionSpace V).dualAnnihilator
      = (∏ i, finrank K (E i)) - ∏ i, finrank K (V i) := by
  have hadd := Subspace.finrank_add_finrank_dualAnnihilator_eq (productInterventionSpace V)
  rw [finrank_productInterventionSpace V, finrank_piTensorProduct] at hadd
  omega

/-! ## Completeness of a product instrument family -/

theorem productInterventionSpace_eq_top_of_forall [∀ i, FiniteDimensional K (E i)]
    (V : (i : ι) → Submodule K (E i)) (hV : ∀ i, V i = ⊤) :
    productInterventionSpace V = ⊤ := by
  have hrank : finrank K (productInterventionSpace V)
      = finrank K (PiTensorProduct K (fun i => E i)) := by
    rw [finrank_productInterventionSpace V, finrank_piTensorProduct]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hV i]
    exact finrank_top K (E i)
  exact Submodule.eq_top_of_finrank_eq hrank

/-- **Product tomography is complete exactly when every slot family spans.** -/
theorem productInterventionSpace_eq_top_iff [∀ i, FiniteDimensional K (E i)]
    [∀ i, Nontrivial (E i)] (V : (i : ι) → Submodule K (E i)) :
    productInterventionSpace V = ⊤ ↔ ∀ i, V i = ⊤ := by
  classical
  constructor
  · intro htop j
    have hle : ∀ i, finrank K (V i) ≤ finrank K (E i) := fun i => Submodule.finrank_le (V i)
    have hpos : ∀ i, 0 < finrank K (E i) := fun i => finrank_pos
    have hrank : (∏ i, finrank K (V i)) = ∏ i, finrank K (E i) := by
      have h1 := finrank_productInterventionSpace V
      rw [htop, finrank_top, finrank_piTensorProduct] at h1
      exact h1.symm
    have hsplitV : finrank K (V j) * ∏ i ∈ Finset.univ.erase j, finrank K (V i)
        = ∏ i, finrank K (V i) :=
      Finset.mul_prod_erase Finset.univ (fun i => finrank K (V i)) (Finset.mem_univ j)
    have hsplitE : finrank K (E j) * ∏ i ∈ Finset.univ.erase j, finrank K (E i)
        = ∏ i, finrank K (E i) :=
      Finset.mul_prod_erase Finset.univ (fun i => finrank K (E i)) (Finset.mem_univ j)
    have hprodle : (∏ i ∈ Finset.univ.erase j, finrank K (V i))
        ≤ ∏ i ∈ Finset.univ.erase j, finrank K (E i) :=
      Finset.prod_le_prod' fun i _ => hle i
    have hPpos : 0 < ∏ i ∈ Finset.univ.erase j, finrank K (E i) :=
      Finset.prod_pos fun i _ => hpos i
    have hchain : finrank K (E j) * (∏ i ∈ Finset.univ.erase j, finrank K (E i))
        ≤ finrank K (V j) * ∏ i ∈ Finset.univ.erase j, finrank K (E i) := by
      calc finrank K (E j) * (∏ i ∈ Finset.univ.erase j, finrank K (E i))
          = ∏ i, finrank K (E i) := hsplitE
        _ = ∏ i, finrank K (V i) := hrank.symm
        _ = finrank K (V j) * ∏ i ∈ Finset.univ.erase j, finrank K (V i) := hsplitV.symm
        _ ≤ finrank K (V j) * ∏ i ∈ Finset.univ.erase j, finrank K (E i) :=
            Nat.mul_le_mul_left _ hprodle
    have hge : finrank K (E j) ≤ finrank K (V j) :=
      Nat.le_of_mul_le_mul_right hchain hPpos
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (hle j) hge)
  · exact productInterventionSpace_eq_top_of_forall V

end

end GaloisForLFunctions.HTGeometry
