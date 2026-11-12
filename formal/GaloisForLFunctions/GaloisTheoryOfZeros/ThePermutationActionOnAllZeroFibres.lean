import GaloisForLFunctions.GaloisTheoryOfZeros.TheFieldOfCompleteFibreTraces
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The action on all complete zero fibres

Source-field automorphisms act faithfully on the product of the finite supports
of all ordinate fibres. Each coordinate commutes with conjugation; multiplicity
is recorded by the complete source polynomial, independently of copy labels.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- Distinct roots in a complete ordinate fibre, without multiplicity-copy labels. -/
def fibreZeroSupport (t : ℝ) : Finset ℂ :=
  (ordinateFibreCopies t).image xiSpectralPoint

private theorem fibreZeroSupport_mem_field (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    (z : ℂ) ∈ fullFibreZeroExtension := by
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp z.property
  rw [← hq]
  exact (centeredZeroInFibreExtension q).property

/-- A fibre support point as an element of the entire centered zero field. -/
def fibreRootInField (t : ℝ) (z : ↥(fibreZeroSupport t)) : fullFibreZeroExtension :=
  ⟨z,fibreZeroSupport_mem_field t z⟩

private def fibrePermutationFun (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : ↥(fibreZeroSupport t)) : ↥(fibreZeroSupport t) :=
  ⟨(σ (fibreRootInField t z) : ℂ),by
    obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp z.property
    have hqF : fibreRootInField t z = centeredZeroInFibreExtension q := Subtype.ext hqz.symm
    obtain ⟨r,hr,he⟩ := fullFibre_aut_preserves_ordinate σ q
    have hqt := (mem_ordinateFibreCopies t q).mp hq
    rw [hqt] at hr
    exact Finset.mem_image.mpr ⟨r,hr,by rw [hqF]; exact he.symm⟩⟩

private theorem fibrePermutationFun_in_field (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : ↥(fibreZeroSupport t)) :
    fibreRootInField t (fibrePermutationFun t σ z) = σ (fibreRootInField t z) :=
  Subtype.ext rfl

/-- The source Galois action on one complete finite support. -/
def fibrePermutation (t : ℝ) :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      Equiv.Perm ↥(fibreZeroSupport t) where
  toFun σ :=
    { toFun := fibrePermutationFun t σ
      invFun := fibrePermutationFun t σ.symm
      left_inv := fun z => by
        apply Subtype.ext
        change (σ.symm (fibreRootInField t (fibrePermutationFun t σ z)) : ℂ) = (z : ℂ)
        rw [fibrePermutationFun_in_field,σ.symm_apply_apply]
        rfl
      right_inv := fun z => by
        apply Subtype.ext
        change (σ (fibreRootInField t (fibrePermutationFun t σ.symm z)) : ℂ) = (z : ℂ)
        rw [fibrePermutationFun_in_field,σ.apply_symm_apply]
        rfl }
  map_one' := by
    apply Equiv.ext
    intro z
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    change ((σ*τ) (fibreRootInField t z) : ℂ) =
      (σ (fibreRootInField t (fibrePermutationFun t τ z)) : ℂ)
    rw [fibrePermutationFun_in_field]
    rfl

/-- Conjugation on the distinct roots of a complete fibre. -/
def fibreConjugation (t : ℝ) : Equiv.Perm ↥(fibreZeroSupport t) :=
  fibrePermutation t fullFibreZeroConjugation

/-- Every fibre permutation induced by the source field commutes with its conjugation pairing. -/
theorem fibrePermutation_commutes_conjugation (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    fibrePermutation t σ * fibreConjugation t = fibreConjugation t * fibrePermutation t σ := by
  have h : σ*fullFibreZeroConjugation = fullFibreZeroConjugation*σ :=
    fullFibreZeroConjugation_central σ
  change fibrePermutation t σ * fibrePermutation t fullFibreZeroConjugation =
    fibrePermutation t fullFibreZeroConjugation * fibrePermutation t σ
  rw [← map_mul,← map_mul,h]

/-- The full action retains every ordinate fibre simultaneously. -/
def allFibreAction :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      (∀ t : ℝ, Equiv.Perm ↥(fibreZeroSupport t)) where
  toFun σ t := fibrePermutation t σ
  map_one' := by funext t; exact (fibrePermutation t).map_one
  map_mul' σ τ := by funext t; exact (fibrePermutation t).map_mul σ τ

/-- The entire source Galois group is determined by its complete fibre permutations. -/
theorem allFibreAction_injective : Function.Injective allFibreAction := by
  intro σ τ he
  have hzero (q : XiZeroCopy) :
      σ (centeredZeroInFibreExtension q) = τ (centeredZeroInFibreExtension q) := by
    let t := (xiSpectralPoint q).re
    let z : ↥(fibreZeroSupport t) :=
      ⟨xiSpectralPoint q,Finset.mem_image.mpr ⟨q,(mem_ordinateFibreCopies t q).mpr rfl,rfl⟩⟩
    have ht := congrFun he t
    have hz := congrArg (fun e : Equiv.Perm ↥(fibreZeroSupport t) => e z) ht
    have hC := congrArg (fun x : ↥(fibreZeroSupport t) => (x : ℂ)) hz
    apply Subtype.ext
    exact hC
  have h := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := fullFibreZeroExtension) rfl (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom)
    (by rintro z ⟨q,rfl⟩; exact hzero q)
  exact AlgEquiv.ext fun z => DFunLike.congr_fun h z

/-- Analytic multiplicity as recorded by the complete source equation. -/
def fibreMultiplicity (t : ℝ) (z : ↥(fibreZeroSupport t)) : ℕ :=
  ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ)).rootMultiplicity (z : ℂ)

private theorem source_polynomial_map_aut (P : Polynomial fullFibreSourceField)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    (P.map (algebraMap fullFibreSourceField fullFibreZeroExtension)).map σ.toRingHom =
      P.map (algebraMap fullFibreSourceField fullFibreZeroExtension) := by
  rw [Polynomial.map_map]
  apply congrArg (fun f : fullFibreSourceField →+* fullFibreZeroExtension => P.map f)
  apply RingHom.ext
  intro a
  exact σ.commutes a

private theorem source_rootMultiplicity_aut (P : Polynomial fullFibreSourceField)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : fullFibreZeroExtension) :
    (P.map (algebraMap fullFibreSourceField fullFibreZeroExtension)).rootMultiplicity (σ z) =
      (P.map (algebraMap fullFibreSourceField fullFibreZeroExtension)).rootMultiplicity z := by
  have h := Polynomial.eq_rootMultiplicity_map
    (p := P.map (algebraMap fullFibreSourceField fullFibreZeroExtension))
    (f := σ.toRingHom) σ.injective z
  rw [source_polynomial_map_aut] at h
  exact h.symm

private theorem fibreMultiplicity_eq_in_field (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    fibreMultiplicity t z =
      ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField fullFibreZeroExtension)).rootMultiplicity
        (fibreRootInField t z) := by
  have h := Polynomial.eq_rootMultiplicity_map
    (p := (sourceFibrePolynomial t).map (algebraMap fullFibreSourceField fullFibreZeroExtension))
    (f := algebraMap fullFibreZeroExtension ℂ) (algebraMap fullFibreZeroExtension ℂ).injective
    (fibreRootInField t z)
  rw [Polynomial.map_map,← IsScalarTower.algebraMap_eq fullFibreSourceField fullFibreZeroExtension ℂ] at h
  exact h.symm

/-- Source automorphisms preserve analytic multiplicity on every complete fibre. -/
theorem fibrePermutation_preserves_multiplicity (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : ↥(fibreZeroSupport t)) :
    fibreMultiplicity t (fibrePermutation t σ z) = fibreMultiplicity t z := by
  rw [fibreMultiplicity_eq_in_field,fibreMultiplicity_eq_in_field]
  change ((sourceFibrePolynomial t).map
      (algebraMap fullFibreSourceField fullFibreZeroExtension)).rootMultiplicity
        (fibreRootInField t (fibrePermutationFun t σ z)) = _
  rw [fibrePermutationFun_in_field,source_rootMultiplicity_aut]

/-- Each finite permutation group carries its discrete topology. -/
instance fibrePermutationTopology (t : ℝ) :
    TopologicalSpace (Equiv.Perm ↥(fibreZeroSupport t)) := ⊥

instance fibrePermutationDiscrete (t : ℝ) :
    DiscreteTopology (Equiv.Perm ↥(fibreZeroSupport t)) := ⟨rfl⟩

private theorem fibrePermutation_kernel (t : ℝ) :
    ((fibrePermutation t).ker : Set
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)) =
    ⋂ z : ↥(fibreZeroSupport t),
      (MulAction.stabilizer
        (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
        (fibreRootInField t z) : Set _) := by
  ext σ
  simp only [Set.mem_iInter]
  change fibrePermutation t σ = 1 ↔ ∀ z, σ (fibreRootInField t z) = fibreRootInField t z
  constructor
  · intro h z
    have hz := DFunLike.congr_fun h z
    apply Subtype.ext
    exact congrArg (fun x : ↥(fibreZeroSupport t) => (x : ℂ)) hz
  · intro h
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun x : fullFibreZeroExtension => (x : ℂ)) (h z)

/-- A finite fibre permutation has an open kernel in the full Krull-topological Galois group. -/
theorem fibrePermutation_kernel_isOpen (t : ℝ) :
    IsOpen ((fibrePermutation t).ker : Set
      (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)) := by
  rw [fibrePermutation_kernel]
  exact isOpen_iInter_of_finite fun z =>
    stabilizer_isOpen_of_isIntegral (K := fullFibreSourceField) (L := fullFibreZeroExtension)
      (fibreRootInField t z)

/-- The complete finite-fibre action is continuous. -/
theorem fibrePermutation_continuous (t : ℝ) : Continuous (fibrePermutation t) := by
  apply continuous_of_continuousAt_one (fibrePermutation t)
  have h : ∀ᶠ σ in nhds (1 : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension),
      fibrePermutation t σ = 1 :=
    (fibrePermutation_kernel_isOpen t).mem_nhds (Subgroup.one_mem _)
  change Filter.Tendsto (fibrePermutation t) _ (nhds (fibrePermutation t 1))
  rw [map_one]
  exact tendsto_const_nhds.congr' (h.mono fun σ hσ => hσ.symm)

/-- The infinite product action is continuous without a height cutoff. -/
theorem allFibreAction_continuous : Continuous allFibreAction :=
  continuous_pi fun t => fibrePermutation_continuous t

/-- The actual arithmetic permutation image is closed in the product of all finite fibres. -/
theorem allFibreAction_range_isClosed : IsClosed (Set.range allFibreAction) := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  exact (isCompact_range allFibreAction_continuous).isClosed

/-- Finite fibre symmetries preserve both the conjugation pairing and analytic multiplicity. -/
def fibreDivisorSymmetries (t : ℝ) : Subgroup (Equiv.Perm ↥(fibreZeroSupport t)) where
  carrier := {τ | τ*fibreConjugation t = fibreConjugation t*τ ∧
    ∀ z, fibreMultiplicity t (τ z) = fibreMultiplicity t z}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    refine ⟨?_,fun z => ?_⟩
    · calc
        (a*b)*fibreConjugation t = a*(b*fibreConjugation t) := mul_assoc _ _ _
        _ = a*(fibreConjugation t*b) := by rw [hb.1]
        _ = (a*fibreConjugation t)*b := (mul_assoc _ _ _).symm
        _ = (fibreConjugation t*a)*b := by rw [ha.1]
        _ = fibreConjugation t*(a*b) := mul_assoc _ _ _
    · exact (ha.2 (b z)).trans (hb.2 z)
  inv_mem' {a} ha := by
    refine ⟨(show Commute a (fibreConjugation t) from ha.1).inv_left.eq,fun z => ?_⟩
    have he : a (a⁻¹ z) = z := by
      change (a*a⁻¹) z = z
      rw [mul_inv_cancel]
      rfl
    have h := ha.2 (a⁻¹ z)
    rw [he] at h
    exact h.symm

/-- The full source group acts through the finite divisor symmetries of each fibre. -/
def fibreDivisorAction (t : ℝ) :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      fibreDivisorSymmetries t where
  toFun σ := ⟨fibrePermutation t σ,
    fibrePermutation_commutes_conjugation t σ,fibrePermutation_preserves_multiplicity t σ⟩
  map_one' := Subtype.ext (fibrePermutation t).map_one
  map_mul' σ τ := Subtype.ext ((fibrePermutation t).map_mul σ τ)

/-- The arithmetic action in the product of all multiplicity-preserving conjugation centralizers. -/
def allFibreDivisorAction :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      (∀ t : ℝ, fibreDivisorSymmetries t) where
  toFun σ t := fibreDivisorAction t σ
  map_one' := by funext t; exact (fibreDivisorAction t).map_one
  map_mul' σ τ := by funext t; exact (fibreDivisorAction t).map_mul σ τ

/-- The constrained product action remains faithful on the entire infinite extension. -/
theorem allFibreDivisorAction_injective : Function.Injective allFibreDivisorAction := by
  intro σ τ h
  apply allFibreAction_injective
  funext t
  exact congrArg (fun f : ∀ t : ℝ, fibreDivisorSymmetries t => (f t).val) h

/-- Every finite divisor coordinate is continuous in the Krull topology. -/
theorem fibreDivisorAction_continuous (t : ℝ) : Continuous (fibreDivisorAction t) :=
  (fibrePermutation_continuous t).subtype_mk _

/-- The constrained infinite product action is continuous. -/
theorem allFibreDivisorAction_continuous : Continuous allFibreDivisorAction :=
  continuous_pi fun t => fibreDivisorAction_continuous t

/-- The source Galois group has closed image in the full product of finite divisor symmetry groups. -/
theorem allFibreDivisorAction_range_isClosed : IsClosed (Set.range allFibreDivisorAction) := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  exact (isCompact_range allFibreDivisorAction_continuous).isClosed

/-- A complete divisor permutation extends exactly when all its finite coordinate restrictions extend. -/
theorem allFibreDivisorAction_mem_range_iff (π : ∀ t : ℝ, fibreDivisorSymmetries t) :
    π ∈ Set.range allFibreDivisorAction ↔
      ∀ S : Finset ℝ, ∃ σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
        ∀ t ∈ S, fibreDivisorAction t σ = π t := by
  constructor
  · rintro ⟨σ,hσ⟩ S
    exact ⟨σ,fun t _ => congrFun hσ t⟩
  · intro h
    letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
    let C : ℝ → Set (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :=
      fun t => {σ | fibreDivisorAction t σ = π t}
    have hC : ∀ t, IsClosed (C t) := fun t =>
      isClosed_eq (fibreDivisorAction_continuous t) continuous_const
    have hfinite : ∀ S : Finset ℝ, (⋂ t ∈ S, C t).Nonempty := by
      intro S
      obtain ⟨σ,hσ⟩ := h S
      refine ⟨σ,Set.mem_iInter.mpr fun t => Set.mem_iInter.mpr fun ht => ?_⟩
      exact hσ t ht
    obtain ⟨σ,hσ⟩ := CompactSpace.iInter_nonempty hC hfinite
    refine ⟨σ,funext fun t => ?_⟩
    exact Set.mem_iInter.mp hσ t

/-- Finite-coordinate compatibility determines a unique automorphism of the whole zero field. -/
theorem allFibreDivisorAction_unique_extension (π : ∀ t : ℝ, fibreDivisorSymmetries t) :
    (∃! σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
      allFibreDivisorAction σ = π) ↔
      ∀ S : Finset ℝ, ∃ σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
        ∀ t ∈ S, fibreDivisorAction t σ = π t := by
  rw [← allFibreDivisorAction_mem_range_iff]
  constructor
  · rintro ⟨σ,hσ,_⟩
    exact ⟨σ,hσ⟩
  · rintro ⟨σ,hσ⟩
    exact ⟨σ,hσ,fun τ hτ => allFibreDivisorAction_injective (hτ.trans hσ.symm)⟩

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allFibreDivisorAction_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibrePermutation_preserves_multiplicity
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allFibreDivisorAction_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allFibreDivisorAction_range_isClosed
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allFibreDivisorAction_unique_extension
