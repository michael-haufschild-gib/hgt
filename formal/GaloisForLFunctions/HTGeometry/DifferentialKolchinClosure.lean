import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver
import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction
import Mathlib.Topology.Basic

/-!
# Kolchin closure and fixed fields

This file constructs the affine Kolchin closure directly from differential-polynomial zero loci.
The construction is relative to a differential coefficient field and does not assume a pre-existing
topology.  Its Galois connection with differential vanishing ideals gives extensivity, monotonicity,
idempotence, and the universal property of closure.

The final theorem is the fixed-field density step used in multiplication-tail arguments.  If every
point stabilizer is Kolchin closed, then a family of differential automorphisms and its Kolchin
closure have exactly the same fixed field.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Common zero locus of a family of differential polynomials over `K`. -/
def differentialZeroLocusOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (S : Set (DifferentialPolynomial ι K)) : Set (ι → L) :=
  {x | ∀ P ∈ S, differentialPolynomialEvalOver (K := K) x P = 0}

/-- Differential polynomials over `K` vanishing on every point of `X`. -/
def differentialVanishingIdealOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) : Ideal (DifferentialPolynomial ι K) where
  carrier := {P | ∀ x ∈ X, differentialPolynomialEvalOver (K := K) x P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ x hx
    simp [hP x hx, hQ x hx]
  smul_mem' := by
    intro P Q hQ x hx
    simp [hQ x hx]

@[simp]
theorem mem_differentialZeroLocusOver_iff
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {S : Set (DifferentialPolynomial ι K)} {x : ι → L} :
    x ∈ differentialZeroLocusOver S ↔
      ∀ P ∈ S, differentialPolynomialEvalOver (K := K) x P = 0 :=
  Iff.rfl

@[simp]
theorem mem_differentialVanishingIdealOver_iff
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {X : Set (ι → L)} {P : DifferentialPolynomial ι K} :
    P ∈ differentialVanishingIdealOver X ↔
      ∀ x ∈ X, differentialPolynomialEvalOver (K := K) x P = 0 :=
  Iff.rfl

/-- A differential vanishing ideal is stable under the total differential-polynomial
derivation. -/
theorem differentialPolynomialOverDerivation_mem_differentialVanishingIdealOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (X : Set (ι → L)) {P : DifferentialPolynomial ι K}
    (hP : P ∈ differentialVanishingIdealOver X) :
    differentialPolynomialOverDerivation ι K P ∈
      differentialVanishingIdealOver X := by
  intro x hx
  rw [differentialPolynomialEvalOver_derivation, hP x hx, map_zero]

/-- Zero loci and vanishing ideals form the defining Kolchin Galois connection. -/
theorem subset_differentialZeroLocusOver_iff
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {X : Set (ι → L)} {S : Set (DifferentialPolynomial ι K)} :
    X ⊆ differentialZeroLocusOver S ↔
      S ⊆ (differentialVanishingIdealOver (K := K) (L := L) X :
        Set (DifferentialPolynomial ι K)) :=
  by
    constructor
    · intro h P hP x hx
      exact h hx P hP
    · intro h x hx P hP
      exact h hP x hx

/-- Affine Kolchin closure over `K`, evaluated in the differential `K`-algebra `L`. -/
def kolchinClosureOver
    (K : Type*) {ι L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) : Set (ι → L) :=
  differentialZeroLocusOver
    (differentialVanishingIdealOver (K := K) (L := L) X :
      Set (DifferentialPolynomial ι K))

/-- A set is Kolchin closed when it is a common differential-polynomial zero locus. -/
def IsKolchinClosedOver
    (K : Type*) {ι L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) : Prop :=
  ∃ S : Set (DifferentialPolynomial ι K), differentialZeroLocusOver S = X

/-- Every set lies in its Kolchin closure. -/
theorem subset_kolchinClosureOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) : X ⊆ kolchinClosureOver K X := by
  intro x hx P hP
  exact hP x hx

/-- Kolchin closure is monotone. -/
theorem kolchinClosureOver_mono
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {X Y : Set (ι → L)} (hXY : X ⊆ Y) :
    kolchinClosureOver K X ⊆ kolchinClosureOver K Y := by
  intro x hx P hPY
  exact hx P fun y hy => hPY y (hXY hy)

/-- Every differential-polynomial zero locus is Kolchin closed. -/
theorem isKolchinClosedOver_differentialZeroLocusOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (S : Set (DifferentialPolynomial ι K)) :
    IsKolchinClosedOver K (L := L) (differentialZeroLocusOver S) :=
  ⟨S, rfl⟩

/-- Kolchin closure is itself Kolchin closed. -/
theorem isKolchinClosedOver_kolchinClosureOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) : IsKolchinClosedOver K (kolchinClosureOver K X) :=
  isKolchinClosedOver_differentialZeroLocusOver _

/-- Universal property: the Kolchin closure is contained in every closed superset. -/
theorem kolchinClosureOver_minimal
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {X Z : Set (ι → L)} (hXZ : X ⊆ Z) (hZ : IsKolchinClosedOver K Z) :
    kolchinClosureOver K X ⊆ Z := by
  obtain ⟨S, rfl⟩ := hZ
  intro x hx P hPS
  exact hx P fun y hy => hXZ hy P hPS

/-- Kolchin closure is idempotent. -/
theorem kolchinClosureOver_idempotent
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) :
    kolchinClosureOver K (kolchinClosureOver K X) = kolchinClosureOver K X := by
  apply Set.Subset.antisymm
  · exact kolchinClosureOver_minimal Set.Subset.rfl
      (isKolchinClosedOver_kolchinClosureOver X)
  · exact subset_kolchinClosureOver _

/-- Closed sets are exactly fixed points of Kolchin closure. -/
theorem isKolchinClosedOver_iff_kolchinClosureOver_eq
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {X : Set (ι → L)} :
    IsKolchinClosedOver K X ↔ kolchinClosureOver K X = X := by
  constructor
  · intro hX
    apply Set.Subset.antisymm
    · exact kolchinClosureOver_minimal Set.Subset.rfl hX
    · exact subset_kolchinClosureOver X
  · intro hX
    rw [← hX]
    exact isKolchinClosedOver_kolchinClosureOver X

/-- Empty affine locus is Kolchin closed. -/
theorem isKolchinClosedOver_empty
    {ι K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L] :
    IsKolchinClosedOver K (∅ : Set (ι → L)) := by
  refine ⟨{1}, ?_⟩
  ext x
  simp [differentialZeroLocusOver]

/-- Whole affine space is Kolchin closed. -/
theorem isKolchinClosedOver_univ
    {ι K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L] :
    IsKolchinClosedOver K (Set.univ : Set (ι → L)) := by
  refine ⟨∅, ?_⟩
  ext x
  simp [differentialZeroLocusOver]

/-- Finite unions of affine Kolchin-closed sets are Kolchin closed. -/
theorem IsKolchinClosedOver.union
    {ι K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    {X Y : Set (ι → L)}
    (hX : IsKolchinClosedOver K X) (hY : IsKolchinClosedOver K Y) :
    IsKolchinClosedOver K (X ∪ Y) := by
  classical
  obtain ⟨S, hS⟩ := hX
  obtain ⟨T, hT⟩ := hY
  let U : Set (DifferentialPolynomial ι K) :=
    {R | ∃ P ∈ S, ∃ Q ∈ T, R = P * Q}
  refine ⟨U, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxX : x ∈ X
    · exact Or.inl hxX
    · right
      have hxnotS : x ∉ differentialZeroLocusOver S := by
        rw [hS]
        exact hxX
      have hexP : ∃ P ∈ S,
          differentialPolynomialEvalOver (K := K) x P ≠ 0 := by
        simpa [differentialZeroLocusOver] using hxnotS
      obtain ⟨P, hPS, hPne⟩ := hexP
      rw [← hT]
      intro Q hQT
      have hPQ := hx (P * Q) ⟨P, hPS, Q, hQT, rfl⟩
      rw [map_mul] at hPQ
      exact (mul_eq_zero.mp hPQ).resolve_left hPne
  · rintro (hxX | hxY) R ⟨P, hPS, Q, hQT, rfl⟩
    · have hxS : x ∈ differentialZeroLocusOver S := by
        rw [hS]
        exact hxX
      rw [map_mul, hxS P hPS, zero_mul]
    · have hxT : x ∈ differentialZeroLocusOver T := by
        rw [hT]
        exact hxY
      rw [map_mul, hxT Q hQT, mul_zero]

/-- Arbitrary intersections of affine Kolchin-closed sets are Kolchin closed. -/
theorem isKolchinClosedOver_sInter
    {ι K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (C : Set (Set (ι → L)))
    (hC : ∀ X ∈ C, IsKolchinClosedOver K X) :
    IsKolchinClosedOver K (⋂₀ C) := by
  classical
  let equations : (X : C) → Set (DifferentialPolynomial ι K) :=
    fun X => Classical.choose (hC X.1 X.2)
  have hequations (X : C) :
      differentialZeroLocusOver (equations X) = X.1 :=
    Classical.choose_spec (hC X.1 X.2)
  let U : Set (DifferentialPolynomial ι K) :=
    {P | ∃ X : C, P ∈ equations X}
  refine ⟨U, ?_⟩
  ext x
  constructor
  · intro hx
    rw [Set.mem_sInter]
    intro X hXC
    let X' : C := ⟨X, hXC⟩
    change x ∈ X'.1
    rw [← hequations X']
    intro P hP
    exact hx P ⟨X', hP⟩
  · intro hx P hP
    obtain ⟨X, hPX⟩ := hP
    have hxX : x ∈ X.1 := (Set.mem_sInter.mp hx) X.1 X.2
    rw [← hequations X] at hxX
    exact hxX P hPX

/-- Affine Kolchin topology over `K`, evaluated in the differential field `L`. -/
@[implicit_reducible]
noncomputable def kolchinTopologicalSpace
    (K : Type*) {ι L : Type*} [Field K] [Field L] [Algebra K L] [Differential L] :
    TopologicalSpace (ι → L) :=
  TopologicalSpace.ofClosed
    {X | IsKolchinClosedOver K X}
    isKolchinClosedOver_empty
    (fun C hC => isKolchinClosedOver_sInter C fun _X hX => hC hX)
    (fun _ hX _ hY => hX.union hY)

/-- Closed sets in the constructed topology are exactly differential-polynomial zero loci. -/
theorem isClosed_kolchinTopologicalSpace_iff
    {ι K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) :
    @IsClosed (ι → L) (kolchinTopologicalSpace K) X ↔
      IsKolchinClosedOver K X := by
  letI : TopologicalSpace (ι → L) := kolchinTopologicalSpace K
  change IsClosed X ↔ IsKolchinClosedOver K X
  constructor
  · intro hX
    have hopen := hX.isOpen_compl
    change IsKolchinClosedOver K Xᶜᶜ at hopen
    simpa only [compl_compl] using hopen
  · intro hX
    refine ⟨?_⟩
    change IsKolchinClosedOver K Xᶜᶜ
    simpa only [compl_compl] using hX

/-- Topological closure in the affine Kolchin topology is the vanishing-ideal closure. -/
theorem closure_kolchinTopologicalSpace_eq_kolchinClosureOver
    {ι K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (X : Set (ι → L)) :
    @closure (ι → L) (kolchinTopologicalSpace K) X = kolchinClosureOver K X := by
  letI : TopologicalSpace (ι → L) := kolchinTopologicalSpace K
  change closure X = kolchinClosureOver K X
  apply Set.Subset.antisymm
  · apply closure_minimal (subset_kolchinClosureOver X)
    rw [isClosed_kolchinTopologicalSpace_iff]
    exact isKolchinClosedOver_kolchinClosureOver X
  · apply kolchinClosureOver_minimal subset_closure
    rw [← isClosed_kolchinTopologicalSpace_iff]
    exact isClosed_closure

/-- The subfield fixed by every differential translation labelled by a point of `S`. -/
def differentialTranslationFixedField
    {K L A : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (translation : A → DifferentialAlgEquiv K L) (S : Set A) :
    IntermediateField K L where
  carrier := {z | ∀ a ∈ S, (translation a).toAlgEquiv z = z}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, hx a ha, hy a ha]
  mul_mem' := by
    intro x y hx hy a ha
    rw [map_mul, hx a ha, hy a ha]
  inv_mem' := by
    intro x hx a ha
    rw [map_inv₀, hx a ha]
  algebraMap_mem' := by
    intro c a ha
    exact (translation a).toAlgEquiv.commutes c

@[simp]
theorem mem_differentialTranslationFixedField_iff
    {K L A : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    {translation : A → DifferentialAlgEquiv K L} {S : Set A} {z : L} :
    z ∈ differentialTranslationFixedField translation S ↔
      ∀ a ∈ S, (translation a).toAlgEquiv z = z :=
  Iff.rfl

/-- A point-labelled fixed field agrees with mathlib's subgroup fixed field when the translated
point set is exactly that subgroup. -/
theorem differentialTranslationFixedField_eq_fixedField_of_image_eq
    {K L A : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (translation : A → DifferentialAlgEquiv K L) (S : Set A)
    (G : Subgroup (L ≃ₐ[K] L))
    (himage : (fun a => (translation a).toAlgEquiv) '' S = (G : Set (L ≃ₐ[K] L))) :
    differentialTranslationFixedField translation S =
      IntermediateField.fixedField G := by
  ext z
  rw [mem_differentialTranslationFixedField_iff,
    IntermediateField.mem_fixedField_iff]
  constructor
  · intro hz σ hσ
    have hσimage : σ ∈ (fun a => (translation a).toAlgEquiv) '' S := by
      rw [himage]
      exact hσ
    obtain ⟨a, ha, rfl⟩ := hσimage
    exact hz a ha
  · intro hz a ha
    apply hz (translation a).toAlgEquiv
    change (translation a).toAlgEquiv ∈ (G : Set (L ≃ₐ[K] L))
    rw [← himage]
    exact ⟨a, ha, rfl⟩

/-- **Kolchin-dense translations have the same fixed field as their closure.**

The only geometric input is the exact one used in the paper proof: for each field element, its
translation stabilizer must be a differential-polynomial closed set. -/
theorem differentialTranslationFixedField_eq_of_kolchinClosureOver_eq
    {ι K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L]
    (translation : (ι → K) → DifferentialAlgEquiv K L)
    (S T : Set (ι → K))
    (hclosure : kolchinClosureOver K S = T)
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    differentialTranslationFixedField translation S =
      differentialTranslationFixedField translation T := by
  ext z
  constructor
  · intro hz a ha
    let Z : Set (ι → K) := {b | (translation b).toAlgEquiv z = z}
    have hSZ : S ⊆ Z := fun b hb => hz b hb
    have hTZ : T ⊆ Z := by
      rw [← hclosure]
      exact kolchinClosureOver_minimal hSZ (hclosed z)
    exact hTZ ha
  · intro hz a ha
    apply hz a
    rw [← hclosure]
    exact subset_kolchinClosureOver S ha

end

end GaloisForLFunctions.HTGeometry
