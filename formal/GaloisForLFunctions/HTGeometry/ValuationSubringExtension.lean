import GaloisForLFunctions.HTGeometry.CriticalNormalClosureSchurValuation
import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex

/-!
# Exact extension of a valuation subring along a field homomorphism

Krull domination extends any valuation ring along a field homomorphism.  Locality of the induced
map proves that contraction is exactly the original valuation ring, not merely a containing local
subring.  This is the field-theoretic prolongation used at every terminal-inward cascade step.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every valuation subring extends along a field homomorphism, with exact contraction. -/
theorem exists_valuationSubring_extension_comap_eq
    {E K : Type*} [Field E] [Field K]
    (A : ValuationSubring E) (f : E →+* K) :
    ∃ B : ValuationSubring K, B.comap f = A := by
  obtain ⟨B, hmem, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (f.comp A.subtype)
  letI : IsLocalHom ((f.comp A.subtype).codRestrict B.toSubring hmem) := hlocal
  exact ⟨B, ValuationSubring.comap_eq_of_local_codRestrict A B f hmem⟩

/-- Membership of every source element is preserved exactly by a chosen prolongation. -/
theorem exists_valuationSubring_extension_mem_iff
    {E K : Type*} [Field E] [Field K]
    (A : ValuationSubring E) (f : E →+* K) :
    ∃ B : ValuationSubring K, ∀ x : E, f x ∈ B ↔ x ∈ A := by
  obtain ⟨B, hB⟩ := exists_valuationSubring_extension_comap_eq A f
  refine ⟨B, fun x => ?_⟩
  change x ∈ B.comap f ↔ x ∈ A
  rw [hB]

/-- A subfield contained in a valuation ring embeds canonically into its residue field. -/
noncomputable def valuationSubringResidueEmbedding
    {L E : Type*} [Field L] [Field E]
    (A : ValuationSubring E) (f : L →+* E) (hmem : ∀ x, f x ∈ A) :
    L →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp (f.codRestrict A.toSubring hmem)

/-- Residue reduction retains every contained subfield faithfully. -/
theorem valuationSubringResidueEmbedding_injective
    {L E : Type*} [Field L] [Field E]
    (A : ValuationSubring E) (f : L →+* E) (hmem : ∀ x, f x ∈ A) :
    Function.Injective (valuationSubringResidueEmbedding A f hmem) :=
  RingHom.injective _

/-- A valuation on a larger field that is trivial on a base field is automatically trivial on
every algebraic intermediate field.  Equivalently, an algebraic intermediate field is entirely
contained in the valuation ring. -/
theorem valuationSubring_contains_algebraic_tower
    {F L K : Type*} [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra L K] [Algebra F K] [IsScalarTower F L K]
    (A : ValuationSubring K) (hF : ∀ x : F, algebraMap F K x ∈ A)
    (halg : Algebra.IsAlgebraic F L) :
    ∀ x : L, algebraMap L K x ∈ A := by
  letI : Algebra.IsAlgebraic F L := halg
  intro x
  apply ValuationInertia.mem_of_isIntegral A hF
  exact (isAlgebraic_iff_isIntegral.mp
    (Algebra.IsAlgebraic.isAlgebraic x)).algebraMap

/-- A valuation on one field in a common overfield can be prolonged while retaining every
algebraic field over a base on which the original valuation is trivial.  This is the exact valued
amalgamation needed for terminal-inward cascade places. -/
theorem exists_valuationSubring_extension_containing_algebraic_tower
    {F E L K : Type*} [Field F] [Field E] [Field L] [Field K]
    [Algebra F E] [Algebra F L] [Algebra E K] [Algebra L K] [Algebra F K]
    [IsScalarTower F E K] [IsScalarTower F L K]
    (A : ValuationSubring E) (hF : ∀ x : F, algebraMap F E x ∈ A)
    (halg : Algebra.IsAlgebraic F L) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧
      ∀ x : L, algebraMap L K x ∈ B := by
  obtain ⟨B, hB⟩ :=
    exists_valuationSubring_extension_comap_eq A (algebraMap E K)
  have hFK : ∀ x : F, algebraMap F K x ∈ B := by
    intro x
    rw [IsScalarTower.algebraMap_apply F E K]
    change algebraMap F E x ∈ B.comap (algebraMap E K)
    rw [hB]
    exact hF x
  exact ⟨B, hB,
    valuationSubring_contains_algebraic_tower B hFK halg⟩

/-- Refine a valuation ring by a valuation ring of its residue field. -/
noncomputable def compositeValuationSubring
    {K : Type*} [Field K] (A : ValuationSubring K)
    (B : ValuationSubring (IsLocalRing.ResidueField A)) : ValuationSubring K where
  toSubring :=
    { carrier := {x | ∃ hx : x ∈ A,
          IsLocalRing.residue A (⟨x, hx⟩ : A) ∈ B}
      zero_mem' := by
        refine ⟨A.zero_mem, ?_⟩
        have heq : (⟨0, A.zero_mem⟩ : A) = 0 := Subtype.ext rfl
        rw [heq, map_zero]
        exact B.zero_mem
      one_mem' := by
        refine ⟨A.one_mem, ?_⟩
        have heq : (⟨1, A.one_mem⟩ : A) = 1 := Subtype.ext rfl
        rw [heq, map_one]
        exact B.one_mem
      add_mem' := by
        rintro x y ⟨hx, hxB⟩ ⟨hy, hyB⟩
        refine ⟨A.toSubring.add_mem hx hy, ?_⟩
        have heq : (⟨x + y, A.toSubring.add_mem hx hy⟩ : A) =
            (⟨x, hx⟩ : A) + ⟨y, hy⟩ := Subtype.ext rfl
        rw [heq, map_add]
        exact B.toSubring.add_mem hxB hyB
      mul_mem' := by
        rintro x y ⟨hx, hxB⟩ ⟨hy, hyB⟩
        refine ⟨A.toSubring.mul_mem hx hy, ?_⟩
        have heq : (⟨x * y, A.toSubring.mul_mem hx hy⟩ : A) =
            (⟨x, hx⟩ : A) * ⟨y, hy⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact B.toSubring.mul_mem hxB hyB
      neg_mem' := by
        rintro x ⟨hx, hxB⟩
        refine ⟨A.toSubring.neg_mem hx, ?_⟩
        have heq : (⟨-x, A.toSubring.neg_mem hx⟩ : A) = -(⟨x, hx⟩ : A) :=
          Subtype.ext rfl
        rw [heq, map_neg]
        exact B.toSubring.neg_mem hxB }
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ A
    · let xa : A := ⟨x, hx⟩
      let y := IsLocalRing.residue A xa
      rcases B.mem_or_inv_mem y with hy | hyinv
      · exact Or.inl ⟨hx, hy⟩
      · by_cases hy0 : y = 0
        · exact Or.inl ⟨hx, by change y ∈ B; rw [hy0]; exact B.zero_mem⟩
        · have hunit : IsUnit xa := by
            by_contra hnu
            have hmax : xa ∈ IsLocalRing.maximalIdeal A :=
              (IsLocalRing.mem_maximalIdeal xa).2 hnu
            exact hy0 ((IsLocalRing.residue_eq_zero_iff xa).2 hmax)
          obtain ⟨u, hu⟩ := hunit
          have huval : (u : A) = xa := hu
          have hxinvA : x⁻¹ ∈ A := by
            have huv : ((↑(u⁻¹) : A) : K) = x⁻¹ := by
              have huK : A.subtype (u : A) = x := congrArg A.subtype huval
              change A.subtype (↑(u⁻¹) : A) = x⁻¹
              rw [map_units_inv A.subtype u, huK]
            rw [← huv]
            exact (↑(u⁻¹) : A).2
          refine Or.inr ⟨hxinvA, ?_⟩
          have hres : IsLocalRing.residue A (⟨x⁻¹, hxinvA⟩ : A) = y⁻¹ := by
            have huv : (⟨x⁻¹, hxinvA⟩ : A) = (↑(u⁻¹) : A) := by
              apply Subtype.ext
              have huK : A.subtype (u : A) = x := congrArg A.subtype huval
              change x⁻¹ = A.subtype (↑(u⁻¹) : A)
              rw [map_units_inv A.subtype u, huK]
            rw [huv]
            have hresu : IsLocalRing.residue A (u : A) = y :=
              congrArg (IsLocalRing.residue A) huval
            rw [map_units_inv (IsLocalRing.residue A) u, hresu]
          rw [hres]
          exact hyinv
    · have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        exact hx A.zero_mem
      let xi : A := ⟨x⁻¹, hxinv⟩
      have hnotunit : ¬ IsUnit xi := by
        intro hu
        obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
        have hzK : x⁻¹ * (z : K) = 1 := congrArg Subtype.val hz
        have hzx : (z : K) = x := by
          calc
            (z : K) = 1 / x⁻¹ :=
              (eq_div_iff (inv_ne_zero hx0)).2 (by simpa [mul_comm] using hzK)
            _ = x := by simp
        have : x ∈ A := by rw [← hzx]; exact z.2
        exact hx this
      have hmax : xi ∈ IsLocalRing.maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal xi).2 hnotunit
      have hreszero : IsLocalRing.residue A xi = 0 :=
        (IsLocalRing.residue_eq_zero_iff xi).2 hmax
      exact Or.inr ⟨hxinv, by rw [hreszero]; exact B.zero_mem⟩

/-- Membership in a composite valuation is parent integrality followed by residue integrality. -/
theorem mem_compositeValuationSubring_iff
    {K : Type*} [Field K] (A : ValuationSubring K)
    (B : ValuationSubring (IsLocalRing.ResidueField A)) (x : K) :
    x ∈ compositeValuationSubring A B ↔
      ∃ hx : x ∈ A, IsLocalRing.residue A (⟨x, hx⟩ : A) ∈ B :=
  Iff.rfl

/-- Composite refinement never enlarges its parent valuation ring. -/
theorem compositeValuationSubring_le
    {K : Type*} [Field K] (A : ValuationSubring K)
    (B : ValuationSubring (IsLocalRing.ResidueField A)) :
    compositeValuationSubring A B ≤ A := by
  intro x hx
  exact hx.choose

/-- For a parent-integral element, composite membership is exactly residue membership. -/
theorem mem_compositeValuationSubring_iff_residue_mem
    {K : Type*} [Field K] (A : ValuationSubring K)
    (B : ValuationSubring (IsLocalRing.ResidueField A)) (x : K) (hx : x ∈ A) :
    x ∈ compositeValuationSubring A B ↔
      IsLocalRing.residue A (⟨x, hx⟩ : A) ∈ B := by
  constructor
  · rintro ⟨hx', hB⟩
    convert hB using 1
  · exact fun hB => ⟨hx, hB⟩

/-- Composite integrality on a contained subfield is exactly integrality of its residue image. -/
theorem mem_compositeValuationSubring_map_iff
    {L K : Type*} [Field L] [Field K]
    (A : ValuationSubring K) (B : ValuationSubring (IsLocalRing.ResidueField A))
    (f : L →+* K) (hmem : ∀ x, f x ∈ A) (x : L) :
    f x ∈ compositeValuationSubring A B ↔
      valuationSubringResidueEmbedding A f hmem x ∈ B := by
  exact mem_compositeValuationSubring_iff_residue_mem A B (f x) (hmem x)

/-- If the residue refinement contains a subfield's residue image, the composite valuation still
contains that whole subfield. -/
theorem compositeValuationSubring_contains_subfield
    {L K : Type*} [Field L] [Field K]
    (A : ValuationSubring K) (B : ValuationSubring (IsLocalRing.ResidueField A))
    (f : L →+* K) (hmem : ∀ x, f x ∈ A)
    (hres : ∀ x, valuationSubringResidueEmbedding A f hmem x ∈ B) :
    ∀ x, f x ∈ compositeValuationSubring A B := by
  intro x
  exact (mem_compositeValuationSubring_map_iff A B f hmem x).2 (hres x)

/-- A valuation of a retained residue subfield can be prolonged and composed with the parent
valuation.  The resulting finer valuation lies below the parent and contracts exactly to the
prescribed valuation of the retained field. -/
theorem exists_compositeValuationSubring_comap_eq
    {F K : Type*} [Field F] [Field K]
    (A : ValuationSubring F) (B : ValuationSubring K)
    (f : F →+* K) (hmem : ∀ x, f x ∈ B) :
    ∃ C : ValuationSubring K, C ≤ B ∧ C.comap f = A := by
  let e := valuationSubringResidueEmbedding B f hmem
  obtain ⟨D, hD⟩ := exists_valuationSubring_extension_comap_eq A e
  refine ⟨compositeValuationSubring B D,
    compositeValuationSubring_le B D, ?_⟩
  apply SetLike.ext
  intro x
  change f x ∈ compositeValuationSubring B D ↔ x ∈ A
  rw [mem_compositeValuationSubring_map_iff B D f hmem x]
  change x ∈ D.comap e ↔ x ∈ A
  rw [hD]

end

end GaloisForLFunctions.HTGeometry
