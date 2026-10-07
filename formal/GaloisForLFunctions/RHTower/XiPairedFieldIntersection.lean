import GaloisForLFunctions.RHTower.XiPairedRadicalDegrees
import GaloisForLFunctions.HTGeometry.IndependentRadicalIntersections
import Mathlib.FieldTheory.Relrank

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective

def orientedMarkedField (b : Bool) : IntermediateField K Ω :=
  IntermediateField.adjoin K (Set.range fun n => pairedRoot (b, n))

def pairedMarkedField : IntermediateField K Ω :=
  IntermediateField.adjoin K (Set.range pairedRoot)

theorem orientedMarkedField_false : orientedMarkedField false = markedExtension := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨n, rfl⟩
    exact root_mem_markedField n
  · change markedField ≤ (orientedMarkedField false).toSubfield
    apply iSup_le
    intro k
    change Subfield.closure ((base : Set Ω) ∪ root '' Set.Iio k) ≤ _
    apply Subfield.closure_le.mpr
    rintro x (hx | ⟨n, _, rfl⟩)
    · obtain ⟨a, rfl⟩ := hx
      exact (orientedMarkedField false).algebraMap_mem a
    · exact IntermediateField.subset_adjoin K _ ⟨n, rfl⟩

theorem orientedMarkedField_le_paired (b : Bool) : orientedMarkedField b ≤ pairedMarkedField :=
  IntermediateField.adjoin.mono K _ _ (by rintro x ⟨n, rfl⟩; exact ⟨(b, n), rfl⟩)

theorem markedExtension_le_paired : markedExtension ≤ pairedMarkedField := by
  rw [← orientedMarkedField_false]
  exact orientedMarkedField_le_paired false

theorem pairedMarkedField_eq_sup :
    pairedMarkedField = orientedMarkedField false ⊔ orientedMarkedField true := by
  unfold pairedMarkedField orientedMarkedField
  rw [← IntermediateField.adjoin_union]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨b, n⟩, rfl⟩
    cases b with
    | false => exact Or.inl ⟨n, rfl⟩
    | true => exact Or.inr ⟨n, rfl⟩
  · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact ⟨(false, n), rfl⟩
    · exact ⟨(true, n), rfl⟩

/-- The actual original and reflected infinite radical fields intersect only in the base. -/
theorem marked_reflected_intersection :
    markedExtension ⊓ orientedMarkedField true = ⊥ := by
  have himage (b : Bool) : pairedRoot '' {j : Bool × ℕ | j.1 = b} =
      Set.range (fun n => pairedRoot (b, n)) := by
    ext x
    constructor
    · rintro ⟨⟨c, n⟩, hc, rfl⟩
      change c = b at hc
      subst c
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(b, n), rfl, rfl⟩
  rw [← orientedMarkedField_false]
  unfold orientedMarkedField
  rw [← himage false, ← himage true]
  apply independent_radical_sets_inf_eq_bot pairedRadicand pairedRoot (by norm_num)
    pairedRoot_sq paired_radicands_not_isSquare
  exact Set.disjoint_left.mpr fun j hj hk => Bool.false_ne_true (hj.symm.trans hk)

/-- Every inclusion of finite paired packets has exactly the missing-label degree. -/
theorem pairedFiniteField_relfinrank (S T : Finset (Bool × ℕ)) (hst : S ⊆ T) :
    (pairedFiniteField S).relfinrank (pairedFiniteField T) = 2 ^ (T.card - S.card) := by
  have hle : pairedFiniteField S ≤ pairedFiniteField T :=
    IntermediateField.adjoin.mono K _ _ (Set.image_mono hst)
  have hmul := IntermediateField.finrank_bot_mul_relfinrank hle
  rw [pairedFiniteField_finrank, pairedFiniteField_finrank] at hmul
  apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ S.card)
  rw [hmul, ← pow_add, Nat.add_sub_of_le (Finset.card_le_card hst)]

/-- Any field carrying a lift and containing the original tower contains its paired completion. -/
theorem pairedMarkedField_minimal (E : IntermediateField K Ω)
    (hmarked : markedExtension ≤ E) (φ : E →+* E)
    (hφ : ∀ a : K, φ (algebraMap K E a) = algebraMap K E (planeReflectEquiv 1 a)) :
    pairedMarkedField ≤ E := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨⟨b, n⟩, rfl⟩
  cases b with
  | false => exact hmarked (root_mem_markedField n)
  | true =>
    apply (root_mem_iff_isSquare (pairedRoot_sq (true, n)) E).mpr
    let u : E := ⟨root n, hmarked (root_mem_markedField n)⟩
    have hu : u * u = algebraMap K E (radicand n) := Subtype.ext (root_sq n)
    refine ⟨φ u, ?_⟩
    rw [← map_mul, hu, hφ, radicand, map_mul, planeReflectEquiv_xiElement]
    rfl

end RHTower.XiGlobalKummer
