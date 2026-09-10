import GaloisForLFunctions.HTGeometry.FrobeniusGaloisObservation
import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw

/-!
# Frobenius approximation and exact recovery

The fixed-point laws of arXiv:2609.09529, Proposition 3.13, give a
property-level characterization of the corpus's kernel refinement,
range factorization, joint repair, and heterogeneous observation families.
-/
namespace GaloisForLFunctions.HTGeometry
open FrobeniusGalois
variable {X Y Z C : Type*}

/-- Kernel refinement is exactly comparison of all possibility operators. -/
theorem kernelRefines_iff_upper_le (q : X → Y) (r : X → Z) :
    KernelRefines q r ↔ ∀ S : Set X, upper q S ⊆ upper r S := by
  constructor
  · intro h S x hx
    obtain ⟨y, hy, he⟩ := hx
    exact ⟨y, hy, h y x he⟩
  · intro h x y he
    obtain ⟨z, hz, hr⟩ := h {x} ⟨x, rfl, he⟩
    have hz' : z = x := hz
    exact hz' ▸ hr

/-- The dual certainty criterion reverses the comparison. -/
theorem kernelRefines_iff_lower_le (q : X → Y) (r : X → Z) :
    KernelRefines q r ↔ ∀ S : Set X, lower r S ⊆ lower q S := by
  constructor
  · intro h S x hx y hy
    exact hx y (h y x hy)
  · intro h x y he
    have hx : x ∈ lower r (r ⁻¹' {r x}) := fun z hz => hz
    have hy := h (r ⁻¹' {r x}) hx y he.symm
    exact hy.symm

/-- A target is recoverable exactly when every target property is a fixed point. -/
theorem factorsThroughRange_iff_upper_preimage (q : X → Y) (r : X → Z) :
    FactorsThroughRange q r ↔ ∀ T : Set Z, upper q (r ⁻¹' T) = r ⁻¹' T := by
  rw [factorsThroughRange_iff_kernelRefines]
  constructor
  · intro h T
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, he⟩
      change r x ∈ T
      rwa [← h y x he]
    · exact subset_upper q _
  · intro h x y he
    have hy : y ∈ upper q (r ⁻¹' {r x}) := ⟨x, rfl, he⟩
    rw [h] at hy
    exact hy.symm

/-- No target-property ambiguity is equivalent to exact target recovery. -/
theorem factorsThroughRange_iff_no_uncertainty (q : X → Y) (r : X → Z) :
    FactorsThroughRange q r ↔
      ∀ T : Set Z, lower q (r ⁻¹' T) = upper q (r ⁻¹' T) := by
  rw [factorsThroughRange_iff_upper_preimage]
  constructor
  · intro h T
    rw [h T, (lower_fixed_iff q _).mpr (h T)]
  · intro h T
    exact (upper_fixed_iff q _).mpr ((lower_eq_upper_iff q _).mp (h T))

/-- A single property is observable exactly when its truth value factors through observations. -/
theorem property_factorsThroughRange_iff (q : X → Y) (S : Set X) :
    FactorsThroughRange q (fun x => x ∈ S) ↔ upper q S = S := by
  rw [factorsThroughRange_iff_kernelRefines]
  constructor
  · intro h
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, he⟩
      have hp : (y ∈ S) = (x ∈ S) := h y x he
      exact hp ▸ hy
    · exact subset_upper q S
  · intro h x y he
    apply propext
    constructor
    · intro hx
      have hy : y ∈ upper q S := ⟨x, hx, he⟩
      rwa [h] at hy
    · intro hy
      have hx : x ∈ upper q S := ⟨y, hy, he.symm⟩
      rwa [h] at hx

/-- Joint repair has an exact Frobenius fixed-point characterization. -/
theorem jointlyRecovers_iff_no_uncertainty (q : X → Y) (r : X → Z) (t : X → C) :
    JointlyRecovers q r t ↔
      ∀ S : Set C, lower (jointObservation q r) (t ⁻¹' S) =
        upper (jointObservation q r) (t ⁻¹' S) := by
  rw [← factorsThroughRange_iff_no_uncertainty, factorsThroughRange_iff_kernelRefines]
  constructor
  · intro h x y he
    exact h x y (congrArg Prod.fst he) (congrArg Prod.snd he)
  · intro h x y hq hr
    exact h x y (Prod.ext hq hr)

/-- Adding a channel decreases the possible region. -/
theorem jointObservation_upper_subset (q : X → Y) (r : X → Z) (S : Set X) :
    upper (jointObservation q r) S ⊆ upper q S ∩ upper r S := by
  rintro x ⟨y, hy, he⟩
  exact ⟨⟨y, hy, congrArg Prod.fst he⟩, y, hy, congrArg Prod.snd he⟩

/-- Adding a channel enlarges the certain region. -/
theorem jointObservation_lower_superset (q : X → Y) (r : X → Z) (S : Set X) :
    lower q S ∪ lower r S ⊆ lower (jointObservation q r) S := by
  intro x hx y he
  exact hx.elim (fun h => h y (congrArg Prod.fst he))
    (fun h => h y (congrArg Prod.snd he))

/-- A target supplied as a channel has no residual ambiguity. -/
theorem targetChannel_exact (q : X → Y) (t : X → C) (S : Set C) :
    lower (jointObservation q t) (t ⁻¹' S) = upper (jointObservation q t) (t ⁻¹' S) :=
  (jointlyRecovers_iff_no_uncertainty q t t).mp (targetChannel_jointlyRecovers q t) S

/-- Arbitrarily many heterogeneous channels satisfy the same certainty criterion. -/
theorem observationFamilyRecovers_iff_no_uncertainty
    {J : Type*} {B : J → Type*} (obs : ∀ j, X → B j) (t : X → C) :
    ObservationFamilyRecovers obs t ↔
      ∀ S : Set C, lower (observationRecord obs) (t ⁻¹' S) =
        upper (observationRecord obs) (t ⁻¹' S) := by
  rw [observationFamilyRecovers_iff_factorsThroughRecordRange,
    factorsThroughRange_iff_no_uncertainty]

/-- Quotient possibility is precisely saturation under the source equivalence relation. -/
theorem quotientObservation_upper (r : Setoid X) (S : Set X) :
    upper (quotientObservation r) S = {x | ∃ y ∈ S, r y x} := by
  ext x
  simp only [upper, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, (mapKernelPair_quotientObservation_iff r y x).mp he⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, (mapKernelPair_quotientObservation_iff r y x).mpr he⟩

/-- Quotient certainty is universal validity on an equivalence class. -/
theorem quotientObservation_lower (r : Setoid X) (S : Set X) :
    lower (quotientObservation r) S = {x | ∀ y, r y x → y ∈ S} := by
  ext x
  constructor
  · intro h y hy
    exact h y ((mapKernelPair_quotientObservation_iff r y x).mpr hy)
  · intro h y hy
    exact h y ((mapKernelPair_quotientObservation_iff r y x).mp hy)

/-- Equivalence-class saturation automatically satisfies the meet Frobenius law. -/
theorem quotientObservation_frobenius (r : Setoid X) (S T : Set X) :
    upper (quotientObservation r) (S ∩ upper (quotientObservation r) T) =
      upper (quotientObservation r) S ∩ upper (quotientObservation r) T :=
  upper_inter_upper _ S T

end GaloisForLFunctions.HTGeometry
