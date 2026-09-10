import GaloisForLFunctions.HTGeometry.FrobeniusGaloisObservation

/-!
# Sharp limits of Frobenius approximation

The meet-Frobenius law in arXiv:2609.09529, Definition 3.8, is weaker
than unrestricted meet preservation. For observation fibers, the latter
holds exactly for injective observations. Thus every information loss
has a precise obstruction, and the surviving law has an exact boundary.
-/
namespace GaloisForLFunctions.HTGeometry.FrobeniusGalois
variable {X Y Z : Type*}

/-- Full meet preservation by possibility is equivalent to lossless observation. -/
theorem upper_preserves_inter_iff (q : X → Y) :
    (∀ S T : Set X, upper q (S ∩ T) = upper q S ∩ upper q T) ↔
      Function.Injective q := by
  constructor
  · intro h x y he
    have hx : x ∈ upper q {x} ∩ upper q {y} :=
      ⟨⟨x, rfl, rfl⟩, y, rfl, he.symm⟩
    rw [← h {x} {y}] at hx
    obtain ⟨z, ⟨hzx, hzy⟩, _⟩ := hx
    exact hzx.symm.trans hzy
  · intro hinj S T
    have hfixed : ∀ U : Set X, upper q U = U := by
      intro U
      apply Set.Subset.antisymm
      · rintro x ⟨y, hy, he⟩
        exact hinj he ▸ hy
      · exact subset_upper q U
    rw [hfixed, hfixed, hfixed]

/-- Universal join preservation by certainty has the same sharp boundary. -/
theorem lower_preserves_union_iff (q : X → Y) :
    (∀ S T : Set X, lower q (S ∪ T) = lower q S ∪ lower q T) ↔
      Function.Injective q := by
  classical
  constructor
  · intro h x y he
    have hx : x ∈ lower q ({x} ∪ {x}ᶜ) := by
      intro z _
      exact Classical.em (z ∈ ({x} : Set X))
    rw [h] at hx
    rcases hx with hp | hn
    · exact (hp y he.symm).symm
    · exact False.elim (hn x rfl rfl)
  · intro hinj S T
    have hfixed : ∀ U : Set X, lower q U = U := by
      intro U
      apply Set.Subset.antisymm (lower_subset q U)
      intro x hx y he
      exact (hinj he).symm ▸ hx
    rw [hfixed, hfixed, hfixed]

/-- Possibility of a singleton retains exactly its observation value. -/
theorem upper_singleton_eq_iff (q : X → Y) (x y : X) :
    upper q {x} = upper q {y} ↔ q x = q y := by
  constructor
  · intro h
    have hx : x ∈ upper q {x} := ⟨x, rfl, rfl⟩
    rw [h] at hx
    obtain ⟨z, hz, he⟩ := hx
    have hz' : z = y := hz
    exact (hz' ▸ he).symm
  · intro h
    ext z
    constructor
    · rintro ⟨w, hw, he⟩
      have hw' : w = x := hw
      exact ⟨y, rfl, h.symm.trans (hw' ▸ he)⟩
    · rintro ⟨w, hw, he⟩
      have hw' : w = y := hw
      exact ⟨x, rfl, h.trans (hw' ▸ he)⟩

/-- Two presentations yield the same Frobenius algebra exactly when they erase the same pairs. -/
theorem upper_operators_eq_iff (q : X → Y) (r : X → Z) :
    upper q = upper r ↔ ∀ x y, q x = q y ↔ r x = r y := by
  constructor
  · intro h x y
    rw [← upper_singleton_eq_iff q, ← upper_singleton_eq_iff r, h]
  · intro h
    funext S
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, (h y x).mp he⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, (h y x).mpr he⟩

/-- The certainty operator contains exactly the same information as the possibility operator. -/
theorem lower_operators_eq_iff (q : X → Y) (r : X → Z) :
    lower q = lower r ↔ upper q = upper r := by
  constructor
  · intro h
    funext S
    have hc := congrArg (fun f : Set X → Set X => (f Sᶜ)ᶜ) h
    simpa [lower_compl] using hc
  · intro h
    funext S
    have hc := congrArg (fun f : Set X → Set X => (f Sᶜ)ᶜ) h
    simpa [upper_compl] using hc
end GaloisForLFunctions.HTGeometry.FrobeniusGalois
