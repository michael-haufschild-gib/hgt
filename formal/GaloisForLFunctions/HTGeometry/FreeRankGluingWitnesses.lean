import GaloisForLFunctions.HTGeometry.DifferentialMatroidGluing

/-!
# A free model realizes the gluing interfaces jointly

Cardinality is a rank function: it is monotone, submodular with equality, and never exceeds
cardinality.  In that free model every coordinate set is independent and every permutation is a rank
automorphism, so the three star-gluing interfaces reduce to geometry: the fibrewise shift of
`iota × ℤ` has free translates along the integer height, and it is rank neutral on any set it fixes.

Taking every edge incident to a single vertex makes the off-star empty, so all four hypotheses of the
graph-gluing theorem hold simultaneously and its conclusion is a true statement about a nonempty
coordinate set.  The gluing layer is therefore not vacuous.
-/

namespace GaloisForLFunctions.MatroidGluing

open Finset

/-! ## The free rank -/

/-- Cardinality as a rank function. -/
def freeRank (Ω : Type*) [DecidableEq Ω] : Rank Ω where
  ρ := Finset.card
  mono h := Finset.card_le_card h
  submodular s t := le_of_eq (Finset.card_union_add_card_inter s t)
  ρ_le_card _ := le_rfl

variable {Ω : Type*} [DecidableEq Ω]

@[simp] theorem freeRank_ρ (s : Finset Ω) : (freeRank Ω).ρ s = s.card := rfl

/-- Every coordinate set is independent in the free model. -/
theorem freeRank_indepSet (S : Set Ω) : (freeRank Ω).IndepSet S := fun _ _ => rfl

/-- Every permutation is a rank automorphism of the free model. -/
theorem freeRank_mem_rankAutSubgroup (e : Equiv.Perm Ω) :
    e ∈ (freeRank Ω).rankAutSubgroup := by
  intro s
  simp only [freeRank_ρ]
  exact Finset.card_image_of_injective s e.injective

omit [DecidableEq Ω] in
/-- A fixed point of a permutation is a fixed point of every integer power. -/
theorem zpow_apply_of_fixed {σ : Equiv.Perm Ω} {y : Ω} (h : σ y = y) (n : ℤ) :
    (σ ^ n) y = y := by
  have hinv : σ⁻¹ y = y := by
    conv_lhs => rw [← h]
    simp
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, Equiv.Perm.mul_apply, h, ih]
  | pred k ih => rw [zpow_sub_one, Equiv.Perm.mul_apply, hinv, ih]

/-- A permutation that fixes a set pointwise is rank neutral on it. -/
theorem freeRank_crossNeutral_of_fixed {σ : Equiv.Perm Ω} {S : Set Ω}
    (hfix : ∀ x ∈ S, σ x = x) : (freeRank Ω).CrossNeutral σ S := by
  intro t ht n
  have himage : t.image ⇑(σ ^ n) = t := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyS : y ∈ S := ht (by simpa using hy)
      rw [zpow_apply_of_fixed (hfix y hyS) n]
      exact hy
    · intro hx
      have hxS : x ∈ S := ht (by simpa using hx)
      exact ⟨x, hx, zpow_apply_of_fixed (hfix x hxS) n⟩
  rw [himage, Finset.union_self]

/-! ## The fibrewise shift -/

/-- The unit shift of the integer fibre of `iota × ℤ`. -/
def fibreShift (iota : Type*) : Equiv.Perm (iota × ℤ) :=
  (Equiv.refl iota).prodCongr (Equiv.addRight (1 : ℤ))

@[simp] theorem fibreShift_apply (iota : Type*) (x : iota × ℤ) :
    fibreShift iota x = (x.1, x.2 + 1) := rfl

theorem fibreShift_zpow_apply (iota : Type*) (n : ℤ) :
    ∀ x : iota × ℤ, (fibreShift iota ^ n) x = (x.1, x.2 + n) := by
  induction n using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [zpow_add_one, Equiv.Perm.mul_apply, fibreShift_apply, ih]
      simp only [Prod.mk.injEq, true_and]
      ring
  | pred k ih =>
      intro x
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have hinv : (fibreShift iota)⁻¹ x = (x.1, x.2 - 1) := by
        apply (fibreShift iota).injective
        simp
      rw [hinv]
      simp only [Prod.mk.injEq, true_and]
      ring

/-- The fibre of `iota × ℤ` over one index. -/
def fibre {iota : Type*} (e : iota) : Set (iota × ℤ) := {p | p.1 = e}

theorem fibreShift_mem_fibreUnion {iota : Type*} [DecidableEq iota]
    {S : Finset iota} {x : iota × ℤ} (hx : x ∈ ⋃ e ∈ S, fibre e) (n : ℤ) :
    (fibreShift iota ^ n) x ∈ ⋃ e ∈ S, fibre e := by
  rw [Set.mem_iUnion₂] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  refine ⟨e, he, ?_⟩
  rw [fibreShift_zpow_apply]
  exact hxe

/-- The fibrewise shift has free translates on every union of fibres. -/
theorem hasFreeTranslates_fibreShift {iota : Type*} [DecidableEq iota] (S : Finset iota) :
    Rank.HasFreeTranslates (fibreShift iota) (⋃ e ∈ S, fibre e) := by
  refine Rank.hasFreeTranslates_of_intHeight _ _ Prod.snd ?_ ?_
  · intro x hx n
    exact fibreShift_mem_fibreUnion hx n
  · intro x _ n
    rw [fibreShift_zpow_apply]

/-! ## Joint realization of the star-gluing hypotheses -/

/-- **The four star-gluing hypotheses hold simultaneously.**  In the free model over `iota × ℤ`, with
every edge incident to the single vertex, the star is a union of fibres — independent, rank
automorphic and freely translated — while the off-star is empty and therefore rank neutral. -/
theorem freeRank_graphGluing_hypotheses {iota : Type*} [DecidableEq iota]
    (edges : Finset iota) :
    (∀ _q : Unit, fibreShift iota ∈ (freeRank (iota × ℤ)).rankAutSubgroup) ∧
      (∀ _q : Unit, (freeRank (iota × ℤ)).IndepSet
        (⋃ e ∈ edges.filter (fun _ => True), fibre e)) ∧
      (∀ _q : Unit, Rank.HasFreeTranslates (fibreShift iota)
        (⋃ e ∈ edges.filter (fun _ => True), fibre e)) ∧
      (∀ _q : Unit, (freeRank (iota × ℤ)).CrossNeutral (fibreShift iota)
        (⋃ e ∈ edges.filter (fun _ => ¬ True), fibre e)) := by
  refine ⟨fun _ => freeRank_mem_rankAutSubgroup _, fun _ => freeRank_indepSet _,
    fun _ => hasFreeTranslates_fibreShift _, fun _ => ?_⟩
  refine freeRank_crossNeutral_of_fixed ?_
  intro x hx
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨e, he, _⟩ := hx
  rw [Finset.mem_filter] at he
  exact absurd trivial he.2

end GaloisForLFunctions.MatroidGluing
