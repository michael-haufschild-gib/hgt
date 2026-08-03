import GaloisForLFunctions.HTGeometry.BarnesGenusShift

/-!
# The ladder slice is the deleted-frame cone

The slice on which one exponent vanishes is, by restriction, the cone of the frame with that period
deleted: the correspondence is a bijection, it matches cone values, and it matches the zero exponent
vector.  The number of directions drops by one, so the ambient genus is one above the genus of the
deleted frame — which is exactly the mismatch already priced as a monomial.

Consequently the slice series of the ladder decomposition is the source of the deleted frame, up to
that monomial.  This is the lower step of the Barnes hierarchy, identified for the constructed
object rather than assumed.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The deleted frame and the slice bijection -/

/-- The period frame with one direction deleted. -/
def deletedFrame (ω : ι → ℂ) (j : ι) : {i : ι // i ≠ j} → ℂ := fun i => ω i.1

omit [Fintype ι] [DecidableEq ι] in
theorem deletedFrame_im_pos {ω : ι → ℂ} (hω : ∀ i, 0 < (ω i).im) (j : ι) :
    ∀ i, 0 < (deletedFrame ω j i).im := fun i => hω i.1

/-- **Restriction identifies the vanishing slice with the deleted-frame cone.** -/
def sliceEquiv (j : ι) :
    ↥({n : ι → ℕ | 1 ≤ n j}ᶜ) ≃ ({i : ι // i ≠ j} → ℕ) where
  toFun m := fun i => m.1 i.1
  invFun g := ⟨fun i => if h : i = j then 0 else g ⟨i, h⟩, by
    intro hmem
    rw [Set.mem_setOf_eq] at hmem
    simp only [dif_pos] at hmem
    omega⟩
  left_inv m := by
    refine Subtype.ext ?_
    funext i
    by_cases h : i = j
    · subst h
      have hm : m.1 i = 0 := by
        have hle : ¬ (1 ≤ m.1 i) := m.2
        omega
      show (if _ : i = i then (0 : ℕ) else m.1 i) = m.1 i
      rw [dif_pos rfl, hm]
    · show (if _ : i = j then (0 : ℕ) else m.1 i) = m.1 i
      rw [dif_neg h]
  right_inv g := by
    funext i
    show (if h : i.1 = j then (0 : ℕ) else g ⟨i.1, h⟩) = g i
    rw [dif_neg i.2]

omit [Fintype ι] in
@[simp] theorem sliceEquiv_apply (j : ι) (m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ))
    (i : {i : ι // i ≠ j}) : sliceEquiv j m i = m.1 i.1 := rfl

omit [Fintype ι] in
theorem sliceEquiv_eq_zero_iff (j : ι) (m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ)) :
    sliceEquiv j m = 0 ↔ m.1 = 0 := by
  constructor
  · intro h
    funext i
    by_cases hi : i = j
    · subst hi
      have hm : ¬ (1 ≤ m.1 i) := m.2
      simpa using Nat.eq_zero_of_not_pos hm
    · have := congrFun h ⟨i, hi⟩
      simpa using this
  · intro h
    funext i
    rw [sliceEquiv_apply, h]
    rfl

/-! ## Matching the cone values -/

theorem conePeriod_sliceEquiv (ω : ι → ℂ) (j : ι) (m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ)) :
    conePeriod ω m.1 = conePeriod (deletedFrame ω j) (sliceEquiv j m) := by
  have hj : m.1 j = 0 := by
    have hm : ¬ (1 ≤ m.1 j) := m.2
    omega
  rw [conePeriod_eq_sum_erase_of_eq_zero ω hj, conePeriod]
  exact Finset.sum_subtype (p := fun i : ι => i ≠ j) (Finset.univ.erase j)
    (fun x => by rw [Finset.mem_erase]; simp) _

/-! ## The genus of the deleted frame -/

theorem card_subtype_ne_succ (j : ι) :
    Fintype.card {i : ι // i ≠ j} + 1 = Fintype.card ι := by
  classical
  show Fintype.card {i : ι // ¬ (i = j)} + 1 = Fintype.card ι
  have hcompl : Fintype.card {i : ι // ¬ (i = j)} =
      Fintype.card ι - Fintype.card {i : ι // i = j} := Fintype.card_subtype_compl _
  have hone : Fintype.card {i : ι // i = j} = 1 := Fintype.card_subtype_eq j
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  rw [hone] at hcompl
  omega

/-! ## The slice series is the deleted-frame series -/

theorem barnesAtom_slice (ω : ι → ℂ) (j : ι) (m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ)) (z : ℂ) :
    barnesAtom ω m.1 z =
      barnesAtomPow (deletedFrame ω j) (Fintype.card {i : ι // i ≠ j} + 1)
        (sliceEquiv j m) z := by
  rw [barnesAtom, barnesAtomPow, conePeriod_sliceEquiv ω j m, card_subtype_ne_succ j]
  by_cases h : m.1 = 0
  · rw [if_pos h, if_pos ((sliceEquiv_eq_zero_iff j m).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((sliceEquiv_eq_zero_iff j m).mp hc))]

/-- **The ladder slice is the deleted-frame series at the ambient genus.** -/
theorem tsum_barnesAtom_slice (ω : ι → ℂ) (j : ι) (z : ℂ) :
    (∑' m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ), barnesAtom ω m.1 z) =
      ∑' g : {i : ι // i ≠ j} → ℕ,
        barnesAtomPow (deletedFrame ω j) (Fintype.card {i : ι // i ≠ j} + 1) g z := by
  rw [tsum_congr fun m => barnesAtom_slice ω j m z]
  exact (sliceEquiv j).tsum_eq fun g =>
    barnesAtomPow (deletedFrame ω j) (Fintype.card {i : ι // i ≠ j} + 1) g z

/-- **The ladder slice is the lower source up to a monomial.**  For a frame with at least two
directions the slice series of the ladder decomposition is the atom series of the deleted frame
minus a constant multiple of `z^{N-1}`. -/
theorem tsum_barnesAtom_slice_eq_lower (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι)
    [Nonempty {i : ι // i ≠ j}] {z : ℂ}
    (hpole : ∀ g : {i : ι // i ≠ j} → ℕ, g ≠ 0 →
      conePeriod (deletedFrame ω j) g + z ≠ 0) :
    (∑' m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ), barnesAtom ω m.1 z) =
      (∑' g : {i : ι // i ≠ j} → ℕ, barnesAtom (deletedFrame ω j) g z) -
        (-1) ^ Fintype.card {i : ι // i ≠ j} * z ^ Fintype.card {i : ι // i ≠ j} *
          coneZeta (deletedFrame ω j) := by
  rw [tsum_barnesAtom_slice ω j z,
    tsum_barnesAtomPow_succ (deletedFrame ω j) (deletedFrame_im_pos hω j) hpole,
    tsum_barnesGenusCorrection_eq (deletedFrame ω j) z]

end

end GaloisForLFunctions
