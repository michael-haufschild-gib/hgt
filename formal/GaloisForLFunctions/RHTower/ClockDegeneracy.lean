import GaloisForLFunctions.RHTower.DivisorSliceFreePart

/-!
# The clock and its degeneracy

Read the divisor physically.  The ordinate is **time**; a slice is the set of states at one instant.
Of the three involutions on `ℂ` that preserve the divisor, conjugation `ρ ↦ conj ρ` reverses time and
fixes space, the functional equation `ρ ↦ 1 − ρ` reverses both, and their composite
`σ : ρ ↦ 1 − conj ρ` — the Hermitian reflection — **fixes time and reflects space**: it is parity.

So the hypothesis says that parity is **unbroken**: every state is its own parity image.  Its failure
is a parity doublet — two distinct states at the *same* instant, which is exactly a degeneracy of the
clock.  The quantitative form is proved here: at every instant

  `#states  =  #(parity-invariant states)  +  2 · #(left-moving states)`,

the first term is `0` or `1` unconditionally, and

  `RiemannHypothesis ↔ every instant carries at most one state`,

i.e. the clock is a **complete observable** — reading the time determines the state.  A corollary
with no hypothesis: **the number of states at an instant is odd exactly when one of them is
parity-invariant**, that is, exactly when the critical point at that height is a zero.
-/

open Complex Set

namespace RHTower

noncomputable section

/-! ## The three parts of a slice are disjoint -/

theorem xiSliceFixed_re {t : ℝ} {ρ : XiDivisorSupport} (h : ρ ∈ xiSliceFixed t) :
    (ρ : ℂ).re = 1 / 2 :=
  (supportPartner_eq_self_iff ρ).mp h.2

theorem disjoint_xiSliceLeft_xiSliceFixed (t : ℝ) :
    Disjoint (xiSliceLeft t) (xiSliceFixed t) := by
  refine Set.disjoint_left.mpr fun ρ hl hf => ?_
  have h1 : (ρ : ℂ).re < 1 / 2 := hl.2
  have h2 : (ρ : ℂ).re = 1 / 2 := xiSliceFixed_re hf
  linarith

theorem disjoint_xiSliceLeftFixed_xiSliceRight (t : ℝ) :
    Disjoint (xiSliceLeft t ∪ xiSliceFixed t) (xiSliceRight t) := by
  refine Set.disjoint_left.mpr fun ρ hlf hr => ?_
  have h2 : 1 / 2 < (ρ : ℂ).re := hr.2
  rcases hlf with hl | hf
  · have h1 : (ρ : ℂ).re < 1 / 2 := hl.2
    linarith
  · have h1 : (ρ : ℂ).re = 1 / 2 := xiSliceFixed_re hf
    linarith

/-! ## Finiteness of the pieces -/

theorem xiSliceLeft_finite (t : ℝ) : (xiSliceLeft t).Finite :=
  (xiSlice_finite t).subset (xiSliceLeft_subset t)

theorem xiSliceRight_finite (t : ℝ) : (xiSliceRight t).Finite :=
  (xiSlice_finite t).subset (xiSliceRight_subset t)

/-- The two half-slices have equal cardinality: parity exchanges them. -/
theorem ncard_xiSliceRight (t : ℝ) : (xiSliceRight t).ncard = (xiSliceLeft t).ncard := by
  rw [xiSliceRight_eq_image t]
  exact Set.ncard_image_of_injective _ supportPartner.injective

/-- The parity-invariant part of a slice has cardinality `0` or `1`, unconditionally. -/
theorem ncard_xiSliceFixed_le_one (t : ℝ) : (xiSliceFixed t).ncard ≤ 1 := by
  rcases (xiSliceFixed_subsingleton t).eq_empty_or_singleton with h | ⟨a, h⟩
  · rw [h]; simp
  · rw [h]; simp

/-! ## The degeneracy formula -/

/-- **The clock degeneracy formula.**  At every instant the number of states is the number of
parity-invariant states plus twice the number of left-moving ones. -/
theorem ncard_xiSlice (t : ℝ) :
    (xiSlice t).ncard = (xiSliceFixed t).ncard + 2 * (xiSliceLeft t).ncard := by
  have hLF : ((xiSliceLeft t ∪ xiSliceFixed t)).ncard
      = (xiSliceLeft t).ncard + (xiSliceFixed t).ncard :=
    Set.ncard_union_eq (disjoint_xiSliceLeft_xiSliceFixed t)
      (xiSliceLeft_finite t) (xiSliceFixed_finite t)
  have hall : (xiSlice t).ncard
      = (xiSliceLeft t ∪ xiSliceFixed t).ncard + (xiSliceRight t).ncard := by
    rw [xiSlice_eq_union t]
    exact Set.ncard_union_eq (disjoint_xiSliceLeftFixed_xiSliceRight t)
      ((xiSliceLeft_finite t).union (xiSliceFixed_finite t)) (xiSliceRight_finite t)
  rw [hall, hLF, ncard_xiSliceRight t]
  ring

/-- **The clock is a complete observable exactly under the hypothesis.** -/
theorem riemannHypothesis_iff_ncard_xiSlice_le_one :
    RiemannHypothesis ↔ ∀ t : ℝ, (xiSlice t).ncard ≤ 1 := by
  rw [riemannHypothesis_iff_xiSliceLeft_empty]
  constructor
  · intro h t
    rw [ncard_xiSlice t, h t]
    simpa using ncard_xiSliceFixed_le_one t
  · intro h t
    have hb := h t
    rw [ncard_xiSlice t] at hb
    have : (xiSliceLeft t).ncard = 0 := by omega
    exact (Set.ncard_eq_zero (xiSliceLeft_finite t)).mp this

/-- **Parity of the degeneracy, unconditionally.**  The number of states at an instant is odd
exactly when one of them is parity-invariant, i.e. exactly when the critical point at that height is
a zero. -/
theorem odd_ncard_xiSlice_iff (t : ℝ) :
    Odd ((xiSlice t).ncard) ↔ (xiSliceFixed t).Nonempty := by
  rw [ncard_xiSlice t]
  rcases (xiSliceFixed_subsingleton t).eq_empty_or_singleton with h | ⟨a, h⟩
  · rw [h]
    simp only [Set.ncard_empty, zero_add, Set.not_nonempty_empty, iff_false]
    rintro ⟨k, hk⟩
    omega
  · rw [h]
    simp only [Set.ncard_singleton]
    constructor
    · intro _; exact ⟨a, rfl⟩
    · intro _; exact ⟨(xiSliceLeft t).ncard, by ring⟩

end

end RHTower
