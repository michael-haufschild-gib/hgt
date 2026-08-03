import GaloisForLFunctions.HTGeometry.BarnesLadderGeneralGenus

/-!
# The order-one ladder is rational

With a single structural direction the ladder decomposition collapses completely.  The slice on
which the exponent vanishes is the single zero vector, whose atom is zero, so the slice series
disappears.  The correction series splits off its zero term — the explicit rational atom at the unit
exponent — and every remaining term is the argument-free telescoping difference of inverse cone
values.

Hence the shift difference of the order-one source is an explicit rational function of the argument
plus a constant:

```text
Ψ(z + ω_j) - Ψ(z) = -A_{e_j}(z) + ∑'_{n ≠ 0} (1/w_{n+e_j} - 1/w_n).
```

This is the bottom step of the Barnes ladder for the constructed source, and it is rational, hence
differentially algebraic.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The slice is trivial at order one -/

omit [DecidableEq ι] in
theorem tsum_barnesAtom_slice_card_one (ω : ι → ℂ) (hcard : Fintype.card ι = 1) (j : ι)
    (z : ℂ) : (∑' m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ), barnesAtom ω m.1 z) = 0 := by
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hzero : ∀ m : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ), barnesAtom ω m.1 z = 0 := by
    intro m
    have hm : m.1 = 0 := by
      funext i
      have hij : i = j := Subsingleton.elim i j
      subst hij
      have hle : ¬ (1 ≤ m.1 i) := m.2
      simpa using Nat.eq_zero_of_not_pos hle
    rw [hm, barnesAtom, if_pos rfl]
  rw [tsum_congr hzero, tsum_zero]

/-! ## The order-one ladder -/

/-- **The order-one ladder is rational.**  With one structural direction the shift difference of the
source is the explicit rational atom at the unit exponent, up to an argument-free constant. -/
theorem barnesSource_shift_sub_card_one (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hcard : Fintype.card ι = 1) (j : ι) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0)
    (hpole' : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + (z + ω j) ≠ 0) :
    logDeriv (barnesConeProduct ω) (z + ω j) - logDeriv (barnesConeProduct ω) z =
      -barnesAtom ω (Pi.single j 1) z +
        ∑' n : ι → ℕ, (if n = 0 then 0 else
          (conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hsummable : Summable fun n : ι → ℕ =>
      barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z :=
    (summable_barnesAtom ω hω (z + ω j)).sub (summable_barnesAtom_add_single ω hω z j)
  have hsplit := Summable.tsum_eq_add_tsum_ite hsummable (0 : ι → ℕ)
  have hzeroterm : barnesAtom ω (0 : ι → ℕ) (z + ω j) -
      barnesAtom ω ((0 : ι → ℕ) + Pi.single j 1) z = -barnesAtom ω (Pi.single j 1) z := by
    rw [barnesAtom, if_pos rfl, zero_add, zero_sub]
  have hrest : ∀ n : ι → ℕ,
      (if n = 0 then 0 else
        barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z) =
      (if n = 0 then 0 else
        (conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹) := by
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_neg hn]
      exact barnesAtom_shift_sub_card_one ω hcard hn j z (conePeriod_ne_zero ω hω hn)
        (conePeriod_ne_zero ω hω (add_single_ne_zero n j))
        (hpole _ (add_single_ne_zero n j))
  rw [barnesSource_ladder_decomposition ω hω j hpole hpole',
    tsum_barnesAtom_slice_card_one ω hcard j z, sub_zero, hsplit, hzeroterm,
    tsum_congr hrest]

end

end GaloisForLFunctions
