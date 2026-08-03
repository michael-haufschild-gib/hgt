import GaloisForLFunctions.HTGeometry.BarnesLadderAtoms

/-!
# The ladder decomposition of the Barnes source

Summing the atomwise ladder shift over the reindexing bijection splits the shift difference of the
source into two convergent pieces: a correction series indexed by the whole cone, and the atom
series of the slice on which the shifted exponent vanishes — the deleted-frame cone, which is the
lower step of the Barnes hierarchy.

```text
Ψ(z + ω_j) - Ψ(z) = ∑'_n (A_n(z + ω_j) - A_{n+e_j}(z)) - ∑'_{n_j = 0} A_n(z).
```

Both series converge, the first because it is a difference of two convergent ones and the second
because it is a subseries.  This is the exact form in which the Barnes ladder is used: the second
term is the lower source, the first is the correction that the normalization absorbs.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## Summability of the atoms -/

theorem norm_barnesAtom_le (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {n : ι → ℕ} (hn : n ≠ 0)
    (z : ℂ) (hcone : 2 * ‖z‖ ≤ ‖conePeriod ω n‖) :
    ‖barnesAtom ω n z‖ ≤
      2 * ‖z‖ ^ Fintype.card ι * (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ := by
  have hwpos : 0 < ‖conePeriod ω n‖ := norm_pos_iff.mpr (conePeriod_ne_zero ω hω hn)
  have hhalf : ‖conePeriod ω n‖ / 2 ≤ ‖conePeriod ω n + z‖ := by
    have hge : ‖conePeriod ω n‖ - ‖z‖ ≤ ‖conePeriod ω n + z‖ := by
      have h := norm_sub_norm_le (conePeriod ω n) (-z)
      simpa [sub_neg_eq_add] using h
    linarith
  have hpos : 0 < ‖conePeriod ω n + z‖ := lt_of_lt_of_le (by positivity) hhalf
  rw [barnesAtom, if_neg hn, norm_div, norm_pow, norm_neg, norm_div, div_pow, div_div,
    div_le_iff₀ (by positivity :
      (0 : ℝ) < ‖conePeriod ω n‖ ^ Fintype.card ι * ‖conePeriod ω n + z‖)]
  have hrw : 2 * ‖z‖ ^ Fintype.card ι * (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ *
      (‖conePeriod ω n‖ ^ Fintype.card ι * ‖conePeriod ω n + z‖) =
      2 * ‖conePeriod ω n + z‖ / ‖conePeriod ω n‖ * ‖z‖ ^ Fintype.card ι := by
    field_simp [pow_succ]
    ring
  rw [hrw]
  have hone : (1 : ℝ) ≤ 2 * ‖conePeriod ω n + z‖ / ‖conePeriod ω n‖ := by
    rw [le_div_iff₀ hwpos]
    linarith
  exact le_mul_of_one_le_left (by positivity) hone

theorem summable_barnesAtom (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (z : ℂ) :
    Summable fun n : ι → ℕ => barnesAtom ω n z := by
  refine Summable.of_norm ?_
  exact summable_of_conePeriod_majorant ω hω (fun n => norm_nonneg _)
    (2 * ‖z‖ ^ Fintype.card ι) ‖z‖ fun n hn hcone => norm_barnesAtom_le ω hω hn z hcone

/-! ## The reindexed slice -/

/-- The reindexing bijection onto the positive slice, as a set-subtype equivalence. -/
def addSingleSetEquiv [DecidableEq ι] (j : ι) :
    (ι → ℕ) ≃ ↥{n : ι → ℕ | 1 ≤ n j} :=
  addSingleEquiv j

theorem summable_barnesAtom_add_single [DecidableEq ι] (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (z : ℂ) (j : ι) :
    Summable fun n : ι → ℕ => barnesAtom ω (n + Pi.single j 1) z :=
  (summable_barnesAtom ω hω z).comp_injective (add_left_injective (Pi.single j 1))

theorem tsum_barnesAtom_split [DecidableEq ι] (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (z : ℂ) (j : ι) :
    (∑' n : ι → ℕ, barnesAtom ω n z) =
      (∑' n : ι → ℕ, barnesAtom ω (n + Pi.single j 1) z) +
        ∑' n : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ), barnesAtom ω n.1 z := by
  have hS := (summable_barnesAtom ω hω z).subtype {n : ι → ℕ | 1 ≤ n j}
  have hSc := (summable_barnesAtom ω hω z).subtype {n : ι → ℕ | 1 ≤ n j}ᶜ
  rw [← Summable.tsum_add_tsum_compl hS hSc]
  congr 1
  exact ((addSingleSetEquiv j).tsum_eq fun m : ↥{n : ι → ℕ | 1 ≤ n j} => barnesAtom ω m.1 z).symm

/-! ## The ladder decomposition -/

/-- **The ladder decomposition of the Barnes source.**  The shift difference splits into the
correction series over the whole cone and the atom series of the deleted-frame slice. -/
theorem barnesSource_ladder_decomposition [DecidableEq ι] (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    {z : ℂ} (j : ι)
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0)
    (hpole' : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + (z + ω j) ≠ 0) :
    logDeriv (barnesConeProduct ω) (z + ω j) - logDeriv (barnesConeProduct ω) z =
      (∑' n : ι → ℕ, (barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z)) -
        ∑' n : ↥({n : ι → ℕ | 1 ≤ n j}ᶜ), barnesAtom ω n.1 z := by
  rw [logDeriv_barnesConeProduct_eq_tsum_barnesAtom ω hω hpole',
    logDeriv_barnesConeProduct_eq_tsum_barnesAtom ω hω hpole,
    tsum_barnesAtom_split ω hω z j,
    Summable.tsum_sub (summable_barnesAtom ω hω (z + ω j))
      (summable_barnesAtom_add_single ω hω z j)]
  ring

end

end GaloisForLFunctions
