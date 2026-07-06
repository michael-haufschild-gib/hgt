/-
Accounting bridge from the completed reflected-grid carrier to paired off-grid events.

This file does not identify the physical AFE/reflection carrier.  It records the
formal parity consequence available once that future accounting step expresses a
charge as the canonical reflected-grid completed charge plus a paired off-grid
integer event list.
-/
import GaloisForLFunctions.RHTower.ReflectedGridCenter
import GaloisForLFunctions.RHTower.LedgerReduction

namespace RHTower

/-- The certified charge obtained by adding a paired off-grid event ledger to the
completed reflected-grid charge at the canonical ratio center. -/
noncomputable def reflectedGridOffgridCharge (C N : ℕ) (L : List ℤ) : ℤ :=
  (reflectedGridCompletedCharge C N reflectedGridRatioCenter : ℤ) + L.sum

/-- If the completed carrier is nontrivial (`N ≥ 1`) and the off-grid ledger is paired,
then the accounted grid-plus-offgrid charge is even. -/
theorem reflectedGridOffgridCharge_even_of_paired {C N : ℕ} {L : List ℤ}
    (hN : 1 ≤ N) (hL : LedgerFluxPaired L) :
    Even (reflectedGridOffgridCharge C N L) := by
  unfold reflectedGridOffgridCharge
  have hgridN : Even (reflectedGridCompletedCharge C N reflectedGridRatioCenter) :=
    reflectedGridCompletedCharge_even_of_ratio_center_of_one_le (C := C) hN
  have hgridZ : Even ((reflectedGridCompletedCharge C N reflectedGridRatioCenter : ℕ) : ℤ) := by
    exact_mod_cast hgridN
  have hoffZ : Even L.sum := by
    rw [even_iff_two_dvd]
    exact ledgerFluxPaired_two_dvd_sum hL
  exact hgridZ.add hoffZ

/-- Deck form of `reflectedGridOffgridCharge_even_of_paired`. -/
theorem reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired {C N : ℕ} {L : List ℤ}
    (hN : 1 ≤ N) (hL : LedgerFluxPaired L) :
    deckRed 2 (reflectedGridOffgridCharge C N L) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact reflectedGridOffgridCharge_even_of_paired hN hL

/-- Accounted-charge form: any future carrier charge identified with the canonical
completed grid charge plus a paired off-grid ledger is deck-trivial at level two. -/
theorem reflectedGridOffgridCharge_deckRed_two_eq_one_of_accounted {C N : ℕ}
    {L : List ℤ} {Q : ℤ} (hN : 1 ≤ N) (hL : LedgerFluxPaired L)
    (hQ : Q = reflectedGridOffgridCharge C N L) :
    deckRed 2 Q = 1 := by
  rw [hQ]
  exact reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired hN hL

/-- Saddle-flux specialization: an even reflected saddle-mode count supplies the paired
off-grid ledger needed by the accounted completed charge. -/
theorem reflectedGridOffgridCharge_deckRed_two_eq_one_of_even_saddle_modes
    {C N K : ℕ} {T a b : ℝ} (hN : 1 ≤ N)
    (hEven : Even (reflectedSaddleModes K T a b).card) :
    deckRed 2 (reflectedGridOffgridCharge C N (reflectedSaddleFluxList K T a b)) = 1 := by
  exact reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired hN
    (reflectedSaddleFluxPaired_of_even hEven)

/-- Accounted saddle-flux form: once a future physical charge is identified with the
completed charge plus the finite reflected saddle-mode ledger, an even saddle-mode count
makes its level-two deck class trivial. -/
theorem reflectedGridOffgridCharge_deckRed_two_eq_one_of_accounted_even_saddle_modes
    {C N K : ℕ} {T a b : ℝ} {Q : ℤ} (hN : 1 ≤ N)
    (hEven : Even (reflectedSaddleModes K T a b).card)
    (hQ : Q = reflectedGridOffgridCharge C N (reflectedSaddleFluxList K T a b)) :
    deckRed 2 Q = 1 := by
  rw [hQ]
  exact reflectedGridOffgridCharge_deckRed_two_eq_one_of_even_saddle_modes hN hEven

end RHTower
