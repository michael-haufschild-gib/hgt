import GaloisForLFunctions.RHTower.MobiusDivisorArityCharge

/-!
# Arity-head interaction charge

Completing arity-weighted energy by its literal head square converts the
otherwise missing terminal head into an exact finite prime-history balance.
The singleton copied-child square cancels exactly; every nonempty copied child
and the resulting head-coupled signed interaction charge remain literal.
No sign or asymptotic bound for that charge is asserted here.
-/

noncomputable section
open Finset
namespace RHTower

/-- Arity energy completed by the literal signed head square. -/
def mobiusDivisorArityHeadEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorArityEnergy M P + (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ)

/-- The signed arity charge coupled to the literal head--singleton interaction. -/
def mobiusDivisorArityHeadCharge (M : ℕ) (P : Finset ℕ) (p : ℕ) : ℝ :=
  mobiusDivisorArityCharge M P p +
    2 * mobiusDivisorSelectionFibre M P ∅ * mobiusDivisorSelectionFibre M P {p}

/-- Adding one head square cancels exactly the singleton copied-child cost in the
arity balance; only nonempty copied children remain. -/
theorem mobiusDivisorArityHeadEnergy_insert (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p ∈ mobiusDivisorSelectionPrimes M) :
    mobiusDivisorArityHeadEnergy M (insert p P) - mobiusDivisorArityHeadEnergy M P =
      mobiusDivisorArityHeadCharge M P p -
        ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset.erase ∅,
          (mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ) := by
  have harity := mobiusDivisorArityEnergy_insert M P hp
  have hhead : mobiusDivisorSelectionFibre M (insert p P) ∅ =
      mobiusDivisorSelectionFibre M P ∅ + mobiusDivisorSelectionFibre M P {p} := by
    rw [mobiusDivisorSelectionFibre_insert]
    simp
  have hsplit := sum_erase_add
    (s := ((mobiusDivisorSelectionPrimes M).erase p).powerset)
    (f := fun R => (mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ))
    (a := ∅) (by simp)
  simp only [insert_empty_eq] at hsplit
  unfold mobiusDivisorArityHeadEnergy mobiusDivisorArityHeadCharge
  rw [hhead]
  nlinarith only [harity, hsplit]

/-- Along any finite legal history, nonempty copied-child cost telescopes to the
initial completed arity energy, final completed arity energy, and accumulated
head-coupled signed charge. -/
theorem mobiusDivisorArityHeadEnergy_history_balance (M : ℕ) (P : Finset ℕ)
    (q : ℕ → ℕ) (n : ℕ) (hq : ∀ k < n, q k ∈ mobiusDivisorSelectionPrimes M) :
    (∑ k ∈ range n,
      ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase (q k)).powerset.erase ∅,
        (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q k)
          (insert (q k) R))^(2 : ℕ)) =
      mobiusDivisorArityHeadEnergy M P -
        mobiusDivisorArityHeadEnergy M (mobiusDivisorArityHistory P q n) +
      ∑ k ∈ range n,
        mobiusDivisorArityHeadCharge M (mobiusDivisorArityHistory P q k) (q k) := by
  have h := Finset.sum_range_sub
    (fun k => mobiusDivisorArityHeadEnergy M (mobiusDivisorArityHistory P q k)) n
  have hstep :
      (∑ k ∈ range n,
        (mobiusDivisorArityHeadEnergy M (mobiusDivisorArityHistory P q (k + 1)) -
          mobiusDivisorArityHeadEnergy M (mobiusDivisorArityHistory P q k))) =
        (∑ k ∈ range n,
          mobiusDivisorArityHeadCharge M (mobiusDivisorArityHistory P q k) (q k)) -
        ∑ k ∈ range n,
          ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase (q k)).powerset.erase ∅,
            (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q k)
              (insert (q k) R))^(2 : ℕ) := by
    rw [← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    exact mobiusDivisorArityHeadEnergy_insert M _ (hq k (mem_range.mp hk))
  rw [hstep] at h
  change _ = _ - mobiusDivisorArityHeadEnergy M P at h
  linarith only [h]

/-- At a fully processed state the completed arity energy is precisely the
terminal signed head square. -/
theorem mobiusDivisorArityHeadEnergy_of_complete (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSelectionPrimes M ⊆ P) :
    mobiusDivisorArityHeadEnergy M P = (mobiusDivisorSelectionFibre M P ∅)^(2 : ℕ) := by
  unfold mobiusDivisorArityHeadEnergy
  rw [mobiusDivisorArityEnergy_of_complete M P hP]
  ring

/-- At a complete history endpoint, terminal head square and every nonempty
copied-child cost are exactly funded by initial completed arity energy plus
the accumulated coupled signed charge. -/
theorem mobiusDivisorArityHeadEnergy_complete_history_balance (M : ℕ) (P : Finset ℕ)
    (q : ℕ → ℕ) (n : ℕ) (hq : ∀ k < n, q k ∈ mobiusDivisorSelectionPrimes M)
    (hcomplete : mobiusDivisorSelectionPrimes M ⊆ mobiusDivisorArityHistory P q n) :
    (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q n) ∅)^(2 : ℕ) +
      (∑ k ∈ range n,
        ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase (q k)).powerset.erase ∅,
          (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q k)
            (insert (q k) R))^(2 : ℕ)) =
      mobiusDivisorArityHeadEnergy M P +
        ∑ k ∈ range n,
          mobiusDivisorArityHeadCharge M (mobiusDivisorArityHistory P q k) (q k) := by
  have h := mobiusDivisorArityHeadEnergy_history_balance M P q n hq
  rw [mobiusDivisorArityHeadEnergy_of_complete M
    (mobiusDivisorArityHistory P q n) hcomplete] at h
  linarith only [h]

end RHTower
