import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadCharge
import GaloisForLFunctions.RHTower.MobiusDivisorTwoChannelPrimeBlocks

/-!
# Two-channel dissipation for the completed arity-head charge

An oriented nonnegative residual field makes each adjacent residual-label
correlation negative after the inserted prime reverses residual parity.  Thus
the existing two-channel source blocks control not only ordinary retained
energy but also the completed arity-head charge, including at nonempty cores.
This remains a sparse local source law; it does not construct an exhaustive
prime order or its global cancellation-stable budget.
-/

noncomputable section
open Finset
namespace RHTower

/-- A globally nonnegative oriented residual field makes every arity-head
prime charge dissipative. -/
theorem mobiusDivisorArityHeadCharge_nonpos_of_oriented_nonneg
    (M : ℕ) (P : Finset ℕ) (p : ℕ)
    (hpos : ∀ R : Finset ℕ, 0 ≤ mobiusDivisorOrientedFibre M P R) :
    mobiusDivisorArityHeadCharge M P p ≤ 0 := by
  have hsplit : mobiusDivisorArityHeadCharge M P p =
      2 * ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
        (R.card : ℝ) * mobiusDivisorSelectionFibre M P R *
          mobiusDivisorSelectionFibre M P (insert p R) +
      2 * (mobiusDivisorSelectionFibre M P ∅ *
        mobiusDivisorSelectionFibre M P {p}) := by
    unfold mobiusDivisorArityHeadCharge mobiusDivisorArityCharge
    ring
  rw [hsplit]
  apply add_nonpos
  · apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply sum_nonpos
    intro R hR
    have hpR : p ∉ R := by
      intro hpR
      exact (mem_erase.mp (mem_powerset.mp hR hpR)).1 rfl
    have hprod :
        mobiusDivisorSelectionFibre M P R *
          mobiusDivisorSelectionFibre M P (insert p R) =
        -mobiusDivisorOrientedFibre M P R *
          mobiusDivisorOrientedFibre M P (insert p R) := by
      unfold mobiusDivisorOrientedFibre
      rw [card_insert_of_notMem hpR, pow_succ]
      have hparity : (-1 : ℝ) ^ R.card * (-1 : ℝ) ^ R.card = 1 := by
        rw [← pow_add, show R.card + R.card = 2 * R.card by omega, pow_mul]
        norm_num
      symm
      calc
        -((-1 : ℝ) ^ R.card * mobiusDivisorSelectionFibre M P R) *
            ((-1 : ℝ) ^ R.card * -1 *
              mobiusDivisorSelectionFibre M P (insert p R)) =
            ((-1 : ℝ) ^ R.card * (-1 : ℝ) ^ R.card) *
              mobiusDivisorSelectionFibre M P R *
                mobiusDivisorSelectionFibre M P (insert p R) := by ring
        _ = _ := by rw [hparity, one_mul]
    calc
      (R.card : ℝ) * mobiusDivisorSelectionFibre M P R *
          mobiusDivisorSelectionFibre M P (insert p R) =
          (R.card : ℝ) *
            (mobiusDivisorSelectionFibre M P R *
              mobiusDivisorSelectionFibre M P (insert p R)) := by ring
      _ = (R.card : ℝ) *
          (-mobiusDivisorOrientedFibre M P R *
            mobiusDivisorOrientedFibre M P (insert p R)) := by rw [hprod]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg R.card)
        (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (hpos R)) (hpos (insert p R)))
  · apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    have hprod :
        mobiusDivisorSelectionFibre M P ∅ *
          mobiusDivisorSelectionFibre M P {p} =
        -mobiusDivisorOrientedFibre M P ∅ *
          mobiusDivisorOrientedFibre M P {p} := by
      unfold mobiusDivisorOrientedFibre
      simp only [card_empty, pow_zero, one_mul, card_singleton, pow_one, neg_one_mul]
      ring
    rw [hprod]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hpos ∅)) (hpos {p})

/-- The actual two-channel source blocks dissipate completed arity-head charge
at every unprocessed prime, including from nonempty processed cores. -/
theorem exists_mobiusDivisorTwoChannelBlockArityHeadDissipation :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ L : Finset ℕ,
      (∀ p ∈ L, p.Prime ∧ p < M ∧ 2 * M ≤ 5 * p) →
      (∑ p ∈ L, divisorUnsignedDilationChannel M p) ≤
        divisorUnsignedDilationChannel M 1 →
      ∀ P ⊆ L, ∀ q : ℕ, q.Prime → q < M → q ∉ P →
        mobiusDivisorArityHeadCharge M P q ≤ 0 := by
  obtain ⟨M₀, hblock⟩ := exists_mobiusDivisorTwoChannelBlockParity
  refine ⟨M₀, ?_⟩
  intro M hM L hL hbudget P hPL q _ _ _
  obtain ⟨hor, _, _, _⟩ := hblock M hM L hL hbudget P hPL
  exact mobiusDivisorArityHeadCharge_nonpos_of_oriented_nonneg M P q
    (fun R => (hor R).1)

end RHTower
