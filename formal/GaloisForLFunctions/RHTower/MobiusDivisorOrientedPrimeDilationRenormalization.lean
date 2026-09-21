import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadProcessedCoreHomothety
import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport

/-!
# Oriented two-scale renormalization under a fresh CCM-FU prime dilation

At cutoff `p * N`, a source label that contains the fresh unprocessed prime `p` is an exact
reflected square-root copy of a label at `N`.  After processing `p`, the oriented residual
coordinate is therefore the literal `p`-free background at the large cutoff minus that amplified
old coordinate.  This identifies, without a positivity surrogate, the exact cancellation an
exhaustive CCM-FU budget must establish.
-/

noncomputable section

open Finset

namespace RHTower

/-- **Oriented two-scale renormalization.** Processing a fresh prime subtracts the exact
square-root-amplified old oriented coordinate from its literal large-cutoff background. -/
theorem mobiusDivisorOrientedFibre_insert_mul_prime_renormalization
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    mobiusDivisorOrientedFibre (p * N) (insert p P) R =
      mobiusDivisorOrientedFibre (p * N) P R -
        Real.sqrt p * mobiusDivisorOrientedFibre N P R := by
  unfold mobiusDivisorOrientedFibre
  rw [mobiusDivisorSelectionFibre_insert_mul_prime hp hNp P R hpP hpR]
  ring

/-- The squared oriented coordinate retains the complete cross-scale term.  Positive diagonal
mass alone cannot control this term, which is exactly where a CCM-FU source cancellation law
must act. -/
theorem mobiusDivisorOrientedFibre_insert_mul_prime_square_renormalization
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    (mobiusDivisorOrientedFibre (p * N) (insert p P) R) ^ 2 =
      (mobiusDivisorOrientedFibre (p * N) P R) ^ 2 +
        p * (mobiusDivisorOrientedFibre N P R) ^ 2 -
          2 * Real.sqrt p *
            mobiusDivisorOrientedFibre (p * N) P R *
              mobiusDivisorOrientedFibre N P R := by
  rw [mobiusDivisorOrientedFibre_insert_mul_prime_renormalization
    hp hNp P R hpP hpR]
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt p = p :=
    Real.mul_self_sqrt (Nat.cast_nonneg p)
  nlinarith

/-- A fresh processed prime cancels an oriented residual coordinate exactly only when its
large-cutoff background equals the amplified old coordinate. -/
theorem mobiusDivisorOrientedFibre_insert_mul_prime_eq_zero_iff_background_eq_copy
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    mobiusDivisorOrientedFibre (p * N) (insert p P) R = 0 ↔
      mobiusDivisorOrientedFibre (p * N) P R =
        Real.sqrt p * mobiusDivisorOrientedFibre N P R := by
  rw [mobiusDivisorOrientedFibre_insert_mul_prime_renormalization
    hp hNp P R hpP hpR]
  constructor <;> intro h <;> linarith

end RHTower
