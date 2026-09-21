import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadProcessedCoreHomothety

/-!
# Bilinear homothety of copied CCM-FU core sectors

One processed prime dilation does not merely preserve a selected pair of old
processed-core coordinates.  Every finite bilinear observer of the entire
copied core sector is multiplied exactly by the dilation prime.  The observer
may be signed, off-diagonal, and depend arbitrarily on the two old cores.

Consequently no cancellation or contraction of inherited core-changing
covariance can arise inside the replicated sector itself.  A CCM-FU schedule
must use a quantitatively controlled interaction with the genuinely new,
`p`-free background.  This theorem makes no claim about that background or
about a global schedule.
-/

noncomputable section

open Finset

namespace RHTower

/-- A finite bilinear observer of processed-core source fibres at two residual labels. -/
def mobiusDivisorProcessedCoreBilinear
    (M : ℕ) (P R S : Finset ℕ) (w : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
    w A B * mobiusDivisorSelectionProcessedCoreFibre M P A R *
      mobiusDivisorSelectionProcessedCoreFibre M P B S

/-- The part of the same observer carried by the canonical old-core copy in a prime-dilated
child field.  It deliberately excludes the new `p`-free background and every background/copy
cross term. -/
def mobiusDivisorProcessedCoreChildCopyBilinear
    (N p : ℕ) (P R S : Finset ℕ) (w : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
    w A B * mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R *
      mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p B) S

/-- **Copied-sector bilinear homothety.** Every finite signed or unsigned core-pair observer
of the inherited sector scales by the positive factor `p` under a fresh prime dilation. -/
theorem mobiusDivisorProcessedCoreChildCopyBilinear_eq_scale
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P R S : Finset ℕ) (hpP : p ∉ P) (w : Finset ℕ → Finset ℕ → ℝ) :
    mobiusDivisorProcessedCoreChildCopyBilinear N p P R S w =
      (p : ℝ) * mobiusDivisorProcessedCoreBilinear N P R S w := by
  unfold mobiusDivisorProcessedCoreChildCopyBilinear
    mobiusDivisorProcessedCoreBilinear
  calc
    (∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
      w A B * mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p A) R *
        mobiusDivisorSelectionProcessedCoreFibre (p * N) (insert p P) (insert p B) S) =
      ∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
        (p : ℝ) * (w A B * mobiusDivisorSelectionProcessedCoreFibre N P A R *
          mobiusDivisorSelectionProcessedCoreFibre N P B S) := by
        apply Finset.sum_congr rfl
        intro A hA
        apply Finset.sum_congr rfl
        intro B hB
        have hpA : p ∉ A := by
          intro hpA
          exact hpP (Finset.mem_powerset.mp hA hpA)
        have hpB : p ∉ B := by
          intro hpB
          exact hpP (Finset.mem_powerset.mp hB hpB)
        rw [mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P A R hpA,
          mobiusDivisorSelectionProcessedCoreFibre_insert_mul_prime hp hNp P B S hpB]
        calc
          w A B * (-Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P A R) *
              (-Real.sqrt p * mobiusDivisorSelectionProcessedCoreFibre N P B S) =
            (Real.sqrt p * Real.sqrt p) *
              (w A B * mobiusDivisorSelectionProcessedCoreFibre N P A R *
                mobiusDivisorSelectionProcessedCoreFibre N P B S) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg p)]
    _ = (p : ℝ) * (∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
        w A B * mobiusDivisorSelectionProcessedCoreFibre N P A R *
          mobiusDivisorSelectionProcessedCoreFibre N P B S) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.mul_sum]

end RHTower
