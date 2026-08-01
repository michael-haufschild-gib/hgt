import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.RHTower.GaussPairedSchattenResidueProducer

/-!
# Canonical diagonal realization of the Gauss-paired Schatten residue

The Gauss-paired endpoint theorems previously required an approximation-number asymptotic for an
unspecified operator.  The universal critical diagonal model supplies an explicit operator:

`aₙ = (gaussPairedChannelResidue m prime / (n + 1)) ^ (1 / (2m))`.

Its critical expression is identically the arithmetic Gauss residue, so the limiting premise is
proved rather than assumed.  The resulting cutoff family escapes every fixed positive Schatten
class unconditionally.

No RH assumption and no numerical computation occur.
-/

open Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- Explicit diagonal `ℓ²` operator realizing the Gauss-paired critical residue. -/
def gaussPairedCriticalDiagonalOperator
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) : EllTwo →L[ℂ] EllTwo :=
  criticalDiagonalOperator ((2 * m : ℕ) : ℝ) (gaussPairedChannelResidue m prime)
    (by exact_mod_cast (show 0 < 2 * m by omega))
    (gaussPairedChannelResidue_pos hm prime)

/-- The critical Gauss expression is a constant sequence, hence has the required asymptotic. -/
theorem tendsto_gaussPairedCriticalDiagonalOperator_approxNumber_rpow_mul_succ
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) :
    Tendsto
      (fun n : ℕ =>
        approxNumber (gaussPairedCriticalDiagonalOperator hm prime) n ^
            ((2 * m : ℕ) : ℝ) * ((n : ℝ) + 1))
      atTop (nhds (gaussPairedChannelResidue m prime)) := by
  simpa [gaussPairedCriticalDiagonalOperator] using
    tendsto_criticalDiagonalOperator_approxNumber_rpow_mul_succ
      ((2 * m : ℕ) : ℝ) (gaussPairedChannelResidue m prime)
      (by exact_mod_cast (show 0 < 2 * m by omega))
      (gaussPairedChannelResidue_pos hm prime)

/-- The explicit diagonal operator carries the Gauss-paired logarithmic Schatten residue. -/
theorem hasSchattenLogResidue_gaussPairedCriticalDiagonalOperator
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) :
    HasSchattenLogResidue ((2 * m : ℕ) : ℝ)
      (gaussPairedCriticalDiagonalOperator hm prime)
      (gaussPairedChannelResidue m prime) :=
  hasSchattenLogResidue_gaussPairedChannelResidue prime
    (tendsto_gaussPairedCriticalDiagonalOperator_approxNumber_rpow_mul_succ hm prime)

/-- The explicit realization has exact Schatten depth `2m`, with no weak-class or residue premise. -/
theorem gaussPairedCriticalDiagonalOperator_exact_schattenDepth
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) :
    (∀ q : ℝ, 0 < q → q ≤ (2 * m : ℕ) →
        ¬ MemSchattenClass q (gaussPairedCriticalDiagonalOperator hm prime)) ∧
      (∀ q : ℝ, (2 * m : ℕ) < q →
        MemSchattenClass q (gaussPairedCriticalDiagonalOperator hm prime)) :=
  gaussPairedChannel_exact_schattenDepth_of_asymptotic hm prime
    (tendsto_gaussPairedCriticalDiagonalOperator_approxNumber_rpow_mul_succ hm prime)

/-- Canonical cutoff family; empty prime apertures use the zero operator. -/
def gaussPairedCutoffCriticalDiagonalOperator
    (prime : ∀ N, Fin (Nat.primeCounting N) → Nat.Primes) (N : ℕ) :
    EllTwo →L[ℂ] EllTwo :=
  if hN : Nat.primeCounting N = 0 then 0 else
    letI : Nonempty (Fin (Nat.primeCounting N)) :=
      ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
    gaussPairedCriticalDiagonalOperator (Nat.one_le_iff_ne_zero.mpr hN) (prime N)

/-- Every nonempty cutoff in the canonical family has the exact Gauss critical asymptotic. -/
theorem tendsto_gaussPairedCutoffCriticalDiagonalOperator_approxNumber_rpow_mul_succ
    (prime : ∀ N, Fin (Nat.primeCounting N) → Nat.Primes)
    (N : ℕ) (hN : Nat.primeCounting N ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        approxNumber (gaussPairedCutoffCriticalDiagonalOperator prime N) n ^
            ((gaussPairedCriticalDepth N : ℕ) : ℝ) * ((n : ℝ) + 1))
      atTop (nhds (gaussPairedChannelResidue (Nat.primeCounting N) (prime N))) := by
  letI : Nonempty (Fin (Nat.primeCounting N)) :=
    ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
  simpa [gaussPairedCutoffCriticalDiagonalOperator, hN, gaussPairedCriticalDepth] using
    tendsto_gaussPairedCriticalDiagonalOperator_approxNumber_rpow_mul_succ
      (Nat.one_le_iff_ne_zero.mpr hN) (prime N)

/-- **Unconditional cofinal exclusion.**  The explicit Gauss cutoff family escapes every fixed
positive Schatten class. -/
theorem exists_cutoff_gaussPairedCutoffCriticalDiagonalOperator_not_memSchattenClass
    (prime : ∀ N, Fin (Nat.primeCounting N) → Nat.Primes)
    (q : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ¬ MemSchattenClass q (gaussPairedCutoffCriticalDiagonalOperator prime N) :=
  exists_cutoff_not_memSchattenClass_of_asymptotic
    (gaussPairedCutoffCriticalDiagonalOperator prime) prime
    (tendsto_gaussPairedCutoffCriticalDiagonalOperator_approxNumber_rpow_mul_succ prime) q hq

end

end RHTower
