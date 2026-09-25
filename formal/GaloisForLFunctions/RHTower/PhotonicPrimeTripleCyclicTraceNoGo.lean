import GaloisForLFunctions.RHTower.PhotonicPrimeSourceFrameNoncommutativityNoGo

/-!
# Three-prime cyclic-trace orientation of the literal Maxwell source

The trace hides the order of two source transfers. At three distinct primes it
does not: the antisymmetric trace is an explicit nonzero Vandermonde expression
in the physical prime log-impedances. Thus taking the raw cyclic trace does not
repair the order-insensitive Euler landing excluded at matrix level. The
positive survivor is a source-defined ordered three-prime orientation current.

This concerns the literal temporal-Maxwell slab source, not the separate
rotating-cylinder transmission relation or all possible scalar readouts.
-/

open Matrix
open scoped Matrix

namespace RHTower

/-- The ordered three-prime source orientation is an exact prime-log
Vandermonde divided by the three log-impedances. -/
theorem ptr_prime_triple_nilpotent_trace (p q r : Nat.Primes) :
    Matrix.trace ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
      photonicPrimeDrivenNilpotent r) =
      (1728 / 125 : ℂ) *
        (photonicPrimeImpedance q - photonicPrimeImpedance p) *
        (photonicPrimeImpedance r - photonicPrimeImpedance q) *
        (photonicPrimeImpedance p - photonicPrimeImpedance r) /
        (photonicPrimeImpedance p * photonicPrimeImpedance q *
          photonicPrimeImpedance r) := by
  have hp := photonicPrimeImpedance_ne_zero p
  have hq := photonicPrimeImpedance_ne_zero q
  have hr := photonicPrimeImpedance_ne_zero r
  simp only [Matrix.trace_fin_two]
  simp [photonicPrimeDrivenNilpotent]
  field_simp [hp, hq, hr]
  ring

private theorem impedance_ne_of_prime_ne (p q : Nat.Primes) (hpq : p ≠ q) :
    photonicPrimeImpedance p ≠ photonicPrimeImpedance q := by
  intro h
  have hre : Real.log (((p : ℕ) : ℝ)) = Real.log (((q : ℕ) : ℝ)) := by
    change (Real.log (((p : ℕ) : ℝ)) : ℂ) =
      (Real.log (((q : ℕ) : ℝ)) : ℂ) at h
    exact_mod_cast h
  have hcast : (((p : ℕ) : ℝ)) = (((q : ℕ) : ℝ)) :=
    Real.log_injOn_pos
      (Set.mem_Ioi.mpr (by exact_mod_cast p.property.pos))
      (Set.mem_Ioi.mpr (by exact_mod_cast q.property.pos)) hre
  exact hpq (Subtype.ext (by exact_mod_cast hcast))

/-- Reversing two distinct prime cells reverses the cubic trace orientation. -/
theorem ptr_prime_triple_nilpotent_trace_reverse (p q r : Nat.Primes) :
    Matrix.trace ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent r) *
      photonicPrimeDrivenNilpotent q) =
      -Matrix.trace ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
        photonicPrimeDrivenNilpotent r) := by
  rw [ptr_prime_triple_nilpotent_trace, ptr_prime_triple_nilpotent_trace]
  ring

/-- The source orientation never vanishes on a triple of distinct primes. -/
theorem ptr_prime_triple_nilpotent_trace_ne_zero (p q r : Nat.Primes)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    Matrix.trace ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
      photonicPrimeDrivenNilpotent r) ≠ 0 := by
  rw [ptr_prime_triple_nilpotent_trace]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact sub_ne_zero.mpr (impedance_ne_of_prime_ne q p hpq.symm)
      · exact sub_ne_zero.mpr (impedance_ne_of_prime_ne r q hqr.symm)
    · exact sub_ne_zero.mpr (impedance_ne_of_prime_ne p r hpr)
  · exact mul_ne_zero (mul_ne_zero
      (photonicPrimeImpedance_ne_zero p)
      (photonicPrimeImpedance_ne_zero q))
      (photonicPrimeImpedance_ne_zero r)

private theorem trace_three_word_diff (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (((1 + A) * (1 + B)) * (1 + C)) -
      Matrix.trace (((1 + A) * (1 + C)) * (1 + B)) =
      Matrix.trace ((A * B) * C) - Matrix.trace ((A * C) * B) := by
  have hmat :
      (((1 + A) * (1 + B)) * (1 + C)) -
        (((1 + A) * (1 + C)) * (1 + B)) =
        (B * C - C * B) + ((A * B) * C - (A * C) * B) := by
    noncomm_ring
  have htrace := congrArg Matrix.trace hmat
  simpa [Matrix.trace_mul_comm B C] using htrace

private theorem source_transfer_two_cycle (p : Nat.Primes) :
    photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) =
      1 + photonicPrimeDrivenNilpotent p := by
  rw [photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell,
    photonicPrimeCyclicTimeCrystalCell_eq_slabCell, pow_two,
    photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent]

/-- Raw cyclic trace of three literal Maxwell prime two-cycles is physically
order-sensitive. Hence it cannot itself descend to a commutative prime-
occupation/Euler readout. -/
theorem ptr_prime_source_triple_cyclic_trace_order_ne (p q r : Nat.Primes)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    Matrix.trace (((photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ)) *
      (photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ))) *
      (photonicPrimeTemporalMaxwellCyclicTransfer r ^ (2 : ℕ))) ≠
    Matrix.trace (((photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ)) *
      (photonicPrimeTemporalMaxwellCyclicTransfer r ^ (2 : ℕ))) *
      (photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ))) := by
  rw [source_transfer_two_cycle, source_transfer_two_cycle,
    source_transfer_two_cycle]
  intro heq
  have hdiff := trace_three_word_diff
    (photonicPrimeDrivenNilpotent p)
    (photonicPrimeDrivenNilpotent q)
    (photonicPrimeDrivenNilpotent r)
  rw [heq, sub_self, ptr_prime_triple_nilpotent_trace_reverse p q r] at hdiff
  have hz : Matrix.trace
      ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
        photonicPrimeDrivenNilpotent r) = 0 := by
    have htwo : (2 : ℂ) * Matrix.trace
        ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
          photonicPrimeDrivenNilpotent r) = 0 := by
      calc
        _ = Matrix.trace
            ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
              photonicPrimeDrivenNilpotent r) -
            -Matrix.trace
              ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
                photonicPrimeDrivenNilpotent r) := by ring
        _ = 0 := hdiff.symm
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ptr_prime_triple_nilpotent_trace_ne_zero p q r hpq hqr hpr hz

end RHTower
