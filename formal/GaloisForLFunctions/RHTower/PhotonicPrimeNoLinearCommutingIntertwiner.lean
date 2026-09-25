import GaloisForLFunctions.RHTower.PhotonicPrimeSourceAlgebraAbelianizationNoGo

/-!
# No fixed linear descent from literal prime Maxwell cells to commuting occupations

## PTR proof-chain position

The literal temporal-Maxwell prime cells would need a source-fixed port into a
commutative arithmetic occupation action before their parabolic transfers could
serve as Euler factors. This module tests the entire finite-dimensional *linear
intertwiner* class, including noninvertible projections and arbitrarily enlarged
commuting target states.

For two distinct primes, the source commutator has nonzero scalar square. An
intertwiner into commuting target actions must annihilate that commutator, so it
is zero. This closes the fixed-linear temporal-slab descent, not an ordered,
nonlinear, nonlocal, or rotating-cylinder PTR source. It does not prove RH.
-/

open Matrix
open scoped Matrix

namespace RHTower

private theorem no_intertwiner_of_commutator_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (U V : Matrix ι ι ℂ) (J : Matrix ι (Fin 2) ℂ) (t : ℂ)
    (ht : t ≠ 0)
    (hsq : (A * B - B * A) ^ (2 : ℕ) =
      t ^ (2 : ℕ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (hUV : U * V = V * U)
    (hA : J * A = U * J) (hB : J * B = V * J) : J = 0 := by
  have hzero : J * (A * B - B * A) = 0 := by
    calc
      J * (A * B - B * A) = (J * A) * B - (J * B) * A := by
        simp only [Matrix.mul_sub, Matrix.mul_assoc]
      _ = (U * J) * B - (V * J) * A := by rw [hA, hB]
      _ = U * (V * J) - V * (U * J) := by
        simp only [Matrix.mul_assoc, hB, hA]
      _ = 0 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUV, sub_self]
  have hzero2 : J * (A * B - B * A) ^ (2 : ℕ) = 0 := by
    rw [pow_two, ← Matrix.mul_assoc, hzero, Matrix.zero_mul]
  rw [hsq] at hzero2
  have hscalar : t ^ (2 : ℕ) • J = 0 := by simpa using hzero2
  exact (smul_eq_zero.mp hscalar).resolve_left (pow_ne_zero _ ht)

private theorem source_cell_eq (p : Nat.Primes) :
    photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) =
      1 + photonicPrimeDrivenNilpotent p := by
  rw [photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell,
    photonicPrimeCyclicTimeCrystalCell_eq_slabCell, pow_two,
    photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent]

/-- **Source-level fixed-linear descent no-go.** Every finite-dimensional
commuting arithmetic target, even an enlarged one, admits only the zero
intertwiner from the same literal two-channel temporal-Maxwell state when two
distinct prime cells are retained. No faithfulness or invertibility is assumed
of the port. -/
theorem ptr_no_nonzero_fixed_linear_commuting_target_intertwiner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : Nat.Primes) (hpq : p ≠ q)
    (U V : Matrix ι ι ℂ) (J : Matrix ι (Fin 2) ℂ)
    (hUV : U * V = V * U)
    (hp : J * (photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ)) = U * J)
    (hq : J * (photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ)) = V * J) :
    J = 0 := by
  let A := photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ)
  let B := photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ)
  let t := Matrix.trace (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q)
  have ht : t ≠ 0 := by
    intro h
    have hneg := ptr_prime_nilpotent_cross_trace_re_neg p q hpq
    change Matrix.trace
      (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) = 0 at h
    rw [h] at hneg
    norm_num at hneg
  have hsq : (A * B - B * A) ^ (2 : ℕ) =
      t ^ (2 : ℕ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp [A, B, t]
    rw [source_cell_eq, source_cell_eq]
    have heq :
        (1 + photonicPrimeDrivenNilpotent p) * (1 + photonicPrimeDrivenNilpotent q) -
          (1 + photonicPrimeDrivenNilpotent q) * (1 + photonicPrimeDrivenNilpotent p) =
        photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q -
          photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p := by
      noncomm_ring
    rw [heq]
    exact ptr_prime_source_commutator_sq p q
  exact no_intertwiner_of_commutator_sq A B U V J t ht hsq hUV hp hq

end RHTower
