import GaloisForLFunctions.RHTower.PhotonicPrimeSourceAlgebraAbelianizationNoGo

/-!
# PTR fixed linear-port order/fusion obstruction

For the literal two-slab temporal-Maxwell prime cells, a unital complex-linear
scalar port cannot both forget two-prime order and multiply the first
backtracking pair. The exact survivor is a conic relation between its order
and fusion defects. This excludes the order-blind fixed linear Euler-port
subroute; ordered, nonlinear, nonlocal, and full-cylinder ports remain open.
-/

open Matrix
open scoped Matrix

namespace RHTower

noncomputable section

abbrev PrimeMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Source-fixed two-prime mixed trace, nonzero for distinct primes. -/
def crossScalar (p q : Nat.Primes) : ℂ :=
  Matrix.trace (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q)

/-- Nilpotent deviation of the literal two-slab temporal-Maxwell prime cycle. -/
def primeTwoCycleDeviation (p : Nat.Primes) : PrimeMatrix :=
  photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) - 1

theorem primeTwoCycleDeviation_eq (p : Nat.Primes) :
    primeTwoCycleDeviation p = photonicPrimeDrivenNilpotent p := by
  unfold primeTwoCycleDeviation
  rw [photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell,
    photonicPrimeCyclicTimeCrystalCell_eq_slabCell, pow_two,
    photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent]
  abel

private theorem prime_anticommutator (p q : Nat.Primes) :
    photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q +
      photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p =
        crossScalar p q • (1 : PrimeMatrix) := by
  have hp := photonicPrimeImpedance_ne_zero p
  have hq := photonicPrimeImpedance_ne_zero q
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossScalar, photonicPrimeDrivenNilpotent,
      Matrix.trace_fin_two] <;>
    field_simp [hp, hq] <;> ring

private theorem prime_cross_backtrack_zero (p q : Nat.Primes) :
    (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
      (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p) = 0 := by
  rw [show (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
      (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p) =
      photonicPrimeDrivenNilpotent p *
        (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent q) *
          photonicPrimeDrivenNilpotent p by simp [mul_assoc]]
  rw [photonicPrimeDrivenNilpotent_sq]
  simp

/-- The literal two-prime cells force a conic tradeoff for every complex-linear
scalar port. A port cannot simultaneously erase order and preserve pair fusion. -/
theorem ptr_prime_linear_port_order_fusion_tradeoff
    (p q : Nat.Primes) (L : PrimeMatrix →ₗ[ℂ] ℂ) :
    (L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) -
       L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) ^ (2 : ℕ) -
      4 * (L ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
             (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) -
           L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
             L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) =
      (crossScalar p q) ^ (2 : ℕ) * (L 1) ^ (2 : ℕ) := by
  have hsum := congrArg L (prime_anticommutator p q)
  simp only [map_add, map_smul, smul_eq_mul] at hsum
  rw [prime_cross_backtrack_zero, map_zero]
  calc
    _ = (L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) +
      L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) ^ (2 : ℕ) := by ring
    _ = _ := by rw [hsum]; ring

/-- If an Euler port erases two-prime order, its fourth-grade backtrack
factorization has an exact, nonzero defect. -/
theorem ptr_prime_order_blind_port_fusion_defect
    (p q : Nat.Primes) (L : PrimeMatrix →ₗ[ℂ] ℂ)
    (horder : L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) =
      L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) :
    L ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
        (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) -
      L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
        L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p) =
      -(crossScalar p q) ^ (2 : ℕ) * (L 1) ^ (2 : ℕ) / 4 := by
  have h := ptr_prime_linear_port_order_fusion_tradeoff p q L
  rw [horder, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at h
  rw [horder]
  linear_combination -h / 4

/-- Two actual prime cells exclude every unital complex-linear scalar port
that is both order-blind and multiplicative on the first backtracking word. -/
theorem ptr_no_order_blind_multiplicative_linear_port
    (p q : Nat.Primes) (hpq : p ≠ q) :
    ¬ ∃ L : PrimeMatrix →ₗ[ℂ] ℂ,
        L 1 = 1 ∧
        L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) =
          L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p) ∧
        L ((photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
             (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p)) =
          L (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
            L (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p) := by
  rintro ⟨L, hunital, horder, hfusion⟩
  have h := ptr_prime_linear_port_order_fusion_tradeoff p q L
  rw [hfusion] at h
  rw [horder, sub_self, sub_self, hunital] at h
  norm_num at h
  have ht : crossScalar p q ≠ 0 := by
    intro hz
    have hn := ptr_prime_nilpotent_cross_trace_re_neg p q hpq
    change (crossScalar p q).re < 0 at hn
    rw [hz] at hn
    norm_num at hn
  exact ht (sq_eq_zero_iff.mp h.symm)

/-- The obstruction is about the physical temporal-Maxwell transfers, not a
freely chosen nilpotent model. -/
theorem ptr_no_fixed_linear_euler_port_on_two_cycle_deviations
    (p q : Nat.Primes) (hpq : p ≠ q) :
    ¬ ∃ L : PrimeMatrix →ₗ[ℂ] ℂ,
        L 1 = 1 ∧
        L (primeTwoCycleDeviation p * primeTwoCycleDeviation q) =
          L (primeTwoCycleDeviation q * primeTwoCycleDeviation p) ∧
        L ((primeTwoCycleDeviation p * primeTwoCycleDeviation q) *
             (primeTwoCycleDeviation q * primeTwoCycleDeviation p)) =
          L (primeTwoCycleDeviation p * primeTwoCycleDeviation q) *
            L (primeTwoCycleDeviation q * primeTwoCycleDeviation p) := by
  simpa only [primeTwoCycleDeviation_eq] using
    ptr_no_order_blind_multiplicative_linear_port p q hpq

end
end RHTower
