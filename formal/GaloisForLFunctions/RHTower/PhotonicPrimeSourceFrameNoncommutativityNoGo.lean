import GaloisForLFunctions.RHTower.PhotonicTemporalMaxwellSlabRealization

/-!
# Literal prime Maxwell cells have no commutative occupation lift

The corpus's source-free temporal-Maxwell prime cell has a parabolic two-cycle,
but its fixed physical state `(D,B)` is not the same as the prime-dependent
Jordan frame used to display `photonicParabolic`.  The nilpotent part of the
two-cycle has a prime-dependent fixed line of slope `-2 log p`.

This file classifies that line and computes a strictly negative cross-prime
trace invariant.  Distinct literal prime cells have no common nonzero fixed
vector, no common invertible Jordan frame (even with different parabolic
powers), and do not commute.  Consequently the commutative prime-occupation
monoid cannot map its prime generators multiplicatively to these literal
physical transfers.  An ordered or nonlocal source construction remains open.

This is a source-assembly no-go, not a rotating-cylinder transmission theorem
or an RH proof.
-/

open Matrix
open scoped Matrix

namespace RHTower

private theorem ptr_prime_impedance_ne_of_ne (p q : Nat.Primes) (hpq : p ≠ q) :
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
  have hnat : (p : ℕ) = (q : ℕ) := by exact_mod_cast hcast
  exact hpq (Subtype.ext hnat)

/-- **Positive survivor:** the source-derived cross-prime invariant is the
negative square of the difference of the logarithmic frame coordinates. -/
theorem ptr_prime_nilpotent_cross_trace (p q : Nat.Primes) :
    Matrix.trace (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) =
      -(144 / 25 : ℂ) *
        (photonicPrimeImpedance p - photonicPrimeImpedance q) ^ 2 /
          (photonicPrimeImpedance p * photonicPrimeImpedance q) := by
  have hp := photonicPrimeImpedance_ne_zero p
  have hq := photonicPrimeImpedance_ne_zero q
  simp only [Matrix.trace_fin_two]
  simp [photonicPrimeDrivenNilpotent]
  field_simp [hp, hq]
  ring

/-- The mixed trace is strictly negative for distinct literal prime cells. -/
theorem ptr_prime_nilpotent_cross_trace_re_neg (p q : Nat.Primes)
    (hpq : p ≠ q) :
    (Matrix.trace
      (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q)).re < 0 := by
  let lp : ℝ := Real.log (((p : ℕ) : ℝ))
  let lq : ℝ := Real.log (((q : ℕ) : ℝ))
  have hp : 0 < lp := Nat.Prime.log_pos p.property
  have hq : 0 < lq := Nat.Prime.log_pos q.property
  have hne : lp ≠ lq := by
    intro he
    have hpqreal : (((p : ℕ) : ℝ)) = (((q : ℕ) : ℝ)) :=
      Real.log_injOn_pos
        (Set.mem_Ioi.mpr (by exact_mod_cast p.property.pos))
        (Set.mem_Ioi.mpr (by exact_mod_cast q.property.pos)) he
    exact hpq (Subtype.ext (by exact_mod_cast hpqreal))
  have hratio : 0 < (lp - lq) ^ 2 / (lp * lq) :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (mul_pos hp hq)
  have heq : Matrix.trace
      (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) =
      ((-(144 / 25 : ℝ) * (lp - lq) ^ 2 / (lp * lq) : ℝ) : ℂ) := by
    rw [ptr_prime_nilpotent_cross_trace]
    simp [lp, lq, photonicPrimeImpedance]
  rw [heq, Complex.ofReal_re]
  calc
    -(144 / 25 : ℝ) * (lp - lq) ^ 2 / (lp * lq) =
        -(144 / 25 : ℝ) * ((lp - lq) ^ 2 / (lp * lq)) := by ring
    _ < 0 := mul_neg_of_neg_of_pos (by norm_num) hratio

private theorem ptr_prime_nilpotents_noncommute (p q : Nat.Primes) (hpq : p ≠ q) :
    photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q ≠
      photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p := by
  intro hcomm
  have hsq : (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) ^
      (2 : ℕ) = 0 := by
    calc
      _ = photonicPrimeDrivenNilpotent p *
          (photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p) *
            photonicPrimeDrivenNilpotent q := by simp [pow_two, mul_assoc]
      _ = photonicPrimeDrivenNilpotent p *
          (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) *
            photonicPrimeDrivenNilpotent q := by rw [hcomm]
      _ = 0 := by
        rw [← mul_assoc, photonicPrimeDrivenNilpotent_sq]
        simp
  have htr : Matrix.trace
      (photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hsq⟩).eq_zero
  have hneg := ptr_prime_nilpotent_cross_trace_re_neg p q hpq
  rw [htr] at hneg
  norm_num at hneg

/-- Exact projective fixed line of one literal prime Maxwell two-cycle. -/
theorem ptr_prime_nilpotent_kernel_iff (p : Nat.Primes) (v : Fin 2 → ℂ) :
    photonicPrimeDrivenNilpotent p *ᵥ v = 0 ↔
      v 1 = -2 * photonicPrimeImpedance p * v 0 := by
  have hp := photonicPrimeImpedance_ne_zero p
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    simp [photonicPrimeDrivenNilpotent, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h0
    field_simp [hp] at h0
    linear_combination (-1 / 6 : ℂ) * h0
  · intro h
    funext i
    fin_cases i <;>
      simp [photonicPrimeDrivenNilpotent, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, h] <;> field_simp [hp] <;> ring

private theorem ptr_no_common_prime_nilpotent_kernel (p q : Nat.Primes)
    (hpq : p ≠ q) (v : Fin 2 → ℂ)
    (hp : photonicPrimeDrivenNilpotent p *ᵥ v = 0)
    (hq : photonicPrimeDrivenNilpotent q *ᵥ v = 0) : v = 0 := by
  have he_p := (ptr_prime_nilpotent_kernel_iff p v).mp hp
  have he_q := (ptr_prime_nilpotent_kernel_iff q v).mp hq
  have hL := ptr_prime_impedance_ne_of_ne p q hpq
  have hx : v 0 = 0 := by
    have hmul : (photonicPrimeImpedance p - photonicPrimeImpedance q) * v 0 = 0 := by
      linear_combination (1 / 2 : ℂ) * he_p - (1 / 2 : ℂ) * he_q
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hL)
  have hy : v 1 = 0 := by rw [he_p, hx]; ring
  funext i
  fin_cases i <;> simp [hx, hy]

private theorem ptr_source_transfer_fixed_iff_nilpotent_kernel (p : Nat.Primes)
    (v : Fin 2 → ℂ) :
    photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) *ᵥ v = v ↔
      photonicPrimeDrivenNilpotent p *ᵥ v = 0 := by
  rw [photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell,
    photonicPrimeCyclicTimeCrystalCell_eq_slabCell, pow_two,
    photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, add_eq_left]

/-- Distinct literal source-free temporal-Maxwell prime cells have no common
nonzero vector fixed by both physical two-cycle transfers. -/
theorem ptr_no_common_source_transfer_fixed_vector (p q : Nat.Primes)
    (hpq : p ≠ q) (v : Fin 2 → ℂ)
    (hp : photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) *ᵥ v = v)
    (hq : photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ) *ᵥ v = v) :
    v = 0 := by
  exact ptr_no_common_prime_nilpotent_kernel p q hpq v
    ((ptr_source_transfer_fixed_iff_nilpotent_kernel p v).mp hp)
    ((ptr_source_transfer_fixed_iff_nilpotent_kernel q v).mp hq)

/-- No invertible physical frame simultaneously puts two distinct literal
prime cells into powers of the same fixed parabolic Jordan block. -/
theorem ptr_no_common_source_jordan_frame (p q : Nat.Primes)
    (m n : ℕ) (hpq : p ≠ q) :
    ¬ ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B.det ≠ 0 ∧
      photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) * B =
        B * photonicParabolic ^ m ∧
      photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ) * B =
        B * photonicParabolic ^ n := by
  rintro ⟨B, hdet, hBp, hBq⟩
  let v : Fin 2 → ℂ := fun i => B i 0
  have hfix (r : Nat.Primes) (k : ℕ)
      (hBr : photonicPrimeTemporalMaxwellCyclicTransfer r ^ (2 : ℕ) * B =
        B * photonicParabolic ^ k) :
      photonicPrimeTemporalMaxwellCyclicTransfer r ^ (2 : ℕ) *ᵥ v = v := by
    funext i
    have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i 0) hBr
    simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, photonicParabolic_pow, photonicUpper] using hi
  have hv := ptr_no_common_source_transfer_fixed_vector p q hpq v
    (hfix p m hBp) (hfix q n hBq)
  have h00 : B 0 0 = 0 := congrFun hv 0
  have h10 : B 1 0 = 0 := congrFun hv 1
  apply hdet
  simp [Matrix.det_fin_two, h00, h10]

/-- Prime-cell order is physically visible in the fixed Maxwell state: two
distinct source-derived parabolic two-cycles do not commute. -/
theorem ptr_source_transfers_noncommute (p q : Nat.Primes) (hpq : p ≠ q) :
    photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) *
        photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ) ≠
      photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ) *
        photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) := by
  have hsource (r : Nat.Primes) :
      photonicPrimeTemporalMaxwellCyclicTransfer r ^ (2 : ℕ) =
        1 + photonicPrimeDrivenNilpotent r := by
    rw [photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell,
      photonicPrimeCyclicTimeCrystalCell_eq_slabCell, pow_two,
      photonicPrimeCyclicSlabCell_sq_eq_one_add_nilpotent]
  intro hcomm
  rw [hsource p, hsource q] at hcomm
  apply ptr_prime_nilpotents_noncommute p q hpq
  calc
    photonicPrimeDrivenNilpotent p * photonicPrimeDrivenNilpotent q =
        (1 + photonicPrimeDrivenNilpotent p) *
          (1 + photonicPrimeDrivenNilpotent q) -
          (1 + photonicPrimeDrivenNilpotent p + photonicPrimeDrivenNilpotent q) := by
      noncomm_ring
    _ = (1 + photonicPrimeDrivenNilpotent q) *
          (1 + photonicPrimeDrivenNilpotent p) -
          (1 + photonicPrimeDrivenNilpotent p + photonicPrimeDrivenNilpotent q) := by
      rw [hcomm]
    _ = photonicPrimeDrivenNilpotent q * photonicPrimeDrivenNilpotent p := by
      noncomm_ring

/-- **Source-level PTR no-go.** No order-insensitive multiplicative map from
the commutative prime-occupation monoid sends each generator to its literal
physical temporal-Maxwell two-cycle. -/
theorem ptr_no_commutative_occupation_lift_of_literal_source :
    ¬ ∃ F : (Nat.Primes →₀ ℕ) → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ ν μ, F (ν + μ) = F ν * F μ) ∧
      (∀ p : Nat.Primes,
        F (Finsupp.single p 1) =
          photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ)) := by
  rintro ⟨F, hmul, hprime⟩
  let p : Nat.Primes := ⟨2, by norm_num⟩
  let q : Nat.Primes := ⟨3, by norm_num⟩
  have hpq : p ≠ q := by decide
  apply ptr_source_transfers_noncommute p q hpq
  calc
    photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) *
        photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ) =
        F (Finsupp.single p 1 + Finsupp.single q 1) := by
          rw [hmul, hprime, hprime]
    _ = F (Finsupp.single q 1 + Finsupp.single p 1) := by rw [add_comm]
    _ = photonicPrimeTemporalMaxwellCyclicTransfer q ^ (2 : ℕ) *
          photonicPrimeTemporalMaxwellCyclicTransfer p ^ (2 : ℕ) := by
            rw [hmul, hprime, hprime]

end RHTower
