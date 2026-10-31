import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeHeads
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The exact adjunction norm of coherent prime-pole response

On prime-supported packets, the divisor jet's pole coefficients are
`log p / sqrt(p-1)`. Their exact squared norm in adjunction energy is
`sum log p / p`. An explicit packet attains this norm. Mertens' theorem
therefore identifies a necessary logarithmic scale in pole response.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticIntersectionTheory

/-- Restrict a conductor coefficient family to prime conductors. -/
def primeOnly (a : ℕ → ℝ) (m : ℕ) : ℝ := if m.Prime then a m else 0

/-- The pole coefficients of the normalized prime divisor jets. -/
def primePoleResponse (Q : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / Real.sqrt (p.totient : ℝ) * a p

/-- Exact squared adjunction norm of the prime-pole functional. -/
def primePoleScale (Q : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / (p : ℝ)

/-- Coherent prime coefficients attaining the pole-response norm. -/
def primePoleWitness (p : ℕ) : ℝ := Real.sqrt (p.totient : ℝ) / (p : ℝ)

theorem primeAdjunctionMass_primeOnly (Q : ℕ) (a : ℕ → ℝ) :
    primeAdjunctionMass Q (primeOnly a) =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, (Real.log p + tameDifferent p) * a p ^ 2 := by
  rw [primeAdjunctionMass, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp only [primeOnly, if_pos hp]
  · simp only [primeOnly, if_neg hp, zero_pow two_ne_zero, mul_zero]

private theorem prime_adjoint_weight {p : ℕ} (hp : p.Prime) :
    Real.log p + tameDifferent p =
      (Real.log p / (p : ℝ)) * ((p : ℝ) / Real.sqrt (p.totient : ℝ)) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith only [h]
  have ht := tameDifferent_prime_pow hp (show (1 : ℕ) ≠ 0 by decide)
  simp only [pow_one] at ht
  rw [ht, div_pow, Real.sq_sqrt (Nat.cast_nonneg p.totient), Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  field_simp [hp0, hp1]
  ring

private theorem prime_pole_weight {p : ℕ} (hp : p.Prime) (a : ℝ) :
    Real.log p / Real.sqrt (p.totient : ℝ) * a =
      (Real.log p / (p : ℝ)) * ((p : ℝ) / Real.sqrt (p.totient : ℝ) * a) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs : Real.sqrt (p.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp.pos)).ne'
  field_simp [hp0, hs]

theorem primePoleScale_nonneg (Q : ℕ) : 0 ≤ primePoleScale Q :=
  sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem primePoleScale_pos {Q : ℕ} (hQ : 2 ≤ Q) : 0 < primePoleScale Q := by
  have h2 : 2 ∈ (Icc 1 Q).filter Nat.Prime :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨by decide, hQ⟩, Nat.prime_two⟩
  have h := single_le_sum (f := fun p : ℕ => Real.log p / (p : ℝ))
    (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)) h2
  exact (div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)).trans_le h

/-- Weighted Cauchy–Schwarz gives the exact prime-pole bound in adjunction energy. -/
theorem primePoleResponse_sq_le (Q : ℕ) (a : ℕ → ℝ) :
    primePoleResponse Q a ^ 2 ≤ primePoleScale Q * primeAdjunctionMass Q (primeOnly a) := by
  have h := nonnegative_weighted_sum_sq_le ((Icc 1 Q).filter Nat.Prime)
    (fun p => Real.log p / (p : ℝ))
    (fun p => (p : ℝ) / Real.sqrt (p.totient : ℝ) * a p)
    (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hresponse : (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      (Real.log p / (p : ℝ)) * ((p : ℝ) / Real.sqrt (p.totient : ℝ) * a p)) =
      primePoleResponse Q a :=
    sum_congr rfl fun p hp => (prime_pole_weight (mem_filter.mp hp).2 (a p)).symm
  have henergy : (∑ p ∈ (Icc 1 Q).filter Nat.Prime,
      (Real.log p / (p : ℝ)) * ((p : ℝ) / Real.sqrt (p.totient : ℝ) * a p) ^ 2) =
      primeAdjunctionMass Q (primeOnly a) := by
    rw [primeAdjunctionMass_primeOnly]
    apply sum_congr rfl
    intro p hp
    rw [prime_adjoint_weight (mem_filter.mp hp).2, mul_pow]
    ring
  rw [hresponse, henergy] at h
  exact h

private theorem prime_witness_rescale {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / Real.sqrt (p.totient : ℝ) * primePoleWitness p = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs : Real.sqrt (p.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp.pos)).ne'
  rw [primePoleWitness]
  field_simp [hp0, hs]

/-- The coherent prime packet attains the pole-response norm exactly. -/
theorem primePoleWitness_response_and_energy (Q : ℕ) :
    primePoleResponse Q primePoleWitness = primePoleScale Q ∧
      primeAdjunctionMass Q (primeOnly primePoleWitness) = primePoleScale Q := by
  constructor
  · apply sum_congr rfl
    intro p hp
    rw [prime_pole_weight (mem_filter.mp hp).2, prime_witness_rescale (mem_filter.mp hp).2, mul_one]
  · rw [primeAdjunctionMass_primeOnly]
    apply sum_congr rfl
    intro p hp
    rw [prime_adjoint_weight (mem_filter.mp hp).2, mul_assoc, ← mul_pow,
      prime_witness_rescale (mem_filter.mp hp).2, one_pow, mul_one]

/-- The optimal pole-response constant is the prime Mertens mass, with an explicit extremizer. -/
theorem optimal_primePoleResponse_constant_iff {Q : ℕ} (hQ : 2 ≤ Q) (C : ℝ) :
    (∀ a : ℕ → ℝ, primePoleResponse Q a ^ 2 ≤ C * primeAdjunctionMass Q (primeOnly a)) ↔
      primePoleScale Q ≤ C := by
  constructor
  · intro hC
    have h := hC primePoleWitness
    rw [(primePoleWitness_response_and_energy Q).1,
      (primePoleWitness_response_and_energy Q).2] at h
    by_contra hc
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hc) (primePoleScale_pos hQ)
    nlinarith only [h, hm]
  · intro hC a
    exact (primePoleResponse_sq_le Q a).trans
      (mul_le_mul_of_nonneg_right hC (primeAdjunctionMass_nonneg Q (primeOnly a)))

/-- The sharp pole-response constant grows as `log Q`, with an absolute error bound. -/
theorem primePoleScale_logarithmic {Q : ℕ} (hQ : 1 ≤ Q) :
    |primePoleScale Q - Real.log Q| ≤
      (Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail) :=
  _root_.RHTower.Mertens.mertens_first_prime Q hQ

#print axioms primePoleResponse_sq_le
#print axioms primePoleWitness_response_and_energy
#print axioms optimal_primePoleResponse_constant_iff
#print axioms primePoleScale_logarithmic

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
