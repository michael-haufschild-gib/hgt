import GaloisForLFunctions.RHTower.Sieve.LocalizedReciprocalMoebiusAmplitude
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.DeletionSignedSupportColumn
open Sieve
attribute [local instance] Classical.propDecidable

private theorem weighted_filter_card_exchange {α β : Type*}
    (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [Pdec : (d : α) → DecidablePred (P d)] (w : α → ℝ) :
    ∑ d ∈ s, w d * ((t.filter (P d)).card : ℝ) =
      ∑ n ∈ t, ∑ d ∈ s, w d * (if P d n then 1 else 0) := by
  have hcard (d : α) : ((t.filter (P d)).card : ℝ) =
      ∑ n ∈ t, if P d n then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]

/-- Exact signed exchange for the complete Euler-deletion support column. -/
theorem signed_support_floor_column_exchange (N R : ℕ) :
    ∑ d ∈ Icc 1 N,
      ((μ d : ℤ) : ℝ) * (R / d : ℕ) *
        (((Icc 1 R).filter (primeSupportedOn d)).card : ℝ) =
      ∑ n ∈ Icc 1 R, ∑ d ∈ Icc 1 N,
        ((μ d : ℤ) : ℝ) * (R / d : ℕ) *
          (if primeSupportedOn d n then 1 else 0) := by
  simpa [mul_assoc] using
    (weighted_filter_card_exchange (Icc 1 N) (Icc 1 R) primeSupportedOn
      (fun d => ((μ d : ℤ) : ℝ) * (R / d : ℕ)))

/-- On positive inputs, prime support is exactly inclusion of prime-factor sets. -/
theorem primeSupportedOn_iff_primeFactors_subset {d n : ℕ}
    (hd : d ≠ 0) (hn : n ≠ 0) :
    primeSupportedOn d n ↔ n.primeFactors ⊆ d.primeFactors := by
  constructor
  · intro hs p hp
    rcases (Nat.mem_primeFactors_of_ne_zero hn).mp hp with ⟨hpp, hpn⟩
    exact (Nat.mem_primeFactors_of_ne_zero hd).mpr ⟨hpp, hs p hpp hpn⟩
  · intro hs p hpp hpn
    have hp : p ∈ n.primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero hn).mpr ⟨hpp, hpn⟩
    exact (Nat.mem_primeFactors_of_ne_zero hd).mp (hs hp) |>.2

/-- On positive inputs, support is divisibility by the product of its distinct primes. -/
theorem primeSupportedOn_iff_prod_primeFactors_dvd {d n : ℕ}
    (hd : d ≠ 0) (hn : n ≠ 0) :
    primeSupportedOn d n ↔ (∏ p ∈ n.primeFactors, p) ∣ d := by
  rw [primeSupportedOn_iff_primeFactors_subset hd hn,
    ← Nat.prod_primeFactors_dvd_iff hd]

/-- At every positive coordinate, the signed Euler-deletion support column is exactly a finite
coprime Möbius column after extracting the product of the coordinate's distinct primes. -/
theorem signed_floor_support_coordinate_reindex (N R n : ℕ) (hn : 0 < n) :
    ∑ d ∈ Icc 1 N,
      ((μ d : ℤ) : ℝ) * (R / d : ℕ) *
        (if primeSupportedOn d n then 1 else 0) =
      ∑ j ∈ (Icc 1 (N / (∏ p ∈ n.primeFactors, p))).filter
          (fun j => (∏ p ∈ n.primeFactors, p).Coprime j),
        ((μ (∏ p ∈ n.primeFactors, p) : ℤ) : ℝ) * ((μ j : ℤ) : ℝ) *
          (R / ((∏ p ∈ n.primeFactors, p) * j) : ℕ) := by
  let e : ℕ := ∏ p ∈ n.primeFactors, p
  have hepos : 0 < e := by
    dsimp [e]
    exact Finset.prod_pos fun p hp =>
      (Nat.mem_primeFactors.mp hp).1.pos
  have hterm (d : ℕ) (hd : d ∈ Icc 1 N) :
      ((μ d : ℤ) : ℝ) * (R / d : ℕ) *
          (if primeSupportedOn d n then 1 else 0) =
        if e ∣ d then ((μ d : ℤ) : ℝ) * (R / d : ℕ) else 0 := by
    have hd0 : d ≠ 0 := Nat.ne_of_gt
      (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)
    have hsupp : primeSupportedOn d n ↔ e ∣ d := by
      simpa only [e] using primeSupportedOn_iff_prod_primeFactors_dvd hd0 hn.ne'
    rw [hsupp]
    split_ifs <;> ring
  rw [sum_congr rfl hterm, ← Finset.sum_filter]
  simpa [e, mul_assoc] using
    (Sieve.sum_filter_dvd_moebius_scaled (e := e) (N := N) hepos
      (fun d => (R / d : ℕ)))

/-- The complete signed support column is a finite sum of its exact coprime Möbius columns.
No support-level sign has been discarded. -/
theorem signed_support_floor_column_full_reindex (N R : ℕ) :
    ∑ d ∈ Icc 1 N,
      ((μ d : ℤ) : ℝ) * (R / d : ℕ) *
        (((Icc 1 R).filter (primeSupportedOn d)).card : ℝ) =
      ∑ n ∈ Icc 1 R,
        ∑ j ∈ (Icc 1 (N / (∏ p ∈ n.primeFactors, p))).filter
            (fun j => (∏ p ∈ n.primeFactors, p).Coprime j),
          ((μ (∏ p ∈ n.primeFactors, p) : ℤ) : ℝ) * ((μ j : ℤ) : ℝ) *
            (R / ((∏ p ∈ n.primeFactors, p) * j) : ℕ) := by
  rw [signed_support_floor_column_exchange]
  apply sum_congr rfl
  intro n hn
  exact signed_floor_support_coordinate_reindex N R n
    (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1)

/-- Exact support exchange for the reciprocal signed column occurring in the Euler-deletion
coprime head. -/
theorem signed_support_reciprocal_column_exchange (N t : ℕ) :
    ∑ d ∈ Icc 1 N,
      ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (((Icc 1 t).filter (primeSupportedOn d)).card : ℝ) =
      ∑ n ∈ Icc 1 t, ∑ d ∈ Icc 1 N,
        ((μ d : ℤ) : ℝ) / (d : ℝ) *
          (if primeSupportedOn d n then 1 else 0) := by
  simpa [mul_assoc] using
    (weighted_filter_card_exchange (Icc 1 N) (Icc 1 t) primeSupportedOn
      (fun d => ((μ d : ℤ) : ℝ) / (d : ℝ)))

/-- A fixed reciprocal support coordinate is exactly its finite coprime Möbius reciprocal tail. -/
theorem signed_reciprocal_support_coordinate_reindex (N n : ℕ) (hn : 0 < n) :
    ∑ d ∈ Icc 1 N,
      ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (if primeSupportedOn d n then 1 else 0) =
      ∑ j ∈ (Icc 1 (N / (∏ p ∈ n.primeFactors, p))).filter
          (fun j => (∏ p ∈ n.primeFactors, p).Coprime j),
        ((μ (∏ p ∈ n.primeFactors, p) : ℤ) : ℝ) * ((μ j : ℤ) : ℝ) /
          (((∏ p ∈ n.primeFactors, p) * j : ℕ) : ℝ) := by
  let e : ℕ := ∏ p ∈ n.primeFactors, p
  have hepos : 0 < e := by
    dsimp [e]
    exact Finset.prod_pos fun p hp =>
      (Nat.mem_primeFactors.mp hp).1.pos
  have hterm (d : ℕ) (hd : d ∈ Icc 1 N) :
      ((μ d : ℤ) : ℝ) / (d : ℝ) *
          (if primeSupportedOn d n then 1 else 0) =
        if e ∣ d then ((μ d : ℤ) : ℝ) / (d : ℝ) else 0 := by
    have hd0 : d ≠ 0 := Nat.ne_of_gt
      (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1)
    have hsupp : primeSupportedOn d n ↔ e ∣ d := by
      simpa only [e] using primeSupportedOn_iff_prod_primeFactors_dvd hd0 hn.ne'
    rw [hsupp]
    split_ifs <;> ring
  rw [sum_congr rfl hterm, ← Finset.sum_filter]
  simpa [e, div_eq_mul_inv, mul_assoc] using
    (Sieve.sum_filter_dvd_moebius_scaled (e := e) (N := N) hepos
      (fun d => 1 / (d : ℝ)))

/-- The full reciprocal signed support column is the exact finite coprime-tail decomposition of
Euler deletion's `mixedColumn`, expressed without discarding signs. -/
theorem signed_support_reciprocal_column_full_reindex (N t : ℕ) :
    ∑ d ∈ Icc 1 N,
      ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (((Icc 1 t).filter (primeSupportedOn d)).card : ℝ) =
      ∑ n ∈ Icc 1 t,
        ∑ j ∈ (Icc 1 (N / (∏ p ∈ n.primeFactors, p))).filter
            (fun j => (∏ p ∈ n.primeFactors, p).Coprime j),
          ((μ (∏ p ∈ n.primeFactors, p) : ℤ) : ℝ) * ((μ j : ℤ) : ℝ) /
            (((∏ p ∈ n.primeFactors, p) * j : ℕ) : ℝ) := by
  rw [signed_support_reciprocal_column_exchange]
  apply sum_congr rfl
  intro n hn
  exact signed_reciprocal_support_coordinate_reindex N n
    (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1)

end RHTower.DeletionSignedSupportColumn
