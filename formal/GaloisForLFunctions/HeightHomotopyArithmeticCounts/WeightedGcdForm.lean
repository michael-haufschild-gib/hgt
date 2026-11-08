import GaloisForLFunctions.RHTower.DivisorBound
import GaloisForLFunctions.RHTower.FareySawtoothMeanSquare
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPeriodVarianceAndNonCommutingLimits

/-!
# Conductor-weighted bounds for the normalized gcd form

The totient divisor-square identity and Cauchy–Schwarz on multiples bound the
gcd form by a weighted square norm. The remaining divisor count has arbitrarily
small power growth, so every positive conductor exponent suffices. Zero extension
transfers the bound from conductor windows to arbitrary finite positive supports.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open TransHorizonIncidenceMechanics

private theorem gcd_multiples_square_le (η : ℝ) (hη : 0 < η)
    (N d : ℕ) (hd : 0 < d) (x : ℕ → ℝ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => d∣n), x n/Real.sqrt n)^2 ≤
      (∑ n ∈ (Icc 1 N).filter (fun n => d∣n), (x n)^2*(n:ℝ)^η)*
        ((d:ℝ)^(-1-η)*∑' k : ℕ, (k:ℝ)^(-1-η)) := by
  have hC := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    ((Icc 1 N).filter (fun n => d∣n))
    (r := fun n => x n/Real.sqrt n)
    (f := fun n => (x n)^2*(n:ℝ)^η)
    (g := fun n => (n:ℝ)^(-η)/n)
    (fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
    (fun n hn => by
      apply le_of_eq
      have hn0 : (0:ℝ)< n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
      have hp : (n:ℝ)^η*(n:ℝ)^(-η)=1 := by
        rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero]
      rw [div_pow, Real.sq_sqrt hn0.le]
      calc (x n)^2/(n:ℝ) = (x n)^2*((n:ℝ)^η*(n:ℝ)^(-η))/(n:ℝ) := by rw [hp, mul_one]
           _ = _ := by ring)
  exact hC.trans (mul_le_mul_of_nonneg_left (sum_multiples_rpow_le hη N d hd)
    (sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

private theorem totient_divisor_decay_le (η : ℝ) (hη : 0 < η) (n : ℕ) :
    (∑ d ∈ n.divisors, (Nat.totient d:ℝ)*(d:ℝ)^(-1-η)) ≤ n.divisors.card := by
  calc (∑ d ∈ n.divisors, (Nat.totient d:ℝ)*(d:ℝ)^(-1-η)) ≤
        ∑ _d ∈ n.divisors, (1:ℝ) := by
          apply sum_le_sum
          intro d hd
          have hd0 : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_mem_divisors hd
          have hd1 : (1:ℝ)≤d := by exact_mod_cast Nat.pos_of_mem_divisors hd
          have hφ : (Nat.totient d:ℝ)≤d := by exact_mod_cast Nat.totient_le d
          calc (Nat.totient d:ℝ)*(d:ℝ)^(-1-η) ≤ (d:ℝ)*(d:ℝ)^(-1-η) :=
                 mul_le_mul_of_nonneg_right hφ (Real.rpow_nonneg hd0.le _)
               _ = (d:ℝ)^(-η) := by
                 calc (d:ℝ)*(d:ℝ)^(-1-η) = (d:ℝ)^(1:ℝ)*(d:ℝ)^(-1-η) := by rw [Real.rpow_one]
                      _ = (d:ℝ)^(-η) := by rw [← Real.rpow_add hd0]; congr 1; ring
               _ ≤ 1 := by
                 simpa only [Real.rpow_zero] using
                   Real.rpow_le_rpow_of_exponent_le hd1 (neg_nonpos.mpr hη.le)
       _ = n.divisors.card := by simp only [sum_const, nsmul_eq_mul, mul_one]

private theorem interval_filter_divisors (N n : ℕ) (hn : n∈Icc 1 N) :
    (Icc 1 N).filter (fun d => d∣n) = n.divisors := by
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  ext d
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hd⟩
    exact ⟨hd, hn0.ne'⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn0,
      (Nat.le_of_dvd hn0 hd).trans (mem_Icc.mp hn).2⟩, hd⟩

/-- Every positive conductor exponent bounds the normalized gcd form on all finite windows. -/
theorem normalized_gcd_form_weighted_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (x : ℕ → ℝ),
      (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (Nat.gcd m n:ℝ)*(x m/Real.sqrt m*(x n/Real.sqrt n))) ≤
      C*∑ n ∈ Icc 1 N, (n:ℝ)^δ*(x n)^2 := by
  let η := δ/2
  have hη : 0 < η := half_pos hδ
  obtain ⟨D, hD, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow hη
  let Z := ∑' k : ℕ, (k:ℝ)^(-1-η)
  have hseries : Summable (fun k : ℕ => (k:ℝ)^(-1-η)) :=
    Real.summable_nat_rpow.mpr (by linarith only [hη])
  have hZ1 : 1 ≤ Z := by
    simpa only [sum_singleton, Nat.cast_one, Real.one_rpow] using
      hseries.sum_le_tsum {1} (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hZ : 0 < Z := zero_lt_one.trans_le hZ1
  refine ⟨Z*D, mul_pos hZ hD, ?_⟩
  intro N x
  have hgram : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (Nat.gcd m n:ℝ)*(x m/Real.sqrt m*(x n/Real.sqrt n))) =
      ∑ d ∈ Icc 1 N, (Nat.totient d:ℝ)*
        (∑ n ∈ (Icc 1 N).filter (fun n => d∣n), x n/Real.sqrt n)^2 := by
    simpa only [show Ioc 0 N=Icc 1 N from rfl] using
      RHTower.sum_sum_gcd_mul_eq N (fun n => x n/Real.sqrt n)
  rw [hgram]
  calc (∑ d ∈ Icc 1 N, (Nat.totient d:ℝ)*
        (∑ n ∈ (Icc 1 N).filter (fun n => d∣n), x n/Real.sqrt n)^2) ≤
        ∑ d ∈ Icc 1 N, (Nat.totient d:ℝ)*
          ((∑ n ∈ (Icc 1 N).filter (fun n => d∣n), (x n)^2*(n:ℝ)^η)*
            ((d:ℝ)^(-1-η)*Z)) := by
          apply sum_le_sum
          intro d hd
          exact mul_le_mul_of_nonneg_left
            (gcd_multiples_square_le η hη N d (mem_Icc.mp hd).1 x) (Nat.cast_nonneg _)
       _ = Z*∑ n ∈ Icc 1 N, ((x n)^2*(n:ℝ)^η)*
          ∑ d ∈ (Icc 1 N).filter (fun d => d∣n), (Nat.totient d:ℝ)*(d:ℝ)^(-1-η) := by
          simp only [sum_filter, mul_sum, sum_mul]
          rw [sum_comm]
          apply sum_congr rfl
          intro n _hn
          apply sum_congr rfl
          intro d _hd
          by_cases hd : d∣n <;> simp only [hd, if_true, if_false] <;> ring
       _ ≤ Z*∑ n ∈ Icc 1 N, ((x n)^2*(n:ℝ)^η)*(n.divisors.card:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hZ.le
          apply sum_le_sum
          intro n hn
          rw [interval_filter_divisors N n hn]
          exact mul_le_mul_of_nonneg_left (totient_divisor_decay_le η hη n)
            (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
       _ ≤ (Z*D)*∑ n ∈ Icc 1 N, (n:ℝ)^δ*(x n)^2 := by
          rw [mul_assoc Z D]
          apply mul_le_mul_of_nonneg_left _ hZ.le
          rw [mul_sum]
          apply sum_le_sum
          intro n hn
          have hn0 : (0:ℝ)< n := by exact_mod_cast (mem_Icc.mp hn).1
          calc ((x n)^2*(n:ℝ)^η)*(n.divisors.card:ℝ) ≤
                ((x n)^2*(n:ℝ)^η)*(D*(n:ℝ)^η) :=
                  mul_le_mul_of_nonneg_left (hdiv n (mem_Icc.mp hn).1)
                    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hn0.le _))
               _ = D*((n:ℝ)^δ*(x n)^2) := by
                  have hp : (n:ℝ)^η*(n:ℝ)^η=(n:ℝ)^δ := by
                    rw [← Real.rpow_add hn0]
                    congr 1
                    dsimp only [η]
                    ring
                  calc ((x n)^2*(n:ℝ)^η)*(D*(n:ℝ)^η) = D*((n:ℝ)^η*(n:ℝ)^η)*(x n)^2 := by ring
                       _ = _ := by rw [hp]; ring


/-- The same bound holds on every finite set of positive conductors. -/
theorem normalized_gcd_form_finite_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (x : ℕ → ℝ),
      (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S,
        (Nat.gcd m n:ℝ)*(x m/Real.sqrt m*(x n/Real.sqrt n))) ≤
      C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := normalized_gcd_form_weighted_bound δ hδ
  refine ⟨C, hC, ?_⟩
  intro S x hS
  let N := S.sup id
  let y : ℕ → ℝ := fun n => if n∈S then x n else 0
  have hsub : S ⊆ Icc 1 N := by
    intro n hn
    exact mem_Icc.mpr ⟨hS n hn, Finset.le_sup (f := id) hn⟩
  have henergy : (∑ n ∈ Icc 1 N, (n:ℝ)^δ*(y n)^2) =
      ∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
    calc _ = ∑ n ∈ S, (n:ℝ)^δ*(y n)^2 :=
           (sum_subset hsub fun n _ hn => by simp only [y, if_neg hn, zero_pow (by decide : 2≠0), mul_zero]).symm
         _ = _ := sum_congr rfl fun n hn => by rw [show y n=x n by simp only [y, if_pos hn]]
  have hrows (m : ℕ) :
      (∑ n ∈ Icc 1 N, (Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n))) =
      ∑ n ∈ S, (Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n)) :=
    (sum_subset hsub fun n _ hn => by simp only [y, if_neg hn, zero_div, mul_zero]).symm
  have hform : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n))) =
      ∑ m ∈ S, ∑ n ∈ S,
      (Nat.gcd m n:ℝ)*(x m/Real.sqrt m*(x n/Real.sqrt n)) := by
    simp_rw [hrows]
    calc _ = ∑ m ∈ S, ∑ n ∈ S,
            (Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n)) :=
           (sum_subset hsub fun m _ hm => by
             simp only [y, if_neg hm, zero_div, zero_mul, mul_zero, sum_const_zero]).symm
         _ = _ := by
           apply sum_congr rfl
           intro m hm
           apply sum_congr rfl
           intro n hn
           simp only [y, if_pos hm, if_pos hn]
  simpa only [henergy, hform] using hbound N y

#print axioms normalized_gcd_form_weighted_bound
#print axioms normalized_gcd_form_finite_bound

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
