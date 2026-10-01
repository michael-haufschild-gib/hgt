import GaloisForLFunctions.RHTower.SteinhausComplexSecondMoment
import Mathlib.Data.Nat.Factorization.Basic

open Complex Finset
open scoped ComplexConjugate
noncomputable section
namespace RHTower

private theorem one_add_primeWeight_le_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    1 + (∑ p ∈ P, ((p : ℝ) - 1)) ≤ ∏ p ∈ P, (p : ℝ) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hP p (mem_insert_self _ _)
    have hPs : ∀ q ∈ P, 1 ≤ q := fun q hq => hP q (mem_insert_of_mem hq)
    have hsum : 0 ≤ ∑ q ∈ P, ((q : ℝ) - 1) :=
      sum_nonneg (fun q hq => sub_nonneg.mpr (by exact_mod_cast hPs q hq))
    have hi := ih hPs
    have himul := mul_le_mul_of_nonneg_left hi (by linarith : (0 : ℝ) ≤ p)
    rw [sum_insert hp, prod_insert hp]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hsum]

/-- Distinct prime divisors have total additive charge at most the integer
frequency minus one. This retains all composite frequencies. -/
theorem primeDivisorWeight_le_frequency (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ P.filter (fun p => p ∣ n), ((p : ℝ) - 1)) ≤ (n : ℝ) - 1 := by
  classical
  have hsub : P.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hn
  have hsum : (∑ p ∈ P.filter (fun p => p ∣ n), ((p : ℝ) - 1)) ≤
      ∑ p ∈ n.primeFactors, ((p : ℝ) - 1) :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
      have h := (Nat.prime_of_mem_primeFactors hp).one_lt
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.le
      exact sub_nonneg.mpr hp1)
  have hprod := one_add_primeWeight_le_product n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hnat : (∏ p ∈ n.primeFactors, p) ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  have hr : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ n := by
    have hh : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    simpa only [Nat.cast_prod] using hh
  linarith

/-- Exact coefficient correlation that will represent the first prime moment
of an arbitrary finite Dirichlet square density. -/
def steinhausSpectralPrimeCorrelation (S : Finset ℕ) (a : ℕ → ℂ) (p : ℕ) : ℂ :=
  ∑ n ∈ S.filter (fun n => p * n ∈ S), a n * conj (a (p * n))

/-- The prime correlation is bounded by coefficient mass on multiples of that
prime; this uses no factorization of the density. -/
theorem norm_steinhausSpectralPrimeCorrelation_sq_le
    (S : Finset ℕ) (a : ℕ → ℂ) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1)
    {p : ℕ} (hp : 0 < p) :
    ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2 ≤
      ∑ m ∈ S.filter (fun m => p ∣ m), ‖a m‖ ^ 2 := by
  classical
  let T := S.filter (fun n => p * n ∈ S)
  have hfirst : (∑ n ∈ T, ‖a n‖ ^ 2) ≤ 1 := by
    rw [← hnorm]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hsecond : (∑ n ∈ T, ‖a (p * n)‖ ^ 2) ≤
      ∑ m ∈ S.filter (fun m => p ∣ m), ‖a m‖ ^ 2 := by
    have himage : T.image (fun n => p * n) ⊆ S.filter (fun m => p ∣ m) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      exact mem_filter.mpr ⟨(mem_filter.mp hn).2, dvd_mul_right p n⟩
    calc
      _ = ∑ m ∈ T.image (fun n => p * n), ‖a m‖ ^ 2 := by
        rw [sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hp hxy)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => sq_nonneg _)
  have htriangle : ‖steinhausSpectralPrimeCorrelation S a p‖ ≤
      ∑ n ∈ T, ‖a n‖ * ‖a (p * n)‖ := by
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, RCLike.norm_conj, T])
  have hcauchy := sum_mul_sq_le_sq_mul_sq T (fun n => ‖a n‖) (fun n => ‖a (p * n)‖)
  have hnonneg : 0 ≤ ∑ n ∈ T, ‖a (p * n)‖ ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (∑ n ∈ T, ‖a n‖ * ‖a (p * n)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle _
    _ ≤ (∑ n ∈ T, ‖a n‖ ^ 2) * ∑ n ∈ T, ‖a (p * n)‖ ^ 2 := hcauchy
    _ ≤ 1 * ∑ n ∈ T, ‖a (p * n)‖ ^ 2 := mul_le_mul_of_nonneg_right hfirst hnonneg
    _ ≤ _ := by simpa only [one_mul] using hsecond

/-- Every normalized finite coefficient family obeys the same prime-moment
frequency-cost law, including arbitrary correlated spectral factors. -/
theorem steinhausSpectralPrimeCorrelation_frequencyCost_lower
    (S P : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, n ≠ 0)
    (hP : ∀ p ∈ P, Nat.Prime p) (hnorm : ∑ n ∈ S, ‖a n‖ ^ 2 = 1) :
    1 + (∑ p ∈ P, ((p : ℝ) - 1) * ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2) ≤
      ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
  classical
  have hbound : (∑ p ∈ P, ((p : ℝ) - 1) * ‖steinhausSpectralPrimeCorrelation S a p‖ ^ 2) ≤
      ∑ n ∈ S, ((n : ℝ) - 1) * ‖a n‖ ^ 2 := by
    calc
      _ ≤ ∑ p ∈ P, ((p : ℝ) - 1) * ∑ n ∈ S.filter (fun n => p ∣ n), ‖a n‖ ^ 2 := by
        apply sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (norm_steinhausSpectralPrimeCorrelation_sq_le S a hnorm (hP p hp).pos)
          (by
            have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
            exact sub_nonneg.mpr hp1)
      _ = ∑ n ∈ S, (∑ p ∈ P.filter (fun p => p ∣ n), ((p : ℝ) - 1)) * ‖a n‖ ^ 2 := by
        simp_rw [sum_filter, mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        simp_rw [sum_mul, ite_mul, zero_mul]
      _ ≤ _ := sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right
        (primeDivisorWeight_le_frequency P hP (hS n hn)) (sq_nonneg _))
  have hsum : (∑ n ∈ S, ((n : ℝ) - 1) * ‖a n‖ ^ 2) =
      (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) - 1 := by
    simp_rw [sub_mul, one_mul, sum_sub_distrib]
    rw [hnorm]
  rw [hsum] at hbound
  linarith

end RHTower
