import GaloisForLFunctions.RHTower.Sieve.LcmQuadraticDiagonalization

/-!
# Reindexing the diagonalised sums

The Selberg diagonalisation leaves the one-dimensional sums `∑_{m ≤ X, e ∣ m} a(m)/m`.  Writing
`m = e m'` turns them into sums over `m' ≤ X/e`, and for the Möbius weight the substituted value
`μ(e m')` vanishes unless `e` and `m'` are coprime, in which case it factors.  These are the two
elementary steps that finish Graham's evaluation.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **Reindexing the multiples of `e`.** -/
theorem sum_filter_dvd_eq_sum_scaled {e N : ℕ} (he : 0 < e) (f : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), f m
      = ∑ j ∈ Finset.Icc 1 (N / e), f (e * j) := by
  classical
  rw [multiples_Icc he N]
  refine Finset.sum_image ?_
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left he hxy

/-- **The Möbius weight vanishes off the coprime locus.** -/
theorem moebius_mul_eq_zero_of_not_coprime {a b : ℕ} (h : ¬ Nat.Coprime a b) :
    (μ (a * b) : ℤ) = 0 := by
  have hne : Nat.gcd a b ≠ 1 := h
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpa : p ∣ a := dvd_trans hpd (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := dvd_trans hpd (Nat.gcd_dvd_right a b)
  have hsq : p * p ∣ a * b := mul_dvd_mul hpa hpb
  refine moebius_eq_zero_of_not_squarefree ?_
  intro hsf
  have hu : IsUnit p := hsf p hsq
  rw [Nat.isUnit_iff] at hu
  exact hp.ne_one hu

/-- **The Möbius weight factors on the coprime locus.** -/
theorem moebius_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    (μ (a * b) : ℤ) = (μ a : ℤ) * (μ b : ℤ) :=
  isMultiplicative_moebius.map_mul_of_coprime h

/-- **The diagonalised Möbius sum, reindexed.**  Every term with `e` and `m'` sharing a factor
drops out, and the surviving terms carry the factor `μ(e)`. -/
theorem sum_filter_dvd_moebius_scaled {e N : ℕ} (he : 0 < e) (g : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), (μ m : ℝ) * g m
      = ∑ j ∈ (Finset.Icc 1 (N / e)).filter (fun j => Nat.Coprime e j),
          (μ e : ℝ) * (μ j : ℝ) * g (e * j) := by
  classical
  rw [sum_filter_dvd_eq_sum_scaled he (fun m => (μ m : ℝ) * g m)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (N / e))
    (fun j => Nat.Coprime e j) (fun j => (μ (e * j) : ℝ) * g (e * j))]
  have hzero : ∑ j ∈ (Finset.Icc 1 (N / e)).filter (fun j => ¬ Nat.Coprime e j),
      (μ (e * j) : ℝ) * g (e * j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨-, hnc⟩ := Finset.mem_filter.mp hj
    have h0 : (μ (e * j) : ℤ) = 0 := moebius_mul_eq_zero_of_not_coprime hnc
    have h0R : ((μ (e * j) : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    rw [h0R, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨-, hc⟩ := Finset.mem_filter.mp hj
  have hfac : ((μ (e * j) : ℤ) : ℝ) = ((μ e : ℤ) : ℝ) * ((μ j : ℤ) : ℝ) := by
    have h := moebius_mul_of_coprime hc
    exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) h
  rw [hfac]

end RHTower.Sieve
