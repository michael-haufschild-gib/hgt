import Mathlib

open Polynomial Filter Complex
open scoped Classical Nat

namespace GaloisForLFunctions.RHTower

/-- **Scaled aggregate Hermite contradiction.** Let `E_i` be roots of an integer polynomial away
from the reference exponent `0`. Suppose an exponential relation has complex coefficients, its
zero-exponent fiber is a nonzero integer `a₀`, and every polynomially weighted coefficient sum
becomes an integer after multiplication by `ρ^t`, where
`t ≤ A * natDegree(q) + C`. Then Hermite's factorial approximation gives a contradiction.

The constants `A` and `C` isolate all denominator growth. The monic case is `ρ = 1`; non-monic
conjugate constructions supply fixed `ρ`, `A`, and `C`, so factorial decay still dominates. -/
theorem exp_scaled_aggregate_zero_relation_ne {ι : Type*} [Fintype ι]
    (E c : ι → ℂ) (g : ℤ[X]) (hg0 : g.eval 0 ≠ 0)
    (hroot : ∀ i : ι, E i ≠ 0 → E i ∈ g.aroots ℂ)
    (ρ a0 : ℤ) (hρ0 : ρ ≠ 0) (A C : ℕ)
    (hrel : ∑ i : ι, c i * Complex.exp (E i) = 0)
    (ha0 : ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i = 0), c i = (a0 : ℂ))
    (ha0ne : a0 ≠ 0)
    (hscaled : ∀ q : ℤ[X], ∃ t : ℕ, ∃ T : ℤ,
      t ≤ A * q.natDegree + C ∧
        (ρ : ℂ) ^ t * ∑ i : ι, c i * Polynomial.aeval (E i) q = (T : ℂ)) : False := by
  have hsplit : (a0 : ℂ) + ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
      c i * Complex.exp (E i) = 0 := by
    have he : (a0 : ℂ) = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i = 0),
        c i * Complex.exp (E i) := by
      rw [← ha0]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_filter] at hi
      rw [hi.2, Complex.exp_zero, mul_one]
    rw [he, Finset.sum_filter_add_sum_filter_not]
    exact hrel
  obtain ⟨B, hB⟩ := LindemannWeierstrass.exp_polynomial_approx g hg0
  have hsum_exp : ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
      c i * Complex.exp (E i) = -(a0 : ℂ) :=
    eq_neg_of_add_eq_zero_right hsplit
  set Cabs : ℝ := ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0), ‖c i‖
    with hCabs
  set ρabs : ℝ := |(ρ : ℝ)| with hρabs
  have hρabs_one : 1 ≤ ρabs := by
    rw [hρabs]
    have h := Int.one_le_abs hρ0
    exact_mod_cast h
  set B' : ℝ := ρabs ^ (A * g.natDegree) * B with hB'
  set N : ℝ := Cabs * ρabs ^ C with hN
  have hlim : Filter.Tendsto (fun p : ℕ => N * (B' ^ p / (p - 1)!)) Filter.atTop (nhds 0) := by
    have h1 := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (1 : ℝ) B' 1
    have h2 : Filter.Tendsto (fun p : ℕ => B' ^ p / (p - 1)!) Filter.atTop (nhds 0) := by
      simpa using h1
    simpa using h2.const_mul N
  have hev : ∀ᶠ p : ℕ in Filter.atTop, N * (B' ^ p / (p - 1)!) < 1 :=
    hlim.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨P₀, hP₀⟩ := hev
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes
    (max P₀ (max ((g.eval 0).natAbs + 1) (max (a0.natAbs + 1) (ρ.natAbs + 1))))
  have hp_ge_P₀ : P₀ ≤ p := le_trans (le_max_left _ _) hp_gt
  have hp_gt_g : (g.eval 0).natAbs < p := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp_gt
    omega
  have hp_gt_a0 : a0.natAbs < p := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) hp_gt)
    omega
  have hp_gt_ρ : ρ.natAbs < p := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) hp_gt)
    omega
  obtain ⟨n_p, hnp_ndvd, gp, hgp_deg, hgp_bound⟩ := hB p hp_gt_g hp_prime
  obtain ⟨t, T₀, ht, hT₀⟩ := hscaled gp
  have hev0 : Polynomial.aeval (0 : ℂ) gp = ((gp.eval 0 : ℤ) : ℂ) := by
    have h0 : (0 : ℂ) = (algebraMap ℤ ℂ) (0 : ℤ) := by simp
    rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    simp
  have hfull : ∑ i : ι, c i * Polynomial.aeval (E i) gp =
      (a0 : ℂ) * ((gp.eval 0 : ℤ) : ℂ) +
        ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
          c i * Polynomial.aeval (E i) gp := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset ι) (fun i => E i = 0)]
    congr 1
    rw [← ha0, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [hi.2, hev0]
  set T : ℤ := T₀ - a0 * gp.eval 0 * ρ ^ t with hT
  have hTcast : (T : ℂ) = (ρ : ℂ) ^ t *
      ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
        c i * Polynomial.aeval (E i) gp := by
    rw [hT]
    push_cast
    rw [← hT₀, hfull]
    ring
  have hbound : ∀ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
      ‖(n_p : ℂ) * Complex.exp (E i) - (p : ℂ) * Polynomial.aeval (E i) gp‖
        ≤ B ^ p / (p - 1)! := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hb := hgp_bound (hroot i hi.2)
    rw [zsmul_eq_mul, nsmul_eq_mul] at hb
    exact hb
  set J : ℤ := a0 * n_p * ρ ^ t + (p : ℤ) * T with hJ
  set δfun : ι → ℂ := fun i => c i *
      ((n_p : ℂ) * Complex.exp (E i) - (p : ℂ) * Polynomial.aeval (E i) gp) with hδ
  have hkey : (J : ℂ) = -((ρ : ℂ) ^ t *
      ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0), δfun i) := by
    have hexpand : ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0), δfun i =
        (n_p : ℂ) * (∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
          c i * Complex.exp (E i)) -
        (p : ℂ) * (∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
          c i * Polynomial.aeval (E i) gp) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hδ]
      ring
    rw [hexpand, hsum_exp, hJ]
    push_cast
    rw [hTcast]
    ring
  have ht' : t ≤ p * (A * g.natDegree) + C := by
    calc
      t ≤ A * gp.natDegree + C := ht
      _ ≤ A * (p * g.natDegree) + C := by
        gcongr
        omega
      _ = p * (A * g.natDegree) + C := by ring
  have hpow : ρabs ^ t ≤ ρabs ^ (p * (A * g.natDegree) + C) :=
    pow_le_pow_right₀ hρabs_one ht'
  have hsumle : ‖∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0), δfun i‖
      ≤ Cabs * (B ^ p / (p - 1)!) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc
      ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0), ‖δfun i‖
          ≤ ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0),
              ‖c i‖ * (B ^ p / (p - 1)!) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            rw [hδ, norm_mul]
            exact mul_le_mul_of_nonneg_left (hbound i hi) (norm_nonneg _)
      _ = Cabs * (B ^ p / (p - 1)!) := by rw [hCabs, ← Finset.sum_mul]
  have hscale : ρabs ^ (p * (A * g.natDegree) + C) *
      (Cabs * (B ^ p / (p - 1)!)) = N * (B' ^ p / (p - 1)!) := by
    rw [hN, hB']
    rw [pow_add, show p * (A * g.natDegree) = (A * g.natDegree) * p by ring,
      pow_mul, mul_pow]
    ring
  have hnorm : ‖(J : ℂ)‖ < 1 := by
    rw [hkey, norm_neg, norm_mul, norm_pow, Complex.norm_intCast, ← hρabs]
    calc
      ρabs ^ t * ‖∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ 0), δfun i‖
          ≤ ρabs ^ (p * (A * g.natDegree) + C) *
              (Cabs * (B ^ p / (p - 1)!)) :=
            mul_le_mul hpow hsumle (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
      _ = N * (B' ^ p / (p - 1)!) := hscale
      _ < 1 := hP₀ p hp_ge_P₀
  have hJ0 : J = 0 := by
    have habs : |(J : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hnorm
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  have hdvd : (p : ℤ) ∣ a0 * n_p * ρ ^ t := by
    have heq : a0 * n_p * ρ ^ t = -((p : ℤ) * T) := by
      have := hJ0
      rw [hJ] at this
      linarith
    rw [heq]
    exact (Dvd.intro T rfl).neg_right
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_prime_int.dvd_mul.mp hdvd with hleft | hρpow
  · rcases hp_prime_int.dvd_mul.mp hleft with ha | hn
    · have hdvdnat : p ∣ a0.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr ha
        rwa [Int.natAbs_natCast] at this
      exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0ne) hdvdnat) (not_le.mpr hp_gt_a0)
    · exact hnp_ndvd hn
  · have hρ : (p : ℤ) ∣ ρ := hp_prime_int.dvd_of_dvd_pow hρpow
    have hdvdnat : p ∣ ρ.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hρ
      rwa [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hρ0) hdvdnat) (not_le.mpr hp_gt_ρ)

end GaloisForLFunctions.RHTower
