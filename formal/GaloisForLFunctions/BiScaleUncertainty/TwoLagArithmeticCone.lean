import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Arithmetic facets for two additive lags

The simultaneous totient, Möbius and lag-two eigenvalues lie in a five-ray cone.
The odd positive-Möbius case supplies the extra bound needed beyond the
one-lag spectral interval. No sieve weight or cancellation hypothesis enters.
-/

noncomputable section
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
set_option autoImplicit false

/-- The second additive-lag eigenvalue in divisor coordinates. -/
def lagTwoEigenvalue (n : ℕ) : ℝ :=
  (μ n : ℝ) + 2 * if 2 ∣ n then (μ (n / 2) : ℝ) else 0

/-- The five closed facets of the simultaneous variance and two-lag cone. -/
def MomentCone (V x y : ℝ) : Prop :=
  0 ≤ 2*V + 3*x + y ∧ 0 ≤ V + x + y ∧ 0 ≤ V - x + y ∧
  0 ≤ V - 4*x - 2*y ∧ 0 ≤ V - x - 2*y

private theorem moebius_divisor_sum (n : ℕ) :
    ∑ e ∈ n.divisors, (μ e : ℝ) = if n=1 then 1 else 0 := by
  calc
    _ = ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n := by
      rw [ArithmeticFunction.coe_zeta_mul_apply]
      rfl
    _ = _ := by rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]; rfl

private theorem even_divisor_moebius_sum {m : ℕ} (hm : 0 < m) :
    ∑ e ∈ (2*m).divisors, (if 2 ∣ e then (μ (e/2) : ℝ) else 0) =
      if m=1 then 1 else 0 := by
  have hset : (2*m).divisors.filter (fun e => 2 ∣ e) =
      m.divisors.image (fun d => 2*d) := by
    ext e
    constructor
    · intro he
      obtain ⟨he, d, rfl⟩ := Finset.mem_filter.mp he
      have hd : d ∣ m := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2)
        (Nat.mem_divisors.mp he).1
      exact Finset.mem_image.mpr ⟨d, Nat.mem_divisors.mpr ⟨hd, by omega⟩, rfl⟩
    · intro he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨?_, by omega⟩, ⟨d, rfl⟩⟩
      obtain ⟨k, hk⟩ := (Nat.mem_divisors.mp hd).1
      exact ⟨k, by rw [hk]; ring⟩
  rw [← Finset.sum_filter, hset, Finset.sum_image]
  · simpa using moebius_divisor_sum m
  · intro a ha b hb hab
    dsimp at hab
    omega

/-- The lag-two eigenvalues invert the exact gcd compatibility kernel. -/
theorem lagTwoEigenvalue_divisor_sum {n : ℕ} (hn : 0 < n) :
    ∑ e ∈ n.divisors, lagTwoEigenvalue e = if n ∣ 2 then (n : ℝ) else 0 := by
  unfold lagTwoEigenvalue
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, moebius_divisor_sum]
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    have hm : 0 < m := by omega
    rw [even_divisor_moebius_sum hm]
    by_cases hm1 : m=1
    · subst m
      norm_num
    · have hn1 : 2*m ≠ 1 := by omega
      have hndvd : ¬ 2*m ∣ 2 := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < 2) hd
        omega
      simp [hm1, hn1, hndvd]
  · have hz : ∑ e ∈ n.divisors, (if 2 ∣ e then (μ (e/2) : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      apply if_neg
      intro hd
      exact h2 (hd.trans (Nat.mem_divisors.mp he).1)
    rw [hz]
    by_cases hn1 : n=1
    · subst n
      norm_num
    · have hn2 : n ≠ 2 := by rintro rfl; exact h2 (by decide)
      have hndvd : ¬ n ∣ 2 := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < 2) hd
        omega
      simp [hn1, hndvd]

/-- Two distinct odd prime factors force a totient of at least eight. -/
theorem odd_totient_ge_eight_of_moebius_one {n : ℕ}
    (hn : 2 ≤ n) (hodd : ¬ 2 ∣ n) (hmu : μ n = 1) :
    8 ≤ Nat.totient n := by
  have hpp : ¬ IsPrimePow n := by
    intro h
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp h
    have hm := ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0)
    rw [hmu] at hm
    (split_ifs at hm; norm_num at hm)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hpp
  have hprimep := Nat.prime_of_mem_primeFactors hp
  have hprimeq := Nat.prime_of_mem_primeFactors hq
  have hdp := Nat.dvd_of_mem_primeFactors hp
  have hdq := Nat.dvd_of_mem_primeFactors hq
  have hp2 : p ≠ 2 := by rintro rfl; exact hodd hdp
  have hq2 : q ≠ 2 := by rintro rfl; exact hodd hdq
  have hsmall (r : ℕ) (hr : Nat.Prime r) (hr2 : r ≠ 2) : r = 3 ∨ 5 ≤ r := by
    have hrlo := hr.two_le
    have hrmod := hr.eq_two_or_odd.resolve_left hr2
    omega
  have hp3 : 3 ≤ p := by have := hprimep.two_le; omega
  have hq3 : 3 ≤ q := by have := hprimeq.two_le; omega
  have hcop := (Nat.coprime_primes hprimep hprimeq).mpr hpq
  have hdprod := hprimep.dvd_mul_of_dvd_ne hpq hprimeq hdp hdq
  have hphi : 8 ≤ Nat.totient (p*q) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hprimep, Nat.totient_prime hprimeq]
    rcases hsmall p hprimep hp2 with hpval | hp5
    · have hq5 : 5 ≤ q := by
        rcases hsmall q hprimeq hq2 with hqval | hq5
        · exact (hpq (hpval.trans hqval.symm)).elim
        · exact hq5
      exact (by norm_num : 8 = 2*4) ▸ Nat.mul_le_mul (by omega) (by omega)
    · exact (by norm_num : 8 = 4*2) ▸ Nat.mul_le_mul (by omega) (by omega)
  exact hphi.trans (Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
    (Nat.totient_dvd_of_dvd hdprod))

private theorem odd_large_bounds {n : ℕ} (hn : 2 ≤ n) (hodd : ¬ 2 ∣ n) :
    6*(μ n : ℝ) ≤ Nat.totient n ∧ 0 ≤ (Nat.totient n : ℝ) + 2*(μ n : ℝ) := by
  have hn3 : 2 < n := by
    have : n ≠ 2 := by rintro rfl; exact hodd (by norm_num)
    omega
  have hp2 : 2 ≤ Nat.totient n := by
    obtain ⟨k, hk⟩ := Nat.totient_even hn3
    have hp := Nat.totient_pos.mpr (show 0 < n by omega)
    omega
  have hp2r : (2 : ℝ) ≤ Nat.totient n := by exact_mod_cast hp2
  rcases ArithmeticFunction.moebius_eq_or n with hm | hm | hm
  · norm_num [hm]
  · have hp8 := odd_totient_ge_eight_of_moebius_one hn hodd hm
    have hp8r : (8 : ℝ) ≤ Nat.totient n := by exact_mod_cast hp8
    constructor <;> norm_num [hm] <;> linarith
  · constructor <;> norm_num [hm] <;> linarith

private theorem odd_bounds {n : ℕ} (hn : 1 ≤ n) (hodd : ¬ 2 ∣ n) :
    (μ n : ℝ) ≤ Nat.totient n ∧ 0 ≤ (Nat.totient n : ℝ) + 2*(μ n : ℝ) := by
  by_cases h1 : n = 1
  · subst n
    norm_num
  · obtain ⟨h, h'⟩ := odd_large_bounds (show 2 ≤ n by omega) hodd
    have hp : (0 : ℝ) ≤ Nat.totient n := Nat.cast_nonneg _
    constructor <;> linarith

private theorem moebius_two_mul (r : ℕ) (hr : ¬ 2 ∣ r) :
    (μ (2*r) : ℝ) = -(μ r : ℝ) := by
  have hcop : Nat.Coprime 2 r := Nat.prime_two.coprime_iff_not_dvd.mpr hr
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

private theorem moebius_four_mul (r : ℕ) : μ (4*r) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two ⟨r, by ring⟩

private theorem totient_four_mul (r : ℕ) (hr : ¬ 2 ∣ r) :
    Nat.totient (4*r) = 2 * Nat.totient r := by
  have hcop : Nat.Coprime 2 r := Nat.prime_two.coprime_iff_not_dvd.mpr hr
  have hfour : 4*r = 2*(2*r) := by ring
  rw [hfour, Nat.totient_mul_of_prime_of_dvd Nat.prime_two (show 2 ∣ 2*r from ⟨r, rfl⟩),
    Nat.totient_mul hcop, Nat.totient_prime Nat.prime_two]
  simp

private theorem even_two_values (r : ℕ) (hr : ¬ 2 ∣ r) :
    (Nat.totient (2*r) : ℝ) = Nat.totient r ∧
    (μ (2*r) : ℝ) = -(μ r : ℝ) ∧ lagTwoEigenvalue (2*r) = (μ r : ℝ) := by
  have hcop : Nat.Coprime 2 r := Nat.prime_two.coprime_iff_not_dvd.mpr hr
  have hm := moebius_two_mul r hr
  refine ⟨?_, hm, ?_⟩
  · simp [Nat.totient_mul hcop, Nat.totient_prime Nat.prime_two]
  · simp [lagTwoEigenvalue, hm]
    ring

private theorem even_four_values (r : ℕ) (hr : ¬ 2 ∣ r) :
    (Nat.totient (4*r) : ℝ) = 2*Nat.totient r ∧
    (μ (4*r) : ℝ) = 0 ∧ lagTwoEigenvalue (4*r) = -2*(μ r : ℝ) := by
  refine ⟨by simp [totient_four_mul r hr], by simp [moebius_four_mul], ?_⟩
  have hdiv : 4*r/2 = 2*r := by omega
  have hd : 2 ∣ 4*r := ⟨2*r, by ring⟩
  simp [lagTwoEigenvalue, moebius_four_mul, hd, hdiv, moebius_two_mul r hr]

private theorem even_eight_values (r : ℕ) :
    (μ (8*r) : ℝ) = 0 ∧ lagTwoEigenvalue (8*r) = 0 := by
  have h8 : 8*r = 4*(2*r) := by ring
  have hdiv : 8*r/2 = 4*r := by omega
  have hd : 2 ∣ 8*r := ⟨4*r, by ring⟩
  constructor
  · simp [h8, moebius_four_mul]
  · simp only [lagTwoEigenvalue, if_pos hd, hdiv]
    simp [h8, moebius_four_mul]

/-- Every nonconstant arithmetic mode satisfies all five simultaneous lag facets. -/
theorem arithmetic_momentCone {n : ℕ} (hn : 2 ≤ n) :
    MomentCone (Nat.totient n) (μ n : ℝ) (lagTwoEigenvalue n) := by
  have hp : (0 : ℝ) ≤ Nat.totient n := Nat.cast_nonneg _
  by_cases h2 : 2 ∣ n
  · obtain ⟨r, rfl⟩ := h2
    by_cases hr : 2 ∣ r
    · obtain ⟨s, rfl⟩ := hr
      have h4 : 2*(2*s) = 4*s := by ring
      rw [h4] at hn hp ⊢
      by_cases hs : 2 ∣ s
      · obtain ⟨t, rfl⟩ := hs
        have h8 : 4*(2*t) = 8*t := by ring
        rw [h8] at hp ⊢
        obtain ⟨hm, hk⟩ := even_eight_values t
        simp only [MomentCone, hm, hk]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      · obtain ⟨hb, hc⟩ := odd_bounds (show 1 ≤ s by omega) hs
        obtain ⟨hf, hm, hk⟩ := even_four_values s hs
        simp only [MomentCone, hf, hm, hk]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    · obtain ⟨hb, hc⟩ := odd_bounds (show 1 ≤ r by omega) hr
      obtain ⟨hf, hm, hk⟩ := even_two_values r hr
      simp only [MomentCone, hf, hm, hk]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · obtain ⟨hb, hc⟩ := odd_large_bounds hn h2
    simp only [lagTwoEigenvalue, if_neg h2, mul_zero, add_zero, MomentCone]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Exact nonnegative variance masses on modes `2, 3, 4, 6, 12`.
The three explicit branches triangulate the cone without a division by variance. -/
theorem momentCone_iff_exists_nonnegative_five_masses (V x y : ℝ) :
    MomentCone V x y ↔ ∃ A B C D E : ℝ,
      0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ E ∧
      V = A+B+C+D+E ∧ x = -A-B/2+D/2 ∧ y = A-B/2-C-D/2+E/2 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    by_cases hxy : 0 ≤ x+y
    · refine ⟨(V-4*x-2*y)/3, 0, 0, 2*(V-x-2*y)/3, 2*(x+y),
        by linarith, le_rfl, le_rfl, by linarith, by linarith, ?_, ?_, ?_⟩ <;> ring
    · by_cases hmid : 0 ≤ V+2*x+y
      · refine ⟨(V-x+y)/3, 0, -x-y, 2*(V+2*x+y)/3, 0,
          by linarith, le_rfl, by linarith, by linarith, le_rfl, ?_, ?_, ?_⟩ <;> ring
      · refine ⟨V+x+y, -2*(V+2*x+y), 2*V+3*x+y, 0, 0,
          h2, by linarith, h1, le_rfl, le_rfl, ?_, ?_, ?_⟩ <;> ring
  · rintro ⟨A, B, C, D, E, hA, hB, hC, hD, hE, hV, hx, hy⟩
    unfold MomentCone
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Complete dual classification: five generating rays test every linear inequality. -/
theorem universal_momentCone_linear_inequality_iff (α β γ : ℝ) :
    (∀ V x y : ℝ, MomentCone V x y → 0 ≤ α*V+β*x+γ*y) ↔
      0 ≤ α-β+γ ∧ 0 ≤ 2*α-β-γ ∧ 0 ≤ α-γ ∧
      0 ≤ 2*α+β-γ ∧ 0 ≤ 2*α+γ := by
  constructor
  · intro h
    have h2 := h 1 (-1) 1 (by norm_num [MomentCone])
    have h3 := h 2 (-1) (-1) (by norm_num [MomentCone])
    have h4 := h 2 0 (-2) (by norm_num [MomentCone])
    have h6 := h 2 1 (-1) (by norm_num [MomentCone])
    have h12 := h 4 0 2 (by norm_num [MomentCone])
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h2, h3, h4, h6, h12⟩ V x y hcone
    obtain ⟨A, B, C, D, E, hA, hB, hC, hD, hE, hV, hx, hy⟩ :=
      (momentCone_iff_exists_nonnegative_five_masses V x y).mp hcone
    rw [hV, hx, hy]
    nlinarith only [mul_nonneg hA h2, mul_nonneg hB h3, mul_nonneg hC h4,
      mul_nonneg hD h6, mul_nonneg hE h12]

end GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
