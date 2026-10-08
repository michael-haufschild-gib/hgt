import GaloisForLFunctions.RHTower.Sieve.LocalizedReciprocalMoebiusAmplitude
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticHarmonicConvolution
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite-prime deletion at the ordinary harmonic endpoint

A multiplicative arithmetic function splits exactly into its prime-supported
and coprime restrictions. A strict bound on each nonconstant prime-power
coefficient gives an absolutely harmonic-summable inverse of each local factor.
Consequently deleting finitely many primes divides an ordinary harmonic limit
by the product of their local Euler factors, without rearranging the conditional
series. This supplies the finite-prime step of WP03 C49.
-/

open ArithmeticFunction
open RHTower.Sieve
open Filter Topology

noncomputable section
namespace RHTower.WeilSingularArithmetic

variable {R : Type*} [CommSemiring R]

def smoothRestriction (r : ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R := by
  classical
  exact ⟨fun n => if primeSupportedOn r n then f n else 0, by simp⟩

def roughRestriction (r : ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R := by
  classical
  exact ⟨fun n => if Nat.Coprime r n then f n else 0, by simp⟩

@[simp] theorem smoothRestriction_one (r : ℕ) (f : ArithmeticFunction R) :
    smoothRestriction r f 1 = f 1 := by
  classical
  simp [smoothRestriction]

@[simp] theorem roughRestriction_one (r : ℕ) (f : ArithmeticFunction R) :
    roughRestriction r f 1 = f 1 := by
  classical
  simp [roughRestriction]

theorem smoothRestriction_multiplicative {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (r : ℕ) : (smoothRestriction r f).IsMultiplicative := by
  classical
  constructor
  · simpa using hf.map_one
  · intro m n hmn
    have hmul := hf.map_mul_of_coprime hmn
    by_cases hm : primeSupportedOn r m <;> by_cases hn : primeSupportedOn r n <;>
      simp [smoothRestriction, primeSupportedOn_mul_iff, hm, hn, hmul]

theorem roughRestriction_multiplicative {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (r : ℕ) : (roughRestriction r f).IsMultiplicative := by
  classical
  constructor
  · simpa using hf.map_one
  · intro m n hmn
    have hmul := hf.map_mul_of_coprime hmn
    change (if Nat.Coprime r (m * n) then f (m * n) else 0) =
      (if Nat.Coprime r m then f m else 0) * (if Nat.Coprime r n then f n else 0)
    by_cases hm : Nat.Coprime r m
    · by_cases hn : Nat.Coprime r n
      · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn, hmul]
      · rw [if_neg (fun h => hn (Nat.coprime_mul_iff_right.mp h).2), if_pos hm,
          if_neg hn, mul_zero]
    · rw [if_neg (fun h => hm (Nat.coprime_mul_iff_right.mp h).1), if_neg hm, zero_mul]

theorem smoothRestriction_prime_pow (f : ArithmeticFunction R)
    {r p k : ℕ} (hp : p.Prime) :
    smoothRestriction r f (p ^ k) = if k = 0 ∨ p ∣ r then f (p ^ k) else 0 := by
  classical
  by_cases hk : k = 0
  · subst k; simp
  · have hs := primeSupportedOn_prime_pow_iff (r := r) hp (Nat.pos_of_ne_zero hk)
    simp [smoothRestriction, hs, hk]

theorem roughRestriction_prime_pow (f : ArithmeticFunction R)
    {r p k : ℕ} (hp : p.Prime) :
    roughRestriction r f (p ^ k) = if k = 0 ∨ ¬ p ∣ r then f (p ^ k) else 0 := by
  classical
  by_cases hk : k = 0
  · subst k; simp
  · have hc : Nat.Coprime r (p ^ k) ↔ ¬ p ∣ r := by
      rw [Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hk), Nat.coprime_comm,
        hp.coprime_iff_not_dvd]
    simp [roughRestriction, hc, hk]

private theorem convolution_prime_power (f g : ArithmeticFunction R)
    (p k : ℕ) (hp : p.Prime) :
    (f * g) (p ^ k) = ∑ j ∈ Finset.range (k + 1), f (p ^ j) * g (p ^ (k - j)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : p ^ k = p ^ (k - j) * p ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
  rw [he, Nat.mul_div_cancel _ (pow_pos hp.pos j)]

/-- Multiplicativity splits an arithmetic function into its smooth and rough
prime factors by exact Dirichlet convolution. -/
theorem smoothRestriction_mul_roughRestriction {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (r : ℕ) : smoothRestriction r f * roughRestriction r f = f := by
  classical
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((smoothRestriction_multiplicative hf r).mul (roughRestriction_multiplicative hf r)) f hf).2
  intro p k hp
  rw [convolution_prime_power _ _ p k hp]
  simp_rw [smoothRestriction_prime_pow _ hp, roughRestriction_prime_pow _ hp]
  by_cases hpr : p ∣ r
  · simp only [hpr, or_true, ↓reduceIte, not_true_eq_false, or_false]
    rw [Finset.sum_eq_single k]
    · simp [hf.map_one]
    · intro j hj hjk
      have hkj : k - j ≠ 0 := by have := Finset.mem_range.mp hj; omega
      simp [hkj]
    · simp
  · simp only [hpr, not_false_eq_true, or_true, or_false, ↓reduceIte]
    rw [Finset.sum_eq_single 0]
    · simp [hf.map_one]
    · intro j hj hj0
      simp [hj0]
    · simp

theorem smoothRestriction_prime_eq_zero_of_not_pow (f : ArithmeticFunction R)
    {p n : ℕ} (hp : p.Prime) (hn : n ∉ Set.range (fun k : ℕ => p ^ k)) :
    smoothRestriction p f n = 0 := by
  classical
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hs : ¬ primeSupportedOn p n := by
      intro hs
      apply hn
      refine ⟨n.primeFactorsList.length, (Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_).symm⟩
      intro q hq hqn
      rcases (Nat.dvd_prime hp).mp (hs q hq hqn) with hq1 | hqp
      · exact (hq.ne_one hq1).elim
      · exact hqp
    simp [smoothRestriction, hs]

private theorem localHarmonicTail_summable_bound {f : ArithmeticFunction ℂ}
    {p : ℕ} (hp : p.Prime) {θ : ℝ}
    (hb : ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ) :
    Summable (fun k : ℕ => ‖f (p ^ (k + 1)) / ((p ^ (k + 1) : ℕ) : ℂ)‖) ∧
      (∑' k : ℕ, ‖f (p ^ (k + 1)) / ((p ^ (k + 1) : ℕ) : ℂ)‖) ≤ θ / (p - 1 : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by positivity
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp1
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (θ / p)
  have hle (k : ℕ) : ‖f (p ^ (k + 1)) / ((p ^ (k + 1) : ℕ) : ℂ)‖ ≤
      (θ / p) * ((p : ℝ)⁻¹) ^ k := by
    rw [norm_div, Complex.norm_natCast]
    calc
      _ ≤ θ / ((p ^ (k + 1) : ℕ) : ℝ) := div_le_div_of_nonneg_right (hb _ (by omega)) (by positivity)
      _ = _ := by push_cast; rw [pow_succ, inv_pow]; ring
  have hs := hg.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  refine ⟨hs, (hs.tsum_le_tsum hle hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  field_simp

theorem exists_primeHarmonic_inverse {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) {θ : ℝ}
    (hθ1 : θ < 1)
    (hb : ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ) :
    ∃ g : ArithmeticFunction ℂ, smoothRestriction p f * g = 1 ∧
      Summable (fun n => ‖g n / (n : ℂ)‖) := by
  classical
  let a := smoothRestriction p f
  let t : ℕ → ℝ := fun n => ‖(a - 1) n / (n : ℂ)‖
  have hi : Function.Injective (fun k : ℕ => p ^ k) := (pow_right_strictMono₀ hp.one_lt).injective
  have ht0 (n : ℕ) (hn : n ∉ Set.range (fun k : ℕ => p ^ k)) : t n = 0 := by
    have hn1 : n ≠ 1 := by intro h; apply hn; exact ⟨0, by simpa using h.symm⟩
    change ‖(smoothRestriction p f n - (1 : ArithmeticFunction ℂ) n) / (n : ℂ)‖ = 0
    simp [smoothRestriction_prime_eq_zero_of_not_pow _ hp hn, hn1]
  have htp (k : ℕ) : t (p ^ (k + 1)) =
      ‖f (p ^ (k + 1)) / ((p ^ (k + 1) : ℕ) : ℂ)‖ := by
    have hne : p ^ (k + 1) ≠ 1 := by
      have h := (pow_right_strictMono₀ hp.one_lt) (show 0 < k + 1 by omega)
      simpa using ne_of_gt h
    change ‖(smoothRestriction p f (p ^ (k + 1)) - (1 : ArithmeticFunction ℂ) (p ^ (k + 1))) /
      ((p ^ (k + 1) : ℕ) : ℂ)‖ = _
    rw [ArithmeticFunction.one_apply_ne hne]
    simp [smoothRestriction_prime_pow _ hp]
  obtain ⟨hs, hbound⟩ := localHarmonicTail_summable_bound hp hb
  have hstail : Summable (fun k : ℕ => t (p ^ (k + 1))) := hs.congr fun k => (htp k).symm
  have hspow : Summable (fun k : ℕ => t (p ^ k)) := (summable_nat_add_iff 1).mp hstail
  have hst : Summable t := (hi.summable_iff ht0).mp hspow
  have hq : (∑' n, t n) ≤ θ / (p - 1 : ℝ) := by
    rw [← hi.tsum_eq (fun n hn => by
      by_contra h; exact hn (ht0 n h))]
    rw [hspow.tsum_eq_zero_add]
    have hzero : t (p ^ 0) = 0 := by
      change ‖(smoothRestriction p f (p ^ 0) - (1 : ArithmeticFunction ℂ) (p ^ 0)) /
        ((p ^ 0 : ℕ) : ℂ)‖ = 0
      simp [hf.map_one]
    simpa only [hzero, htp, zero_add] using hbound
  apply exists_harmonicSummable_inverse a (by simp [a, hf.map_one]) hst
  apply lt_of_le_of_lt hq
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  apply (div_lt_iff₀ hp1).2
  linarith

theorem smoothRestriction_prime_harmonic_summable {f : ArithmeticFunction ℂ}
    {p : ℕ} (hp : p.Prime) {θ : ℝ}
    (hb : ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ) :
    Summable (fun n : ℕ => ‖smoothRestriction p f n / (n : ℂ)‖) := by
  have hs := (localHarmonicTail_summable_bound hp hb).1
  have hsp : Summable (fun k : ℕ => ‖f (p ^ k) / ((p ^ k : ℕ) : ℂ)‖) :=
    (summable_nat_add_iff 1).mp hs
  have hi := (pow_right_strictMono₀ hp.one_lt).injective
  apply (hi.summable_iff (fun n hn => ?_)).mp
  · simpa [Function.comp_def, smoothRestriction_prime_pow _ hp] using hsp
  · simp [smoothRestriction_prime_eq_zero_of_not_pow _ hp hn]

theorem smoothRestriction_prime_harmonic_tsum (f : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) :
    (∑' n : ℕ, smoothRestriction p f n / (n : ℂ)) =
      ∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ) := by
  have hi := (pow_right_strictMono₀ hp.one_lt).injective
  have ht := hi.tsum_eq (f := fun n : ℕ => smoothRestriction p f n / (n : ℂ)) (by
    intro n hn
    by_contra h
    apply hn
    simp [smoothRestriction_prime_eq_zero_of_not_pow _ hp h])
  simpa [smoothRestriction_prime_pow _ hp] using ht.symm

/-- Deleting a prime preserves an ordinary harmonic limit and divides it by
the absolutely convergent local Euler factor. -/
theorem tendsto_roughRestriction_prime {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) {θ : ℝ}
    (hθ1 : θ < 1) (hb : ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ)
    {H : ℂ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ)) atTop (𝓝 H)) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, roughRestriction p f n / (n : ℂ))
      atTop (𝓝 (H / (∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ)))) := by
  obtain ⟨g, hag, hg⟩ := exists_primeHarmonic_inverse hf hp hθ1 hb
  have hscalar := harmonic_inverse_product hag (smoothRestriction_prime_harmonic_summable hp hb) hg
  rw [smoothRestriction_prime_harmonic_tsum f hp] at hscalar
  have hne : (∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hscalar
    exact zero_ne_one hscalar
  have he : g * f = roughRestriction p f := by
    calc
      _ = g * (smoothRestriction p f * roughRestriction p f) := by
        rw [smoothRestriction_mul_roughRestriction hf]
      _ = (smoothRestriction p f * g) * roughRestriction p f := by ring
      _ = _ := by rw [hag, one_mul]
  have h := tendsto_harmonic_mul_of_summable hg hH
  rw [he] at h
  convert h using 1
  congr 1
  apply (div_eq_iff hne).2
  symm
  calc
    _ = H * ((∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ)) *
        (∑' n : ℕ, g n / (n : ℂ))) := by ring
    _ = H := by rw [hscalar, mul_one]

@[simp] theorem roughRestriction_one_modulus (f : ArithmeticFunction R) :
    roughRestriction 1 f = f := by
  classical
  ext n
  simp [roughRestriction]

theorem roughRestriction_mul_modulus (f : ArithmeticFunction R) (r s : ℕ) :
    roughRestriction (r * s) f = roughRestriction r (roughRestriction s f) := by
  classical
  ext n
  change (if Nat.Coprime (r * s) n then f n else 0) =
    (if Nat.Coprime r n then (if Nat.Coprime s n then f n else 0) else 0)
  simp only [Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

/-- Finite-prime deletion at the ordinary harmonic endpoint, with its exact
Euler-factor denominator. -/
theorem tendsto_roughRestriction_finset {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ1 : θ < 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hb : ∀ p ∈ P, ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ)
    {H : ℂ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ)) atTop (𝓝 H)) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, roughRestriction (∏ p ∈ P, p) f n / (n : ℂ))
      atTop (𝓝 (H / (∏ p ∈ P, ∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ)))) := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using hH
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hb' := fun q hq => hb q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime (∏ q ∈ P, q) p := by
      apply Nat.Coprime.prod_left
      intro q hq
      exact (Nat.coprime_primes (hP' q hq) hp).2 (fun he => hpP (he ▸ hq))
    have heval (k : ℕ) : roughRestriction (∏ q ∈ P, q) f (p ^ k) = f (p ^ k) := by
      change (if Nat.Coprime (∏ q ∈ P, q) (p ^ k) then f (p ^ k) else 0) = _
      exact if_pos (hcop.pow_right k)
    have hl := tendsto_roughRestriction_prime (roughRestriction_multiplicative hf _) hp hθ1
      (fun k hk => by rw [heval]; exact hb p (Finset.mem_insert_self p P) k hk)
      (ih hP' hb')
    simpa only [Finset.prod_insert hpP, roughRestriction_mul_modulus, heval, div_div,
      mul_comm (∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ))] using hl

end RHTower.WeilSingularArithmetic
