import GaloisForLFunctions.RHTower.Sieve.JointTuranKubilius
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# The mean square of a truncated divisor moment

Rankin's trick turns the truncation tail of the Legendre expansion into the `α`-th divisor moment
of the sifted part of `n`.  Its mean square over an initial segment is a pair sum over the divisors
of the sifting modulus:

```text
   ∑_{n ≤ Y} (∑_{e ∣ gcd(n,P)} e^α)²  ≤  Y · ∑_{e₁,e₂ ∣ P} (e₁e₂)^α / lcm(e₁,e₂) .
```

This is the shape the `c₁,n` bound of Matomäki–Teräväinen, Lemma 2.3, reduces to.
-/

namespace RHTower.Sieve

open Finset

theorem divisors_gcd_eq {n P : ℕ} (hn : 0 < n) (hP : 0 < P) :
    (Nat.gcd n P).divisors = P.divisors.filter (fun e => e ∣ n) := by
  ext e
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨⟨h2, by omega⟩, h1⟩
  · rintro ⟨⟨h2, -⟩, h1⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    have : 0 < Nat.gcd n P := Nat.gcd_pos_of_pos_left _ hn
    omega

/-- **The mean square of the divisor moment.** -/
theorem sum_sq_divisor_moment_le {P Y : ℕ} (hP : 0 < P) (α : ℝ) :
    ∑ n ∈ Finset.Icc 1 Y, (∑ e ∈ (Nat.gcd n P).divisors, (e : ℝ) ^ α) ^ 2
      ≤ (Y : ℝ) * ∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
          ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α) / ((Nat.lcm e₁ e₂ : ℕ) : ℝ) := by
  classical
  -- rewrite each inner sum as an indicator sum over the divisors of `P`
  have hrw : ∀ n ∈ Finset.Icc 1 Y,
      (∑ e ∈ (Nat.gcd n P).divisors, (e : ℝ) ^ α) ^ 2
        = ∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
            ((if e₁ ∣ n then (1 : ℝ) else 0) * (if e₂ ∣ n then (1 : ℝ) else 0))
              * ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : 0 < n := hn.1
    rw [divisors_gcd_eq hn0 hP, Finset.sum_filter, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ => ?_
    by_cases h1 : e₁ ∣ n <;> by_cases h2 : e₂ ∣ n <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl hrw]
  -- swap the sums
  have hswap : ∑ n ∈ Finset.Icc 1 Y, ∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
        ((if e₁ ∣ n then (1 : ℝ) else 0) * (if e₂ ∣ n then (1 : ℝ) else 0))
          * ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α)
      = ∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors, ∑ n ∈ Finset.Icc 1 Y,
          ((if e₁ ∣ n then (1 : ℝ) else 0) * (if e₂ ∣ n then (1 : ℝ) else 0))
            * ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  -- bound each pair
  have hterm : ∀ e₁ ∈ P.divisors, ∀ e₂ ∈ P.divisors,
      (∑ n ∈ Finset.Icc 1 Y,
        ((if e₁ ∣ n then (1 : ℝ) else 0) * (if e₂ ∣ n then (1 : ℝ) else 0))
          * ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α))
        ≤ (Y : ℝ) * (((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α) / ((Nat.lcm e₁ e₂ : ℕ) : ℝ)) := by
    intro e₁ h1 e₂ h2
    have hcoef : (0 : ℝ) ≤ (e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α := by
      have : (0 : ℝ) ≤ (e₁ : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h' : (0 : ℝ) ≤ (e₂ : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have hind : ∀ n : ℕ,
        ((if e₁ ∣ n then (1 : ℝ) else 0) * (if e₂ ∣ n then (1 : ℝ) else 0))
          ≤ (if Nat.lcm e₁ e₂ ∣ n then (1 : ℝ) else 0) := by
      intro n
      by_cases hn1 : e₁ ∣ n
      · by_cases hn2 : e₂ ∣ n
        · rw [if_pos hn1, if_pos hn2, if_pos (Nat.lcm_dvd hn1 hn2), mul_one]
        · rw [if_neg hn2, mul_zero]
          split <;> norm_num
      · rw [if_neg hn1, zero_mul]
        split <;> norm_num
    have hstep : (∑ n ∈ Finset.Icc 1 Y,
        ((if e₁ ∣ n then (1 : ℝ) else 0) * (if e₂ ∣ n then (1 : ℝ) else 0))
          * ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α))
        ≤ ∑ n ∈ Finset.Icc 1 Y,
            (if Nat.lcm e₁ e₂ ∣ n then (1 : ℝ) else 0) * ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α) :=
      Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hind n) hcoef
    refine hstep.trans ?_
    rw [← Finset.sum_mul]
    have hcount := sum_indicator_dvd_le (Nat.lcm e₁ e₂) Y
    have hmul := mul_le_mul_of_nonneg_right hcount hcoef
    refine hmul.trans (le_of_eq ?_)
    rw [div_mul_eq_mul_div, mul_div_assoc]
  refine le_trans (Finset.sum_le_sum fun e₁ h1 => Finset.sum_le_sum (hterm e₁ h1)) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e₁ _ => ?_
  rw [Finset.mul_sum]

/-! ## The pair sum in gcd form -/

/-- **Each pair term is a power of the product times the gcd.**  `gcd·lcm = e₁e₂` turns the `lcm`
denominator into a `gcd` numerator, which Gauss's identity `∑_{d ∣ n} φ(d) = n` then expands. -/
theorem pair_term_eq {e₁ e₂ : ℕ} (h₁ : 0 < e₁) (h₂ : 0 < e₂) (α : ℝ) :
    ((e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α) / ((Nat.lcm e₁ e₂ : ℕ) : ℝ)
      = ((e₁ : ℝ) * (e₂ : ℝ)) ^ (α - 1) * ((Nat.gcd e₁ e₂ : ℕ) : ℝ) := by
  have h1R : (0 : ℝ) < (e₁ : ℝ) := by exact_mod_cast h₁
  have h2R : (0 : ℝ) < (e₂ : ℝ) := by exact_mod_cast h₂
  have hgl : Nat.gcd e₁ e₂ * Nat.lcm e₁ e₂ = e₁ * e₂ := Nat.gcd_mul_lcm e₁ e₂
  have hlcm : 0 < Nat.lcm e₁ e₂ := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.mul_zero] at hgl
    exact absurd hgl.symm (by positivity)
  have hlcmR : (0 : ℝ) < ((Nat.lcm e₁ e₂ : ℕ) : ℝ) := by exact_mod_cast hlcm
  have hglR : ((Nat.gcd e₁ e₂ : ℕ) : ℝ) * ((Nat.lcm e₁ e₂ : ℕ) : ℝ) = (e₁ : ℝ) * (e₂ : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hgl
  have hmul : (e₁ : ℝ) ^ α * (e₂ : ℝ) ^ α = ((e₁ : ℝ) * (e₂ : ℝ)) ^ α :=
    (Real.mul_rpow h1R.le h2R.le).symm
  have hsub : ((e₁ : ℝ) * (e₂ : ℝ)) ^ (α - 1)
      = ((e₁ : ℝ) * (e₂ : ℝ)) ^ α / ((e₁ : ℝ) * (e₂ : ℝ)) := by
    rw [Real.rpow_sub (by positivity), Real.rpow_one]
  rw [hmul, hsub, ← hglR]
  field_simp

/-- The divisors of a gcd of two divisors of `P`. -/
theorem divisors_gcd_pair_eq {P e₁ e₂ : ℕ} (hP : 0 < P) (h₁ : e₁ ∈ P.divisors)
    (_h₂ : e₂ ∈ P.divisors) :
    (Nat.gcd e₁ e₂).divisors = P.divisors.filter (fun d => d ∣ e₁ ∧ d ∣ e₂) := by
  classical
  have hd₁ : e₁ ∣ P := (Nat.mem_divisors.1 h₁).1
  have he₁ : 0 < e₁ := Nat.pos_of_mem_divisors h₁
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, -⟩
    exact ⟨⟨ha.trans hd₁, by omega⟩, ha, hb⟩
  · rintro ⟨⟨-, -⟩, ha, hb⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    have : 0 < Nat.gcd e₁ e₂ := Nat.gcd_pos_of_pos_left _ he₁
    omega

/-- **Gauss's identity on a pair of divisors.** -/
theorem gcd_eq_sum_totient_filter {P e₁ e₂ : ℕ} (hP : 0 < P) (h₁ : e₁ ∈ P.divisors)
    (h₂ : e₂ ∈ P.divisors) :
    ((Nat.gcd e₁ e₂ : ℕ) : ℝ)
      = ∑ d ∈ P.divisors, (if d ∣ e₁ ∧ d ∣ e₂ then ((Nat.totient d : ℕ) : ℝ) else 0) := by
  classical
  have hsum : ∑ d ∈ (Nat.gcd e₁ e₂).divisors, Nat.totient d = Nat.gcd e₁ e₂ :=
    Nat.sum_totient _
  rw [divisors_gcd_pair_eq hP h₁ h₂] at hsum
  rw [← Finset.sum_filter]
  exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsum.symm

/-- **The pair sum, expanded by Gauss's identity.** -/
theorem sum_pair_gcd_eq {P : ℕ} (hP : 0 < P) (α : ℝ) :
    (∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (α - 1) * ((Nat.gcd e₁ e₂ : ℕ) : ℝ))
      = ∑ d ∈ P.divisors, ((Nat.totient d : ℕ) : ℝ)
          * (∑ e ∈ P.divisors.filter (fun e => d ∣ e), (e : ℝ) ^ (α - 1)) ^ 2 := by
  classical
  have hexp : ∀ e₁ ∈ P.divisors, ∀ e₂ ∈ P.divisors,
      ((e₁ : ℝ) * (e₂ : ℝ)) ^ (α - 1) * ((Nat.gcd e₁ e₂ : ℕ) : ℝ)
        = ∑ d ∈ P.divisors, (if d ∣ e₁ then (e₁ : ℝ) ^ (α - 1) else 0)
            * (if d ∣ e₂ then (e₂ : ℝ) ^ (α - 1) else 0) * ((Nat.totient d : ℕ) : ℝ) := by
    intro e₁ h₁ e₂ h₂
    have h1R : (0 : ℝ) ≤ (e₁ : ℝ) := Nat.cast_nonneg _
    have h2R : (0 : ℝ) ≤ (e₂ : ℝ) := Nat.cast_nonneg _
    rw [Real.mul_rpow h1R h2R, gcd_eq_sum_totient_filter hP h₁ h₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd₁ : d ∣ e₁ <;> by_cases hd₂ : d ∣ e₂ <;> simp [hd₁, hd₂]
  rw [Finset.sum_congr rfl fun e₁ h₁ => Finset.sum_congr rfl fun e₂ h₂ => hexp e₁ h₁ e₂ h₂]
  -- swap the sums and factor
  rw [Finset.sum_congr rfl fun e₁ (_ : e₁ ∈ P.divisors) => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hfac : (∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
        (if d ∣ e₁ then (e₁ : ℝ) ^ (α - 1) else 0) * (if d ∣ e₂ then (e₂ : ℝ) ^ (α - 1) else 0)
          * ((Nat.totient d : ℕ) : ℝ))
      = ((Nat.totient d : ℕ) : ℝ)
        * ((∑ e ∈ P.divisors, (if d ∣ e then (e : ℝ) ^ (α - 1) else 0))
          * ∑ e ∈ P.divisors, (if d ∣ e then (e : ℝ) ^ (α - 1) else 0)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₂ _ => ?_
    ring
  rw [hfac, ← Finset.sum_filter, sq]

/-- A real power of a cast finite product factors into the product of the
corresponding real powers. -/
lemma natCast_prod_rpow (s : Finset ℕ) (β : ℝ) :
    (((∏ p ∈ s, p : ℕ) : ℝ) ^ β) = ∏ p ∈ s, (p : ℝ) ^ β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg (∏ q ∈ s, q)),
        Finset.prod_insert hp, ih]

/-- For a squarefree integer, a real power is the product of the same powers
over its prime factors. -/
lemma natCast_rpow_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) (β : ℝ) :
    (n : ℝ) ^ β = ∏ p ∈ n.primeFactors, (p : ℝ) ^ β := by
  calc
    (n : ℝ) ^ β = (((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ^ β) := by
      rw [Nat.prod_primeFactors_of_squarefree hn]
    _ = ∏ p ∈ n.primeFactors, (p : ℝ) ^ β :=
      natCast_prod_rpow n.primeFactors β

/-- Euler-product evaluation of a divisor real-power sum for squarefree
integers. -/
theorem sum_divisors_rpow_eq_prod
    {P : ℕ} (hSq : Squarefree P) (β : ℝ) :
    ∑ d ∈ P.divisors, (d : ℝ) ^ β =
      ∏ p ∈ P.primeFactors, ((p : ℝ) ^ β + 1) := by
  have hprod : ∏ p ∈ P.primeFactors, p = P :=
    Nat.prod_primeFactors_of_squarefree hSq
  calc
    ∑ d ∈ P.divisors, (d : ℝ) ^ β =
        ∑ d ∈ P.divisors, ∏ p ∈ d.primeFactors, (p : ℝ) ^ β := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← natCast_rpow_eq_prod_primeFactors
        (hSq.squarefree_of_dvd (Nat.mem_divisors.mp hd).1) β]
    _ = ∑ d ∈ (∏ p ∈ P.primeFactors, p).divisors,
          ∏ p ∈ d.primeFactors, (p : ℝ) ^ β := by rw [hprod]
    _ = ∏ p ∈ P.primeFactors, ((p : ℝ) ^ β + 1) := by
      exact sum_divisors_prod_primes_eq_prod
        (fun p hp => Nat.prime_of_mem_primeFactors hp) (fun p => (p : ℝ) ^ β)

/-- Divisors of `P` divisible by `d` inject into all divisors of `P` after
division by `d`. Real-power positivity turns the injection into the needed
Rankin-sum bound. -/
theorem sum_filter_dvd_rpow_le
    {P d : ℕ} (hP : 0 < P) (β : ℝ) :
    ∑ e ∈ P.divisors.filter (fun e => d ∣ e), (e : ℝ) ^ β ≤
      (d : ℝ) ^ β * ∑ f ∈ P.divisors, (f : ℝ) ^ β := by
  let s := P.divisors.filter (fun e => d ∣ e)
  have hquot_subset : s.image (fun e => e / d) ⊆ P.divisors := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨e, he, rfl⟩ := hf
    have heP : e ∈ P.divisors := (Finset.mem_filter.mp he).1
    exact Nat.mem_divisors.mpr ⟨
      (Nat.div_dvd_of_dvd (Finset.mem_filter.mp he).2).trans
        (Nat.mem_divisors.mp heP).1,
      ne_of_gt hP⟩
  have hquot_inj : Set.InjOn (fun e => e / d) s := by
    intro e₁ he₁ e₂ he₂ heq
    have hd₁ : d ∣ e₁ := (Finset.mem_filter.mp he₁).2
    have hd₂ : d ∣ e₂ := (Finset.mem_filter.mp he₂).2
    calc
      e₁ = d * (e₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (e₂ / d) := congrArg (d * ·) heq
      _ = e₂ := Nat.mul_div_cancel' hd₂
  have hquot_sum :
      ∑ e ∈ s, ((e / d : ℕ) : ℝ) ^ β =
        ∑ f ∈ s.image (fun e => e / d), (f : ℝ) ^ β := by
    simpa using
      (Finset.sum_image (f := fun f : ℕ => (f : ℝ) ^ β) hquot_inj).symm
  have hsum_le :
      ∑ e ∈ s, ((e / d : ℕ) : ℝ) ^ β ≤
        ∑ f ∈ P.divisors, (f : ℝ) ^ β := by
    rw [hquot_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hquot_subset
      (fun f _ _ => Real.rpow_nonneg (Nat.cast_nonneg f) β)
  change ∑ e ∈ s, (e : ℝ) ^ β ≤
    (d : ℝ) ^ β * ∑ f ∈ P.divisors, (f : ℝ) ^ β
  calc
    ∑ e ∈ s, (e : ℝ) ^ β =
        ∑ e ∈ s, (d : ℝ) ^ β * ((e / d : ℕ) : ℝ) ^ β := by
      apply Finset.sum_congr rfl
      intro e he
      have hde : d ∣ e := (Finset.mem_filter.mp he).2
      rw [← Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg (e / d))]
      congr 1
      norm_cast
      exact (Nat.mul_div_cancel' hde).symm
    _ = (d : ℝ) ^ β * ∑ e ∈ s, ((e / d : ℕ) : ℝ) ^ β := by
      rw [Finset.mul_sum]
    _ ≤ (d : ℝ) ^ β * ∑ f ∈ P.divisors, (f : ℝ) ^ β :=
      mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg (Nat.cast_nonneg d) β)

/-- One totient-weighted square in the divisor-moment expansion is bounded by
the global divisor power sum and the residual divisor power. -/
lemma totient_mul_inner_sq_le
    {P d : ℕ} (hP : 0 < P) (hd : d ∈ P.divisors) (α : ℝ) :
    (d.totient : ℝ) *
        (∑ e ∈ P.divisors.filter (fun e => d ∣ e), (e : ℝ) ^ (α - 1)) ^ 2 ≤
      (∑ f ∈ P.divisors, (f : ℝ) ^ (α - 1)) ^ 2 *
        (d : ℝ) ^ (2 * α - 1) := by
  let inner : ℝ :=
    ∑ e ∈ P.divisors.filter (fun e => d ∣ e), (e : ℝ) ^ (α - 1)
  let A : ℝ := ∑ f ∈ P.divisors, (f : ℝ) ^ (α - 1)
  have hinner_nonneg : 0 ≤ inner := by
    exact Finset.sum_nonneg fun e _ =>
      Real.rpow_nonneg (Nat.cast_nonneg e) (α - 1)
  have hA_nonneg : 0 ≤ A := by
    exact Finset.sum_nonneg fun f _ =>
      Real.rpow_nonneg (Nat.cast_nonneg f) (α - 1)
  have hinner_le : inner ≤ (d : ℝ) ^ (α - 1) * A := by
    exact sum_filter_dvd_rpow_le hP (α - 1)
  have hright_nonneg : 0 ≤ (d : ℝ) ^ (α - 1) * A :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) (α - 1)) hA_nonneg
  have hsq : inner ^ 2 ≤ ((d : ℝ) ^ (α - 1) * A) ^ 2 :=
    (sq_le_sq₀ hinner_nonneg hright_nonneg).2 hinner_le
  have htotient : (d.totient : ℝ) ≤ d := by
    exact_mod_cast Nat.totient_le d
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors hd
  have hrpow_sq : ((d : ℝ) ^ (α - 1)) ^ 2 =
      (d : ℝ) ^ (2 * (α - 1)) := by
    rw [pow_two, ← Real.rpow_add hdpos]
    congr 1
    ring
  change (d.totient : ℝ) * inner ^ 2 ≤ A ^ 2 * (d : ℝ) ^ (2 * α - 1)
  calc
    (d.totient : ℝ) * inner ^ 2 ≤
        (d.totient : ℝ) * ((d : ℝ) ^ (α - 1) * A) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d.totient)
    _ ≤ (d : ℝ) * ((d : ℝ) ^ (α - 1) * A) ^ 2 :=
      mul_le_mul_of_nonneg_right htotient (sq_nonneg _)
    _ = A ^ 2 * (((d : ℝ) ^ (1 : ℝ)) * ((d : ℝ) ^ (α - 1)) ^ 2) := by
      rw [Real.rpow_one]
      ring
    _ = A ^ 2 * (((d : ℝ) ^ (1 : ℝ)) *
          (d : ℝ) ^ (2 * (α - 1))) := by rw [hrpow_sq]
    _ = A ^ 2 * (d : ℝ) ^ (1 + 2 * (α - 1)) := by
      rw [Real.rpow_add hdpos]
    _ = A ^ 2 * (d : ℝ) ^ (2 * α - 1) := by ring_nf

/-- The divisor pair sum is bounded by two one-variable divisor power sums. -/
theorem sum_pair_gcd_le_divisor_rpow
    {P : ℕ} (hP : 0 < P) (α : ℝ) :
    ∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (α - 1) * (e₁.gcd e₂ : ℝ) ≤
      (∑ f ∈ P.divisors, (f : ℝ) ^ (α - 1)) ^ 2 *
        ∑ d ∈ P.divisors, (d : ℝ) ^ (2 * α - 1) := by
  rw [sum_pair_gcd_eq hP α]
  calc
    ∑ d ∈ P.divisors, (d.totient : ℝ) *
        (∑ e ∈ P.divisors.filter (fun e => d ∣ e), (e : ℝ) ^ (α - 1)) ^ 2 ≤
        ∑ d ∈ P.divisors,
          (∑ f ∈ P.divisors, (f : ℝ) ^ (α - 1)) ^ 2 *
            (d : ℝ) ^ (2 * α - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      exact totient_mul_inner_sq_le hP hd α
    _ = (∑ f ∈ P.divisors, (f : ℝ) ^ (α - 1)) ^ 2 *
        ∑ d ∈ P.divisors, (d : ℝ) ^ (2 * α - 1) := by
      rw [Finset.mul_sum]

/-- Euler-product form of the divisor pair bound used in the `c₁` mean-square
estimate of the Matomäki--Teräväinen minorant. -/
theorem sum_pair_gcd_le_eulerProducts
    {P : ℕ} (hP : 0 < P) (hSq : Squarefree P) (α : ℝ) :
    ∑ e₁ ∈ P.divisors, ∑ e₂ ∈ P.divisors,
        ((e₁ : ℝ) * (e₂ : ℝ)) ^ (α - 1) * (e₁.gcd e₂ : ℝ) ≤
      (∏ p ∈ P.primeFactors, ((p : ℝ) ^ (α - 1) + 1)) ^ 2 *
        ∏ p ∈ P.primeFactors, ((p : ℝ) ^ (2 * α - 1) + 1) := by
  rw [← sum_divisors_rpow_eq_prod hSq (α - 1),
    ← sum_divisors_rpow_eq_prod hSq (2 * α - 1)]
  exact sum_pair_gcd_le_divisor_rpow hP α

end RHTower.Sieve
