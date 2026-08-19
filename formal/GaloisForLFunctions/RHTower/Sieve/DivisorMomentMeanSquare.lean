import GaloisForLFunctions.RHTower.Sieve.JointTuranKubilius

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

end RHTower.Sieve
