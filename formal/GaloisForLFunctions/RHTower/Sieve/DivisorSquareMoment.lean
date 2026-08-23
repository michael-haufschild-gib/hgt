import GaloisForLFunctions.RHTower.Sieve.BrunTitchmarsh

/-!
# The second moment of the divisor function

`Σ_{n ≤ N} d(n)² ≤ N·H_N³`, by counting the pairs of divisors: the number of `n ≤ N` divisible by
both `a` and `b` is `N/lcm(a,b) = N·gcd(a,b)/(ab)`, and Gauss's identity `Σ_{g ∣ m} φ(g) = m`
turns the resulting `gcd` into a third harmonic factor.  This is the only coefficient moment the
type-II half of Vaughan's identity needs.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The real harmonic sum. -/
def invSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n

theorem invSum_nonneg (N : ℕ) : 0 ≤ invSum N :=
  Finset.sum_nonneg fun n _ => by positivity

theorem invSum_mono {M N : ℕ} (h : M ≤ N) : invSum M ≤ invSum N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h) ?_
  intro n _ _
  positivity

/-- The reciprocal sum over the multiples of `g`. -/
theorem sum_inv_multiples_real (N g : ℕ) (hg : 1 ≤ g) :
    (∑ n ∈ (Finset.Icc 1 N).filter (g ∣ ·), (1 : ℝ) / n) = (1 / g) * invSum (N / g) := by
  rw [invSum, Finset.mul_sum]
  refine (Finset.sum_bij' (fun k _ => g * k) (fun n _ => n / g) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk ⊢
    refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < g)).mp hk.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hgn⟩
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hgn) (by omega), Nat.div_le_div_right hnN⟩
  · intro k _hk
    exact Nat.mul_div_cancel_left k (by omega)
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
    have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
    push_cast
    field_simp

/-- The divisors of `n` are the divisibility filter on `[1, N]`. -/
theorem divisors_eq_filter_Icc {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (· ∣ n) := by
  ext a
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hdvd, -⟩
    have ha1 : 1 ≤ a := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have han : a ≤ n := Nat.le_of_dvd (by omega) hdvd
    exact ⟨⟨ha1, by omega⟩, hdvd⟩
  · rintro ⟨-, hdvd⟩
    exact ⟨hdvd, by omega⟩

/-- The number of `n ≤ N` divisible by both `a` and `b`. -/
theorem card_filter_dvd_pair_le (N : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((((Finset.Icc 1 N).filter (fun n => a ∣ n ∧ b ∣ n)).card : ℕ) : ℝ)
      ≤ (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) := by
  have hL : 1 ≤ Nat.lcm a b := Nat.one_le_iff_ne_zero.2 (Nat.lcm_ne_zero (by omega) (by omega))
  have hset : (Finset.Icc 1 N).filter (fun n => a ∣ n ∧ b ∣ n)
      = (Finset.Ioc 0 N).filter (Nat.lcm a b ∣ ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Nat.lcm_dvd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd⟩
      exact ⟨⟨by omega, h2⟩, hd⟩
    · rintro ⟨⟨h1, h2⟩, hd⟩
      exact ⟨⟨by omega, h2⟩, hd⟩
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  have hLpos : (0 : ℝ) < (Nat.lcm a b : ℝ) := by exact_mod_cast hL
  have hdiv : ((N / Nat.lcm a b : ℕ) : ℝ) ≤ (N : ℝ) / (Nat.lcm a b : ℝ) := by
    rw [le_div_iff₀ hLpos]
    have := Nat.div_mul_le_self N (Nat.lcm a b)
    exact_mod_cast this
  refine hdiv.trans (le_of_eq ?_)
  have hglr : ((Nat.gcd a b : ℕ) : ℝ) * ((Nat.lcm a b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  field_simp
  linear_combination (-(N : ℝ)) * hglr

/-- Gauss's identity, packaged as an indicator sum over `[1, N]`. -/
theorem gcd_eq_sum_totient_indicator {N a b : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (_hb : 1 ≤ b) :
    ((Nat.gcd a b : ℕ) : ℝ)
      = ∑ g ∈ Finset.Icc 1 N, (if g ∣ a ∧ g ∣ b then (Nat.totient g : ℝ) else 0) := by
  have hg1 : 1 ≤ Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by omega)
  have hgN : Nat.gcd a b ≤ N := le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)) haN
  have hsum : ∑ g ∈ (Nat.gcd a b).divisors, (Nat.totient g : ℕ) = Nat.gcd a b :=
    Nat.sum_totient _
  have hfilter : (Nat.gcd a b).divisors = (Finset.Icc 1 N).filter (fun g => g ∣ a ∧ g ∣ b) := by
    rw [divisors_eq_filter_Icc hg1 hgN]
    refine Finset.filter_congr fun g _ => ?_
    simp [Nat.dvd_gcd_iff]
  have hcast : ((Nat.gcd a b : ℕ) : ℝ)
      = ∑ g ∈ (Nat.gcd a b).divisors, (Nat.totient g : ℝ) := by
    exact_mod_cast hsum.symm
  rw [hcast, hfilter, Finset.sum_filter]

/-- **The second moment of the divisor function.** -/
theorem sum_card_divisors_sq_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) * invSum N ^ 3 := by
  classical
  have hexp : ∀ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ 2
      = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          (if a ∣ n then (1 : ℝ) else 0) * (if b ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hcard : ((n.divisors.card : ℕ) : ℝ)
        = ∑ a ∈ Finset.Icc 1 N, (if a ∣ n then (1 : ℝ) else 0) := by
      rw [← Finset.sum_filter, divisors_eq_filter_Icc hn.1 hn.2]
      simp
    rw [hcard, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hexp]
  have hswap : ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        (if a ∣ n then (1 : ℝ) else 0) * (if b ∣ n then (1 : ℝ) else 0)
      = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if a ∣ n then (1 : ℝ) else 0) * (if b ∣ n then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  have hcount : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc 1 N,
          (if a ∣ n then (1 : ℝ) else 0) * (if b ∣ n then (1 : ℝ) else 0))
        ≤ (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ)) := by
    intro a ha b hb
    rw [Finset.mem_Icc] at ha hb
    have hid : (∑ n ∈ Finset.Icc 1 N,
        (if a ∣ n then (1 : ℝ) else 0) * (if b ∣ n then (1 : ℝ) else 0))
        = (((Finset.Icc 1 N).filter (fun n => a ∣ n ∧ b ∣ n)).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h1 : a ∣ n <;> by_cases h2 : b ∣ n <;> simp [h1, h2]
    rw [hid]
    exact card_filter_dvd_pair_le N ha.1 hb.1
  refine le_trans (Finset.sum_le_sum fun a ha =>
    Finset.sum_le_sum fun b hb => hcount a ha b hb) ?_
  have hgauss : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
      (N : ℝ) * (Nat.gcd a b : ℝ) / ((a : ℝ) * (b : ℝ))
        = ∑ g ∈ Finset.Icc 1 N,
            (N : ℝ) * ((if g ∣ a then (1 : ℝ) else 0) / a)
              * ((if g ∣ b then (1 : ℝ) else 0) / b) * (Nat.totient g : ℝ) := by
    intro a ha b hb
    rw [Finset.mem_Icc] at ha hb
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha.1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb.1
    rw [gcd_eq_sum_totient_indicator ha.1 ha.2 hb.1, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases h1 : g ∣ a <;> by_cases h2 : g ∣ b <;> simp [h1, h2] <;> field_simp
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hgauss a ha b hb]
  have hswap2 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N,
        (N : ℝ) * ((if g ∣ a then (1 : ℝ) else 0) / a)
          * ((if g ∣ b then (1 : ℝ) else 0) / b) * (Nat.totient g : ℝ)
      = ∑ g ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          (N : ℝ) * ((if g ∣ a then (1 : ℝ) else 0) / a)
            * ((if g ∣ b then (1 : ℝ) else 0) / b) * (Nat.totient g : ℝ) := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.Icc 1 N) => Finset.sum_comm]
    exact Finset.sum_comm
  rw [hswap2]
  have hfactor : ∀ g ∈ Finset.Icc 1 N,
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          (N : ℝ) * ((if g ∣ a then (1 : ℝ) else 0) / a)
            * ((if g ∣ b then (1 : ℝ) else 0) / b) * (Nat.totient g : ℝ))
        = ((N : ℝ) * (Nat.totient g : ℝ))
            * ((∑ a ∈ Finset.Icc 1 N, (if g ∣ a then (1 : ℝ) else 0) / a)
                * ∑ b ∈ Finset.Icc 1 N, (if g ∣ b then (1 : ℝ) else 0) / b) := by
    intro g _
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl hfactor]
  have hinner : ∀ g ∈ Finset.Icc 1 N,
      (∑ a ∈ Finset.Icc 1 N, (if g ∣ a then (1 : ℝ) else 0) / a)
        = (1 / g) * invSum (N / g) := by
    intro g hg
    rw [Finset.mem_Icc] at hg
    rw [← sum_inv_multiples_real N g hg.1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : g ∣ a <;> simp [h]
  have hrewrite : (∑ g ∈ Finset.Icc 1 N, ((N : ℝ) * (Nat.totient g : ℝ))
        * ((∑ a ∈ Finset.Icc 1 N, (if g ∣ a then (1 : ℝ) else 0) / a)
            * ∑ b ∈ Finset.Icc 1 N, (if g ∣ b then (1 : ℝ) else 0) / b))
      = ∑ g ∈ Finset.Icc 1 N, ((N : ℝ) * (Nat.totient g : ℝ))
          * ((1 / g) * invSum (N / g) * ((1 / g) * invSum (N / g))) :=
    Finset.sum_congr rfl fun g hg => by rw [hinner g hg]
  rw [hrewrite]
  have hbound : ∀ g ∈ Finset.Icc 1 N,
      ((N : ℝ) * (Nat.totient g : ℝ)) * ((1 / g) * invSum (N / g) * ((1 / g) * invSum (N / g)))
        ≤ (N : ℝ) * invSum N ^ 2 * (1 / g) := by
    intro g hg
    rw [Finset.mem_Icc] at hg
    have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg.1
    have hphi : ((Nat.totient g : ℕ) : ℝ) ≤ (g : ℝ) := by exact_mod_cast Nat.totient_le g
    have hmono : invSum (N / g) ≤ invSum N := invSum_mono (Nat.div_le_self N g)
    have hnn : 0 ≤ invSum (N / g) := invSum_nonneg _
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hsq : invSum (N / g) * invSum (N / g) ≤ invSum N ^ 2 := by nlinarith
    have hid : ((N : ℝ) * (Nat.totient g : ℝ))
        * ((1 / g) * invSum (N / g) * ((1 / g) * invSum (N / g)))
        = (N : ℝ) * (Nat.totient g : ℝ) / (g : ℝ) ^ 2
            * (invSum (N / g) * invSum (N / g)) := by
      field_simp
    rw [hid]
    have hcoef : (N : ℝ) * (Nat.totient g : ℝ) / (g : ℝ) ^ 2 ≤ (N : ℝ) * (1 / g) := by
      rw [div_le_iff₀ (by positivity)]
      have hstep : (N : ℝ) * (Nat.totient g : ℝ) ≤ (N : ℝ) * (g : ℝ) :=
        mul_le_mul_of_nonneg_left hphi hN0
      have : (N : ℝ) * (1 / g) * (g : ℝ) ^ 2 = (N : ℝ) * (g : ℝ) := by field_simp
      rw [this]
      exact hstep
    have hsq0 : (0 : ℝ) ≤ invSum (N / g) * invSum (N / g) := by positivity
    calc (N : ℝ) * (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (invSum (N / g) * invSum (N / g))
        ≤ ((N : ℝ) * (1 / g)) * (invSum N ^ 2) :=
          mul_le_mul hcoef hsq hsq0 (by positivity)
      _ = (N : ℝ) * invSum N ^ 2 * (1 / g) := by ring
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [← Finset.mul_sum, show (∑ g ∈ Finset.Icc 1 N, (1 : ℝ) / g) = invSum N from rfl]
  ring_nf
  rfl

end

end RHTower.Sieve
