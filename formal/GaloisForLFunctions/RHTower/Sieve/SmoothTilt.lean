import GaloisForLFunctions.RHTower.Sieve.SmoothSum
import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# Tilted bound for smooth numbers with few prime factors

Restricting the reciprocal sum over `z`-smooth integers to those with at most `k` distinct prime
factors is handled by the same exponential tilt that controls the Brun truncation defect: for
`0 < t ≤ 1` and `ω s ≤ k` one has `t ^ k ≤ t ^ ω s`, so

`∑_{s z-smooth, ω s ≤ k} 1/s ≤ t^{-k} ∑_{s z-smooth} t^{ω s}/s ≤ t^{-k} ∏_{p ≤ z} (1 + t/(p-1))`.

The shifted Euler product is then evaluated by Mertens' second theorem, using
`∑_{p ≤ z} 1/(p-1) ≤ ∑_{p ≤ z} 1/p + 1`, where the correction telescopes because
`1/(k(k-1)) = 1/(k-1) - 1/k`.

Optimising `t` at `k / ∑_{p ≤ z} 1/p` turns the bound into `exp` of the Chernoff rate
`I(c) = 1 - c + c log c` evaluated at `c = k / log log z`; no elementary symmetric function
inequality is used.
-/

namespace RHTower.Sieve

open Finset Nat

/-- A tilted Euler product against an arbitrary nonnegative weight. -/
theorem prod_one_add_mul_le_exp (P : Finset ℕ) {t : ℝ} (ht : 0 ≤ t) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) :
    ∏ p ∈ P, (1 + t * w p) ≤ Real.exp (t * ∑ p ∈ P, w p) := by
  have hnonneg : ∀ p ∈ P, (0 : ℝ) ≤ 1 + t * w p := by
    intro p hp
    have : (0 : ℝ) ≤ t * w p := mul_nonneg ht (hw p hp)
    linarith
  have hstep : ∀ p ∈ P, 1 + t * w p ≤ Real.exp (t * w p) := by
    intro p _
    have := Real.add_one_le_exp (t * w p)
    linarith
  calc ∏ p ∈ P, (1 + t * w p)
      ≤ ∏ p ∈ P, Real.exp (t * w p) := Finset.prod_le_prod hnonneg hstep
    _ = Real.exp (∑ p ∈ P, t * w p) := (Real.exp_sum _ _).symm
    _ = Real.exp (t * ∑ p ∈ P, w p) := by rw [← Finset.mul_sum]

/-- The shifted prime reciprocal sum exceeds the ordinary one by at most `1`. -/
theorem sum_inv_pred_primesLE_le (z : ℕ) :
    ∑ p ∈ Nat.primesLE z, 1 / ((p : ℝ) - 1) ≤ mertensS z + 1 := by
  have hsplit : ∑ p ∈ Nat.primesLE z, 1 / ((p : ℝ) - 1)
      = mertensS z + ∑ p ∈ Nat.primesLE z, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [mertensS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have h0 : (p : ℝ) ≠ 0 := by intro h; rw [h] at hpR; linarith
    have h1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith [h]
    field_simp
    ring
  have htail : ∑ p ∈ Nat.primesLE z, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    have hsub : Nat.primesLE z ⊆ Finset.Ico 2 (z + 1) := by
      intro p hp
      obtain ⟨hple, hprime⟩ := Nat.mem_primesLE.1 hp
      exact Finset.mem_Ico.2 ⟨hprime.two_le, by omega⟩
    have hnonneg : ∀ k ∈ Finset.Ico 2 (z + 1), (0 : ℝ) ≤ 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
      intro k hk
      have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Ico.1 hk).1
      have : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
      positivity
    have hmono : ∑ p ∈ Nat.primesLE z, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ k ∈ Finset.Ico 2 (z + 1), 1 / ((k : ℝ) * ((k : ℝ) - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnonneg k hk
    refine le_trans hmono ?_
    rcases Nat.lt_or_ge z 2 with hz | hz
    · have : Finset.Ico 2 (z + 1) = ∅ := by
        refine Finset.Ico_eq_empty ?_
        omega
      rw [this, Finset.sum_empty]
      norm_num
    · have hcong : ∀ k ∈ Finset.Ico 2 (z + 1),
          (fun k : ℕ => -(1 / ((k : ℝ) - 1))) (k + 1) - (fun k : ℕ => -(1 / ((k : ℝ) - 1))) k
            = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
        intro k hk
        have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Ico.1 hk).1
        have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        have h0 : (k : ℝ) ≠ 0 := by intro h; rw [h] at hkR; linarith
        have h1 : (k : ℝ) - 1 ≠ 0 := by intro h; linarith [h]
        have hkey : -(1 / ((k : ℝ))) - (-(1 / ((k : ℝ) - 1))) = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
          field_simp
          ring
        simp only [hc, add_sub_cancel_right]
        exact hkey
      have hz1 : 2 ≤ z + 1 := by omega
      have htel := sum_Ico_telescope (fun k : ℕ => -(1 / ((k : ℝ) - 1))) hz1
      rw [Finset.sum_congr rfl hcong] at htel
      rw [htel]
      have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      have hpos : (0 : ℝ) < ((z + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
      have : (0 : ℝ) < 1 / (((z + 1 : ℕ) : ℝ) - 1) := by positivity
      norm_num
  linarith

/-- **Tilted smooth bound.**  The reciprocal sum over `z`-smooth integers with at most `k` distinct
prime factors is bounded by the tilted Euler product. -/
theorem sum_smoothUpTo_card_le_inv_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (k z Y : ℕ) :
    ∑ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k}, (1 : ℝ) / s
      ≤ (∏ p ∈ Nat.primesLE z, (1 + t / ((p : ℝ) - 1))) / t ^ k := by
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  rw [le_div_iff₀ htk, Finset.sum_mul]
  have hstep : ∀ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k},
      (1 : ℝ) / s * t ^ k ≤ smoothWeight t s := by
    intro s hs
    obtain ⟨hsmem, hcard⟩ := Finset.mem_filter.1 hs
    have hs1 : 1 ≤ s := (mem_smoothUpTo.1 hsmem).1.1
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
    have hpow : t ^ k ≤ t ^ s.primeFactors.card := pow_le_pow_of_le_one ht0.le ht1 hcard
    unfold smoothWeight
    rw [div_mul_eq_mul_div, one_mul, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.2 hsR.le)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun s _ _ => smoothWeight_nonneg ht0.le s)) ?_
  exact sum_smoothWeight_le ht0.le z Y

/-- **Tilted smooth bound, exponential form.**  Mertens' second theorem evaluates the Euler
product, leaving the Chernoff shape `t^{-k} exp(t (log log z + C))`. -/
theorem sum_smoothUpTo_card_le_inv_le_exp {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (k : ℕ) {z : ℕ}
    (hz : 2 ≤ z) (Y : ℕ) :
    ∑ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k}, (1 : ℝ) / s
      ≤ Real.exp (t * (logLog z + mertensSecondUpperConst + 1)) / t ^ k := by
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  refine le_trans (sum_smoothUpTo_card_le_inv_le ht0 ht1 k z Y) ?_
  rw [div_le_div_iff_of_pos_right htk]
  have hw : ∀ p ∈ Nat.primesLE z, (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hrw : ∏ p ∈ Nat.primesLE z, (1 + t / ((p : ℝ) - 1))
      = ∏ p ∈ Nat.primesLE z, (1 + t * (1 / ((p : ℝ) - 1))) := by
    refine Finset.prod_congr rfl ?_
    intro p _
    rw [mul_one_div]
  rw [hrw]
  refine le_trans (prod_one_add_mul_le_exp _ ht0.le _ hw) ?_
  refine Real.exp_le_exp.2 ?_
  have hsum := sum_inv_pred_primesLE_le z
  have hmert := mertensS_le hz
  have : ∑ p ∈ Nat.primesLE z, 1 / ((p : ℝ) - 1) ≤ logLog z + mertensSecondUpperConst + 1 := by
    linarith
  exact mul_le_mul_of_nonneg_left this ht0.le

end RHTower.Sieve
