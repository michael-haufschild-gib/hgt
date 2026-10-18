import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic

/-!
# Ordered pronic gap cells and collective prefix energy

A compensated residue difference has zero pronic mean on each quotient cell
before its two jump progressions overlap. For disjoint ordered modulus gaps,
these cells have nonpositive pair covariance at every finite horizon. Splitting
signed coefficients into positive and negative parts gives a collective bound
with constant two and no factor counting the gaps.

Inside a cluster of total gap length `H` and base `P > K * H`, quotient levels
of equal parity have disjoint supports. The resulting all-level bound costs
four times the exact diagonal sum `h * harmonic K - K * h^2 / p`. Removing
the explicit birth correction gives a bound for the literal residue packet on
`n < (K + 1) * P`, with constant eight and birth cost `2 * H / P`.

The constructor `pronicGapChainLower` encodes the ordering and pre-overlap
condition from data. Public statements require no analytic hypotheses.
These are finite-prefix estimates; the later signed tail remains unbounded
by this argument. No complete-period averaging replaces the pronic weight.
-/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The compensated difference of two residue modes on one quotient cell. -/
def compensatedPronicGapCell (p h k n : ℕ) : ℝ :=
  if n ∈ Ico (k * p) (k * (p + h)) then (k : ℝ) * h - p
  else if n ∈ Ico (k * (p + h)) ((k + 1) * p) then ((k : ℝ) + 1) * h
  else 0

private theorem cell_pronic_interval {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ico a b, 1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / (a : ℝ) - 1 / b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab, ih]
    have hb : (b : ℝ) ≠ 0 := by have : 0 < b := ha.trans_le hab; positivity
    have haR : (a : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private theorem cell_zero_before {p h k n : ℕ} (hn : n < k * p) :
    compensatedPronicGapCell p h k n = 0 := by
  have hb : k * p ≤ k * (p + h) := by nlinarith
  have hfirst : n ∉ Ico (k * p) (k * (p + h)) := by simp only [mem_Ico]; omega
  have hsecond : n ∉ Ico (k * (p + h)) ((k + 1) * p) := by
    simp only [mem_Ico]
    omega
  simp only [compensatedPronicGapCell, if_neg hfirst, if_neg hsecond]

private theorem cell_zero_after {p h k n : ℕ} (hkh : k * h ≤ p)
    (hn : (k + 1) * p ≤ n) : compensatedPronicGapCell p h k n = 0 := by
  have hb : k * (p + h) ≤ (k + 1) * p := by nlinarith
  have hfirst : n ∉ Ico (k * p) (k * (p + h)) := by simp only [mem_Ico]; omega
  have hsecond : n ∉ Ico (k * (p + h)) ((k + 1) * p) := by
    simp only [mem_Ico]
    omega
  simp only [compensatedPronicGapCell, if_neg hfirst, if_neg hsecond]

private theorem cell_weighted_sum {p h k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hkh : k * h ≤ p) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ n ∈ range ((k + 1) * p),
      f (compensatedPronicGapCell p h k n) / ((n : ℝ) * ((n : ℝ) + 1))) =
      f ((k : ℝ) * h - p) *
        (1 / ((k : ℝ) * p) - 1 / ((k : ℝ) * ((p : ℝ) + h))) +
      f (((k : ℝ) + 1) * h) *
        (1 / ((k : ℝ) * ((p : ℝ) + h)) - 1 / (((k : ℝ) + 1) * p)) := by
  let g (n : ℕ) := f (compensatedPronicGapCell p h k n) /
    ((n : ℝ) * ((n : ℝ) + 1))
  have hab : k * p ≤ k * (p + h) := by nlinarith
  have hbc : k * (p + h) ≤ (k + 1) * p := by nlinarith
  have hzero : ∑ n ∈ range (k * p), g n = 0 := by
    apply sum_eq_zero
    intro n hn
    simp only [g, cell_zero_before (mem_range.mp hn), hf, zero_div]
  have hfirst : (∑ n ∈ Ico (k * p) (k * (p + h)), g n) =
      f ((k : ℝ) * h - p) *
        (1 / ((k : ℝ) * p) - 1 / ((k : ℝ) * ((p : ℝ) + h))) := by
    calc
      _ = ∑ n ∈ Ico (k * p) (k * (p + h)),
          f ((k : ℝ) * h - p) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        simp only [g, compensatedPronicGapCell, if_pos hn, mul_one_div]
      _ = _ := by
        rw [← mul_sum, cell_pronic_interval (by positivity) hab]
        push_cast
        rfl
  have hsecond : (∑ n ∈ Ico (k * (p + h)) ((k + 1) * p), g n) =
      f (((k : ℝ) + 1) * h) *
        (1 / ((k : ℝ) * ((p : ℝ) + h)) - 1 / (((k : ℝ) + 1) * p)) := by
    calc
      _ = ∑ n ∈ Ico (k * (p + h)) ((k + 1) * p),
          f (((k : ℝ) + 1) * h) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        have hnfirst : n ∉ Ico (k * p) (k * (p + h)) := by
          have := (mem_Ico.mp hn).1
          simp only [mem_Ico]
          omega
        simp only [g, compensatedPronicGapCell, if_neg hnfirst, if_pos hn, mul_one_div]
      _ = _ := by
        rw [← mul_sum, cell_pronic_interval (by positivity) hbc]
        push_cast
        rfl
  change ∑ n ∈ range ((k + 1) * p), g n = _
  rw [← sum_range_add_sum_Ico g (hab.trans hbc), hzero, zero_add,
    ← sum_Ico_consecutive g hab hbc, hfirst, hsecond]

private theorem cell_mean_zero {p h k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hkh : k * h ≤ p) :
    (∑ n ∈ range ((k + 1) * p),
      compensatedPronicGapCell p h k n / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
  have hs := cell_weighted_sum hp hk hkh id rfl
  simp only [id_eq] at hs
  rw [hs]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hqR : (p : ℝ) + h ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem cell_energy_exact {p h k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hkh : k * h ≤ p) :
    (∑ n ∈ range ((k + 1) * p),
      (compensatedPronicGapCell p h k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      (h : ℝ) / k - (h : ℝ) ^ 2 / p := by
  rw [cell_weighted_sum hp hk hkh (fun x => x ^ 2) (by simp)]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hqR : (p : ℝ) + h ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem sum_range_cutoff (f : ℕ → ℝ) (T C : ℕ)
    (hf : ∀ n, C ≤ n → f n = 0) :
    (∑ n ∈ range T, f n) = ∑ n ∈ range (min T C), f n := by
  symm
  apply sum_subset (range_mono (min_le_left _ _))
  intro n hn hnc
  apply hf
  have := mem_range.mp hn
  have := not_lt.mp (fun h => hnc (mem_range.mpr h))
  omega

private theorem cell_prefix_mean_nonpos {p h k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hkh : k * h ≤ p) (T : ℕ) :
    (∑ n ∈ range T,
      compensatedPronicGapCell p h k n / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 0 := by
  have hneg : (k : ℝ) * h - p ≤ 0 := by
    have ht : (k : ℝ) * h ≤ p := by exact_mod_cast hkh
    linarith
  by_cases hT : T ≤ k * (p + h)
  · apply sum_nonpos
    intro n hn
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hnT := mem_range.mp hn
    have hsecond : n ∉ Ico (k * (p + h)) ((k + 1) * p) := by
      simp only [mem_Ico]
      omega
    simp only [compensatedPronicGapCell, if_neg hsecond]
    split_ifs <;> linarith
  · let C := (k + 1) * p
    let U := max T C
    let f (n : ℕ) := compensatedPronicGapCell p h k n /
      ((n : ℝ) * ((n : ℝ) + 1))
    have htotal : ∑ n ∈ range U, f n = 0 := by
      rw [sum_range_cutoff f U C (fun n hn => by simp [f, cell_zero_after hkh hn])]
      rw [min_eq_right (le_max_right T C)]
      exact cell_mean_zero hp hk hkh
    have ht := sum_range_add_sum_Ico f (le_max_left T C)
    have htail : 0 ≤ ∑ n ∈ Ico T U, f n := by
      apply sum_nonneg
      intro n hn
      have hnT := (mem_Ico.mp hn).1
      have hfirst : n ∉ Ico (k * p) (k * (p + h)) := by
        simp only [mem_Ico]
        omega
      unfold f
      apply div_nonneg _ (by positivity)
      simp only [compensatedPronicGapCell, if_neg hfirst]
      split_ifs <;> positivity
    rw [htotal] at ht
    linarith

private theorem cell_covariance_nonpos {p h r l k : ℕ}
    (hr : 0 < r) (hk : 0 < k)
    (hkh : k * h ≤ p) (hkl : k * l ≤ r) (horder : p + h ≤ r) (T : ℕ) :
    (∑ n ∈ range T, compensatedPronicGapCell p h k n *
      compensatedPronicGapCell r l k n / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 0 := by
  have hboundary : k * (p + h) ≤ k * r := Nat.mul_le_mul_left k horder
  have hvalue (n : ℕ) :
      compensatedPronicGapCell p h k n * compensatedPronicGapCell r l k n =
        (((k : ℝ) + 1) * h) *
          (if n < (k + 1) * p then compensatedPronicGapCell r l k n else 0) := by
    by_cases hn : n < k * r
    · rw [cell_zero_before hn]
      split_ifs <;> ring
    · by_cases hc : n < (k + 1) * p
      · have hnfirst : n ∉ Ico (k * p) (k * (p + h)) := by
          simp only [mem_Ico]
          omega
        have hnsecond : n ∈ Ico (k * (p + h)) ((k + 1) * p) := by
          simp only [mem_Ico]
          omega
        rw [compensatedPronicGapCell, if_neg hnfirst, if_pos hnsecond, if_pos hc]
      · rw [cell_zero_after hkh (not_lt.mp hc), if_neg hc]
        ring
  have hcut :
      (∑ n ∈ range T, if n < (k + 1) * p then
        compensatedPronicGapCell r l k n / ((n : ℝ) * ((n : ℝ) + 1)) else 0) =
      ∑ n ∈ range (min T ((k + 1) * p)),
        compensatedPronicGapCell r l k n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_range]
    omega
  calc
    _ = (((k : ℝ) + 1) * h) *
        ∑ n ∈ range T, if n < (k + 1) * p then
          compensatedPronicGapCell r l k n / ((n : ℝ) * ((n : ℝ) + 1)) else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      rw [hvalue]
      split_ifs <;> ring
    _ ≤ 0 := by
      rw [hcut]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (cell_prefix_mean_nonpos hr hk hkl _)

private theorem cell_energy_le {p h k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hkh : k * h ≤ p) (T : ℕ) :
    (∑ n ∈ range T, (compensatedPronicGapCell p h k n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) ≤ (h : ℝ) / k - (h : ℝ) ^ 2 / p := by
  rw [sum_range_cutoff _ T ((k + 1) * p) (fun n hn => by
    rw [cell_zero_after hkh hn]; simp)]
  calc
    _ ≤ ∑ n ∈ range ((k + 1) * p), (compensatedPronicGapCell p h k n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right _ _))
      intro n _ _
      positivity
    _ = _ := cell_energy_exact hp hk hkh

private theorem nonnegative_family_energy_le (m T : ℕ) (f : ℕ → ℕ → ℝ)
    (B a : ℕ → ℝ)
    (ha : ∀ i ∈ range m, 0 ≤ a i)
    (hcov : ∀ i ∈ range m, ∀ j ∈ range m, i ≠ j →
      (∑ n ∈ range T, f i n * f j n / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 0)
    (hdiag : ∀ i ∈ range m,
      (∑ n ∈ range T, (f i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ B i) :
    (∑ n ∈ range T, (∑ i ∈ range m, a i * f i n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) ≤ ∑ i ∈ range m, (a i) ^ 2 * B i := by
  have hexpand :
      (∑ n ∈ range T, (∑ i ∈ range m, a i * f i n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ i ∈ range m, ∑ j ∈ range m, a i * a j *
        (∑ n ∈ range T, f i n * f j n / ((n : ℝ) * ((n : ℝ) + 1))) := by
    calc
      _ = ∑ n ∈ range T, ∑ i ∈ range m, ∑ j ∈ range m,
          a i * a j * (f i n * f j n / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n _
        rw [sq, sum_mul_sum]
        simp only [sum_div]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
        apply sum_congr rfl
        intro j _
        rw [mul_sum]
  rw [hexpand]
  apply sum_le_sum
  intro i hi
  calc
    _ ≤ ∑ j ∈ range m, if j = i then (a i) ^ 2 * B i else 0 := by
      apply sum_le_sum
      intro j hj
      by_cases hij : j = i
      · subst j
        have h := mul_le_mul_of_nonneg_left (hdiag i hi) (sq_nonneg (a i))
        simpa [sq] using h
      · rw [if_neg hij]
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (ha i hi) (ha j hj))
          (hcov i hi j hj (fun he => hij he.symm))
    _ = _ := by simp [hi]

private theorem signed_family_energy_le (m T : ℕ) (f : ℕ → ℕ → ℝ)
    (B a : ℕ → ℝ)
    (hcov : ∀ i ∈ range m, ∀ j ∈ range m, i ≠ j →
      (∑ n ∈ range T, f i n * f j n / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 0)
    (hdiag : ∀ i ∈ range m,
      (∑ n ∈ range T, (f i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ B i) :
    (∑ n ∈ range T, (∑ i ∈ range m, a i * f i n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) ≤ 2 * ∑ i ∈ range m, (a i) ^ 2 * B i := by
  let ap (i : ℕ) := if 0 ≤ a i then a i else 0
  let am (i : ℕ) := if 0 ≤ a i then 0 else -a i
  have hap (i : ℕ) : 0 ≤ ap i := by unfold ap; split_ifs <;> linarith
  have ham (i : ℕ) : 0 ≤ am i := by unfold am; split_ifs <;> linarith
  have hp := nonnegative_family_energy_le m T f B ap (fun i _ => hap i) hcov hdiag
  have hn := nonnegative_family_energy_le m T f B am (fun i _ => ham i) hcov hdiag
  have hsplit (n : ℕ) : (∑ i ∈ range m, a i * f i n) =
      (∑ i ∈ range m, ap i * f i n) - ∑ i ∈ range m, am i * f i n := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    unfold ap am
    split_ifs <;> ring
  have hpoint (n : ℕ) : (∑ i ∈ range m, a i * f i n) ^ 2 ≤
      2 * (∑ i ∈ range m, ap i * f i n) ^ 2 +
      2 * (∑ i ∈ range m, am i * f i n) ^ 2 := by
    rw [hsplit]
    nlinarith [sq_nonneg ((∑ i ∈ range m, ap i * f i n) + ∑ i ∈ range m, am i * f i n)]
  have he : (∑ n ∈ range T, (∑ i ∈ range m, a i * f i n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * (∑ n ∈ range T, (∑ i ∈ range m, ap i * f i n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) +
      2 * (∑ n ∈ range T, (∑ i ∈ range m, am i * f i n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) := by
    calc
      _ ≤ ∑ n ∈ range T,
          (2 * (∑ i ∈ range m, ap i * f i n) ^ 2 +
            2 * (∑ i ∈ range m, am i * f i n) ^ 2) /
              ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n _
        exact div_le_div_of_nonneg_right (hpoint n) (by positivity)
      _ = _ := by
        simp_rw [add_div, mul_div_assoc]
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hright : 2 * (∑ i ∈ range m, (ap i) ^ 2 * B i) +
      2 * (∑ i ∈ range m, (am i) ^ 2 * B i) =
      2 * ∑ i ∈ range m, (a i) ^ 2 * B i := by
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    unfold ap am
    split_ifs <;> ring
  calc
    _ ≤ 2 * (∑ i ∈ range m, (ap i) ^ 2 * B i) +
        2 * (∑ i ∈ range m, (am i) ^ 2 * B i) := by linarith
    _ = _ := hright

private theorem cell_mod_cast {p n k : ℕ} (hl : k * p ≤ n) (hu : n < (k + 1) * p) :
    ((n % p : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) * p := by
  have hd : n / p = k := Nat.div_eq_of_lt_le hl hu
  have he := Nat.mod_add_div n p
  rw [hd] at he
  have heR : ((n % p : ℕ) : ℝ) + (p : ℝ) * k = n := by exact_mod_cast he
  nlinarith

private theorem cell_eq_residue {p h k : ℕ} (hk : 0 < k)
    (hkh : k * h ≤ p) (n : ℕ) :
    compensatedPronicGapCell p h k n =
      if n ∈ Ico (k * p) ((k + 1) * p) then
        ((n % p : ℕ) : ℝ) - ((n % (p + h) : ℕ) : ℝ) + h else 0 := by
  have hab : k * p ≤ k * (p + h) := by nlinarith
  have hbc : k * (p + h) ≤ (k + 1) * p := by nlinarith
  by_cases hn : n ∈ Ico (k * p) ((k + 1) * p)
  · rw [if_pos hn]
    have hnl := (mem_Ico.mp hn).1
    have hnu := (mem_Ico.mp hn).2
    by_cases hnb : n < k * (p + h)
    · have hnfirst : n ∈ Ico (k * p) (k * (p + h)) := mem_Ico.mpr ⟨hnl, hnb⟩
      rw [compensatedPronicGapCell, if_pos hnfirst]
      have hpred : (k - 1) * (p + h) ≤ n := by
        have he : k - 1 + 1 = k := by omega
        nlinarith
      have hpredU : n < (k - 1 + 1) * (p + h) := by
        simpa only [Nat.sub_add_cancel hk] using hnb
      rw [cell_mod_cast hnl hnu, cell_mod_cast hpred hpredU]
      have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk, Nat.cast_one]
      rw [hkm]
      push_cast
      ring
    · have hnfirst : n ∉ Ico (k * p) (k * (p + h)) := by simp only [mem_Ico]; omega
      have hnsecond : n ∈ Ico (k * (p + h)) ((k + 1) * p) := by
        simp only [mem_Ico]
        omega
      rw [compensatedPronicGapCell, if_neg hnfirst, if_pos hnsecond]
      have hqlo : k * (p + h) ≤ n := by omega
      have hqhi : n < (k + 1) * (p + h) := by nlinarith
      rw [cell_mod_cast hnl hnu, cell_mod_cast hqlo hqhi]
      push_cast
      ring
  · rw [if_neg hn]
    by_cases hlow : n < k * p
    · exact cell_zero_before hlow
    · apply cell_zero_after hkh
      simp only [mem_Ico] at hn
      omega

/-- The quotient-cell step formula equals the literal compensated residue difference. -/
theorem compensatedPronicGapCell_eq_residue (k : ℕ+) (h r n : ℕ) :
    let p := (k : ℕ) * h + r + 1
    compensatedPronicGapCell p h k n =
      if n ∈ Ico ((k : ℕ) * p) (((k : ℕ) + 1) * p) then
        ((n % p : ℕ) : ℝ) - ((n % (p + h) : ℕ) : ℝ) + h else 0 := by
  dsimp only
  exact cell_eq_residue k.pos (by omega) n

/-- Each compensated quotient cell has zero pronic mean and an exact gap-sized variance. -/
theorem compensatedPronicGapCell_moments (k : ℕ+) (h r : ℕ) :
    let p := (k : ℕ) * h + r + 1
    (∑ n ∈ range (((k : ℕ) + 1) * p),
      compensatedPronicGapCell p h k n / ((n : ℝ) * ((n : ℝ) + 1))) = 0 ∧
    (∑ n ∈ range (((k : ℕ) + 1) * p),
      (compensatedPronicGapCell p h k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
        (h : ℝ) / k - (h : ℝ) ^ 2 / p := by
  dsimp only
  exact ⟨cell_mean_zero (by positivity) k.pos (by omega),
    cell_energy_exact (by positivity) k.pos (by omega)⟩

/-- Ordered modulus gaps inside a common pre-overlap cluster, constructed from their lengths. -/
def pronicGapChainLower (K m offset : ℕ) (h : ℕ → ℕ) (i : ℕ) : ℕ :=
  K * (∑ j ∈ range m, h j) + offset + 1 + ∑ j ∈ range i, h j

private theorem chain_lower_pos (K : ℕ+) (m offset : ℕ) (h : ℕ → ℕ) (i : ℕ) :
    0 < pronicGapChainLower K m offset h i := by
  unfold pronicGapChainLower
  positivity

private theorem chain_gap_admissible (K : ℕ+) (m offset : ℕ) (h : ℕ → ℕ)
    {i k : ℕ} (hi : i ∈ range m) (hk : k ≤ (K : ℕ)) :
    k * h i ≤ pronicGapChainLower K m offset h i := by
  have hs : h i ≤ ∑ j ∈ range m, h j := single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hs1 := Nat.mul_le_mul_left k hs
  have hs2 := Nat.mul_le_mul_right (∑ j ∈ range m, h j) hk
  unfold pronicGapChainLower
  omega

private theorem chain_gap_ordered (K m offset : ℕ) (h : ℕ → ℕ)
    {i j : ℕ} (hij : i < j) :
    pronicGapChainLower K m offset h i + h i ≤ pronicGapChainLower K m offset h j := by
  have hs : (∑ t ∈ range (i + 1), h t) ≤ ∑ t ∈ range j, h t :=
    sum_le_sum_of_subset (range_mono hij)
  rw [Finset.sum_range_succ] at hs
  unfold pronicGapChainLower
  omega

private theorem chain_level_energy_le (K : ℕ+) (m offset T : ℕ) (h : ℕ → ℕ)
    (a : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (hkK : k ≤ (K : ℕ)) :
    (∑ n ∈ range T,
      (∑ i ∈ range m, a i *
        compensatedPronicGapCell (pronicGapChainLower K m offset h i) (h i) k n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * ∑ i ∈ range m, (a i) ^ 2 *
        ((h i : ℝ) / k - (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i) := by
  apply signed_family_energy_le
  · intro i hi j hj hij
    rcases lt_trichotomy i j with ho | ho | ho
    · exact cell_covariance_nonpos (chain_lower_pos K m offset h j) hk (chain_gap_admissible K m offset h hi hkK)
        (chain_gap_admissible K m offset h hj hkK) (chain_gap_ordered K m offset h ho) T
    · exact False.elim (hij ho)
    · have hh := cell_covariance_nonpos (chain_lower_pos K m offset h i) hk (chain_gap_admissible K m offset h hj hkK)
        (chain_gap_admissible K m offset h hi hkK) (chain_gap_ordered K m offset h ho) T
      simpa only [mul_comm] using hh
  · intro i hi
    exact cell_energy_le (chain_lower_pos K m offset h i) hk
      (chain_gap_admissible K m offset h hi hkK) T

/-- At every quotient level, a signed ordered gap chain has no number-of-gaps loss. -/
theorem compensatedPronicGapChain_level_energy_le (K : ℕ+) (m offset T : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) (k : Fin (K : ℕ)) :
    (∑ n ∈ range T,
      (∑ i ∈ range m, a i *
        compensatedPronicGapCell (pronicGapChainLower K m offset h i) (h i) (k + 1) n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * ∑ i ∈ range m, (a i) ^ 2 *
        ((h i : ℝ) / ((k : ℝ) + 1) -
          (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i) := by
  have hk : (k : ℕ) + 1 ≤ (K : ℕ) := k.isLt
  simpa only [Nat.cast_add, Nat.cast_one] using
    chain_level_energy_le K m offset T h a (by omega : 0 < (k : ℕ) + 1) hk

private theorem separated_levels_energy_le (K T : ℕ) (g : ℕ → ℕ → ℝ)
    (hsep : ∀ i ∈ range K, ∀ j ∈ range K, i + 2 ≤ j → ∀ n, g i n * g j n = 0) :
    (∑ n ∈ range T, (∑ i ∈ range K, g i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * ∑ i ∈ range K, ∑ n ∈ range T, (g i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  let f (t i n : ℕ) := if i % 2 = t then g i n else 0
  have horth (t : ℕ) : ∀ i ∈ range K, ∀ j ∈ range K, i ≠ j →
      (∑ n ∈ range T, f t i n * f t j n / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 0 := by
    intro i hi j hj hij
    have hz : (∑ n ∈ range T, f t i n * f t j n /
        ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
      apply sum_eq_zero
      intro n _
      by_cases hit : i % 2 = t
      · by_cases hjt : j % 2 = t
        · have hh : i + 2 ≤ j ∨ j + 2 ≤ i := by omega
          rcases hh with hh | hh
          · simp only [f, if_pos hit, if_pos hjt, hsep i hi j hj hh n, zero_div]
          · have he : g i n * g j n = 0 := by
              simpa only [mul_comm] using hsep j hj i hi hh n
            simp only [f, if_pos hit, if_pos hjt, he, zero_div]
        · simp only [f, if_pos hit, if_neg hjt, mul_zero, zero_div]
      · simp only [f, if_neg hit, zero_mul, zero_div]
    exact hz.le
  have he (t : ℕ) :
      (∑ n ∈ range T, (∑ i ∈ range K, f t i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ∑ i ∈ range K, ∑ n ∈ range T, (f t i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    simpa only [one_mul, one_pow] using nonnegative_family_energy_le K T (f t)
      (fun i => ∑ n ∈ range T, (f t i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
      (fun _ => 1) (fun _ _ => zero_le_one) (horth t) (fun _ _ => le_rfl)
  have hsplit (i n : ℕ) : g i n = f 0 i n + f 1 i n := by
    by_cases hi : i % 2 = 0
    · have hi1 : i % 2 ≠ 1 := by omega
      simp only [f, if_pos hi, if_neg hi1, add_zero]
    · have hi1 : i % 2 = 1 := by omega
      simp only [f, if_neg hi, if_pos hi1, zero_add]
  have hsum (n : ℕ) : (∑ i ∈ range K, g i n) =
      (∑ i ∈ range K, f 0 i n) + ∑ i ∈ range K, f 1 i n := by
    simp_rw [hsplit]
    rw [sum_add_distrib]
  have hpoint (n : ℕ) : (∑ i ∈ range K, g i n) ^ 2 ≤
      2 * (∑ i ∈ range K, f 0 i n) ^ 2 + 2 * (∑ i ∈ range K, f 1 i n) ^ 2 := by
    rw [hsum]
    nlinarith [sq_nonneg ((∑ i ∈ range K, f 0 i n) - ∑ i ∈ range K, f 1 i n)]
  have htriangle :
      (∑ n ∈ range T, (∑ i ∈ range K, g i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * (∑ n ∈ range T, (∑ i ∈ range K, f 0 i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
      2 * (∑ n ∈ range T, (∑ i ∈ range K, f 1 i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    calc
      _ ≤ ∑ n ∈ range T,
          (2 * (∑ i ∈ range K, f 0 i n) ^ 2 + 2 * (∑ i ∈ range K, f 1 i n) ^ 2) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n _
        exact div_le_div_of_nonneg_right (hpoint n) (by positivity)
      _ = _ := by
        simp_rw [add_div, mul_div_assoc]
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hdiag :
      (∑ i ∈ range K, ∑ n ∈ range T, (f 0 i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
      (∑ i ∈ range K, ∑ n ∈ range T, (f 1 i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ i ∈ range K, ∑ n ∈ range T, (g i n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hi : i % 2 = 0
    · have hi1 : i % 2 ≠ 1 := by omega
      simp only [f, if_pos hi, if_neg hi1]
      ring
    · have hi1 : i % 2 = 1 := by omega
      simp only [f, if_neg hi, if_pos hi1]
      ring
  have he0 := he 0
  have he1 := he 1
  linarith

private theorem chain_bounds (K m offset : ℕ) (h : ℕ → ℕ) {i : ℕ} (hi : i ∈ range m) :
    pronicGapChainLower K m offset h 0 ≤ pronicGapChainLower K m offset h i ∧
    pronicGapChainLower K m offset h i ≤
      pronicGapChainLower K m offset h 0 + ∑ j ∈ range m, h j := by
  have hs : (∑ j ∈ range i, h j) ≤ ∑ j ∈ range m, h j :=
    sum_le_sum_of_subset (range_mono (mem_range.mp hi).le)
  unfold pronicGapChainLower
  simp only [sum_range_zero, add_zero]
  omega

private theorem chain_levels_separated (K : ℕ+) (m offset : ℕ) (h : ℕ → ℕ) (a : ℕ → ℝ)
    {i j : ℕ} (hi : i ∈ range (K : ℕ)) (hj : j ∈ range (K : ℕ)) (hij : i + 2 ≤ j) (n : ℕ) :
    (∑ t ∈ range m, a t * compensatedPronicGapCell (pronicGapChainLower K m offset h t) (h t) (i + 1) n) *
    (∑ t ∈ range m, a t * compensatedPronicGapCell (pronicGapChainLower K m offset h t) (h t) (j + 1) n) = 0 := by
  let P := pronicGapChainLower K m offset h 0
  let H := ∑ t ∈ range m, h t
  have hKH : (K : ℕ) * H ≤ P := by
    simp only [P, H, pronicGapChainLower, sum_range_zero, add_zero]
    omega
  have hiK : i + 1 ≤ (K : ℕ) := mem_range.mp hi
  have hjK : j + 1 ≤ (K : ℕ) := mem_range.mp hj
  have hlevel : (i + 2) * H ≤ P :=
    (Nat.mul_le_mul_right H (by omega : i + 2 ≤ (K : ℕ))).trans hKH
  have hboundary : (i + 2) * (P + H) ≤ (j + 1) * P := by nlinarith
  by_cases hn : n < (j + 1) * P
  · have hz : (∑ t ∈ range m,
        a t * compensatedPronicGapCell (pronicGapChainLower K m offset h t) (h t) (j + 1) n) = 0 := by
      apply sum_eq_zero
      intro t ht
      have hlo := (chain_bounds K m offset h ht).1
      have hnp : n < (j + 1) * pronicGapChainLower K m offset h t :=
        hn.trans_le (Nat.mul_le_mul_left (j + 1) hlo)
      rw [cell_zero_before hnp, mul_zero]
    rw [hz, mul_zero]
  · have hz : (∑ t ∈ range m,
        a t * compensatedPronicGapCell (pronicGapChainLower K m offset h t) (h t) (i + 1) n) = 0 := by
      apply sum_eq_zero
      intro t ht
      have hhi := (chain_bounds K m offset h ht).2
      change pronicGapChainLower K m offset h t ≤ P + H at hhi
      have hnp : (i + 1 + 1) * pronicGapChainLower K m offset h t ≤ n := by
        calc
          _ = (i + 2) * pronicGapChainLower K m offset h t := by congr 1
          _ ≤ (i + 2) * (P + H) := Nat.mul_le_mul_left (i + 2) hhi
          _ ≤ (j + 1) * P := hboundary
          _ ≤ n := not_lt.mp hn
      rw [cell_zero_after (chain_gap_admissible K m offset h ht hiK) hnp, mul_zero]
    rw [hz, zero_mul]

private theorem sum_inverse_succ (K : ℕ) :
    (∑ k ∈ range K, 1 / ((k : ℝ) + 1)) = (harmonic K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ]
    push_cast
    ring

private theorem sum_gap_level_budget (K : ℕ) (h p : ℝ) :
    (∑ k ∈ range K, (h / ((k : ℝ) + 1) - h ^ 2 / p)) =
      h * (harmonic K : ℝ) - (K : ℝ) * h ^ 2 / p := by
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hs : (∑ k ∈ range K, h / ((k : ℝ) + 1)) = h * (harmonic K : ℝ) := by
    simp_rw [div_eq_mul_inv]
    rw [← mul_sum]
    congr 1
    simpa only [one_div] using sum_inverse_succ K
  rw [hs]
  ring

/-- Across all pre-overlap quotient levels, signed chains retain a uniform collective bound. -/
theorem compensatedPronicGapChain_energy_le (K : ℕ+) (m offset T : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ range T,
      (∑ k ∈ range (K : ℕ), ∑ i ∈ range m, a i *
        compensatedPronicGapCell (pronicGapChainLower K m offset h i) (h i) (k + 1) n) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) ≤
      4 * ∑ i ∈ range m, (a i) ^ 2 *
        ((h i : ℝ) * (harmonic (K : ℕ) : ℝ) -
          (K : ℝ) * (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i) := by
  let g (k n : ℕ) := ∑ i ∈ range m, a i *
    compensatedPronicGapCell (pronicGapChainLower K m offset h i) (h i) (k + 1) n
  let B (k i : ℕ) := (a i) ^ 2 * ((h i : ℝ) / ((k : ℝ) + 1) -
    (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i)
  have hs := separated_levels_energy_le (K : ℕ) T g
    (fun i hi j hj hij n => chain_levels_separated K m offset h a hi hj hij n)
  have hlevels : (∑ k ∈ range (K : ℕ), ∑ n ∈ range T,
      (g k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ∑ k ∈ range (K : ℕ), 2 * ∑ i ∈ range m, B k i := by
    apply sum_le_sum
    intro k hk
    simpa only [g, B, Nat.cast_add, Nat.cast_one] using
      chain_level_energy_le K m offset T h a (by omega : 0 < k + 1) (mem_range.mp hk)
  have htotal : (∑ k ∈ range (K : ℕ), ∑ i ∈ range m, B k i) =
      ∑ i ∈ range m, (a i) ^ 2 * ((h i : ℝ) * (harmonic (K : ℕ) : ℝ) -
        (K : ℝ) * (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    unfold B
    rw [← mul_sum, sum_gap_level_budget]
  have hfactor : (∑ k ∈ range (K : ℕ), 2 * ∑ i ∈ range m, B k i) =
      2 * ∑ k ∈ range (K : ℕ), ∑ i ∈ range m, B k i := by rw [mul_sum]
  calc
    _ ≤ 2 * ∑ k ∈ range (K : ℕ), ∑ n ∈ range T,
        (g k n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := hs
    _ ≤ 2 * (∑ k ∈ range (K : ℕ), 2 * ∑ i ∈ range m, B k i) :=
      mul_le_mul_of_nonneg_left hlevels (by positivity)
    _ = _ := by rw [hfactor, htotal]; ring

private theorem sum_cells_eq_residue {p h K n : ℕ} (hp : 0 < p)
    (hKh : K * h ≤ p) (hn : n < (K + 1) * p) :
    (∑ k ∈ range K, compensatedPronicGapCell p h (k + 1) n) =
      ((n % p : ℕ) : ℝ) - ((n % (p + h) : ℕ) : ℝ) +
        (if p ≤ n then (h : ℝ) else 0) := by
  by_cases hlow : n < p
  · have hz : (∑ k ∈ range K, compensatedPronicGapCell p h (k + 1) n) = 0 := by
      apply sum_eq_zero
      intro k _
      apply cell_zero_before
      nlinarith
    rw [hz, Nat.mod_eq_of_lt hlow, Nat.mod_eq_of_lt (show n < p + h by omega),
      if_neg (by omega : ¬ p ≤ n)]
    ring
  · let d := n / p
    have hdlo : d * p ≤ n := Nat.div_mul_le_self n p
    have hdhi : n < (d + 1) * p := by
      simpa only [d, Nat.mul_comm] using Nat.lt_mul_div_succ n hp
    have hdpos : 0 < d := by nlinarith
    have hdK : d ≤ K := by
      by_contra hh
      have : K + 1 ≤ d := by omega
      nlinarith
    have hidx : d - 1 ∈ range K := by simp only [mem_range]; omega
    rw [Finset.sum_eq_single (d - 1)]
    · have he : d - 1 + 1 = d := by omega
      rw [he, cell_eq_residue hdpos ((Nat.mul_le_mul_right h hdK).trans hKh) n,
        if_pos (mem_Ico.mpr ⟨hdlo, hdhi⟩), if_pos (by omega : p ≤ n)]
    · intro j hj hji
      have hjK : j + 1 ≤ K := mem_range.mp hj
      by_cases hjlow : n < (j + 1) * p
      · exact cell_zero_before hjlow
      · have hjhigh : (j + 1 + 1) * p ≤ n := by
          by_contra hh
          have hdiv : n / p = j + 1 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          dsimp only [d] at hji
          omega
        exact cell_zero_after ((Nat.mul_le_mul_right h hjK).trans hKh) hjhigh
    · intro hnot
      exact False.elim (hnot hidx)

private theorem weighted_gap_cauchy (m : ℕ) (a : ℕ → ℝ) (h : ℕ → ℕ) :
    (∑ i ∈ range m, a i * (h i : ℝ)) ^ 2 ≤
      (∑ i ∈ range m, (h i : ℝ)) * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  have hs (i : ℕ) : (Real.sqrt (h i : ℝ)) ^ 2 = (h i : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have he (i : ℕ) : Real.sqrt (h i : ℝ) * (a i * Real.sqrt (h i : ℝ)) = a i * (h i : ℝ) := by
    calc
      _ = a i * (Real.sqrt (h i : ℝ)) ^ 2 := by ring
      _ = _ := by rw [hs]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (range m)
    (fun i => Real.sqrt (h i : ℝ)) (fun i => a i * Real.sqrt (h i : ℝ))
  simpa only [he, mul_pow, hs] using hc

private theorem birth_packet_sq_le (m n : ℕ) (p h : ℕ → ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ range m, if p i ≤ n then a i * (h i : ℝ) else 0) ^ 2 ≤
      ((∑ i ∈ range m, h i : ℕ) : ℝ) * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let b (i : ℕ) := if p i ≤ n then a i else 0
  have he : (∑ i ∈ range m, if p i ≤ n then a i * (h i : ℝ) else 0) =
      ∑ i ∈ range m, b i * (h i : ℝ) := by
    apply sum_congr rfl
    intro i _
    unfold b
    split_ifs <;> ring
  rw [he]
  have hb : (∑ i ∈ range m, (b i) ^ 2 * (h i : ℝ)) ≤
      ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
    apply sum_le_sum
    intro i _
    unfold b
    split_ifs
    · exact le_rfl
    · simp only [zero_pow (by omega : 2 ≠ 0), zero_mul]
      positivity
  have hc := (weighted_gap_cauchy m b h).trans
    (mul_le_mul_of_nonneg_left hb (sum_nonneg fun _ _ => Nat.cast_nonneg _))
  simpa only [Nat.cast_sum] using hc

private theorem birth_packet_energy_le (m T P : ℕ) (p h : ℕ → ℕ) (a : ℕ → ℝ)
    (hP : 0 < P) (hbase : ∀ i ∈ range m, P ≤ p i) :
    (∑ n ∈ range T, (∑ i ∈ range m, if p i ≤ n then a i * (h i : ℝ) else 0) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ((∑ i ∈ range m, h i : ℕ) : ℝ) / P * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let B (n : ℕ) := ∑ i ∈ range m, if p i ≤ n then a i * (h i : ℝ) else 0
  let A := ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)
  let H := ∑ i ∈ range m, h i
  have hA : 0 ≤ A := sum_nonneg fun _ _ => by positivity
  have hzero (n : ℕ) (hn : n < P) : B n = 0 := by
    apply sum_eq_zero
    intro i hi
    have hpi := hbase i hi
    rw [if_neg (by omega : ¬ p i ≤ n)]
  change (∑ n ∈ range T, (B n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ (H : ℝ) / P * A
  by_cases hT : T < P
  · have hz : (∑ n ∈ range T, (B n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [hzero n (lt_trans (mem_range.mp hn) hT)]
      simp
    rw [hz]
    positivity
  · have hPT : P ≤ T := by omega
    have hz : (∑ n ∈ range P, (B n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [hzero n (mem_range.mp hn)]
      simp
    rw [← sum_range_add_sum_Ico (fun n => (B n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) hPT,
      hz, zero_add]
    calc
      _ ≤ ∑ n ∈ Ico P T, ((H : ℝ) * A) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_le_sum
        intro n _
        simpa only [B, A, H, mul_one_div] using
          div_le_div_of_nonneg_right (birth_packet_sq_le m n p h a) (by positivity)
      _ = ((H : ℝ) * A) * (1 / (P : ℝ) - 1 / T) := by
        rw [← mul_sum, cell_pronic_interval hP hPT]
      _ ≤ ((H : ℝ) * A) * (1 / (P : ℝ)) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = _ := by ring

/-- Literal signed residue differences have a collective prefix bound with explicit birth cost. -/
theorem pronicResidueGapChain_prefix_energy_le (K : ℕ+) (m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    let T := ((K : ℕ) + 1) * P
    (∑ n ∈ range T,
      (∑ i ∈ range m, a i *
        (((n % pronicGapChainLower K m offset h i : ℕ) : ℝ) -
          ((n % (pronicGapChainLower K m offset h i + h i) : ℕ) : ℝ))) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) ≤
      8 * ∑ i ∈ range m, (a i) ^ 2 *
        ((h i : ℝ) * (harmonic (K : ℕ) : ℝ) -
          (K : ℝ) * (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i) +
      2 * (((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
        ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  let P := p 0
  let T := ((K : ℕ) + 1) * P
  let F (n : ℕ) := ∑ i ∈ range m, a i *
    (((n % p i : ℕ) : ℝ) - ((n % (p i + h i) : ℕ) : ℝ))
  let W (n : ℕ) := ∑ k ∈ range (K : ℕ), ∑ i ∈ range m,
    a i * compensatedPronicGapCell (p i) (h i) (k + 1) n
  let D (n : ℕ) := ∑ i ∈ range m, if p i ≤ n then a i * (h i : ℝ) else 0
  have hsplit (n : ℕ) (hn : n ∈ range T) : W n = F n + D n := by
    have hnT : n < ((K : ℕ) + 1) * P := mem_range.mp hn
    unfold W F D
    rw [sum_comm, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← mul_sum]
    have hlo := (chain_bounds K m offset h hi).1
    have hnp : n < ((K : ℕ) + 1) * p i :=
      hnT.trans_le (Nat.mul_le_mul_left ((K : ℕ) + 1) hlo)
    rw [sum_cells_eq_residue (chain_lower_pos K m offset h i)
      (chain_gap_admissible K m offset h hi le_rfl) hnp]
    split_ifs <;> ring
  have hpoint (n : ℕ) (hn : n ∈ range T) : (F n) ^ 2 ≤ 2 * (W n) ^ 2 + 2 * (D n) ^ 2 := by
    have he : F n = W n - D n := by linarith [hsplit n hn]
    rw [he]
    nlinarith [sq_nonneg (W n + D n)]
  have htriangle : (∑ n ∈ range T, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * (∑ n ∈ range T, (W n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
      2 * (∑ n ∈ range T, (D n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    calc
      _ ≤ ∑ n ∈ range T, (2 * (W n) ^ 2 + 2 * (D n) ^ 2) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n hn
        exact div_le_div_of_nonneg_right (hpoint n hn) (by positivity)
      _ = _ := by
        simp_rw [add_div, mul_div_assoc]
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hW := compensatedPronicGapChain_energy_le K m offset T h a
  have hD := birth_packet_energy_le m T P p h a (chain_lower_pos K m offset h 0)
    (fun i hi => (chain_bounds K m offset h hi).1)
  change (∑ n ∈ range T, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _
  change (∑ n ∈ range T, (W n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _ at hW
  change (∑ n ∈ range T, (D n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _ at hD
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
