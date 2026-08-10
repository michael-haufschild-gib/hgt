import GaloisForLFunctions.RHTower.Sieve.PrimeWindowSharpLevel

/-!
# The sharp prime window count at an arbitrary scale

`logNeighbourCount_le_sharp` is the unit scale `δ = 1`.  The almost-diagonal mean value theorem uses
the scale `δ = 1/T` forced by the height, so the count is needed for every `δ ∈ (0,1]`.  At the
level `z = (qδ)^{1/4}` the same argument gives

```text
#{p : |log p − log q| < δ} ≤ 700·(qδ)/log(qδ) + 1        whenever  e⁴ ≤ qδ ,
```

the window length `≍ qδ` divided by its own logarithm.  The threshold `qδ ≥ e⁴` is exactly the
condition under which Brun–Titchmarsh's error `6z(1+log z)³` stays below its main term; below it the
window carries `O(1)` primes anyway.

Feeding this into the almost-diagonal mean value theorem gives the mean square in affine form with
the *sharp* near-diagonal mass:

```text
∫ ‖P‖² ≤ (5·700/4)·∑_q (q/log(qδ))·‖a_q‖²  +  (5/(4δ))·∑_q ‖a_q‖² .
```
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- `e^δ − e^{−δ} ≤ 4δ` on the unit interval. -/
theorem exp_sub_exp_neg_le_four_mul {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.exp δ - Real.exp (-δ) ≤ 4 * δ := by
  have hlow : 1 - δ ≤ Real.exp (-δ) := by
    linarith [Real.add_one_le_exp (-δ)]
  have hpos : (0 : ℝ) < Real.exp δ := Real.exp_pos _
  have hprod : (1 - δ) * Real.exp δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hlow hpos.le
    rw [← Real.exp_add] at h
    simpa using h
  have hup : Real.exp δ ≤ 1 + δ * Real.exp δ := by nlinarith [hprod]
  have hδe : Real.exp δ ≤ Real.exp 1 := Real.exp_le_exp.mpr hδ1
  have he : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  nlinarith [hup, hlow, hδe, he, hδ0.le]

/-- **The sharp prime window count at an arbitrary scale.** -/
theorem logNeighbourCount_le_sharp_delta (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime) {q : ℕ}
    (hq : 2 ≤ q) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hbig : 4 ≤ Real.log ((q : ℝ) * δ)) :
    (logNeighbourCount s δ q : ℝ) ≤ 700 * (((q : ℝ) * δ) / Real.log ((q : ℝ) * δ)) + 1 := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  set L : ℝ := (q : ℝ) * δ with hLdef
  have hL0 : (0 : ℝ) < L := by rw [hLdef]; positivity
  have hu4 : (4 : ℝ) ≤ Real.log L := hbig
  have hLexp : Real.exp (Real.log L) = L := Real.exp_log hL0
  have hL1 : (1 : ℝ) ≤ L := by
    have h1 : Real.exp 0 ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr (by linarith)
    rw [hLexp] at h1
    simpa using h1
  -- the level
  have hlogz : Real.log (Real.sqrt (Real.sqrt L)) = Real.log L / 4 := log_sqrt_sqrt hL0.le
  have hzval : Real.sqrt (Real.sqrt L) = Real.exp (Real.log L / 4) := sqrt_sqrt_eq_exp hL0
  have hz1 : 1 < Real.sqrt (Real.sqrt L) := by
    rw [hzval]
    linarith [Real.add_one_le_exp (Real.log L / 4)]
  have hbt := logNeighbourCount_le_bt s hs hδ0.le hq1 hz1
  rw [hlogz, hzval] at hbt
  -- the error term
  have hpoly := poly_le_exp_three_quarters hu4
  have hmerge : Real.exp (3 * Real.log L / 4) * Real.exp (Real.log L / 4) = L := by
    rw [← Real.exp_add, show 3 * Real.log L / 4 + Real.log L / 4 = Real.log L by ring, hLexp]
  have h4pos : (0 : ℝ) < Real.exp (Real.log L / 4) := Real.exp_pos _
  have hlogL0 : (0 : ℝ) < Real.log L := by linarith
  have herr : 6 * Real.exp (Real.log L / 4) * (1 + Real.log L / 4) ^ 3
      ≤ 610 * (L / Real.log L) := by
    have hrw : (610 : ℝ) * (L / Real.log L) = (610 * L) / Real.log L := by ring
    rw [hrw, le_div_iff₀ hlogL0]
    have hstep := mul_le_mul_of_nonneg_right hpoly h4pos.le
    have hLr : 610 * Real.exp (3 * Real.log L / 4) * Real.exp (Real.log L / 4) = 610 * L := by
      rw [mul_assoc, hmerge]
    nlinarith [hstep, hLr.le, hLr.ge]
  -- the main term
  have hwin : (q : ℝ) * (Real.exp δ - Real.exp (-δ)) ≤ 4 * L := by
    have h := exp_sub_exp_neg_le_four_mul hδ0 hδ1
    have := mul_le_mul_of_nonneg_left h hq0.le
    rw [hLdef]
    nlinarith [this]
  have hmain : 2 * ((q : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / (Real.log L / 4)
      ≤ 40 * (L / Real.log L) := by
    have hrw1 : 2 * ((q : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / (Real.log L / 4)
        = (8 * ((q : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1)) / Real.log L := by
      field_simp
      ring
    have hrw2 : (40 : ℝ) * (L / Real.log L) = (40 * L) / Real.log L := by ring
    rw [hrw1, hrw2, div_le_div_iff₀ hlogL0 hlogL0]
    have hstep : 8 * ((q : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) ≤ 40 * L := by
      linarith [hwin, hL1]
    nlinarith [mul_le_mul_of_nonneg_right hstep hlogL0.le]
  have hLu : (0 : ℝ) ≤ L / Real.log L := by positivity
  linarith [hbt, herr, hmain]

/-- **The prime-supported mean value theorem in affine form, with the sharp near-diagonal mass.** -/
theorem integral_Icc_normSq_logPoly_le_prime_sharp_delta (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ m ∈ s, m.Prime) {δ W : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbig : ∀ q ∈ s, 4 ≤ Real.log ((q : ℝ) * δ)) (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 * 700 / 4) * ∑ q ∈ s, ((q : ℝ) / Real.log ((q : ℝ) * δ)) * ‖a q‖ ^ 2
        + (5 / (4 * δ)) * ∑ q ∈ s, ‖a q‖ ^ 2 := by
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s hδ0 hWδ) ?_
  have hsplit : ∀ q ∈ s,
      (logNeighbourCount s δ q : ℝ) * ‖a q‖ ^ 2
        ≤ (700 * (((q : ℝ) * δ) / Real.log ((q : ℝ) * δ)) + 1) * ‖a q‖ ^ 2 := by
    intro q hq
    exact mul_le_mul_of_nonneg_right
      (logNeighbourCount_le_sharp_delta s hs (hs q hq).two_le hδ0 hδ1 (hbig q hq)) (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsplit) (by positivity)) ?_
  have hexpand : ∑ q ∈ s, (700 * (((q : ℝ) * δ) / Real.log ((q : ℝ) * δ)) + 1) * ‖a q‖ ^ 2
      = 700 * δ * (∑ q ∈ s, ((q : ℝ) / Real.log ((q : ℝ) * δ)) * ‖a q‖ ^ 2)
        + ∑ q ∈ s, ‖a q‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    field_simp
  rw [hexpand, mul_add]
  have h1 : (5 / (4 * δ)) * (700 * δ * ∑ q ∈ s, ((q : ℝ) / Real.log ((q : ℝ) * δ)) * ‖a q‖ ^ 2)
      = (5 * 700 / 4) * ∑ q ∈ s, ((q : ℝ) / Real.log ((q : ℝ) * δ)) * ‖a q‖ ^ 2 := by
    field_simp
  rw [h1]

end RHTower.Sieve

end
