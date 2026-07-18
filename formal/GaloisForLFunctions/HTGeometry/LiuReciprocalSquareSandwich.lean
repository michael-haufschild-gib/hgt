import Mathlib

/-!
# The Liu reciprocal-square sandwich has a strictly positive gap

Formalization of the card
`docs/drafts/pipeline/2-fully-proven/needs-audit/liu-reciprocal-square-sandwich-positive-gap.md`.

Dasheng Liu's proposed disproof of the Riemann hypothesis (arXiv:2404.06306v3, equations
(4.17)--(4.26)) derives a contradiction from two reciprocal-square estimates, an alleged lower
bound `L(z)` and an alleged upper bound `U(z)` for the same quantity `S₂ = ∑ aₘ²`.  This file
proves that the two estimates are *analytically compatible*: under the stated positivity and
summability hypotheses one always has

```text
L(z) < S₂ < U(z),
```

so the reversal `U(z) ≤ L(z)` claimed in the preprint cannot be an analytic consequence of the
product.  The gap is moreover exactly computed and is a manifestly positive odd power series.

## Main statements

* `HTGeometry.LiuSandwich.log_one_add_lower` : `x - x²/2 < log (1 + x)` for `0 < x`.
* `HTGeometry.LiuSandwich.log_one_sub_upper` : `log (1 - x) < -x - x²/2` for `0 < x < 1`.
* `HTGeometry.LiuSandwich.lowerBd_lt_sumSq` and `sumSq_lt_upperBd` : the two sandwich halves.
* `HTGeometry.LiuSandwich.upperBd_sub_lowerBd_eq` : the exact gap `(2/z²) ∑ (log((1+aₘz)/(1-aₘz)) - 2aₘz)`.
* `HTGeometry.LiuSandwich.hasSum_logRatio_tail` : `log((1+x)/(1-x)) - 2x = 2 ∑_{k≥1} x^(2k+1)/(2k+1)`.
* `HTGeometry.LiuSandwich.upperBd_sub_lowerBd_eq_oddSeries` : the gap in the card's double-series form.
* `HTGeometry.LiuSandwich.liu_sandwich` : the packaged sandwich with strictly positive gap.
* `HTGeometry.LiuSandwich.not_upperBd_le_lowerBd` : the route kill — no exact evaluation can reverse
  the two bounds.

Nothing here is postulated: every statement is an unconditional theorem of real analysis.
-/

open Set

namespace HTGeometry
namespace LiuSandwich

/-! ## Two elementary logarithmic bounds

Both are proved by the derivative argument of the card: an auxiliary function vanishing at `0` has
strictly positive derivative, hence is strictly monotone. -/

/-- `log (1 + x) > x - x²/2` for every `x > 0`.  The auxiliary function
`t ↦ log (1 + t) - t + t²/2` vanishes at `0` and has derivative `t²/(1+t) > 0`. -/
theorem log_one_add_lower {x : ℝ} (hx : 0 < x) : x - x ^ 2 / 2 < Real.log (1 + x) := by
  have key : StrictMonoOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id) (by fun_prop)
      refine ContinuousOn.log (by fun_prop) ?_
      intro t ht
      simp only [Set.mem_Ici] at ht
      linarith
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      have ht1 : (0 : ℝ) < 1 + t := by linarith
      have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
        simpa using (hasDerivAt_id t).const_add (1 : ℝ)
      have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹ * 1) t := by
        simpa [Function.comp] using (Real.hasDerivAt_log (ne_of_gt ht1)).comp t h1
      have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 : ℝ) * t ^ 1 / 2) t := by
        simpa using (hasDerivAt_pow 2 t).div_const 2
      have hd : HasDerivAt (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
          ((1 + t)⁻¹ * 1 - 1 + (2 : ℝ) * t ^ 1 / 2) t :=
        (h2.sub (hasDerivAt_id t)).add h3
      rw [hd.deriv]
      have hrw : (1 + t)⁻¹ * 1 - 1 + (2 : ℝ) * t ^ 1 / 2 = t ^ 2 / (1 + t) := by
        field_simp
        ring
      rw [hrw]
      positivity
  have h0 : Real.log (1 + (0 : ℝ)) - 0 + (0 : ℝ) ^ 2 / 2 = 0 := by norm_num
  have := key Set.self_mem_Ici (Set.mem_Ici.2 hx.le) hx
  simp only [h0] at this
  linarith

/-- `log (1 - x) < -x - x²/2` for every `0 < x < 1`.  The auxiliary function
`t ↦ -t - t²/2 - log (1 - t)` vanishes at `0` and has derivative `t²/(1-t) > 0`. -/
theorem log_one_sub_upper {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (1 - x) < -x - x ^ 2 / 2 := by
  have key : StrictMonoOn (fun t : ℝ => -t - t ^ 2 / 2 - Real.log (1 - t))
      (Set.Ico (0 : ℝ) 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 1) ?_ ?_
    · refine ContinuousOn.sub (by fun_prop) ?_
      refine ContinuousOn.log (by fun_prop) ?_
      intro t ht
      simp only [Set.mem_Ico] at ht
      have := ht.2
      intro h
      linarith [sub_eq_zero.1 h]
    · intro t ht
      rw [interior_Ico, Set.mem_Ioo] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have hsub : (0 : ℝ) < 1 - t := by linarith
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) ((1 - t)⁻¹ * (-1)) t := by
        simpa [Function.comp] using (Real.hasDerivAt_log (ne_of_gt hsub)).comp t h1
      have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 : ℝ) * t ^ 1 / 2) t := by
        simpa using (hasDerivAt_pow 2 t).div_const 2
      have hd : HasDerivAt (fun t : ℝ => -t - t ^ 2 / 2 - Real.log (1 - t))
          (-1 - (2 : ℝ) * t ^ 1 / 2 - (1 - t)⁻¹ * (-1)) t :=
        (((hasDerivAt_id t).neg).sub h3).sub h2
      rw [hd.deriv]
      have hrw : -1 - (2 : ℝ) * t ^ 1 / 2 - (1 - t)⁻¹ * (-1) = t ^ 2 / (1 - t) := by
        field_simp
        ring
      rw [hrw]
      positivity
  have h0 : -(0 : ℝ) - (0 : ℝ) ^ 2 / 2 - Real.log (1 - (0 : ℝ)) = 0 := by norm_num
  have hmem0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have := key hmem0 ⟨hx0.le, hx1⟩ hx0
  simp only [h0] at this
  linarith

/-! ## The two bounds -/

variable {ι : Type*} {a : ι → ℝ} {z q : ℝ}

/-- `Ψ(z) = ∑ log (1 + aₘ z)`.  Evaluated at `-z` it is the second logarithmic sum of the card. -/
noncomputable def logSum (a : ι → ℝ) (z : ℝ) : ℝ := ∑' m, Real.log (1 + a m * z)

/-- The alleged lower bound `L(z) = (2/z²)(S₁ z - Ψ(z))`. -/
noncomputable def lowerBd (a : ι → ℝ) (z : ℝ) : ℝ :=
  2 / z ^ 2 * ((∑' m, a m) * z - logSum a z)

/-- The alleged upper bound `U(z) = -(2/z²)(S₁ z + Ψ(-z))`. -/
noncomputable def upperBd (a : ι → ℝ) (z : ℝ) : ℝ :=
  -(2 / z ^ 2) * ((∑' m, a m) * z + logSum a (-z))

@[simp] theorem logSum_neg (a : ι → ℝ) (z : ℝ) :
    logSum a (-z) = ∑' m, Real.log (1 - a m * z) := by
  simp [logSum, mul_neg, sub_eq_add_neg]

/-! ### Summability -/

/-- `0 ≤ log (1 + aₘ z) ≤ aₘ z` makes the first logarithmic family summable. -/
theorem summable_logAdd (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hsum : Summable a) :
    Summable fun m => Real.log (1 + a m * z) := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hsum.mul_right z)
  · have : 0 < a m * z := mul_pos (hpos m) hz
    exact Real.log_nonneg (by linarith)
  · have h := Real.log_le_sub_one_of_pos (x := 1 + a m * z)
      (by have := mul_pos (hpos m) hz; linarith)
    linarith

/-- `0 ≤ -log (1 - aₘ z) ≤ aₘ z/(1-q)` makes the second logarithmic family summable. -/
theorem summable_logSub (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    Summable fun m => Real.log (1 - a m * z) := by
  have hcomp : Summable fun m => a m * z / (1 - q) :=
    ((hsum.mul_right z).div_const (1 - q))
  have hneg : Summable fun m => -Real.log (1 - a m * z) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hcomp
    · have hx : 0 < a m * z := mul_pos (hpos m) hz
      have h1 : a m * z ≤ q := hb m
      have : Real.log (1 - a m * z) ≤ 0 :=
        Real.log_nonpos (by linarith) (by linarith)
      linarith
    · have hx : 0 < a m * z := mul_pos (hpos m) hz
      have h1 : a m * z ≤ q := hb m
      have hden : (0 : ℝ) < 1 - a m * z := by linarith
      have hdenq : (0 : ℝ) < 1 - q := by linarith
      have h2 : Real.log ((1 - a m * z)⁻¹) ≤ (1 - a m * z)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_inv] at h2
      have h3 : (1 - a m * z)⁻¹ - 1 = a m * z / (1 - a m * z) := by
        field_simp
        ring
      rw [h3] at h2
      refine h2.trans ?_
      apply div_le_div_of_nonneg_left hx.le hdenq
      linarith
  simpa using hneg.neg

/-- The squares are summable: `aₘ² ≤ (q/z) aₘ`. -/
theorem summable_sq (hpos : ∀ m, 0 < a m) (hz : 0 < z)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    Summable fun m => (a m) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_)
    (hsum.mul_right (q / z))
  have h1 : a m ≤ q / z := by
    rw [le_div_iff₀ hz]
    exact hb m
  have h2 : 0 < a m := hpos m
  nlinarith

/-! ### The lower half of the sandwich -/

/-- Rewriting of the lower-side excess as a single sum. -/
theorem lowerExcess_eq (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hsum : Summable a) :
    (∑' m, a m) * z - logSum a z = ∑' m, (a m * z - Real.log (1 + a m * z)) := by
  rw [logSum, ← tsum_mul_right,
    ← Summable.tsum_sub (hsum.mul_right z) (summable_logAdd hpos hz hsum)]

/-- **Lower half of the sandwich.** `L(z) < S₂`. -/
theorem lowerBd_lt_sumSq [Nonempty ι] (hpos : ∀ m, 0 < a m) (hz : 0 < z)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    lowerBd a z < ∑' m, (a m) ^ 2 := by
  obtain ⟨m₀⟩ := ‹Nonempty ι›
  have hzne : z ≠ 0 := ne_of_gt hz
  have hsq := summable_sq hpos hz hb hsum
  have hterm : ∀ m, a m * z - Real.log (1 + a m * z) < (a m) ^ 2 * (z ^ 2 / 2) := by
    intro m
    have hx : 0 < a m * z := mul_pos (hpos m) hz
    have h := log_one_add_lower hx
    nlinarith [h]
  have hsum1 : Summable fun m => a m * z - Real.log (1 + a m * z) :=
    (hsum.mul_right z).sub (summable_logAdd hpos hz hsum)
  have hsum2 : Summable fun m => (a m) ^ 2 * (z ^ 2 / 2) := hsq.mul_right _
  have hlt : ∑' m, (a m * z - Real.log (1 + a m * z))
      < ∑' m, ((a m) ^ 2 * (z ^ 2 / 2)) :=
    hsum1.tsum_lt_tsum (i := m₀) (fun m => (hterm m).le) (hterm m₀) hsum2
  rw [tsum_mul_right] at hlt
  have hpos2 : (0 : ℝ) < 2 / z ^ 2 := by positivity
  calc lowerBd a z = 2 / z ^ 2 * (∑' m, (a m * z - Real.log (1 + a m * z))) := by
        rw [lowerBd, lowerExcess_eq hpos hz hsum]
    _ < 2 / z ^ 2 * ((∑' m, (a m) ^ 2) * (z ^ 2 / 2)) := by
        exact mul_lt_mul_of_pos_left hlt hpos2
    _ = ∑' m, (a m) ^ 2 := by field_simp

/-! ### The upper half of the sandwich -/

/-- Rewriting of the upper-side excess as a single sum. -/
theorem upperExcess_eq (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    -((∑' m, a m) * z) - logSum a (-z) = ∑' m, (-(a m * z) - Real.log (1 - a m * z)) := by
  rw [logSum_neg, ← tsum_mul_right, ← tsum_neg,
    ← Summable.tsum_sub ((hsum.mul_right z).neg) (summable_logSub hpos hz hq hb hsum)]

/-- **Upper half of the sandwich.** `S₂ < U(z)`. -/
theorem sumSq_lt_upperBd [Nonempty ι] (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    ∑' m, (a m) ^ 2 < upperBd a z := by
  obtain ⟨m₀⟩ := ‹Nonempty ι›
  have hzne : z ≠ 0 := ne_of_gt hz
  have hsq := summable_sq hpos hz hb hsum
  have hterm : ∀ m, (a m) ^ 2 * (z ^ 2 / 2) < -(a m * z) - Real.log (1 - a m * z) := by
    intro m
    have hx : 0 < a m * z := mul_pos (hpos m) hz
    have hx1 : a m * z < 1 := lt_of_le_of_lt (hb m) hq
    have h := log_one_sub_upper hx hx1
    nlinarith [h]
  have hsum1 : Summable fun m => -(a m * z) - Real.log (1 - a m * z) :=
    ((hsum.mul_right z).neg).sub (summable_logSub hpos hz hq hb hsum)
  have hsum2 : Summable fun m => (a m) ^ 2 * (z ^ 2 / 2) := hsq.mul_right _
  have hlt : ∑' m, ((a m) ^ 2 * (z ^ 2 / 2))
      < ∑' m, (-(a m * z) - Real.log (1 - a m * z)) :=
    hsum2.tsum_lt_tsum (i := m₀) (fun m => (hterm m).le) (hterm m₀) hsum1
  rw [tsum_mul_right] at hlt
  have hpos2 : (0 : ℝ) < 2 / z ^ 2 := by positivity
  have hU : upperBd a z = 2 / z ^ 2 * (-((∑' m, a m) * z) - logSum a (-z)) := by
    rw [upperBd]; ring
  calc ∑' m, (a m) ^ 2 = 2 / z ^ 2 * ((∑' m, (a m) ^ 2) * (z ^ 2 / 2)) := by field_simp
    _ < 2 / z ^ 2 * (∑' m, (-(a m * z) - Real.log (1 - a m * z))) :=
        mul_lt_mul_of_pos_left hlt hpos2
    _ = upperBd a z := by rw [hU, upperExcess_eq hpos hz hq hb hsum]

/-! ### The exact gap -/

/-- **Exact gap identity.**
`U(z) - L(z) = (2/z²) ∑ (log (1 + aₘ z) - log (1 - aₘ z) - 2 aₘ z)`. -/
theorem upperBd_sub_lowerBd_eq (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    upperBd a z - lowerBd a z
      = 2 / z ^ 2 * ∑' m, (Real.log (1 + a m * z) - Real.log (1 - a m * z) - 2 * (a m * z)) := by
  have hA := summable_logAdd hpos hz hsum
  have hB := summable_logSub hpos hz hq hb hsum
  have hC : Summable fun m => 2 * (a m * z) := (hsum.mul_right z).mul_left 2
  have hsplit : ∑' m, (Real.log (1 + a m * z) - Real.log (1 - a m * z) - 2 * (a m * z))
      = logSum a z - logSum a (-z) - 2 * ((∑' m, a m) * z) := by
    rw [Summable.tsum_sub (hA.sub hB) hC, Summable.tsum_sub hA hB, logSum, logSum_neg]
    congr 1
    rw [tsum_mul_left, tsum_mul_right]
  rw [hsplit, upperBd, lowerBd]
  ring

/-! ### The odd power series form of the gap -/

/-- For `|x| < 1`, `log (1 + x) - log (1 - x) = 2 ∑_{j ≥ 0} x^(2j+1)/(2j+1)`. -/
theorem hasSum_logRatio {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => 2 * x ^ (2 * j + 1) / (2 * j + 1))
      (Real.log (1 + x) - Real.log (1 - x)) := by
  have h1 : HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)) (-Real.log (1 - x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hxneg : |(-x)| < 1 := by rwa [abs_neg]
  have h2 : HasSum (fun n : ℕ => (-x) ^ (n + 1) / (n + 1)) (-Real.log (1 - -x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hxneg
  have h2' : HasSum (fun n : ℕ => (-x) ^ (n + 1) / (n + 1)) (-Real.log (1 + x)) := by
    simpa [sub_neg_eq_add] using h2
  have hdiff : HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1) - (-x) ^ (n + 1) / (n + 1))
      (Real.log (1 + x) - Real.log (1 - x)) := by
    have := h1.sub h2'
    convert this using 1
    ring
  set F : ℕ → ℝ := fun n => x ^ (n + 1) / (n + 1) - (-x) ^ (n + 1) / (n + 1) with hF
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := by
    intro i j h
    simp only at h
    omega
  have hzero : ∀ n ∉ Set.range (fun j : ℕ => 2 * j), F n = 0 := by
    intro n hn
    have hodd : ¬ Even n := by
      intro he
      obtain ⟨r, hr⟩ := he
      exact hn ⟨r, by simp only; omega⟩
    have heven : Even (n + 1) := by
      rcases Nat.even_or_odd n with h | h
      · exact absurd h hodd
      · exact h.add_one
    simp [hF, heven.neg_pow]
  have hcomp : (fun j : ℕ => F (2 * j)) = fun j : ℕ => 2 * x ^ (2 * j + 1) / (2 * j + 1) := by
    funext j
    have heven : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
    have hodd : Odd (2 * j + 1) := ⟨j, by ring⟩
    rw [hF]
    simp only
    rw [hodd.neg_pow]
    push_cast
    ring
  have := (hinj.hasSum_iff (f := F) hzero (a := Real.log (1 + x) - Real.log (1 - x)))
  rw [show (F ∘ fun j : ℕ => 2 * j) = fun j : ℕ => 2 * x ^ (2 * j + 1) / (2 * j + 1) from hcomp]
    at this
  exact this.2 hdiff

/-- The tail form of the card: `log ((1+x)/(1-x)) - 2x = 2 ∑_{k ≥ 1} x^(2k+1)/(2k+1)`. -/
theorem hasSum_logRatio_tail {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => 2 * x ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1))
      (Real.log (1 + x) - Real.log (1 - x) - 2 * x) := by
  set f : ℕ → ℝ := fun j => 2 * x ^ (2 * j + 1) / (2 * (j : ℝ) + 1) with hf
  have h : HasSum f (Real.log (1 + x) - Real.log (1 - x)) := hasSum_logRatio hx
  have h0 : (∑ i ∈ Finset.range 1, f i) = 2 * x := by
    simp [hf]
  have hshift : HasSum (fun n : ℕ => f (n + 1))
      (Real.log (1 + x) - Real.log (1 - x) - 2 * x) := by
    rw [hasSum_nat_add_iff (f := f) 1, h0]
    simpa using h
  have hfun : (fun n : ℕ => f (n + 1))
      = fun k : ℕ => 2 * x ^ (2 * (k + 1) + 1) / (2 * ((k : ℝ) + 1) + 1) := by
    funext n
    simp only [hf]
    push_cast
    ring
  rwa [hfun] at hshift

/-- Each gap term is a strictly positive odd series. -/
theorem gap_term_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < Real.log (1 + x) - Real.log (1 - x) - 2 * x := by
  have h1 := log_one_add_lower hx0
  have h2 := log_one_sub_upper hx0 hx1
  nlinarith [sq_nonneg x]

/-- **The gap in the card's double-series form.**
`U(z) - L(z) = (4/z²) ∑ₘ ∑_{k ≥ 1} (aₘ z)^(2k+1)/(2k+1)`. -/
theorem upperBd_sub_lowerBd_eq_oddSeries (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    upperBd a z - lowerBd a z
      = 4 / z ^ 2 *
        ∑' m, ∑' k : ℕ, (a m * z) ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1) := by
  have hterm : ∀ m,
      Real.log (1 + a m * z) - Real.log (1 - a m * z) - 2 * (a m * z)
        = 2 * ∑' k : ℕ, (a m * z) ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1) := by
    intro m
    have hx : 0 < a m * z := mul_pos (hpos m) hz
    have hx1 : a m * z < 1 := lt_of_le_of_lt (hb m) hq
    have habs : |a m * z| < 1 := by
      rw [abs_of_pos hx]; exact hx1
    have h := hasSum_logRatio_tail habs
    have h' : HasSum (fun k : ℕ => (a m * z) ^ (2 * (k + 1) + 1) / (2 * (k + 1) + 1))
        ((Real.log (1 + a m * z) - Real.log (1 - a m * z) - 2 * (a m * z)) / 2) := by
      have := h.div_const 2
      convert this using 2 with k
      ring
    rw [h'.tsum_eq]
    ring
  rw [upperBd_sub_lowerBd_eq hpos hz hq hb hsum]
  rw [tsum_congr hterm, tsum_mul_left]
  ring

/-! ## The packaged theorem and the route kill -/

/-- **Liu reciprocal-square sandwich with a strictly positive gap.**
For a nonempty positive summable family `a` with `aₘ z ≤ q < 1` and `z > 0`, the alleged lower
bound is strictly below `S₂ = ∑ aₘ²`, which is strictly below the alleged upper bound; in
particular the gap `U(z) - L(z)` is strictly positive. -/
theorem liu_sandwich [Nonempty ι] (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    lowerBd a z < ∑' m, (a m) ^ 2 ∧ ∑' m, (a m) ^ 2 < upperBd a z ∧
      0 < upperBd a z - lowerBd a z := by
  have hL := lowerBd_lt_sumSq (q := q) hpos hz hb hsum
  have hU := sumSq_lt_upperBd hpos hz hq hb hsum
  exact ⟨hL, hU, by linarith⟩

/-- **Route kill.** Under the preprint's own positive-product hypotheses no exact evaluation can
put the upper bound at or below the lower bound: the reversal used to derive the contradiction is
not an analytic consequence of the product. -/
theorem not_upperBd_le_lowerBd [Nonempty ι] (hpos : ∀ m, 0 < a m) (hz : 0 < z) (hq : q < 1)
    (hb : ∀ m, a m * z ≤ q) (hsum : Summable a) :
    ¬ upperBd a z ≤ lowerBd a z := by
  have h := (liu_sandwich hpos hz hq hb hsum).2.2
  linarith

end LiuSandwich
end HTGeometry
