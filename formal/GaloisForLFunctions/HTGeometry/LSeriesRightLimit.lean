/-
# A Dirichlet series tends to its first coefficient to the right

Past the abscissa of absolute convergence the tail of a Dirichlet series is dominated by
`2^{σ₀ - Re s}` times a fixed convergent sum, so the series tends to its first coefficient along
*every* family whose real part escapes to `+∞` — no restriction to the real axis, and no
restriction on the imaginary part.

Main results:
* `norm_term_le_of_re_le` — the terms decrease as the real part grows.
* `norm_term_le_two_pow` — past the second term the decay is geometric in `Re s`.
* `summable_norm_term_of_rpow_bound` — a polynomial coefficient bound gives absolute convergence.
* `tendsto_LSeries_of_re_atTop` — **`L(f,s) → f(1)` whenever `Re s → ∞`**.
-/
import Mathlib

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem norm_term_le_of_re_le {f : ℕ → ℂ} {σ₀ : ℝ} {w : ℂ} (hw : σ₀ ≤ w.re) (n : ℕ) :
    ‖LSeries.term f w n‖ ≤ ‖LSeries.term f (σ₀ : ℂ) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, Complex.ofReal_re]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
    have hpow : ((n : ℝ)) ^ σ₀ ≤ ((n : ℝ)) ^ w.re :=
      Real.rpow_le_rpow_of_exponent_le hn1 hw
    have hb : (0 : ℝ) < ((n : ℝ)) ^ σ₀ := Real.rpow_pos_of_pos hnpos _
    have hc : (0 : ℝ) < ((n : ℝ)) ^ w.re := Real.rpow_pos_of_pos hnpos _
    rw [div_le_div_iff₀ hc hb]
    exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)

theorem norm_term_le_two_pow {f : ℕ → ℂ} {σ₀ : ℝ} {w : ℂ} (hw : σ₀ ≤ w.re) {n : ℕ}
    (hn : 2 ≤ n) :
    ‖LSeries.term f w n‖ ≤ (2 : ℝ) ^ (σ₀ - w.re) * ‖LSeries.term f (σ₀ : ℂ) n‖ := by
  have hn0 : n ≠ 0 := by omega
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0, Complex.ofReal_re]
  have hz : σ₀ - w.re ≤ 0 := by linarith
  have hkey : ((n : ℝ)) ^ (σ₀ - w.re) ≤ (2 : ℝ) ^ (σ₀ - w.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 hz
  have heq : ‖f n‖ / (n : ℝ) ^ w.re = (‖f n‖ / (n : ℝ) ^ σ₀) * ((n : ℝ) ^ (σ₀ - w.re)) := by
    rw [Real.rpow_sub hnpos]
    field_simp
  rw [heq, mul_comm ((2 : ℝ) ^ (σ₀ - w.re))]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

theorem summable_norm_term_of_rpow_bound {f : ℕ → ℂ} {C p σ₀ : ℝ}
    (hf : ∀ n : ℕ, ‖f n‖ ≤ C * (n : ℝ) ^ p) (hp : p + 1 < σ₀) :
    Summable (fun n : ℕ => ‖LSeries.term f (σ₀ : ℂ) n‖) := by
  have hC : 0 ≤ C := by
    have := hf 1
    simp at this
    linarith [norm_nonneg (f 1)]
  have hsum : Summable (fun n : ℕ => C * ((n : ℝ) ^ (-(σ₀ - p)))) := by
    refine Summable.mul_left C ?_
    have hrw : (fun n : ℕ => ((n : ℝ) ^ (-(σ₀ - p)))) = fun n : ℕ => (((n : ℝ) ^ (σ₀ - p))⁻¹) := by
      funext n
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
    rw [hrw, Real.summable_nat_rpow_inv]
    linarith
  refine hsum.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
    positivity
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
    rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re, div_le_iff₀
      (Real.rpow_pos_of_pos hnpos _)]
    have hstep : C * ((n : ℝ) ^ (-(σ₀ - p))) * (n : ℝ) ^ σ₀ = C * (n : ℝ) ^ p := by
      rw [mul_assoc, ← Real.rpow_add hnpos]
      have hexp : -(σ₀ - p) + σ₀ = p := by ring
      rw [hexp]
    rw [hstep]
    exact hf n

/-- **A Dirichlet series tends to its first coefficient along every family escaping to the
right.** -/
theorem tendsto_LSeries_of_re_atTop {f : ℕ → ℂ} {σ₀ : ℝ}
    (hσ : Summable (fun n : ℕ => ‖LSeries.term f (σ₀ : ℂ) n‖))
    {α : Type*} {l : Filter α} {w : α → ℂ} (hw : Tendsto (fun a => (w a).re) l atTop) :
    Tendsto (fun a => LSeries f (w a)) l (𝓝 (f 1)) := by
  classical
  set S : ℝ := ∑' n : ℕ, ‖LSeries.term f (σ₀ : ℂ) n‖ with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have key : ∀ᶠ a in l, ‖LSeries f (w a) - f 1‖ ≤ (2 : ℝ) ^ (σ₀ - (w a).re) * S := by
    filter_upwards [hw.eventually_ge_atTop σ₀] with a ha
    have hnorm : Summable (fun n : ℕ => ‖LSeries.term f (w a) n‖) :=
      hσ.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_term_le_of_re_le ha n)
    have hsummable : Summable (LSeries.term f (w a)) := hnorm.of_norm
    have hsplit := hsummable.tsum_eq_add_tsum_ite 1
    have hone : LSeries.term f (w a) 1 = f 1 := by simp
    have hLS : LSeries f (w a) - f 1
        = ∑' n : ℕ, (if n = 1 then 0 else LSeries.term f (w a) n) := by
      have : LSeries f (w a) = ∑' n : ℕ, LSeries.term f (w a) n := rfl
      rw [this, hsplit, hone]
      ring
    have hbound : ∀ n : ℕ, ‖(if n = 1 then 0 else LSeries.term f (w a) n)‖
        ≤ (2 : ℝ) ^ (σ₀ - (w a).re) * ‖LSeries.term f (σ₀ : ℂ) n‖ := by
      intro n
      by_cases h1 : n = 1
      · simp [h1]
        positivity
      · rcases eq_or_ne n 0 with rfl | h0
        · simp
        · have hn2 : 2 ≤ n := by omega
          rw [if_neg h1]
          exact norm_term_le_two_pow ha hn2
    have hsum2 : Summable (fun n : ℕ =>
        (2 : ℝ) ^ (σ₀ - (w a).re) * ‖LSeries.term f (σ₀ : ℂ) n‖) := hσ.mul_left _
    have hsumu : Summable (fun n : ℕ => ‖(if n = 1 then 0 else LSeries.term f (w a) n)‖) :=
      hsum2.of_nonneg_of_le (fun n => norm_nonneg _) hbound
    rw [hLS]
    calc ‖∑' n : ℕ, (if n = 1 then 0 else LSeries.term f (w a) n)‖
        ≤ ∑' n : ℕ, ‖(if n = 1 then 0 else LSeries.term f (w a) n)‖ :=
          norm_tsum_le_tsum_norm hsumu
      _ ≤ ∑' n : ℕ, (2 : ℝ) ^ (σ₀ - (w a).re) * ‖LSeries.term f (σ₀ : ℂ) n‖ :=
          hsumu.tsum_le_tsum hbound hsum2
      _ = (2 : ℝ) ^ (σ₀ - (w a).re) * S := by rw [tsum_mul_left]
  have hten : Tendsto (fun a => (2 : ℝ) ^ (σ₀ - (w a).re)) l (𝓝 0) := by
    have hbot : Tendsto (fun a => Real.log 2 * (σ₀ - (w a).re)) l atBot := by
      have h1 : Tendsto (fun a => -(w a).re) l atBot := tendsto_neg_atTop_atBot.comp hw
      have h2 : Tendsto (fun a => σ₀ + -(w a).re) l atBot :=
        Filter.tendsto_atBot_add_const_left _ _ h1
      have h3 : Tendsto (fun a => σ₀ - (w a).re) l atBot := by
        refine h2.congr fun a => by ring
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact Filter.Tendsto.const_mul_atBot hlog h3
    have hexp := Real.tendsto_exp_atBot.comp hbot
    refine hexp.congr fun a => ?_
    exact (Real.rpow_def_of_pos (by norm_num) _).symm
  have hzero : Tendsto (fun a => (2 : ℝ) ^ (σ₀ - (w a).re) * S) l (𝓝 0) := by
    have := hten.mul_const S
    rwa [zero_mul] at this
  have hsub : Tendsto (fun a => LSeries f (w a) - f 1) l (𝓝 0) :=
    squeeze_zero_norm' key hzero
  have := hsub.add (tendsto_const_nhds (x := f 1) (f := l))
  rw [zero_add] at this
  refine this.congr fun a => ?_
  ring

end GaloisForLFunctions.HTGeometry
