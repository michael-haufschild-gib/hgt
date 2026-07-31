import GaloisForLFunctions.HTGeometry.GammaPolyValuationBoundary

/-!
# The logarithmic layer of the valuation ordering

Equation (19) gives every nonzero element of the digamma field the shape `c·s^a·(log s)^b·(1+o(1))`,
and the ordering (26) compares such coefficients lexicographically in `(k, a, b)`: smaller Gamma
exponent dominates; at equal Gamma exponent, larger `a`; at equal `(k, a)`, larger `b`.  The previous
file settled the `(k, a)` layer; this file adds the logarithmic coordinate.

Two estimates carry it.  On a vertical line `‖log s‖ ≤ log‖s‖ + π`, so the logarithm is dominated by
every positive power of `s` (`tendsto_log_pow_div_pow_vertical`); and `‖log s‖ → ∞`, so a strictly
larger logarithmic exponent in the denominator wins at equal `(k, a)`.  Combining with the
super-polynomial Gamma decay, `s^n (log s)^b Γ(s)^k → 0` for every `n`, `b` and every `k ≥ 1`: the
Gamma direction still beats the whole algebraic-logarithmic scale.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-! ### Size of the complex logarithm on a vertical line -/

theorem norm_log_le_of_one_le {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
  have hre : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
  have him : (Complex.log z).im = Complex.arg z := Complex.log_im z
  have hlognn : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him, abs_of_nonneg hlognn]
  linarith [Complex.abs_arg_le_pi z]

/-- The logarithm grows without bound on an upper vertical line. -/
theorem tendsto_norm_log_vertical_atTop {σ : ℝ} (_hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ => ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (Real.tendsto_log_atTop.comp tendsto_id)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hs : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_norm_vertical σ ht0.le
  have h1 : Real.log t ≤ Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
    Real.log_le_log ht0 hs
  have h2 : Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
      ≤ ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [← Complex.log_re]
    exact Complex.re_le_norm _
  exact le_trans h1 h2

/-- **The logarithm is dominated by every positive power of `s`.** -/
theorem tendsto_log_pow_div_pow_vertical {σ : ℝ} (hσ : 0 ≤ σ) (b : ℕ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b /
        ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) atTop (nhds 0) := by
  have hbase : Tendsto (fun t : ℝ => Real.log (σ + t) ^ b / t) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-σ) b one_ne_zero).comp
      (tendsto_atTop_add_const_left atTop σ tendsto_id)
    refine h.congr (fun t => ?_)
    simp only [Function.comp_apply, id_eq]
    congr 1
    ring
  have hg : Tendsto (fun t : ℝ => (2 : ℝ) ^ b * (Real.log (σ + t) ^ b / t)) atTop (nhds 0) := by
    simpa using hbase.const_mul ((2 : ℝ) ^ b)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  have hpi : Tendsto (fun t : ℝ => Real.log (σ + t)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop σ tendsto_id)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpi.eventually_ge_atTop Real.pi] with t ht hlog
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hs : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_norm_vertical σ ht0.le
  have hs1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_trans ht hs
  have hsle : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := norm_vertical_le hσ ht0.le
  have hlogle : Real.log ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ Real.log (σ + t) :=
    Real.log_le_log (lt_of_lt_of_le one_pos hs1) hsle
  have hnum : ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * Real.log (σ + t) := by
    refine (norm_log_le_of_one_le hs1).trans ?_
    linarith
  have hnumnn : (0 : ℝ) ≤ Real.log (σ + t) := le_trans Real.pi_nonneg hlog
  rw [norm_div, norm_pow, norm_pow]
  have hb : ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b ≤ (2 * Real.log (σ + t)) ^ b :=
    pow_le_pow_left₀ (norm_nonneg _) hnum b
  have hden : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d := by
    calc t ≤ t ^ d := le_self_pow₀ ht hd.ne'
      _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d := pow_le_pow_left₀ ht0.le hs d
  calc ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b /
        ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d
      ≤ (2 * Real.log (σ + t)) ^ b / t := by
        refine div_le_div₀ (by positivity) hb ht0 hden
    _ = (2 : ℝ) ^ b * (Real.log (σ + t) ^ b / t) := by
        rw [mul_pow]
        ring

/-- **Gamma beats the whole algebraic-logarithmic scale.** -/
theorem tendsto_pow_mul_log_pow_mul_Gamma_pow {σ : ℝ} (hσ : 0 < σ) (n b k : ℕ) (hk : 0 < k) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ n *
        (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b *
        (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ k) atTop (nhds 0) := by
  have h1 := tendsto_pow_mul_Gamma_pow hσ (n + 1) k hk
  have h2 := tendsto_log_pow_div_pow_vertical hσ.le b (d := 1) one_pos
  have hmul := h1.mul h2
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  field_simp
  ring

/-! ### The lexicographic ordering with the logarithmic coordinate -/

/-- A Gamma-rational coefficient weighted by the algebraic-logarithmic monomial `s^a (log s)^b`. -/
def GammaRationalDatum.logFn (D : GammaRationalDatum) (a b : ℕ) (s : ℂ) : ℂ :=
  s ^ a * (Complex.log s) ^ b * D.fn s

theorem logFn_ratio_eq (D₁ D₂ : GammaRationalDatum) (a₁ b₁ a₂ b₂ : ℕ) (s : ℂ) :
    D₁.logFn a₁ b₁ s / D₂.logFn a₂ b₂ s
      = (s ^ a₁ * (Complex.log s) ^ b₁) / (s ^ a₂ * (Complex.log s) ^ b₂) *
        (D₁.fn s / D₂.fn s) := by
  simp only [GammaRationalDatum.logFn]
  rw [div_mul_div_comm]

/-- The algebraic-logarithmic monomials are ordered lexicographically on a vertical line. -/
theorem tendsto_logMonomial_ratio_zero {σ : ℝ} (hσ : 0 ≤ σ) {a₁ b₁ a₂ b₂ : ℕ}
    (hlex : a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)) :
    Tendsto (fun t : ℝ =>
        (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
          (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₁) /
        (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂ *
          (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₂)) atTop (nhds 0) := by
  have hlogtop := tendsto_norm_log_vertical_atTop hσ
  rcases hlex with hlt | ⟨heq, hblt⟩
  · -- strictly smaller power of `s`: the logarithm cannot compensate
    obtain ⟨d, hd, hdpos⟩ : ∃ d, a₂ = a₁ + d ∧ 0 < d := ⟨a₂ - a₁, by omega, by omega⟩
    have hkey := tendsto_log_pow_div_pow_vertical hσ b₁ hdpos
    rw [tendsto_zero_iff_norm_tendsto_zero] at hkey ⊢
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hkey
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlogtop.eventually_ge_atTop 1] with t ht hlog1
    have hs : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_norm_vertical σ ht.le
    have hspos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := lt_of_lt_of_le ht hs
    have hL : (0 : ℝ) < ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
      lt_of_lt_of_le one_pos hlog1
    have hlogb : (1 : ℝ) ≤ ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b₂ :=
      one_le_pow₀ hlog1
    simp only [norm_div, norm_mul, norm_pow, hd, pow_add]
    rw [show ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d *
        ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b₂
        = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ a₁ *
          (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d *
            ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b₂) from by ring]
    rw [mul_div_mul_left _ _ (ne_of_gt (pow_pos hspos a₁))]
    exact div_le_div₀ (by positivity) le_rfl (pow_pos hspos d)
      (le_mul_of_one_le_right (by positivity) hlogb)
  · -- equal powers of `s`: the logarithm decides
    subst heq
    obtain ⟨e, he, hepos⟩ : ∃ e, b₂ = b₁ + e ∧ 0 < e := ⟨b₂ - b₁, by omega, by omega⟩
    have hinv : Tendsto (fun t : ℝ =>
        ((Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ e)⁻¹) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (g := fun t : ℝ =>
          ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖⁻¹)
        (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      · filter_upwards [hlogtop.eventually_ge_atTop 1] with t hlog1
        rw [norm_inv, norm_pow]
        have hpos : (0 : ℝ) < ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
          lt_of_lt_of_le one_pos hlog1
        rw [inv_le_inv₀ (by positivity) hpos]
        exact le_self_pow₀ hlog1 hepos.ne'
      · exact tendsto_inv_atTop_zero.comp hlogtop
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlogtop.eventually_ge_atTop 1] with t ht hlog1
    have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [h] at him
      simp only [Complex.zero_im] at him
      linarith
    have hlogne : Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlog1
      linarith
    rw [he, pow_add]
    field_simp

/-- **Lexicographic ordering at equal Gamma valuation.**  A strictly smaller algebraic-logarithmic
monomial in the numerator sends the normalized ratio to zero. -/
theorem gammaRationalDatum_logRatio_tendsto_zero_of_lex
    (D₁ D₂ : GammaRationalDatum) {a₁ b₁ a₂ b₂ : ℕ}
    (hn : D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder)
    (hlex : a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.logFn a₁ b₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.logFn a₂ b₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hratio := gammaRationalDatum_ratio_vertical_tendsto D₁ D₂ 0 (by omega) hσ
  rw [pow_zero, one_mul] at hratio
  have hmon := tendsto_logMonomial_ratio_zero hσ.le hlex
  have hmul := hmon.mul hratio
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards with t
  exact (logFn_ratio_eq D₁ D₂ a₁ b₁ a₂ b₂ _).symm

/-- **Equal Gamma valuation and equal algebraic-logarithmic monomial give the residue quotient.** -/
theorem gammaRationalDatum_logRatio_tendsto_residue
    (D₁ D₂ : GammaRationalDatum) (a b : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder)
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.logFn a b ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.logFn a b ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds (D₁.residue / D₂.residue)) := by
  have hratio := gammaRationalDatum_ratio_vertical_tendsto D₁ D₂ 0 (by omega) hσ
  rw [pow_zero, one_mul] at hratio
  have hlogtop := tendsto_norm_log_vertical_atTop hσ.le
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlogtop.eventually_ge_atTop 1] with t ht hlog1
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  have hlogne : Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlog1
    linarith
  rw [logFn_ratio_eq, div_self (by positivity), one_mul]

end

end GaloisForLFunctions
