import GaloisForLFunctions.HTGeometry.GammaLogStripCollapse
import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic

/-!
# The valuation ordering with a general logarithmic-scale weight, and the digamma instance

The algebraic-logarithmic scale of eq. (19) is not tied to `log s`: what the ordering uses is only
that the weight grows without bound and is dominated by every positive power of `s`.  This file
isolates those two properties as `IsVerticalLogWeight` and reproves the whole ordering for an
arbitrary such weight, so the same theorems apply to the actual generator of the digamma field.

`Complex.log` is a weight, and so is `Complex.digamma`: the corpus vertical asymptotic
`ψ(σ+it) − (log t + iπ/2) → 0` bounds `‖ψ‖` by `2 log t` eventually, which is exactly the domination
required.  Consequently the finite-phase collapse holds for coefficients
`s^a ψ(s)^b · P(Γ)/Q(Γ)` — monomials in the actual digamma field, not in an auxiliary logarithm.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- A logarithmic-scale weight on the vertical line of abscissa `σ`: it grows without bound, yet is
dominated by every positive power of `s`. -/
structure IsVerticalLogWeight (w : ℂ → ℂ) (σ : ℝ) : Prop where
  tendsto_norm_atTop :
    Tendsto (fun t : ℝ => ‖w ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop
  tendsto_pow_div_pow : ∀ b d : ℕ, 0 < d →
    Tendsto (fun t : ℝ => (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b /
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) atTop (nhds 0)

/-- The principal logarithm is a logarithmic-scale weight. -/
theorem isVerticalLogWeight_log {σ : ℝ} (hσ : 0 ≤ σ) : IsVerticalLogWeight Complex.log σ where
  tendsto_norm_atTop := tendsto_norm_log_vertical_atTop hσ
  tendsto_pow_div_pow := fun b _ hd => tendsto_log_pow_div_pow_vertical hσ b hd

/-! ### The digamma function is a logarithmic-scale weight -/

/-- The corpus vertical asymptotic bounds digamma by twice the logarithm of the height. -/
theorem norm_digamma_vertical_le_two_log {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᶠ t : ℝ in atTop, ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * Real.log t := by
  have hasy := RHTower.digamma_vertical_sub_log_I_tendsto_zero σ hσ
  have hclose : ∀ᶠ t : ℝ in atTop,
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
        ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)‖ ≤ 1 := by
    have hn : Tendsto (fun t : ℝ =>
        ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
          ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)‖) atTop (nhds 0) := by
      simpa using hasy.norm
    exact Filter.Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hn
  have hlogtop : Tendsto (fun t : ℝ => Real.log t) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ), hclose,
    hlogtop.eventually_ge_atTop (Real.pi / 2 + 1)] with t ht hcl hlog
  have hlognn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hmain : ‖(Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I‖
      ≤ Real.log t + Real.pi / 2 := by
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖((Real.log t : ℝ) : ℂ)‖ = Real.log t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognn]
    have h2 : ‖(Real.pi / 2 : ℂ) * Complex.I‖ = Real.pi / 2 := by
      simp [abs_of_nonneg Real.pi_nonneg]
    rw [h1, h2]
  calc ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖(Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
          ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)) +
          ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)‖ := by congr 1; ring
    _ ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
          ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)‖ +
        ‖(Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ 1 + (Real.log t + Real.pi / 2) := add_le_add hcl hmain
    _ ≤ 2 * Real.log t := by linarith

/-- **Digamma is dominated by every positive power of `s`.** -/
theorem tendsto_digamma_pow_div_pow_vertical {σ : ℝ} (hσ : 0 ≤ σ) (b : ℕ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b /
        ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) atTop (nhds 0) := by
  have hbase : Tendsto (fun t : ℝ => Real.log t ^ b / t) atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 b one_ne_zero
    refine h.congr (fun t => ?_)
    congr 1
    ring
  have hg : Tendsto (fun t : ℝ => (2 : ℝ) ^ b * (Real.log t ^ b / t)) atTop (nhds 0) := by
    simpa using hbase.const_mul ((2 : ℝ) ^ b)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [eventually_ge_atTop (1 : ℝ), norm_digamma_vertical_le_two_log hσ] with t ht hpsi
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlognn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hs : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_norm_vertical σ ht0.le
  have hden : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d := by
    calc t ≤ t ^ d := le_self_pow₀ ht hd.ne'
      _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d := pow_le_pow_left₀ ht0.le hs d
  rw [norm_div, norm_pow, norm_pow]
  have hb : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b ≤ (2 * Real.log t) ^ b :=
    pow_le_pow_left₀ (norm_nonneg _) hpsi b
  calc ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b /
        ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d
      ≤ (2 * Real.log t) ^ b / t := div_le_div₀ (by positivity) hb ht0 hden
    _ = (2 : ℝ) ^ b * (Real.log t ^ b / t) := by
        rw [mul_pow]
        ring

/-- Digamma is a logarithmic-scale weight on every vertical line of nonnegative abscissa. -/
theorem isVerticalLogWeight_digamma {σ : ℝ} (hσ : 0 ≤ σ) :
    IsVerticalLogWeight Complex.digamma σ where
  tendsto_norm_atTop := by
    refine tendsto_atTop_mono' atTop ?_ (re_digamma_vertical_tendsto_atTop hσ)
    filter_upwards with t
    exact Complex.re_le_norm _
  tendsto_pow_div_pow := fun b _ hd => tendsto_digamma_pow_div_pow_vertical hσ b hd

/-! ### The ordering for a general weight -/

/-- **A positive power of `Γ` annihilates every weighted monomial.** -/
theorem tendsto_pow_mul_weight_pow_mul_Gamma_pow {w : ℂ → ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hw : IsVerticalLogWeight w σ) (n b k : ℕ) (hk : 0 < k) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ n *
        (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b *
        (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ k) atTop (nhds 0) := by
  have h1 := tendsto_pow_mul_Gamma_pow hσ (n + 1) k hk
  have h2 := hw.tendsto_pow_div_pow b 1 one_pos
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

/-- Weighted monomials are ordered lexicographically on a vertical line. -/
theorem tendsto_weightedMonomial_ratio_zero {w : ℂ → ℂ} {σ : ℝ} (_hσ : 0 < σ)
    (hw : IsVerticalLogWeight w σ) {a₁ b₁ a₂ b₂ : ℕ}
    (hlex : a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)) :
    Tendsto (fun t : ℝ =>
        (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
          (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₁) /
        (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂ *
          (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₂)) atTop (nhds 0) := by
  have hwtop := hw.tendsto_norm_atTop
  rcases hlex with hlt | ⟨heq, hblt⟩
  · obtain ⟨d, hd, hdpos⟩ : ∃ d, a₂ = a₁ + d ∧ 0 < d := ⟨a₂ - a₁, by omega, by omega⟩
    have hkey := hw.tendsto_pow_div_pow b₁ d hdpos
    rw [tendsto_zero_iff_norm_tendsto_zero] at hkey ⊢
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hkey
    filter_upwards [eventually_gt_atTop (0 : ℝ), hwtop.eventually_ge_atTop 1] with t ht hw1
    have hs : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_norm_vertical σ ht.le
    have hspos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := lt_of_lt_of_le ht hs
    have hwb : (1 : ℝ) ≤ ‖w ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b₂ := one_le_pow₀ hw1
    simp only [norm_div, norm_mul, norm_pow, hd, pow_add]
    rw [show ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d *
        ‖w ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b₂
        = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ a₁ *
          (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d *
            ‖w ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ b₂) from by ring]
    rw [mul_div_mul_left _ _ (ne_of_gt (pow_pos hspos a₁))]
    exact div_le_div₀ (by positivity) le_rfl (pow_pos hspos d)
      (le_mul_of_one_le_right (by positivity) hwb)
  · subst heq
    obtain ⟨e, he, hepos⟩ : ∃ e, b₂ = b₁ + e ∧ 0 < e := ⟨b₂ - b₁, by omega, by omega⟩
    have hinv : Tendsto (fun t : ℝ =>
        ((w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ e)⁻¹) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (g := fun t : ℝ => ‖w ((σ : ℂ) + (t : ℂ) * Complex.I)‖⁻¹)
        (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
      · filter_upwards [hwtop.eventually_ge_atTop 1] with t hw1
        rw [norm_inv, norm_pow]
        have hpos : (0 : ℝ) < ‖w ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le one_pos hw1
        rw [inv_le_inv₀ (by positivity) hpos]
        exact le_self_pow₀ hw1 hepos.ne'
      · exact tendsto_inv_atTop_zero.comp hwtop
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ), hwtop.eventually_ge_atTop 1] with t ht hw1
    have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [h] at him
      simp only [Complex.zero_im] at him
      linarith
    have hwne : w ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw1
      linarith
    rw [he, pow_add]
    field_simp

/-! ### Weighted Gamma monomials and the collapse -/

/-- A Gamma-rational coefficient weighted by `s^a · w(s)^b`. -/
def GammaRationalDatum.weightedFn (D : GammaRationalDatum) (w : ℂ → ℂ) (a b : ℕ) (s : ℂ) : ℂ :=
  s ^ a * (w s) ^ b * D.fn s

theorem weightedFn_ratio_eq (D₁ D₂ : GammaRationalDatum) (w : ℂ → ℂ) (a₁ b₁ a₂ b₂ : ℕ) (s : ℂ) :
    D₁.weightedFn w a₁ b₁ s / D₂.weightedFn w a₂ b₂ s
      = (s ^ a₁ * (w s) ^ b₁) / (s ^ a₂ * (w s) ^ b₂) * (D₁.fn s / D₂.fn s) := by
  simp only [GammaRationalDatum.weightedFn]
  rw [div_mul_div_comm]

theorem weightedFn_eventually_ne_zero (D : GammaRationalDatum) {w : ℂ → ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hw : IsVerticalLogWeight w σ) (a b : ℕ) :
    ∀ᶠ t : ℝ in atTop, D.weightedFn w a b ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), hw.tendsto_norm_atTop.eventually_ge_atTop 1,
    gammaRationalDatum_fn_eventually_ne_zero D hσ] with t ht hw1 hfn
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  have hwne : w ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    linarith
  simp only [GammaRationalDatum.weightedFn]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hsne) (pow_ne_zero _ hwne)) hfn

/-- **Strict subordination sends the weighted ratio to zero.** -/
theorem weightedRatio_tendsto_zero_of_subordinate (D₁ D₂ : GammaRationalDatum) {w : ℂ → ℂ}
    (a₁ b₁ a₂ b₂ : ℕ) (hsub : StrictlySubordinateAt D₁ D₂ a₁ b₁ a₂ b₂)
    {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) :
    Tendsto (fun t : ℝ =>
        D₁.weightedFn w a₁ b₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.weightedFn w a₂ b₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  rcases hsub with ⟨n, hnpos, hn⟩ | ⟨heq, hlex⟩
  · -- a strictly larger Gamma valuation absorbs the whole weighted monomial
    have hnum := tendsto_pow_mul_weight_pow_mul_Gamma_pow hσ hw a₁ b₁ n hnpos
    have hg0 : Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
        atTop (nhds 0) := Gamma_vertical_tendsto_zero hσ
    have hunit : Tendsto (fun t : ℝ =>
        (D₁.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
          D₂.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))) /
        (D₁.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
          D₂.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
        atTop (nhds ((D₁.numUnit.eval 0 * D₂.denUnit.eval 0) /
          (D₁.denUnit.eval 0 * D₂.numUnit.eval 0))) :=
      ((((Polynomial.continuous D₁.numUnit).tendsto 0).mul
        ((Polynomial.continuous D₂.denUnit).tendsto 0)).div
        (((Polynomial.continuous D₁.denUnit).tendsto 0).mul
          ((Polynomial.continuous D₂.numUnit).tendsto 0))
        (mul_ne_zero D₁.denUnit_ne D₂.numUnit_ne)).comp hg0
    have hmodel : Tendsto (fun t : ℝ =>
        (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
            (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₁ *
            (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n) *
          ((D₁.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
              D₂.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))) /
            (D₁.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
              D₂.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))) *
          ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂ *
            (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₂)⁻¹)) atTop (nhds 0) := by
      have hprod := hnum.mul hunit
      rw [zero_mul] at hprod
      rw [tendsto_zero_iff_norm_tendsto_zero] at hprod ⊢
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hprod
      filter_upwards [eventually_ge_atTop (1 : ℝ),
        hw.tendsto_norm_atTop.eventually_ge_atTop 1] with t ht hw1
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
      have hs1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
        le_trans ht (le_norm_vertical σ ht0.le)
      have hinv : ‖((((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂ *
          (w ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₂)⁻¹)‖ ≤ 1 := by
        rw [norm_inv, norm_mul, norm_pow, norm_pow]
        rw [inv_le_one₀ (by positivity)]
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs1) (one_le_pow₀ hw1)
      rw [norm_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hinv (norm_nonneg _)) (le_of_eq (mul_one _))
    refine hmodel.congr' ?_
    have hgne : ∀ᶠ t : ℝ in atTop, Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      (Gamma_vertical_tendsto_nhdsWithin_zero hσ).eventually self_mem_nhdsWithin
    have hunits : ∀ (R : Polynomial ℂ), R.eval 0 ≠ 0 →
        ∀ᶠ t : ℝ in atTop, R.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
      intro R hR
      exact (((Polynomial.continuous R).tendsto 0).comp hg0).eventually (isOpen_ne.mem_nhds hR)
    filter_upwards [hgne, hunits D₁.denUnit D₁.denUnit_ne, hunits D₂.numUnit D₂.numUnit_ne,
      hunits D₂.denUnit D₂.denUnit_ne] with t hg h1 h2 h3
    have hfac := gammaRational_ratio_eq (g := Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      hg D₁.numUnit D₁.denUnit D₂.numUnit D₂.denUnit
      D₁.numOrder D₁.denOrder D₂.numOrder D₂.denOrder n hn h1 h2 h3
    rw [weightedFn_ratio_eq]
    simp only [GammaRationalDatum.fn, GammaRationalDatum.num, GammaRationalDatum.den]
    rw [hfac]
    field_simp
  · -- equal Gamma valuation: the weighted monomials decide
    have hratio := gammaRationalDatum_ratio_vertical_tendsto D₁ D₂ 0 (by omega) hσ
    rw [pow_zero, one_mul] at hratio
    have hmon := tendsto_weightedMonomial_ratio_zero hσ hw hlex
    have hmul := hmon.mul hratio
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards with t
    exact (weightedFn_ratio_eq D₁ D₂ w a₁ b₁ a₂ b₂ _).symm

/-- **Unconditional finite-phase collapse against weighted Gamma monomials.**  With a weight that is
a logarithmic scale on every vertical line of positive abscissa — `Complex.log` and `Complex.digamma`
both are — a holomorphic Bohr almost-periodic `f` satisfying a finite differential relation whose
coefficients are the monomials `s^{a α} w(s)^{b α}·P_α(Γ)/Q_α(Γ)`, with the coefficient at `β`
strictly dominating all the others, has `M_β(f) = 0` identically on the strip. -/
theorem weighted_strip_relation_dominant_monomial_eq_zero
    {ι : Type*} [DecidableEq ι] (E : Finset ι) {w : ℂ → ℂ}
    (hw : ∀ x : ℝ, 0 < x → IsVerticalLogWeight w x)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → GammaRationalDatum) (a b : ι → ℕ) (β : ι) (hβ : β ∈ E)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (a α) (b α) (a β) (b β))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (D α).weightedFn w (a α) (b α) s * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 := by
  classical
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse E hη f exps
      (fun α => (D α).weightedFn w (a α) (b α)) β hβ hf hap hrel
  intro z₀ hz₀
  have hzre : 0 < z₀.re := by
    have habs : |z₀.re - σ| < η := hz₀
    have hlt := (abs_lt.mp habs).1
    linarith
  have hwz := hw z₀.re hzre
  have hFβ : ∀ᶠ l in atTop,
      (D β).weightedFn w (a β) (b β) (z₀ + (T l : ℂ) * Complex.I) ≠ 0 :=
    eventually_vertical_along_returns (p := fun s => (D β).weightedFn w (a β) (b β) s ≠ 0)
      (z₀ := z₀) (weightedFn_eventually_ne_zero (D β) hzre hwz (a β) (b β)) hT
  have hcoeff : ∀ α ∈ E, Tendsto
      (fun l => (D α).weightedFn w (a α) (b α) (z₀ + (T l : ℂ) * Complex.I) /
        (D β).weightedFn w (a β) (b β) (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (if α = β then (1 : ℂ) else 0)) := by
    intro α hα
    rcases eq_or_ne α β with hab | hab
    · subst hab
      have hone : Tendsto
          (fun l => (D α).weightedFn w (a α) (b α) (z₀ + (T l : ℂ) * Complex.I) /
            (D α).weightedFn w (a α) (b α) (z₀ + (T l : ℂ) * Complex.I))
          atTop (nhds (1 : ℂ)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hFβ] with l hl
        exact (div_self hl).symm
      simpa using hone
    · have hzero := weightedRatio_tendsto_zero_of_subordinate (D α) (D β) (a α) (b α) (a β) (b β)
        (hdom α hα hab) hzre hwz
      simpa [hab] using tendsto_vertical_along_returns
        (F := fun s => (D α).weightedFn w (a α) (b α) s / (D β).weightedFn w (a β) (b β) s)
        (z₀ := z₀) hzero hT
  have hcollapse := hmain z₀ hz₀ (fun α => if α = β then (1 : ℂ) else 0) hFβ hcoeff
  have hred := Finset.sum_eq_single_of_mem β hβ
    (f := fun α : ι => (if α = β then (1 : ℂ) else 0) * diffMonomial f (exps α) z₀)
    (by
      intro c _ hc
      simp [hc])
  have hzero := hcollapse.1
  rw [hred] at hzero
  simpa using hzero

/-- **The digamma instance.**  The collapse holds for coefficients `s^a ψ(s)^b · P(Γ)/Q(Γ)`, i.e. for
monomials of the actual digamma field. -/
theorem digamma_strip_relation_dominant_monomial_eq_zero
    {ι : Type*} [DecidableEq ι] (E : Finset ι)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → GammaRationalDatum) (a b : ι → ℕ) (β : ι) (hβ : β ∈ E)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (a α) (b α) (a β) (b β))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (D α).weightedFn Complex.digamma (a α) (b α) s * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 :=
  weighted_strip_relation_dominant_monomial_eq_zero E
    (fun _x hx => isVerticalLogWeight_digamma hx.le) hη hση f exps D a b β hβ hdom hf hap hrel

end

end GaloisForLFunctions
