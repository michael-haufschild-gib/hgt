import GaloisForLFunctions.SquareRootThreshold.AttainedDepthIsVisible

/-!
# The depth-deficit transform replaces the gap

Fix a bump `b` and let `q_t` be the pair weights of the zeros right of the critical line. Let
`½ + D` be the largest real part among the zeros of nonzero weight, attained on the top level.
The zeros below it may accumulate at depth `D`; there need not be a gap. They enter the off-line
sum `Σ_t q_t e^{(δ_t + iγ_t)v}` only through the **depth-deficit transform**

`G(v) = Σ_{δ_t < D} |q_t| e^{−(D − δ_t)v}`,

which is antitone (`depthDeficit_anti`) and relaxes to `0` (`tendsto_depthDeficit`). With a gap
`g` it is at most `e^{−gv} Σ|q_t|` (`depthDeficit_le_of_gap`), which gives back the logarithmic
aperture of finite off-line sets.

**The level split** (`norm_offLineSum_sub_level_le`). For a finite part `T₀` of the top level,
the off-line sum at lag `v` is its part over `T₀`, of size `e^{Dv}`, up to an error of at most
`e^{Dv}(τ + G(v))`, where `τ` is the weight of the level outside `T₀` (`levelTail`).
`InghamWindowsForAnAttainedTopLevel` turns this into visibility in every window of fixed length.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The depth-deficit transform `G(v) = Σ_{Re t < r} |q_t| e^{−(r − Re t)v}` of the zeros right of
the line strictly below the level `Re t = r`. -/
def depthDeficit (Z : ZeroConfig) (b : ℝ → ℂ) (r v : ℝ) : ℝ :=
  ∑' t : rightZeros Z, if (t : ℂ).re < r then
    ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v) else 0

theorem summable_norm_offLineWeight (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Summable fun t : rightZeros Z => ‖offLineWeight b (Z.mult t) t‖ := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  have hF : Summable (Z.carrier.indicator (lagTerm Z b 0)) :=
    summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs 0)
  have hsum0 : Summable fun t : rightZeros Z => lagTerm Z b 0 t :=
    summable_subtype_iff_indicator.mpr (summable_indicator_of_subset (fun z hz => hz.1) hF)
  refine hsum0.norm.congr fun t => ?_
  rw [lagTerm_eq_weight hb.continuous hbc, norm_mul, norm_mul]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Real.exp_zero, Complex.ofReal_one,
    norm_one, mul_one]

theorem depthDeficit_term_le {Z : ZeroConfig} {b : ℝ → ℂ} {r v : ℝ} (hv : 0 ≤ v)
    (t : rightZeros Z) :
    0 ≤ (if (t : ℂ).re < r then
      ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v) else 0) ∧
    (if (t : ℂ).re < r then
      ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v) else 0) ≤
      ‖offLineWeight b (Z.mult t) t‖ := by
  split_ifs with h
  · exact ⟨by positivity, mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv))⟩
  · exact ⟨le_rfl, norm_nonneg _⟩

theorem summable_depthDeficit (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Summable fun t : rightZeros Z => if (t : ℂ).re < r then
      ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v) else 0 :=
  Summable.of_nonneg_of_le (fun t => (depthDeficit_term_le hv t).1)
    (fun t => (depthDeficit_term_le hv t).2) (summable_norm_offLineWeight Z hZ hb hbs)

/-- `G` is antitone in the lag. -/
theorem depthDeficit_anti (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r : ℝ) {V v : ℝ} (hV : 0 ≤ V)
    (hVv : V ≤ v) : depthDeficit Z b r v ≤ depthDeficit Z b r V := by
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_depthDeficit Z hZ hb hbs r (hV.trans hVv))
    (summable_depthDeficit Z hZ hb hbs r hV)
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hVv (by linarith))) (norm_nonneg _)
  · exact le_rfl

/-- **`G` relaxes to `0`.** -/
theorem tendsto_depthDeficit (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r : ℝ) :
    Tendsto (fun v => depthDeficit Z b r v) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : rightZeros Z => 0)
    (f := fun v (t : rightZeros Z) => if (t : ℂ).re < r then
      ‖offLineWeight b (Z.mult t) t‖ * Real.exp (((t : ℂ).re - r) * v) else 0)
    (summable_norm_offLineWeight Z hZ hb hbs) (fun t => ?_)
    (eventually_ge_atTop 0 |>.mono fun v hv t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (depthDeficit_term_le hv t).1]
      exact (depthDeficit_term_le hv t).2)
  · simpa [depthDeficit] using h
  · split_ifs with ht
    · have hexp : Tendsto (fun v => Real.exp (((t : ℂ).re - r) * v)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      simpa using hexp.const_mul ‖offLineWeight b (Z.mult t) t‖
    · exact tendsto_const_nhds

/-- **The gap bound.** If every zero of nonzero weight below the level `r` has real part at most
`r − g`, then `G(v) ≤ e^{−gv} Σ|q_t|`. -/
theorem depthDeficit_le_of_gap (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {r g v : ℝ} (hv : 0 ≤ v)
    (hgap : ∀ t ∈ rightZeros Z, t.re < r → offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ r - g) :
    depthDeficit Z b r v ≤
      Real.exp (-(g * v)) * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ := by
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_depthDeficit Z hZ hb hbs r hv)
    ((summable_norm_offLineWeight Z hZ hb hbs).mul_left _)
  split_ifs with h
  · by_cases hq : offLineWeight b (Z.mult t) t = 0
    · rw [hq, norm_zero, zero_mul, mul_zero]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have := hgap t t.2 h hq
    nlinarith
  · positivity

/-- The weight `τ = Σ |q_t|` of the zeros right of the line on the level `Re t = r` outside `T₀`. -/
def levelTail (Z : ZeroConfig) (b : ℝ → ℂ) (r : ℝ) (T₀ : Finset ℂ) : ℝ :=
  ∑' t : rightZeros Z, if (t : ℂ).re = r ∧ (t : ℂ) ∉ T₀ then ‖offLineWeight b (Z.mult t) t‖ else 0

theorem summable_levelTail (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (r : ℝ) (T₀ : Finset ℂ) :
    Summable fun t : rightZeros Z => if (t : ℂ).re = r ∧ (t : ℂ) ∉ T₀ then
      ‖offLineWeight b (Z.mult t) t‖ else 0 :=
  Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
    (fun _ => by split_ifs <;> simp) (summable_norm_offLineWeight Z hZ hb hbs)

/-- **The level split.** Let every zero of nonzero weight satisfy `Re t ≤ Re t₀`, and let `T₀` be a
finite set of zeros right of the line on the level `Re t = Re t₀`. At lag `v ≥ 0` the off-line
sum differs from its part over `T₀` by at most `e^{Dv}(τ + G(v))`, `D = Re t₀ − ½`, with `τ` the
weight of the level outside `T₀`. -/
theorem norm_offLineSum_sub_level_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ t₀.re)
    {T₀ : Finset ℂ} (hT₀ : ∀ t ∈ T₀, t ∈ rightZeros Z ∧ t.re = t₀.re) {v : ℝ} (hv : 0 ≤ v) :
    ‖∑' t : rightZeros Z, offLineWeight b (Z.mult t) t *
        (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v) -
      ∑ t ∈ T₀, offLineWeight b (Z.mult t) t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) *
        cexp (I * t.im * v)‖ ≤
      Real.exp ((t₀.re - 1 / 2) * v) * (levelTail Z b t₀.re T₀ + depthDeficit Z b t₀.re v) := by
  classical
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
  set F : ℂ → ℂ := fun t => q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v)
    with hF
  have hE : ∀ t : ℂ, ‖cexp (I * t.im * v)‖ = 1 := fun t => by
    rw [show I * (t.im : ℂ) * (v : ℂ) = ((t.im * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnF : ∀ t : ℂ, ‖F t‖ = ‖q t‖ * Real.exp ((t.re - 1 / 2) * v) := fun t => by
    rw [hF, norm_mul, norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hqs := summable_norm_offLineWeight Z hZ hb hbs
  have hFs : Summable fun t : rightZeros Z => F t := by
    refine Summable.of_norm_bounded (hqs.mul_right (Real.exp ((t₀.re - 1 / 2) * v))) fun t => ?_
    rw [hnF]
    by_cases h0 : q t = 0
    · rw [h0, norm_zero, zero_mul]
      positivity
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (by linarith [htop t t.2 h0]) hv)) (norm_nonneg _)
  have hIs : Summable fun t : rightZeros Z => if (t : ℂ) ∈ T₀ then F t else 0 :=
    Summable.of_norm_bounded hFs.norm fun t => by split_ifs <;> simp
  have hlevel : ∑' t : rightZeros Z, (if (t : ℂ) ∈ T₀ then F t else 0) = ∑ t ∈ T₀, F t := by
    rw [tsum_subtype (rightZeros Z) fun z => if z ∈ T₀ then F z else 0,
      tsum_eq_sum (s := T₀) fun z hz => by simp [Set.indicator, hz]]
    exact Finset.sum_congr rfl fun z hz => by simp [Set.indicator_of_mem (hT₀ z hz).1, hz]
  have hτ := summable_levelTail Z hZ hb hbs t₀.re T₀
  have hG := summable_depthDeficit Z hZ hb hbs t₀.re hv
  have hterm : ∀ t : rightZeros Z, ‖F t - (if (t : ℂ) ∈ T₀ then F t else 0)‖ ≤
      Real.exp ((t₀.re - 1 / 2) * v) * ((if (t : ℂ).re = t₀.re ∧ (t : ℂ) ∉ T₀ then ‖q t‖ else 0) +
        (if (t : ℂ).re < t₀.re then ‖q t‖ * Real.exp (((t : ℂ).re - t₀.re) * v) else 0)) :=
      fun t => by
    have ha : 0 ≤ (if (t : ℂ).re = t₀.re ∧ (t : ℂ) ∉ T₀ then ‖q t‖ else 0) := by
      split_ifs <;> positivity
    have hg := (depthDeficit_term_le (Z := Z) (b := b) (r := t₀.re) hv t).1
    have hR := mul_nonneg (Real.exp_pos ((t₀.re - 1 / 2) * v)).le (add_nonneg ha hg)
    by_cases hT : (t : ℂ) ∈ T₀
    · rw [if_pos hT, sub_self, norm_zero]
      exact hR
    rw [if_neg hT, sub_zero]
    by_cases h0 : q t = 0
    · have : ‖F t‖ = 0 := by rw [hnF, h0, norm_zero, zero_mul]
      rw [this]
      exact hR
    rw [hnF]
    rcases (htop t t.2 h0).lt_or_eq with hlt | heq
    · rw [if_neg fun h => hlt.ne h.1, zero_add, if_pos hlt, ← mul_assoc,
        mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
      exact le_of_eq (by ring_nf)
    · rw [if_pos ⟨heq, hT⟩, if_neg heq.not_lt, add_zero, heq, mul_comm]
  rw [← hlevel, ← hFs.tsum_sub hIs, levelTail, depthDeficit, ← hτ.tsum_add hG, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm ((hτ.add hG).mul_left _)
  · exact Summable.tsum_le_tsum hterm
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm ((hτ.add hG).mul_left _))
      ((hτ.add hG).mul_left _)

end GaloisForLFunctions.SquareRootThreshold
