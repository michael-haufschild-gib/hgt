import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.StateProductMultiplicity
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSideIsNormalisedAtTheLeftEnd
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift

/-!
# Every critical state sees a left zero

For the critical half-line ground state `F`, right-half-plane zero-freeness of `L F` supplies a
pole of `stateMeromorphic W₀ F` at every shifted zero `ρ - 17/2` on or right of the critical line
(`Re ρ ≥ ½`), leaving open whether `L F` could vanish at every zero strictly left of the line
(`0 < Re ρ < ½`).

Pairing the two-point explicit formula `globalRemainder F (4 + it) - globalRemainder F (-4 + it)`
against the Cauchy-damped conjugate transform `(N²/(N² + t²)) L F(-4 - it)` and shifting the
divided-difference remainders far left yields, for every `N > 20`, the exact identity

  `-(a / 2π) ∫ (N²/(N² + t²)) |L F(-4 + it)|² dt`
  `= (N / 2) L F(N - 4) B F(-N + 4) + Σ_c (N²/(N² - (z_c - 4)²)) L F(z_c) L F(-z_c)`.

The left side is bounded above by a strictly negative constant independent of `N`; the boundary
term `(N / 2) L F(N - 4) B F(-N + 4)` tends to zero as `N → ∞` because `|F(u)| ≤ C e^u` bounds
`N |L F(N - 4)|` while `B F(-N + 4) → 0`; and every critical-line zero `z_c = iγ` contributes a
nonnegative real part since `L F(iγ) L F(-iγ) = |L F(iγ)|² ≥ 0` and `Re(N² - (iγ - 4)²) =
N² - 16 + γ² > 0`. Hence some off-line zero pair satisfies `L F(z_c) L F(-z_c) ≠ 0`, and reflecting
into the left half-strip produces a zero with `-½ < Re z < 0` and `L F(z) ≠ 0`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Elementary Cauchy-pair vertical integrals -/

private theorem integral_scaled_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    ∫ u : ℝ, a / (a ^ 2 + u ^ 2) = (if 0 < a then 1 else -1) * Real.pi := by
  have ha2 : 0 < |a| := abs_pos.mpr ha
  have hpt : (fun u : ℝ => a / (a ^ 2 + u ^ 2)) =
      fun u : ℝ => (a / |a| ^ 2) * (1 + (|a|⁻¹ * u) ^ 2)⁻¹ := by
    funext u
    have hsq : |a| ^ 2 = a ^ 2 := sq_abs a
    field_simp [ha, ha2.ne']
    nlinarith [hsq]
  rw [hpt, integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹)
    (inv_ne_zero ha2.ne')]
  simp only [inv_inv, abs_abs, smul_eq_mul, integral_univ_inv_one_add_sq]
  split_ifs with hpos
  · rw [abs_of_pos hpos]
    field_simp [hpos.ne']
  · have hneg : a < 0 := lt_of_le_of_ne (not_lt.mp hpos) ha
    rw [abs_of_neg hneg]
    field_simp [hneg.ne']

private theorem integrable_scaled_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    Integrable fun u : ℝ => a / (a ^ 2 + u ^ 2) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hdom : Integrable fun u : ℝ => (|a| / min (a ^ 2) 1) * (1 + u ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hm : 0 < min (a ^ 2) 1 := lt_min ha2 one_pos
  refine hdom.mono' (by
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.div (continuous_const.add (continuous_pow 2))
      fun u => by nlinarith [sq_nonneg u]) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by nlinarith [sq_nonneg u] : 0 < a ^ 2 + u ^ 2)]
  have hle : min (a ^ 2) 1 * (1 + u ^ 2) ≤ a ^ 2 + u ^ 2 := by
    have h1 : min (a ^ 2) 1 ≤ a ^ 2 := min_le_left _ _
    have h2 : min (a ^ 2) 1 ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg u]
  rw [div_mul_eq_mul_div, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (abs_nonneg a) hm hle

private theorem integrable_odd_diff_cauchy {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable fun u : ℝ => u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  set m := min (min (a ^ 2) (b ^ 2)) 1
  have hm : 0 < m := lt_min (lt_min ha2 hb2) one_pos
  have hdom : Integrable fun u : ℝ => (|b ^ 2 - a ^ 2| / m ^ 2) * (1 + u ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hcont : Continuous fun u : ℝ => u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) :=
    continuous_id.mul ((continuous_const.add (continuous_pow 2)).inv₀
      (fun u => by nlinarith [sq_nonneg u]) |>.sub
      ((continuous_const.add (continuous_pow 2)).inv₀ (fun u => by nlinarith [sq_nonneg u])))
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have hda : 0 < a ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hdb : 0 < b ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hpt : u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) =
      u * (b ^ 2 - a ^ 2) / ((a ^ 2 + u ^ 2) * (b ^ 2 + u ^ 2)) := by
    field_simp [hda.ne', hdb.ne']
  rw [hpt, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (mul_pos hda hdb)]
  have hma : m * (1 + u ^ 2) ≤ a ^ 2 + u ^ 2 := by
    have h1 : m ≤ a ^ 2 := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg u]
  have hmb : m * (1 + u ^ 2) ≤ b ^ 2 + u ^ 2 := by
    have h1 : m ≤ b ^ 2 := (min_le_left _ _).trans (min_le_right _ _)
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg u]
  have hprod : m ^ 2 * (1 + u ^ 2) ^ 2 ≤ (a ^ 2 + u ^ 2) * (b ^ 2 + u ^ 2) := by
    calc m ^ 2 * (1 + u ^ 2) ^ 2 = (m * (1 + u ^ 2)) * (m * (1 + u ^ 2)) := by ring
      _ ≤ (a ^ 2 + u ^ 2) * (b ^ 2 + u ^ 2) :=
        mul_le_mul hma hmb (by positivity) hda.le
  have hu : |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hnum : |u| * |b ^ 2 - a ^ 2| * (m ^ 2 * (1 + u ^ 2)) ≤
      |b ^ 2 - a ^ 2| * (m ^ 2 * (1 + u ^ 2) ^ 2) := by
    have : |u| * (1 + u ^ 2) ≤ (1 + u ^ 2) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hu (by positivity)
    nlinarith [mul_nonneg (abs_nonneg (b ^ 2 - a ^ 2)) (sq_nonneg m)]
  rw [div_mul_eq_mul_div, ← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hda hdb)
    (mul_pos (sq_pos_of_pos hm) (by positivity))]
  calc |u| * |b ^ 2 - a ^ 2| * (m ^ 2 * (1 + u ^ 2))
      ≤ |b ^ 2 - a ^ 2| * (m ^ 2 * (1 + u ^ 2) ^ 2) := hnum
    _ ≤ |b ^ 2 - a ^ 2| * ((a ^ 2 + u ^ 2) * (b ^ 2 + u ^ 2)) :=
      mul_le_mul_of_nonneg_left hprod (abs_nonneg _)

private theorem integral_odd_diff_cauchy_eq_zero (a b : ℝ) :
    (∫ u : ℝ, u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹)) = 0 := by
  have h := integral_comp_neg (fun u : ℝ => u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹))
  have hneg : (fun u : ℝ => (-u) * ((a ^ 2 + (-u) ^ 2)⁻¹ - (b ^ 2 + (-u) ^ 2)⁻¹)) =
      fun u : ℝ => -(u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹)) := by
    funext u; ring
  rw [hneg, integral_neg] at h
  linarith

/-- Exact vertical integral of a horizontal-shift Cauchy resolvent pair: `2π` when the line
separates the poles (`p₀.re < σ < p₀.re + K`), and `0` when both poles lie strictly right of `σ`. -/
private theorem integral_cauchy_pair_vertical {p₀ : ℂ} {K σ : ℝ} (hK : 0 < K)
    (h1 : p₀.re ≠ σ) (h2 : p₀.re + K ≠ σ) :
    (∫ t : ℝ, ((((σ : ℂ) + t * I) - p₀)⁻¹ - (((σ : ℂ) + t * I) - (p₀ + K))⁻¹)) =
      if p₀.re < σ ∧ σ < p₀.re + K then (2 * Real.pi : ℂ)
      else if σ < p₀.re then 0
      else -(2 * Real.pi : ℂ) := by
  set a := σ - p₀.re
  set b := σ - (p₀.re + K)
  have ha : a ≠ 0 := sub_ne_zero.mpr h1.symm
  have hb : b ≠ 0 := sub_ne_zero.mpr h2.symm
  have hshift : (∫ t : ℝ, ((((σ : ℂ) + t * I) - p₀)⁻¹ - (((σ : ℂ) + t * I) - (p₀ + K))⁻¹)) =
      ∫ u : ℝ, (((a : ℂ) + u * I)⁻¹ - ((b : ℂ) + u * I)⁻¹) := by
    rw [← integral_sub_right_eq_self _ p₀.im]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have e1 : ((σ : ℂ) + (t + p₀.im : ℝ) * I) - p₀ = (a : ℂ) + t * I := by
      apply Complex.ext <;> simp [a]; ring
    have e2 : ((σ : ℂ) + (t + p₀.im : ℝ) * I) - (p₀ + K) = (b : ℂ) + t * I := by
      apply Complex.ext <;> simp [b]; ring
    rw [e1, e2]
  rw [hshift]
  have hdecomp : (fun u : ℝ => (((a : ℂ) + u * I)⁻¹ - ((b : ℂ) + u * I)⁻¹)) =
      fun u : ℝ => ((a / (a ^ 2 + u ^ 2) - b / (b ^ 2 + u ^ 2) : ℝ) : ℂ) -
        I * ((u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) : ℝ) : ℂ) := by
    funext u
    have hna : Complex.normSq ((a : ℂ) + u * I) = a ^ 2 + u ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    have hnb : Complex.normSq ((b : ℂ) + u * I) = b ^ 2 + u ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    have hda : 0 < a ^ 2 + u ^ 2 := by nlinarith [sq_pos_of_ne_zero ha, sq_nonneg u]
    have hdb : 0 < b ^ 2 + u ^ 2 := by nlinarith [sq_pos_of_ne_zero hb, sq_nonneg u]
    rw [Complex.inv_def, Complex.inv_def, hna, hnb]
    apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring
  have hintR : Integrable fun u : ℝ =>
      ((a / (a ^ 2 + u ^ 2) - b / (b ^ 2 + u ^ 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp_integrable
      ((integrable_scaled_inv_sq_add_sq ha).sub (integrable_scaled_inv_sq_add_sq hb))
  have hintI : Integrable fun u : ℝ =>
      I * ((u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp_integrable (integrable_odd_diff_cauchy ha hb)).const_mul I
  rw [hdecomp, integral_sub hintR hintI, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_odd_diff_cauchy_eq_zero, Complex.ofReal_zero, mul_zero,
    sub_zero, integral_sub (integrable_scaled_inv_sq_add_sq ha) (integrable_scaled_inv_sq_add_sq hb),
    integral_scaled_inv_sq_add_sq ha, integral_scaled_inv_sq_add_sq hb]
  split_ifs with hsep hlt
  · have ha_pos : 0 < a := by dsimp [a]; linarith [hsep.1]
    have hb_neg : ¬ 0 < b := by dsimp [b]; linarith [hsep.2]
    rw [if_pos ha_pos, if_neg hb_neg]; push_cast; ring
  · have ha_neg : ¬ 0 < a := by dsimp [a]; linarith
    have hb_neg : ¬ 0 < b := by dsimp [b]; linarith
    rw [if_neg ha_neg, if_neg hb_neg]; push_cast; ring
  · have ha_pos : 0 < a := by
      rcases lt_or_gt_of_ne h1 with hp | hp
      · dsimp [a]; linarith
      · exact absurd hp hlt
    have hb_pos : 0 < b := by
      rcases lt_or_gt_of_ne h2 with hp2 | hp2
      · dsimp [b]; linarith
      · exfalso; exact hsep ⟨by dsimp [a] at ha_pos; linarith, hp2⟩
    rw [if_pos ha_pos, if_pos hb_pos]; push_cast; ring

/-! ### One-pole vertical residue evaluation by `dslope` -/

private lemma norm_sub_ge_of_im_large {s p : ℂ} (h : 2 * (1 + |p.im|) ≤ 1 + |s.im|) :
    (1 + |s.im|) / 2 ≤ ‖s - p‖ := by
  have him : |s.im| - |p.im| ≤ |(s - p).im| := by
    rw [Complex.sub_im]; exact abs_sub_abs_le_abs_sub s.im p.im
  have hle : |(s - p).im| ≤ ‖s - p‖ := Complex.abs_im_le_norm (s - p)
  linarith

/-- If `G` is holomorphic on `Re s < σ₁` (`σ₀ < σ₁`), decays as `B / (1 + |Im s|)` on `Re s ≤ σ₀`,
and satisfies `‖G(-M + it)‖ ≤ b(M) / (1 + |t|)` with `b(M) → 0` as `M → ∞`, then at any simple
pole `p₀` strictly left of `σ₀` the vertical integral of `G(s) / (s - p₀)` along `Re s = σ₀` is
`2π G(p₀)`. -/
private theorem integral_vertical_one_pole_left {G : ℂ → ℂ} {σ₀ σ₁ : ℝ} {p₀ : ℂ}
    (hσ : σ₀ < σ₁) (hp₀ : p₀.re < σ₀)
    (hdiff : ∀ s : ℂ, s.re < σ₁ → DifferentiableAt ℂ G s)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ s : ℂ, s.re ≤ σ₀ → ‖G s‖ ≤ B / (1 + |s.im|))
    {b : ℝ → ℝ} (hb0 : ∀ M, 0 ≤ b M) (hbtend : Tendsto b atTop (𝓝 0))
    (hbleft : ∀ M : ℝ, -σ₀ ≤ M → ∀ t : ℝ, ‖G ((-M : ℂ) + t * I)‖ ≤ b M / (1 + |t|)) :
    (∫ t : ℝ, G ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) - p₀)) =
      (2 * Real.pi : ℂ) * G p₀ := by
  set K : ℝ := σ₀ - p₀.re + 1
  have hK : 0 < K := by dsimp [K]; linarith
  set p₁ : ℂ := p₀ + K
  have hp₁re : p₁.re = σ₀ + 1 := by simp [p₁, K]; ring
  set R : ℂ → ℂ := fun s => dslope G p₀ s + G p₀ / (s - p₁)
  have hU : IsOpen {s : ℂ | s.re < σ₁} := isOpen_lt Complex.continuous_re continuous_const
  have hp₀U : {s : ℂ | s.re < σ₁} ∈ 𝓝 p₀ := hU.mem_nhds (hp₀.trans hσ)
  have hdslope_on : DifferentiableOn ℂ (dslope G p₀) {s : ℂ | s.re < σ₁} :=
    (differentiableOn_dslope hp₀U).mpr fun s hs => (hdiff s hs).differentiableWithinAt
  have hR_diff : ∀ s : ℂ, s.re ≤ σ₀ → DifferentiableAt ℂ R s := by
    intro s hs
    have hd1 : DifferentiableAt ℂ (dslope G p₀) s :=
      hdslope_on.differentiableAt (hU.mem_nhds (hs.trans_lt hσ))
    have hne1 : s - p₁ ≠ 0 := by
      intro he; have := congrArg Complex.re he; simp [hp₁re] at this; linarith
    exact hd1.add ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hne1)
  have hR_eq : ∀ s : ℂ, s ≠ p₀ → s ≠ p₁ →
      R s = G s / (s - p₀) - G p₀ * ((s - p₀)⁻¹ - (s - p₁)⁻¹) := by
    intro s h0 h1
    dsimp [R]
    rw [dslope_of_ne _ h0, slope_def_field]
    field_simp [sub_ne_zero.mpr h0, sub_ne_zero.mpr h1]
    ring
  have hshift : ∀ M : ℝ, max (-p₀.re + 1) (-σ₀) ≤ M →
      (∫ t : ℝ, R ((σ₀ : ℂ) + t * I)) = ∫ t : ℝ, R ((-M : ℂ) + t * I) := by
    intro M hM
    have hM1 : -p₀.re + 1 ≤ M := (le_max_left _ _).trans hM
    have hM2 : -σ₀ ≤ M := (le_max_right _ _).trans hM
    set T₀ : ℝ := 2 * (1 + |p₀.im|)
    have hKpt : IsCompact (Icc (-M) σ₀ ×ˢ Icc (-T₀) T₀) := isCompact_Icc.prod isCompact_Icc
    have hRcont : ContinuousOn (fun q : ℝ × ℝ => R ((q.1 : ℂ) + q.2 * I))
        (Icc (-M) σ₀ ×ˢ Icc (-T₀) T₀) := by
      intro q hq
      exact ((hR_diff _ hq.1.2).continuousAt.comp
        (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I).continuousAt).continuousWithinAt
    obtain ⟨C₀, hC₀⟩ := hKpt.exists_bound_of_continuousOn hRcont
    have hC₀n := abs_nonneg C₀
    set Cfar : ℝ := 4 * B + 4 * ‖G p₀‖ * K
    set Ctot : ℝ := (|C₀| + 1) * (1 + T₀ ^ 2) + Cfar
    refine integral_vertical_line_shift_of_decay (Φ := R) (c₁ := σ₀) (c₂ := -M) (C := Ctot)
      (fun s hs => hR_diff s (by
        rcases Set.mem_uIcc.mp hs with h | h <;> linarith [h.1, h.2]))
      (fun s hs => ?_)
    have hs_mem : -M ≤ s.re ∧ s.re ≤ σ₀ := by
      rcases Set.mem_uIcc.mp hs with h | h <;> constructor <;> linarith [h.1, h.2]
    rcases le_or_gt |s.im| T₀ with hnear | hfar
    · have hqin : (s.re, s.im) ∈ Icc (-M) σ₀ ×ˢ Icc (-T₀) T₀ :=
        ⟨hs_mem, abs_le.mp hnear⟩
      have hval : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
      have hb1 : ‖R s‖ ≤ |C₀| := by
        rw [← hval]
        exact (hC₀ (s.re, s.im) hqin).trans (le_abs_self C₀)
      have hsim2 : 1 + s.im ^ 2 ≤ 1 + T₀ ^ 2 := by
        have := sq_le_sq.mpr (hnear.trans (le_abs_self T₀))
        linarith
      rw [le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2)]
      calc ‖R s‖ * (1 + s.im ^ 2) ≤ |C₀| * (1 + T₀ ^ 2) :=
            mul_le_mul hb1 hsim2 (by positivity) hC₀n
        _ ≤ Ctot := by dsimp [Ctot, Cfar]; nlinarith [norm_nonneg (G p₀)]
    · have h1 : 2 * (1 + |p₀.im|) ≤ 1 + |s.im| := by dsimp [T₀] at hfar; linarith
      have hp₁im : p₁.im = p₀.im := by simp [p₁]
      have h2 : 2 * (1 + |p₁.im|) ≤ 1 + |s.im| := by rwa [hp₁im]
      have hd0 : (1 + |s.im|) / 2 ≤ ‖s - p₀‖ := norm_sub_ge_of_im_large h1
      have hd1 : (1 + |s.im|) / 2 ≤ ‖s - p₁‖ := norm_sub_ge_of_im_large h2
      have hpos_im : 0 < (1 + |s.im|) / 2 := by positivity
      have hne0 : s ≠ p₀ := fun e => by rw [e, sub_self, norm_zero] at hd0; linarith
      have hne1 : s ≠ p₁ := fun e => by rw [e, sub_self, norm_zero] at hd1; linarith
      rw [hR_eq s hne0 hne1]
      have hpair : (s - p₀)⁻¹ - (s - p₁)⁻¹ = -(K : ℂ) / ((s - p₀) * (s - p₁)) := by
        have : p₁ - p₀ = (K : ℂ) := by dsimp [p₁]; ring
        field_simp [sub_ne_zero.mpr hne0, sub_ne_zero.mpr hne1]
        linear_combination -this
      rw [hpair]
      have hsq : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
      have ht1 : ‖G s / (s - p₀)‖ ≤ 4 * B / (1 + s.im ^ 2) := by
        rw [norm_div]
        have hG := hbound s hs_mem.2
        have : ‖G s‖ / ‖s - p₀‖ ≤ (B / (1 + |s.im|)) / ((1 + |s.im|) / 2) :=
          div_le_div₀ (by positivity) hG hpos_im hd0
        refine this.trans ?_
        rw [div_div, show (1 + |s.im|) * ((1 + |s.im|) / 2) = (1 + |s.im|) ^ 2 / 2 by ring,
          div_div_eq_mul_div, mul_comm B 2]
        exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq).trans
          (div_le_div_of_nonneg_right (by linarith) (by positivity))
      have ht2 : ‖G p₀ * (-(K : ℂ) / ((s - p₀) * (s - p₁)))‖ ≤
          4 * ‖G p₀‖ * K / (1 + s.im ^ 2) := by
        rw [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hK.le,
          norm_mul, ← mul_div_assoc]
        have hden : ((1 + |s.im|) / 2) * ((1 + |s.im|) / 2) ≤ ‖s - p₀‖ * ‖s - p₁‖ :=
          mul_le_mul hd0 hd1 hpos_im.le (norm_nonneg _)
        have hstep : ‖G p₀‖ * K / (‖s - p₀‖ * ‖s - p₁‖) ≤
            ‖G p₀‖ * K / (((1 + |s.im|) / 2) * ((1 + |s.im|) / 2)) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hpos_im hpos_im) hden
        refine hstep.trans ?_
        rw [show ((1 + |s.im|) / 2) * ((1 + |s.im|) / 2) = (1 + |s.im|) ^ 2 / 4 by ring,
          div_div_eq_mul_div]
        exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq).trans_eq (by ring)
      calc ‖G s / (s - p₀) - G p₀ * (-(K : ℂ) / ((s - p₀) * (s - p₁)))‖
          ≤ ‖G s / (s - p₀)‖ + ‖G p₀ * (-(K : ℂ) / ((s - p₀) * (s - p₁)))‖ := norm_sub_le _ _
        _ ≤ 4 * B / (1 + s.im ^ 2) + 4 * ‖G p₀‖ * K / (1 + s.im ^ 2) := add_le_add ht1 ht2
        _ = Cfar / (1 + s.im ^ 2) := by dsimp [Cfar]; ring
        _ ≤ Ctot / (1 + s.im ^ 2) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          dsimp [Ctot]; nlinarith [sq_nonneg T₀]
  -- Evaluate `∫ R((-M : ℂ) + t * I) dt → 0` as `M → ∞`
  have hR_left_tend : Tendsto (fun M : ℝ => ∫ t : ℝ, R ((-M : ℂ) + t * I)) atTop (𝓝 0) := by
    have hdom_tend : Tendsto (fun M : ℝ => b M * Real.pi) atTop (𝓝 0) := by
      simpa using hbtend.mul_const Real.pi
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop (max (-p₀.re + 1) (-σ₀)),
      (Metric.tendsto_nhds.mp hdom_tend) ε hε] with M hM hbM
    have hM1 : -p₀.re + 1 ≤ M := (le_max_left _ _).trans hM
    have hM2 : -σ₀ ≤ M := (le_max_right _ _).trans hM
    have heqM : (fun t : ℝ => R ((-M : ℂ) + t * I)) = fun t : ℝ =>
        G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀) -
          G p₀ * ((((-M : ℂ) + t * I) - p₀)⁻¹ - (((-M : ℂ) + t * I) - p₁)⁻¹) := by
      funext t
      refine hR_eq _ (fun e => ?_) (fun e => ?_)
      · have := congrArg Complex.re e; simp at this; linarith
      · have := congrArg Complex.re e; simp [hp₁re] at this; linarith
    have hint1 : Integrable fun t : ℝ => G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀) := by
      have hcont : Continuous fun t : ℝ => G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀) := by
        rw [continuous_iff_continuousAt]; intro t
        exact ((hdiff _ (by simp; linarith)).continuousAt.comp (by fun_prop)).div
          (by fun_prop) (fun e => by have := congrArg Complex.re e; simp at this; linarith)
      refine (integrable_inv_one_add_sq.const_mul (b M)).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rw [norm_div]
      have hG := hbleft M hM2 t
      have hd : √(1 + t ^ 2) ≤ ‖((-M : ℂ) + t * I) - p₀‖ := by
        rw [Complex.norm_def, Real.sqrt_le_sqrt_iff (Complex.normSq_nonneg _), Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
          Complex.neg_im, Complex.ofReal_im, Complex.mul_im]
        have hr : 1 ≤ -M - p₀.re := by linarith
        have him : |t - p₀.im| ≥ 0 := abs_nonneg _
        -- Even simpler bound: use `|Re| ≥ 1` and `|Im|`? Careful: `(t - p₀.im)²` vs `t²`!
        sorry
      sorry
    sorry
  sorry
