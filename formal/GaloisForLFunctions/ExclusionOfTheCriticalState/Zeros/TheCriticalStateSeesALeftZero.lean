import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.StateProductMultiplicity
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSideIsNormalisedAtTheLeftEnd
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerExponentialBarriers
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier

/-!
# Every critical state sees a left zero

For the critical half-line ground state `F`, right-half-plane zero-freeness of `L F` supplies a
pole of `stateMeromorphic W₀ F` at every shifted zero `ρ - 17/2` on or right of the critical line
(`Re ρ ≥ ½`), leaving open whether `L F` could vanish at every zero strictly left of the line
(`0 < Re ρ < ½`).

Pairing `globalRemainder F (4 + it) - globalRemainder F (-4 + it)` against the bi-Cauchy kernel
`W_N(4 + it) L F(-4 - it)` with `W_N(w) = 4 N⁴ / ((N² - w²)(4N² - w²))` and shifting the
pole-subtracted `dslope` remainders far left yields, for every `N ≥ 20`, the exact identity

  `-(a / 2π) ∫ W_N(4 + it) ‖L F(-4 + it)‖² dt`
  `= (2N/3) L F(N) B F(-N) - (N/3) L F(2N) B F(-2N) + Σ_c W_N(z_c) L F(z_c) L F(-z_c)`.

As `N → ∞`, Plancherel on `Re w = -4` sends the left side to `-a W₈(F) < 0`, the boundary terms
at `-N` and `-2N` vanish because `|F(u)| ≤ C e^u` bounds `N |L F(N)|` while `B F(-N) → 0`, and
every critical-line zero `z_c = iγ` contributes `4 N⁴ / ((N² + γ²)(4N² + γ²)) · ‖L F(iγ)‖² ≥ 0`.
Hence some off-line zero pair satisfies `L F(z_c) L F(-z_c) ≠ 0`, and reflecting into the left
half-strip yields a centred zero with `-½ < Re z < 0` and `L F(z) ≠ 0`.
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
  rw [hpt, integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) |a|⁻¹]
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
    exact continuous_const.div (by fun_prop : Continuous fun u : ℝ => a ^ 2 + u ^ 2)
      fun u => (by nlinarith [sq_nonneg u] : 0 < a ^ 2 + u ^ 2).ne')
      (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by nlinarith [sq_nonneg u] : 0 < a ^ 2 + u ^ 2)]
  have hle : min (a ^ 2) 1 * (1 + u ^ 2) ≤ a ^ 2 + u ^ 2 := by
    have h1 : min (a ^ 2) 1 ≤ a ^ 2 := min_le_left _ _
    have h2 : min (a ^ 2) 1 ≤ 1 := min_le_right _ _
    nlinarith [sq_nonneg u]
  rw [← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (abs_nonneg a) (mul_pos hm (by positivity)) hle

private theorem integrable_odd_diff_cauchy {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable fun u : ℝ => u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  set m := min (min (a ^ 2) (b ^ 2)) 1
  have hm : 0 < m := lt_min (lt_min ha2 hb2) one_pos
  have hdom : Integrable fun u : ℝ => (|b ^ 2 - a ^ 2| / m ^ 2) * (1 + u ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hcont : Continuous fun u : ℝ => u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) :=
    continuous_id.mul (((by fun_prop : Continuous fun u : ℝ => a ^ 2 + u ^ 2).inv₀
      fun u => (by nlinarith [sq_nonneg u] : 0 < a ^ 2 + u ^ 2).ne').sub
      ((by fun_prop : Continuous fun u : ℝ => b ^ 2 + u ^ 2).inv₀
        fun u => (by nlinarith [sq_nonneg u] : 0 < b ^ 2 + u ^ 2).ne'))
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have hda : 0 < a ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hdb : 0 < b ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hpt : u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) =
      u * (b ^ 2 - a ^ 2) / ((a ^ 2 + u ^ 2) * (b ^ 2 + u ^ 2)) := by
    field_simp [hda.ne', hdb.ne']; ring
  rw [hpt, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (mul_pos hda hdb)]
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
      _ ≤ (a ^ 2 + u ^ 2) * (b ^ 2 + u ^ 2) := mul_le_mul hma hmb (by positivity) hda.le
  have hu : |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hnum : |u| * |b ^ 2 - a ^ 2| * (m ^ 2 * (1 + u ^ 2)) ≤
      |b ^ 2 - a ^ 2| * (m ^ 2 * (1 + u ^ 2) ^ 2) := by
    have h1 : |u| * (1 + u ^ 2) ≤ (1 + u ^ 2) ^ 2 := by nlinarith [hu, sq_nonneg u]
    nlinarith [h1, mul_nonneg (abs_nonneg (b ^ 2 - a ^ 2)) (sq_nonneg m)]
  rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (mul_pos hda hdb)
    (mul_pos (sq_pos_of_pos hm) (by positivity))]
  exact hnum.trans (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))

private theorem integral_odd_diff_cauchy_eq_zero (a b : ℝ) :
    (∫ u : ℝ, u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹)) = 0 := by
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ => u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹)) (-1)
  have hneg : (fun u : ℝ => (-1 * u) * ((a ^ 2 + (-1 * u) ^ 2)⁻¹ - (b ^ 2 + (-1 * u) ^ 2)⁻¹)) =
      fun u : ℝ => -(u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹)) := by
    funext u; ring
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  rw [hneg, integral_neg] at h
  linarith

private theorem integrable_cauchy_pair_vertical {p₀ : ℂ} {K σ : ℝ}
    (h1 : p₀.re ≠ σ) (h2 : p₀.re + K ≠ σ) :
    Integrable fun t : ℝ =>
      ((((σ : ℂ) + t * I) - p₀)⁻¹ - (((σ : ℂ) + t * I) - (p₀ + K))⁻¹) := by
  set a := σ - p₀.re
  set b := σ - (p₀.re + K)
  have ha : a ≠ 0 := sub_ne_zero.mpr h1.symm
  have hb : b ≠ 0 := sub_ne_zero.mpr h2.symm
  have hdecomp : (fun u : ℝ => (((a : ℂ) + u * I)⁻¹ - ((b : ℂ) + u * I)⁻¹)) =
      fun u : ℝ => ((a / (a ^ 2 + u ^ 2) - b / (b ^ 2 + u ^ 2) : ℝ) : ℂ) -
        I * ((u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) : ℝ) : ℂ) := by
    funext u
    have hna : Complex.normSq ((a : ℂ) + u * I) = a ^ 2 + u ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    have hnb : Complex.normSq ((b : ℂ) + u * I) = b ^ 2 + u ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    rw [Complex.inv_def, Complex.inv_def, hna, hnb]
    apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring
  have hint_u : Integrable fun u : ℝ => (((a : ℂ) + u * I)⁻¹ - ((b : ℂ) + u * I)⁻¹) := by
    rw [hdecomp]
    exact (Complex.ofRealCLM.integrable_comp
      ((integrable_scaled_inv_sq_add_sq ha).sub (integrable_scaled_inv_sq_add_sq hb))).sub
      ((Complex.ofRealCLM.integrable_comp (integrable_odd_diff_cauchy ha hb)).const_mul I)
  have hsub := hint_u.comp_sub_right p₀.im
  refine hsub.congr (Eventually.of_forall fun t => ?_)
  dsimp only [Function.comp_def]
  have e1 : ((σ : ℂ) + t * I) - p₀ = (a : ℂ) + (t - p₀.im : ℝ) * I := by
    apply Complex.ext <;> simp [a]
  have e2 : ((σ : ℂ) + t * I) - (p₀ + K) = (b : ℂ) + (t - p₀.im : ℝ) * I := by
    apply Complex.ext <;> simp [b]
  rw [e1, e2]

private theorem integral_cauchy_pair_vertical {p₀ : ℂ} {K σ : ℝ} (hK : 0 < K)
    (h1 : p₀.re ≠ σ) (h2 : p₀.re + K ≠ σ) :
    (∫ t : ℝ, ((((σ : ℂ) + t * I) - p₀)⁻¹ - (((σ : ℂ) + t * I) - (p₀ + K))⁻¹)) =
      if p₀.re < σ ∧ σ < p₀.re + K then (2 * Real.pi : ℂ) else 0 := by
  set a := σ - p₀.re
  set b := σ - (p₀.re + K)
  have ha : a ≠ 0 := sub_ne_zero.mpr h1.symm
  have hb : b ≠ 0 := sub_ne_zero.mpr h2.symm
  have hshift : (∫ t : ℝ, ((((σ : ℂ) + t * I) - p₀)⁻¹ - (((σ : ℂ) + t * I) - (p₀ + K))⁻¹)) =
      ∫ u : ℝ, (((a : ℂ) + u * I)⁻¹ - ((b : ℂ) + u * I)⁻¹) := by
    rw [← integral_add_right_eq_self _ p₀.im]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    have e1 : ((σ : ℂ) + (t + p₀.im : ℝ) * I) - p₀ = (a : ℂ) + t * I := by
      apply Complex.ext <;> simp [a]
    have e2 : ((σ : ℂ) + (t + p₀.im : ℝ) * I) - (p₀ + K) = (b : ℂ) + t * I := by
      apply Complex.ext <;> simp [b]
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
    rw [Complex.inv_def, Complex.inv_def, hna, hnb]
    apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring
  have hintR : Integrable fun u : ℝ =>
      ((a / (a ^ 2 + u ^ 2) - b / (b ^ 2 + u ^ 2) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integrable_comp
      ((integrable_scaled_inv_sq_add_sq ha).sub (integrable_scaled_inv_sq_add_sq hb))
  have hintI : Integrable fun u : ℝ =>
      I * ((u * ((a ^ 2 + u ^ 2)⁻¹ - (b ^ 2 + u ^ 2)⁻¹) : ℝ) : ℂ) :=
    (Complex.ofRealCLM.integrable_comp (integrable_odd_diff_cauchy ha hb)).const_mul I
  rw [hdecomp, integral_sub hintR hintI, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_odd_diff_cauchy_eq_zero, Complex.ofReal_zero, mul_zero,
    sub_zero, integral_sub (integrable_scaled_inv_sq_add_sq ha) (integrable_scaled_inv_sq_add_sq hb),
    integral_scaled_inv_sq_add_sq ha, integral_scaled_inv_sq_add_sq hb]
  by_cases hsep : p₀.re < σ ∧ σ < p₀.re + K
  · rw [if_pos hsep]
    have ha_pos : 0 < a := by dsimp [a]; linarith [hsep.1]
    have hb_neg : ¬ 0 < b := by dsimp [b]; linarith [hsep.2]
    rw [if_pos ha_pos, if_neg hb_neg]; push_cast; ring
  · rw [if_neg hsep]
    by_cases hlt : σ < p₀.re
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

private lemma one_add_abs_le_norm_sub_of_re_gap {s p : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hre : δ ≤ |s.re - p.re|) :
    1 + |s.im| ≤ (1 + (1 + |p.im|) / δ) * ‖s - p‖ := by
  have hr : δ ≤ ‖s - p‖ := hre.trans (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _)
  have hi : |s.im| - |p.im| ≤ ‖s - p‖ :=
    (abs_sub_abs_le_abs_sub s.im p.im).trans
      (by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _)
  have h1 : 1 + |p.im| ≤ ((1 + |p.im|) / δ) * ‖s - p‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  linarith

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
    set T₀ : ℝ := 2 * (1 + |p₀.im|)
    have hKpt : IsCompact (Icc (-M) σ₀ ×ˢ Icc (-T₀) T₀) := isCompact_Icc.prod isCompact_Icc
    have hRcont : ContinuousOn (fun q : ℝ × ℝ => R ((q.1 : ℂ) + q.2 * I))
        (Icc (-M) σ₀ ×ˢ Icc (-T₀) T₀) := fun q hq =>
      ((hR_diff _ (by simp [hq.1.2])).continuousAt.comp
        (by fun_prop : Continuous fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * I).continuousAt).continuousWithinAt
    obtain ⟨C₀, hC₀⟩ := hKpt.exists_bound_of_continuousOn hRcont
    have hC₀n := abs_nonneg C₀
    set Cfar : ℝ := 4 * B + 4 * ‖G p₀‖ * K
    set Ctot : ℝ := (|C₀| + 1) * (1 + T₀ ^ 2) + Cfar
    have hMσ : -σ₀ ≤ M := (le_max_right _ _).trans hM
    rw [show (-M : ℂ) = ((-M : ℝ) : ℂ) by simp]
    refine integral_vertical_line_shift_of_decay (Φ := R) (c₁ := σ₀) (c₂ := -M) (C := Ctot)
      (fun s hs => hR_diff s (by
        rcases Set.mem_uIcc.mp hs with h | h <;> linarith [h.1, h.2, hMσ]))
      (fun s hs => ?_)
    have hs_mem : -M ≤ s.re ∧ s.re ≤ σ₀ := by
      rcases Set.mem_uIcc.mp hs with h | h <;> constructor <;> linarith [h.1, h.2, hMσ]
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
      have hne0 : s ≠ p₀ := sub_ne_zero.mp (norm_ne_zero_iff.mp (hpos_im.trans_le hd0).ne')
      have hne1 : s ≠ p₁ := sub_ne_zero.mp (norm_ne_zero_iff.mp (hpos_im.trans_le hd1).ne')
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
  have hR_zero : (∫ t : ℝ, R ((σ₀ : ℂ) + t * I)) = 0 := by
    set Cp : ℝ := 2 + |p₀.im|
    have hCp : 0 < Cp := by dsimp [Cp]; positivity
    have hlim : Tendsto (fun M : ℝ => ∫ t : ℝ, R ((-M : ℂ) + t * I)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun M : ℝ => Cp * b M * Real.pi) ?_
        (by simpa using (hbtend.const_mul Cp).mul_const Real.pi)
      filter_upwards [eventually_ge_atTop (max (-p₀.re + 1) (-σ₀))] with M hM
      have hM1 : -p₀.re + 1 ≤ M := (le_max_left _ _).trans hM
      have hM2 : -σ₀ ≤ M := (le_max_right _ _).trans hM
      have heqM : (fun t : ℝ => R ((-M : ℂ) + t * I)) = fun t : ℝ =>
          G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀) -
            G p₀ * ((((-M : ℂ) + t * I) - p₀)⁻¹ - (((-M : ℂ) + t * I) - p₁)⁻¹) := by
        funext t
        exact hR_eq _ (fun e => by have := congrArg Complex.re e; simp at this; linarith)
          (fun e => by have := congrArg Complex.re e; simp [hp₁re] at this; linarith)
      have hdomM : ∀ t : ℝ, ‖G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀)‖ ≤
          (Cp * b M) * (1 + t ^ 2)⁻¹ := by
        intro t
        have hreM : ((-M : ℂ) + t * I).re = -M := by simp
        have himM : ((-M : ℂ) + t * I).im = t := by simp
        have hgap : 1 ≤ |((-M : ℂ) + t * I).re - p₀.re| := by
          rw [hreM, abs_of_nonpos (by linarith)]
          linarith
        have hw := one_add_abs_le_norm_sub_of_re_gap one_pos hgap
        rw [himM, div_one, show 1 + (1 + |p₀.im|) = Cp by dsimp [Cp]; ring] at hw
        have hnpos : 0 < ‖((-M : ℂ) + t * I) - p₀‖ := by
          have : 0 < 1 + |t| := by positivity
          nlinarith
        rw [norm_div, div_le_iff₀ hnpos]
        have hG := hbleft M hM2 t
        have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
        calc ‖G ((-M : ℂ) + t * I)‖ ≤ b M / (1 + |t|) := hG
          _ = (Cp * b M / (1 + |t|) ^ 2) * ((1 + |t|) / Cp) := by
              field_simp [hCp.ne', (by positivity : (0 : ℝ) < 1 + |t|).ne']
          _ ≤ (Cp * b M * (1 + t ^ 2)⁻¹) * ‖((-M : ℂ) + t * I) - p₀‖ := by
              refine mul_le_mul ?_ ((div_le_iff₀ hCp).mpr (by linarith)) (by positivity)
                (mul_nonneg (mul_nonneg hCp.le (hb0 M)) (by positivity))
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_left
                (inv_anti₀ (by positivity) hsq) (mul_nonneg hCp.le (hb0 M))
      have hint1 : Integrable fun t : ℝ => G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀) := by
        have hcont : Continuous fun t : ℝ => G ((-M : ℂ) + t * I) / (((-M : ℂ) + t * I) - p₀) := by
          rw [continuous_iff_continuousAt]; intro t
          have hd1 : ContinuousAt (G ∘ fun s : ℝ => (-M : ℂ) + s * I) t :=
            ContinuousAt.comp (hdiff _ (by simp; linarith)).continuousAt
              (by fun_prop : Continuous fun s : ℝ => (-M : ℂ) + s * I).continuousAt
          exact hd1.div (by fun_prop) (fun e => by have := congrArg Complex.re e; simp at this; linarith)
        exact (integrable_inv_one_add_sq.const_mul (Cp * b M)).mono'
          hcont.aestronglyMeasurable (Eventually.of_forall hdomM)
      have hint2 : Integrable fun t : ℝ =>
          G p₀ * ((((-M : ℂ) + t * I) - p₀)⁻¹ - (((-M : ℂ) + t * I) - p₁)⁻¹) := by
        have hi := (integrable_cauchy_pair_vertical (p₀ := p₀) (K := K) (σ := -M)
          (by linarith) (by linarith)).const_mul (G p₀)
        simpa only [Complex.ofReal_neg] using hi
      have hp_zero : (∫ t : ℝ, ((((-M : ℂ) + t * I) - p₀)⁻¹ - (((-M : ℂ) + t * I) - p₁)⁻¹)) = 0 := by
        have hc := integral_cauchy_pair_vertical (p₀ := p₀) (K := K) (σ := -M) hK
          (by linarith) (by linarith)
        rw [if_neg (by intro h; linarith [h.1])] at hc
        simpa only [Complex.ofReal_neg] using hc
      rw [integral_congr_ae (Eventually.of_forall (congrFun heqM)), integral_sub hint1 hint2,
        integral_const_mul, hp_zero, mul_zero, sub_zero]
      refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul (Cp * b M))
        (Eventually.of_forall hdomM)).trans_eq ?_
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
    have hconst : (fun M : ℝ => ∫ t : ℝ, R ((-M : ℂ) + t * I)) =ᶠ[atTop]
        fun _ : ℝ => ∫ t : ℝ, R ((σ₀ : ℂ) + t * I) := by
      filter_upwards [eventually_ge_atTop (max (-p₀.re + 1) (-σ₀))] with M hM
      exact (hshift M hM).symm
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hconst.symm) hlim
  -- Now split `R` along `Re s = σ₀`
  have heq0 : (fun t : ℝ => R ((σ₀ : ℂ) + t * I)) = fun t : ℝ =>
      G ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) - p₀) -
        G p₀ * (((((σ₀ : ℂ) + t * I) - p₀)⁻¹ - (((σ₀ : ℂ) + t * I) - p₁)⁻¹)) := by
    funext t
    exact hR_eq _ (fun e => by have := congrArg Complex.re e; simp at this; linarith)
      (fun e => by have := congrArg Complex.re e; simp [hp₁re] at this)
  have hint_G : Integrable fun t : ℝ => G ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) - p₀) := by
    set δ₀ := σ₀ - p₀.re
    have hδ₀ : 0 < δ₀ := sub_pos.mpr hp₀
    set Cδ := 1 + (1 + |p₀.im|) / δ₀
    have hCδ : 0 < Cδ := by dsimp [Cδ]; positivity
    have hcont : Continuous fun t : ℝ => G ((σ₀ : ℂ) + t * I) / (((σ₀ : ℂ) + t * I) - p₀) := by
      rw [continuous_iff_continuousAt]; intro t
      have hd1 : ContinuousAt (G ∘ fun s : ℝ => (σ₀ : ℂ) + s * I) t :=
        ContinuousAt.comp (hdiff _ (by simp; linarith)).continuousAt
          (by fun_prop : Continuous fun s : ℝ => (σ₀ : ℂ) + s * I).continuousAt
      exact hd1.div (by fun_prop) (fun e => by have := congrArg Complex.re e; simp at this; linarith)
    refine (integrable_inv_one_add_sq.const_mul (Cδ * B)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have hre0 : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    have him0 : ((σ₀ : ℂ) + t * I).im = t := by simp
    have hgap : δ₀ ≤ |((σ₀ : ℂ) + t * I).re - p₀.re| := by
      rw [hre0]; exact (abs_of_pos hδ₀).ge
    have hw := one_add_abs_le_norm_sub_of_re_gap hδ₀ hgap
    rw [him0, show 1 + (1 + |p₀.im|) / δ₀ = Cδ by rfl] at hw
    have hnpos : 0 < ‖((σ₀ : ℂ) + t * I) - p₀‖ := by
      have : 0 < 1 + |t| := by positivity
      nlinarith
    rw [norm_div, div_le_iff₀ hnpos]
    have hG := hbound ((σ₀ : ℂ) + t * I) (by simp)
    rw [him0] at hG
    have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    calc ‖G ((σ₀ : ℂ) + t * I)‖ ≤ B / (1 + |t|) := hG
      _ = (Cδ * B / (1 + |t|) ^ 2) * ((1 + |t|) / Cδ) := by
          field_simp [hCδ.ne', (by positivity : (0 : ℝ) < 1 + |t|).ne']
      _ ≤ (Cδ * B * (1 + t ^ 2)⁻¹) * ‖((σ₀ : ℂ) + t * I) - p₀‖ := by
          refine mul_le_mul ?_ ((div_le_iff₀ hCδ).mpr (by linarith))
            (by positivity) (mul_nonneg (mul_nonneg hCδ.le hB0) (by positivity))
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (mul_nonneg hCδ.le hB0)
  have hint_P : Integrable fun t : ℝ =>
      G p₀ * (((((σ₀ : ℂ) + t * I) - p₀)⁻¹ - (((σ₀ : ℂ) + t * I) - p₁)⁻¹)) :=
    (integrable_cauchy_pair_vertical (p₀ := p₀) (K := K) (σ := σ₀) hp₀.ne
      (by linarith)).const_mul (G p₀)
  have hp_val : (∫ t : ℝ, ((((σ₀ : ℂ) + t * I) - p₀)⁻¹ - (((σ₀ : ℂ) + t * I) - p₁)⁻¹)) =
      (2 * Real.pi : ℂ) := by
    have hc := integral_cauchy_pair_vertical (p₀ := p₀) (K := K) (σ := σ₀) hK hp₀.ne (by linarith)
    rw [if_pos ⟨hp₀, by dsimp [K]; linarith⟩] at hc
    exact hc
  rw [integral_congr_ae (Eventually.of_forall (congrFun heq0)), integral_sub hint_G hint_P,
    integral_const_mul, hp_val] at hR_zero
  linear_combination hR_zero

/-! ### Cauchy kernels and state vertical identities -/

private def singleCauchy (L : ℝ) (w : ℂ) : ℂ :=
  (L : ℂ) ^ 2 / ((L : ℂ) ^ 2 - w ^ 2)

private def biCauchy (N : ℝ) (w : ℂ) : ℂ :=
  4 * (N : ℂ) ^ 4 / (((N : ℂ) ^ 2 - w ^ 2) * (4 * (N : ℂ) ^ 2 - w ^ 2))

private theorem biCauchy_eq_sub {N : ℝ} (_hN : 0 < N) {w : ℂ}
    (h1 : (N : ℂ) ^ 2 - w ^ 2 ≠ 0) (h2 : 4 * (N : ℂ) ^ 2 - w ^ 2 ≠ 0) :
    biCauchy N w = (4 / 3 : ℂ) * singleCauchy N w -
      (1 / 3 : ℂ) * singleCauchy (2 * N) w := by
  unfold biCauchy singleCauchy
  push_cast
  have h2' : (2 * (N : ℂ)) ^ 2 - w ^ 2 = 4 * (N : ℂ) ^ 2 - w ^ 2 := by ring
  rw [h2']
  field_simp [h1, h2]
  ring

private theorem cauchy_denom_ne_zero {L : ℝ} (_hL : 20 ≤ L) {w : ℂ}
    (hw1 : w ≠ -(L : ℂ)) (hw2 : w.re < L) : (L : ℂ) ^ 2 - w ^ 2 ≠ 0 := by
  have hfac : (L : ℂ) ^ 2 - w ^ 2 = ((L : ℂ) - w) * ((L : ℂ) + w) := by ring
  rw [hfac]
  refine mul_ne_zero (fun e => ?_) (fun e => hw1 ?_)
  · have := congrArg Complex.re e; simp at this; linarith
  · linear_combination e

private theorem norm_sub_sq_on_four_ge {L : ℝ} (hL : 8 ≤ L) (t : ℝ) :
    (3 / 4 : ℝ) * L ^ 2 + t ^ 2 ≤ ‖(L : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ := by
  have hre : ((L : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2).re = L ^ 2 - 16 + t ^ 2 := by
    have : ((4 : ℂ) + t * I) ^ 2 = ((16 - t ^ 2 : ℝ) : ℂ) + ((8 * t : ℝ) : ℂ) * I := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this]; simp [pow_two]; ring
  have hpos : (3 / 4 : ℝ) * L ^ 2 + t ^ 2 ≤ L ^ 2 - 16 + t ^ 2 := by nlinarith
  exact hpos.trans ((le_abs_self _).trans (by rw [← hre]; exact Complex.abs_re_le_norm _))

private theorem norm_biCauchy_four_le {N : ℝ} (hN : 8 ≤ N) (t : ℝ) :
    ‖biCauchy N ((4 : ℂ) + t * I)‖ ≤ 2 := by
  unfold biCauchy
  have h1 := norm_sub_sq_on_four_ge hN t
  have h2 := norm_sub_sq_on_four_ge (L := 2 * N) (by linarith) t
  have h2' : ((2 * N : ℝ) : ℂ) ^ 2 = 4 * (N : ℂ) ^ 2 := by push_cast; ring
  rw [h2'] at h2
  have hd1 : (3 / 4 : ℝ) * N ^ 2 ≤ ‖(N : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
    (by nlinarith [sq_nonneg t] : (3 / 4 : ℝ) * N ^ 2 ≤ (3 / 4) * N ^ 2 + t ^ 2).trans h1
  have hd2 : 3 * N ^ 2 ≤ ‖4 * (N : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
    (by nlinarith [sq_nonneg t] : 3 * N ^ 2 ≤ (3 / 4) * (2 * N) ^ 2 + t ^ 2).trans h2
  have hNpos : 0 < N := by linarith
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hNpos.le,
    show ‖(4 : ℂ)‖ = 4 by norm_num, norm_mul]
  have hprod : ((3 / 4 : ℝ) * N ^ 2) * (3 * N ^ 2) ≤
      ‖(N : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ * ‖4 * (N : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
    mul_le_mul hd1 hd2 (by positivity) (norm_nonneg _)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hprod).trans (by
    rw [show (3 / 4 : ℝ) * N ^ 2 * (3 * N ^ 2) = (9 / 4 : ℝ) * N ^ 4 by ring,
      div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hNpos 4])

private theorem norm_biCauchy_four_decay {N : ℝ} (hN : 8 ≤ N) (t : ℝ) :
    ‖biCauchy N ((4 : ℂ) + t * I)‖ ≤ 4 * N ^ 4 / ((1 + t ^ 2) * (1 + t ^ 2)) := by
  unfold biCauchy
  have h1 := norm_sub_sq_on_four_ge hN t
  have h2 := norm_sub_sq_on_four_ge (L := 2 * N) (by linarith) t
  have h2' : ((2 * N : ℝ) : ℂ) ^ 2 = 4 * (N : ℂ) ^ 2 := by push_cast; ring
  rw [h2'] at h2
  have hd1 : 1 + t ^ 2 ≤ ‖(N : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
    (by nlinarith : 1 + t ^ 2 ≤ (3 / 4) * N ^ 2 + t ^ 2).trans h1
  have hd2 : 1 + t ^ 2 ≤ ‖4 * (N : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
    (by nlinarith : 1 + t ^ 2 ≤ (3 / 4) * (2 * N) ^ 2 + t ^ 2).trans h2
  have hNpos : 0 < N := by linarith
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hNpos.le,
    show ‖(4 : ℂ)‖ = 4 by norm_num, norm_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul hd1 hd2 (by positivity) (norm_nonneg _))

private theorem tendsto_biCauchy_four (t : ℝ) :
    Tendsto (fun N : ℝ => biCauchy N ((4 : ℂ) + t * I)) atTop (𝓝 1) := by
  set z : ℂ := ((4 : ℂ) + t * I) ^ 2
  have hz : Tendsto (fun N : ℝ => z / (N : ℂ) ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℝ => ((N : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
      have h1 := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0)))
      simp only [Complex.ofReal_zero] at h1
      exact h1.congr fun N => by dsimp [Function.comp_def]; push_cast; rfl
    simpa [div_eq_mul_inv] using hinv.const_mul z
  have hlim : Tendsto (fun N : ℝ => (4 : ℂ) / ((1 - z / (N : ℂ) ^ 2) * (4 - z / (N : ℂ) ^ 2)))
      atTop (𝓝 1) := by
    have hd : Tendsto (fun N : ℝ => (1 - z / (N : ℂ) ^ 2) * (4 - z / (N : ℂ) ^ 2))
        atTop (𝓝 ((1 - 0) * (4 - 0))) :=
      (tendsto_const_nhds.sub hz).mul (tendsto_const_nhds.sub hz)
    have hq := (tendsto_const_nhds (x := (4 : ℂ))).div hd (by norm_num)
    have h4 : (4 : ℂ) / ((1 - 0) * (4 - 0)) = 1 := by norm_num
    rw [h4] at hq
    exact hq
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (8 : ℝ)] with N hN
  have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  unfold biCauchy
  dsimp [z]
  field_simp [hN0]

private theorem biCauchy_pureImag_real_nonneg {N : ℝ} (hN : 0 < N) {z : ℂ} (hz : z.re = 0)
    (F : ℝ → ℝ) :
    0 ≤ (biCauchy N z * negativeHalfLineLaplace (cx F) z *
      negativeHalfLineLaplace (cx F) (-z)).re := by
  have hz_eq : z = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hz]
  have hz_sq : z ^ 2 = -((z.im ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hz_eq]
    push_cast; ring_nf; rw [I_sq]; ring
  have hbi : biCauchy N z =
      ((4 * N ^ 4 / ((N ^ 2 + z.im ^ 2) * (4 * N ^ 2 + z.im ^ 2)) : ℝ) : ℂ) := by
    unfold biCauchy
    rw [hz_sq]
    push_cast
    ring
  have hconj : negativeHalfLineLaplace (cx F) (-z) =
      conj (negativeHalfLineLaplace (cx F) z) := by
    unfold negativeHalfLineLaplace cx
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [hz_eq]
    simp [mul_comm]
  rw [mul_assoc, hconj, Complex.mul_conj, hbi, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

/-! ### Decay and Laplace properties of the critical state -/

private theorem criticalState_laplace_decay_right {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.re →
      ‖negativeHalfLineLaplace (cx F) w‖ ≤ C₁ / (w.re + 1) := by
  obtain ⟨C, hC0, hae⟩ := (criticalHalfLineGroundState_exponential_bounds hW ht hF).1 1
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun w hw => ?_⟩
  have hdom : Integrable fun u : ℝ => C * probe (w.re + 1) u :=
    (integrable_probe (by linarith)).const_mul C
  have hbound : ∀ᵐ (u : ℝ) ∂volume, ‖cexp (w * (u : ℂ)) * cx F u‖ ≤ C * probe (w.re + 1) u := by
    filter_upwards [hae] with u hu
    rcases lt_or_ge u 0 with huneg | hupos
    · rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.norm_real, Real.norm_eq_abs,
        probe_of_neg huneg]
      calc Real.exp (w.re * u) * |F u| ≤ Real.exp (w.re * u) * (C * Real.exp (1 * u)) :=
            mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
        _ = C * Real.exp ((w.re + 1) * u) := by
            rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.exp_add]
            congr 2; ring
    · have h0 := (criticalHalfLineEnergyDomain_of_groundState hF).support u hupos
      simp [cx, h0, probe_of_nonneg hupos]
  refine (norm_integral_le_of_norm_le hdom hbound).trans_eq ?_
  rw [integral_const_mul, integral_probe (by linarith)]
  ring

private theorem criticalState_globalRemainder_four {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (t : ℝ) :
    globalRemainder F ((4 : ℂ) + t * I) =
      -(criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hb12 := (criticalHalfLineGroundState_exponential_bounds hW ht hF).2 12 (by norm_num)
  have hLap_cont : ContinuousAt (fun ε : ℝ =>
      -(criticalAliasCoefficient W₀ : ℂ) *
        negativeHalfLineLaplace (cx F) (((-4 + ε : ℝ) : ℂ) + t * I)) 0 := by
    have hdiff := (differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by show -(12 / 2 : ℝ) < (((-4 + (0 : ℝ) : ℝ) : ℂ) + t * I).re; simp; norm_num))
    have hc1 : ContinuousAt
        (negativeHalfLineLaplace (cx F) ∘ fun ε : ℝ => ((-4 + ε : ℝ) : ℂ) + t * I) 0 :=
      ContinuousAt.comp hdiff.continuousAt
        (by fun_prop : Continuous fun ε : ℝ => ((-4 + ε : ℝ) : ℂ) + t * I).continuousAt
    exact continuousAt_const.mul hc1
  have hRem_cont : ContinuousAt (fun ε : ℝ =>
      globalRemainder F (((4 + ε : ℝ) : ℂ) + t * I)) 0 := by
    have hxi4 : xi (1 / 2 + (((4 + (0 : ℝ) : ℝ) : ℂ) + t * I)) ≠ 0 :=
      xi_ne_zero_of_half_le_abs_re (by simp; norm_num)
    have hdiff : DifferentiableAt ℂ (globalRemainder F) (((4 + (0 : ℝ) : ℝ) : ℂ) + t * I) := by
      refine differentiableAt_globalRemainder hd fun _ hz => hxi4 ?_
      rw [xi_eq_half_mul_Gammaℝ_mul_zetaEntire (by rw [re_one_half_add]; simp; norm_num), hz]
      ring
    exact ContinuousAt.comp (g := globalRemainder F)
      (f := fun ε : ℝ => ((4 + ε : ℝ) : ℂ) + t * I) hdiff.continuousAt
      (by fun_prop : Continuous fun ε : ℝ => ((4 + ε : ℝ) : ℂ) + t * I).continuousAt
  have hev : (fun ε : ℝ => globalRemainder F (((4 + ε : ℝ) : ℂ) + t * I)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => -(criticalAliasCoefficient W₀ : ℂ) *
        negativeHalfLineLaplace (cx F) (((-4 + ε : ℝ) : ℂ) + t * I) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h := criticalState_alias_mul_laplace hW ht hF
      (u := ((-4 + ε : ℝ) : ℂ) + t * I) (by simp; linarith)
    have harg : (((-4 + ε : ℝ) : ℂ) + t * I) + 8 = (((4 + ε : ℝ) : ℂ) + t * I) := by
      push_cast; ring
    rw [harg] at h
    calc globalRemainder F (((4 + ε : ℝ) : ℂ) + t * I)
        = -((criticalAliasCoefficient W₀ : ℂ) *
            negativeHalfLineLaplace (cx F) (((-4 + ε : ℝ) : ℂ) + t * I)) := by
            rw [h, neg_neg]
      _ = -(criticalAliasCoefficient W₀ : ℂ) *
            negativeHalfLineLaplace (cx F) (((-4 + ε : ℝ) : ℂ) + t * I) := by ring
  have hlim1 := (hRem_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  have heq0 := tendsto_nhds_unique hlim1
    (hLap_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  norm_num at heq0
  rw [heq0]
  ring

private theorem criticalState_laplace_conj (F : ℝ → ℝ) (w : ℂ) :
    negativeHalfLineLaplace (cx F) (conj w) = conj (negativeHalfLineLaplace (cx F) w) := by
  unfold negativeHalfLineLaplace cx
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

private theorem criticalState_norm_sq_four_integrable_and_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Integrable (fun t : ℝ => ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2) ∧
      0 < ∫ t : ℝ, ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hb10 := (criticalHalfLineGroundState_exponential_bounds hW ht hF).2 10 (by norm_num)
  let φ : ℝ → ℂ := fun x => ((F (-x) * Real.exp (5 * x) : ℝ) : ℂ)
  have hφm : Measurable φ :=
    Complex.measurable_ofReal.comp ((hd.meas.comp measurable_neg).mul (by fun_prop))
  have hφ2 : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))) := by
    rw [memLp_two_iff_integrable_sq_norm hφm.aestronglyMeasurable]
    have hcomp := hb10.comp_neg
    refine hcomp.integrableOn.congr_fun (fun x _ => ?_) measurableSet_Ioi
    dsimp [φ]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← Real.exp_nat_mul]
    ring_nf
  have hlap_eq : ∀ ξ : ℝ, laplaceRay φ (rayLine 1 ξ) =
      negativeHalfLineLaplace (cx F) ((-4 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) := by
    intro ξ
    unfold laplaceRay negativeHalfLineLaplace
    have h1 := integral_comp_neg_Ioi (0 : ℝ)
      (fun u : ℝ => cexp (((-4 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * u) * cx F u)
    rw [neg_zero] at h1
    have h2 : ∫ u in Iic (0 : ℝ),
        cexp (((-4 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * u) * cx F u =
        ∫ u : ℝ, cexp (((-4 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * u) * cx F u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        rw [cx, hd.support u (not_le.mp hu).le, Complex.ofReal_zero, mul_zero]
    rw [← h2, ← h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [φ, expRay, rayLine, cx]
    rw [Complex.ofReal_mul]
    have hexp : (Real.exp (5 * x) : ℂ) * cexp (-(((1 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * x)) =
        cexp (((-4 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * (-x : ℝ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    calc ((F (-x) : ℂ) * (Real.exp (5 * x) : ℂ)) *
            cexp (-(((1 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * x))
        = (F (-x) : ℂ) * ((Real.exp (5 * x) : ℂ) *
            cexp (-(((1 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * x))) := by ring
      _ = cexp (((-4 : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * (-x : ℝ)) * (F (-x) : ℂ) := by
          rw [hexp, mul_comm]
  have hmem_lp := memLp_two_laplaceRay_line hφ2 one_pos
  have hmem_ξ : Integrable fun ξ : ℝ => ‖laplaceRay φ (rayLine 1 ξ)‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hmem_lp.1).mp hmem_lp
  have hplanch := integral_norm_sq_laplaceRay_line hφ2 one_pos
  simp_rw [hlap_eq] at hmem_ξ hplanch
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hint_t : Integrable fun t : ℝ => ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 :=
    (integrable_comp_mul_left_iff
      (fun t : ℝ => ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2) hpi).mp hmem_ξ
  refine ⟨hint_t, ?_⟩
  have hscale := Measure.integral_comp_mul_left
    (fun t : ℝ => ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2) (2 * Real.pi)
  rw [hplanch] at hscale
  have hrhs_pos : 0 < ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * 1 * x)) * ‖φ x‖ ^ 2 := by
    have heq_W8 : (∫ x in Ioi (0 : ℝ), Real.exp (-(2 * 1 * x)) * ‖φ x‖ ^ 2) =
        ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
      have h1 := integral_comp_neg_Ioi (0 : ℝ) (fun u : ℝ => F u ^ 2 * Real.exp (-(8 * u)))
      rw [neg_zero] at h1
      have h2 : (∫ u in Iic (0 : ℝ), F u ^ 2 * Real.exp (-(8 * u))) =
          ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
          rw [hd.support u (not_le.mp hu).le, zero_pow two_ne_zero, zero_mul]
      rw [← h2, ← h1]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      dsimp [φ]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← Real.exp_nat_mul]
      push_cast
      have : Real.exp (-(2 * 1 * x)) * (F (-x) ^ 2 * Real.exp (2 * (5 * x))) =
          F (-x) ^ 2 * (Real.exp (-(2 * 1 * x)) * Real.exp (2 * (5 * x))) := by ring
      rw [this, ← Real.exp_add]
      congr 2; ring
    rw [heq_W8]
    have hunit : ∫ u : ℝ, F u ^ 2 = 1 := hF.2.2.2.1
    have hle_exp : ∀ u : ℝ, F u ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u)) := fun u => by
      rcases lt_or_ge u 0 with hu | hu
      · exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by linarith))
      · simp [hd.support u hu]
    have hge1 : 1 ≤ ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
      hunit ▸ integral_mono hd.sq hd.exponential hle_exp
    linarith
  have hinv_pos : 0 < |(2 * Real.pi)⁻¹| := abs_pos.mpr (inv_ne_zero hpi)
  rw [smul_eq_mul] at hscale
  by_contra hle
  push Not at hle
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hinv_pos.le hle
  rw [← hscale] at hnonpos
  exact not_lt_of_ge hnonpos hrhs_pos

/-! ### Exact single-parameter residue identities -/

private theorem integral_singleCauchy_left_line {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {L : ℝ} (hL : 20 ≤ L) :
    (∫ t : ℝ, singleCauchy L ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I)) =
      (2 * Real.pi : ℂ) * (((L : ℂ) / 2) *
        negativeHalfLineLaplace (cx F) (L : ℂ) *
        globalRemainder F (-(L : ℂ) - 8)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hb12 := (criticalHalfLineGroundState_exponential_bounds hW ht hF).2 12 (by norm_num)
  obtain ⟨C₁, hC₁0, hLap_right⟩ := criticalState_laplace_decay_right hW ht hF
  obtain ⟨KL, hKL⟩ := exists_bound_leftRemainder hd
  have hKL0 : 0 ≤ KL := (norm_nonneg _).trans (hKL (-1) (by simp))
  have hm4_int : Integrable fun u : ℝ => |F u| * Real.exp ((-4 : ℝ) * u) :=
    integrable_abs_mul_exp_of_sq hd.meas hd.support hb12 (by norm_num)
  set m4 : ℝ := ∫ u : ℝ, |F u| * Real.exp ((-4 : ℝ) * u)
  have hm4_0 : 0 ≤ m4 := integral_nonneg fun _ => by positivity
  have hLap4 : ∀ w : ℂ, w.re ≤ 4 → ‖negativeHalfLineLaplace (cx F) (-w)‖ ≤ m4 := by
    intro w hw
    refine norm_integral_le_of_norm_le hm4_int (Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_cexp_mul_ofReal]
    simp only [cx, Complex.norm_real, Real.norm_eq_abs, Complex.neg_re]
    rcases lt_or_ge u 0 with hu | hu
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
    · simp [hd.support u hu]
  have hRem8 : ∀ w : ℂ, w.re ≤ 4 → ‖globalRemainder F (w - 8)‖ ≤ KL := by
    intro w hw
    have hlt : (w - 8).re < -(1 / 2) := by simp; linarith
    rw [globalRemainder, if_neg (not_lt.mpr hlt.le), if_pos hlt]
    exact hKL (w - 8) (by simp; linarith)
  let G : ℂ → ℂ := fun w => -((L : ℂ) ^ 2 / (w - L)) *
    negativeHalfLineLaplace (cx F) (-w) * globalRemainder F (w - 8)
  have hG_diff : ∀ s : ℂ, s.re < 5 → DifferentiableAt ℂ G s := by
    intro s hs
    have hne : s - (L : ℂ) ≠ 0 := by intro e; have := congrArg Complex.re e; simp at this; linarith
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => -((L : ℂ) ^ 2 / (w - L))) s :=
      (((differentiableAt_const ((L : ℂ) ^ 2) (x := s)).div
        ((differentiableAt_id (x := s)).sub (differentiableAt_const (L : ℂ) (x := s))) hne).neg)
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => negativeHalfLineLaplace (cx F) (-w)) s :=
      ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by show -(12 / 2 : ℝ) < (-s).re; simp; linarith))).comp s differentiableAt_id.neg
    have hd3 : DifferentiableAt ℂ (fun w : ℂ => globalRemainder F (w - 8)) s :=
      (differentiableAt_globalRemainder hd (p := s - 8)
        (fun h' => absurd h' (by simp; linarith))).comp s (differentiableAt_id.sub_const 8)
    exact (hd1.mul hd2).mul hd3
  have hwL : ∀ s : ℂ, s.re ≤ 4 → 1 + |s.im| ≤ 2 * ‖s - (L : ℂ)‖ := by
    intro s hs
    have h1 := one_add_abs_le_norm_sub_of_re_gap (p := (L : ℂ)) (δ := 1) one_pos
      (by simp; rw [abs_of_neg (by linarith)]; linarith)
    simp only [Complex.ofReal_im, abs_zero, add_zero, div_one] at h1
    linarith
  have hG_bound : ∀ s : ℂ, s.re ≤ 4 →
      ‖G s‖ ≤ (2 * L ^ 2 * m4 * KL) / (1 + |s.im|) := by
    intro s hs
    dsimp [G]
    rw [norm_mul, norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ L)]
    have hden := hwL s hs
    have hn : 0 < ‖s - (L : ℂ)‖ := by
      have hpos1 : 0 < 1 + |s.im| := by positivity
      linarith
    calc L ^ 2 / ‖s - (L : ℂ)‖ * ‖negativeHalfLineLaplace (cx F) (-s)‖ *
            ‖globalRemainder F (s - 8)‖
        ≤ L ^ 2 / ((1 + |s.im|) / 2) * m4 * KL := by
          refine mul_le_mul (mul_le_mul (div_le_div_of_nonneg_left (by positivity)
            (by positivity) (by linarith)) (hLap4 s hs) (norm_nonneg _) (by positivity))
            (hRem8 s hs) (norm_nonneg _) (by positivity)
      _ = (2 * L ^ 2 * m4 * KL) / (1 + |s.im|) := by
          field_simp [(by positivity : (0 : ℝ) < 1 + |s.im|).ne']
  let b : ℝ → ℝ := fun M => 2 * L ^ 2 * (max m4 C₁ / (max M 0 + 1)) * KL
  have hb0 : ∀ M, 0 ≤ b M := fun M => by dsimp [b]; positivity
  have hbtend : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => (M + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h2 : Tendsto (fun M : ℝ => 2 * L ^ 2 * (max m4 C₁ * (M + 1)⁻¹) * KL) atTop (𝓝 0) := by
      simpa using ((h1.const_mul (max m4 C₁)).const_mul (2 * L ^ 2)).mul_const KL
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    dsimp [b]; rw [max_eq_left hM, div_eq_mul_inv]
  have hbleft : ∀ M : ℝ, -(4 : ℝ) ≤ M → ∀ t : ℝ,
      ‖G ((-M : ℂ) + t * I)‖ ≤ b M / (1 + |t|) := by
    intro M hM t
    have hs : ((-M : ℂ) + t * I).re ≤ 4 := by simp; linarith
    have himM : ((-M : ℂ) + t * I).im = t := by simp
    have hden := hwL ((-M : ℂ) + t * I) hs
    rw [himM] at hden
    have hLapM : ‖negativeHalfLineLaplace (cx F) (-((-M : ℂ) + t * I))‖ ≤
        max m4 C₁ / (max M 0 + 1) := by
      rcases lt_or_ge M 0 with hMneg | hMpos
      · rw [max_eq_right hMneg.le, zero_add, div_one]
        exact (hLap4 _ hs).trans (le_max_left _ _)
      · rw [max_eq_left hMpos]
        have hreM : (-((-M : ℂ) + t * I)).re = M := by simp
        have h := hLap_right (-((-M : ℂ) + t * I)) (by rw [hreM]; exact hMpos)
        rw [hreM] at h
        exact h.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by linarith))
    dsimp [G, b]
    rw [norm_mul, norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ L)]
    calc L ^ 2 / ‖((-M : ℂ) + t * I) - (L : ℂ)‖ *
            ‖negativeHalfLineLaplace (cx F) (-((-M : ℂ) + t * I))‖ *
            ‖globalRemainder F (((-M : ℂ) + t * I) - 8)‖
        ≤ L ^ 2 / ((1 + |t|) / 2) * (max m4 C₁ / (max M 0 + 1)) * KL := by
          refine mul_le_mul (mul_le_mul (div_le_div_of_nonneg_left (by positivity)
            (by positivity) (by linarith)) hLapM (norm_nonneg _) (by positivity))
            (hRem8 _ hs) (norm_nonneg _) (by positivity)
      _ = 2 * L ^ 2 * (max m4 C₁ / (max M 0 + 1)) * KL / (1 + |t|) := by
          field_simp [(by positivity : (0 : ℝ) < 1 + |t|).ne']
  have hmain := integral_vertical_one_pole_left (G := G) (σ₀ := 4) (σ₁ := 5) (p₀ := -(L : ℂ))
    (by norm_num) (by simp; linarith) hG_diff (by positivity) hG_bound hb0 hbtend hbleft
  rw [show ((4 : ℝ) : ℂ) = 4 by norm_num] at hmain
  have hcongr : (fun t : ℝ => singleCauchy L ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I)) =
      fun t : ℝ => G ((4 : ℂ) + t * I) / (((4 : ℂ) + t * I) - -(L : ℂ)) := by
    funext t
    dsimp [G, singleCauchy]
    have h1 : ((4 : ℂ) + t * I) - (L : ℂ) ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp at this; linarith
    have h2 : ((4 : ℂ) + t * I) - -(L : ℂ) ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp at this; linarith
    have h3 : (L : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2 =
        -((((4 : ℂ) + t * I) - (L : ℂ)) * (((4 : ℂ) + t * I) - -(L : ℂ))) := by ring
    have he1 : -((4 : ℂ) + t * I) = (-4 : ℂ) - t * I := by ring
    have he2 : ((4 : ℂ) + t * I) - 8 = (-4 : ℂ) + t * I := by ring
    rw [he1, he2, h3]
    field_simp [h1, h2]
  rw [integral_congr_ae (Eventually.of_forall (congrFun hcongr)), hmain]
  dsimp [G]
  have hL0 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h2L : -(L : ℂ) - (L : ℂ) = -2 * (L : ℂ) := by ring
  rw [neg_neg, h2L]
  field_simp [hL0]

private theorem integral_singleCauchy_zero_term {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {L : ℝ} (hL : 20 ≤ L)
    (c : XiZeroCopy) :
    (∫ t : ℝ, singleCauchy L ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹)) =
      (2 * Real.pi : ℂ) * (singleCauchy L (centredZero c) *
        negativeHalfLineLaplace (cx F) (-centredZero c) +
        ((L : ℂ) / 2) * negativeHalfLineLaplace (cx F) (L : ℂ) *
          ((-(L : ℂ) - centredZero c)⁻¹ - (-(L : ℂ) - 8 - centredZero c)⁻¹)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hb12 := (criticalHalfLineGroundState_exponential_bounds hW ht hF).2 12 (by norm_num)
  obtain ⟨C₁, hC₁0, hLap_right⟩ := criticalState_laplace_decay_right hW ht hF
  have hm4_int : Integrable fun u : ℝ => |F u| * Real.exp ((-4 : ℝ) * u) :=
    integrable_abs_mul_exp_of_sq hd.meas hd.support hb12 (by norm_num)
  set m4 : ℝ := ∫ u : ℝ, |F u| * Real.exp ((-4 : ℝ) * u)
  have hm4_0 : 0 ≤ m4 := integral_nonneg fun _ => by positivity
  have hLap4 : ∀ w : ℂ, w.re ≤ 4 → ‖negativeHalfLineLaplace (cx F) (-w)‖ ≤ m4 := by
    intro w hw
    refine norm_integral_le_of_norm_le hm4_int (Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_cexp_mul_ofReal]
    simp only [cx, Complex.norm_real, Real.norm_eq_abs, Complex.neg_re]
    rcases lt_or_ge u 0 with hu | hu
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
    · simp [hd.support u hu]
  set z := centredZero c
  have hz_abs := abs_lt.mp (abs_re_centredZero_lt c)
  let H : ℂ → ℂ := fun w => 8 * (L : ℂ) ^ 2 * negativeHalfLineLaplace (cx F) (-w) /
    ((w - L) * (w - (8 + z)))
  have hH_diff : ∀ s : ℂ, s.re < 5 → DifferentiableAt ℂ H s := by
    intro s hs
    have hn1 : s - (L : ℂ) ≠ 0 := by intro e; have := congrArg Complex.re e; simp at this; linarith
    have hn2 : s - (8 + z) ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp at this; linarith [hz_abs.1]
    have hdLap : DifferentiableAt ℂ (fun w : ℂ => negativeHalfLineLaplace (cx F) (-w)) s :=
      ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by show -(12 / 2 : ℝ) < (-s).re; simp; linarith))).comp s differentiableAt_id.neg
    exact ((differentiableAt_const _).mul hdLap).div
      ((differentiableAt_id.sub_const _).mul (differentiableAt_id.sub_const _))
      (mul_ne_zero hn1 hn2)
  have hden_prod : ∀ s : ℂ, s.re ≤ 4 → 1 + |s.im| ≤ 2 * (‖s - (L : ℂ)‖ * ‖s - (8 + z)‖) := by
    intro s hs
    have hw1 : 1 + |s.im| ≤ 2 * ‖s - (L : ℂ)‖ := by
      have h1 := one_add_abs_le_norm_sub_of_re_gap (p := (L : ℂ)) (δ := 1) one_pos
        (by simp; rw [abs_of_neg (by linarith)]; linarith)
      simp only [Complex.ofReal_im, abs_zero, add_zero, div_one] at h1
      linarith
    have hw2 : 1 ≤ ‖s - (8 + z)‖ := by
      have : 1 ≤ |s.re - (8 + z).re| := by
        simp; rw [abs_of_neg (by linarith [hz_abs.1])]; linarith [hz_abs.1]
      exact this.trans (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _)
    calc 1 + |s.im| ≤ (2 * ‖s - (L : ℂ)‖) * 1 := by linarith
      _ ≤ (2 * ‖s - (L : ℂ)‖) * ‖s - (8 + z)‖ := mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = 2 * (‖s - (L : ℂ)‖ * ‖s - (8 + z)‖) := by ring
  have hH_bound : ∀ s : ℂ, s.re ≤ 4 → ‖H s‖ ≤ (16 * L ^ 2 * m4) / (1 + |s.im|) := by
    intro s hs
    dsimp [H]
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ L), show ‖(8 : ℂ)‖ = 8 by norm_num, norm_mul]
    have hp := hden_prod s hs
    have hpos : 0 < ‖s - (L : ℂ)‖ * ‖s - (8 + z)‖ := by
      have : 0 < 1 + |s.im| := by positivity
      linarith
    calc 8 * L ^ 2 * ‖negativeHalfLineLaplace (cx F) (-s)‖ /
            (‖s - (L : ℂ)‖ * ‖s - (8 + z)‖)
        ≤ 8 * L ^ 2 * m4 / ((1 + |s.im|) / 2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hLap4 s hs) (by positivity))
            (by positivity) (by linarith)
      _ = (16 * L ^ 2 * m4) / (1 + |s.im|) := by
          field_simp [(by positivity : (0 : ℝ) < 1 + |s.im|).ne']; ring
  let b : ℝ → ℝ := fun M => 16 * L ^ 2 * (max m4 C₁ / (max M 0 + 1))
  have hb0 : ∀ M, 0 ≤ b M := fun M => by dsimp [b]; positivity
  have hbtend : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => (M + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h2 : Tendsto (fun M : ℝ => 16 * L ^ 2 * (max m4 C₁ * (M + 1)⁻¹)) atTop (𝓝 0) := by
      simpa using (h1.const_mul (max m4 C₁)).const_mul (16 * L ^ 2)
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
    dsimp [b]; rw [max_eq_left hM, div_eq_mul_inv]
  have hbleft : ∀ M : ℝ, -(4 : ℝ) ≤ M → ∀ t : ℝ,
      ‖H ((-M : ℂ) + t * I)‖ ≤ b M / (1 + |t|) := by
    intro M hM t
    have hs : ((-M : ℂ) + t * I).re ≤ 4 := by simp; linarith
    have himM : ((-M : ℂ) + t * I).im = t := by simp
    have hp := hden_prod ((-M : ℂ) + t * I) hs
    rw [himM] at hp
    have hLapM : ‖negativeHalfLineLaplace (cx F) (-((-M : ℂ) + t * I))‖ ≤
        max m4 C₁ / (max M 0 + 1) := by
      rcases lt_or_ge M 0 with hMneg | hMpos
      · rw [max_eq_right hMneg.le, zero_add, div_one]
        exact (hLap4 _ hs).trans (le_max_left _ _)
      · rw [max_eq_left hMpos]
        have hreM : (-((-M : ℂ) + t * I)).re = M := by simp
        have h := hLap_right (-((-M : ℂ) + t * I)) (by rw [hreM]; exact hMpos)
        rw [hreM] at h
        exact h.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by linarith))
    dsimp [H, b]
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ L), show ‖(8 : ℂ)‖ = 8 by norm_num, norm_mul]
    calc 8 * L ^ 2 * ‖negativeHalfLineLaplace (cx F) (-((-M : ℂ) + t * I))‖ /
            (‖((-M : ℂ) + t * I) - (L : ℂ)‖ * ‖((-M : ℂ) + t * I) - (8 + z)‖)
        ≤ 8 * L ^ 2 * (max m4 C₁ / (max M 0 + 1)) / ((1 + |t|) / 2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hLapM (by positivity))
            (by positivity) (by linarith)
      _ = 16 * L ^ 2 * (max m4 C₁ / (max M 0 + 1)) / (1 + |t|) := by
          field_simp [(by positivity : (0 : ℝ) < 1 + |t|).ne']; ring
  have hzL : z + (L : ℂ) ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith [hz_abs.1]
  have hI1 := integral_vertical_one_pole_left (G := H) (σ₀ := 4) (σ₁ := 5) (p₀ := z)
    (by norm_num) (by linarith [hz_abs.2]) hH_diff (by positivity) hH_bound hb0 hbtend hbleft
  have hI2 := integral_vertical_one_pole_left (G := H) (σ₀ := 4) (σ₁ := 5) (p₀ := -(L : ℂ))
    (by norm_num) (by simp; linarith) hH_diff (by positivity) hH_bound hb0 hbtend hbleft
  rw [show ((4 : ℝ) : ℂ) = 4 by norm_num] at hI1 hI2
  -- Integrability of each single-pole piece on `Re w = 4`
  have hint_pole : ∀ p₀ : ℂ, p₀.re < 4 →
      Integrable fun t : ℝ => H ((4 : ℂ) + t * I) / (((4 : ℂ) + t * I) - p₀) := by
    intro p₀ hp₀
    set δ₀ := 4 - p₀.re
    have hδ₀ : 0 < δ₀ := sub_pos.mpr hp₀
    set Cδ := 1 + (1 + |p₀.im|) / δ₀
    have hCδ : 0 < Cδ := by dsimp [Cδ]; positivity
    have hcont : Continuous fun t : ℝ => H ((4 : ℂ) + t * I) / (((4 : ℂ) + t * I) - p₀) := by
      rw [continuous_iff_continuousAt]; intro t
      have hd1 : ContinuousAt (H ∘ fun s : ℝ => (4 : ℂ) + s * I) t :=
        ContinuousAt.comp (hH_diff _ (by simp; norm_num)).continuousAt
          (by fun_prop : Continuous fun s : ℝ => (4 : ℂ) + s * I).continuousAt
      exact hd1.div (by fun_prop) (fun e => by have := congrArg Complex.re e; simp at this; linarith)
    refine (integrable_inv_one_add_sq.const_mul (Cδ * (16 * L ^ 2 * m4))).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have hre4 : ((4 : ℂ) + t * I).re = 4 := by simp
    have him4 : ((4 : ℂ) + t * I).im = t := by simp
    have hgap : δ₀ ≤ |((4 : ℂ) + t * I).re - p₀.re| := by
      rw [hre4]; exact (abs_of_pos hδ₀).ge
    have hw := one_add_abs_le_norm_sub_of_re_gap hδ₀ hgap
    rw [him4, show 1 + (1 + |p₀.im|) / δ₀ = Cδ by rfl] at hw
    have hnpos : 0 < ‖((4 : ℂ) + t * I) - p₀‖ := by
      have : 0 < 1 + |t| := by positivity
      nlinarith
    rw [norm_div, div_le_iff₀ hnpos]
    have hG := hH_bound ((4 : ℂ) + t * I) (by simp)
    rw [him4] at hG
    have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    calc ‖H ((4 : ℂ) + t * I)‖ ≤ (16 * L ^ 2 * m4) / (1 + |t|) := hG
      _ = (Cδ * (16 * L ^ 2 * m4) / (1 + |t|) ^ 2) * ((1 + |t|) / Cδ) := by
          field_simp [hCδ.ne', (by positivity : (0 : ℝ) < 1 + |t|).ne']
      _ ≤ (Cδ * (16 * L ^ 2 * m4) * (1 + t ^ 2)⁻¹) * ‖((4 : ℂ) + t * I) - p₀‖ := by
          refine mul_le_mul ?_ ((div_le_iff₀ hCδ).mpr (by linarith))
            (by positivity) (by positivity)
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (by positivity)
  have hsplit : (fun t : ℝ => singleCauchy L ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        ((((4 : ℂ) + t * I) - z)⁻¹ - (((-4 : ℂ) + t * I) - z)⁻¹)) =
      fun t : ℝ => (z + (L : ℂ))⁻¹ *
        (H ((4 : ℂ) + t * I) / (((4 : ℂ) + t * I) - z) -
          H ((4 : ℂ) + t * I) / (((4 : ℂ) + t * I) - -(L : ℂ))) := by
    funext t
    set w := (4 : ℂ) + t * I
    have hwL1 : w - (L : ℂ) ≠ 0 := by intro e; have := congrArg Complex.re e; simp [w] at this; linarith
    have hwL2 : w - -(L : ℂ) ≠ 0 := by intro e; have := congrArg Complex.re e; simp [w] at this; linarith
    have hwz1 : w - z ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp [w] at this; linarith [hz_abs.2]
    have hwz2 : w - (8 + z) ≠ 0 := by
      intro e; have := congrArg Complex.re e; simp [w] at this; linarith [hz_abs.1]
    have h1 : (-4 : ℂ) - t * I = -w := by dsimp [w]; ring
    have h2 : ((-4 : ℂ) + t * I) - z = w - (8 + z) := by dsimp [w]; ring
    have h3 : (L : ℂ) ^ 2 - w ^ 2 = -((w - (L : ℂ)) * (w - -(L : ℂ))) := by ring
    rw [h1, h2]
    dsimp [singleCauchy, H]
    rw [h3]
    field_simp [hwL1, hwL2, hwz1, hwz2, hzL]
    ring
  rw [integral_congr_ae (Eventually.of_forall (congrFun hsplit)), integral_const_mul,
    integral_sub (hint_pole z (by linarith [hz_abs.2])) (hint_pole (-(L : ℂ)) (by simp; linarith)),
    hI1, hI2]
  -- Simplify the exact residue expression
  dsimp [H, singleCauchy]
  have hL0 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hz_sub_L : z - (L : ℂ) ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith [hz_abs.2]
  have hL2_sub_z2 : (L : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    rw [show (L : ℂ) ^ 2 - z ^ 2 = -(z - (L : ℂ)) * (z + (L : ℂ)) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hz_sub_L) hzL
  have hmL_sub_z : -(L : ℂ) - z ≠ 0 := by
    intro e; apply hzL; linear_combination -e
  have hmL8_sub_z : -(L : ℂ) - 8 - z ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith [hz_abs.1]
  have hz8 : z - (8 + z) = -8 := by ring
  have hmL8 : -(L : ℂ) - (8 + z) = -(L : ℂ) - 8 - z := by ring
  have hm2L : -(L : ℂ) - (L : ℂ) = -2 * (L : ℂ) := by ring
  rw [hz8, neg_neg, hm2L, hmL8]
  field_simp [hzL, hz_sub_L, hL2_sub_z2, hmL_sub_z, hmL8_sub_z, hL0]
  ring

/-! ### The bilateral zero-seeing theorem -/

private theorem biCauchy_state_identity {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {N : ℝ} (hN : 20 ≤ N) :
    -(criticalAliasCoefficient W₀ : ℂ) *
        (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
          ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ)) =
      (2 * Real.pi : ℂ) *
        (((2 * (N : ℂ) / 3) * negativeHalfLineLaplace (cx F) (N : ℂ) *
            globalRemainder F (-(N : ℂ)) -
          ((N : ℂ) / 3) * negativeHalfLineLaplace (cx F) (2 * (N : ℂ)) *
            globalRemainder F (-(2 * (N : ℂ)))) +
          ∑' c : XiZeroCopy, biCauchy N (centredZero c) *
            negativeHalfLineLaplace (cx F) (centredZero c) *
            negativeHalfLineLaplace (cx F) (-centredZero c)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hb12 := (criticalHalfLineGroundState_exponential_bounds hW ht hF).2 12 (by norm_num)
  have hm4_int : Integrable fun u : ℝ => |F u| * Real.exp ((-4 : ℝ) * u) :=
    integrable_abs_mul_exp_of_sq hd.meas hd.support hb12 (by norm_num)
  set m4 : ℝ := ∫ u : ℝ, |F u| * Real.exp ((-4 : ℝ) * u)
  have hm4_0 : 0 ≤ m4 := integral_nonneg fun _ => by positivity
  have hLap4_t : ∀ t : ℝ, ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I)‖ ≤ m4 := by
    intro t
    refine norm_integral_le_of_norm_le hm4_int (Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_cexp_mul_ofReal]
    simp only [cx, Complex.norm_real, Real.norm_eq_abs]
    rcases lt_or_ge u 0 with hu | hu
    · have : ((-4 : ℂ) - t * I).re = -4 := by simp
      rw [this, mul_comm]
    · simp [hd.support u hu]
  -- Summability and Fubini for the biCauchy zero sum
  let term : XiZeroCopy → ℝ → ℂ := fun c t =>
    biCauchy N ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
      (negativeHalfLineLaplace (cx F) (centredZero c) *
        ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹))
  let dom : XiZeroCopy → ℝ → ℝ := fun c t =>
    (2720 * N ^ 4 * m4 * halfPoleMass F * ‖centredZero c‖⁻¹ ^ 2) * (1 + t ^ 2)⁻¹
  have hterm_norm : ∀ c t, ‖term c t‖ ≤ dom c t := by
    intro c t
    dsimp [term, dom]
    have hbi := norm_biCauchy_four_decay (N := N) (by linarith) t
    have hLc : ‖negativeHalfLineLaplace (cx F) (centredZero c)‖ ≤ halfPoleMass F :=
      norm_laplace_le_halfPoleMass hd (by
        have := (abs_lt.mp (abs_re_centredZero_lt c)).1; linarith)
    have h1 : ‖(((4 : ℂ) + t * I) - centredZero c)⁻¹‖ ≤ (9 + 2 * |t|) * ‖centredZero c‖⁻¹ := by
      have hpnorm : ‖(4 : ℂ) + t * I‖ ≤ 4 + |t| :=
        (norm_add_le _ _).trans (by simp [Complex.norm_I])
      have := norm_inv_sub_le (p := (4 : ℂ) + t * I) (z := centredZero c) (δ := 1 / 2)
        (P := 4 + |t|) (by norm_num) (centredZero_ne_zero c)
        (half_le_norm_sub_centredZero (by simp) c) hpnorm
      refine this.trans_eq (by ring)
    have h2 : ‖(((-4 : ℂ) + t * I) - centredZero c)⁻¹‖ ≤ (9 + 2 * |t|) * ‖centredZero c‖⁻¹ := by
      have hpnorm : ‖(-4 : ℂ) + t * I‖ ≤ 4 + |t| :=
        (norm_add_le _ _).trans (by simp [Complex.norm_I])
      have := norm_inv_sub_le (p := (-4 : ℂ) + t * I) (z := centredZero c) (δ := 1 / 2)
        (P := 4 + |t|) (by norm_num) (centredZero_ne_zero c)
        (half_le_norm_sub_centredZero (by simp) c) hpnorm
      refine this.trans_eq (by ring)
    have hdiff_eq : (((4 : ℂ) + t * I) - centredZero c)⁻¹ -
        (((-4 : ℂ) + t * I) - centredZero c)⁻¹ =
        (-8 : ℂ) * ((((4 : ℂ) + t * I) - centredZero c)⁻¹ *
          (((-4 : ℂ) + t * I) - centredZero c)⁻¹) := by
      have hn1 : ((4 : ℂ) + t * I) - centredZero c ≠ 0 := by
        intro e; have := congrArg Complex.re e; simp at this
        linarith [(abs_lt.mp (abs_re_centredZero_lt c)).2]
      have hn2 : ((-4 : ℂ) + t * I) - centredZero c ≠ 0 := by
        intro e; have := congrArg Complex.re e; simp at this
        linarith [(abs_lt.mp (abs_re_centredZero_lt c)).1]
      field_simp [hn1, hn2]; ring
    have hdiff_le : ‖(((4 : ℂ) + t * I) - centredZero c)⁻¹ -
        (((-4 : ℂ) + t * I) - centredZero c)⁻¹‖ ≤
        8 * (9 + 2 * |t|) ^ 2 * ‖centredZero c‖⁻¹ ^ 2 := by
      rw [hdiff_eq, norm_mul, norm_mul, show ‖(-8 : ℂ)‖ = 8 by norm_num]
      calc 8 * (‖(((4 : ℂ) + t * I) - centredZero c)⁻¹‖ *
              ‖(((-4 : ℂ) + t * I) - centredZero c)⁻¹‖)
          ≤ 8 * (((9 + 2 * |t|) * ‖centredZero c‖⁻¹) *
              ((9 + 2 * |t|) * ‖centredZero c‖⁻¹)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by norm_num)
        _ = 8 * (9 + 2 * |t|) ^ 2 * ‖centredZero c‖⁻¹ ^ 2 := by ring
    have hpoly : 8 * (9 + 2 * |t|) ^ 2 ≤ 680 * (1 + t ^ 2) := by
      nlinarith [sq_nonneg (9 * |t| - 2), sq_abs t, abs_nonneg t]
    have hprod_t : (4 * N ^ 4 / ((1 + t ^ 2) * (1 + t ^ 2))) * (8 * (9 + 2 * |t|) ^ 2) ≤
        2720 * N ^ 4 * (1 + t ^ 2)⁻¹ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (1 + t ^ 2) * (1 + t ^ 2))]
      calc 4 * N ^ 4 * (8 * (9 + 2 * |t|) ^ 2)
          ≤ 4 * N ^ 4 * (680 * (1 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = 2720 * N ^ 4 * (1 + t ^ 2)⁻¹ * ((1 + t ^ 2) * (1 + t ^ 2)) := by
            field_simp [(by positivity : (0 : ℝ) < 1 + t ^ 2).ne']; norm_num
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖biCauchy N ((4 : ℂ) + t * I)‖ * ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I)‖ *
            (‖negativeHalfLineLaplace (cx F) (centredZero c)‖ *
              ‖(((4 : ℂ) + t * I) - centredZero c)⁻¹ -
                (((-4 : ℂ) + t * I) - centredZero c)⁻¹‖)
        ≤ (4 * N ^ 4 / ((1 + t ^ 2) * (1 + t ^ 2))) * m4 *
            (halfPoleMass F * (8 * (9 + 2 * |t|) ^ 2 * ‖centredZero c‖⁻¹ ^ 2)) := by
          refine mul_le_mul (mul_le_mul hbi (hLap4_t t) (norm_nonneg _) (by positivity))
            (mul_le_mul hLc hdiff_le (norm_nonneg _) (halfPoleMass_nonneg F))
            (by positivity) (by positivity)
      _ = ((4 * N ^ 4 / ((1 + t ^ 2) * (1 + t ^ 2))) * (8 * (9 + 2 * |t|) ^ 2)) *
            (m4 * halfPoleMass F * ‖centredZero c‖⁻¹ ^ 2) := by ring
      _ ≤ (2720 * N ^ 4 * (1 + t ^ 2)⁻¹) * (m4 * halfPoleMass F * ‖centredZero c‖⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_right hprod_t
            (mul_nonneg (mul_nonneg hm4_0 (halfPoleMass_nonneg F)) (by positivity))
      _ = _ := by ring
  have hdom_sum : ∀ t, HasSum (fun c => dom c t)
      ((2720 * N ^ 4 * m4 * halfPoleMass F * (∑' c : XiZeroCopy, ‖centredZero c‖⁻¹ ^ 2)) *
        (1 + t ^ 2)⁻¹) := fun t =>
    ((summable_inv_sq_centredZero.hasSum.mul_left
      (2720 * N ^ 4 * m4 * halfPoleMass F)).mul_right (1 + t ^ 2)⁻¹).congr_fun
      fun c => by dsimp [dom]
  have hpt_sum : ∀ t : ℝ, HasSum (fun c => term c t)
      (biCauchy N ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        (globalRemainder F ((4 : ℂ) + t * I) - globalRemainder F ((-4 : ℂ) + t * I))) := by
    intro t
    have hxi1 : xi (1 / 2 + ((4 : ℂ) + t * I)) ≠ 0 :=
      xi_ne_zero_of_half_le_abs_re (by simp; norm_num)
    have hxi2 : xi (1 / 2 + ((-4 : ℂ) + t * I)) ≠ 0 :=
      xi_ne_zero_of_half_le_abs_re (by simp; norm_num)
    have htsum := globalRemainder_sub_eq_tsum hd hxi1 hxi2
    have hsum_c : Summable fun c : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero c) *
          ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹) := by
      obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_zeroFree_ball hxi1
      obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_zeroFree_ball hxi2
      exact ((summable_zeroSum_term hd hδ₁ (hb₁ _ (mem_ball_self hδ₁))).sub
        (summable_zeroSum_term hd hδ₂ (hb₂ _ (mem_ball_self hδ₂)))).congr fun c => by ring
    rw [htsum]
    exact hsum_c.hasSum.mul_left _
  have hterm_cont : ∀ c, Continuous (term c) := by
    intro c
    dsimp [term, biCauchy]
    refine ((continuous_const.div ?_ ?_).mul ?_).mul (continuous_const.mul (Continuous.sub ?_ ?_))
    · fun_prop
    · intro t
      exact mul_ne_zero (cauchy_denom_ne_zero hN
          (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))
        (by
          have : 4 * (N : ℂ) ^ 2 = ((2 * N : ℝ) : ℂ) ^ 2 := by push_cast; ring
          rw [this]
          exact cauchy_denom_ne_zero (by linarith)
            (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))
    · rw [continuous_iff_continuousAt]; intro t
      exact ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by show -(12 / 2 : ℝ) < ((-4 : ℂ) - t * I).re; simp; norm_num))).continuousAt.comp
        (by fun_prop)
    · exact (by fun_prop : Continuous fun t : ℝ => ((4 : ℂ) + t * I) - centredZero c).inv₀
        fun t e => by
          have := congrArg Complex.re e; simp at this
          linarith [(abs_lt.mp (abs_re_centredZero_lt c)).2]
    · exact (by fun_prop : Continuous fun t : ℝ => ((-4 : ℂ) + t * I) - centredZero c).inv₀
        fun t e => by
          have := congrArg Complex.re e; simp at this
          linarith [(abs_lt.mp (abs_re_centredZero_lt c)).1]
  have hfub := MeasureTheory.hasSum_integral_of_dominated_convergence dom
    (fun c => (hterm_cont c).aestronglyMeasurable)
    (fun c => Eventually.of_forall (hterm_norm c))
    (Eventually.of_forall fun t => (hdom_sum t).summable)
    ((integrable_inv_one_add_sq.const_mul _).congr
      (Eventually.of_forall fun t => (hdom_sum t).tsum_eq.symm))
    (Eventually.of_forall hpt_sum)
  -- Evaluate each zero's integral via `biCauchy_eq_sub` and `integral_singleCauchy_zero_term`
  have hterm_int_eq : ∀ c : XiZeroCopy, (∫ t : ℝ, term c t) =
      (2 * Real.pi : ℂ) * (biCauchy N (centredZero c) *
        negativeHalfLineLaplace (cx F) (centredZero c) *
        negativeHalfLineLaplace (cx F) (-centredZero c) +
        (4 / 3 : ℂ) * ((N : ℂ) / 2) * negativeHalfLineLaplace (cx F) (N : ℂ) *
          (negativeHalfLineLaplace (cx F) (centredZero c) *
            ((-(N : ℂ) - centredZero c)⁻¹ - (-(N : ℂ) - 8 - centredZero c)⁻¹)) -
        (1 / 3 : ℂ) * (((2 * N : ℝ) : ℂ) / 2) * negativeHalfLineLaplace (cx F) ((2 * N : ℝ) : ℂ) *
          (negativeHalfLineLaplace (cx F) (centredZero c) *
            ((-((2 * N : ℝ) : ℂ) - centredZero c)⁻¹ -
              (-((2 * N : ℝ) : ℂ) - 8 - centredZero c)⁻¹))) := by
    intro c
    have hsplit_bi : ∀ t : ℝ, term c t =
        negativeHalfLineLaplace (cx F) (centredZero c) *
          ((4 / 3 : ℂ) * (singleCauchy N ((4 : ℂ) + t * I) *
              negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
              ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹)) -
            (1 / 3 : ℂ) * (singleCauchy (2 * N) ((4 : ℂ) + t * I) *
              negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
              ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹))) := by
      intro t
      dsimp [term]
      rw [biCauchy_eq_sub (by linarith)
        (cauchy_denom_ne_zero hN
          (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))
        (by
          have : 4 * (N : ℂ) ^ 2 = ((2 * N : ℝ) : ℂ) ^ 2 := by push_cast; ring
          rw [this]
          exact cauchy_denom_ne_zero (by linarith)
            (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))]
      ring
    have hint_s : ∀ L : ℝ, 20 ≤ L → Integrable fun t : ℝ =>
        singleCauchy L ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
          ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹) := by
      intro L hL
      have hcont : Continuous fun t : ℝ =>
          singleCauchy L ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
            ((((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹) := by
        dsimp [singleCauchy]
        refine ((continuous_const.div (by fun_prop) fun t => cauchy_denom_ne_zero hL
          (fun e => by have := congrArg Complex.re e; simp at this; linarith)
          (by simp; linarith)).mul ?_).mul (Continuous.sub ?_ ?_)
        · rw [continuous_iff_continuousAt]; intro t
          exact ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
            ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
              (by show -(12 / 2 : ℝ) < ((-4 : ℂ) - t * I).re; simp; norm_num))).continuousAt.comp
            (by fun_prop)
        · exact (by fun_prop : Continuous fun t : ℝ => ((4 : ℂ) + t * I) - centredZero c).inv₀
            fun t e => by
              have := congrArg Complex.re e; simp at this
              linarith [(abs_lt.mp (abs_re_centredZero_lt c)).2]
        · exact (by fun_prop : Continuous fun t : ℝ => ((-4 : ℂ) + t * I) - centredZero c).inv₀
            fun t e => by
              have := congrArg Complex.re e; simp at this
              linarith [(abs_lt.mp (abs_re_centredZero_lt c)).1]
      refine (integrable_inv_one_add_sq.const_mul (4 * L ^ 2 * m4 * 8 * 4)).mono'
        hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
      have hsc : ‖singleCauchy L ((4 : ℂ) + t * I)‖ ≤ (4 / 3 : ℝ) * L ^ 2 * (1 + t ^ 2)⁻¹ := by
        unfold singleCauchy
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ L)]
        have hd0 := norm_sub_sq_on_four_ge (by linarith) t
        have hle : (3 / 4 : ℝ) * (1 + t ^ 2) ≤ ‖(L : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
          (by nlinarith : (3 / 4 : ℝ) * (1 + t ^ 2) ≤ (3 / 4) * L ^ 2 + t ^ 2).trans hd0
        exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hle).trans_eq (by
          field_simp [(by positivity : (0 : ℝ) < 1 + t ^ 2).ne'])
      have hn1 : 1 / 2 ≤ ‖((4 : ℂ) + t * I) - centredZero c‖ :=
        half_le_norm_sub_centredZero (by simp) c
      have hn2 : 1 / 2 ≤ ‖((-4 : ℂ) + t * I) - centredZero c‖ :=
        half_le_norm_sub_centredZero (by simp) c
      have hd_pair : ‖(((4 : ℂ) + t * I) - centredZero c)⁻¹ -
          (((-4 : ℂ) + t * I) - centredZero c)⁻¹‖ ≤ 32 := by
        have heq : (((4 : ℂ) + t * I) - centredZero c)⁻¹ -
            (((-4 : ℂ) + t * I) - centredZero c)⁻¹ =
            (-8 : ℂ) / ((((4 : ℂ) + t * I) - centredZero c) *
              (((-4 : ℂ) + t * I) - centredZero c)) := by
          field_simp [(by linarith : 0 < ‖((4 : ℂ) + t * I) - centredZero c‖).ne' |> norm_ne_zero_iff.mp,
            (by linarith : 0 < ‖((-4 : ℂ) + t * I) - centredZero c‖).ne' |> norm_ne_zero_iff.mp]
          ring
        rw [heq, norm_div, show ‖(-8 : ℂ)‖ = 8 by norm_num, norm_mul]
        have : (1 / 4 : ℝ) ≤ ‖((4 : ℂ) + t * I) - centredZero c‖ *
            ‖((-4 : ℂ) + t * I) - centredZero c‖ := by
          have := mul_le_mul hn1 hn2 (by norm_num) (norm_nonneg _)
          linarith
        exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num) this).trans_eq (by norm_num)
      rw [norm_mul, norm_mul]
      calc ‖singleCauchy L ((4 : ℂ) + t * I)‖ *
              ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I)‖ *
              ‖(((4 : ℂ) + t * I) - centredZero c)⁻¹ - (((-4 : ℂ) + t * I) - centredZero c)⁻¹‖
          ≤ ((4 / 3 : ℝ) * L ^ 2 * (1 + t ^ 2)⁻¹) * m4 * 32 :=
            mul_le_mul (mul_le_mul hsc (hLap4_t t) (norm_nonneg _) (by positivity)) hd_pair
              (norm_nonneg _) (by positivity)
        _ ≤ (4 * L ^ 2 * m4 * 8 * 4) * (1 + t ^ 2)⁻¹ := by
            nlinarith [mul_nonneg (mul_nonneg (sq_nonneg L) hm4_0)
              (inv_nonneg.mpr (by positivity : 0 ≤ 1 + t ^ 2))]
    rw [integral_congr_ae (Eventually.of_forall hsplit_bi), integral_const_mul,
      integral_sub ((hint_s N hN).const_mul _) ((hint_s (2 * N) (by linarith)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_singleCauchy_zero_term hW ht hF hN c,
      integral_singleCauchy_zero_term hW ht hF (L := 2 * N) (by linarith) c]
    have hz_abs := abs_lt.mp (abs_re_centredZero_lt c)
    have hbi_z := biCauchy_eq_sub (N := N) (by linarith)
      (cauchy_denom_ne_zero hN
        (fun e => by have := congrArg Complex.re e; simp at this; linarith [hz_abs.1])
        (by linarith [hz_abs.2]))
      (by
        have : 4 * (N : ℂ) ^ 2 = ((2 * N : ℝ) : ℂ) ^ 2 := by push_cast; ring
        rw [this]
        exact cauchy_denom_ne_zero (by linarith)
          (fun e => by have := congrArg Complex.re e; simp at this; linarith [hz_abs.1])
          (by linarith [hz_abs.2]))
    rw [hbi_z]
    ring
  -- Sum the right-hand side over `c : XiZeroCopy`
  have hsum_pole_L : ∀ L : ℝ, 20 ≤ L → HasSum (fun c : XiZeroCopy =>
      negativeHalfLineLaplace (cx F) (centredZero c) *
        ((-(L : ℂ) - centredZero c)⁻¹ - (-(L : ℂ) - 8 - centredZero c)⁻¹))
      (globalRemainder F (-(L : ℂ)) - globalRemainder F (-(L : ℂ) - 8)) := by
    intro L hL
    have hx1 : xi (1 / 2 + -(L : ℂ)) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
      rw [Complex.neg_re, Complex.ofReal_re, abs_of_neg (by linarith)]; linarith)
    have hx2 : xi (1 / 2 + (-(L : ℂ) - 8)) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
      have hre2 : (-(L : ℂ) - 8).re = -L - 8 := by simp
      rw [hre2, abs_of_neg (by linarith)]; linarith)
    obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_zeroFree_ball hx1
    obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_zeroFree_ball hx2
    have hs : Summable fun c : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero c) *
          ((-(L : ℂ) - centredZero c)⁻¹ - (-(L : ℂ) - 8 - centredZero c)⁻¹) :=
      ((summable_zeroSum_term hd hδ₁ (hb₁ _ (mem_ball_self hδ₁))).sub
        (summable_zeroSum_term hd hδ₂ (hb₂ _ (mem_ball_self hδ₂)))).congr fun c => by ring
    rw [globalRemainder_sub_eq_tsum hd hx1 hx2]
    exact hs.hasSum
  have hs_main : Summable fun c : XiZeroCopy =>
      biCauchy N (centredZero c) * negativeHalfLineLaplace (cx F) (centredZero c) *
        negativeHalfLineLaplace (cx F) (-centredZero c) := by
    have htotal : Summable fun c => ∫ t : ℝ, term c t := hfub.summable
    have hsub1 := ((hsum_pole_L N hN).summable.mul_left
      ((4 / 3 : ℂ) * ((N : ℂ) / 2) * negativeHalfLineLaplace (cx F) (N : ℂ)))
    have hsub2 := ((hsum_pole_L (2 * N) (by linarith)).summable.mul_left
      ((1 / 3 : ℂ) * (((2 * N : ℝ) : ℂ) / 2) *
        negativeHalfLineLaplace (cx F) ((2 * N : ℝ) : ℂ)))
    have hpi_ne : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hdiv := (htotal.mul_left (2 * Real.pi : ℂ)⁻¹).congr fun c => by
      rw [hterm_int_eq c, inv_mul_cancel_left₀ hpi_ne]
    exact ((hdiv.sub hsub1).add hsub2).congr fun c => by ring
  have hRHS_eq : (∑' c : XiZeroCopy, ∫ t : ℝ, term c t) =
      (2 * Real.pi : ℂ) *
        (((4 / 3 : ℂ) * ((N : ℂ) / 2) * negativeHalfLineLaplace (cx F) (N : ℂ) *
            (globalRemainder F (-(N : ℂ)) - globalRemainder F (-(N : ℂ) - 8)) -
          (1 / 3 : ℂ) * (((2 * N : ℝ) : ℂ) / 2) *
            negativeHalfLineLaplace (cx F) ((2 * N : ℝ) : ℂ) *
            (globalRemainder F (-((2 * N : ℝ) : ℂ)) -
              globalRemainder F (-((2 * N : ℝ) : ℂ) - 8))) +
          ∑' c : XiZeroCopy, biCauchy N (centredZero c) *
            negativeHalfLineLaplace (cx F) (centredZero c) *
            negativeHalfLineLaplace (cx F) (-centredZero c)) := by
    have hs1 := (hsum_pole_L N hN).mul_left
      ((4 / 3 : ℂ) * ((N : ℂ) / 2) * negativeHalfLineLaplace (cx F) (N : ℂ))
    have hs2 := (hsum_pole_L (2 * N) (by linarith)).mul_left
      ((1 / 3 : ℂ) * (((2 * N : ℝ) : ℂ) / 2) *
        negativeHalfLineLaplace (cx F) ((2 * N : ℝ) : ℂ))
    have hcomb := ((hs_main.hasSum.add hs1).sub hs2).mul_left (2 * Real.pi : ℂ)
    refine (hcomb.congr_fun fun c => ?_).tsum_eq.trans (by ring)
    rw [hterm_int_eq c]
  -- Split the left-hand integral into `4 + t * I` and `-4 + t * I`
  obtain ⟨hnorm_int, _⟩ := criticalState_norm_sq_four_integrable_and_pos hW ht hF
  have hint_pos4 : Integrable fun t : ℝ =>
      biCauchy N ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((4 : ℂ) + t * I) := by
    have heq : (fun t : ℝ => biCauchy N ((4 : ℂ) + t * I) *
          negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
          globalRemainder F ((4 : ℂ) + t * I)) =
        fun t : ℝ => -(criticalAliasCoefficient W₀ : ℂ) *
          (biCauchy N ((4 : ℂ) + t * I) *
            ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ)) := by
      funext t
      rw [criticalState_globalRemainder_four hW ht hF t]
      have hconj_arg : (-4 : ℂ) - t * I = conj ((-4 : ℂ) + t * I) := by
        apply Complex.ext <;> simp
      rw [hconj_arg, criticalState_laplace_conj]
      have hnsq : conj (negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)) *
          negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I) =
          ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc biCauchy N ((4 : ℂ) + t * I) *
              conj (negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)) *
              (-(criticalAliasCoefficient W₀ : ℂ) *
                negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I))
          = -(criticalAliasCoefficient W₀ : ℂ) * (biCauchy N ((4 : ℂ) + t * I) *
              (conj (negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)) *
                negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I))) := by ring
        _ = _ := by rw [hnsq]
    rw [heq]
    refine Integrable.const_mul ?_ _
    refine (hnorm_int.const_mul 2).mono' ?_ (Eventually.of_forall fun t => ?_)
    · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
      · dsimp [biCauchy]
        refine continuous_const.div (by fun_prop) fun t => mul_ne_zero
          (cauchy_denom_ne_zero hN
            (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))
          (by
            have : 4 * (N : ℂ) ^ 2 = ((2 * N : ℝ) : ℂ) ^ 2 := by push_cast; ring
            rw [this]
            exact cauchy_denom_ne_zero (by linarith)
              (fun e => by have := congrArg Complex.re e; simp at this; linarith)
              (by simp; linarith))
      · refine Complex.continuous_ofReal.comp ((continuous_norm.comp ?_).pow 2)
        rw [continuous_iff_continuousAt]; intro t
        exact ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (by show -(12 / 2 : ℝ) < ((-4 : ℂ) + t * I).re; simp; norm_num))).continuousAt.comp
          (by fun_prop)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (norm_biCauchy_four_le (by linarith) t) (sq_nonneg _)
  obtain ⟨KL, hKL⟩ := exists_bound_leftRemainder hd
  have hKL0 : 0 ≤ KL := (norm_nonneg _).trans (hKL (-1) (by simp))
  have hint_single_left : ∀ L : ℝ, 20 ≤ L → Integrable fun t : ℝ =>
      singleCauchy L ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I) := by
    intro L hL
    have hcont : Continuous fun t : ℝ =>
        singleCauchy L ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
          globalRemainder F ((-4 : ℂ) + t * I) := by
      dsimp [singleCauchy]
      refine ((continuous_const.div (by fun_prop) fun t => cauchy_denom_ne_zero hL
        (fun e => by have := congrArg Complex.re e; simp at this; linarith)
        (by simp; linarith)).mul ?_).mul ?_
      · rw [continuous_iff_continuousAt]; intro t
        exact ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (by show -(12 / 2 : ℝ) < ((-4 : ℂ) - t * I).re; simp; norm_num))).continuousAt.comp
          (by fun_prop)
      · rw [continuous_iff_continuousAt]; intro t
        exact ContinuousAt.comp (g := globalRemainder F) (f := fun s : ℝ => (-4 : ℂ) + s * I)
          (differentiableAt_globalRemainder hd (p := (-4 : ℂ) + t * I)
            (fun h' => absurd h' (by simp; norm_num))).continuousAt
          (by fun_prop : Continuous fun s : ℝ => (-4 : ℂ) + s * I).continuousAt
    refine (integrable_inv_one_add_sq.const_mul (2 * L ^ 2 * m4 * KL)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have hsc : ‖singleCauchy L ((4 : ℂ) + t * I)‖ ≤ (4 / 3 : ℝ) * L ^ 2 * (1 + t ^ 2)⁻¹ := by
      unfold singleCauchy
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ L)]
      have hd0 := norm_sub_sq_on_four_ge (by linarith) t
      have hle : (3 / 4 : ℝ) * (1 + t ^ 2) ≤ ‖(L : ℂ) ^ 2 - ((4 : ℂ) + t * I) ^ 2‖ :=
        (by nlinarith : (3 / 4 : ℝ) * (1 + t ^ 2) ≤ (3 / 4) * L ^ 2 + t ^ 2).trans hd0
      exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hle).trans_eq (by
        field_simp [(by positivity : (0 : ℝ) < 1 + t ^ 2).ne'])
    have hrem : ‖globalRemainder F ((-4 : ℂ) + t * I)‖ ≤ KL := by
      have hlt : ((-4 : ℂ) + t * I).re < -(1 / 2) := by simp; norm_num
      rw [globalRemainder, if_neg (not_lt.mpr hlt.le), if_pos hlt]
      exact hKL _ (by simp)
    rw [norm_mul, norm_mul]
    calc ‖singleCauchy L ((4 : ℂ) + t * I)‖ *
            ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I)‖ *
            ‖globalRemainder F ((-4 : ℂ) + t * I)‖
        ≤ ((4 / 3 : ℝ) * L ^ 2 * (1 + t ^ 2)⁻¹) * m4 * KL :=
          mul_le_mul (mul_le_mul hsc (hLap4_t t) (norm_nonneg _) (by positivity))
            hrem (norm_nonneg _) (by positivity)
      _ ≤ (2 * L ^ 2 * m4 * KL) * (1 + t ^ 2)⁻¹ := by
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg L) hm4_0)
            (mul_nonneg hKL0 (inv_nonneg.mpr (by positivity : 0 ≤ 1 + t ^ 2)))]
  have hleft_split : (fun t : ℝ => biCauchy N ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I)) =
      fun t : ℝ => (4 / 3 : ℂ) * (singleCauchy N ((4 : ℂ) + t * I) *
          negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
          globalRemainder F ((-4 : ℂ) + t * I)) -
        (1 / 3 : ℂ) * (singleCauchy (2 * N) ((4 : ℂ) + t * I) *
          negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
          globalRemainder F ((-4 : ℂ) + t * I)) := by
    funext t
    rw [biCauchy_eq_sub (by linarith)
      (cauchy_denom_ne_zero hN
        (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))
      (by
        have : 4 * (N : ℂ) ^ 2 = ((2 * N : ℝ) : ℂ) ^ 2 := by push_cast; ring
        rw [this]
        exact cauchy_denom_ne_zero (by linarith)
          (fun e => by have := congrArg Complex.re e; simp at this; linarith) (by simp; linarith))]
    ring
  have hint_neg4 : Integrable fun t : ℝ =>
      biCauchy N ((4 : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I) := by
    rw [hleft_split]
    exact ((hint_single_left N hN).const_mul _).sub
      ((hint_single_left (2 * N) (by linarith)).const_mul _)
  have hneg4_val : (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I)) =
      (2 * Real.pi : ℂ) *
        ((4 / 3 : ℂ) * ((N : ℂ) / 2) * negativeHalfLineLaplace (cx F) (N : ℂ) *
          globalRemainder F (-(N : ℂ) - 8) -
        (1 / 3 : ℂ) * (((2 * N : ℝ) : ℂ) / 2) *
          negativeHalfLineLaplace (cx F) ((2 * N : ℝ) : ℂ) *
          globalRemainder F (-((2 * N : ℝ) : ℂ) - 8)) := by
    rw [integral_congr_ae (Eventually.of_forall (congrFun hleft_split)),
      integral_sub ((hint_single_left N hN).const_mul _)
        ((hint_single_left (2 * N) (by linarith)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_singleCauchy_left_line hW ht hF hN,
      integral_singleCauchy_left_line hW ht hF (L := 2 * N) (by linarith)]
    ring
  have hpos4_val : (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((4 : ℂ) + t * I)) =
      -(criticalAliasCoefficient W₀ : ℂ) *
        (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
          ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [criticalState_globalRemainder_four hW ht hF t]
    have hconj_arg : (-4 : ℂ) - t * I = conj ((-4 : ℂ) + t * I) := by
      apply Complex.ext <;> simp
    rw [hconj_arg, criticalState_laplace_conj]
    have hnsq : conj (negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I) =
        ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc biCauchy N ((4 : ℂ) + t * I) *
            conj (negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)) *
            (-(criticalAliasCoefficient W₀ : ℂ) *
              negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I))
        = -(criticalAliasCoefficient W₀ : ℂ) * (biCauchy N ((4 : ℂ) + t * I) *
            (conj (negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)) *
              negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I))) := by ring
      _ = _ := by rw [hnsq]
  have hLHS_sub : (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        (globalRemainder F ((4 : ℂ) + t * I) - globalRemainder F ((-4 : ℂ) + t * I))) =
      (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((4 : ℂ) + t * I)) -
      (∫ t : ℝ, biCauchy N ((4 : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((-4 : ℂ) - t * I) *
        globalRemainder F ((-4 : ℂ) + t * I)) := by
    rw [← integral_sub hint_pos4 hint_neg4]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  have hfub_eq := hfub.tsum_eq
  rw [hRHS_eq, hLHS_sub, hpos4_val, hneg4_val] at hfub_eq
  push_cast at hfub_eq ⊢
  linear_combination -hfub_eq

/-- **Every critical half-line ground state sees at least one left off-critical zero:** there exists
a centred zero copy `c` with `Re(centredZero c) < 0` and `L F(centredZero c) ≠ 0` (together with
`L F(-centredZero c) ≠ 0`). -/
theorem criticalState_exists_seen_left_centredZero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : XiZeroCopy, (centredZero c).re < 0 ∧
      negativeHalfLineLaplace (cx F) (centredZero c) ≠ 0 ∧
      negativeHalfLineLaplace (cx F) (-centredZero c) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hoff_zero : ∀ c : XiZeroCopy, (centredZero c).re ≠ 0 →
      negativeHalfLineLaplace (cx F) (centredZero c) *
        negativeHalfLineLaplace (cx F) (-centredZero c) = 0 := by
    intro c hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · by_cases hL : negativeHalfLineLaplace (cx F) (centredZero c) = 0
      · rw [hL, zero_mul]
      · rw [hall c hlt hL, mul_zero]
    · have hxi_neg : xi (1 / 2 + -centredZero c) = 0 := by
        rw [show (1 : ℂ) / 2 + -centredZero c = 1 - (1 / 2 + centredZero c) by ring,
          xi_one_sub]
        exact xi_centredZero c
      obtain ⟨c', hc'⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi_neg
      have hzc' : centredZero c' = -centredZero c := by
        rw [centredZero, hc']; ring
      have hlt' : (centredZero c').re < 0 := by rw [hzc']; simp; linarith
      by_cases hL' : negativeHalfLineLaplace (cx F) (centredZero c') = 0
      · rw [← hzc', hL', mul_zero]
      · have hneg' := hall c' hlt' hL'
        rw [hzc', neg_neg] at hneg'
        rw [hneg', zero_mul]
  -- Under `hoff_zero`, the zero sum has nonnegative real part for every `N ≥ 20`
  have hsum_re_nonneg : ∀ N : ℝ, 20 ≤ N →
      0 ≤ (∑' c : XiZeroCopy, biCauchy N (centredZero c) *
        negativeHalfLineLaplace (cx F) (centredZero c) *
        negativeHalfLineLaplace (cx F) (-centredZero c)).re := by
    intro N hN
    have hd := criticalHalfLineEnergyDomain_of_groundState hF
    have hs : Summable fun c : XiZeroCopy => biCauchy N (centredZero c) *
        negativeHalfLineLaplace (cx F) (centredZero c) *
        negativeHalfLineLaplace (cx F) (-centredZero c) := by
      refine Summable.of_norm_bounded
        (summable_inv_sq_centredZero.mul_left (16 * N ^ 4 * halfPoleMass F ^ 2)) fun c => ?_
      have hz_abs := abs_lt.mp (abs_re_centredZero_lt c)
      have hLc1 : ‖negativeHalfLineLaplace (cx F) (centredZero c)‖ ≤ halfPoleMass F :=
        norm_laplace_le_halfPoleMass hd (by linarith [hz_abs.1])
      have hLc2 : ‖negativeHalfLineLaplace (cx F) (-centredZero c)‖ ≤ halfPoleMass F :=
        norm_laplace_le_halfPoleMass hd (by simp; linarith [hz_abs.2])
      have hn1 : 1 ≤ ‖(N : ℂ) - centredZero c‖ := by
        have : 1 ≤ |(N : ℂ).re - (centredZero c).re| := by
          simp; rw [abs_of_pos (by linarith [hz_abs.2])]; linarith [hz_abs.2]
        exact this.trans (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _)
      have hn2 : 1 ≤ ‖(N : ℂ) + centredZero c‖ := by
        have : 1 ≤ |(N : ℂ).re - (-centredZero c).re| := by
          simp; rw [abs_of_pos (by linarith [hz_abs.1])]; linarith [hz_abs.1]
        exact this.trans (by rw [← Complex.sub_re, sub_neg_eq_add]; exact Complex.abs_re_le_norm _)
      have hn3 : ‖centredZero c‖ / 2 ≤ ‖2 * (N : ℂ) - centredZero c‖ ∧
          ‖centredZero c‖ / 2 ≤ ‖2 * (N : ℂ) + centredZero c‖ := by
        have h_each : ∀ M : ℝ, 20 ≤ M → ∀ s : ℂ, |s.re| < 1 / 2 →
            ‖s‖ / 2 ≤ ‖(M : ℂ) - s‖ := by
          intro M hM s hs
          have h1 : 19 ≤ |(M : ℂ).re - s.re| := by
            simp; rw [abs_of_pos (by linarith [(abs_lt.mp hs).2])]; linarith [(abs_lt.mp hs).2]
          have hr : 19 ≤ ‖(M : ℂ) - s‖ :=
            h1.trans (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _)
          have hi : |s.im| ≤ ‖(M : ℂ) - s‖ := by
            have : |((M : ℂ) - s).im| = |s.im| := by simp
            rw [← this]; exact Complex.abs_im_le_norm _
          have hns : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
          linarith [(abs_lt.mp hs).2]
        refine ⟨?_, ?_⟩
        · simpa [show ((2 * N : ℝ) : ℂ) = 2 * (N : ℂ) by push_cast; rfl] using
            h_each (2 * N) (by linarith) (centredZero c) (abs_re_centredZero_lt c)
        · have := h_each (2 * N) (by linarith) (-centredZero c)
            (by simpa using abs_re_centredZero_lt c)
          simpa [sub_neg_eq_add, show ((2 * N : ℝ) : ℂ) = 2 * (N : ℂ) by push_cast; rfl] using this
      have hbi_le : ‖biCauchy N (centredZero c)‖ ≤ 16 * N ^ 4 * ‖centredZero c‖⁻¹ ^ 2 := by
        unfold biCauchy
        have hf1 : (N : ℂ) ^ 2 - (centredZero c) ^ 2 =
            ((N : ℂ) - centredZero c) * ((N : ℂ) + centredZero c) := by ring
        have hf2 : 4 * (N : ℂ) ^ 2 - (centredZero c) ^ 2 =
            (2 * (N : ℂ) - centredZero c) * (2 * (N : ℂ) + centredZero c) := by ring
        rw [hf1, hf2, norm_div, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg (by linarith : 0 ≤ N), show ‖(4 : ℂ)‖ = 4 by norm_num,
          norm_mul, norm_mul, norm_mul]
        have hzpos : 0 < ‖centredZero c‖ := zero_lt_one.trans (one_lt_norm_centredZero c)
        have hden : 1 * (‖centredZero c‖ / 2 * (‖centredZero c‖ / 2)) ≤
            (‖(N : ℂ) - centredZero c‖ * ‖(N : ℂ) + centredZero c‖) *
              (‖2 * (N : ℂ) - centredZero c‖ * ‖2 * (N : ℂ) + centredZero c‖) :=
          mul_le_mul (by nlinarith [hn1, hn2])
            (mul_le_mul hn3.1 hn3.2 (by positivity) (norm_nonneg _))
            (by positivity) (by positivity)
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans_eq ?_
        field_simp [hzpos.ne']; ring
      rw [norm_mul, norm_mul]
      calc ‖biCauchy N (centredZero c)‖ * ‖negativeHalfLineLaplace (cx F) (centredZero c)‖ *
              ‖negativeHalfLineLaplace (cx F) (-centredZero c)‖
          ≤ (16 * N ^ 4 * ‖centredZero c‖⁻¹ ^ 2) * halfPoleMass F * halfPoleMass F :=
            mul_le_mul (mul_le_mul hbi_le hLc1 (norm_nonneg _) (by positivity))
              hLc2 (norm_nonneg _) (mul_nonneg (by positivity) (halfPoleMass_nonneg F))
        _ = _ := by ring
    have hre_tsum := (Complex.reCLM.hasSum hs.hasSum).tsum_eq
    dsimp at hre_tsum
    rw [← hre_tsum]
    refine tsum_nonneg fun c => ?_
    change 0 ≤ (biCauchy N (centredZero c) *
      negativeHalfLineLaplace (cx F) (centredZero c) *
      negativeHalfLineLaplace (cx F) (-centredZero c)).re
    by_cases hre0 : (centredZero c).re = 0
    · exact biCauchy_pureImag_real_nonneg (by linarith) hre0 F
    · rw [mul_assoc, hoff_zero c hre0, mul_zero, Complex.zero_re]
  -- Pass `N → ∞` on both sides of `biCauchy_state_identity`
  obtain ⟨hnorm_int, hnorm_pos⟩ := criticalState_norm_sq_four_integrable_and_pos hW ht hF
  have ha_pos := criticalAliasCoefficient_positive hW
  have hb12 := (criticalHalfLineGroundState_exponential_bounds hW ht hF).2 12 (by norm_num)
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hLHS_tend : Tendsto (fun n : ℕ =>
      (-(criticalAliasCoefficient W₀ : ℂ) *
        (∫ t : ℝ, biCauchy ((n : ℝ) + 20) ((4 : ℂ) + t * I) *
          ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ))).re)
      atTop (𝓝 (-criticalAliasCoefficient W₀ *
        ∫ t : ℝ, ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2)) := by
    have ht_N : Tendsto (fun n : ℕ => (n : ℝ) + 20) atTop atTop :=
      tendsto_atTop_add_const_right _ 20 tendsto_natCast_atTop_atTop
    have hdom_int : Tendsto (fun n : ℕ =>
        ∫ t : ℝ, biCauchy ((n : ℝ) + 20) ((4 : ℂ) + t * I) *
          ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ))
        atTop (𝓝 (∫ t : ℝ, (1 : ℂ) *
          ((‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ))) := by
      refine tendsto_integral_of_dominated_convergence
        (fun t => 2 * ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2)
        (fun n => ?_) (hnorm_int.const_mul 2) (fun n => Eventually.of_forall fun t => ?_)
        (Eventually.of_forall fun t => ?_)
      · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ ?_)
        · dsimp [biCauchy]
          have hN20 : (20 : ℝ) ≤ (n : ℝ) + 20 := by linarith [Nat.cast_nonneg (α := ℝ) n]
          refine continuous_const.div (by fun_prop) fun t => mul_ne_zero
            (cauchy_denom_ne_zero hN20
              (fun e => by have := congrArg Complex.re e; simp at this; linarith)
              (by simp; linarith))
            (by
              have : 4 * (((n : ℝ) + 20 : ℝ) : ℂ) ^ 2 = ((2 * ((n : ℝ) + 20) : ℝ) : ℂ) ^ 2 := by
                push_cast; ring
              rw [this]
              exact cauchy_denom_ne_zero (by linarith)
                (fun e => by have := congrArg Complex.re e; simp at this; linarith)
                (by simp; linarith))
        · refine Complex.continuous_ofReal.comp ((continuous_norm.comp ?_).pow 2)
          rw [continuous_iff_continuousAt]; intro t
          exact ((differentiableOn_laplace_of_sq hd.meas hd.support hb12).differentiableAt
            ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
              (by show -(12 / 2 : ℝ) < ((-4 : ℂ) + t * I).re; simp; norm_num))).continuousAt.comp
            (by fun_prop)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right
          (norm_biCauchy_four_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) t) (sq_nonneg _)
      · exact ((tendsto_biCauchy_four t).comp ht_N).mul_const _
    have hmul := (Complex.continuous_re.continuousAt.tendsto.comp
      (hdom_int.const_mul (-(criticalAliasCoefficient W₀ : ℂ))))
    simpa only [one_mul, Function.comp_def, integral_complex_ofReal, ← Complex.ofReal_neg,
      ← Complex.ofReal_mul, Complex.ofReal_re, neg_mul] using hmul
  -- Boundary terms tend to zero as `n → ∞`
  obtain ⟨C₁, hC₁0, hLap_right⟩ := criticalState_laplace_decay_right hW ht hF
  have hbnd_tend : ∀ k : ℝ, 1 ≤ k → Tendsto (fun n : ℕ =>
      ((k * ((n : ℝ) + 20) : ℝ) : ℂ) *
        negativeHalfLineLaplace (cx F) ((k * ((n : ℝ) + 20) : ℝ) : ℂ) *
        globalRemainder F (-((k * ((n : ℝ) + 20) : ℝ) : ℂ))) atTop (𝓝 0) := by
    intro k hk
    have hrem_tend : Tendsto (fun n : ℕ =>
        globalRemainder F (-((k * ((n : ℝ) + 20) : ℝ) : ℂ))) atTop (𝓝 0) := by
      refine (tendsto_globalRemainder_left hd).comp ?_
      rw [tendsto_comap_iff]
      have : (Complex.re ∘ fun n : ℕ => -((k * ((n : ℝ) + 20) : ℝ) : ℂ)) =
          fun n : ℕ => -(k * ((n : ℝ) + 20)) := by funext n; simp
      rw [this]
      exact tendsto_neg_atTop_atBot.comp
        ((tendsto_atTop_add_const_right _ 20 tendsto_natCast_atTop_atTop).const_mul_atTop
          (by linarith))
    refine squeeze_zero_norm (a := fun n : ℕ => C₁ *
      ‖globalRemainder F (-((k * ((n : ℝ) + 20) : ℝ) : ℂ))‖) (fun n => ?_)
      (by simpa using hrem_tend.norm.const_mul C₁)
    have hpos_x : 0 < k * ((n : ℝ) + 20) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hL := hLap_right ((k * ((n : ℝ) + 20) : ℝ) : ℂ) (by simp [hpos_x.le])
    simp only [Complex.ofReal_re] at hL
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos_x.le]
    have h1 : k * ((n : ℝ) + 20) * (C₁ / (k * ((n : ℝ) + 20) + 1)) ≤ C₁ := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith [hC₁0]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hL hpos_x.le).trans h1) (norm_nonneg _)
  have hbnd_comb : Tendsto (fun n : ℕ =>
      ((2 * Real.pi : ℂ) *
        (((2 * (((n : ℝ) + 20 : ℝ) : ℂ) / 3) *
            negativeHalfLineLaplace (cx F) (((n : ℝ) + 20 : ℝ) : ℂ) *
            globalRemainder F (-(((n : ℝ) + 20 : ℝ) : ℂ)) -
          ((((n : ℝ) + 20 : ℝ) : ℂ) / 3) *
            negativeHalfLineLaplace (cx F) (2 * (((n : ℝ) + 20 : ℝ) : ℂ)) *
            globalRemainder F (-(2 * (((n : ℝ) + 20 : ℝ) : ℂ)))))).re) atTop (𝓝 0) := by
    have h1 := (hbnd_tend 1 le_rfl).const_mul (2 / 3 : ℂ)
    have h2 := (hbnd_tend 2 (by norm_num)).const_mul (1 / 6 : ℂ)
    have h3 := Complex.continuous_re.continuousAt.tendsto.comp
      ((h1.sub h2).const_mul (2 * Real.pi : ℂ))
    simp only [mul_zero, sub_zero, Complex.zero_re, Function.comp_def] at h3
    refine h3.congr fun n => ?_
    congr 1
    push_cast
    ring
  -- Contradiction for large `n`
  set L_neg : ℝ := -criticalAliasCoefficient W₀ *
    ∫ t : ℝ, ‖negativeHalfLineLaplace (cx F) ((-4 : ℂ) + t * I)‖ ^ 2
  have hL_neg : L_neg < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos ha_pos) hnorm_pos
  have hev1 := hLHS_tend.eventually (gt_mem_nhds (by linarith : L_neg < L_neg / 2))
  have hev2 := hbnd_comb.eventually (lt_mem_nhds (by linarith : L_neg / 2 < 0))
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hN20 : (20 : ℝ) ≤ (n : ℝ) + 20 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hid := congrArg Complex.re (biCauchy_state_identity hW ht hF hN20)
  have hre_mul : ∀ z : ℂ, ((2 * Real.pi : ℂ) * z).re = (2 * Real.pi) * z.re := fun z => by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  have hre_split : ((2 * Real.pi : ℂ) *
      (((2 * (((n : ℝ) + 20 : ℝ) : ℂ) / 3) *
          negativeHalfLineLaplace (cx F) (((n : ℝ) + 20 : ℝ) : ℂ) *
          globalRemainder F (-(((n : ℝ) + 20 : ℝ) : ℂ)) -
        ((((n : ℝ) + 20 : ℝ) : ℂ) / 3) *
          negativeHalfLineLaplace (cx F) (2 * (((n : ℝ) + 20 : ℝ) : ℂ)) *
          globalRemainder F (-(2 * (((n : ℝ) + 20 : ℝ) : ℂ)))) +
        ∑' c : XiZeroCopy, biCauchy ((n : ℝ) + 20) (centredZero c) *
          negativeHalfLineLaplace (cx F) (centredZero c) *
          negativeHalfLineLaplace (cx F) (-centredZero c))).re =
      ((2 * Real.pi : ℂ) *
        (((2 * (((n : ℝ) + 20 : ℝ) : ℂ) / 3) *
            negativeHalfLineLaplace (cx F) (((n : ℝ) + 20 : ℝ) : ℂ) *
            globalRemainder F (-(((n : ℝ) + 20 : ℝ) : ℂ)) -
          ((((n : ℝ) + 20 : ℝ) : ℂ) / 3) *
            negativeHalfLineLaplace (cx F) (2 * (((n : ℝ) + 20 : ℝ) : ℂ)) *
            globalRemainder F (-(2 * (((n : ℝ) + 20 : ℝ) : ℂ)))))).re +
      (2 * Real.pi) * (∑' c : XiZeroCopy, biCauchy ((n : ℝ) + 20) (centredZero c) *
          negativeHalfLineLaplace (cx F) (centredZero c) *
          negativeHalfLineLaplace (cx F) (-centredZero c)).re := by
    rw [mul_add, Complex.add_re, hre_mul (∑' c : XiZeroCopy, _)]
  rw [hre_split] at hid
  have hsum_ge := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (hsum_re_nonneg ((n : ℝ) + 20) hN20)
  linarith [hid, hn1, hn2, hsum_ge]

/-! ### Corollaries for zeta zeros, poles, and the cleared state product -/

/-- Every critical state sees at least one nontrivial zero `ρ` of `ζ` strictly in the left half
of the critical strip (`0 < Re ρ < ½`). -/
theorem criticalState_exists_seen_left_zetaZero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧
      negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0 := by
  obtain ⟨c, hre_neg, hL, _⟩ := criticalState_exists_seen_left_centredZero hW ht hF
  refine ⟨(c.1 : ℂ), ?_, xiZeroCopy_re_pos c, ?_, ?_⟩
  · exact (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (xiZeroCopy_re_pos c)
      (xiZeroCopy_ne_one c)).mp (xi_xiZeroCopy_eq_zero c)
  · unfold centredZero at hre_neg; simp at hre_neg; linarith
  · exact hL

/-- The meromorphic continuation `stateMeromorphic W₀ F` of a critical state has at least one
non-removable pole strictly in the open left half-strip `-17/2 < Re w < -8`. -/
theorem criticalState_has_left_strip_pole {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ w : ℂ, -(17 / 2) < w.re ∧ w.re < -8 ∧
      ¬ DifferentiableAt ℂ (stateMeromorphic W₀ F) w := by
  obtain ⟨ρ, hζ, hρ0, hρhalf, hL⟩ := criticalState_exists_seen_left_zetaZero hW ht hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨ρ - 17 / 2, by simp; linarith, by simp; linarith, ?_⟩
  exact not_differentiableAt_of_residue (tendsto_stateMeromorphic_residue hd hζ hρ0)
    ((levyResidue_ne_zero_iff hW hζ).mpr hL)

/-- Every critical state has at least one left zero `z` (`Re z < 0`) at which the entire product
`stateXiProduct W₀ F` drops multiplicity by one. -/
theorem criticalState_exists_left_stateXiProduct_order_drop {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : XiZeroCopy, (centredZero c).re < 0 ∧
      analyticOrderAt (stateXiProduct W₀ F) (centredZero c - 8) + 1 =
        analyticOrderAt xi (1 / 2 + centredZero c) := by
  obtain ⟨c, hlt, hL, _⟩ := criticalState_exists_seen_left_centredZero hW ht hF
  exact ⟨c, hlt, analyticOrderAt_stateXiProduct_add_one hW
    (criticalHalfLineEnergyDomain_of_groundState hF) (xi_centredZero c) hL⟩

/-- **Unconditional dichotomy:** either RH holds, or the critical state exists, sees at least one
zero strictly left of the critical line, and has a pole of its meromorphic continuation in
`-17/2 < Re w < -8`. -/
theorem riemannHypothesis_or_criticalState_sees_left_zero :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧
          negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0) ∧
        ∃ w : ℂ, -(17 / 2) < w.re ∧ w.re < -8 ∧
          ¬ DifferentiableAt ℂ (stateMeromorphic W₀ F) w := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      criticalState_exists_seen_left_zetaZero hW ht hF,
      criticalState_has_left_strip_pole hW ht hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
