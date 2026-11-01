import GaloisForLFunctions.RHTower.SharpWeilNearRadicalCount

/-!
# The genus function reads the distinct, resolved zeros

The near radical of Weil's form at level `L` and threshold `ε` is the largest space of Hodge-class
tests (`C²`, supported in `[−L, L]`, transform vanishing at `±i/2`) on which `‖W(f, f)‖ ≤ ε ∫|f|²`.
The construction `RHTower.sharpCount_at_level` produces such a space of dimension
`Shannon(L, T) − #constraints`, the constraints being the values of the transform at the zeros of
height `≤ T = 2πe^{2(L − η/8)}`. Weil's form sees a zero through the *value* of the transform
there: a zero of multiplicity `m` is one constraint, not `m`, and two zeros closer than the
resolution of the threshold are one constraint up to an error the threshold absorbs.

**Main theorem** (`nearRadical_at_level_of_net`). Let `S` be a finite set of zeros such that every
zero of height `≤ T` lies within `δ` of `S` (a `δ`-net), with `δ L ≤ 1`. Then the Hodge-class
tests at level `L` contain a subspace `V` with
`dim V ≥ (2 − η)e^{2L} + (2N(0,T) + c₀ − #S)` and
`‖W(f,f)‖ ≤ (exp(−η²e^{2L}/(300L)) + δ·Q(L)·e^{9L}) ∫|f|²` on `V`, `Q` polynomial in `L`.

Mechanism. The constraint map evaluates `f̂_c` on `S` instead of on all low zeros. An unconstrained
low zero `ρ` lies within `δ` of a constrained `s ∈ S`, and the strip Lipschitz bound
`‖f̂(γ_ρ) − f̂(γ_s)‖ ≤ 2δL e^{L/2} ∫|f|` (`norm_paperFT_sub_le_of_support`) makes its Weil summand
of size `δ e^{O(L)}`, far below the threshold once `δ ≤ exp(−η²e^{2L}/(100L))`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23 RHTower
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Strip bounds for the transform of a test vanishing off `[−U, U]` -/

/-- `‖f̂(z)‖ ≤ e^{|Im z| U} ∫‖f‖` for `f` vanishing off `[−U, U]`. -/
theorem norm_paperFT_le_of_support {f : ℝ → ℂ} {U : ℝ} (hf : Integrable f)
    (hfs : ∀ u, U < |u| → f u = 0) (z : ℂ) :
    ‖paperFT f z‖ ≤ Real.exp (|z.im| * U) * ∫ u, ‖f u‖ := by
  unfold paperFT
  refine (norm_integral_le_of_norm_le (hf.norm.mul_const (Real.exp (|z.im| * U)))
    (Eventually.of_forall fun u => ?_)).trans (le_of_eq (by rw [integral_mul_const, mul_comm]))
  rw [norm_mul]
  by_cases hu : U < |u|
  · rw [hfs u hu, norm_zero, zero_mul]; positivity
  · push Not at hu
    refine mul_le_mul_of_nonneg_left ((norm_cexp_I_mul_le_exp (le_refl _) u).trans ?_)
      (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu (abs_nonneg _))

/-- **Strip Lipschitz bound.** For `f` vanishing off `[−U, U]` and `‖z − w‖ U ≤ 1`,
`‖f̂(z) − f̂(w)‖ ≤ 2 ‖z − w‖ U e^{|Im w| U} ∫‖f‖`. -/
theorem norm_paperFT_sub_le_of_support {f : ℝ → ℂ} {U : ℝ} (hf : Integrable f)
    (hfs : ∀ u, U < |u| → f u = 0) {z w : ℂ} (hzw : ‖z - w‖ * U ≤ 1) :
    ‖paperFT f z - paperFT f w‖ ≤
      2 * ‖z - w‖ * U * Real.exp (|w.im| * U) * ∫ u, ‖f u‖ := by
  unfold paperFT
  rw [← integral_sub (integrable_mul_cexp_of_support hf hfs z)
    (integrable_mul_cexp_of_support hf hfs w)]
  refine (norm_integral_le_of_norm_le
    (hf.norm.mul_const (2 * ‖z - w‖ * U * Real.exp (|w.im| * U)))
    (Eventually.of_forall fun u => ?_)).trans (le_of_eq (by rw [integral_mul_const]; ring))
  by_cases hu : U < |u|
  · simp [hfs u hu]
  · push Not at hu
    have hsplit : cexp (I * z * u) = cexp (I * w * u) * cexp (I * (z - w) * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e : f u * cexp (I * z * u) - f u * cexp (I * w * u) =
        f u * cexp (I * w * u) * (cexp (I * (z - w) * u) - 1) := by
      rw [hsplit]; ring
    rw [e, norm_mul, norm_mul]
    have h1 : ‖cexp (I * w * u)‖ ≤ Real.exp (|w.im| * U) :=
      (norm_cexp_I_mul_le_exp (le_refl _) u).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu (abs_nonneg _)))
    have h3 : ‖I * (z - w) * (u : ℂ)‖ = ‖z - w‖ * |u| := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ‖z - w‖ * |u| ≤ ‖z - w‖ * U := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    have h2 : ‖cexp (I * (z - w) * u) - 1‖ ≤ 2 * (‖z - w‖ * U) := by
      refine (Complex.norm_exp_sub_one_le (by rw [h3]; exact h4.trans hzw)).trans ?_
      rw [h3]; linarith
    calc ‖f u‖ * ‖cexp (I * w * u)‖ * ‖cexp (I * (z - w) * u) - 1‖
        ≤ ‖f u‖ * Real.exp (|w.im| * U) * (2 * (‖z - w‖ * U)) := by gcongr
      _ = ‖f u‖ * (2 * ‖z - w‖ * U * Real.exp (|w.im| * U)) := by ring

/-- **Product bound near a constrained zero.** If `f̂(w) = 0`, `‖z − w‖ ≤ δ`, `δU ≤ 1`, and both
`z`, `w` lie in the strip `|Im| ≤ 1/2`, then `‖f̂(z)‖ ‖f̂(z̄)‖ ≤ 2δU e^{U} (∫‖f‖)²`. -/
theorem norm_paperFT_mul_le_of_near_zero {f : ℝ → ℂ} {U δ : ℝ} (hU : 0 ≤ U) (hf : Integrable f)
    (hfs : ∀ u, U < |u| → f u = 0) {z w : ℂ} (hz : |z.im| ≤ 1 / 2) (hw : |w.im| ≤ 1 / 2)
    (hzw : ‖z - w‖ ≤ δ) (hδU : δ * U ≤ 1) (h0 : paperFT f w = 0) :
    ‖paperFT f z‖ * ‖paperFT f ((starRingEnd ℂ) z)‖ ≤
      2 * δ * U * Real.exp U * (∫ u, ‖f u‖) ^ 2 := by
  have hfI0 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
  have hzwU : ‖z - w‖ * U ≤ 1 := (mul_le_mul_of_nonneg_right hzw hU).trans hδU
  have hexp : Real.exp (|w.im| * U) ≤ Real.exp (U / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hv1 : ‖paperFT f z‖ ≤ 2 * δ * U * Real.exp (U / 2) * ∫ u, ‖f u‖ := by
    have h := norm_paperFT_sub_le_of_support hf hfs hzwU
    rw [h0, sub_zero] at h
    refine h.trans ?_
    gcongr
  have hv2 : ‖paperFT f ((starRingEnd ℂ) z)‖ ≤ Real.exp (U / 2) * ∫ u, ‖f u‖ := by
    refine (norm_paperFT_le_of_support hf hfs _).trans ?_
    have hexp' : Real.exp (|((starRingEnd ℂ) z).im| * U) ≤ Real.exp (U / 2) := by
      rw [Complex.conj_im, abs_neg]; exact Real.exp_le_exp.mpr (by nlinarith)
    gcongr
  calc ‖paperFT f z‖ * ‖paperFT f ((starRingEnd ℂ) z)‖
      ≤ (2 * δ * U * Real.exp (U / 2) * ∫ u, ‖f u‖) * (Real.exp (U / 2) * ∫ u, ‖f u‖) :=
        mul_le_mul hv1 hv2 (norm_nonneg _) (by positivity)
    _ = 2 * δ * U * (Real.exp (U / 2) * Real.exp (U / 2)) * (∫ u, ‖f u‖) ^ 2 := by ring
    _ = 2 * δ * U * Real.exp U * (∫ u, ‖f u‖) ^ 2 := by rw [← Real.exp_add, add_halves]

/-- `γ_ρ − γ_s = (ρ − s)/i` has the norm of `ρ − s`. -/
theorem norm_gammaOf_sub (ρ s : ℂ) : ‖gammaOf ρ - gammaOf s‖ = ‖ρ - s‖ := by
  have e : gammaOf ρ - gammaOf s = (ρ - s) / I := by unfold gammaOf; ring
  rw [e, norm_div, Complex.norm_I, div_one]

/-! ### The plateau and the plateau tests -/

/-- The box plateau has norm at most `1`: it is a probability average of `boxPower`, whose norm
is at most `1`. -/
theorem norm_boxPlateau_le_one {A h r : ℝ} (hh : 0 < h) (hr : 0 < r) (n : ℕ) (x : ℝ) :
    ‖boxPlateau A h n r x‖ ≤ 1 := by
  rw [boxPlateau_apply]
  have hint : Integrable fun t => (radiusBump hr).normed volume (x - t) :=
    (radiusBump hr).integrable_normed.comp_sub_left x
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_mul, norm_smoothUnitBump hr]
    calc ‖boxPower A h n t‖ * (radiusBump hr).normed volume (x - t)
        ≤ 1 * (radiusBump hr).normed volume (x - t) :=
          mul_le_mul_of_nonneg_right (norm_boxPower_le hh n t) ((radiusBump hr).nonneg_normed _)
      _ = _ := one_mul _
  · rw [integral_sub_left_eq_self (fun t => (radiusBump hr).normed volume t) volume x,
      (radiusBump hr).integral_normed]

/-- `∫‖b‖ ≤ 2U` for `b` of norm at most `1` vanishing off `[−U, U]`. -/
theorem integral_norm_le_of_support {b : ℝ → ℂ} {U : ℝ} (hU : 0 ≤ U) (hb : Integrable b)
    (hb1 : ∀ u, ‖b u‖ ≤ 1) (hbs : ∀ u, U < |u| → b u = 0) :
    ∫ u, ‖b u‖ ≤ 2 * U := by
  have hind : Integrable ((Icc (-U) U).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))
  calc ∫ u, ‖b u‖ ≤ ∫ u, (Icc (-U) U).indicator (fun _ => (1 : ℝ)) u := by
        refine integral_mono hb.norm hind fun u => ?_
        by_cases hu : u ∈ Icc (-U) U
        · rw [indicator_of_mem hu]; exact hb1 u
        · rw [indicator_of_notMem hu]
          have hUu : U < |u| := by
            rw [mem_Icc, not_and_or, not_le, not_le] at hu
            rcases hu with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          rw [hbs u hUu, norm_zero]
    _ = 2 * U := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
          Real.volume_real_Icc_of_le (by linarith)]
        ring

/-- `‖p_c(u)‖ ≤ Σ|c_j|` for the band trigonometric polynomial. -/
theorem norm_bandTrigPoly_le (ℓ : ℝ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) (u : ℝ) :
    ‖bandTrigPoly ℓ k₀ c u‖ ≤ ∑ j, ‖c j‖ := by
  unfold bandTrigPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_exp]
  have : (I * (trigFreq ℓ k₀ j : ℂ) * (u : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one]

/-- The plateau test `f_c = b · p_c` is integrable when `b` is. -/
theorem integrable_trigTest {b : ℝ → ℂ} (hb : Integrable b) (ℓ : ℝ) (k₀ : ℕ)
    (c : Fin (2 * k₀ + 1) → ℂ) : Integrable (trigTest b ℓ k₀ c) :=
  hb.mul_bdd (continuous_bandTrigPoly ℓ k₀ c).aestronglyMeasurable
    (Eventually.of_forall (norm_bandTrigPoly_le ℓ k₀ c))

/-- `∫‖f_c‖ ≤ (Σ|c_j|) ∫‖b‖` for the plateau test `f_c = b · p_c`. -/
theorem integral_norm_trigTest_le {b : ℝ → ℂ} (hb : Integrable b) (ℓ : ℝ) (k₀ : ℕ)
    (c : Fin (2 * k₀ + 1) → ℂ) :
    ∫ u, ‖trigTest b ℓ k₀ c u‖ ≤ (∑ j, ‖c j‖) * ∫ u, ‖b u‖ := by
  calc ∫ u, ‖trigTest b ℓ k₀ c u‖ ≤ ∫ u, ‖b u‖ * ∑ j, ‖c j‖ := by
        refine integral_mono (integrable_trigTest hb ℓ k₀ c).norm (hb.norm.mul_const _)
          fun u => ?_
        simp only [trigTest, norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_bandTrigPoly_le ℓ k₀ c u) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * ∫ u, ‖b u‖ := by rw [integral_mul_const, mul_comm]

/-- Far-field product bound for a plateau test: for `|Re x| > T` in the strip,
`‖f̂_c(x)‖ ‖f̂_c(x̄)‖ ≤ ((Σ|c_j|) B)² / (1 + |Re x| − T)³`. -/
theorem norm_paperFT_trigTest_mul_le_of_far {b : ℝ → ℂ} {U ℓ T Δ B : ℝ} (hb : Integrable b)
    (hbs : ∀ u, U < |u| → b u = 0) (hℓ : 0 < ℓ) {k₀ : ℕ} (hΩ : k₀ * π / ℓ + Δ ≤ T)
    (hΔ : 1 ≤ Δ) (hB : 0 ≤ B)
    (hdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| → ‖paperFT b w‖ ≤ B / w.re ^ 2)
    (c : Fin (2 * k₀ + 1) → ℂ) {x : ℂ} (hx : |x.im| ≤ 1 / 2) (hT : T < |x.re|) :
    ‖paperFT (trigTest b ℓ k₀ c) x‖ * ‖paperFT (trigTest b ℓ k₀ c) ((starRingEnd ℂ) x)‖ ≤
      ((∑ j, ‖c j‖) * B) ^ 2 / (1 + (|x.re| - T)) ^ 3 := by
  have hx' : |((starRingEnd ℂ) x).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hx
  have hT' : T < |((starRingEnd ℂ) x).re| := by rw [Complex.conj_re]; exact hT
  have hv1 := norm_paperFT_trigTest_far_le hb hbs hℓ hΩ hΔ hB hdec c hx hT
  have hv2 := norm_paperFT_trigTest_far_le hb hbs hℓ hΩ hΔ hB hdec c hx' hT'
  rw [Complex.conj_re] at hv2
  set D := 1 + (|x.re| - T) with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hK0 : 0 ≤ ((∑ j, ‖c j‖) * B) ^ 2 := by positivity
  calc ‖paperFT (trigTest b ℓ k₀ c) x‖ * ‖paperFT (trigTest b ℓ k₀ c) ((starRingEnd ℂ) x)‖
      ≤ ((∑ j, ‖c j‖) * B / D ^ 2) * ((∑ j, ‖c j‖) * B / D ^ 2) :=
        mul_le_mul hv1 hv2 (norm_nonneg _) (by positivity)
    _ = ((∑ j, ‖c j‖) * B) ^ 2 / D ^ 4 := by rw [div_mul_div_comm]; congr 1 <;> ring
    _ ≤ ((∑ j, ‖c j‖) * B) ^ 2 / D ^ 3 := by
        apply div_le_div_of_nonneg_left hK0 (by positivity)
        calc D ^ 3 = D ^ 3 * 1 := by ring
          _ ≤ D ^ 3 * D := by gcongr
          _ = D ^ 4 := by ring

/-! ### Two weight comparisons for the unit-window zero sums -/

/-- For `|x| ≤ T`, the weight `(1 + |x − T|)^{-3}` is at least `(1 + 2T)^{-3}`. -/
theorem one_div_pow_three_le_of_abs_le {x T : ℝ} (hx : |x| ≤ T) :
    1 / (1 + 2 * T) ^ 3 ≤ 1 / (1 + |x - T|) ^ 3 := by
  have hT : 0 ≤ T := le_trans (abs_nonneg x) hx
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have := abs_le.mp hx
  have : |x - T| ≤ 2 * T := by rw [abs_le]; constructor <;> linarith
  linarith

/-- For `|x| > T ≥ 0`, `(1 + (|x| − T))^{-3} ≤ (1 + |x − T|)^{-3} + (1 + |x + T|)^{-3}`. -/
theorem one_div_pow_three_le_add {x T : ℝ} (hT : 0 ≤ T) (hx : T < |x|) :
    1 / (1 + (|x| - T)) ^ 3 ≤ 1 / (1 + |x - T|) ^ 3 + 1 / (1 + |x - -T|) ^ 3 := by
  rcases lt_or_gt_of_ne (show x ≠ 0 by intro h; rw [h, abs_zero] at hx; linarith) with hneg | hpos
  · have e : 1 + (|x| - T) = 1 + |x - -T| := by
      rw [abs_of_neg hneg, sub_neg_eq_add, abs_of_nonpos (by rw [abs_of_neg hneg] at hx; linarith)]
      ring
    rw [e]
    have : 0 ≤ 1 / (1 + |x - T|) ^ 3 := by positivity
    linarith
  · have e : 1 + (|x| - T) = 1 + |x - T| := by
      rw [abs_of_pos hpos, abs_of_nonneg (by rw [abs_of_pos hpos] at hx; linarith)]
    rw [e]
    have : 0 ≤ 1 / (1 + |x - -T|) ^ 3 := by positivity
    linarith

/-! ### Weil energy of a plateau test constrained on a net of the low zeros -/

/-- **Weil energy of a plateau test constrained on a `δ`-net of the low zeros.** If `f̂_c`
vanishes at `γ_s` for every `s ∈ S ⊆ 𝒵` and every zero of height `≤ T` lies within `δ` of `S`
(`0 ≤ δ`, `δ U ≤ 1`, `b` vanishing off `[−U, U]`), then
`‖W(f_c, f_c)‖ ≤ ((Σ|c_j|)² B² + (1 + 2T)³ · 2δU e^{U} (∫‖b‖)² (Σ|c_j|)²) · 48 A₀ log(T + 3)`.
The first term is the contribution of the zeros above `T` (far-field decay of `f̂_c`), the second
that of the unconstrained zeros below `T` (strip Lipschitz bound). -/
theorem norm_W_trigTest_le_of_net {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {b : ℝ → ℂ} {U ℓ T Δ B δ : ℝ} (hU : 0 ≤ U) (hb : Integrable b)
    (hbs : ∀ u, U < |u| → b u = 0) (hℓ : 0 < ℓ)
    {k₀ : ℕ} (hΩ : k₀ * π / ℓ + Δ ≤ T) (hΔ : 1 ≤ Δ) (hB : 0 ≤ B)
    (hdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| → ‖paperFT b w‖ ≤ B / w.re ^ 2)
    (c : Fin (2 * k₀ + 1) → ℂ) {S : Set ℂ} (hS : S ⊆ zetaZeroConfig.carrier)
    (hδ : 0 ≤ δ) (hδU : δ * U ≤ 1)
    (hnet : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T → ∃ s ∈ S, ‖ρ - s‖ ≤ δ)
    (hc : ∀ s ∈ S, paperFT (trigTest b ℓ k₀ c) (gammaOf s) = 0) :
    ‖zetaZeroConfig.W (trigTest b ℓ k₀ c) (trigTest b ℓ k₀ c)‖ ≤
      (((∑ j, ‖c j‖) * B) ^ 2 +
        (1 + 2 * T) ^ 3 * (2 * δ * U * Real.exp U * (∫ u, ‖b u‖) ^ 2 * (∑ j, ‖c j‖) ^ 2)) *
        (48 * A₀ * Real.log (T + 3)) := by
  have hT0 : 0 ≤ T := by
    have : 0 ≤ (k₀ : ℝ) * π / ℓ := by positivity
    linarith
  set f := trigTest b ℓ k₀ c with hf
  have hfint : Integrable f := integrable_trigTest hb ℓ k₀ c
  have hfs : ∀ u, U < |u| → f u = 0 := fun u hu => by simp [hf, trigTest, hbs u hu]
  have hfI : ∫ u, ‖f u‖ ≤ (∑ j, ‖c j‖) * ∫ u, ‖b u‖ := integral_norm_trigTest_le hb ℓ k₀ c
  have hfI0 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
  set K := ((∑ j, ‖c j‖) * B) ^ 2 with hK
  set K' := (1 + 2 * T) ^ 3 * (2 * δ * U * Real.exp U * (∫ u, ‖b u‖) ^ 2 * (∑ j, ‖c j‖) ^ 2)
    with hK'
  have hK0 : 0 ≤ K := by positivity
  have hK'0 : 0 ≤ K' := by positivity
  -- the product bound at an unconstrained low zero, in the weight `(1 + 2T)^{-3}`
  have hlowprod : 2 * δ * U * Real.exp U * (∫ u, ‖f u‖) ^ 2 ≤ K' * (1 / (1 + 2 * T) ^ 3) := by
    have e : K' * (1 / (1 + 2 * T) ^ 3) =
        2 * δ * U * Real.exp U * (∫ u, ‖b u‖) ^ 2 * (∑ j, ‖c j‖) ^ 2 := by
      rw [hK', mul_comm, ← mul_assoc, one_div_mul_cancel (by positivity), one_mul]
    rw [e]
    have hsq : (∫ u, ‖f u‖) ^ 2 ≤ ((∑ j, ‖c j‖) * ∫ u, ‖b u‖) ^ 2 :=
      pow_le_pow_left₀ hfI0 hfI 2
    calc 2 * δ * U * Real.exp U * (∫ u, ‖f u‖) ^ 2
        ≤ 2 * δ * U * Real.exp U * ((∑ j, ‖c j‖) * ∫ u, ‖b u‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * δ * U * Real.exp U * (∫ u, ‖b u‖) ^ 2 * (∑ j, ‖c j‖) ^ 2 := by ring
  obtain ⟨hs₁, hle₁⟩ := window_tsum_le zetaZeroConfig hA₀ hloc T
  obtain ⟨hs₂, hle₂⟩ := window_tsum_le zetaZeroConfig hA₀ hloc (-T)
  set g : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (K + K') * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - T|) ^ 3 +
      (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - -T|) ^ 3) with hg
  have hgs : Summable g := (hs₁.add hs₂).mul_left (K + K')
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand f f ρ‖ ≤ g ρ := by
    intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hre1 : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
    have hw0 : 0 ≤ 1 / (1 + |(ρ : ℂ).im - T|) ^ 3 := by positivity
    have hw0' : 0 ≤ 1 / (1 + |(ρ : ℂ).im - -T|) ^ 3 := by positivity
    have hgρ : g ρ = (zetaZeroConfig.mult ρ : ℝ) *
        ((K + K') * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3 + 1 / (1 + |(ρ : ℂ).im - -T|) ^ 3)) := by
      simp only [hg]; ring
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj, mul_assoc, hgρ]
    apply mul_le_mul_of_nonneg_left _ hm
    by_cases hlow : |(ρ : ℂ).im| ≤ T
    · -- an unconstrained low zero: within `δ` of a constrained one
      obtain ⟨s, hsS, hρs⟩ := hnet ρ hmem hlow
      have hsstrip : 0 < s.re ∧ s.re < 1 := by
        have h : IsNontrivialZero s := hS hsS
        exact ⟨h.2.1, h.2.2⟩
      have hsIm : |(gammaOf s).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hsstrip).le
      have hρs' : ‖gammaOf (ρ : ℂ) - gammaOf s‖ ≤ δ := by rw [norm_gammaOf_sub]; exact hρs
      have hprod := norm_paperFT_mul_le_of_near_zero hU hfint hfs hIm hsIm hρs' hδU (hc s hsS)
      have h1 := one_div_pow_three_le_of_abs_le hlow
      calc ‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
          ≤ K' * (1 / (1 + 2 * T) ^ 3) := hprod.trans hlowprod
        _ ≤ K' * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3) := mul_le_mul_of_nonneg_left h1 hK'0
        _ ≤ (K + K') * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3 + 1 / (1 + |(ρ : ℂ).im - -T|) ^ 3) := by
            nlinarith [mul_nonneg hK0 hw0, mul_nonneg hK0 hw0', mul_nonneg hK'0 hw0']
    · -- a zero above `T`: far-field decay
      push Not at hlow
      have hprod := norm_paperFT_trigTest_mul_le_of_far hb hbs hℓ hΩ hΔ hB hdec c hIm
        (by rw [hre1]; exact hlow)
      rw [hre1] at hprod
      have hsplit := one_div_pow_three_le_add hT0 hlow
      calc ‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
          ≤ K / (1 + (|(ρ : ℂ).im| - T)) ^ 3 := hprod
        _ = K * (1 / (1 + (|(ρ : ℂ).im| - T)) ^ 3) := by ring
        _ ≤ K * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3 + 1 / (1 + |(ρ : ℂ).im - -T|) ^ 3) :=
            mul_le_mul_of_nonneg_left hsplit hK0
        _ ≤ (K + K') * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3 + 1 / (1 + |(ρ : ℂ).im - -T|) ^ 3) := by
            nlinarith [mul_nonneg hK'0 hw0, mul_nonneg hK'0 hw0']
  have hsum' : Summable fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f f ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hgs
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ((Summable.tsum_le_tsum hpt hsum' hgs).trans ?_)
  rw [hg, tsum_mul_left, Summable.tsum_add hs₁ hs₂]
  rw [abs_neg, abs_of_nonneg hT0] at hle₂
  rw [abs_of_nonneg hT0] at hle₁
  calc (K + K') * (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) /
        (1 + |(ρ : ℂ).im - T|) ^ 3 + ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - -T|) ^ 3)
      ≤ (K + K') * (24 * A₀ * Real.log (T + 3) + 24 * A₀ * Real.log (T + 3)) :=
        mul_le_mul_of_nonneg_left (add_le_add hle₁ hle₂) (by linarith)
    _ = (K + K') * (48 * A₀ * Real.log (T + 3)) := by ring

/-! ### Arithmetic of the level parameters and of the net margin -/

/-- Polynomials of any degree lose against `e^{2L}`. -/
theorem eventually_mul_pow_le_exp {K : ℝ} (hK : 0 < K) (c : ℝ) (n : ℕ) :
    ∀ᶠ L : ℝ in atTop, c * (1 + L) ^ n ≤ K * Real.exp (2 * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp (2 * L) / (2 * L) ^ n) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop n).comp (tendsto_id.const_mul_atTop two_pos)
  filter_upwards [ht.eventually_ge_atTop (|c| / K), eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have hpos : 0 < (2 * L) ^ n := by positivity
  rw [div_le_div_iff₀ hK hpos] at hL
  have h1 : (1 + L) ^ n ≤ (2 * L) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  have h2 : c * (1 + L) ^ n ≤ |c| * (2 * L) ^ n :=
    (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg c))
  linarith

/-- Size bounds of the level parameters `ℓ = L − η/8`, `T = 2πe^{2ℓ}`, `k ≤ (T − Δ)ℓ/π`. -/
theorem level_bounds {η L ℓ T Δ k : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hL : 1 ≤ L)
    (hℓ : ℓ = L - η / 8) (hT : T = 2 * π * Real.exp (2 * ℓ))
    (hΔ : Δ = π * η * Real.exp (2 * L) / (8 * L)) (hk : k ≤ (T - Δ) * ℓ / π) :
    7 / 8 ≤ ℓ ∧ 0 ≤ T ∧ T ≤ 2 * π * Real.exp (2 * L) ∧
      2 * k + 1 ≤ 5 * L * Real.exp (2 * L) ∧
      0 ≤ Real.log (T + 3) ∧ Real.log (T + 3) ≤ 3 + 2 * L := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hE := Real.exp_pos (2 * L)
  have hE1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hℓ7 : 7 / 8 ≤ ℓ := by rw [hℓ]; linarith
  have hℓL : ℓ ≤ L := by rw [hℓ]; linarith
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; positivity
  have hTle : T ≤ 2 * π * Real.exp (2 * L) := by rw [hT]; gcongr
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hk2 : 2 * k + 1 ≤ 5 * L * Real.exp (2 * L) := by
    have h1 : k ≤ T * ℓ / π := by
      refine hk.trans ?_
      apply div_le_div_of_nonneg_right _ hpi.le
      nlinarith
    have h2 : T * ℓ / π ≤ 2 * L * Real.exp (2 * L) := by
      rw [div_le_iff₀ hpi]
      have : T * ℓ ≤ (2 * π * Real.exp (2 * L)) * L :=
        mul_le_mul hTle hℓL (by linarith) (by positivity)
      nlinarith
    nlinarith
  have hlog : Real.log (T + 3) ≤ 3 + 2 * L := by
    have h1 : T + 3 ≤ 10 * Real.exp (2 * L) := by nlinarith
    have h2 : Real.log (T + 3) ≤ Real.log (10 * Real.exp (2 * L)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) hE.ne', Real.log_exp] at h2
    have h3 : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h4 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  exact ⟨hℓ7, hT0, hTle, hk2, hlog0, hlog⟩

/-- The polynomial factor of the net term: `Q(L) = 5268480 · A₀ · L⁴ · (3 + 2L)`. -/
def netPoly (A₀ L : ℝ) : ℝ := 5268480 * A₀ * L ^ 4 * (3 + 2 * L)

/-- **Net-term arithmetic.** With `2k + 1 ≤ 5Le^{2L}`, `T ≤ 2πe^{2L}`, `log(T + 3) ≤ 3 + 2L`,
`ℓ ≥ 7/8` and `0 ≤ I_b ≤ 2L`:
`(2k+1) · (1 + 2T)³ · 2δL e^{L} I_b² · 48 A₀ log(T + 3) / (2ℓ) ≤ δ · Q(L) · e^{9L}`. -/
theorem net_margin_arith {L ℓ T A₀ k Ib δ : ℝ} (hL : 1 ≤ L) (hℓ : 7 / 8 ≤ ℓ)
    (hk2 : 2 * k + 1 ≤ 5 * L * Real.exp (2 * L)) (hk0 : 0 ≤ 2 * k + 1) (hT0 : 0 ≤ T)
    (hTle : T ≤ 2 * π * Real.exp (2 * L)) (hlog0 : 0 ≤ Real.log (T + 3))
    (hlog : Real.log (T + 3) ≤ 3 + 2 * L) (hA₀ : 1 ≤ A₀) (hIb0 : 0 ≤ Ib) (hIb : Ib ≤ 2 * L)
    (hδ : 0 ≤ δ) :
    (2 * k + 1) * ((1 + 2 * T) ^ 3 * (2 * δ * L * Real.exp L * Ib ^ 2)) *
        (48 * A₀ * Real.log (T + 3)) / (2 * ℓ) ≤
      δ * (netPoly A₀ L * Real.exp (9 * L)) := by
  have hE := Real.exp_pos (2 * L)
  have hE1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hA0 : 0 ≤ A₀ := by linarith
  have hpi := Real.pi_lt_d2
  have h1 : 1 + 2 * T ≤ 14 * Real.exp (2 * L) := by nlinarith
  have hQ : (1 + 2 * T) ^ 3 ≤ 2744 * Real.exp (2 * L) ^ 3 := by
    calc (1 + 2 * T) ^ 3 ≤ (14 * Real.exp (2 * L)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h1 3
      _ = 2744 * Real.exp (2 * L) ^ 3 := by ring
  have hR : 2 * δ * L * Real.exp L * Ib ^ 2 ≤ 2 * δ * L * Real.exp L * (4 * L ^ 2) := by
    have : Ib ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hIb0 hIb 2
    have h0 : 0 ≤ 2 * δ * L * Real.exp L := by positivity
    nlinarith
  have hS : 48 * A₀ * Real.log (T + 3) ≤ 48 * A₀ * (3 + 2 * L) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hnum : (2 * k + 1) * ((1 + 2 * T) ^ 3 * (2 * δ * L * Real.exp L * Ib ^ 2)) *
      (48 * A₀ * Real.log (T + 3)) ≤
      (5 * L * Real.exp (2 * L)) * ((2744 * Real.exp (2 * L) ^ 3) *
        (2 * δ * L * Real.exp L * (4 * L ^ 2))) * (48 * A₀ * (3 + 2 * L)) := by
    have hR0 : 0 ≤ 2 * δ * L * Real.exp L * Ib ^ 2 := by positivity
    have hS0 : 0 ≤ 48 * A₀ * Real.log (T + 3) := by positivity
    have hQR : (1 + 2 * T) ^ 3 * (2 * δ * L * Real.exp L * Ib ^ 2) ≤
        (2744 * Real.exp (2 * L) ^ 3) * (2 * δ * L * Real.exp L * (4 * L ^ 2)) :=
      mul_le_mul hQ hR hR0 (by positivity)
    have hPQR : (2 * k + 1) * ((1 + 2 * T) ^ 3 * (2 * δ * L * Real.exp L * Ib ^ 2)) ≤
        (5 * L * Real.exp (2 * L)) * ((2744 * Real.exp (2 * L) ^ 3) *
          (2 * δ * L * Real.exp L * (4 * L ^ 2))) :=
      mul_le_mul hk2 hQR (by positivity) (by positivity)
    exact mul_le_mul hPQR hS hS0 (by positivity)
  have hden : (2 * k + 1) * ((1 + 2 * T) ^ 3 * (2 * δ * L * Real.exp L * Ib ^ 2)) *
      (48 * A₀ * Real.log (T + 3)) / (2 * ℓ) ≤
      (2 * k + 1) * ((1 + 2 * T) ^ 3 * (2 * δ * L * Real.exp L * Ib ^ 2)) *
        (48 * A₀ * Real.log (T + 3)) :=
    div_le_self (by positivity) (by linarith)
  have hexp : Real.exp (2 * L) * Real.exp (2 * L) ^ 3 * Real.exp L = Real.exp (9 * L) := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hfinal : (5 * L * Real.exp (2 * L)) * ((2744 * Real.exp (2 * L) ^ 3) *
      (2 * δ * L * Real.exp L * (4 * L ^ 2))) * (48 * A₀ * (3 + 2 * L)) =
      δ * (netPoly A₀ L * Real.exp (9 * L)) := by
    rw [← hexp, netPoly]; ring
  linarith

/-- **Energy assembly.** From the two-term energy bound, Cauchy–Schwarz on the coefficients, the
bulk lower bound and the two margin inequalities, `W ≤ (ε₁ + ε₂) I₂`. -/
theorem energy_assembly {W Σc B Q R Sg k ℓ I₂ ε₁ ε₂ : ℝ}
    (hW : W ≤ ((Σc * B) ^ 2 + Q * (R * Σc ^ 2)) * Sg)
    (hS : Σc ^ 2 ≤ (2 * k + 1) * (I₂ / (2 * ℓ))) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hSg : 0 ≤ Sg) (hI : 0 ≤ I₂)
    (hmarg : (2 * k + 1) * B ^ 2 * Sg / (2 * ℓ) ≤ ε₁)
    (hnet : (2 * k + 1) * (Q * R) * Sg / (2 * ℓ) ≤ ε₂) :
    W ≤ (ε₁ + ε₂) * I₂ := by
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have h1 : (Σc * B) ^ 2 * Sg ≤ ε₁ * I₂ := by
    calc (Σc * B) ^ 2 * Sg = Σc ^ 2 * (B ^ 2 * Sg) := by ring
      _ ≤ ((2 * k + 1) * (I₂ / (2 * ℓ))) * (B ^ 2 * Sg) :=
          mul_le_mul_of_nonneg_right hS (mul_nonneg hB2 hSg)
      _ = ((2 * k + 1) * B ^ 2 * Sg / (2 * ℓ)) * I₂ := by ring
      _ ≤ ε₁ * I₂ := mul_le_mul_of_nonneg_right hmarg hI
  have h2 : Q * (R * Σc ^ 2) * Sg ≤ ε₂ * I₂ := by
    calc Q * (R * Σc ^ 2) * Sg = Σc ^ 2 * (Q * R * Sg) := by ring
      _ ≤ ((2 * k + 1) * (I₂ / (2 * ℓ))) * (Q * R * Sg) :=
          mul_le_mul_of_nonneg_right hS (mul_nonneg (mul_nonneg hQ hR) hSg)
      _ = ((2 * k + 1) * (Q * R) * Sg / (2 * ℓ)) * I₂ := by ring
      _ ≤ ε₂ * I₂ := mul_le_mul_of_nonneg_right hnet hI
  calc W ≤ ((Σc * B) ^ 2 + Q * (R * Σc ^ 2)) * Sg := hW
    _ = (Σc * B) ^ 2 * Sg + Q * (R * Σc ^ 2) * Sg := by ring
    _ ≤ ε₁ * I₂ + ε₂ * I₂ := add_le_add h1 h2
    _ = (ε₁ + ε₂) * I₂ := by ring

/-! ### The near radical at a fixed level, constrained on a net -/

/-- The constraint map: the values of `f̂_c` on the finite set `S` and at `±i/2`. -/
def netConstraint (b : ℝ → ℂ) (ℓ : ℝ) (k₀ : ℕ) (S : Finset ℂ) :
    (Fin (2 * k₀ + 1) → ℂ) →ₗ[ℂ] ((S → ℂ) × (ℂ × ℂ)) where
  toFun c := (fun s => ∑ j, c j * paperFT b (gammaOf (s : ℂ) + trigFreq ℓ k₀ j),
    ∑ j, c j * paperFT b (I / 2 + trigFreq ℓ k₀ j),
    ∑ j, c j * paperFT b (-(I / 2) + trigFreq ℓ k₀ j))
  map_add' c d := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Prod.mk_add_mk]; rfl
  map_smul' a c := by
    ext ρ <;> simp [Finset.mul_sum, mul_assoc]

/-- The kernel of the net constraint map has dimension at least `2k₀ + 1 − (#S + 2)`. -/
theorem finrank_ker_netConstraint_ge (b : ℝ → ℂ) (ℓ : ℝ) (k₀ : ℕ) (S : Finset ℂ) :
    ((2 * k₀ + 1 : ℕ) : ℝ) - ((S.card + 2 : ℕ) : ℝ) ≤
      (Module.finrank ℂ (LinearMap.ker (netConstraint b ℓ k₀ S)) : ℝ) := by
  set Λ := netConstraint b ℓ k₀ S
  have hrn := LinearMap.finrank_range_add_finrank_ker Λ
  have hcod : Module.finrank ℂ ((S → ℂ) × (ℂ × ℂ)) = S.card + 2 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_self, Fintype.card_coe]
  have hrange : Module.finrank ℂ (LinearMap.range Λ) ≤ S.card + 2 := by
    rw [← hcod]; exact Submodule.finrank_le _
  have hdim : Module.finrank ℂ (Fin (2 * k₀ + 1) → ℂ) = 2 * k₀ + 1 := by simp
  rw [hdim] at hrn
  have : 2 * k₀ + 1 ≤ S.card + 2 + Module.finrank ℂ (LinearMap.ker Λ) := by omega
  have h' : ((2 * k₀ + 1 : ℕ) : ℝ) ≤ ((S.card + 2 : ℕ) : ℝ) +
      (Module.finrank ℂ (LinearMap.ker Λ) : ℝ) := by exact_mod_cast this
  linarith

/-- **The near radical at a fixed level, constrained on a net.** Under the size conditions
`(C1)–(C5)` of `RHTower.sharpCount_at_level`, for every finite set `S` of zeros such that every zero
of height `≤ T = 2πe^{2(L − η/8)}` lies within `δ` of `S` (`0 ≤ δ`, `δL ≤ 1`), the Hodge-class
tests at level `L` contain a subspace `V` with
`dim V ≥ (2 − η)e^{2L} + (2N(0,T) + c₀ − #S)` and
`‖W(f,f)‖ ≤ (exp(−η²e^{2L}/(300L)) + δ · Q(L) e^{9L}) ∫|f|²` on `V`. -/
theorem nearRadical_at_level_of_net {η L A₀ CR T₁ δ : ℝ} {c₀ : ℕ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hL : 1 ≤ L) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hCR : 0 ≤ CR) (hcount : ∀ T : ℝ, T₁ ≤ T →
      (zetaZeroConfig.N 0 T : ℝ) ≤ zeroCountMain T + CR * Real.log T ^ 2)
    (hC1 : 3 + c₀ + 2 * CR * (2 + 2 * L) ^ 2 ≤ η / 4 * Real.exp (2 * L))
    (hC2 : Real.log (960 * A₀ * L * (3 + 2 * L)) + 7 * L + 2 ≤
      η ^ 2 * Real.exp (2 * L) / (1000 * L))
    (hC3 : 1 ≤ π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L))
    (hC4 : 1 ≤ π * η * Real.exp (2 * L) / (8 * L))
    (hC5 : T₁ ≤ 2 * π * Real.exp (2 * (L - η / 8)))
    (hδ : 0 ≤ δ) (hδL : δ * L ≤ 1)
    (S : Finset ℂ) (hS : ∀ s ∈ S, s ∈ zetaZeroConfig.carrier)
    (hnet : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ 2 * π * Real.exp (2 * (L - η / 8)) →
      ∃ s ∈ S, ‖ρ - s‖ ≤ δ) :
    ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
      (2 - η) * Real.exp (2 * L) +
        (2 * (zetaZeroConfig.N 0 (2 * π * Real.exp (2 * (L - η / 8))) : ℝ) + c₀ - S.card) ≤
          (Module.finrank ℂ V : ℝ) ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤
        (Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) +
          δ * (netPoly A₀ L * Real.exp (9 * L))) * ∫ u, ‖f u‖ ^ 2 := by
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = L - η / 8 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * π * Real.exp (2 * ℓ) := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = π * η * Real.exp (2 * L) / (8 * L) := ⟨_, rfl⟩
  have hTdef : 2 * π * Real.exp (2 * (L - η / 8)) = T := by rw [hT, hℓ]
  rw [hTdef] at hnet ⊢
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  have hΔ1 : 1 ≤ Δ := by rw [hΔ]; exact hC4
  have hΔ0 : 0 < Δ := by linarith
  -- the number of box smoothings
  have hNeq : η / 8 * Δ / (8 * Real.exp 1) =
      π * η ^ 2 * Real.exp (2 * L) / (512 * Real.exp 1 * L) := by
    rw [hΔ]; field_simp; ring
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊η / 8 * Δ / (8 * Real.exp 1)⌋₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact Nat.le_floor (by rw [hNeq]; exact_mod_cast hC3)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ η / 8 * Δ / (8 * Real.exp 1) := by
    rw [hNdef]; exact Nat.floor_le (by positivity)
  have hNgt : η / 8 * Δ / (8 * Real.exp 1) - 1 < N := by
    have := Nat.lt_floor_add_one (η / 8 * Δ / (8 * Real.exp 1)); rw [← hNdef] at this; linarith
  -- the plateau
  obtain ⟨hbC, hb1, hb0, hbint, hdec⟩ := levelPlateau_spec hη0 hη1 hL hΔ0 hN1 hNle
  set b := boxPlateau (L - η / 8 + η / 8 / 2) (η / 8 / (4 * N)) N (η / 8 / 4) with hbdef
  rw [← hℓ] at hb1
  have hbs : ∀ u, L < |u| → b u = 0 := fun u hu => hb0 u hu.le
  have hbnorm : ∀ u, ‖b u‖ ≤ 1 := fun u =>
    norm_boxPlateau_le_one (div_pos (by positivity) (by positivity)) (by positivity) N u
  have hbI : ∫ u, ‖b u‖ ≤ 2 * L :=
    integral_norm_le_of_support (by linarith) hbint hbnorm hbs
  have hbI0 : 0 ≤ ∫ u, ‖b u‖ := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = 2 * Real.exp ((L - η / 8 + η / 8 / 2 + η / 8 / 4) / 2) * Real.exp (-N) * Δ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hdec' : ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| → ‖paperFT b w‖ ≤ B / w.re ^ 2 :=
    fun w h1 h2 => by rw [hBdef]; exact hdec w h1 h2
  -- the frequencies
  have hE := Real.exp_pos (2 * L)
  have hexpℓ : Real.exp (2 * L) / 2 ≤ Real.exp (2 * ℓ) := by
    have := Real.add_one_le_exp (-(η / 4))
    rw [hℓ, show 2 * (L - η / 8) = 2 * L + (-(η / 4)) by ring, Real.exp_add]
    nlinarith
  have hTΔ : Δ ≤ T := by
    have h2 : Δ ≤ π * Real.exp (2 * L) / 8 := by
      rw [hΔ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : π * η * Real.exp (2 * L) ≤ π * Real.exp (2 * L) * L := by
        have := mul_le_mul_of_nonneg_left (show η ≤ L by linarith)
          (by positivity : (0 : ℝ) ≤ π * Real.exp (2 * L))
        linarith
      linarith
    have h3 : π * Real.exp (2 * L) ≤ T := by
      rw [hT]
      have := mul_le_mul_of_nonneg_left hexpℓ (by positivity : (0 : ℝ) ≤ 2 * π)
      linarith
    have : 0 ≤ π * Real.exp (2 * L) := by positivity
    linarith
  obtain ⟨k₀, hk₀def⟩ : ∃ k₀ : ℕ, k₀ = ⌊(T - Δ) * ℓ / π⌋₊ := ⟨_, rfl⟩
  have hk₀le : (k₀ : ℝ) ≤ (T - Δ) * ℓ / π := by
    have hTΔ' : 0 ≤ T - Δ := by linarith
    rw [hk₀def]; exact Nat.floor_le (by positivity)
  have hk₀gt : (T - Δ) * ℓ / π - 1 < k₀ := by
    have := Nat.lt_floor_add_one ((T - Δ) * ℓ / π); rw [← hk₀def] at this; linarith
  have hΩ : k₀ * π / ℓ + Δ ≤ T := by
    have : (k₀ : ℝ) * π / ℓ ≤ T - Δ := by
      rw [div_le_iff₀ hℓpos]
      rw [le_div_iff₀ hpi] at hk₀le; linarith
    linarith
  -- the constraint map and the subspace
  set Λ := netConstraint b ℓ k₀ S with hΛdef
  have hΛ : ∀ c, Λ c = (fun s : S => paperFT (trigTest b ℓ k₀ c) (gammaOf (s : ℂ)),
      paperFT (trigTest b ℓ k₀ c) (I / 2), paperFT (trigTest b ℓ k₀ c) (-(I / 2))) := by
    intro c
    simp only [hΛdef, netConstraint, LinearMap.coe_mk, AddHom.coe_mk,
      paperFT_trigTest hbint hbs]
  set Φ := trigTestMap b ℓ k₀ with hΦdef
  have hΦinj : Function.Injective Φ :=
    trigTestMap_injective hℓpos hbC.continuous hbs hb1 k₀
  refine ⟨(LinearMap.ker Λ).map Φ, inferInstance, ?_, ?_, ?_⟩
  · -- dimension count: `2k₀ + 1` coefficients, `#S + 2` constraints
    have hequiv := Submodule.equivMapOfInjective Φ hΦinj (LinearMap.ker Λ)
    rw [← hequiv.finrank_eq]
    have hker := finrank_ker_netConstraint_ge b ℓ k₀ S
    have hTT₁ : T₁ ≤ T := by rw [hT, hℓ]; exact hC5
    have hcnt := hcount T hTT₁
    have harith := sharpCount_dim_arith (k := (k₀ : ℝ)) (c₀ := (c₀ : ℝ)) hη0 hη1 hL hℓ hT hΔ
      hk₀gt hCR (by exact_mod_cast hC1)
    push_cast at hker
    linarith
  · rintro f ⟨c, hc, rfl⟩
    have hΛc : Λ c = 0 := hc
    rw [hΛ] at hΛc
    obtain ⟨-, h23⟩ := Prod.mk_eq_zero.mp hΛc
    obtain ⟨h2, h3⟩ := Prod.mk_eq_zero.mp h23
    exact ⟨contDiff_trigTest hbC ℓ k₀ c, tsupport_trigTest hb0 ℓ k₀ c, h2, h3⟩
  · rintro f ⟨c, hc, rfl⟩
    have hΛc : Λ c = 0 := hc
    rw [hΛ] at hΛc
    have hzero : ∀ s ∈ (S : Set ℂ), paperFT (trigTest b ℓ k₀ c) (gammaOf s) = 0 := by
      intro s hs
      have h1 := congrFun (Prod.mk_eq_zero.mp hΛc).1 ⟨s, hs⟩
      simpa using h1
    have hSc : (S : Set ℂ) ⊆ zetaZeroConfig.carrier := fun s hs => hS s hs
    have hnet' : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T →
        ∃ s ∈ (S : Set ℂ), ‖ρ - s‖ ≤ δ := by
      intro ρ hρ hρT
      obtain ⟨s, hs, h⟩ := hnet ρ hρ hρT
      exact ⟨s, hs, h⟩
    have hW := norm_W_trigTest_le_of_net hA₀ hloc (by linarith) hbint hbs hℓpos hΩ hΔ1 hB0 hdec'
      c hSc hδ hδL hnet' hzero
    have hbulk := two_mul_sum_le_integral_trigTest hℓpos hbC.continuous hbs hb1 k₀ c
    have hCS : (∑ j, ‖c j‖) ^ 2 ≤ (2 * k₀ + 1 : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (2 * k₀ + 1))))
        (f := fun j => ‖c j‖)
      rw [Finset.card_univ, Fintype.card_fin] at h
      have e : (((2 * k₀ + 1 : ℕ) : ℝ)) = 2 * k₀ + 1 := by push_cast; ring
      rw [e] at h
      exact h
    have hAr : L - η / 8 + η / 8 / 2 + η / 8 / 4 ≤ L := by linarith
    have hmarg := sharpCount_margin_arith (η := η) (L := L) (ℓ := ℓ) (T := T) (Δ := Δ)
      (k := (k₀ : ℝ)) (N := (N : ℝ)) (A₀ := A₀)
      (A := L - η / 8 + η / 8 / 2) (r := η / 8 / 4) hη0 hη1 hL hℓ hT hΔ hk₀le hNgt
      hAr hA₀ hC2
    have hmarg' : (2 * k₀ + 1 : ℝ) * B ^ 2 * (48 * A₀ * Real.log (T + 3)) / (2 * ℓ) ≤
        Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) := by
      rw [hBdef]; exact hmarg
    obtain ⟨hℓ7, hT0, hTle, hk2, hlog0, hlog⟩ :=
      level_bounds (k := (k₀ : ℝ)) hη0 hη1 hL hℓ hT hΔ hk₀le
    have hnetm := net_margin_arith (k := (k₀ : ℝ)) (Ib := ∫ u, ‖b u‖) hL hℓ7 hk2
      (by positivity) hT0 hTle hlog0 hlog hA₀ hbI0 hbI hδ
    set I₂ := ∫ u, ‖trigTest b ℓ k₀ c u‖ ^ 2 with hI₂
    have hI0 : 0 ≤ I₂ := integral_nonneg fun _ => by positivity
    have hS' : (∑ j, ‖c j‖) ^ 2 ≤ (2 * k₀ + 1 : ℝ) * (I₂ / (2 * ℓ)) := by
      refine hCS.trans ?_
      have : ∑ j, ‖c j‖ ^ 2 ≤ I₂ / (2 * ℓ) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hlogT0 : 0 ≤ 48 * A₀ * Real.log (T + 3) := by
      have : 0 ≤ A₀ := by linarith
      positivity
    show ‖zetaZeroConfig.W (Φ c) (Φ c)‖ ≤ _
    have hΦc : Φ c = trigTest b ℓ k₀ c := rfl
    rw [hΦc]
    exact energy_assembly hW hS' (by positivity) (by positivity) hlogT0 hI0 hmarg' hnetm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
