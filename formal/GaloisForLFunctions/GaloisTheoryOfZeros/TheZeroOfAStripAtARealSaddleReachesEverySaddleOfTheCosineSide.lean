import GaloisForLFunctions.GaloisTheoryOfZeros.ASignedLoopOfSaddlesExchangesTheZerosOfTwoAdjacentStrips

/-!
# The zero of a strip at a real saddle reaches every saddle of the cosine side

The squared ratio of the two terms of the model has the modulus

`|Q(a)| = 64π⁴ e^{9σ + 2 Re f(a)} / (Φ(0)² |2a − 1|)`, `Re f(a) = πe^{2σ}(cos 2η · (σ − 1) − η sin 2η)`,

at the saddle `a = σ + iη`. For fixed `σ` it decreases in `η ∈ [0, π/4)`: the cosine term dominates
below every saddle at which it dominates, and at the real saddles it dominates by the factor
`e^{7σ/2}`.

**Theorem** (`exists_simplyJoined_ofReal`). For every window `R`, far out: the zero of a strip at a
real saddle `ρ` is joined through simple zeros to the zero of the same strip at every saddle `a` of
the cosine side.

Proof. Along the real saddles from `ρ` to `Re a` and then up the vertical segment to `a` the
cosine term dominates, so the zero of a strip stays in its strip
(`exists_simplyJoined_of_stripFacts`).
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The modulus of the squared ratio -/

/-- `|Q(a)| = 64π⁴ e^{9σ + 2 Re f(a)} / (Φ(0)² |2a − 1|)`. -/
theorem norm_saddleRatioSq_eq (a : ℂ) :
    ‖saddleRatioSq a‖ = 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 *
      Real.exp (9 * a.re + 2 * (saddlePhaseValue a).re) / ‖2 * a - 1‖ := by
  have h1 : ‖-(64 * (π : ℂ) ^ 4)‖ = 64 * π ^ 4 := by
    rw [norm_neg, show (64 : ℂ) * (π : ℂ) ^ 4 = ((64 * π ^ 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : (9 * a + 2 * saddlePhaseValue a).re = 9 * a.re + 2 * (saddlePhaseValue a).re := by
    have e1 : (9 * a).re = 9 * a.re := by simp
    have e2 : (2 * saddlePhaseValue a).re = 2 * (saddlePhaseValue a).re := by simp
    rw [Complex.add_re, e1, e2]
  rw [saddleRatioSq, norm_div, norm_mul, norm_mul, norm_pow, h1, Complex.norm_exp, h2]
  ring

theorem WideRegion.two_mul_sub_one_ne_zero {a : ℂ} (h : WideRegion a) : 2 * a - 1 ≠ 0 := by
  intro h0
  have h1 : (2 * a - 1).re = 2 * a.re - 1 := by simp
  rw [h0, Complex.zero_re] at h1
  linarith [h.1]

theorem WideRegion.norm_bulkTerm_pos {a : ℂ} (h : WideRegion a) : 0 < ‖bulkTerm a‖ :=
  lt_of_lt_of_le (mul_pos (norm_pos_iff.mpr kernelC_zero_ne_zero) (Real.exp_pos _))
    h.le_norm_bulkTerm

/-- The cosine term dominates iff `|Q| ≥ (100/97)²`. -/
theorem cosineSide_iff {a : ℂ} (h : WideRegion a) :
    CosineSide a ↔ (100 / 97) ^ 2 ≤ ‖saddleRatioSq a‖ := by
  have hB := h.norm_bulkTerm_pos
  have hsq : ‖2 * saddleTerm a‖ ^ 2 = ‖saddleRatioSq a‖ * ‖bulkTerm a‖ ^ 2 := by
    rw [← norm_pow, two_mul_saddleTerm_sq h.ne_zero h.two_mul_sub_one_ne_zero, norm_mul, norm_pow]
  unfold CosineSide
  constructor
  · intro hc
    have h1 : (100 / 97 * ‖bulkTerm a‖) ^ 2 ≤ ‖2 * saddleTerm a‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [hsq, mul_pow] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  · intro hQ
    have h1 : (100 / 97 * ‖bulkTerm a‖) ^ 2 ≤ ‖2 * saddleTerm a‖ ^ 2 := by
      rw [hsq, mul_pow]
      exact mul_le_mul_of_nonneg_right hQ (by positivity)
    have h2 := (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h1
    linarith

/-! ## Below a saddle -/

/-- A point below a saddle of the wide region, at the same real part, is in the wide region. -/
theorem WideRegion.of_below {a a' : ℂ} (h : WideRegion a) (hre : a'.re = a.re) (h0 : 0 ≤ a'.im)
    (him : a'.im ≤ a.im) : WideRegion a' :=
  ⟨by rw [hre]; exact h.1, h0, by rw [hre]; linarith [h.2.2]⟩

/-- `|Q|` increases towards the real axis at a fixed real part: `Re f` decreases in `η` and
`|2a − 1|` increases. -/
theorem norm_saddleRatioSq_le_of_below {a a' : ℂ} (h : WideRegion a) (hre : a'.re = a.re)
    (h0 : 0 ≤ a'.im) (him : a'.im ≤ a.im) : ‖saddleRatioSq a‖ ≤ ‖saddleRatioSq a'‖ := by
  have hπ := Real.pi_pos
  have hlt := h.im_lt
  have hf : (saddlePhaseValue a).re ≤ (saddlePhaseValue a').re := by
    rw [saddlePhaseValue_re, saddlePhaseValue_re, hre]
    have hcos : Real.cos (2 * a.im) ≤ Real.cos (2 * a'.im) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    have hsin : Real.sin (2 * a'.im) ≤ Real.sin (2 * a.im) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have hs0 : 0 ≤ Real.sin (2 * a'.im) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hprod : Real.sin (2 * a'.im) * a'.im ≤ Real.sin (2 * a.im) * a.im :=
      mul_le_mul hsin him h0 (le_trans hs0 hsin)
    have h3 : Real.cos (2 * a.im) * (a.re - 1) ≤ Real.cos (2 * a'.im) * (a.re - 1) :=
      mul_le_mul_of_nonneg_right hcos (by linarith [h.1])
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hn : ‖2 * a' - 1‖ ≤ ‖2 * a - 1‖ := by
    have e1 : (2 * a' - 1).re = (2 * a - 1).re := by simp [hre]
    have e2 : (2 * a' - 1).im = 2 * a'.im := by simp
    have e3 : (2 * a - 1).im = 2 * a.im := by simp
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, e1, e2, e3]
    nlinarith [mul_le_mul him him h0 (le_trans h0 him)]
  have hn0 : 0 < ‖2 * a' - 1‖ :=
    norm_pos_iff.mpr (h.of_below hre h0 him).two_mul_sub_one_ne_zero
  have hE : Real.exp (9 * a.re + 2 * (saddlePhaseValue a).re) ≤
      Real.exp (9 * a'.re + 2 * (saddlePhaseValue a').re) :=
    Real.exp_le_exp.mpr (by rw [hre]; linarith)
  have hC : 0 ≤ 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 := by positivity
  rw [norm_saddleRatioSq_eq, norm_saddleRatioSq_eq]
  calc 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 * Real.exp (9 * a.re + 2 * (saddlePhaseValue a).re) /
        ‖2 * a - 1‖
      ≤ 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 * Real.exp (9 * a.re + 2 * (saddlePhaseValue a).re) /
        ‖2 * a' - 1‖ := div_le_div_of_nonneg_left (by positivity) hn0 hn
    _ ≤ 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 * Real.exp (9 * a'.re + 2 * (saddlePhaseValue a').re) /
        ‖2 * a' - 1‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hC) hn0.le

/-- **The cosine term dominates below every saddle at which it dominates.** -/
theorem CosineSide.of_below {a a' : ℂ} (hc : CosineSide a) (h : WideRegion a)
    (hre : a'.re = a.re) (h0 : 0 ≤ a'.im) (him : a'.im ≤ a.im) : CosineSide a' :=
  (cosineSide_iff (h.of_below hre h0 him)).mpr
    (((cosineSide_iff h).mp hc).trans (norm_saddleRatioSq_le_of_below h hre h0 him))

/-! ## Real saddles -/

theorem wideRegion_ofReal {ρ : ℝ} (hρ : 50 ≤ ρ) : WideRegion (ρ : ℂ) := by
  refine ⟨by rw [Complex.ofReal_re]; exact hρ, by rw [Complex.ofReal_im], ?_⟩
  rw [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  have h1 : 1 / (4 * ρ) ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith [Real.pi_gt_three]

/-- At a real saddle far out the bulk term is small against the saddle term:
`|B₀| ≤ Φ(0)` and `|S₀| ≥ e^{7ρ/2}`. -/
theorem norm_bulkTerm_ofReal_le {ρ : ℝ} (hρ : 50 ≤ ρ) (hΦ : ‖kernelC 0‖ ≤ ρ) :
    ‖bulkTerm (ρ : ℂ)‖ ≤ 1 / 100 * ‖saddleTerm (ρ : ℂ)‖ := by
  have hW := wideRegion_ofReal hρ
  have h1 := hW.norm_bulkTerm_le
  have h2 := hW.le_norm_saddleTerm
  have h3 := hW.phase_re_nonneg (by rw [Complex.ofReal_im]; norm_num)
  rw [Complex.ofReal_re] at h2
  have h4 : Real.exp (7 * ρ / 2) ≤ Real.exp (7 * ρ / 2 + (saddlePhaseValue (ρ : ℂ)).re) :=
    Real.exp_le_exp.mpr (by linarith)
  have h5 : 100 * ρ ≤ Real.exp (7 * ρ / 2) := by
    have e : Real.exp (7 * ρ / 2) = Real.exp ρ * Real.exp (5 * ρ / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h6 := Real.add_one_le_exp ρ
    have h7 := Real.add_one_le_exp (5 * ρ / 2)
    have h8 : (ρ + 1) * (5 * ρ / 2 + 1) ≤ Real.exp ρ * Real.exp (5 * ρ / 2) :=
      mul_le_mul h6 h7 (by linarith) (Real.exp_pos _).le
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (by linarith : (0 : ℝ) ≤ ρ)]
  linarith

theorem cosineSide_ofReal {ρ : ℝ} (hρ : 50 ≤ ρ) (hΦ : ‖kernelC 0‖ ≤ ρ) :
    CosineSide (ρ : ℂ) := by
  have h := norm_bulkTerm_ofReal_le hρ hΦ
  unfold CosineSide
  rw [norm_mul, Complex.norm_ofNat]
  linarith [norm_nonneg (saddleTerm (ρ : ℂ))]

/-! ## Segments of saddles -/

/-- The parameter of a segment, constant outside `[0, 1]`. -/
def unitClamp (s : ℝ) : ℝ := max 0 (min s 1)

theorem continuous_unitClamp : Continuous unitClamp :=
  continuous_const.max (continuous_id.min continuous_const)

theorem unitClamp_mem (s : ℝ) : unitClamp s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem unitClamp_zero : unitClamp 0 = 0 := by simp [unitClamp]

theorem unitClamp_one : unitClamp 1 = 1 := by simp [unitClamp]

/-- Along a segment of saddles on which the strips hold the zeros of the window, the zero of a
strip is joined through simple zeros to the zero of the same strip at the end. -/
theorem exists_simplyJoined_segment {R : ℝ} {p q : ℂ}
    (hW : ∀ c ∈ Icc (0 : ℝ) 1, WideRegion (p + c * (q - p)))
    (hF : ∀ c ∈ Icc (0 : ℝ) 1, StripFacts R (p + c * (q - p))) {θ : ℝ}
    (hθ : Real.sin θ = 0) (hθR : |θ| + π + 2 ≤ R) {z₀ : ℂ}
    (h0 : complexHeat (saddleTime p) z₀ = 0) (hz₀ : p * z₀ ∈ cosStrip θ) :
    ∃ z₁, SimplyJoined (saddleTime p) z₀ (saddleTime q) z₁ ∧
      complexHeat (saddleTime q) z₁ = 0 ∧ q * z₁ ∈ openCosStrip θ := by
  have ha : Continuous fun s : ℝ => p + (unitClamp s : ℂ) * (q - p) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_unitClamp).mul continuous_const)
  have a0 : p + (unitClamp 0 : ℂ) * (q - p) = p := by
    rw [unitClamp_zero, Complex.ofReal_zero, zero_mul, add_zero]
  have a1 : p + (unitClamp 1 : ℂ) * (q - p) = q := by
    rw [unitClamp_one, Complex.ofReal_one, one_mul, add_sub_cancel]
  have h := exists_simplyJoined_of_stripFacts (R := R)
    (a := fun s : ℝ => p + (unitClamp s : ℂ) * (q - p)) ha
    (fun s => hW _ (unitClamp_mem s)) (fun s => hF _ (unitClamp_mem s)) hθ hθR (z₀ := z₀)
    (by rw [a0]; exact h0) (by rw [a0]; exact hz₀)
  rw [a0, a1] at h
  exact h

/-! ## From a real saddle to a saddle of the cosine side -/

/-- **The zero of a strip at a real saddle reaches every saddle of the cosine side.** For every
window `R` there is `σ₀ ≥ max(50, Φ(0))` beyond which the strips hold the zeros of the window on
the cosine side, and the zero of a strip at a real saddle `ρ` is joined through simple zeros to the
zero of the same strip at every saddle `a` of the cosine side. -/
theorem exists_simplyJoined_ofReal (R : ℝ) : ∃ σ₀ : ℝ, 50 ≤ σ₀ ∧ ‖kernelC 0‖ ≤ σ₀ ∧
    (∀ a : ℂ, WideRegion a → σ₀ ≤ a.re → CosineSide a → StripFacts R a) ∧
    ∀ a : ℂ, WideRegion a → CosineSide a → σ₀ ≤ a.re → ∀ ρ : ℝ, σ₀ ≤ ρ →
      ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R → ∀ z₀ : ℂ,
        complexHeat (saddleTime (ρ : ℂ)) z₀ = 0 → (ρ : ℂ) * z₀ ∈ cosStrip θ →
        ∃ z₁, SimplyJoined (saddleTime (ρ : ℂ)) z₀ (saddleTime a) z₁ ∧
          complexHeat (saddleTime a) z₁ = 0 ∧ a * z₁ ∈ openCosStrip θ := by
  obtain ⟨σA, hσA⟩ := exists_stripFacts R
  have h50 : (50 : ℝ) ≤ max σA (max 50 ‖kernelC 0‖) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hΦ : ‖kernelC 0‖ ≤ max σA (max 50 ‖kernelC 0‖) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hA : σA ≤ max σA (max 50 ‖kernelC 0‖) := le_max_left _ _
  have hfacts : ∀ a : ℂ, WideRegion a → max σA (max 50 ‖kernelC 0‖) ≤ a.re → CosineSide a →
      StripFacts R a := fun a hW hfar hc => hσA a hW (hA.trans hfar) hc
  refine ⟨_, h50, hΦ, hfacts, fun a hW hc hfar ρ hρ θ hθ hθR z₀ h0 hz₀ => ?_⟩
  -- the real saddles from `ρ` to `Re a`
  have hreal : ∀ c ∈ Icc (0 : ℝ) 1,
      (ρ : ℂ) + c * ((a.re : ℂ) - ρ) = ((ρ + c * (a.re - ρ) : ℝ) : ℂ) ∧
        max σA (max 50 ‖kernelC 0‖) ≤ ρ + c * (a.re - ρ) := by
    intro c hc'
    refine ⟨by push_cast; ring, ?_⟩
    nlinarith [mul_nonneg hc'.1 (sub_nonneg.mpr hfar),
      mul_nonneg (sub_nonneg.mpr hc'.2) (sub_nonneg.mpr hρ)]
  obtain ⟨z₁, hj₁, hz₁, hs₁⟩ := exists_simplyJoined_segment (R := R) (p := (ρ : ℂ))
    (q := (a.re : ℂ))
    (fun c hc' => by
      rw [(hreal c hc').1]
      exact wideRegion_ofReal (h50.trans (hreal c hc').2))
    (fun c hc' => by
      rw [(hreal c hc').1]
      exact hfacts _ (wideRegion_ofReal (h50.trans (hreal c hc').2))
        (by rw [Complex.ofReal_re]; exact (hreal c hc').2)
        (cosineSide_ofReal (h50.trans (hreal c hc').2) (hΦ.trans (hreal c hc').2)))
    hθ hθR h0 hz₀
  -- the vertical segment from `Re a` to `a`
  have hvert : ∀ c ∈ Icc (0 : ℝ) 1,
      ((a.re : ℂ) + c * (a - a.re)).re = a.re ∧ ((a.re : ℂ) + c * (a - a.re)).im = c * a.im := by
    intro c _
    constructor <;> simp
  have hvim : ∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ c * a.im ∧ c * a.im ≤ a.im := fun c hc' =>
    ⟨mul_nonneg hc'.1 hW.2.1, by nlinarith [mul_nonneg (sub_nonneg.mpr hc'.2) hW.2.1]⟩
  obtain ⟨z₂, hj₂, hz₂, hs₂⟩ := exists_simplyJoined_segment (R := R) (p := (a.re : ℂ)) (q := a)
    (fun c hc' => hW.of_below (hvert c hc').1 (by rw [(hvert c hc').2]; exact (hvim c hc').1)
      (by rw [(hvert c hc').2]; exact (hvim c hc').2))
    (fun c hc' => hfacts _
      (hW.of_below (hvert c hc').1 (by rw [(hvert c hc').2]; exact (hvim c hc').1)
        (by rw [(hvert c hc').2]; exact (hvim c hc').2))
      (by rw [(hvert c hc').1]; exact hfar)
      (hc.of_below hW (hvert c hc').1 (by rw [(hvert c hc').2]; exact (hvim c hc').1)
        (by rw [(hvert c hc').2]; exact (hvim c hc').2)))
    hθ hθR hz₁ (openCosStrip_subset θ hs₁)
  exact ⟨z₂, hj₁.trans hj₂, hz₂, hs₂⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
