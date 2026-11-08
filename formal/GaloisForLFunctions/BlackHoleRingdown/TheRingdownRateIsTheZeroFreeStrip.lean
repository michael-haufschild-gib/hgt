import GaloisForLFunctions.BlackHoleRingdown.TheRingdownOfAPulse
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# The ringdown rate of a pulse is the zero-free strip

For a compact pulse `h` sent into the modular horizon, let `𝓕_h(τ, z) = Π_h(τ, z) - 6a(-i/2)e^{τ/2}` be
its image field with the mean growth removed. For `0 < δ ≤ 1/4`:

  every zero of `ζ` with `Re ρ > 0` has `Re ρ ≤ 1 - 2δ`
  ⟺ for every pulse, every point and every `ε > 0`, `𝓕_h(τ, z) = O(e^{-(δ-ε)τ})` as `τ → ∞`

(`zeroFreeStrip_iff_pulse_ringdown`). At `δ = 1/4` this is RH (`riemannHypothesis_iff_pulse_ringdown`).
So the late-time decay exponent of the physical field is exactly half the width of the zero-free strip,
the same `δ` that the horocycle reads as the gain `y^{1/2+δ}` over the trivial thermalization rate.

**Forward.** `𝓕_h(τ) = ∫ a(ξ) E(iξ) e^{iξτ} dξ`. On `-σ ≤ Re u ≤ 0`, `σ < δ`, `ξ(1+2u)` has no zeros, the
three-circles bound makes `1/ζ(1+2u)` polynomial, so `E` grows polynomially and the rapid amplitude beats
it. Shifting the line to `Re u = -σ` gives `|𝓕_h(τ)| ≤ e^{-στ} ∫ |a E|`.

**Converse.** The image field vanishes before the pulse arrives (`τ ≤ -T`), and for `Re w > ½` its
Laplace transform is `2π a(-iw) E(w; z)`, row by row. If `𝓕_h = O(e^{-δτ})`, the Laplace transform of `𝓕_h`
is holomorphic on `Re w > -δ`, so `ξ(1+2w)((2w-1)ℒ𝓕_h(w) + 2m e^{(w-½)T})` and `2π a(-iw)(2w-1)N(w; z)`
are entire on `Re w > -δ` and agree on `Re w > ½`. At a zero `p = (ρ-1)/2` the first vanishes, so
`a(-ip) N(p; z) = 0`, which fails for the exciting pulse at a suitable point.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

namespace RingdownRate

/-! ### The image field vanishes before the pulse arrives -/

/-- Every image of a point of height `Y` has height at most `max Y Y⁻¹`. -/
theorem rowHgt_le (p : EisensteinSeries.gammaSet 1 1 0) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    rowHgt (rowC p) (rowD p) x Y ≤ max Y Y⁻¹ := by
  have hR := rowDen_pos p x hY
  unfold rowHgt
  rw [div_le_iff₀ hR]
  have hYi : Y⁻¹ ≤ max Y Y⁻¹ := le_max_right _ _
  have hYm : Y ≤ max Y Y⁻¹ := le_max_left _ _
  by_cases hc : p.1 0 = 0
  · have hg : (p.1 0).gcd (p.1 1) = 1 := p.2.2
    rw [hc, Int.gcd_zero_left] at hg
    have hd : (p.1 1) ^ 2 = 1 := by
      have := Int.natAbs_sq (p.1 1)
      rw [hg] at this
      simpa using this.symm
    have hdR : rowD p ^ 2 = 1 := by
      unfold rowD
      exact_mod_cast hd
    have hcR : rowC p = 0 := by
      unfold rowC
      rw [hc]
      simp
    have hden : rowDen (rowC p) (rowD p) x Y = 1 := by
      unfold rowDen
      rw [hcR]
      simpa using hdR
    rw [hden, mul_one]
    exact hYm
  · have hc1 : (1 : ℝ) ≤ rowC p ^ 2 := by
      have h1 : (1 : ℤ) ≤ |p.1 0| := Int.one_le_abs hc
      have h2 : (1 : ℝ) ≤ |((p.1 0 : ℤ) : ℝ)| := by exact_mod_cast h1
      unfold rowC
      rw [one_le_sq_iff_one_le_abs]
      exact h2
    have hden : Y ^ 2 ≤ rowDen (rowC p) (rowD p) x Y := by
      unfold rowDen
      nlinarith [sq_nonneg (rowC p * x + rowD p), sq_nonneg Y]
    have hYinv : Y = Y⁻¹ * Y ^ 2 := by field_simp
    calc Y = Y⁻¹ * Y ^ 2 := hYinv
      _ ≤ max Y Y⁻¹ * rowDen (rowC p) (rowD p) x Y :=
          mul_le_mul hYi hden (by positivity) (by positivity)

/-- **Causality.** The image field of a pulse vanishes at all early times. -/
theorem imageField_eq_zero_of_le (h : CompactPulse) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ τ : ℝ, τ ≤ -T → imageField h τ x Y = 0 := by
  obtain ⟨S₀, hS₀, hsupp⟩ := h.exists_support_bound
  refine ⟨S₀ + |Real.log (max Y Y⁻¹)| + 1, by positivity, fun τ hτ => ?_⟩
  have hterm : ∀ p : EisensteinSeries.gammaSet 1 1 0, imageTerm h (rowC p) (rowD p) τ x Y = 0 := by
    intro p
    have hy := rowHgt_pos hY (rowDen_pos p x hY)
    have hlog : Real.log (rowHgt (rowC p) (rowD p) x Y) ≤ |Real.log (max Y Y⁻¹)| :=
      (Real.log_le_log hy (rowHgt_le p x hY)).trans (le_abs_self _)
    have hneg : S₀ < |τ + Real.log (rowHgt (rowC p) (rowD p) x Y)| := by
      have := neg_abs_le (τ + Real.log (rowHgt (rowC p) (rowD p) x Y))
      linarith
    rw [imageTerm, pulseF, hsupp _ hneg, mul_zero]
  simp [imageField, hterm]

/-! ### The Laplace transform of the image field -/

theorem imageTerm_mul_exp (h : ℝ → ℂ) (p : EisensteinSeries.gammaSet 1 1 0) (τ x : ℝ) {Y : ℝ}
    (hY : 0 < Y) (w : ℂ) :
    Complex.exp (-w * τ) * imageTerm h (rowC p) (rowD p) τ x Y =
      ((rowHgt (rowC p) (rowD p) x Y : ℝ) : ℂ) ^ (1 / 2 + w) *
        (h (τ + Real.log (rowHgt (rowC p) (rowD p) x Y)) *
          Complex.exp (-w * ((τ + Real.log (rowHgt (rowC p) (rowD p) x Y) : ℝ) : ℂ))) := by
  have hy := rowHgt_pos hY (rowDen_pos p x hY)
  set y := rowHgt (rowC p) (rowD p) x Y
  rw [cpow_half_add_eq hy, imageTerm, pulseF]
  have e : Complex.exp (-w * τ) =
      Complex.exp (w * (Real.log y : ℂ)) * Complex.exp (-w * ((τ + Real.log y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

/-- **The Laplace transform of the image field is the Eisenstein function.** For `Re w > ½`,
`∫ e^{-wτ} Π_h(τ, z) dτ = 2π a(-iw) E(w; z)`: each row contributes `y_γ^{½+w}` times the Laplace
transform of the pulse, and the row sum is the Eisenstein series. -/
theorem integral_exp_mul_imageField (h : CompactPulse) (x : ℝ) {Y : ℝ} (hY : 0 < Y) {w : ℂ}
    (hw : 1 / 2 < w.re) (him : w.im ≠ 0) :
    ∫ τ : ℝ, Complex.exp (-w * τ) * imageField h τ x Y =
      2 * Real.pi * pulseAmplitude h (-I * w) * normalizedEisenstein w x Y := by
  set z := chartPoint x hY with hz
  have hzre : z.re = x := rfl
  have hzim : z.im = Y := rfl
  have hrow : ∀ p : EisensteinSeries.gammaSet 1 1 0, rowHgt (rowC p) (rowD p) x Y = rowHeight p z := by
    intro p
    rw [rowHeight, ← rowHgt_eq_im, hzre, hzim]
  set k : ℝ → ℂ := fun S => h S * Complex.exp (-w * S) with hk
  have hkint : Integrable k := by
    refine (h.integrable_mul_cexp (-I * w)).congr (Eventually.of_forall fun S => ?_)
    simp only [hk]
    congr 2
    linear_combination (w * (S : ℂ)) * I_sq
  set F : EisensteinSeries.gammaSet 1 1 0 → ℝ → ℂ := fun p τ =>
    Complex.exp (-w * τ) * imageTerm h (rowC p) (rowD p) τ x Y with hF
  have hFeq : ∀ p τ, F p τ = ((rowHeight p z : ℝ) : ℂ) ^ (1 / 2 + w) *
      k (τ + Real.log (rowHeight p z)) := by
    intro p τ
    simp only [hF, hk]
    rw [imageTerm_mul_exp h p τ x hY w, hrow]
  have hnormpow : ∀ p : EisensteinSeries.gammaSet 1 1 0,
      ‖((rowHeight p z : ℝ) : ℂ) ^ (1 / 2 + w)‖ = rowHeight p z ^ (1 / 2 + w.re) := by
    intro p
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (rowHeight_pos p z)]
    congr 1
    simp
  have hFint : ∀ p, Integrable (F p) := by
    intro p
    have := (hkint.comp_add_right (Real.log (rowHeight p z))).const_mul
      (((rowHeight p z : ℝ) : ℂ) ^ (1 / 2 + w))
    refine this.congr (Eventually.of_forall fun τ => ?_)
    rw [hFeq]
  have hFval : ∀ p, ∫ τ, F p τ =
      ((rowHeight p z : ℝ) : ℂ) ^ (1 / 2 + w) * (2 * Real.pi * pulseAmplitude h (-I * w)) := by
    intro p
    simp_rw [hFeq]
    rw [integral_const_mul, integral_add_right_eq_self (fun τ => k τ), hk,
      h.integral_mul_cexp_eq w]
  have hFnorm : ∀ p, ∫ τ, ‖F p τ‖ = (∫ S, ‖k S‖) * rowHeight p z ^ (1 / 2 + w.re) := by
    intro p
    simp_rw [hFeq, norm_mul, hnormpow]
    rw [integral_const_mul, integral_add_right_eq_self (fun τ => ‖k τ‖), mul_comm]
  have hsum0 : Summable fun p : EisensteinSeries.gammaSet 1 1 0 =>
      ((rowHeight p z : ℝ) : ℂ) ^ (((1 / 2 + w.re : ℝ) : ℂ)) :=
    summable_rowHeight_cpow (by simp; linarith) z
  have hsumN : Summable fun p : EisensteinSeries.gammaSet 1 1 0 => rowHeight p z ^ (1 / 2 + w.re) := by
    refine hsum0.norm.congr fun p => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (rowHeight_pos p z), Complex.ofReal_re]
  have hsumI : Summable fun p => ∫ τ, ‖F p τ‖ := by
    simp_rw [hFnorm]
    exact hsumN.mul_left _
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsumI
  have hlhs : ∫ τ : ℝ, Complex.exp (-w * τ) * imageField h τ x Y =
      (1 / 2 : ℂ) * ∫ τ, ∑' p, F p τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [hF, imageField]
    rw [tsum_mul_left]
    ring
  rw [hlhs, ← hHS.tsum_eq]
  simp_rw [hFval]
  rw [tsum_mul_right]
  have hE := normalizedEisenstein_eq_rowSum hw him z
  rw [hzre, hzim] at hE
  rw [hE, rowSum]
  ring

/-! ### Laplace transforms of decaying fields -/

theorem setIntegral_Ioi_shift (f : ℝ → ℂ) (T : ℝ) :
    ∫ τ in Ioi (-T), f τ = ∫ σ in Ioi (0 : ℝ), f (σ - T) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self _ T]
  refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
  simp only
  by_cases hσ : 0 < σ
  · rw [indicator_of_mem (show σ - T ∈ Ioi (-T) by simp; linarith),
      indicator_of_mem (show σ ∈ Ioi (0 : ℝ) from hσ)]
  · rw [indicator_of_notMem (show σ - T ∉ Ioi (-T) by simp; linarith),
      indicator_of_notMem (show σ ∉ Ioi (0 : ℝ) from hσ)]

theorem norm_exp_mul_le {G : ℝ → ℂ} {T δ C : ℝ} (hb : ∀ τ, -T < τ → ‖G τ‖ ≤ C * Real.exp (-δ * τ))
    (w : ℂ) {τ : ℝ} (hτ : -T < τ) :
    ‖Complex.exp (-w * τ) * G τ‖ ≤ C * Real.exp (-(w.re + δ) * τ) := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (-w * (τ : ℂ)).re = -(w.re * τ) := by simp
  rw [hre]
  calc Real.exp (-(w.re * τ)) * ‖G τ‖ ≤ Real.exp (-(w.re * τ)) * (C * Real.exp (-δ * τ)) :=
        mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le
    _ = C * Real.exp (-(w.re + δ) * τ) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

theorem integrableOn_exp_mul_of_bound {G : ℝ → ℂ} (hG : Continuous G) {T δ C : ℝ}
    (hb : ∀ τ, -T < τ → ‖G τ‖ ≤ C * Real.exp (-δ * τ)) {w : ℂ} (hw : -δ < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w * τ) * G τ) (Ioi (-T)) := by
  have hint : IntegrableOn (fun τ : ℝ => C * Real.exp (-(w.re + δ) * τ)) (Ioi (-T)) :=
    (integrableOn_exp_mul_Ioi (by linarith) (-T)).const_mul C
  refine hint.mono' ((by fun_prop : Continuous fun τ : ℝ => Complex.exp (-w * τ)).mul hG).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => norm_exp_mul_le hb w hτ))

/-- **The Laplace transform of a field decaying like `e^{-δτ}` is holomorphic on `Re w > -δ`.** -/
theorem differentiableOn_laplace {G : ℝ → ℂ} (hG : Continuous G) {T δ C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ τ, -T < τ → ‖G τ‖ ≤ C * Real.exp (-δ * τ)) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ τ in Ioi (-T), Complex.exp (-w * τ) * G τ) {w : ℂ | -δ < w.re} := by
  intro w₀ hw₀
  have hw₀' : -δ < w₀.re := hw₀
  set η : ℝ := (w₀.re + δ) / 2 with hη
  set s₀ : ℝ := (w₀.re - δ) / 2 with hs₀
  have hη0 : 0 < η := by rw [hη]; linarith
  set φ : ℝ → ℂ := fun σ => G (σ - T) * Complex.exp (-(s₀ : ℂ) * σ) with hφ
  have hφL : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))) := by
    have hbase := (memLp_two_expRay_restrict (w := (η : ℂ)) (by simpa using hη0) 0).const_mul
      ((C * Real.exp (δ * T) : ℝ) : ℂ)
    refine hbase.of_le ((hG.comp (continuous_id.sub continuous_const)).mul
      (by fun_prop)).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun σ hσ => ?_))
    have hσ' : -T < σ - T := by simp at hσ; linarith
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_expRay, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hre : (-(s₀ : ℂ) * (σ : ℂ)).re = -(s₀ * σ) := by simp
    rw [hre]
    have h1 := hb _ hσ'
    calc ‖G (σ - T)‖ * Real.exp (-(s₀ * σ)) ≤ C * Real.exp (-δ * (σ - T)) * Real.exp (-(s₀ * σ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = C * Real.exp (δ * T) * Real.exp (-((η : ℂ).re * σ)) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
          congr 2
          simp only [Complex.ofReal_re]
          rw [hη, hs₀]
          ring
  have heq : (fun w : ℂ => ∫ τ in Ioi (-T), Complex.exp (-w * τ) * G τ) =
      fun w => Complex.exp (w * T) * laplaceRay φ (w - s₀) := by
    funext w
    rw [setIntegral_Ioi_shift, laplaceRay, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun σ _ => ?_
    simp only [hφ, expRay]
    have e2 : Complex.exp (-w * ((σ - T : ℝ) : ℂ)) = Complex.exp (w * T) *
        (Complex.exp (-(s₀ : ℂ) * σ) * Complex.exp (-((w - s₀) * σ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e2]
    ring
  rw [heq]
  have hmem : w₀ - (s₀ : ℂ) ∈ {w : ℂ | 0 < w.re} := by
    show 0 < (w₀ - (s₀ : ℂ)).re
    simp only [sub_re, ofReal_re]
    rw [hs₀]
    linarith
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL := ((differentiableOn_laplaceRay hφL).differentiableAt (hopen.mem_nhds hmem)).comp w₀
    (differentiableAt_id.sub_const (s₀ : ℂ))
  exact ((by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (w * T)) w₀).mul hL
    |>.differentiableWithinAt

/-! ### The converse: a ringdown rate is a zero-free strip -/

/-- The entire numerator `(2w-1) N(w; x, 1)`. -/
def entireNumerator (x : ℝ) (w : ℂ) : ℂ :=
  (2 * w - 1) * xi (1 + 2 * w) + (1 + 2 * w) * xi (2 * w) +
    (2 * w - 1) * ((1 + 2 * w) * (2 * w)) * eisTail w x 1

theorem entireNumerator_eq (x : ℝ) {w : ℂ} (hw : 2 * w - 1 ≠ 0) :
    entireNumerator x w = (2 * w - 1) * eisensteinNumerator w x 1 := by
  simp only [entireNumerator, eisensteinNumerator, Complex.ofReal_one, one_cpow, one_mul, mul_one]
  field_simp

theorem differentiable_entireNumerator (x : ℝ) : Differentiable ℂ (entireNumerator x) := by
  intro w
  have hx1 : DifferentiableAt ℂ (fun v : ℂ => xi (1 + 2 * v)) w := differentiable_xi_shift w
  have hx2 : DifferentiableAt ℂ (fun v : ℂ => xi (2 * v)) w :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) w
  have ht := differentiableAt_eisTail x one_pos w
  unfold entireNumerator
  fun_prop

/-- **A ringdown rate is a zero-free strip.** If at height `1` every compact pulse rings down at rate
`e^{-δτ}` after its mean growth is removed, every zero of `ζ` with `Re ρ > 0` has `Re ρ ≤ 1 - 2δ`. -/
theorem re_le_of_pulse_ringdown {δ : ℝ} (hδ : 0 < δ)
    (hdecay : ∀ (h : CompactPulse) (x : ℝ), ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖pulseField h τ x 1‖ ≤ C * Real.exp (-δ * τ))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) : ρ.re ≤ 1 - 2 * δ := by
  by_contra hlt
  push Not at hlt
  have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ
  have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  set p : ℂ := (ρ - 1) / 2 with hpdef
  have hp1 : 1 + 2 * p = ρ := by rw [hpdef]; ring
  have hpxi : xi (1 + 2 * p) = 0 := by rw [hp1]; exact (xi_eq_zero_iff hρ0 hne1).2 hρ
  have hpre : p.re = (ρ.re - 1) / 2 := by rw [hpdef]; simp
  have hpU : -δ < p.re := by rw [hpre]; linarith
  have hp2 : 2 * p - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  obtain ⟨h, x, hN⟩ := exists_pulse_exciting_zero hpxi one_pos
  obtain ⟨C₀, hC₀⟩ := hdecay h x
  obtain ⟨T, hT0, hTz⟩ := imageField_eq_zero_of_le h x one_pos
  set G : ℝ → ℂ := fun τ => pulseField h τ x 1 with hG
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun τ =>
    (hasDerivAt_pulseField_time h τ x one_pos).continuousAt
  -- a bound on `(-T, ∞)`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := 0)).exists_bound_of_continuousOn hGc.continuousOn
  set C : ℝ := max (max C₀ B) 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hb : ∀ τ, -T < τ → ‖G τ‖ ≤ C * Real.exp (-δ * τ) := by
    intro τ hτ
    rcases le_or_gt 0 τ with h0 | h0
    · calc ‖G τ‖ ≤ C₀ * Real.exp (-δ * τ) := hC₀ τ h0
        _ ≤ C * Real.exp (-δ * τ) :=
            mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) (Real.exp_pos _).le
    · have h1 : ‖G τ‖ ≤ B := hB τ ⟨hτ.le, h0.le⟩
      have h2 : 1 ≤ Real.exp (-δ * τ) := Real.one_le_exp (by nlinarith)
      calc ‖G τ‖ ≤ B := h1
        _ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
        _ ≤ C * Real.exp (-δ * τ) := le_mul_of_one_le_right hC h2
  set m := meanCoefficient h with hm
  set L : ℂ → ℂ := fun w => ∫ τ in Ioi (-T), Complex.exp (-w * τ) * G τ with hL
  set U : Set ℂ := {w : ℂ | -δ < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hLd : DifferentiableOn ℂ L U := differentiableOn_laplace hGc hC hb
  set Φ₁ : ℂ → ℂ := fun w => (2 * w - 1) * xi (1 + 2 * w) * L w +
    2 * m * xi (1 + 2 * w) * Complex.exp ((w - 1 / 2) * T) with hΦ₁
  set Φ₂ : ℂ → ℂ := fun w => 2 * Real.pi * pulseAmplitude h (-I * w) * entireNumerator x w with hΦ₂
  have hxid : Differentiable ℂ fun w : ℂ => xi (1 + 2 * w) := fun w => differentiable_xi_shift w
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    intro w hw
    have hLw := (hLd w hw).differentiableAt (hUo.mem_nhds hw)
    have : DifferentiableAt ℂ Φ₁ w := by
      simp only [hΦ₁]
      have := hxid w
      fun_prop
    exact this.differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    intro w _
    have ha := h.differentiable_amplitude
    have hn := differentiable_entireNumerator x
    have : DifferentiableAt ℂ Φ₂ w := by
      simp only [hΦ₂]
      have h1 : DifferentiableAt ℂ (fun w : ℂ => pulseAmplitude h (-I * w)) w :=
        (ha _).comp w (by fun_prop)
      have h2 := hn w
      fun_prop
    exact this.differentiableWithinAt
  -- the two agree on `Re w > ½`, `Im w > 0`
  have hagree : ∀ w : ℂ, 1 / 2 < w.re → 0 < w.im → Φ₁ w = Φ₂ w := by
    intro w hw hwi
    have hwU : -δ < w.re := by linarith
    have hlap := integral_exp_mul_imageField h x one_pos hw hwi.ne'
    -- split the transform at the arrival time
    have hsplit : ∫ τ : ℝ, Complex.exp (-w * τ) * imageField h τ x 1 =
        L w + m * (-Complex.exp ((1 / 2 - w) * (-T : ℝ)) / (1 / 2 - w)) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (-T)) fun τ hτ => by
        rw [hTz τ (by simpa using hτ), mul_zero]]
      have hre : (1 / 2 - w).re < 0 := by simp; linarith
      have he : ∀ τ : ℝ, Complex.exp (-w * τ) * imageField h τ x 1 =
          Complex.exp (-w * τ) * G τ + m * Complex.exp ((1 / 2 - w) * τ) := by
        intro τ
        have e1 : Complex.exp (-w * τ) * Complex.exp ((τ : ℂ) / 2) = Complex.exp ((1 / 2 - w) * τ) := by
          rw [← Complex.exp_add]
          congr 1
          ring
        simp only [hG, pulseField]
        rw [← hm]
        linear_combination m * e1
      rw [setIntegral_congr_fun measurableSet_Ioi (fun τ _ => he τ),
        integral_add (integrableOn_exp_mul_of_bound hGc hb hwU)
          ((integrableOn_exp_mul_complex_Ioi hre (-T)).const_mul m),
        integral_const_mul, integral_exp_mul_complex_Ioi hre (-T)]
    have hξ : xi (1 + 2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
    have h2w : 2 * w - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    have h12 : (1 / 2 - w : ℂ) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    have hcomb := hlap.symm.trans hsplit
    rw [normalizedEisenstein_eq_numerator_div hξ x 1] at hcomb
    set e := Complex.exp ((w - 1 / 2) * T) with he
    have hexp : Complex.exp ((1 / 2 - w) * ((-T : ℝ) : ℂ)) = e := by
      rw [he]
      congr 1
      push_cast
      ring
    rw [hexp] at hcomb
    have h3 : 2 * Real.pi * pulseAmplitude h (-I * w) * eisensteinNumerator w x 1 =
        xi (1 + 2 * w) * (L w + m * (-e / (1 / 2 - w))) := by
      rw [← hcomb]
      field_simp
    have h4 : (2 * w - 1) * (-e / (1 / 2 - w)) = 2 * e := by
      rw [show (2 * w - 1) * (-e / (1 / 2 - w)) = 2 * e * ((1 / 2 - w) / (1 / 2 - w)) by ring,
        div_self h12, mul_one]
    simp only [hΦ₁, hΦ₂]
    rw [entireNumerator_eq x h2w,
      show (2 * Real.pi : ℂ) * pulseAmplitude h (-I * w) * ((2 * w - 1) * eisensteinNumerator w x 1) =
        (2 * w - 1) * (2 * Real.pi * pulseAmplitude h (-I * w) * eisensteinNumerator w x 1) by ring, h3]
    linear_combination (-(xi (1 + 2 * w)) * m) * h4
  have hEq : EqOn Φ₁ Φ₂ U := by
    refine hΦ₁a.eqOn_of_preconnected_of_eventuallyEq hΦ₂a (convex_halfSpace_re_gt (-δ)).isPreconnected
      (show (1 + I : ℂ) ∈ U by show -δ < (1 + I).re; simp; linarith) ?_
    have hV : IsOpen {w : ℂ | 1 / 2 < w.re ∧ 0 < w.im} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)
    filter_upwards [hV.mem_nhds (show (1 + I : ℂ) ∈ {w : ℂ | 1 / 2 < w.re ∧ 0 < w.im} by
      exact ⟨by norm_num, by norm_num⟩)] with w hw
    exact hagree w hw.1 hw.2
  have hp := hEq hpU
  simp only [hΦ₁, hΦ₂, hpxi, mul_zero, zero_mul, add_zero] at hp
  rw [entireNumerator_eq x hp2] at hp
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have : pulseNumerator h x 1 p = 0 := by
    rw [pulseNumerator]
    have h3 : (2 * Real.pi : ℂ) * (2 * p - 1) * (pulseAmplitude h (-I * p) * eisensteinNumerator p x 1) = 0 := by
      linear_combination -hp
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (mul_ne_zero hpi hp2)
    · exact h4
  exact hN this

/-! ### The forward direction: a zero-free strip is a ringdown rate -/

theorem differentiableAt_normalizedEisenstein {u : ℂ} (hξ : xi (1 + 2 * u) ≠ 0) (hu : u.re < 1 / 2)
    (x : ℝ) {Y : ℝ} (hY : 0 < Y) : DifferentiableAt ℂ (fun v => normalizedEisenstein v x Y) u := by
  have hc : ContinuousAt (fun v : ℂ => xi (1 + 2 * v)) u := (differentiable_xi_shift u).continuousAt
  refine ((differentiableAt_eisensteinNumerator x hY hu).div (differentiable_xi_shift u) hξ).congr_of_eventuallyEq ?_
  filter_upwards [hc.eventually_ne hξ] with v hv
  exact normalizedEisenstein_eq_numerator_div hv x Y

section ZeroFree

variable {δ σ : ℝ} (hδ : δ ≤ 1 / 4) (hσ : 0 < σ) (hσδ : σ < δ)
  (hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ)
include hδ hσδ hz

theorem xi_ne_zero_of_zeroFree {u : ℂ} (h1 : -σ ≤ u.re) : xi (1 + 2 * u) ≠ 0 := by
  have hre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  rcases lt_or_ge (1 + 2 * u).re 1 with h | h
  · have hne : 1 + 2 * u ≠ 1 := fun he => by rw [he, one_re] at h; exact lt_irrefl _ h
    have hpos : 0 < (1 + 2 * u).re := by rw [hre]; linarith
    rw [Ne, xi_eq_zero_iff hpos hne]
    intro h0
    have := hz _ h0 hpos
    rw [hre] at this
    linarith
  · exact xi_ne_zero_of_one_le_re h

include hσ in
/-- **The spectral integrand decays on the zero-free strip.** On `-σ ≤ Re u ≤ 0` the amplitude times
the Eisenstein function is `O(1/(1+Im² u))`: polynomial growth of `E` from the three-circles bound for
`1/ζ`, beaten by the rapid amplitude; a compact box near the real axis. -/
theorem exists_amplitude_eisenstein_le (h : CompactPulse) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖pulseAmplitude h (-I * u) * normalizedEisenstein u x Y‖ ≤ B / (1 + u.im ^ 2) := by
  set Θ : ℝ := 1 - 2 * δ with hΘ
  have hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz' h0 => by
    have := hz z h0 (by linarith)
    linarith
  obtain ⟨κ, hκ, hζ⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree (Θ := Θ) (by linarith)
    (by linarith) hzf (δ := 2 * (δ - σ)) (by linarith) (by linarith) (ε := 1) one_pos
  have hinv : ∀ u : ℂ, -σ ≤ u.re → 3 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ 2 / κ * (1 + |u.im|) ^ 1 := by
    intro u h1 h3
    have him : |(1 + 2 * u).im| = 2 * |u.im| := by
      have : (1 + 2 * u).im = 2 * u.im := by simp
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs1 : Θ + 2 * (δ - σ) ≤ (1 + 2 * u).re := by simp; linarith
    have hs2 : 6 ≤ |(1 + 2 * u).im| := by rw [him]; linarith
    have hb := hζ _ hs1 hs2
    rw [Real.rpow_neg_one, him] at hb
    have hζpos : 0 < ‖riemannZeta (1 + 2 * u)‖ := lt_of_lt_of_le (by positivity) hb
    rw [norm_inv, inv_le_comm₀ hζpos (by positivity)]
    calc (2 / κ * (1 + |u.im|) ^ 1)⁻¹ = κ * (2 + 2 * |u.im|)⁻¹ := by
          field_simp
      _ ≤ ‖riemannZeta (1 + 2 * u)‖ := hb
  obtain ⟨C₁, M₁, hC₁, hjet⟩ := exists_jets_le_of_zeta (Y₀ := Y) (A := σ) (c := 0) hY hσ.le le_rfl
    (K := 2 / κ) (N := 1) (by positivity)
  obtain ⟨C₂, hC₂, hrap⟩ := h.rapidAmplitude.decay σ (M₁ + 2)
  have hYw : Y ∈ Icc (Y / 2) (2 * Y) := ⟨by linarith, by linarith⟩
  have hlarge : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 → 3 ≤ |u.im| →
      ‖pulseAmplitude h (-I * u) * normalizedEisenstein u x Y‖ ≤ C₁ * C₂ / (1 + u.im ^ 2) := by
    intro u h1 h2 h3
    have hE := (hjet u x Y h1 h2 (by linarith) hYw (hinv u h1 h3)).1
    have hw1 : (-I * u).re = u.im := by simp
    have hw2 : (-I * u).im = -u.re := by simp
    have ha := hrap (-I * u) (by rw [hw2, abs_neg, abs_le]; constructor <;> linarith)
    rw [hw1] at ha
    have ht : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
    rw [le_div_iff₀ (by positivity), norm_mul]
    calc ‖pulseAmplitude h (-I * u)‖ * ‖normalizedEisenstein u x Y‖ * (1 + u.im ^ 2)
        ≤ ‖pulseAmplitude h (-I * u)‖ * (C₁ * (1 + |u.im|) ^ M₁) * (1 + |u.im|) ^ 2 := by
          gcongr
      _ = C₁ * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ (M₁ + 2)) := by ring
      _ ≤ C₁ * C₂ := mul_le_mul_of_nonneg_left ha hC₁
  set K : Set ℂ := Icc (-σ) 0 ×ℂ Icc (-3) 3 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun u => pulseAmplitude h (-I * u) * normalizedEisenstein u x Y) K := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have h1 : DifferentiableAt ℂ (fun u : ℂ => pulseAmplitude h (-I * u)) u :=
      (h.differentiable_amplitude _).comp u (by fun_prop)
    have h2 := differentiableAt_normalizedEisenstein
      (xi_ne_zero_of_zeroFree hδ hσδ hz hu'.1.1) (by linarith [hu'.1.2]) x hY
    exact (h1.mul h2).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max (10 * max B₀ 0) (C₁ * C₂), by positivity, fun u h1 h2 => ?_⟩
  by_cases h3 : 3 ≤ |u.im|
  · exact (hlarge u h1 h2 h3).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  · have h3' := abs_le.1 (not_le.1 h3).le
    have hb := hB₀ u (Complex.mem_reProdIm.2 ⟨⟨h1, h2⟩, h3'⟩)
    have hsq : u.im ^ 2 ≤ 9 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc ‖pulseAmplitude h (-I * u) * normalizedEisenstein u x Y‖ * (1 + u.im ^ 2)
        ≤ max B₀ 0 * 10 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
          (le_max_right _ _)
      _ ≤ max (10 * max B₀ 0) (C₁ * C₂) := by linarith [le_max_left (10 * max B₀ 0) (C₁ * C₂)]

include hσ in
/-- **A zero-free strip is a ringdown rate.** If every zero with `Re ρ > 0` has `Re ρ ≤ 1 - 2δ`, then
for `0 < σ < δ` the field of every pulse decays like `e^{-στ}`: the spectral line moves to `Re u = -σ`. -/
theorem pulseField_decay_of_zeroFree (h : CompactPulse) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ‖pulseField h τ x Y‖ ≤ C * Real.exp (-σ * τ) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_eisenstein_le hδ hσ hσδ hz h x hY
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * normalizedEisenstein u x Y *
    Complex.exp (u * τ) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → -σ ≤ s.re ∧ s.re ≤ 0 := by
    intro s hs
    rw [uIcc_of_ge (by linarith)] at hs
    exact hs
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have ha : DifferentiableAt ℂ (fun u : ℂ => pulseAmplitude h (-I * u)) s :=
      (h.differentiable_amplitude _).comp s (by fun_prop)
    have hE := differentiableAt_normalizedEisenstein (xi_ne_zero_of_zeroFree hδ hσδ hz h1)
      (by linarith) x hY
    exact (ha.mul hE).mul (by fun_prop)
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → ‖Φ s‖ ≤ B / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have he : ‖Complex.exp (s * τ)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (s * (τ : ℂ)).re = s.re * τ := by simp
      rw [this]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg h2 hτ)
    simp only [hΦ]
    rw [norm_mul]
    calc ‖pulseAmplitude h (-I * s) * normalizedEisenstein s x Y‖ * ‖Complex.exp (s * τ)‖
        ≤ B / (1 + s.im ^ 2) * 1 :=
          mul_le_mul (hB s h1 h2) he (norm_nonneg _) (by positivity)
      _ = B / (1 + s.im ^ 2) := mul_one _
  have hshift := integral_vertical_line_shift_of_decay hd hbΦ
  have hpk : pulseField h τ x Y = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + t * I) := by
    rw [pulseField_eq_packet h τ x hY, pulsePacket]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hΦ]
    have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
    rw [e, show -I * ((t : ℂ) * I) = t by linear_combination (-(t : ℂ)) * I_sq]
    congr 2
    ring
  rw [hpk, hshift]
  have hpt : ∀ t : ℝ, ‖Φ (((-σ : ℝ) : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) := by
    intro t
    have hre : (((-σ : ℝ) : ℂ) + t * I).re = -σ := by simp
    have him : (((-σ : ℝ) : ℂ) + t * I).im = t := by simp
    simp only [hΦ]
    rw [norm_mul, Complex.norm_exp]
    have : ((((-σ : ℝ) : ℂ) + t * I) * (τ : ℂ)).re = -σ * τ := by simp
    rw [this]
    have hb := hB _ (by rw [hre]) (by rw [hre]; linarith)
    rw [him] at hb
    rw [div_eq_mul_inv] at hb
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hint : Integrable fun t : ℝ => B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) :=
    (integrable_inv_one_add_sq.const_mul B).mul_const _
  calc ‖∫ t : ℝ, Φ (((-σ : ℝ) : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp (-σ * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

end ZeroFree

/-! ### The ringdown rate -/

/-- **The ringdown rate of a pulse is the zero-free strip.** For `0 < δ ≤ 1/4`, every zero of `ζ` with
`Re ρ > 0` has `Re ρ ≤ 1 - 2δ` iff the field of every compact pulse, with its mean growth removed,
decays like `e^{-(δ-ε)τ}` at every point of the horizon, for every `ε > 0`. -/
theorem zeroFreeStrip_iff_pulse_ringdown {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ) ↔
      ∀ ε : ℝ, 0 < ε → ∀ (h : CompactPulse) (x Y : ℝ), 0 < Y → ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖pulseField h τ x Y‖ ≤ C * Real.exp (-(δ - ε) * τ) := by
  constructor
  · intro hz ε hε h x Y hY
    have hm0 : 0 < min ε (δ / 2) := lt_min hε (by linarith)
    have hm1 : min ε (δ / 2) ≤ δ / 2 := min_le_right _ _
    have hm2 : min ε (δ / 2) ≤ ε := min_le_left _ _
    obtain ⟨C, hC, hbd⟩ := pulseField_decay_of_zeroFree (σ := δ - min ε (δ / 2)) hδ
      (by linarith) (by linarith) hz h x hY
    refine ⟨C, fun τ hτ => (hbd τ hτ).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)⟩
    nlinarith
  · intro hr ρ hρ hρ0
    by_contra hlt
    push Not at hlt
    have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ
    set ε : ℝ := (ρ.re - (1 - 2 * δ)) / 4 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hεδ : ε < δ := by rw [hε]; linarith
    have := re_le_of_pulse_ringdown (δ := δ - ε) (by linarith)
      (fun h x => hr ε hε0 h x 1 one_pos) hρ hρ0
    linarith

/-- **RH is the quarter ringdown rate of every pulse.** -/
theorem riemannHypothesis_iff_pulse_ringdown :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ (h : CompactPulse) (x Y : ℝ), 0 < Y → ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖pulseField h τ x Y‖ ≤ C * Real.exp (-(1 / 4 - ε) * τ) := by
  rw [← zeroFreeStrip_iff_pulse_ringdown (by norm_num) le_rfl]
  constructor
  · intro hRH ρ hρ hρ0
    have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ
    have hne : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
    have htriv : ¬∃ n : ℕ, ρ = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at hρ0
      have := n.cast_nonneg (α := ℝ)
      linarith
    have := hRH ρ hρ htriv hne
    linarith
  · intro hz
    by_contra hRH
    obtain ⟨ρ, hρ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    have := hz ρ hρ (by linarith)
    linarith

end RingdownRate

end GaloisForLFunctions.BlackHoleRingdown
