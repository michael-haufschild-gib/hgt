import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinFunctionOnContours
import GaloisForLFunctions.BlackHoleRingdown.TheReflectedSignalIsTheEchoTrain
import GaloisForLFunctions.RHTower.EisensteinTruncatedRowSum

/-!
# The spectrum of the image field

Inserting the Fourier inversion of the pulse in each row and summing gives

`Π_h(τ, z) = ∫ a(-iu) e^{uτ} E(u; z) dy`,   `u = c + iy`, `c > ½`,

because the row sum is the Eisenstein series. Moving the line to `Re u = 0` crosses the pole of `E` at `u = ½`,
with residue `(3/π) a(-i/2) e^{τ/2}`. Hence

`Π_h(τ, z) = 𝓕_h(τ, z) + 6 a(-i/2) e^{τ/2}`,   `𝓕_h(τ, z) = ∫ a(ξ) E(iξ; z) e^{iξτ} dξ`.

So the elementary sum over images is a spectral superposition of Eisenstein functions plus a mean growth. In
particular `𝓕_h` is a smooth, invariant, exact solution of the wave equation for every compact pulse.
-/

open Complex MeasureTheory Set Filter Topology EisensteinSeries
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The row sum -/

theorem normalizedEisenstein_eq_rowSum {u : ℂ} (hu : 1 / 2 < u.re) (him : u.im ≠ 0) (z : ℍ) :
    normalizedEisenstein u z.re z.im = (1 / 2 : ℂ) * rowSum (1 / 2 + u) z := by
  have hre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  have h0 : xi (1 + 2 * u) ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hre]; linarith)
  have him1 : (1 + 2 * u).im ≠ 0 := by simpa using him
  have hA : msA u ≠ 0 := by
    intro h
    have hx := xi_eq_reflectedCompletedLambda him1
    rw [show reflectedCompletedLambda (1 + 2 * u) = msA u from rfl, h, mul_zero] at hx
    exact h0 hx
  rw [normalizedEisenstein_eq_lineModel_div him h0, lineModel_eq_cuspLeg]
  have hline : d4BMCompletedEisensteinCuspLeg .scalar u z.re z.im = eisensteinLineModel u z := rfl
  rw [hline, eisensteinLineModel_eq_rowSum hu, show reflectedCompletedLambda (1 + 2 * u) = msA u from rfl,
    mul_div_cancel_left₀ _ hA]

theorem cpow_half_add_eq {y : ℝ} (hy : 0 < y) (u : ℂ) :
    (y : ℂ) ^ (1 / 2 + u) = ((Real.sqrt y : ℝ) : ℂ) * Complex.exp (u * (Real.log y : ℂ)) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_add _ _ hyC]
  congr 1
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
    norm_num
  · rw [Complex.cpow_def_of_ne_zero hyC, ← Complex.ofReal_log hy.le, mul_comm]

/-- The line parameter. -/
def linePoint (c y : ℝ) : ℂ := (c : ℂ) + (y : ℂ) * I

theorem linePoint_re (c y : ℝ) : (linePoint c y).re = c := by simp [linePoint]

theorem linePoint_im (c y : ℝ) : (linePoint c y).im = y := by simp [linePoint]

/-- The plane wave as a line integral. -/
theorem pulseF_eq_integral (h : CompactPulse) (c τ : ℝ) {y : ℝ} (hy : 0 < y) :
    pulseF h τ y = ∫ t : ℝ, pulseAmplitude h (-I * linePoint c t) *
      Complex.exp (linePoint c t * (τ : ℂ)) * (y : ℂ) ^ (1 / 2 + linePoint c t) := by
  rw [pulseF, h.eq_integral_amplitude_line c (τ + Real.log y), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [linePoint]
  rw [cpow_half_add_eq hy]
  have he : Complex.exp (((c : ℂ) + (t : ℂ) * I) * ((τ + Real.log y : ℝ) : ℂ)) =
      Complex.exp (((c : ℂ) + (t : ℂ) * I) * (τ : ℂ)) *
        Complex.exp (((c : ℂ) + (t : ℂ) * I) * (Real.log y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The time amplitude on a line. -/
def lineAmplitude (h : ℝ → ℂ) (c τ t : ℝ) : ℂ :=
  pulseAmplitude h (-I * linePoint c t) * Complex.exp (linePoint c t * (τ : ℂ))

theorem integrable_lineAmplitude (h : CompactPulse) (c τ : ℝ) :
    Integrable (lineAmplitude h c τ) := by
  have hint := h.integrable_amplitude_line c
  have harg : ∀ t : ℝ, -I * linePoint c t = (t : ℂ) - c * I := fun t => by
    rw [linePoint]
    linear_combination (-(t : ℂ)) * I_sq
  have hcont : Continuous (lineAmplitude h c τ) := by
    unfold lineAmplitude
    exact (h.differentiable_amplitude.continuous.comp (by unfold linePoint; fun_prop)).mul
      (by unfold linePoint; fun_prop)
  refine (hint.norm.mul_const (Real.exp (c * τ))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [lineAmplitude, norm_mul, Complex.norm_exp, harg]
  have hre : (linePoint c t * (τ : ℂ)).re = c * τ := by simp [linePoint]
  rw [hre]

/-- **The image field as a line integral.** -/
theorem imageField_eq_line (h : CompactPulse) {c : ℝ} (hc : 1 / 2 < c) (τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    imageField h τ x Y =
      ∫ t : ℝ, lineAmplitude h c τ t * normalizedEisenstein (linePoint c t) x Y := by
  set z := chartPoint x hY with hz
  have hzre : z.re = x := rfl
  have hzim : z.im = Y := rfl
  have hrow : ∀ p : gammaSet 1 1 0, rowHgt (rowC p) (rowD p) x Y = rowHeight p z := by
    intro p
    rw [rowHeight, ← rowHgt_eq_im, hzre, hzim]
  set F : gammaSet 1 1 0 → ℝ → ℂ := fun p t =>
    lineAmplitude h c τ t * (rowHeight p z : ℂ) ^ (1 / 2 + linePoint c t) with hF
  have hnormpow : ∀ (p : gammaSet 1 1 0) (t : ℝ), ‖(rowHeight p z : ℂ) ^ (1 / 2 + linePoint c t)‖ =
      rowHeight p z ^ (1 / 2 + c) := by
    intro p t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (rowHeight_pos p z)]
    congr 1
    simp [linePoint]
  have hA := integrable_lineAmplitude h c τ
  have hFint : ∀ p, Integrable (F p) := by
    intro p
    have hb : Continuous fun t : ℝ => (rowHeight p z : ℂ) ^ (1 / 2 + linePoint c t) := by
      refine Continuous.const_cpow (by unfold linePoint; fun_prop) (Or.inl ?_)
      exact_mod_cast (rowHeight_pos p z).ne'
    refine (hA.norm.mul_const (rowHeight p z ^ (1 / 2 + c))).mono'
      (hA.aestronglyMeasurable.mul hb.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [hF]
    simp only
    rw [norm_mul, hnormpow]
  have hsum0 : Summable fun p : gammaSet 1 1 0 => (rowHeight p z : ℂ) ^ (((1 / 2 + c : ℝ) : ℂ)) :=
    summable_rowHeight_cpow (by simp; linarith) z
  have hsumN : Summable fun p : gammaSet 1 1 0 => rowHeight p z ^ (1 / 2 + c) := by
    refine hsum0.norm.congr fun p => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (rowHeight_pos p z), Complex.ofReal_re]
  have hsumI : Summable fun p => ∫ t, ‖F p t‖ := by
    have hval : ∀ p, ∫ t, ‖F p t‖ = (∫ t, ‖lineAmplitude h c τ t‖) * rowHeight p z ^ (1 / 2 + c) := by
      intro p
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hF]
      rw [norm_mul, hnormpow]
    simp_rw [hval]
    exact hsumN.mul_left _
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsumI
  have hterm : ∀ p : gammaSet 1 1 0, ∫ t, F p t = imageTerm h (rowC p) (rowD p) τ x Y := by
    intro p
    rw [imageTerm, hrow, pulseF_eq_integral h c τ (rowHeight_pos p z)]
    rfl
  simp_rw [hterm] at hHS
  rw [imageField, hHS.tsum_eq, ← integral_const_mul]
  have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
    have : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (by simp)
    exact this
  refine integral_congr_ae (hae.mono fun t ht => ?_)
  simp only [hF]
  have him : (linePoint c t).im ≠ 0 := by rwa [linePoint_im]
  have hE := normalizedEisenstein_eq_rowSum (u := linePoint c t) (by rw [linePoint_re]; exact hc) him z
  rw [hzre, hzim] at hE
  rw [hE, tsum_mul_left, rowSum]
  ring

/-! ### The contour shift -/

/-- **The shift across a simple pole at `½`.** -/
theorem integral_line_shift {f : ℂ → ℂ} {c : ℝ} (hc : 1 / 2 < c)
    (hana : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ c → s ≠ 1 / 2 → AnalyticAt ℂ f s)
    (hmero : MeromorphicAt f (1 / 2))
    (hR : Integrable fun y : ℝ => f ((c : ℂ) + (y : ℂ) * I))
    (hL : Integrable fun y : ℝ => f (((0 : ℝ) : ℂ) + (y : ℂ) * I))
    {L B : ℕ → ℝ} (hLat : Tendsto L atTop atTop) (hB : Tendsto B atTop (𝓝 0))
    (hedge : ∀ᶠ k in atTop, ∀ x ∈ Icc (0 : ℝ) c, ∀ s : ℝ, |s| = L k →
      ‖f ((x : ℂ) + (s : ℂ) * I)‖ ≤ B k) :
    (∫ y : ℝ, f ((c : ℂ) + (y : ℂ) * I)) - ∫ y : ℝ, f (((0 : ℝ) : ℂ) + (y : ℂ) * I) =
      2 * Real.pi * laurentCoeff f (1 / 2) (-1) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hrect : ∀ᶠ k in atTop, RectangleIntegral' f ⟨0, -L k⟩ ⟨c, L k⟩ = laurentCoeff f (1 / 2) (-1) := by
    filter_upwards [hLat.eventually_gt_atTop 0] with k hk
    have hre1 : (0 : ℝ) ≤ c := hc0
    have him1 : -L k ≤ L k := by linarith
    have h := rectangleIntegral'_eq_sum_laurentCoeff (f := f) (z := ⟨0, -L k⟩) (w := ⟨c, L k⟩)
      (P := {1 / 2}) hre1 him1 ?_ ?_ ?_
    · simpa using h
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
      simp only
      rw [uIoo_of_le hre1, uIoo_of_le him1]
      constructor
      · constructor
        · norm_num
        · simpa using hc
      · constructor
        · simpa using hk
        · simpa using hk
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact hmero
    · intro s hs hsP
      rw [Rectangle, Complex.mem_reProdIm] at hs
      simp only at hs
      rw [uIcc_of_le hre1] at hs
      refine hana s hs.1.1 hs.1.2 fun he => hsP ?_
      rw [Finset.mem_singleton]
      exact he
  have hbound : Tendsto (fun k => B k * c) atTop (𝓝 0) := by
    simpa using hB.mul_const c
  have hEdge : ∀ s : ℝ, s = 1 ∨ s = -1 → Tendsto
      (fun k => HIntegral f 0 c (s * L k)) atTop (𝓝 0) := by
    intro s hs
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hedge, hLat.eventually_gt_atTop 0] with k hk hLk
    rw [HIntegral]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := c)
      (f := fun x : ℝ => f ((x : ℂ) + ((s * L k : ℝ) : ℂ) * I)) (C := B k) (fun x hx => by
        rw [uIoc_of_le hc0] at hx
        refine hk x ⟨hx.1.le, hx.2⟩ (s * L k) ?_
        rcases hs with rfl | rfl
        · rw [one_mul, abs_of_pos hLk]
        · rw [neg_one_mul, abs_neg, abs_of_pos hLk])
    refine hb.trans (le_of_eq ?_)
    rw [sub_zero, abs_of_nonneg hc0]
  have hBot := hEdge (-1) (Or.inr rfl)
  have hTop := hEdge 1 (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hBot hTop
  have hlow : Tendsto (fun k => -L k) atTop atBot := tendsto_neg_atTop_atBot.comp hLat
  have hRl := intervalIntegral_tendsto_integral hR hlow hLat
  have hLl := intervalIntegral_tendsto_integral hL hlow hLat
  have hmain := ((hBot.sub hTop).add (hRl.const_smul I)).sub (hLl.const_smul I)
  have hscaled := hmain.const_smul ((1 : ℂ) / (2 * Real.pi * I))
  have hlimit : ((1 : ℂ) / (2 * Real.pi * I)) •
      ((0 - 0 + I • ∫ y : ℝ, f ((c : ℂ) + (y : ℂ) * I)) -
        I • ∫ y : ℝ, f (((0 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (2 * Real.pi : ℂ)⁻¹ * ((∫ y : ℝ, f ((c : ℂ) + (y : ℂ) * I)) -
        ∫ y : ℝ, f (((0 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hlimit] at hscaled
  have hconst : Tendsto (fun k => RectangleIntegral' f ⟨0, -L k⟩ ⟨c, L k⟩) atTop
      (𝓝 (laurentCoeff f (1 / 2) (-1))) :=
    tendsto_const_nhds.congr' (hrect.mono fun k hk => hk.symm)
  have huniq := tendsto_nhds_unique (hscaled.congr fun k => ?_) hconst
  · have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [← huniq, mul_inv_cancel_left₀ hpi]
  · simp only [RectangleIntegral', RectangleIntegral, VIntegral]

/-- The numerator of `(2u - 1) E(u)`, regular at `u = ½`. -/
def rightNumerator (x Y : ℝ) (u : ℂ) : ℂ :=
  (2 * u - 1) * (Y : ℂ) ^ (1 / 2 + u) +
    (1 + 2 * u) * (xi (2 * u) / xi (1 + 2 * u)) * (Y : ℂ) ^ (1 / 2 - u) +
    (2 * u - 1) * (tailWeight u * eisTail u x Y)

theorem rightNumerator_div {u : ℂ} (hu : 2 * u - 1 ≠ 0) (x Y : ℝ) :
    rightNumerator x Y u / (2 * u - 1) = normalizedEisenstein u x Y := by
  simp only [rightNumerator, normalizedEisenstein, scatteringPhase]
  field_simp

theorem analyticAt_rightNumerator (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : 0 ≤ u.re) :
    AnalyticAt ℂ (rightNumerator x Y) u := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : AnalyticAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 + v)) u :=
    ((by fun_prop : Differentiable ℂ fun v : ℂ => 1 / 2 + v).const_cpow (Or.inl hYC)).analyticAt u
  have h2 : AnalyticAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 - v)) u :=
    ((by fun_prop : Differentiable ℂ fun v : ℂ => 1 / 2 - v).const_cpow (Or.inl hYC)).analyticAt u
  have hx1 : AnalyticAt ℂ (fun v : ℂ => xi (1 + 2 * v)) u := differentiable_xi_shift.analyticAt u
  have hx2 : AnalyticAt ℂ (fun v : ℂ => xi (2 * v)) u :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).analyticAt u
  have hne := xi_shift_ne_zero hu
  have hτ : AnalyticAt ℂ (fun v : ℂ => eisTail v x Y) u := by
    have : Differentiable ℂ fun v : ℂ => eisTail v x Y := fun v => differentiableAt_eisTail x hY v
    exact this.analyticAt u
  have hw : AnalyticAt ℂ (fun v : ℂ => tailWeight v) u := by
    unfold tailWeight
    exact (by fun_prop : AnalyticAt ℂ (fun v : ℂ => (1 + 2 * v) * (2 * v)) u).div hx1 hne
  have ha : AnalyticAt ℂ (fun v : ℂ => 2 * v - 1) u := by fun_prop
  have hb : AnalyticAt ℂ (fun v : ℂ => 1 + 2 * v) u := by fun_prop
  exact ((ha.mul h1).add ((hb.mul (hx2.div hx1 hne)).mul h2)).add (ha.mul (hw.mul hτ))

/-- The integrand of the shift. -/
def spectralIntegrand (h : ℝ → ℂ) (τ x Y : ℝ) (u : ℂ) : ℂ :=
  pulseAmplitude h (-I * u) * Complex.exp (u * (τ : ℂ)) * rightNumerator x Y u / (2 * u - 1)

theorem spectralIntegrand_eq (h : ℝ → ℂ) (τ x Y : ℝ) {u : ℂ} (hu : 2 * u - 1 ≠ 0) :
    spectralIntegrand h τ x Y u =
      pulseAmplitude h (-I * u) * Complex.exp (u * (τ : ℂ)) * normalizedEisenstein u x Y := by
  rw [spectralIntegrand, ← rightNumerator_div hu]
  ring

theorem two_mul_line_sub_one_ne {c : ℝ} (hc : c ≠ 1 / 2) (y : ℝ) : 2 * linePoint c y - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [linePoint] at this
  exact hc (by linarith)

section Shift

variable (h : CompactPulse) (τ x : ℝ) {Y : ℝ} (hY : 0 < Y)

include hY

theorem analyticAt_spectralIntegrand {s : ℂ} (hs : 0 ≤ s.re) (hne : s ≠ 1 / 2) :
    AnalyticAt ℂ (spectralIntegrand h τ x Y) s := by
  have hd : (2 : ℂ) * s - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  have h1 : AnalyticAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) s :=
    (h.differentiable_amplitude.comp (by fun_prop : Differentiable ℂ fun v : ℂ => -I * v)).analyticAt s
  have h2 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (τ : ℂ))) s := by fun_prop
  exact ((h1.mul h2).mul (analyticAt_rightNumerator x hY hs)).div (by fun_prop) hd

/-- **The residue at `u = ½`.** -/
theorem laurentCoeff_spectralIntegrand :
    laurentCoeff (spectralIntegrand h τ x Y) (1 / 2) (-1) =
      pulseAmplitude h (-I * (1 / 2)) * Complex.exp ((τ : ℂ) / 2) * (3 / (Real.pi : ℂ)) := by
  have hre : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re := by norm_num
  have h1 : AnalyticAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) (1 / 2) :=
    (h.differentiable_amplitude.comp (by fun_prop : Differentiable ℂ fun v : ℂ => -I * v)).analyticAt _
  have h2 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (τ : ℂ))) (1 / 2) := by fun_prop
  have hP : AnalyticAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v) * Complex.exp (v * (τ : ℂ)) *
      rightNumerator x Y v) (1 / 2) := (h1.mul h2).mul (analyticAt_rightNumerator x hY hre)
  have hD : Differentiable ℂ fun w : ℂ => 2 * w - 1 := by fun_prop
  have hder : deriv (fun w : ℂ => 2 * w - 1) (1 / 2) = 2 := by
    have hd : HasDerivAt (fun w : ℂ => 2 * w - 1) 2 (1 / 2) := by
      simpa using ((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2).sub_const 1
    exact hd.deriv
  have heq : laurentCoeff (spectralIntegrand h τ x Y) (1 / 2) (-1) =
      laurentCoeff (fun u => (fun v : ℂ => pulseAmplitude h (-I * v) *
        Complex.exp (v * (τ : ℂ)) * rightNumerator x Y v) u / (2 * u - 1)) (1 / 2) (-1) := rfl
  rw [heq, laurentCoeff_div_of_simple_zero hP hD (by norm_num) (by rw [hder]; norm_num), hder]
  have e0 : (2 : ℂ) * (1 / 2) - 1 = 0 := by norm_num
  have e1 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
  have e2 : (1 : ℂ) + 1 = 2 := by norm_num
  have e3 : (1 / 2 : ℂ) - 1 / 2 = 0 := by norm_num
  have hval : rightNumerator x Y (1 / 2) = 2 * (3 / (Real.pi : ℂ)) := by
    rw [rightNumerator, e0, e1, e2, xi_one_div_xi_two, e3, Complex.cpow_zero]
    ring
  rw [hval, show (1 / 2 : ℂ) * (τ : ℂ) = (τ : ℂ) / 2 by ring]
  ring

theorem meromorphicAt_spectralIntegrand :
    MeromorphicAt (spectralIntegrand h τ x Y) (1 / 2) := by
  have hre : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re := by norm_num
  have h1 : AnalyticAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) (1 / 2) :=
    (h.differentiable_amplitude.comp (by fun_prop : Differentiable ℂ fun v : ℂ => -I * v)).analyticAt _
  have h2 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (τ : ℂ))) (1 / 2) := by fun_prop
  exact ((h1.mul h2).mul (analyticAt_rightNumerator x hY hre)).meromorphicAt.div
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 * w - 1) (1 / 2)).meromorphicAt

omit hY in
/-- The integrand against a polynomial bound for `E`. -/
theorem norm_spectralIntegrand_le {u : ℂ} {B : ℝ} (hu : 2 * u - 1 ≠ 0) (hB : |u.re| ≤ B) {M : ℕ}
    {Ca K : ℝ} (hCa : ∀ v : ℂ, |v.re| ≤ B →
      ‖pulseAmplitude h (-I * v)‖ * (1 + |v.im|) ^ M ≤ Ca * ((1 + |v.im|) ^ 2)⁻¹)
    (hE : ‖normalizedEisenstein u x Y‖ ≤ K * (1 + |u.im|) ^ M) (hK : 0 ≤ K) :
    ‖spectralIntegrand h τ x Y u‖ ≤
      Real.exp (B * |τ|) * K * Ca * ((1 + |u.im|) ^ 2)⁻¹ := by
  rw [spectralIntegrand_eq _ _ _ _ hu, norm_mul, norm_mul, Complex.norm_exp]
  have hre : (u * (τ : ℂ)).re = u.re * τ := by simp
  rw [hre]
  have hexp : Real.exp (u.re * τ) ≤ Real.exp (B * |τ|) := by
    refine Real.exp_le_exp.mpr ?_
    calc u.re * τ ≤ |u.re * τ| := le_abs_self _
      _ = |u.re| * |τ| := abs_mul _ _
      _ ≤ B * |τ| := mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have ha := hCa u hB
  calc ‖pulseAmplitude h (-I * u)‖ * Real.exp (u.re * τ) * ‖normalizedEisenstein u x Y‖
      ≤ ‖pulseAmplitude h (-I * u)‖ * Real.exp (B * |τ|) * (K * (1 + |u.im|) ^ M) := by
        gcongr
    _ = Real.exp (B * |τ|) * K * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ M) := by ring
    _ ≤ Real.exp (B * |τ|) * K * (Ca * ((1 + |u.im|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by ring

/-- **The shift of the image field.** -/
theorem integral_spectralIntegrand_shift :
    (∫ y : ℝ, spectralIntegrand h τ x Y (((1 : ℝ) : ℂ) + (y : ℂ) * I)) -
        ∫ y : ℝ, spectralIntegrand h τ x Y (((0 : ℝ) : ℂ) + (y : ℂ) * I) =
      2 * Real.pi * laurentCoeff (spectralIntegrand h τ x Y) (1 / 2) (-1) := by
  have hrapid := h.rapidAmplitude
  obtain ⟨C₀, M₀, hC₀, hline⟩ := exists_eisenstein_jets_line_le_poly hY
  obtain ⟨C₁, M₁, hC₁, hright⟩ := exists_jets_right_line (c := 1) hY (by norm_num)
  obtain ⟨C₂, M₂, k₀, hC₂, hgood⟩ := exists_jets_goodHeight (A := 0) (c := 1) hY le_rfl (by norm_num)
  obtain ⟨Ca₀, hCa₀, ha₀⟩ := hrapid.exists_rotated_le 1 M₀
  obtain ⟨Ca₁, hCa₁, ha₁⟩ := hrapid.exists_rotated_le 1 M₁
  obtain ⟨Ca₂, hCa₂, ha₂⟩ := hrapid.exists_rotated_le 1 M₂
  have hYm := mem_window_self hY
  have hcontLine : ∀ c : ℝ, 0 ≤ c → c ≠ 1 / 2 →
      Continuous fun y : ℝ => spectralIntegrand h τ x Y ((c : ℂ) + (y : ℂ) * I) := by
    intro c hc0 hc
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : ((c : ℂ) + (y : ℂ) * I) ≠ 1 / 2 := fun he => hc (by
      have := congrArg Complex.re he
      simpa using this)
    have han := analyticAt_spectralIntegrand h τ x hY (s := (c : ℂ) + (y : ℂ) * I) (by simpa using hc0)
      hne
    exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) han.continuousAt (by fun_prop)
  have hL : Integrable fun y : ℝ => spectralIntegrand h τ x Y (((0 : ℝ) : ℂ) + (y : ℂ) * I) := by
    refine integrable_of_continuous_of_inv_sq_tail (hcontLine 0 le_rfl (by norm_num)) (R := 0)
      (C := Real.exp (1 * |τ|) * C₀ * Ca₀) fun y _ => ?_
    have heq : ((0 : ℝ) : ℂ) + (y : ℂ) * I = (y : ℂ) * I := by simp
    have hd := two_mul_line_sub_one_ne (c := 0) (by norm_num) y
    rw [linePoint] at hd
    have hb := norm_spectralIntegrand_le h τ x (u := ((0 : ℝ) : ℂ) + (y : ℂ) * I) (B := 1) (M := M₀)
      (Ca := Ca₀) (K := C₀) hd (by simp) ha₀ (by
        rw [heq]
        have him : ((y : ℂ) * I).im = y := by simp
        rw [him]
        exact (hline y x Y hYm).1) hC₀
    have him : (((0 : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    rwa [him] at hb
  have hR : Integrable fun y : ℝ => spectralIntegrand h τ x Y (((1 : ℝ) : ℂ) + (y : ℂ) * I) := by
    refine integrable_of_continuous_of_inv_sq_tail (hcontLine 1 (by norm_num) (by norm_num)) (R := 1)
      (C := Real.exp (1 * |τ|) * C₁ * Ca₁) fun y hy => ?_
    have hd := two_mul_line_sub_one_ne (c := 1) (by norm_num) y
    rw [linePoint] at hd
    have him : (((1 : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
    have hb := norm_spectralIntegrand_le h τ x (u := ((1 : ℝ) : ℂ) + (y : ℂ) * I) (B := 1) (M := M₁)
      (Ca := Ca₁) (K := C₁) hd (by simp) ha₁ (by
        rw [him]
        exact (hright y x Y hy hYm).1) hC₁
    rwa [him] at hb
  have hLat : Tendsto (fun k => goodHeight k / 2) atTop atTop :=
    tendsto_goodHeight.atTop_div_const (by norm_num)
  have hB : Tendsto (fun k => Real.exp (1 * |τ|) * C₂ * Ca₂ * ((1 + goodHeight k / 2) ^ 2)⁻¹)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => 1 + goodHeight k / 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ hLat
    have h2 : Tendsto (fun k => (1 + goodHeight k / 2) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
    simpa using (tendsto_inv_atTop_zero.comp h2).const_mul (Real.exp (1 * |τ|) * C₂ * Ca₂)
  refine integral_line_shift (c := 1) (by norm_num)
    (fun s hs _ hne => analyticAt_spectralIntegrand h τ x hY hs hne)
    (meromorphicAt_spectralIntegrand h τ x hY) hR hL hLat hB ?_
  filter_upwards [eventually_ge_atTop k₀, hLat.eventually_ge_atTop 1] with k hk hLk q hq s hs
  have him : ((q : ℂ) + (s : ℂ) * I).im = s := by simp
  have hre : ((q : ℂ) + (s : ℂ) * I).re = q := by simp
  have hd : 2 * ((q : ℂ) + (s : ℂ) * I) - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    rw [this, abs_zero] at hs
    linarith
  have hb := norm_spectralIntegrand_le h τ x (u := (q : ℂ) + (s : ℂ) * I) (B := 1) (M := M₂)
    (Ca := Ca₂) (K := C₂) hd (by rw [hre, abs_of_nonneg hq.1]; exact hq.2) ha₂ (by
      have hg := hgood k hk ((q : ℂ) + (s : ℂ) * I) x Y (by rw [hre]; simpa using hq.1)
        (by rw [hre]; exact hq.2) (by rw [him]; exact hs) (by rw [him, hs]; exact hLk) hYm
      rw [him] at hg ⊢
      exact hg.1) hC₂
  rw [him, hs] at hb
  exact hb

end Shift

/-! ### The bridge -/

/-- The coefficient of the mean growth, `6 a(-i/2) = (3/π) ∫ h(S) e^{-S/2} dS`. -/
def meanCoefficient (h : ℝ → ℂ) : ℂ := 6 * pulseAmplitude h (-I * (1 / 2))

/-- The spectral packet of a pulse. -/
def pulsePacket (h : ℝ → ℂ) (τ x Y : ℝ) : ℂ :=
  ∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * normalizedEisenstein ((ξ : ℂ) * I) x Y *
    Complex.exp (I * (ξ : ℂ) * (τ : ℂ))

/-- **The image field is the spectral packet plus the mean growth.** -/
theorem imageField_eq_packet (h : CompactPulse) (τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    imageField h τ x Y = pulsePacket h τ x Y + meanCoefficient h * Complex.exp ((τ : ℂ) / 2) := by
  have hshift := integral_spectralIntegrand_shift h τ x hY
  rw [laurentCoeff_spectralIntegrand h τ x hY] at hshift
  have hright : ∫ y : ℝ, spectralIntegrand h τ x Y (((1 : ℝ) : ℂ) + (y : ℂ) * I) = imageField h τ x Y := by
    rw [imageField_eq_line h (c := 1) (by norm_num) τ x hY]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hd := two_mul_line_sub_one_ne (c := 1) (by norm_num) t
    rw [linePoint] at hd
    simp only [lineAmplitude, linePoint]
    exact spectralIntegrand_eq _ _ _ _ hd
  have hleft : ∫ y : ℝ, spectralIntegrand h τ x Y (((0 : ℝ) : ℂ) + (y : ℂ) * I) = pulsePacket h τ x Y := by
    rw [pulsePacket]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hd := two_mul_line_sub_one_ne (c := 0) (by norm_num) t
    rw [linePoint] at hd
    simp only
    rw [spectralIntegrand_eq _ _ _ _ hd]
    have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
    have harg : -I * ((t : ℂ) * I) = t := by linear_combination (-(t : ℂ)) * I_sq
    have he : Complex.exp ((t : ℂ) * I * (τ : ℂ)) = Complex.exp (I * (t : ℂ) * (τ : ℂ)) := by
      congr 1
      ring
    rw [e, harg, he]
    ring
  rw [hright, hleft] at hshift
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [sub_eq_iff_eq_add] at hshift
  rw [hshift, meanCoefficient]
  field_simp
  ring

/-- The image field with its mean growth removed. -/
def pulseField (h : ℝ → ℂ) (τ x Y : ℝ) : ℂ :=
  imageField h τ x Y - meanCoefficient h * Complex.exp ((τ : ℂ) / 2)

theorem pulseField_eq_packet (h : CompactPulse) (τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    pulseField h τ x Y = pulsePacket h τ x Y := by
  rw [pulseField, imageField_eq_packet h τ x hY]
  ring

theorem meanCoefficient_D (h : CompactPulse) : meanCoefficient h.D = (1 / 2) * meanCoefficient h := by
  rw [meanCoefficient, meanCoefficient, h.amplitude_D]
  linear_combination (-3 * pulseAmplitude h (-I * (1 / 2))) * I_sq

theorem hasDerivAt_pulseField_time (h : CompactPulse) (τ x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun s => pulseField h s x Y) (pulseField h.D τ x Y) τ := by
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) / 2)) (Complex.exp ((τ : ℂ) / 2) * (1 / 2)) τ := by
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ) / 2) (1 / 2) τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).div_const (2 : ℂ)
    exact h0.cexp
  have h1 := (hasDerivAt_imageField_time h x τ hY).sub (hexp.const_mul (meanCoefficient h))
  refine h1.congr_deriv ?_
  rw [pulseField, meanCoefficient_D]
  ring

/-- **The spectral packet of any compact pulse solves the modular wave equation.** -/
theorem isModularWave_pulseField (h : CompactPulse) : IsModularWave (pulseField h) where
  diff := fun x y hy τ => (hasDerivAt_pulseField_time h τ x hy).differentiableAt
  diff2 := fun x y hy τ => by
    have heq : (deriv fun s => pulseField h s x y) = fun s => pulseField h.D s x y :=
      funext fun s => (hasDerivAt_pulseField_time h s x hy).deriv
    rw [heq]
    exact (hasDerivAt_pulseField_time h.D τ x hy).differentiableAt
  wave := fun τ x y hy => by
    have heq : (deriv fun s => pulseField h s x y) = fun s => pulseField h.D s x y :=
      funext fun s => (hasDerivAt_pulseField_time h s x hy).deriv
    rw [heq, (hasDerivAt_pulseField_time h.D τ x hy).deriv]
    have hw := (isModularWave_imageField h).wave τ x y hy
    have hI : (deriv fun s => imageField h s x y) = fun s => imageField h.D s x y :=
      funext fun s => (hasDerivAt_imageField_time h x s hy).deriv
    rw [hI, (hasDerivAt_imageField_time h.D x τ hy).deriv] at hw
    have hsx : (deriv fun q => pulseField h τ q y) = deriv fun q => imageField h τ q y := by
      funext q
      exact deriv_sub_const _
    have hsy : (deriv fun q => pulseField h τ x q) = deriv fun q => imageField h τ x q := by
      funext q
      exact deriv_sub_const _
    rw [hsx, hsy, pulseField, pulseField, hw, meanCoefficient_D, meanCoefficient_D]
    ring

/-- **The field of a pulse is invariant.** -/
theorem pulseField_smul (h : ℝ → ℂ) (τ : ℝ) (γ : SL(2, ℤ)) (z : ℍ) :
    pulseField h τ (γ • z : ℍ).re (γ • z : ℍ).im = pulseField h τ z.re z.im := by
  rw [pulseField, pulseField, imageField_smul]

end GaloisForLFunctions.BlackHoleRingdown

end
