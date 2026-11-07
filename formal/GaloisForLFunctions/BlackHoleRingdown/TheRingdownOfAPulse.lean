import GaloisForLFunctions.BlackHoleRingdown.TheSpectrumOfTheImageField
import GaloisForLFunctions.BlackHoleRingdown.TheContourPackage
import GaloisForLFunctions.BlackHoleRingdown.TheModesOfTheRingdown
import GaloisForLFunctions.BlackHoleRingdown.TheFieldIsSmoothAcrossTheHorizon

/-!
# The ringdown of a pulse

For every compact pulse the field `𝓕_h` has the ringdown expansion: partial sums over the zeros up to the good
heights converge to `𝓕_h - R`, uniformly on each half line `τ ≥ -τ₀`, with `R = O(e^{-Aτ})` for every `A`. A
zero of multiplicity `n+1` contributes `e^{pτ}` times a polynomial of degree at most `n`. The top coefficient
is `a(-ip) N(p; x, Y)` over a nonzero factor, and every single zero is excited by some pulse.

So the image field `Π_h = 𝓕_h + 6a(-i/2) e^{τ/2}` has the exact late-time form: a mean growth, one damped mode
per zero, and a remainder below every exponential.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-- The time-free numerator `a(-iu) N(u; x, Y)`. -/
def pulseNumerator (h : ℝ → ℂ) (x Y : ℝ) (u : ℂ) : ℂ :=
  pulseAmplitude h (-I * u) * eisensteinNumerator u x Y

theorem inverseXiQuotient_pulseNumerator (h : ℝ → ℂ) (x Y : ℝ) {u : ℂ} (hu : xi (1 + 2 * u) ≠ 0) :
    inverseXiQuotient (pulseNumerator h x Y) u =
      pulseAmplitude h (-I * u) * normalizedEisenstein u x Y := by
  rw [inverseXiQuotient, pulseNumerator, normalizedEisenstein_eq_numerator_div hu]
  ring

theorem xi_ne_zero_of_re_le {u : ℂ} (hu : u.re ≤ -(1 / 2)) : xi (1 + 2 * u) ≠ 0 := fun h => by
  have := re_pos_of_xi_eq_zero h
  simp at this
  linarith

section Data

variable (h : CompactPulse) (x : ℝ) {Y : ℝ} (hY : 0 < Y)

theorem analyticAt_pulseNumerator (hY : 0 < Y) {u : ℂ} (hu : u.re ≤ 0) :
    AnalyticAt ℂ (pulseNumerator h x Y) u :=
  ((h.differentiable_amplitude.comp
    (by fun_prop : Differentiable ℂ fun v : ℂ => -I * v)).analyticAt u).mul
    (analyticAt_eisensteinNumerator x hY hu)

include hY

/-- **The contour data of a pulse.** -/
theorem contourData_pulse {A : ℝ} (hA : 1 ≤ A) : ContourData A (pulseNumerator h x Y) := by
  have hAnn : 0 ≤ A := by linarith
  have hrapid := h.rapidAmplitude
  have hYm := mem_window_self hY
  obtain ⟨C₀, M₀, hC₀, hline⟩ := exists_eisenstein_jets_line_le_poly hY
  obtain ⟨C₁, T₁, M₁, hC₁, hleft⟩ := exists_jets_left_line hY hA
  obtain ⟨C₂, M₂, k₀, hC₂, hgood⟩ := exists_jets_goodHeight (A := A) (c := 0) hY hAnn le_rfl
  obtain ⟨Ca₀, hCa₀, ha₀⟩ := hrapid.exists_rotated_le 0 M₀
  obtain ⟨Ca₁, hCa₁, ha₁⟩ := hrapid.exists_rotated_le A M₁
  obtain ⟨Ca₂, hCa₂, ha₂⟩ := hrapid.exists_rotated_le A M₂
  have hbound : ∀ {u : ℂ} {M : ℕ} {B Ca K : ℝ}, xi (1 + 2 * u) ≠ 0 → |u.re| ≤ B →
      (∀ v : ℂ, |v.re| ≤ B → ‖pulseAmplitude h (-I * v)‖ * (1 + |v.im|) ^ M ≤
        Ca * ((1 + |v.im|) ^ 2)⁻¹) →
      ‖normalizedEisenstein u x Y‖ ≤ K * (1 + |u.im|) ^ M → 0 ≤ K →
      ‖inverseXiQuotient (pulseNumerator h x Y) u‖ ≤ K * Ca * ((1 + |u.im|) ^ 2)⁻¹ := by
    intro u M B Ca K hne hu hCa hE hK
    rw [inverseXiQuotient_pulseNumerator h x Y hne, norm_mul]
    calc ‖pulseAmplitude h (-I * u)‖ * ‖normalizedEisenstein u x Y‖
        ≤ ‖pulseAmplitude h (-I * u)‖ * (K * (1 + |u.im|) ^ M) :=
          mul_le_mul_of_nonneg_left hE (norm_nonneg _)
      _ = K * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ M) := by ring
      _ ≤ K * (Ca * ((1 + |u.im|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hCa u hu) hK
      _ = _ := by ring
  refine ⟨fun u _ h2 => analyticAt_pulseNumerator h x hY h2, ?_, ?_, ?_⟩
  · have hcont : Continuous fun y : ℝ => inverseXiQuotient (pulseNumerator h x Y) ((y : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have han : AnalyticAt ℂ (inverseXiQuotient (pulseNumerator h x Y)) ((y : ℂ) * I) :=
        (analyticAt_pulseNumerator h x hY (by simp)).div (differentiable_xi_shift.analyticAt _)
          (xi_line_ne_zero y)
      exact ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) * I) han.continuousAt (by fun_prop)
    refine integrable_of_continuous_of_inv_sq_tail hcont (R := 0) (C := C₀ * Ca₀) fun y _ => ?_
    have him : ((y : ℂ) * I).im = y := by simp
    have hb := hbound (u := (y : ℂ) * I) (B := 0) (xi_line_ne_zero y) (by simp) ha₀ (by
      rw [him]
      exact (hline y x Y hYm).1) hC₀
    rwa [him] at hb
  · have hre : ∀ y : ℝ, (((-A : ℝ) : ℂ) + (y : ℂ) * I).re = -A := fun y => by simp
    have him : ∀ y : ℝ, (((-A : ℝ) : ℂ) + (y : ℂ) * I).im = y := fun y => by simp
    have hne : ∀ y : ℝ, xi (1 + 2 * (((-A : ℝ) : ℂ) + (y : ℂ) * I)) ≠ 0 := fun y =>
      xi_ne_zero_of_re_le (by rw [hre]; linarith)
    have hcont : Continuous fun y : ℝ =>
        inverseXiQuotient (pulseNumerator h x Y) (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have han : AnalyticAt ℂ (inverseXiQuotient (pulseNumerator h x Y))
          (((-A : ℝ) : ℂ) + (y : ℂ) * I) :=
        (analyticAt_pulseNumerator h x hY (by rw [hre]; linarith)).div
          (differentiable_xi_shift.analyticAt _) (hne y)
      exact ContinuousAt.comp (f := fun y : ℝ => ((-A : ℝ) : ℂ) + (y : ℂ) * I) han.continuousAt
        (by fun_prop)
    refine integrable_of_continuous_of_inv_sq_tail hcont (R := T₁) (C := C₁ * Ca₁) fun y hy => ?_
    have hb := hbound (u := ((-A : ℝ) : ℂ) + (y : ℂ) * I) (B := A) (hne y)
      (by rw [hre, abs_neg, abs_of_nonneg hAnn]) ha₁ (by
        rw [him]
        exact (hleft y x Y hy hYm).1) hC₁
    rwa [him] at hb
  · have hLat : Tendsto (fun k => goodHeight k / 2) atTop atTop :=
      tendsto_goodHeight.atTop_div_const (by norm_num)
    refine ⟨fun k => C₂ * Ca₂ * ((1 + goodHeight k / 2) ^ 2)⁻¹, ?_, ?_⟩
    · have h1 : Tendsto (fun k => 1 + goodHeight k / 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ hLat
      have h2 : Tendsto (fun k => (1 + goodHeight k / 2) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
      simpa using (tendsto_inv_atTop_zero.comp h2).const_mul (C₂ * Ca₂)
    · filter_upwards [eventually_ge_atTop k₀, hLat.eventually_ge_atTop 1] with k hk hLk u h1 h2 him
      have hne : xi (1 + 2 * u) ≠ 0 := by
        refine xi_ne_zero_of_abs_im_goodHeight k ?_
        have h3 : (1 + 2 * u).im = 2 * u.im := by simp
        rw [h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), him]
        ring
      have hg := hgood k hk u x Y h1 h2 him (by rw [him]; exact hLk) hYm
      have hb := hbound (u := u) (B := A) hne (abs_le.mpr ⟨h1, h2.trans hAnn⟩) ha₂ hg.1 hC₂
      rwa [him] at hb

/-- The field of the contour package is the packet. -/
theorem contourField_pulse (h : ℝ → ℂ) (τ x Y : ℝ) :
    contourField (pulseNumerator h x Y) τ = pulsePacket h τ x Y := by
  rw [contourField, pulsePacket]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [inverseXiQuotient, timeNumerator, pulseNumerator, normalizedEisenstein_eq_numerator_div
    (xi_line_ne_zero y)]
  have harg : -I * ((y : ℂ) * I) = y := by linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp ((y : ℂ) * I * (τ : ℂ)) = Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
    congr 1
    ring
  rw [harg, he]
  ring

/-- **The ringdown of a pulse.** -/
theorem pulse_ringdown :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ τ₀ : ℝ, 0 ≤ τ₀ → TendstoUniformlyOn (fun k τ => contourPartial (pulseNumerator h x Y) τ k)
        (fun τ => pulsePacket h τ x Y - Rem τ) atTop (Ici (-τ₀)) := by
  obtain ⟨Rem, hRem, hlim⟩ := contour_expansion fun A hA => contourData_pulse h x hY hA
  refine ⟨Rem, hRem, fun τ₀ hτ₀ => ?_⟩
  have := hlim τ₀ hτ₀
  simp_rw [contourField_pulse] at this
  exact this

end Data

/-! ### The modes -/

/-- **The mode of a zero, for any numerator analytic there.** -/
theorem exists_contourMode {R : ℂ → ℂ} {p : ℂ} (hR : AnalyticAt ℂ R p) (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (c : ℕ → ℂ),
      analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      (c 0 = 0 ↔ R p = 0) ∧
      ∀ τ : ℝ, laurentCoeff (inverseXiQuotient (timeNumerator R τ)) p (-1) =
        Complex.exp (p * (τ : ℂ)) * ∑ i ∈ Finset.range (n + 1),
          c i * (τ : ℂ) ^ (n - i) / ((n - i).factorial : ℂ) := by
  obtain ⟨n, g, horder, hg, hg0, hfac⟩ := exists_xi_shift_factor hp
  refine ⟨n, fun i => taylorCoeffZero (fun t => R (p + t) / g (p + t)) i, horder, ?_, fun τ => ?_⟩
  · simp only [taylorCoeffZero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      add_zero, div_eq_zero_iff, hg0, or_false]
  · exact laurentCoeff_mul_exp_div hR hg hg0 hfac (τ : ℂ)

/-- **Excitation.**  At a zero, the mode of the pulse has a nonzero top coefficient exactly when
`a(-ip) N(p; x, Y) ≠ 0`. -/
theorem exists_pulseMode (h : CompactPulse) (x : ℝ) {Y : ℝ} (hY : 0 < Y) {p : ℂ}
    (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (c : ℕ → ℂ),
      analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      (c 0 = 0 ↔ pulseAmplitude h (-I * p) = 0 ∨ eisensteinNumerator p x Y = 0) ∧
      ∀ τ : ℝ, laurentCoeff (inverseXiQuotient (timeNumerator (pulseNumerator h x Y) τ)) p (-1) =
        Complex.exp (p * (τ : ℂ)) * ∑ i ∈ Finset.range (n + 1),
          c i * (τ : ℂ) ^ (n - i) / ((n - i).factorial : ℂ) := by
  obtain ⟨n, c, h1, h2, h3⟩ := exists_contourMode
    (analyticAt_pulseNumerator h x hY (re_neg_of_xi_shift_eq_zero hp).le) hp
  exact ⟨n, c, h1, by rw [h2, pulseNumerator, mul_eq_zero], h3⟩

/-- A pulse that excites a prescribed point: a bump times `e^{pS}`. -/
def excitingPulse (p : ℂ) : CompactPulse where
  toFun := fun S => ((ContDiffBump.mk (c := (0 : ℝ)) 1 2 one_pos one_lt_two : ContDiffBump (0 : ℝ)) S : ℂ) *
    Complex.exp (p * (S : ℂ))
  smooth := by
    have h1 := (ContDiffBump.mk (c := (0 : ℝ)) 1 2 one_pos one_lt_two).contDiff (n := ∞)
    exact (Complex.ofRealCLM.contDiff.comp h1).mul (by fun_prop)
  compact := by
    have h1 := (ContDiffBump.mk (c := (0 : ℝ)) 1 2 one_pos one_lt_two).hasCompactSupport
    exact (h1.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right

/-- **Every point is excited by some pulse.** -/
theorem pulseAmplitude_excitingPulse_ne_zero (p : ℂ) :
    pulseAmplitude (excitingPulse p) (-I * p) ≠ 0 := by
  set b : ContDiffBump (0 : ℝ) := ContDiffBump.mk (c := (0 : ℝ)) 1 2 one_pos one_lt_two with hb
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hkey : (2 * Real.pi : ℂ) * pulseAmplitude (excitingPulse p) (-I * p) = ((∫ S : ℝ, b S : ℝ) : ℂ) := by
    rw [← (excitingPulse p).integral_mul_cexp_eq p, ← integral_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun S => ?_)
    show ((b S : ℝ) : ℂ) * Complex.exp (p * (S : ℂ)) * Complex.exp (-p * (S : ℂ)) = ((b S : ℝ) : ℂ)
    rw [mul_assoc, ← Complex.exp_add]
    have : p * (S : ℂ) + -p * (S : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero, mul_one]
  intro h0
  rw [h0, mul_zero] at hkey
  have hpos : 0 < ∫ S : ℝ, b S := b.integral_pos
  have : (∫ S : ℝ, b S) = 0 := by exact_mod_cast hkey.symm
  linarith

/-- **Every zero is excited by some pulse at some point of each horocycle.** -/
theorem exists_pulse_exciting_zero {p : ℂ} (hp : xi (1 + 2 * p) = 0) {Y : ℝ} (hY : 0 < Y) :
    ∃ (h : CompactPulse) (x : ℝ), pulseNumerator h x Y p ≠ 0 := by
  obtain ⟨x, -, hx⟩ := exists_eisensteinNumerator_ne_zero hp hY
  exact ⟨excitingPulse p, x, mul_ne_zero (pulseAmplitude_excitingPulse_ne_zero p) hx⟩

/-! ### The fields on the black hole -/

/-- **Ringdown of the Neumann field of a pulse.** -/
theorem neumannWave_pulse_ringdown (h : CompactPulse) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ t r : ℝ, Tendsto (fun k =>
          Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
            contourPartial (pulseNumerator h x y) (hyperboloidalTime t (tortoise r)) k) atTop
        (𝓝 (conformalScalar (neumannWave (pulseField h)) t r x y -
          Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
            Rem (hyperboloidalTime t (tortoise r)))) := by
  obtain ⟨Rem, hRem, hlim⟩ := pulse_ringdown h x hy
  refine ⟨Rem, hRem, fun t r => ?_⟩
  set τ := hyperboloidalTime t (tortoise r) with hτ
  have hat := (hlim |τ| (abs_nonneg τ)).tendsto_at (neg_abs_le τ : τ ∈ Ici (-|τ|))
  have h2 := hat.const_mul (Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)) / (r : ℂ))
  have hval : conformalScalar (neumannWave (pulseField h)) t r x y =
      Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)) / (r : ℂ) * pulsePacket h τ x y := by
    rw [← pulseField_eq_packet h τ x hy]
    simp only [conformalScalar, neumannWave, neumannLift, dampedProfile, ← hτ]
    ring
  rw [mul_sub, ← hval] at h2
  exact h2

end GaloisForLFunctions.BlackHoleRingdown

end
