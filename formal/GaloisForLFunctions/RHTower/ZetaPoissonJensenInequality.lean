import GaloisForLFunctions.RHTower.ZetaCriticalLineWeightedSecondMoment

/-!
# The Poisson–Jensen inequality for `ζ` on the half-plane `Re s > ½`

For `s₀` with `Re s₀ > ½`, `s₀ ≠ 1`, `ζ(s₀) ≠ 0`, and every finite set `Z` of zeros of `ζ` with
`Re ρ > ½`,

`Σ_{ρ ∈ Z} log (|ρ + s̄₀ - 1|/|ρ - s₀|)`
`  ≤ ∫ log |ζ(½ + iτ)| P_{s₀}(τ) dτ - log |ζ(s₀)| + log (|s₀|/|s₀ - 1|)`,

where `P_{s₀}(τ) = (σ₀ - ½)/(π((σ₀ - ½)² + (τ - t₀)²))` is the Poisson kernel of the half-plane.
Every term on the left is positive, so a single centre `s₀` with nonpositive right side forces the
Riemann hypothesis.

The half-plane automorphism `T(s) = (2σ₀ - 1)(s - ½) + ½ + i t₀` fixes `∞` and the critical line and
sends `1` to `s₀`; Jensen's inequality on the boundary circle is applied to
`w ↦ (T(s) - 1) ζ(T(s))`, `s = 1/(1 - w)`.  The pole factor contributes
`∫ log |½ + iτ - 1| P_{s₀}(τ) dτ = log |s₀|`.
-/

open Complex Metric Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The half-plane automorphism `T(s) = (2σ₀ - 1)(s - ½) + ½ + i t₀`. -/
def halfPlaneShift (s0 s : ℂ) : ℂ :=
  ((2 * s0.re - 1 : ℝ) : ℂ) * (s - 1 / 2) + 1 / 2 + (s0.im : ℂ) * I

/-- The Poisson kernel of the half-plane `Re s > ½` at `s₀`. -/
def halfPlanePoissonKernel (s0 : ℂ) (τ : ℝ) : ℝ :=
  (s0.re - 1 / 2) / (π * ((s0.re - 1 / 2) ^ 2 + (τ - s0.im) ^ 2))

theorem halfPlaneShift_one (s0 : ℂ) : halfPlaneShift s0 1 = s0 := by
  apply Complex.ext
  · simp [halfPlaneShift]; ring
  · simp [halfPlaneShift]

theorem re_halfPlaneShift (s0 s : ℂ) :
    (halfPlaneShift s0 s).re = (2 * s0.re - 1) * (s.re - 1 / 2) + 1 / 2 := by
  simp [halfPlaneShift]

theorem halfPlaneShift_criticalLine (s0 : ℂ) (t : ℝ) :
    halfPlaneShift s0 (1 / 2 + t * I) = 1 / 2 + (((2 * s0.re - 1) * t + s0.im : ℝ) : ℂ) * I := by
  unfold halfPlaneShift
  push_cast
  ring

theorem norm_halfPlaneShift_add_two_le {s0 : ℂ} (hs0 : 1 / 2 < s0.re) (s : ℂ) :
    ‖halfPlaneShift s0 s‖ + 2 ≤ (2 * s0.re + 2 + ‖s0‖) * (‖s‖ + 2) := by
  have hlam : 0 < 2 * s0.re - 1 := by linarith
  have h1 : halfPlaneShift s0 s
      = ((2 * s0.re - 1 : ℝ) : ℂ) * s + (1 - s0.re + (s0.im : ℂ) * I) := by
    unfold halfPlaneShift; push_cast; ring
  have h2 : ‖(1 - s0.re + (s0.im : ℂ) * I)‖ ≤ 1 + ‖s0‖ := by
    have : (1 - s0.re + (s0.im : ℂ) * I) = 1 - (starRingEnd ℂ) s0 := by
      apply Complex.ext <;> simp
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, Complex.norm_conj]
  have h3 : ‖halfPlaneShift s0 s‖ ≤ (2 * s0.re - 1) * ‖s‖ + (1 + ‖s0‖) := by
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    linarith
  have h4 := norm_nonneg s
  have h5 := norm_nonneg s0
  nlinarith

/-- `G_{s₀}(w) = (T(s) - 1) ζ(T(s))` at `s = 1/(1 - w)`. -/
def shiftedZetaDisc (s0 w : ℂ) : ℂ := zetaEntire (halfPlaneShift s0 (halfPlaneOfDisc w))

theorem shiftedZetaDisc_zero (s0 : ℂ) : shiftedZetaDisc s0 0 = zetaEntire s0 := by
  rw [shiftedZetaDisc, halfPlaneOfDisc, sub_zero, inv_one, halfPlaneShift_one]

theorem differentiableOn_shiftedZetaDisc (s0 : ℂ) :
    DifferentiableOn ℂ (shiftedZetaDisc s0) {1}ᶜ := by
  intro w hw
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h1 : DifferentiableWithinAt ℂ halfPlaneOfDisc {1}ᶜ w :=
    (((differentiableAt_const _).sub differentiableAt_id).inv hne).differentiableWithinAt
  have h2 : Differentiable ℂ (halfPlaneShift s0) := by
    unfold halfPlaneShift; fun_prop
  exact ((differentiable_zetaEntire _).comp_differentiableWithinAt w
    ((h2 _).comp_differentiableWithinAt w h1))

theorem measurable_shiftedZetaDisc (s0 : ℂ) : Measurable (shiftedZetaDisc s0) := by
  have h2 : Continuous (halfPlaneShift s0) := by unfold halfPlaneShift; fun_prop
  exact differentiable_zetaEntire.continuous.measurable.comp
    (h2.measurable.comp ((measurable_const.sub measurable_id).inv))

theorem exists_log_norm_shiftedZetaDisc_le {s0 : ℂ} (hs0 : 1 / 2 < s0.re) :
    ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 →
      Real.log ‖shiftedZetaDisc s0 w‖ ≤ A - 2 * Real.log ‖1 - w‖ := by
  obtain ⟨K, hK1, hK⟩ := exists_norm_zetaEntire_le
  set C : ℝ := 2 * s0.re + 2 + ‖s0‖ with hC
  have hC1 : 1 ≤ C := by have := norm_nonneg s0; rw [hC]; linarith
  refine ⟨Real.log (K * C ^ 2) + 2 * Real.log 5, fun w hw hw1 => ?_⟩
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hn0 : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
  have hn2 : ‖1 - w‖ ≤ 2 := by
    calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hs : ‖halfPlaneOfDisc w‖ = 1 / ‖1 - w‖ := by
    rw [halfPlaneOfDisc, norm_inv, one_div]
  have hbound : ‖halfPlaneOfDisc w‖ + 2 ≤ 5 / ‖1 - w‖ := by
    rw [hs, div_add' _ _ _ hn0.ne', div_le_div_iff_of_pos_right hn0]
    nlinarith
  have hre : 1 / 2 ≤ (halfPlaneShift s0 (halfPlaneOfDisc w)).re := by
    rw [re_halfPlaneShift]
    have := re_halfPlaneOfDisc_ge hw hw1
    nlinarith
  have hG := hK _ hre
  have hT := norm_halfPlaneShift_add_two_le hs0 (halfPlaneOfDisc w)
  have hKC : 1 ≤ K * C ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.log (K * C ^ 2) := Real.log_nonneg hKC
  have hlog5 : 2 * Real.log ‖1 - w‖ ≤ 2 * Real.log 5 := by
    have := Real.log_le_log hn0 (by linarith : ‖1 - w‖ ≤ 5)
    linarith
  rcases eq_or_ne (shiftedZetaDisc s0 w) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    linarith
  · have hpos : 0 < ‖shiftedZetaDisc s0 w‖ := norm_pos_iff.mpr h0
    have h1 : ‖shiftedZetaDisc s0 w‖ ≤ K * C ^ 2 * (5 / ‖1 - w‖) ^ 2 := by
      calc ‖shiftedZetaDisc s0 w‖ ≤ K * (‖halfPlaneShift s0 (halfPlaneOfDisc w)‖ + 2) ^ 2 := hG
        _ ≤ K * (C * (‖halfPlaneOfDisc w‖ + 2)) ^ 2 := by
            gcongr
        _ = K * C ^ 2 * (‖halfPlaneOfDisc w‖ + 2) ^ 2 := by ring
        _ ≤ K * C ^ 2 * (5 / ‖1 - w‖) ^ 2 := by
            gcongr
    have h2 := Real.log_le_log hpos h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_div (by norm_num)
      hn0.ne'] at h2
    push_cast at h2
    linarith


/-- **Affine substitution on the critical line.**  For `λ > 0`,
`(1/2π) ∫ F(λt + t₀) dt/(¼ + t²) = ∫ F(τ) P(τ) dτ` with
`P(τ) = (λ/2)/(π((λ/2)² + (τ - t₀)²))`, together with the equivalence of integrability. -/
theorem integrable_iff_and_integral_affine_criticalLine (F : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (t0 : ℝ) :
    (Integrable (fun t : ℝ => F (lam * t + t0) / (1 / 4 + t ^ 2)) ↔
        Integrable (fun τ : ℝ => F τ * ((lam / 2) / (π * ((lam / 2) ^ 2 + (τ - t0) ^ 2))))) ∧
      (2 * π)⁻¹ * ∫ t : ℝ, F (lam * t + t0) / (1 / 4 + t ^ 2)
        = ∫ τ : ℝ, F τ * ((lam / 2) / (π * ((lam / 2) ^ 2 + (τ - t0) ^ 2))) := by
  set K : ℝ → ℝ := fun τ => F τ / (1 / 4 + ((τ - t0) / lam) ^ 2) with hK
  have hKt : ∀ t : ℝ, F (lam * t + t0) / (1 / 4 + t ^ 2) = K (lam * t + t0) := by
    intro t
    simp only [hK]
    congr 2
    field_simp
    ring
  have hKP : ∀ τ : ℝ, (2 * π)⁻¹ * (lam⁻¹ * K τ)
      = F τ * ((lam / 2) / (π * ((lam / 2) ^ 2 + (τ - t0) ^ 2))) := by
    intro τ
    simp only [hK]
    field_simp
    ring
  have hl0 : lam ≠ 0 := hlam.ne'
  have hiff : Integrable (fun t : ℝ => K (lam * t + t0)) ↔ Integrable K := by
    constructor
    · intro h
      have h1 := (h.comp_mul_left' (inv_ne_zero hl0)).comp_add_right (-t0)
      refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
      field_simp
      ring_nf
    · intro h
      exact (h.comp_add_right t0).comp_mul_left' hl0
  have hint_eq : ∫ t : ℝ, K (lam * t + t0) = lam⁻¹ * ∫ τ : ℝ, K τ := by
    have := Measure.integral_comp_mul_left (fun x : ℝ => K (x + t0)) lam
    rw [this, integral_add_right_eq_self, abs_of_pos (inv_pos.mpr hlam), smul_eq_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [hKt]
    rw [hiff]
    constructor
    · intro h
      refine (h.const_mul ((2 * π)⁻¹ * lam⁻¹)).congr (Filter.Eventually.of_forall fun τ => ?_)
      dsimp only
      rw [← hKP τ]; ring
    · intro h
      refine (h.const_mul (2 * π * lam)).congr (Filter.Eventually.of_forall fun τ => ?_)
      dsimp only
      rw [← hKP τ]
      have hπ : (2 * π) ≠ 0 := by positivity
      field_simp
  · simp_rw [hKt]
    rw [hint_eq]
    simp_rw [← hKP]
    rw [integral_const_mul, integral_const_mul]

theorem halfPlanePoissonKernel_eq (s0 : ℂ) (τ : ℝ) :
    halfPlanePoissonKernel s0 τ
      = ((2 * s0.re - 1) / 2) / (π * (((2 * s0.re - 1) / 2) ^ 2 + (τ - s0.im) ^ 2)) := by
  unfold halfPlanePoissonKernel
  ring_nf

/-- **Circle averages under the centre shift.**  `circleAverage g 0 1` for `g` evaluated through
`T` equals the Poisson average on the critical line. -/
theorem circleAverage_shift_eq_poisson {s0 : ℂ} (hs0 : 1 / 2 < s0.re) (F : ℝ → ℝ) (g : ℂ → ℝ)
    (hg : ∀ t : ℝ, g (circleMap 0 1 (criticalLineAngle t)) = F ((2 * s0.re - 1) * t + s0.im)) :
    (CircleIntegrable g 0 1 ↔ Integrable (fun τ : ℝ => F τ * halfPlanePoissonKernel s0 τ)) ∧
      circleAverage g 0 1 = ∫ τ : ℝ, F τ * halfPlanePoissonKernel s0 τ := by
  have hlam : 0 < 2 * s0.re - 1 := by linarith
  obtain ⟨hiff, heq⟩ := integrable_iff_and_integral_affine_criticalLine F hlam s0.im
  have hfun : (fun t : ℝ => g (circleMap 0 1 (criticalLineAngle t)) / (1 / 4 + t ^ 2))
      = fun t => F ((2 * s0.re - 1) * t + s0.im) / (1 / 4 + t ^ 2) := by
    funext t; rw [hg]
  simp_rw [halfPlanePoissonKernel_eq]
  refine ⟨?_, ?_⟩
  · rw [circleIntegrable_iff_integrable_criticalLine, hfun, hiff]
  · rw [circleAverage_eq_integral_criticalLine, hfun, heq]

/-- The disc zero attached to a zero `ρ` of `ζ` with `Re ρ > ½`. -/
theorem shiftedZetaDisc_zero_of_zeta {s0 ρ : ℂ} (hs0 : 1 / 2 < s0.re) (hρ : riemannZeta ρ = 0)
    (hre : 1 / 2 < ρ.re) :
    shiftedZetaDisc s0 ((ρ - s0) / (ρ + (starRingEnd ℂ) s0 - 1)) = 0 ∧
      ‖(ρ - s0) / (ρ + (starRingEnd ℂ) s0 - 1)‖ < 1 := by
  set q : ℂ := ρ + (starRingEnd ℂ) s0 - 1 with hq
  have hqre : q.re = ρ.re + s0.re - 1 := by simp [hq]
  have hq0 : q ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hq] at this; linarith
  have hlamC : ((2 * s0.re - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * s0.re - 1) ≠ 0 by linarith)
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hρ
  have hone : 1 - (ρ - s0) / q = ((2 * s0.re - 1 : ℝ) : ℂ) / q := by
    rw [eq_div_iff hq0, sub_mul, div_mul_cancel₀ _ hq0, one_mul, hq]
    push_cast
    have h := Complex.add_conj s0
    push_cast at h
    linear_combination h
  refine ⟨?_, ?_⟩
  · rw [shiftedZetaDisc, halfPlaneOfDisc, hone, inv_div]
    have hT : halfPlaneShift s0 (q / ((2 * s0.re - 1 : ℝ) : ℂ)) = ρ := by
      unfold halfPlaneShift
      rw [hq]
      field_simp
      apply Complex.ext <;> simp <;> ring
    rw [hT, zetaEntire_eq hρ1, hρ, mul_zero]
  · rw [norm_div, div_lt_one (norm_pos_iff.mpr hq0)]
    have h1 : ‖ρ - s0‖ ^ 2 < ‖q‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply, hq]
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
        Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1


/-- The pole factor: `circleAverage (log |s₀ - 1 + s̄₀ w| - log |1 - w|) = log |s₀|`. -/
theorem circleIntegrable_and_circleAverage_poleFactor {s0 : ℂ} (hs0 : 1 / 2 < s0.re) :
    CircleIntegrable (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖
        - Real.log ‖1 - w‖) 0 1 ∧
      circleAverage (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖
        - Real.log ‖1 - w‖) 0 1 = Real.log ‖s0‖ := by
  have hs00 : s0 ≠ 0 := by rintro rfl; simp at hs0; linarith
  have hcs0 : (starRingEnd ℂ) s0 ≠ 0 := by simpa using hs00
  set c : ℂ := -(s0 - 1) / (starRingEnd ℂ) s0 with hc
  have hlt : ‖s0 - 1‖ < ‖s0‖ := by
    have h1 : ‖s0 - 1‖ ^ 2 < ‖s0‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  have hcn : ‖c‖ < 1 := by
    rw [hc, norm_div, norm_neg, Complex.norm_conj, div_lt_one (norm_pos_iff.mpr hs00)]
    exact hlt
  have hci1 : CircleIntegrable (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (f := fun w : ℂ => s0 - 1 + (starRingEnd ℂ) s0 * w)
      (fun w _ => (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).meromorphicAt)
  have hci2 : CircleIntegrable (fun w : ℂ => Real.log ‖1 - w‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (f := fun w : ℂ => 1 - w)
      (fun w _ => (analyticAt_const.sub analyticAt_id).meromorphicAt)
  have hci3 : CircleIntegrable (fun w : ℂ => Real.log ‖w - c‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (f := fun w : ℂ => w - c)
      (fun w _ => (analyticAt_id.sub analyticAt_const).meromorphicAt)
  refine ⟨hci1.sub hci2, ?_⟩
  rw [circleAverage_fun_sub hci1 hci2]
  have h2 : circleAverage (fun w : ℂ => Real.log ‖1 - w‖) 0 1 = 0 := by
    have : (fun w : ℂ => Real.log ‖1 - w‖) = fun w => Real.log ‖w - 1‖ := by
      funext w; rw [norm_sub_rev]
    rw [this]
    exact circleAverage_log_norm_sub_const₁ (by simp)
  have h1 : circleAverage (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖) 0 1
      = Real.log ‖s0‖ := by
    have hsph : Set.EqOn (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖)
        (fun w => Real.log ‖(starRingEnd ℂ) s0‖ + Real.log ‖w - c‖) (sphere (0 : ℂ) |1|) := by
      intro w hw
      rw [abs_one, mem_sphere, dist_zero_right] at hw
      have hwc : w - c ≠ 0 := by
        intro h; rw [sub_eq_zero] at h; rw [h] at hw; linarith
      have hfac : s0 - 1 + (starRingEnd ℂ) s0 * w = (starRingEnd ℂ) s0 * (w - c) := by
        rw [hc]; field_simp; ring
      simp only
      rw [hfac, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hcs0) (norm_ne_zero_iff.mpr hwc)]
    rw [circleAverage_congr_sphere hsph, circleAverage_fun_add (circleIntegrable_const _ _ _) hci3,
      circleAverage_const, circleAverage_log_norm_sub_const₀ hcn, add_zero, Complex.norm_conj]
  rw [h1, h2, sub_zero]

/-- `T(1/(1 - w)) - 1 = (s₀ - 1 + s̄₀ w)/(1 - w)`. -/
theorem halfPlaneShift_halfPlaneOfDisc_sub_one (s0 : ℂ) {w : ℂ} (hw : w ≠ 1) :
    halfPlaneShift s0 (halfPlaneOfDisc w) - 1
      = (s0 - 1 + (starRingEnd ℂ) s0 * w) / (1 - w) := by
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  obtain ⟨σ, t, rfl⟩ : ∃ σ t : ℝ, s0 = (σ : ℂ) + (t : ℂ) * I :=
    ⟨s0.re, s0.im, (Complex.re_add_im s0).symm⟩
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  have hconj : (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * I) = (σ : ℂ) - (t : ℂ) * I := by
    apply Complex.ext <;> simp
  unfold halfPlaneShift halfPlaneOfDisc
  rw [hre, him, hconj, eq_div_iff hne]
  push_cast
  field_simp
  ring

/-- **The Poisson–Jensen inequality for `ζ`.**  For `Re s₀ > ½`, `s₀ ≠ 1`, `ζ(s₀) ≠ 0` and finitely
many zeros `ρ` of `ζ` with `Re ρ > ½`,
`Σ log (|ρ + s̄₀ - 1|/|ρ - s₀|) ≤ ∫ log |ζ(½ + iτ)| P_{s₀}(τ) dτ - log |ζ(s₀)|`
`+ log (|s₀|/|s₀ - 1|)`, and the integrand is integrable. -/
theorem integrable_and_sum_log_blaschke_le {s0 : ℂ} (hs0 : 1 / 2 < s0.re) (hs01 : s0 ≠ 1)
    (hz0 : riemannZeta s0 ≠ 0) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) :
    Integrable (fun τ : ℝ =>
        Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ) ∧
      ∑ ρ ∈ Z, Real.log (‖ρ + (starRingEnd ℂ) s0 - 1‖ / ‖ρ - s0‖)
        ≤ (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ)
          - Real.log ‖riemannZeta s0‖ + Real.log (‖s0‖ / ‖s0 - 1‖) := by
  have hlam : 0 < 2 * s0.re - 1 := by linarith
  have hs00 : s0 ≠ 0 := by rintro rfl; simp at hs0; linarith
  set U := Z.image (fun ρ : ℂ => (ρ - s0) / (ρ + (starRingEnd ℂ) s0 - 1)) with hUdef
  have hU : ∀ u ∈ U, shiftedZetaDisc s0 u = 0 ∧ ‖u‖ < 1 := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hu
    exact shiftedZetaDisc_zero_of_zeta hs0 (hZ ρ hρ).1 (hZ ρ hρ).2
  have hG0 : zetaEntire s0 ≠ 0 := by
    rw [zetaEntire_eq hs01]; exact mul_ne_zero (sub_ne_zero.mpr hs01) hz0
  obtain ⟨hci, hle⟩ := circleIntegrable_and_sum_log_add_le_circleAverage
    (differentiableOn_shiftedZetaDisc s0) (measurable_shiftedZetaDisc s0)
    (by rw [shiftedZetaDisc_zero]; exact hG0) (exists_log_norm_shiftedZetaDisc_le hs0) hU
  rw [shiftedZetaDisc_zero] at hle
  set F1 : ℝ → ℝ := fun τ => Real.log ‖zetaEntire (1 / 2 + τ * I)‖ with hF1
  set F2 : ℝ → ℝ := fun τ => Real.log ‖(1 / 2 + τ * I : ℂ) - 1‖ with hF2
  have hcrit : ∀ t : ℝ, halfPlaneShift s0 (halfPlaneOfDisc (circleMap 0 1 (criticalLineAngle t)))
      = 1 / 2 + (((2 * s0.re - 1) * t + s0.im : ℝ) : ℂ) * I := by
    intro t
    rw [halfPlaneOfDisc_circleMap_criticalLineAngle, halfPlaneShift_criticalLine]
  obtain ⟨hiff1, heq1⟩ := circleAverage_shift_eq_poisson hs0 F1
    (fun w => Real.log ‖shiftedZetaDisc s0 w‖) (fun t => by
      simp only [hF1, shiftedZetaDisc, hcrit])
  have hF1int := hiff1.mp hci
  obtain ⟨hpci, hpavg⟩ := circleIntegrable_and_circleAverage_poleFactor hs0
  have hw1 : ∀ t : ℝ, circleMap 0 1 (criticalLineAngle t) ≠ 1 := by
    intro t h
    have := halfPlaneOfDisc_circleMap_criticalLineAngle t
    rw [h, halfPlaneOfDisc, sub_self, inv_zero] at this
    have h2 := congrArg Complex.re this
    norm_num at h2
  obtain ⟨hiff2, heq2⟩ := circleAverage_shift_eq_poisson hs0 F2
    (fun w : ℂ => Real.log ‖s0 - 1 + (starRingEnd ℂ) s0 * w‖ - Real.log ‖1 - w‖) (fun t => by
      have hwt := hw1 t
      set w := circleMap 0 1 (criticalLineAngle t) with hwdef
      have hwn : ‖w‖ = 1 := by rw [hwdef]; simp
      have hnum : s0 - 1 + (starRingEnd ℂ) s0 * w ≠ 0 := by
        intro h
        have hw' : w = -(s0 - 1) / (starRingEnd ℂ) s0 := by
          have hcs0 : (starRingEnd ℂ) s0 ≠ 0 := by simpa using hs00
          field_simp; linear_combination h
        have hlt : ‖s0 - 1‖ < ‖s0‖ := by
          have h1 : ‖s0 - 1‖ ^ 2 < ‖s0‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
              Complex.normSq_apply]
            simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
            nlinarith
          exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
        rw [hw', norm_div, norm_neg, Complex.norm_conj,
          div_eq_one_iff_eq (norm_ne_zero_iff.mpr hs00)] at hwn
        linarith
      have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwt)
      simp only [hF2]
      rw [← hcrit t, halfPlaneShift_halfPlaneOfDisc_sub_one s0 hwt, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hnum) (norm_ne_zero_iff.mpr hden)])
  have hF2int := hiff2.mp hpci
  rw [hpavg] at heq2
  have hne1 : ∀ τ : ℝ, (1 / 2 : ℂ) + τ * I ≠ 1 := by
    intro τ h; have := congrArg Complex.re h; norm_num at this
  have hcount : {τ : ℝ | riemannZeta (1 / 2 + τ * I) = 0}.Countable := by
    have hinj : Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + τ * I) := by
      intro a b hab
      have := congrArg Complex.im hab
      simpa using this
    refine (countable_setOf_zetaEntire_eq_zero.preimage hinj).mono fun τ hτ => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hτ ⊢
    rw [zetaEntire_eq (hne1 τ), hτ, mul_zero]
  have hae : ∀ᵐ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ
      = F1 τ * halfPlanePoissonKernel s0 τ - F2 τ * halfPlanePoissonKernel s0 τ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero _)] with τ hτ
    have hsub : (1 / 2 : ℂ) + τ * I - 1 ≠ 0 := sub_ne_zero.mpr (hne1 τ)
    simp only [hF1, hF2]
    rw [zetaEntire_eq (hne1 τ), norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hsub)
      (norm_ne_zero_iff.mpr hτ)]
    ring
  have hZint : Integrable (fun τ : ℝ =>
      Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ) :=
    (hF1int.sub hF2int).congr (hae.mono fun τ hτ => hτ.symm)
  have hZeq : ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ
      = circleAverage (fun w => Real.log ‖shiftedZetaDisc s0 w‖) 0 1 - Real.log ‖s0‖ := by
    rw [integral_congr_ae hae, integral_sub hF1int hF2int, ← heq1, ← heq2]
  refine ⟨hZint, ?_⟩
  rw [hZeq]
  have hsum : ∑ u ∈ U, Real.log (1 / ‖u‖)
      = ∑ ρ ∈ Z, Real.log (‖ρ + (starRingEnd ℂ) s0 - 1‖ / ‖ρ - s0‖) := by
    rw [hUdef, Finset.sum_image]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [norm_div, one_div_div]
    · intro a ha b hb hab
      have hqa : a + (starRingEnd ℂ) s0 - 1 ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith [(hZ a ha).2]
      have hqb : b + (starRingEnd ℂ) s0 - 1 ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith [(hZ b hb).2]
      have hcross := hab
      simp only at hcross
      rw [div_eq_div_iff hqa hqb] at hcross
      have hk : (s0 + (starRingEnd ℂ) s0 - 1) ≠ 0 := by
        rw [Complex.add_conj]
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have : (a - b) * (s0 + (starRingEnd ℂ) s0 - 1) = 0 := by linear_combination hcross
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hk
  rw [← hsum]
  have hlogG : Real.log ‖zetaEntire s0‖ = Real.log ‖s0 - 1‖ + Real.log ‖riemannZeta s0‖ := by
    rw [zetaEntire_eq hs01, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs01))
      (norm_ne_zero_iff.mpr hz0)]
  rw [hlogG] at hle
  rw [Real.log_div (norm_ne_zero_iff.mpr hs00) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs01))]
  linarith

/-- **The Poisson–Jensen criterion.**  If for some `s₀` with `Re s₀ > ½`, `s₀ ≠ 1`, `ζ(s₀) ≠ 0`,
`∫ log |ζ(½ + iτ)| P_{s₀}(τ) dτ ≤ log |ζ(s₀)| - log (|s₀|/|s₀ - 1|)`, the Riemann hypothesis
holds. -/
theorem riemannHypothesis_of_poisson_log_norm_zeta_le {s0 : ℂ} (hs0 : 1 / 2 < s0.re)
    (hs01 : s0 ≠ 1) (hz0 : riemannZeta s0 ≠ 0)
    (h : ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ
      ≤ Real.log ‖riemannZeta s0‖ - Real.log (‖s0‖ / ‖s0 - 1‖)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro ρ hρ hzρ
  have hle := (integrable_and_sum_log_blaschke_le hs0 hs01 hz0 (Z := {ρ})
    (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact ⟨hzρ, hρ⟩)).2
  rw [Finset.sum_singleton] at hle
  have hρs0 : ρ ≠ s0 := by rintro rfl; exact hz0 hzρ
  have hlt : ‖ρ - s0‖ < ‖ρ + (starRingEnd ℂ) s0 - 1‖ := by
    have h1 : ‖ρ - s0‖ ^ 2 < ‖ρ + (starRingEnd ℂ) s0 - 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
        Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  have hpos0 : 0 < ‖ρ - s0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρs0)
  have hpos : 0 < Real.log (‖ρ + (starRingEnd ℂ) s0 - 1‖ / ‖ρ - s0‖) :=
    Real.log_pos (by rw [one_lt_div hpos0]; exact hlt)
  linarith

end

end RHTower
