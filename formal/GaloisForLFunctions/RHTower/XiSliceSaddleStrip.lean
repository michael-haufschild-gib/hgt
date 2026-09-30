import GaloisForLFunctions.RHTower.XiSliceCoeffPositivitySharpWindow

/-!
# The slice saddle with the saddle disc inside the critical strip

`XiSliceSaddleArcBoundsEulerRegion` and `XiSliceCoeffPositivitySharpWindow` prove `c_{2k}(t) > 0`
when the saddle radius satisfies `R ≥ ½ + 2η`, so that the saddle disc `|w − R| ≤ η` puts both
points `½ + w ± it` in the Euler half-plane. The only inputs used there are

* the slice product `g_t` has no zero on an open set `U ⊇ {|w − R| ≤ r}`,
* `ξ'/ξ(s)` is within a constant `C` of `½ log(s/2)` at the points `½ + w ± it` of the disc.

Here both are hypotheses (`XiSliceStirling t C S`), so the saddle radius may be as small as `2r`,
with the saddle disc inside the critical strip. The Stirling hypothesis follows from a bound
`|ζ'/ζ(s)| ≤ B` with `C = 3 + B` (`norm_logDeriv_xi_sub_half_log_le_of_zeta`).
-/

open Complex Real Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-! ## The slice product on a zero-free set -/

theorem xi_ne_zero_of_xiSliceProduct_ne_zero {t : ℝ} {w : ℂ} (h : xiSliceProduct t w ≠ 0) :
    xi (1 / 2 + w + (t : ℂ) * I) ≠ 0 ∧ xi (1 / 2 + w - (t : ℂ) * I) ≠ 0 := by
  unfold xiSliceProduct at h
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  refine ⟨left_ne_zero_of_mul h, ?_⟩
  have h2 := right_ne_zero_of_mul h
  rwa [e, xi_one_sub] at h2

/-- **Scaled logarithmic derivative on a zero-free set.** -/
theorem scaledLogDeriv_xiSliceProduct_of_ne {t : ℝ} {w : ℂ} (hne : xiSliceProduct t w ≠ 0) :
    HTGeometry.scaledLogDeriv (xiSliceProduct t) w = w * xiSliceLogDeriv t w := by
  have hA : xi (1 / 2 + w + (t : ℂ) * I) ≠ 0 := (xi_ne_zero_of_xiSliceProduct_ne_zero hne).1
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  have hB : xi (1 / 2 - w + (t : ℂ) * I) ≠ 0 := by
    rw [e, xi_one_sub]; exact (xi_ne_zero_of_xiSliceProduct_ne_zero hne).2
  have h1 : HasDerivAt (fun x : ℂ => xi (1 / 2 + x + (t : ℂ) * I))
      (deriv xi (1 / 2 + w + (t : ℂ) * I)) w := by
    have := (xi_differentiable (1 / 2 + w + (t : ℂ) * I)).hasDerivAt.comp w
      (((hasDerivAt_id' w).const_add (1 / 2 : ℂ)).add_const ((t : ℂ) * I))
    exact this.congr_deriv (by simp)
  have h2 : HasDerivAt (fun x : ℂ => xi (1 / 2 - x + (t : ℂ) * I))
      (-deriv xi (1 / 2 - w + (t : ℂ) * I)) w := by
    have := (xi_differentiable (1 / 2 - w + (t : ℂ) * I)).hasDerivAt.comp w
      (((hasDerivAt_id' w).const_sub (1 / 2 : ℂ)).add_const ((t : ℂ) * I))
    exact this.congr_deriv (by simp)
  have hd : deriv (xiSliceProduct t) w
      = deriv xi (1 / 2 + w + (t : ℂ) * I) * xi (1 / 2 - w + (t : ℂ) * I)
        + xi (1 / 2 + w + (t : ℂ) * I) * (-deriv xi (1 / 2 - w + (t : ℂ) * I)) :=
    (h1.mul h2).deriv
  have hfe : logDeriv xi (1 / 2 - w + (t : ℂ) * I) = -logDeriv xi (1 / 2 + w - (t : ℂ) * I) := by
    rw [e, logDeriv_xi_one_sub_xiLogDerivSymmetry]
  have key : ∀ a b da db : ℂ, a ≠ 0 → b ≠ 0 →
      w * (da * b + a * -db) / (a * b) = w * (da / a + -(db / b)) := by
    intro a b da db ha hb; field_simp
  have hsl : xiSliceProduct t w = xi (1 / 2 + w + (t : ℂ) * I) * xi (1 / 2 - w + (t : ℂ) * I) := rfl
  unfold HTGeometry.scaledLogDeriv xiSliceLogDeriv
  rw [hd, hsl, show logDeriv xi (1 / 2 + w - (t : ℂ) * I) = -logDeriv xi (1 / 2 - w + (t : ℂ) * I)
    by rw [hfe, neg_neg], logDeriv_apply, logDeriv_apply]
  exact key _ _ _ _ hA hB

theorem im_scaledLogDeriv_xiSliceProduct_ofReal_of_ne {t x : ℝ}
    (hne : xiSliceProduct t (x : ℂ) ≠ 0) :
    (HTGeometry.scaledLogDeriv (xiSliceProduct t) (x : ℂ)).im = 0 := by
  rw [scaledLogDeriv_xiSliceProduct_of_ne hne]
  have hc : (1 / 2 : ℂ) + (x : ℂ) - (t : ℂ) * I
      = (starRingEnd ℂ) (1 / 2 + (x : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  unfold xiSliceLogDeriv
  rw [hc, logDeriv_xi_conj_xiLogDerivSymmetry]
  simp [Complex.mul_im]

theorem differentiableOn_xiSliceLogDeriv_of {t : ℝ} {U : Set ℂ}
    (hU : ∀ w ∈ U, xiSliceProduct t w ≠ 0) :
    DifferentiableOn ℂ (xiSliceLogDeriv t) U := by
  have hd : Differentiable ℂ (deriv xi) := fun s =>
    ((xi_differentiable.differentiableOn.deriv isOpen_univ) s (Set.mem_univ _)).differentiableAt
      (Filter.univ_mem)
  intro w hw
  obtain ⟨hA, hB⟩ := xi_ne_zero_of_xiSliceProduct_ne_zero (hU w hw)
  have h1 : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi (1 / 2 + w + (t : ℂ) * I)) w := by
    have hin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w + (t : ℂ) * I) w := by fun_prop
    simp only [logDeriv_apply]
    exact ((hd _).comp w hin).div ((xi_differentiable _).comp w hin) hA
  have h2 : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi (1 / 2 + w - (t : ℂ) * I)) w := by
    have hin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w - (t : ℂ) * I) w := by fun_prop
    simp only [logDeriv_apply]
    exact ((hd _).comp w hin).div ((xi_differentiable _).comp w hin) hB
  exact (h1.add h2).differentiableWithinAt

/-- **Quarter-arc formula at a nonvanishing radius.** -/
theorem xiSliceCoeff_two_mul_eq_quarter_of_ne (t : ℝ) (k : ℕ) {R : ℝ} (hR0 : 0 < R)
    (hne : xiSliceProduct t (R : ℂ) ≠ 0) :
    xiSliceCoeff t (2 * k)
      = ((2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * k))
          * ∫ θ in (0 : ℝ)..(Real.pi / 2),
            (HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ).re : ℝ) : ℂ) := by
  rw [xiSliceCoeff_eq_circle t (2 * k) hR0]
  have hsa : ∀ θ : ℝ, Complex.exp (-((((2 * k : ℕ) : ℝ) * θ : ℝ) : ℂ) * I)
        * xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))
      = xiSliceProduct t (R : ℂ) * HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ := by
    intro θ
    unfold HTGeometry.saddleArc
    push_cast
    field_simp
  simp_rw [hsa]
  set S : ℝ → ℂ := fun θ => HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ with hSdef
  have hSc : Continuous S := by
    have hg := differentiable_xiSliceProduct t
    simp only [hSdef, HTGeometry.saddleArc]
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    fun_prop
  rw [intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable S MeasureTheory.volume 0 (2 * Real.pi) :=
    hSc.intervalIntegrable _ _
  have hre : (∫ θ in (0 : ℝ)..(2 * Real.pi), S θ).re
      = 4 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re := by
    rw [HTGeometry.re_intervalIntegral hint]
    rw [integral_zero_two_pi_of_period_pi_parity (h := fun θ => (S θ).re) (σ := 1)
      (Complex.continuous_re.comp hSc)
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_add_pi])
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_neg]; simp)]
    ring
  have him : (∫ θ in (0 : ℝ)..(2 * Real.pi), S θ).im = 0 := by
    rw [HTGeometry.im_intervalIntegral hint]
    rw [integral_zero_two_pi_of_period_pi_parity (h := fun θ => (S θ).im) (σ := -1)
      (Complex.continuous_im.comp hSc)
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_add_pi])
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_neg]; simp)]
    ring
  have hI : (∫ θ in (0 : ℝ)..(2 * Real.pi), S θ)
      = ((4 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hre]; simp
    · rw [him]; simp
  rw [hI, xiSliceProduct_ofReal_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hRn : R ^ (2 * k) ≠ 0 := pow_ne_zero _ hR0.ne'
  push_cast
  field_simp
  ring

/-! ## Stirling comparison for `ξ'/ξ` off the real axis -/

/-- **Stirling comparison from a bound on `ζ'/ζ`.** Off the real axis, in `Re s > 0` with
`|s| ≥ 4` and `ζ(s) ≠ 0`, `|ξ'/ξ(s) − ½ log(s/2)| ≤ 3 + |ζ'/ζ(s)|`. -/
theorem norm_logDeriv_xi_sub_half_log_le_of_zeta {s : ℂ} {B : ℝ} (hs : 0 < s.re) (him : s.im ≠ 0)
    (hs4 : 4 ≤ ‖s‖) (hζ : riemannZeta s ≠ 0) (hB : ‖logDeriv riemannZeta s‖ ≤ B) :
    ‖logDeriv xi s - Complex.log (s / 2) / 2‖ ≤ 3 + B := by
  rw [logDeriv_xi_fourFactor_offReal him hζ]
  have e : 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2
      + logDeriv riemannZeta s - Complex.log (s / 2) / 2
      = (1 / s + 1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2
        + ((Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 + logDeriv riemannZeta s) := by
    ring
  rw [e]
  have h1 : ‖1 / s‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) hs4
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (by norm_num)
    have := norm_sub_norm_le s 1; simp only [norm_one] at this; linarith
  have h3 : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ 11 / 10 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2']
    linarith [Real.pi_lt_d2]
  have hs2re : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hs2 : 2 ≤ ‖s / 2‖ := by
    rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have h4 : ‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2‖ ≤ 3 / 4 := by
    rw [norm_div]; simp only [Complex.norm_ofNat]
    have := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hs2re hs2
    have h' : 3 / ‖s / 2‖ ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
    linarith
  calc _ ≤ ‖(1 / s + 1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2‖
        + ‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 + logDeriv riemannZeta s‖ :=
        norm_add_le _ _
    _ ≤ (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖)
        + (‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2‖ + ‖logDeriv riemannZeta s‖) := by
        gcongr
        · exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
        · exact norm_add_le _ _
    _ ≤ (1 / 4 + 1 / 3 + 11 / 10) + (3 / 4 + B) := by gcongr
    _ ≤ 3 + B := by linarith

/-- The Stirling comparison transfers to the conjugate point. -/
theorem norm_logDeriv_xi_sub_half_log_conj {s : ℂ} (hs : 0 < s.re) :
    ‖logDeriv xi ((starRingEnd ℂ) s) - Complex.log ((starRingEnd ℂ) s / 2) / 2‖
      = ‖logDeriv xi s - Complex.log (s / 2) / 2‖ := by
  have harg : (s / 2).arg ≠ Real.pi := by
    intro h
    have hre : 0 < (s / 2).re := by simp; linarith
    have := Complex.abs_arg_le_pi_div_two_iff.mpr hre.le
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  have hc : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, show (starRingEnd ℂ) (2 : ℂ) = 2 from Complex.conj_ofNat 2]
  rw [logDeriv_xi_conj_xiLogDerivSymmetry, hc, Complex.log_conj _ harg,
    show (starRingEnd ℂ) (Complex.log (s / 2)) / 2 = (starRingEnd ℂ) (Complex.log (s / 2) / 2) by
      rw [map_div₀, Complex.conj_ofNat], ← map_sub, Complex.norm_conj]

/-! ## Disc bounds under the Stirling hypothesis -/

/-- `ξ'/ξ` is within `C` of `½ log(s/2)` at both points `½ + w ± it` for `w ∈ S`. -/
def XiSliceStirling (t C : ℝ) (S : Set ℂ) : Prop :=
  ∀ w ∈ S,
    ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I) - Complex.log ((1 / 2 + w + (t : ℂ) * I) / 2) / 2‖ ≤ C
    ∧ ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I) - Complex.log ((1 / 2 + w - (t : ℂ) * I) / 2) / 2‖
      ≤ C

theorem logDeriv_xi_annulus_bounds_of_stirling {s : ℂ} {m₁ m₂ C : ℝ} (hre0 : 0 < s.re)
    (hE : ‖logDeriv xi s - Complex.log (s / 2) / 2‖ ≤ C) (hm₁ : 4 ≤ m₁) (h₁ : m₁ ≤ ‖s‖)
    (h₂ : ‖s‖ ≤ m₂) :
    ‖logDeriv xi s‖ ≤ Real.log (m₂ / 2) / 2 + Real.pi / 4 + C
      ∧ Real.log (m₁ / 2) / 2 - C ≤ (logDeriv xi s).re
      ∧ (logDeriv xi s).re ≤ Real.log (m₂ / 2) / 2 + C := by
  have hs4 : 4 ≤ ‖s‖ := le_trans hm₁ h₁
  have hre2 : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hn2 : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; simp
  have hn1 : 1 ≤ ‖s / 2‖ := by rw [hn2]; linarith
  have hlogle : Real.log ‖s / 2‖ ≤ Real.log (m₂ / 2) := by
    rw [hn2]; exact Real.log_le_log (by linarith) (by linarith)
  have hlogge : Real.log (m₁ / 2) ≤ Real.log ‖s / 2‖ := by
    rw [hn2]; exact Real.log_le_log (by linarith) (by linarith)
  have hlog := norm_log_le_of_re_pos hre2 hn1
  have hre : (Complex.log (s / 2) / 2).re = Real.log ‖s / 2‖ / 2 := by
    rw [Complex.div_ofNat_re, Complex.log_re]
  have hEre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hE))
  rw [Complex.sub_re, hre] at hEre
  refine ⟨?_, by linarith [hEre.1], by linarith [hEre.2]⟩
  calc ‖logDeriv xi s‖ ≤ ‖Complex.log (s / 2) / 2‖ + ‖logDeriv xi s - Complex.log (s / 2) / 2‖ := by
        have := norm_add_le (Complex.log (s / 2) / 2) (logDeriv xi s - Complex.log (s / 2) / 2)
        simpa using this
    _ ≤ (Real.log (m₂ / 2) + Real.pi / 2) / 2 + C := by
        rw [norm_div]; simp only [Complex.norm_ofNat]
        gcongr
        linarith
    _ = Real.log (m₂ / 2) / 2 + Real.pi / 4 + C := by ring

theorem norm_logDeriv_xi_sub_le_annulus_of_stirling {s s' : ℂ} {m₁ m₂ C : ℝ} (hre : 0 < s.re)
    (hre' : 0 < s'.re) (hE : ‖logDeriv xi s - Complex.log (s / 2) / 2‖ ≤ C)
    (hE' : ‖logDeriv xi s' - Complex.log (s' / 2) / 2‖ ≤ C)
    (hm₁ : 4 ≤ m₁) (h₁ : m₁ ≤ ‖s‖) (h₂ : ‖s‖ ≤ m₂) (h₁' : m₁ ≤ ‖s'‖) (h₂' : ‖s'‖ ≤ m₂) :
    ‖logDeriv xi s - logDeriv xi s'‖ ≤ Real.log (m₂ / m₁) / 2 + Real.pi / 2 + 2 * C := by
  have hre2 : ∀ z : ℂ, 0 < z.re → 0 < (z / 2).re := fun z hz => by
    have : (z / 2).re = z.re / 2 := by simp
    rw [this]; linarith
  have hlog := norm_log_sub_log_le_of_re_pos (hre2 s hre) (hre2 s' hre')
  have hn2 : ∀ z : ℂ, ‖z / 2‖ = ‖z‖ / 2 := fun z => by rw [norm_div]; simp
  have hm1pos : 0 < m₁ := by linarith
  have hspos : 0 < ‖s‖ := by linarith
  have hs'pos : 0 < ‖s'‖ := by linarith
  have hratio : |Real.log ‖s / 2‖ - Real.log ‖s' / 2‖| ≤ Real.log (m₂ / m₁) := by
    rw [hn2, hn2, ← Real.log_div (by positivity) (by positivity), abs_le]
    have hp : 0 < ‖s‖ / 2 / (‖s'‖ / 2) := by positivity
    constructor
    · rw [neg_le, ← Real.log_inv, inv_div]
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by linarith) hm1pos]
      nlinarith
    · apply Real.log_le_log hp
      rw [div_le_div_iff₀ (by linarith) hm1pos]
      nlinarith
  calc ‖logDeriv xi s - logDeriv xi s'‖
      ≤ ‖Complex.log (s / 2) / 2 - Complex.log (s' / 2) / 2‖
        + ‖logDeriv xi s - Complex.log (s / 2) / 2‖
        + ‖logDeriv xi s' - Complex.log (s' / 2) / 2‖ := by
        have e : logDeriv xi s - logDeriv xi s'
            = (Complex.log (s / 2) / 2 - Complex.log (s' / 2) / 2)
              + (logDeriv xi s - Complex.log (s / 2) / 2)
              - (logDeriv xi s' - Complex.log (s' / 2) / 2) := by ring
        rw [e]
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (Real.log (m₂ / m₁) + Real.pi) / 2 + C + C := by
        gcongr
        rw [← sub_div, norm_div]; simp only [Complex.norm_ofNat]
        gcongr
        linarith
    _ = Real.log (m₂ / m₁) / 2 + Real.pi / 2 + 2 * C := by ring

/-- Geometry of `½ + w ± it` for `|w − R| ≤ r ≤ R ≤ t/2`, `r ≤ ½`, `t ≥ 8`. -/
theorem slicePoint_annulus_strip {t R r : ℝ} (hr1 : r ≤ 1 / 2) (ht : 8 ≤ t) (hrR : r ≤ R)
    (hRt : R ≤ t / 2) {w : ℂ} (hw : w ∈ closedBall (R : ℂ) r) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    1 / 2 ≤ (1 / 2 + w + (ε * t : ℝ) * I).re ∧ 3 * t / 4 ≤ ‖1 / 2 + w + (ε * t : ℝ) * I‖
      ∧ ‖1 / 2 + w + (ε * t : ℝ) * I‖ ≤ 3 * t := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw))
  have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hw))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
  have hεt : |ε * t| = t := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_pos (by linarith : (0 : ℝ) < t)]
  have hsre : (1 / 2 + w + (ε * t : ℝ) * I).re = 1 / 2 + w.re := by simp
  have hsim : (1 / 2 + w + (ε * t : ℝ) * I).im = w.im + ε * t := by simp
  refine ⟨by rw [hsre]; linarith, ?_, ?_⟩
  · refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [hsim]
    have h1 : |ε * t| - |w.im| ≤ |w.im + ε * t| := by
      have := abs_sub_abs_le_abs_sub (ε * t) (-w.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this; linarith
    rw [hεt] at h1
    have : |w.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hsre, hsim]
    have h1 : |1 / 2 + w.re| ≤ 1 / 2 + R + r := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |w.im + ε * t| ≤ r + t := by
      refine (abs_add_le _ _).trans ?_
      rw [hεt]; have : |w.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    linarith

/-- Disc bounds for `L = ξ'/ξ(½+·+it) + ξ'/ξ(½+·−it)` on `|w − R| ≤ r` under the Stirling
hypothesis. -/
theorem xiSliceLogDeriv_disc_bounds_strip {t R r C : ℝ} (hr1 : r ≤ 1 / 2) (ht : 8 ≤ t)
    (hrR : r ≤ R) (hRt : R ≤ t / 2) (hS : XiSliceStirling t C (closedBall (R : ℂ) r))
    {w : ℂ} (hw : w ∈ closedBall (R : ℂ) r) :
    ‖xiSliceLogDeriv t w‖ ≤ Real.log (3 * t / 2) + Real.pi / 2 + 2 * C
      ∧ ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖ ≤ Real.log 4 + Real.pi + 4 * C := by
  have hr0 : 0 ≤ r := by
    have := dist_nonneg (x := w) (y := (R : ℂ)); rw [mem_closedBall] at hw; linarith
  have hR0 : (R : ℂ) ∈ closedBall (R : ℂ) r := mem_closedBall_self hr0
  have ep : ∀ z : ℂ, (1 / 2 + z + ((1 : ℝ) * t : ℝ) * I) = 1 / 2 + z + (t : ℂ) * I := by
    intro z; push_cast; ring
  have em : ∀ z : ℂ, (1 / 2 + z + ((-1 : ℝ) * t : ℝ) * I) = 1 / 2 + z - (t : ℂ) * I := by
    intro z; push_cast; ring
  obtain ⟨p1, p2, p3⟩ := slicePoint_annulus_strip hr1 ht hrR hRt hw 1 (Or.inl rfl)
  obtain ⟨m1, m2, m3⟩ := slicePoint_annulus_strip hr1 ht hrR hRt hw (-1) (Or.inr rfl)
  obtain ⟨q1, q2, q3⟩ := slicePoint_annulus_strip hr1 ht hrR hRt hR0 1 (Or.inl rfl)
  obtain ⟨n1, n2, n3⟩ := slicePoint_annulus_strip hr1 ht hrR hRt hR0 (-1) (Or.inr rfl)
  rw [ep] at p1 p2 p3 q1 q2 q3
  rw [em] at m1 m2 m3 n1 n2 n3
  obtain ⟨hwp, hwm⟩ := hS w hw
  obtain ⟨hRp, hRm⟩ := hS R hR0
  have hm : (4 : ℝ) ≤ 3 * t / 4 := by linarith
  have hA := (logDeriv_xi_annulus_bounds_of_stirling (by linarith) hwp hm p2 p3).1
  have hB := (logDeriv_xi_annulus_bounds_of_stirling (by linarith) hwm hm m2 m3).1
  have hdiv : 3 * t / (3 * t / 4) = 4 := by field_simp
  have hD1 := norm_logDeriv_xi_sub_le_annulus_of_stirling (by linarith) (by linarith) hwp hRp hm
    p2 p3 q2 q3
  have hD2 := norm_logDeriv_xi_sub_le_annulus_of_stirling (by linarith) (by linarith) hwm hRm hm
    m2 m3 n2 n3
  rw [hdiv] at hD1 hD2
  constructor
  · unfold xiSliceLogDeriv
    calc _ ≤ ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I)‖ + ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I)‖ :=
          norm_add_le _ _
      _ ≤ (Real.log (3 * t / 2) / 2 + Real.pi / 4 + C)
          + (Real.log (3 * t / 2) / 2 + Real.pi / 4 + C) := by
          gcongr
      _ = _ := by ring
  · unfold xiSliceLogDeriv
    have e : logDeriv xi (1 / 2 + w + (t : ℂ) * I) + logDeriv xi (1 / 2 + w - (t : ℂ) * I)
        - (logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I) + logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I))
        = (logDeriv xi (1 / 2 + w + (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I))
          + (logDeriv xi (1 / 2 + w - (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I)) := by
      ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (Real.log 4 / 2 + Real.pi / 2 + 2 * C) + (Real.log 4 / 2 + Real.pi / 2 + 2 * C) :=
          add_le_add hD1 hD2
      _ = _ := by ring

/-- `L(R)` is real, with `log(t/2) − 2C ≤ L(R) ≤ log t + 2C`, when `ξ'/ξ(½ + R + it)` is within
`C` of `½ log`. -/
theorem xiSliceLogDeriv_real_bounds_strip {t R C : ℝ} (ht : 8 ≤ t) (hR : 0 ≤ R) (hRt : R ≤ t / 2)
    (hE : ‖logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I)
      - Complex.log ((1 / 2 + (R : ℂ) + (t : ℂ) * I) / 2) / 2‖ ≤ C) :
    (xiSliceLogDeriv t R).im = 0
      ∧ Real.log (t / 2) - 2 * C ≤ (xiSliceLogDeriv t R).re
      ∧ (xiSliceLogDeriv t R).re ≤ Real.log t + 2 * C := by
  set s : ℂ := 1 / 2 + (R : ℂ) + (t : ℂ) * I with hs
  have hc : (1 / 2 : ℂ) + (R : ℂ) - (t : ℂ) * I = (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext <;> simp
  have hL : xiSliceLogDeriv t R = logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s) := by
    unfold xiSliceLogDeriv; rw [hc, logDeriv_xi_conj_xiLogDerivSymmetry]
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have h1 : t ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; rw [hsim, abs_of_pos (by linarith)] at this; exact this
  have h2 : ‖s‖ ≤ 2 * t := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsre, hsim, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  obtain ⟨-, hlo, hhi⟩ := logDeriv_xi_annulus_bounds_of_stirling (s := s) (m₁ := t) (m₂ := 2 * t)
    (by rw [hsre]; linarith) hE (by linarith) h1 h2
  rw [hL]
  have hre : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).re = 2 * (logDeriv xi s).re := by
    simp; ring
  have him : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).im = 0 := by simp
  rw [hre, him]
  have e : 2 * t / 2 = t := by ring
  rw [e] at hhi
  refine ⟨rfl, by linarith, by linarith⟩

/-- The saddle-disc constant on the radius-`r` disc with Stirling constant `C`. -/
def xiSliceDiscConstantStrip (r C t R : ℝ) : ℝ :=
  r * (Real.log (3 * t / 2) + Real.pi / 2 + 2 * C) + R * (Real.log 4 + Real.pi + 4 * C)

/-- **Saddle-arc control with the saddle disc in the strip.** If the slice product has no zero on
an open `U ⊇ {|w − R| ≤ r}` and the Stirling hypothesis holds on the disc, the bounds of
`HTGeometry.saddleArc_bounds` hold with `M = xiSliceDiscConstantStrip r C t R`. -/
theorem xiSlice_saddleArc_bounds_strip {t R r C θ : ℝ} {U : Set ℂ} (hUo : IsOpen U)
    (hU : ∀ w ∈ U, xiSliceProduct t w ≠ 0) (hball : closedBall (R : ℂ) r ⊆ U) (hr : 0 < r)
    (hr1 : r ≤ 1 / 2) (ht : 8 ≤ t) (hrR : r ≤ R) (hRt : R ≤ t / 2)
    (hS : XiSliceStirling t C (closedBall (R : ℂ) r)) (hθ0 : 0 ≤ θ) (hθ : R * θ ≤ r / 2) :
    ‖HTGeometry.saddleArc (xiSliceProduct t) R
        (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) + 32 * xiSliceDiscConstantStrip r C t R / r ^ 2 * R ^ 2 * θ ^ 3 / 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * xiSliceDiscConstantStrip r C t R / r ^ 2 * R ^ 2 * θ ^ 3 / 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 32 * xiSliceDiscConstantStrip r C t R / r ^ 2 * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * xiSliceDiscConstantStrip r C t R / r ^ 2 * R ^ 2 * θ ^ 3 / 3)
        ≤ (HTGeometry.saddleArc (xiSliceProduct t) R
            (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ).re) := by
  have hR0 : 0 < R := by linarith
  have hRU : (R : ℂ) ∈ U := hball (mem_closedBall_self hr.le)
  apply HTGeometry.saddleArc_bounds hUo (differentiable_xiSliceProduct t).differentiableOn
    hU hR0 hr hball
  · intro w hw
    rw [scaledLogDeriv_xiSliceProduct_of_ne (hU w (hball hw)),
      scaledLogDeriv_xiSliceProduct_of_ne (hU _ hRU)]
    obtain ⟨h1, h2⟩ := xiSliceLogDeriv_disc_bounds_strip hr1 ht hrR hRt hS hw
    have hwR : ‖w - R‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hw
    have e : w * xiSliceLogDeriv t w - R * xiSliceLogDeriv t R
        = (w - R) * xiSliceLogDeriv t w + R * (xiSliceLogDeriv t w - xiSliceLogDeriv t R) := by ring
    rw [e]
    calc _ ≤ ‖(w - R) * xiSliceLogDeriv t w‖ + ‖(R : ℂ) * (xiSliceLogDeriv t w - xiSliceLogDeriv t R)‖ :=
          norm_add_le _ _
      _ = ‖w - R‖ * ‖xiSliceLogDeriv t w‖ + R * ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
      _ ≤ r * (Real.log (3 * t / 2) + Real.pi / 2 + 2 * C)
          + R * (Real.log 4 + Real.pi + 4 * C) := by
          gcongr
      _ = xiSliceDiscConstantStrip r C t R := by unfold xiSliceDiscConstantStrip; ring
  · intro x hx
    exact im_scaledLogDeriv_xiSliceProduct_ofReal_of_ne (hU _ hx)
  · exact hθ0
  · exact hθ

/-- **The saddle slope in the strip.** `|F'(R) − L(R)| ≤ R(log 4 + π + 4C)/r`. -/
theorem xiSlice_saddleSlope_bounds_strip {t R r C : ℝ} {U : Set ℂ} (hUo : IsOpen U)
    (hU : ∀ w ∈ U, xiSliceProduct t w ≠ 0) (hball : closedBall (R : ℂ) r ⊆ U) (hr : 0 < r)
    (hr1 : r ≤ 1 / 2) (ht : 8 ≤ t) (hrR : r ≤ R) (hRt : R ≤ t / 2)
    (hS : XiSliceStirling t C (closedBall (R : ℂ) r)) :
    Real.log (t / 2) - 2 * C - R * (Real.log 4 + Real.pi + 4 * C) / r
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
    ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ≤ Real.log t + 2 * C + R * (Real.log 4 + Real.pi + 4 * C) / r := by
  have hR0 : 0 < R := by linarith
  have hRU : (R : ℂ) ∈ U := hball (mem_closedBall_self hr.le)
  have hLd := differentiableOn_xiSliceLogDeriv_of hU
  have hev : HTGeometry.scaledLogDeriv (xiSliceProduct t) =ᶠ[nhds (R : ℂ)]
      fun w => w * xiSliceLogDeriv t w := by
    filter_upwards [hUo.mem_nhds hRU] with w hw
    exact scaledLogDeriv_xiSliceProduct_of_ne (hU w hw)
  have hLR : HasDerivAt (xiSliceLogDeriv t) (deriv (xiSliceLogDeriv t) R) R :=
    (hLd.differentiableAt (hUo.mem_nhds hRU)).hasDerivAt
  have hderiv : deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R
      = xiSliceLogDeriv t R + R * deriv (xiSliceLogDeriv t) R := by
    rw [hev.deriv_eq]
    have := (hasDerivAt_id' (R : ℂ)).mul hLR
    exact this.deriv.trans (by ring)
  have hcauchy : ‖deriv (xiSliceLogDeriv t) R‖ ≤ (Real.log 4 + Real.pi + 4 * C) / r :=
    HTGeometry.norm_deriv_le_of_norm_sub_le hLd (c := (R : ℂ)) hr hball
      (fun z hz => (xiSliceLogDeriv_disc_bounds_strip hr1 ht hrR hRt hS
        (sphere_subset_closedBall hz)).2)
  have hSR := (hS R (mem_closedBall_self hr.le)).1
  obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds_strip ht hR0.le hRt hSR
  have hRd : |(R * deriv (xiSliceLogDeriv t) R : ℂ).re|
      ≤ R * (Real.log 4 + Real.pi + 4 * C) / r := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    calc R * ‖deriv (xiSliceLogDeriv t) R‖
        ≤ R * ((Real.log 4 + Real.pi + 4 * C) / r) := by gcongr
      _ = R * (Real.log 4 + Real.pi + 4 * C) / r := by ring
  rw [hderiv, Complex.add_re]
  have := abs_le.mp hRd
  constructor <;> linarith [this.1, this.2]

/-- **Existence of the saddle radius in the strip.** -/
theorem exists_saddle_radius_strip {t a b C : ℝ} {U : Set ℂ} (ht : 8 ≤ t) (ha : 0 ≤ a)
    (hab : a ≤ b) (hbt : b ≤ t / 2) (hU : ∀ w ∈ U, xiSliceProduct t w ≠ 0)
    (hIcc : ∀ R ∈ Set.Icc a b, (R : ℂ) ∈ U)
    (hE : ∀ R ∈ Set.Icc a b, ‖logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I)
      - Complex.log ((1 / 2 + (R : ℂ) + (t : ℂ) * I) / 2) / 2‖ ≤ C) {k : ℕ}
    (hlo : a * (Real.log t + 2 * C) ≤ 2 * (k : ℝ))
    (hhi : 2 * (k : ℝ) ≤ b * (Real.log (t / 2) - 2 * C)) :
    ∃ R ∈ Set.Icc a b, (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (k : ℝ) := by
  set φ : ℝ → ℝ := fun R => R * (xiSliceLogDeriv t R).re with hφ
  have hcont : ContinuousOn φ (Set.Icc a b) := by
    have hL : ContinuousOn (fun R : ℝ => xiSliceLogDeriv t (R : ℂ)) (Set.Icc a b) :=
      (differentiableOn_xiSliceLogDeriv_of hU).continuousOn.comp
        Complex.continuous_ofReal.continuousOn hIcc
    exact continuousOn_id.mul (Complex.continuous_re.comp_continuousOn hL)
  have ha' : φ a ≤ 2 * k := by
    obtain ⟨-, -, hhia⟩ := xiSliceLogDeriv_real_bounds_strip ht ha (by linarith)
      (hE a ⟨le_rfl, hab⟩)
    simp only [hφ]
    nlinarith
  have hb' : 2 * k ≤ φ b := by
    obtain ⟨-, hlob, -⟩ := xiSliceLogDeriv_real_bounds_strip ht (by linarith) hbt
      (hE b ⟨hab, le_rfl⟩)
    simp only [hφ]
    nlinarith
  obtain ⟨R, hR, hRk⟩ := intermediate_value_Icc hab hcont ⟨ha', hb'⟩
  refine ⟨R, hR, ?_⟩
  rw [scaledLogDeriv_xiSliceProduct_of_ne (hU _ (hIcc R hR))]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact hRk

/-- **Positivity at one height from strip saddle data.** Let `0 < r ≤ 1/8`, `2r ≤ R₁`,
`K = R₁/(2r)`, and let `R ∈ [2r, R₁]` be the saddle radius of the order `2k` at height `t`, with the slice product
zero-free on an open `U ⊇ {|w − R| ≤ r}` and the Stirling hypothesis with constant `C ≥ 0` on that
disc. If the saddle slope lies in `[(9/10)u, 2u]`, the disc constant is at most `2ru`, the arc beyond
`1/(1000K)` is bounded by `E`, and `Λ = Ru` satisfies the three scale conditions with
`(π/2)E ≤ Λ^{−1/2}/10`, then `c_{2k}(t) > 0`. -/
theorem xiSliceCoeff_pos_of_saddle_strip {r R₁ K t u R E C : ℝ} {k : ℕ} {U : Set ℂ}
    (hUo : IsOpen U) (hU : ∀ w ∈ U, xiSliceProduct t w ≠ 0) (hball : closedBall (R : ℂ) r ⊆ U)
    (hS : XiSliceStirling t C (closedBall (R : ℂ) r)) (hC : 0 ≤ C) (hr : 0 < r)
    (hr8 : r ≤ 1 / 8) (hR₁ : 2 * r ≤ R₁) (hKdef : K = R₁ / (2 * r)) (ht8 : 8 ≤ t)
    (hu0 : 0 < u) (hRa : 2 * r ≤ R) (hRb : R ≤ R₁) (hRt : R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (k : ℝ))
    (hF₁lo : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re)
    (hF₁hi : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * u)
    (hKd : xiSliceDiscConstantStrip r C t R ≤ 2 * r * u)
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi / 2 → ‖sliceArc t R k θ‖ ≤ E)
    (hΛ1 : 1 ≤ R * u)
    (hE1 : (R * u) ^ (1 / 2 : ℝ) * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8) < 50)
    (hE3 : (R * u) ^ (-(2 / 5) : ℝ) < 1 / (1000 * K))
    (hE4 : (R * u) ^ (-(1 / 5) : ℝ) < 3 / (2 * (1 + 128 * K)))
    (hEt : Real.pi / 2 * E ≤ (R * u) ^ (-(1 / 2) : ℝ) / 10) :
    0 < xiSliceCoeff t (2 * k) := by
  have hR0 : 0 < R := by linarith
  have hR₁0 : 0 < R₁ := by linarith
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  have hKd0 : 0 ≤ xiSliceDiscConstantStrip r C t R := by
    unfold xiSliceDiscConstantStrip
    have h1 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
    have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    exact add_nonneg (mul_nonneg hr.le (by linarith [Real.pi_pos]))
      (mul_nonneg hR0.le (by linarith [Real.pi_pos]))
  obtain ⟨D, hDdef⟩ : ∃ D, D = xiSliceDiscConstantStrip r C t R * R / (4 * r ^ 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact div_nonneg (mul_nonneg hKd0 hR0.le) (by positivity)
  have hD : D ≤ K * u := by
    rw [hDdef, div_le_iff₀ (by positivity), hKdef]
    have e : R₁ / (2 * r) * u * (4 * r ^ 2) = 2 * r * u * R₁ := by field_simp; ring
    rw [e]
    calc xiSliceDiscConstantStrip r C t R * R ≤ xiSliceDiscConstantStrip r C t R * R₁ :=
          mul_le_mul_of_nonneg_left hRb hKd0
      _ ≤ 2 * r * u * R₁ := mul_le_mul_of_nonneg_right hKd hR₁0.le
  have hcub : ∀ θ : ℝ, 32 * xiSliceDiscConstantStrip r C t R / r ^ 2 * R ^ 2 * θ ^ 3 / 3
      = 128 / 3 * (R * D) * θ ^ 3 := by
    intro θ; rw [hDdef]; field_simp; ring
  have hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖sliceArc t R k θ‖ ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
          * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
          + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 128 / 3 * (R * D) * θ ^ 3) ≤ (sliceArc t R k θ).re) := by
    intro θ hθ0 hθ
    have hRθ : R * θ ≤ r / 2 := by
      have h1 : R * θ ≤ R₁ * θ := mul_le_mul_of_nonneg_right hRb hθ0
      have h2 : R₁ * θ ≤ R₁ * (1 / (1000 * K)) := mul_le_mul_of_nonneg_left hθ hR₁0.le
      have h3 : R₁ * (1 / (1000 * K)) = r / 500 := by rw [hKdef]; field_simp; ring
      linarith
    have h := xiSlice_saddleArc_bounds_strip hUo hU hball hr (by linarith) ht8 (by linarith) hRt
      hS hθ0 hRθ
    rw [hsad, hcub θ] at h
    exact h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * u := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hE1 hE3 hE4 hEt
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hδ₀] at hEt
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδθ : δ ≤ 1 / (1000 * K) := by rw [hδ]; exact hE3.le
  have hcore : Λ * δ₀ ^ 2 ≤ 1 := by rw [hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : (1 + 128 * K) * Λ * δ ^ 3 ≤ 3 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [hδ, mul_assoc, this]
    have h4 := hE4.le
    rw [le_div_iff₀ (by positivity)] at h4
    linarith
  have hhalf : Λ ^ (1 / 2 : ℝ) * δ₀ = 1 := by
    rw [hδ₀]; exact rpow_half_mul_rpow_neg_half_eq_one hΛ0
  have hmid : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := by
    have e : -Λ * δ ^ 2 / 8 = -(Λ ^ (1 / 5 : ℝ)) / 8 := by
      rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
    rw [e]
    have h1 : Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) ≤ 50 * δ₀ := by
      calc Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8)
          = Λ ^ (1 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) * δ₀ := by
            rw [mul_comm (Λ ^ (1 / 2 : ℝ)), mul_assoc, hhalf, mul_one]
        _ ≤ 50 * δ₀ := by gcongr
    linarith only [h1]
  have hSc : Continuous fun θ : ℝ => sliceArc t R k θ := by
    have hg := differentiable_xiSliceProduct t
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [sliceArc, HTGeometry.saddleArc]
    fun_prop
  subst hΛ
  have hpos := quarter_integral_pos_of_arc_bounds_scaled hSc hR0 hu0 hK1 hF₁lo hF₁hi hD hD0
    hb htail hδ₀pos hδ₀δ hδθ hcore hphase hmid hEt
  have hRU : (R : ℂ) ∈ U := hball (mem_closedBall_self hr.le)
  rw [xiSliceCoeff_two_mul_eq_quarter_of_ne t k hR0 (hU _ hRU), Complex.zero_lt_real]
  have hxi0 := (xi_ne_zero_of_xiSliceProduct_ne_zero (hU _ hRU)).1
  have hxi : 0 < ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    refine norm_pos_iff.mpr ?_
    have e : ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I = 1 / 2 + (R : ℂ) + (t : ℂ) * I := by push_cast; ring
    rw [e]; exact hxi0
  have hfac : 0 < 2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * k)) := by
    positivity
  exact mul_pos hfac hpos

end

end RHTower
