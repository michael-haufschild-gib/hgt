import GaloisForLFunctions.RHTower.ZetaDiscBoundaryJensenInequality
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The Balazard–Saias–Yor inequality

For every finite set `Z` of zeros of `ζ` with `Re ρ > ½`,

`Σ_{ρ ∈ Z} log (|ρ| / |1 - ρ|) ≤ (1/2π) ∫_ℝ log |ζ(½ + it)| dt / (¼ + t²)`,

and the integrand is integrable.  Every term on the left is positive, so the integral is
nonnegative, and if it is `≤ 0` the Riemann hypothesis holds.

The boundary circle of `zetaDisc` is carried to the critical line by `θ(t) = π - 2 arctan(2t)`:
`1/(1 - e^{iθ(t)}) = ½ + it` and `|dθ/dt| = 1/(¼ + t²)`.  The factor `s - 1` of
`zetaEntire s = (s - 1) ζ(s)` contributes `∫ log(¼ + t²) dt/(¼ + t²) = 0`, which is the vanishing
of the circle average of `log |w - 1|` on the unit circle.
-/

open Complex Metric Real MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The angle `θ(t) = π - 2 arctan(2t)` of the boundary point corresponding to `½ + it`. -/
def criticalLineAngle (t : ℝ) : ℝ := π - 2 * Real.arctan (2 * t)

theorem cos_criticalLineAngle (t : ℝ) :
    Real.cos (criticalLineAngle t) = (4 * t ^ 2 - 1) / (1 + 4 * t ^ 2) := by
  have h : 0 < 1 + (2 * t) ^ 2 := by positivity
  unfold criticalLineAngle
  rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow,
    Real.sq_sqrt h.le]
  field_simp
  ring

theorem sin_criticalLineAngle (t : ℝ) :
    Real.sin (criticalLineAngle t) = 4 * t / (1 + 4 * t ^ 2) := by
  have h : 0 < 1 + (2 * t) ^ 2 := by positivity
  have hs : √(1 + (2 * t) ^ 2) * √(1 + (2 * t) ^ 2) = 1 + (2 * t) ^ 2 := Real.mul_self_sqrt h.le
  have hs0 : 0 < √(1 + (2 * t) ^ 2) := Real.sqrt_pos.mpr h
  unfold criticalLineAngle
  rw [Real.sin_pi_sub, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan,
    show 2 * (2 * t / √(1 + (2 * t) ^ 2)) * (1 / √(1 + (2 * t) ^ 2))
      = 4 * t / (√(1 + (2 * t) ^ 2) * √(1 + (2 * t) ^ 2)) by field_simp; ring, hs]
  ring

/-- The boundary point of angle `θ(t)` is carried to `½ + it`. -/
theorem halfPlaneOfDisc_circleMap_criticalLineAngle (t : ℝ) :
    halfPlaneOfDisc (circleMap 0 1 (criticalLineAngle t)) = 1 / 2 + t * I := by
  unfold halfPlaneOfDisc
  refine inv_eq_of_mul_eq_one_right ?_
  have hre : (circleMap 0 1 (criticalLineAngle t)).re = (4 * t ^ 2 - 1) / (1 + 4 * t ^ 2) := by
    rw [← cos_criticalLineAngle]; simp [circleMap, Complex.exp_ofReal_mul_I_re]
  have him : (circleMap 0 1 (criticalLineAngle t)).im = 4 * t / (1 + 4 * t ^ 2) := by
    rw [← sin_criticalLineAngle]; simp [circleMap, Complex.exp_ofReal_mul_I_im]
  have h : 0 < 1 + 4 * t ^ 2 := by positivity
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, hre, Complex.add_re,
      Complex.div_ofNat_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.one_im, him, Complex.add_im, Complex.div_ofNat_im,
      Complex.mul_I_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  · simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, hre, Complex.add_re,
      Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      Complex.sub_im, Complex.one_im, him, Complex.add_im, Complex.div_ofNat_im,
      Complex.I_re, Complex.I_im]
    field_simp
    ring

theorem hasDerivAt_criticalLineAngle (t : ℝ) :
    HasDerivAt criticalLineAngle (-(4 / (1 + 4 * t ^ 2))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have h2 := (Real.hasDerivAt_arctan (2 * t)).comp t h1
  have h3 := (h2.const_mul 2).const_sub π
  unfold criticalLineAngle
  have e : -(4 / (1 + 4 * t ^ 2)) = -(2 * (1 / (1 + (2 * t) ^ 2) * 2)) := by
    field_simp; ring
  rw [e]
  exact h3

theorem strictAnti_criticalLineAngle : StrictAnti criticalLineAngle := by
  intro a b hab
  unfold criticalLineAngle
  have := Real.arctan_strictMono (by linarith : 2 * a < 2 * b)
  linarith

theorem image_criticalLineAngle : criticalLineAngle '' Set.univ = Set.Ioo 0 (2 * π) := by
  ext θ
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioo]
  constructor
  · rintro ⟨t, rfl⟩
    unfold criticalLineAngle
    have h1 := Real.arctan_lt_pi_div_two (2 * t)
    have h2 := Real.neg_pi_div_two_lt_arctan (2 * t)
    constructor <;> linarith
  · rintro ⟨h0, h2⟩
    refine ⟨Real.tan ((π - θ) / 2) / 2, ?_⟩
    unfold criticalLineAngle
    rw [show 2 * (Real.tan ((π - θ) / 2) / 2) = Real.tan ((π - θ) / 2) by ring,
      Real.arctan_tan (by linarith) (by linarith)]
    ring

theorem abs_deriv_criticalLineAngle (t : ℝ) : |-(4 / (1 + 4 * t ^ 2))| = 1 / (1 / 4 + t ^ 2) := by
  rw [abs_neg, abs_of_pos (by positivity)]
  field_simp

/-- **The unit circle as the critical line.**
`circleAverage g 0 1 = (1/2π) ∫ g(e^{iθ(t)}) dt/(¼ + t²)`. -/
theorem circleAverage_eq_integral_criticalLine (g : ℂ → ℝ) :
    circleAverage g 0 1
      = (2 * π)⁻¹ * ∫ t : ℝ, g (circleMap 0 1 (criticalLineAngle t)) / (1 / 4 + t ^ 2) := by
  rw [circleAverage_def, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, ← image_criticalLineAngle,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_criticalLineAngle x).hasDerivWithinAt)
      strictAnti_criticalLineAngle.injective.injOn (fun θ => g (circleMap 0 1 θ)),
    Measure.restrict_univ, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, abs_deriv_criticalLineAngle]
  ring

theorem circleIntegrable_iff_integrable_criticalLine (g : ℂ → ℝ) :
    CircleIntegrable g 0 1
      ↔ Integrable (fun t : ℝ => g (circleMap 0 1 (criticalLineAngle t)) / (1 / 4 + t ^ 2)) := by
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity),
    integrableOn_Ioc_iff_integrableOn_Ioo, ← image_criticalLineAngle,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_criticalLineAngle x).hasDerivWithinAt)
      strictAnti_criticalLineAngle.injective.injOn (fun θ => g (circleMap 0 1 θ)),
    integrableOn_univ]
  refine integrable_congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, abs_deriv_criticalLineAngle]
  ring


theorem norm_half_add_mul_I (t : ℝ) : ‖(1 / 2 : ℂ) + t * I‖ = √(1 / 4 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im,
    Complex.div_ofNat_im, Complex.one_im, Complex.mul_im]
  ring

theorem norm_half_add_mul_I_sub_one (t : ℝ) : ‖(1 / 2 : ℂ) + t * I - 1‖ = √(1 / 4 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.one_im, Complex.mul_im]
  ring

theorem log_norm_circleMap_criticalLineAngle_sub_one (t : ℝ) :
    Real.log ‖circleMap 0 1 (criticalLineAngle t) - 1‖ = -(Real.log (1 / 4 + t ^ 2) / 2) := by
  have h := halfPlaneOfDisc_circleMap_criticalLineAngle t
  unfold halfPlaneOfDisc at h
  have h1 : (1 - circleMap 0 1 (criticalLineAngle t)) = ((1 / 2 : ℂ) + t * I)⁻¹ := by
    rw [← h, inv_inv]
  rw [← norm_neg, neg_sub, h1, norm_inv, norm_half_add_mul_I, Real.log_inv,
    Real.log_sqrt (by positivity)]

/-- `∫_ℝ log(¼ + t²) dt/(¼ + t²) = 0`. -/
theorem integrable_and_integral_log_criticalLine_weight :
    Integrable (fun t : ℝ => Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2)) ∧
      ∫ t : ℝ, Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2) = 0 := by
  set g : ℂ → ℝ := fun w => Real.log ‖w - 1‖ with hg
  have hci : CircleIntegrable g 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (f := fun w : ℂ => w - 1)
      (fun w _ => (analyticAt_id.sub analyticAt_const).meromorphicAt)
  have havg : circleAverage g 0 1 = 0 := circleAverage_log_norm_sub_const₁ (by simp)
  have key : (fun t : ℝ => g (circleMap 0 1 (criticalLineAngle t)) / (1 / 4 + t ^ 2))
      = fun t => (-1 / 2 : ℝ) * (Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2)) := by
    funext t
    simp only [hg, log_norm_circleMap_criticalLineAngle_sub_one]
    ring
  have hint := (circleIntegrable_iff_integrable_criticalLine g).mp hci
  rw [key] at hint
  have hint' : Integrable (fun t : ℝ => Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2)) := by
    have := hint.const_mul (-2)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    ring
  refine ⟨hint', ?_⟩
  have h := circleAverage_eq_integral_criticalLine g
  rw [havg, key, integral_const_mul] at h
  have hπ : (2 * π)⁻¹ ≠ 0 := by positivity
  have : (-1 / 2 : ℝ) * ∫ t : ℝ, Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2) = 0 := by
    rcases mul_eq_zero.mp h.symm with h0 | h0
    · exact absurd h0 hπ
    · exact h0
  linarith

/-- The zeros of an entire function that is not identically zero form a countable set. -/
theorem countable_setOf_eq_zero_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ}
    (hx : f x ≠ 0) : {s : ℂ | f s = 0}.Countable := by
  have han : AnalyticOnNhd ℂ f Set.univ := fun s _ => hf.analyticAt s
  have hcod := han.preimage_zero_mem_codiscrete hx
  have hdisc := isDiscrete_of_codiscreteWithin (U := Set.univ) (s := f ⁻¹' {0}) hcod
  have := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  rw [Set.inter_univ] at this
  exact this

/-- The zeros of `(s - 1) ζ(s)` form a countable set. -/
theorem countable_setOf_zetaEntire_eq_zero : {s : ℂ | zetaEntire s = 0}.Countable :=
  countable_setOf_eq_zero_of_differentiable differentiable_zetaEntire
    (x := 1) (by rw [zetaEntire_eval_one]; exact one_ne_zero)

/-- **The Balazard–Saias–Yor inequality.**  For finitely many zeros `ρ` of `ζ` with `Re ρ > ½`,
`Σ log (|ρ|/|1 - ρ|) ≤ (1/2π) ∫ log |ζ(½ + it)| dt/(¼ + t²)`, and the integrand is integrable. -/
theorem integrable_and_sum_log_le_integral_log_norm_zeta {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re) :
    Integrable (fun t : ℝ => Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) ∧
      ∑ ρ ∈ Z, Real.log (‖ρ‖ / ‖1 - ρ‖)
        ≤ (2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  have hρ0 : ∀ ρ ∈ Z, ρ ≠ 0 := by
    intro ρ hρ h0; have := (hZ ρ hρ).2; rw [h0, Complex.zero_re] at this; linarith
  set U := Z.image (fun ρ : ℂ => 1 - ρ⁻¹) with hUdef
  have hU : ∀ u ∈ U, zetaDisc u = 0 ∧ ‖u‖ < 1 := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h1, _, h3⟩ := zetaDisc_one_sub_inv (hZ ρ hρ).1 (hZ ρ hρ).2
    exact ⟨h1, h3⟩
  obtain ⟨hci, hle⟩ := circleIntegrable_and_sum_log_le_circleAverage_zetaDisc hU
  set H : ℝ → ℝ := fun t => Real.log ‖zetaEntire (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) with hH
  have hHeq : (fun t : ℝ => Real.log ‖zetaDisc (circleMap 0 1 (criticalLineAngle t))‖
      / (1 / 4 + t ^ 2)) = H := by
    funext t
    simp only [hH, zetaDisc, halfPlaneOfDisc_circleMap_criticalLineAngle]
  have hHint : Integrable H := by
    have := (circleIntegrable_iff_integrable_criticalLine _).mp hci
    rwa [hHeq] at this
  have hHavg : circleAverage (fun w => Real.log ‖zetaDisc w‖) 0 1 = (2 * π)⁻¹ * ∫ t, H t := by
    rw [circleAverage_eq_integral_criticalLine, hHeq]
  obtain ⟨hWint, hW0⟩ := integrable_and_integral_log_criticalLine_weight
  have hcount : {t : ℝ | riemannZeta (1 / 2 + t * I) = 0}.Countable := by
    have hinj : Function.Injective (fun t : ℝ => (1 / 2 : ℂ) + t * I) := by
      intro a b hab
      have := congrArg Complex.im hab
      simpa using this
    refine (countable_setOf_zetaEntire_eq_zero.preimage hinj).mono fun t ht => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht ⊢
    have hne : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; norm_num at this
    rw [zetaEntire_eq hne, ht, mul_zero]
  have hae : ∀ᵐ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)
      = H t - (1 / 2) * (Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2)) := by
    have h0 : volume {t : ℝ | riemannZeta (1 / 2 + t * I) = 0} = 0 := hcount.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with t ht
    have hne : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; norm_num at this
    have hsub : (1 / 2 : ℂ) + t * I - 1 ≠ 0 := sub_ne_zero.mpr hne
    simp only [hH]
    rw [zetaEntire_eq hne, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hsub)
      (norm_ne_zero_iff.mpr ht), norm_half_add_mul_I_sub_one, Real.log_sqrt (by positivity)]
    ring
  have hZint : Integrable (fun t : ℝ => Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) :=
    (hHint.sub (hWint.const_mul (1 / 2))).congr (hae.mono fun t ht => ht.symm)
  have hZeq : ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) = ∫ t, H t := by
    rw [integral_congr_ae hae, integral_sub hHint (hWint.const_mul (1 / 2)), integral_const_mul,
      hW0, mul_zero, sub_zero]
  refine ⟨hZint, ?_⟩
  rw [hZeq, ← hHavg]
  have hsum : ∑ u ∈ U, Real.log (1 / ‖u‖) = ∑ ρ ∈ Z, Real.log (‖ρ‖ / ‖1 - ρ‖) := by
    rw [hUdef, Finset.sum_image]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      obtain ⟨_, h2, _⟩ := zetaDisc_one_sub_inv (hZ ρ hρ).1 (hZ ρ hρ).2
      rw [h2, one_div_div]
    · intro a ha b hb hab
      have : a⁻¹ = b⁻¹ := by simpa using hab
      exact inv_injective this
  rw [← hsum]
  exact hle

/-- **Nonnegativity of the Balazard–Saias–Yor integral.**
`∫ log |ζ(½ + it)| dt/(¼ + t²) ≥ 0`. -/
theorem integral_log_norm_zeta_criticalLine_nonneg :
    0 ≤ ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  have h := (integrable_and_sum_log_le_integral_log_norm_zeta (Z := ∅) (by simp)).2
  rw [Finset.sum_empty] at h
  have hπ : 0 < (2 * π)⁻¹ := by positivity
  nlinarith

/-- **The Balazard–Saias–Yor criterion, one-sided form.**  If
`∫ log |ζ(½ + it)| dt/(¼ + t²) ≤ 0`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_integral_log_norm_zeta_criticalLine_le_zero
    (h : ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) ≤ 0) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  have hle := (integrable_and_sum_log_le_integral_log_norm_zeta (Z := {s})
    (fun ρ hρ => by rw [Finset.mem_singleton] at hρ; subst hρ; exact ⟨hz, hs⟩)).2
  rw [Finset.sum_singleton] at hle
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  have hlt : ‖1 - s‖ < ‖s‖ := by
    have h1 : ‖1 - s‖ ^ 2 < ‖s‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  have hpos0 : 0 < ‖1 - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs1))
  have hpos : 0 < Real.log (‖s‖ / ‖1 - s‖) :=
    Real.log_pos (by rw [one_lt_div hpos0]; exact hlt)
  have hπ : 0 < (2 * π)⁻¹ := by positivity
  nlinarith

end

end RHTower
