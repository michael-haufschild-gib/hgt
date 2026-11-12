import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeAtomsOfZetaAreItsDominantZeros

/-!
# Absolute logarithmic integrability gives Mellin holomorphy

Integrability for every real damping above a threshold suffices for a
holomorphic Mellin transform on that half-plane. A smaller damping absorbs
the time factor in the parameter derivative; no pointwise growth bound
on the arithmetic sequence is required.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The Mellin transform represented by the positive logarithmic staircase. -/
def oneSidedStepMellin (f : ℕ → ℝ) (s : ℂ) : ℂ :=
  s * ∫ u in Ioi (0 : ℝ), stepLaplaceIntegrand f s u

/-- Wherever the cell majorant is summable, the literal integral is the
usual summatory Mellin pairing. -/
theorem oneSidedStepMellin_eq_complexMellinPairing
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-s.re - 1)) :
    oneSidedStepMellin f s = TransHorizonIncidenceMechanics.complexMellinPairing f s := by
  have he : (∫ u in Ioi (0 : ℝ), stepLaplaceIntegrand f s u) =
      ∫ u : ℝ, stepLaplaceIntegrand f s u := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    exact stepLaplaceIntegrand_of_neg hf0 s (not_le.mp hu)
  rw [oneSidedStepMellin, he, integral_stepLaplaceIntegrand hf0 hs hsum]
  have hs0 : s ≠ 0 := by
    intro he
    rw [he, zero_re] at hs
    exact lt_irrefl 0 hs
  field_simp [hs0]

/-- Complex damping has the same norm as its real part. -/
theorem integrableOn_stepLaplaceIntegrand_of_real
    {f : ℕ → ℝ} {s : ℂ}
    (h : IntegrableOn (stepLaplaceIntegrand f (s.re : ℂ)) (Ioi 0)) :
    IntegrableOn (stepLaplaceIntegrand f s) (Ioi 0) := by
  apply h.norm.mono' (measurable_stepLaplaceIntegrand f s).aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [norm_stepLaplaceIntegrand, norm_stepLaplaceIntegrand, ofReal_re]

private theorem time_mul_exp_le {b c u : ℝ} (hbc : b < c) :
    u * Real.exp (-c * u) ≤ (c - b)⁻¹ * Real.exp (-b * u) := by
  have hg : 0 < c - b := sub_pos.mpr hbc
  have ht : u ≤ (c - b)⁻¹ * Real.exp ((c - b) * u) := by
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hg).2
    have hh := Real.add_one_le_exp ((c - b) * u)
    nlinarith only [hh]
  calc
    _ ≤ ((c - b)⁻¹ * Real.exp ((c - b) * u)) * Real.exp (-c * u) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, show (c - b) * u + -c * u = -b * u by ring]

/-- Every absolutely convergent open damping half-plane is a holomorphy
half-plane for the literal logarithmic integral. -/
theorem differentiableOn_oneSidedStepMellin
    {f : ℕ → ℝ} {θ : ℝ}
    (hint : ∀ c : ℝ, θ < c →
      IntegrableOn (stepLaplaceIntegrand f (c : ℂ)) (Ioi 0)) :
    DifferentiableOn ℂ (oneSidedStepMellin f) {s : ℂ | θ < s.re} := by
  intro z hz
  change θ < z.re at hz
  let r : ℝ := (z.re - θ) / 4
  let c : ℝ := z.re - 2 * r
  let V : Set ℂ := Metric.ball z r
  let D : ℂ → ℝ → ℂ := fun w u => -(u : ℂ) * stepLaplaceIntegrand f w u
  let B : ℝ → ℝ := fun u => r⁻¹ * ‖stepLaplaceIntegrand f (c : ℂ) u‖
  have hr : 0 < r := by dsimp only [r]; linarith only [hz]
  have hc : θ < c := by dsimp only [c, r]; linarith only [hz]
  have hV : V ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have hB : Integrable B (volume.restrict (Ioi 0)) := (hint c hc).norm.const_mul _
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (stepLaplaceIntegrand f w) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun w => (measurable_stepLaplaceIntegrand f w).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D z) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Measurable (fun u : ℝ => -(u : ℂ))).aestronglyMeasurable.mul
      (measurable_stepLaplaceIntegrand f z).aestronglyMeasurable
  have hbound : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ∀ w ∈ V, ‖D w u‖ ≤ B u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have habs : |w.re - z.re| < r := calc
      _ = |(w - z).re| := by rw [sub_re]
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
      _ = dist w z := (dist_eq_norm _ _).symm
      _ < r := hw
    have hwr : c ≤ w.re - r := by
      have hn := neg_abs_le (w.re - z.re)
      dsimp only [c]
      linarith only [habs, hn]
    have hm := time_mul_exp_le (u := u) (b := w.re - r) (by linarith only [hr] : w.re - r < w.re)
    rw [show w.re - (w.re - r) = r by ring] at hm
    have he : Real.exp (-(w.re - r) * u) ≤ Real.exp (-c * u) :=
      Real.exp_le_exp.mpr (by nlinarith only [hwr, (show 0 < u from hu)])
    dsimp only [D, B]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < u from hu), norm_stepLaplaceIntegrand,
      norm_stepLaplaceIntegrand, ofReal_re]
    calc
      _ = (u * Real.exp (-w.re * u)) * |f ⌊Real.exp u⌋₊| := by congr 2 <;> ring
      _ ≤ (r⁻¹ * Real.exp (-(w.re - r) * u)) * |f ⌊Real.exp u⌋₊| :=
        mul_le_mul_of_nonneg_right hm (abs_nonneg _)
      _ ≤ (r⁻¹ * Real.exp (-c * u)) * |f ⌊Real.exp u⌋₊| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hr.le)) (abs_nonneg _)
      _ = _ := by congr 2 <;> ring
  have hdiff : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ∀ w ∈ V,
      HasDerivAt (fun v : ℂ => stepLaplaceIntegrand f v u) (D w u) w := by
    exact Eventually.of_forall fun u w _ => by
      have hi : HasDerivAt (fun v : ℂ => -v * (u : ℂ)) (-(u : ℂ)) w := by
        simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul] using
          (hasDerivAt_id w).neg.mul_const (u : ℂ)
      exact (hi.cexp.mul_const (f ⌊Real.exp u⌋₊ : ℂ)).congr_deriv (by
        dsimp only [D, stepLaplaceIntegrand]
        ring)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmeas
    (integrableOn_stepLaplaceIntegrand_of_real (hint z.re hz))
    hDmeas hbound hB hdiff).2
  exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
