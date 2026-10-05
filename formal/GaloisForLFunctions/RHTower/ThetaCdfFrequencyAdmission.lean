import GaloisForLFunctions.RHTower.ThetaCdfFixedShiftAction

/-!
# Frequency admission of the theta CDF action is discrete

For a real frequency `r` put `Φ(r) = ∫_ℝ (1 − cos(2πr F(x))) dx` with the theta CDF `F`.  The
nonnegative integral is finite if and only if `r ∈ ℤ`: for non-integral `r` the integrand tends
to `1 − cos 2πr > 0` as `x → +∞`, while for integral `r` it is the integrable CDF-action
integrand.  The theta clock is intrinsically a lattice action.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

/-- The real-frequency CDF-action integrand `1 − cos(2πr F(x))`. -/
def cdfFrequencyIntegrand (r x : ℝ) : ℝ := 1 - Real.cos (2 * Real.pi * r * thetaSource.cdfFun x)

theorem cdfFrequencyIntegrand_nonneg (r x : ℝ) : 0 ≤ cdfFrequencyIntegrand r x :=
  sub_nonneg.2 (Real.cos_le_one _)

theorem continuous_cdfFrequencyIntegrand (r : ℝ) : Continuous (cdfFrequencyIntegrand r) :=
  continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul thetaSource.continuous_cdfFun))

theorem one_sub_cos_two_pi_mul_pos {r : ℝ} (hr : ∀ n : ℤ, r ≠ n) : 0 < 1 - Real.cos (2 * Real.pi * r) := by
  have hne : Real.cos (2 * Real.pi * r) ≠ 1 := by
    rw [Ne, Real.cos_eq_one_iff]
    rintro ⟨n, hn⟩
    exact hr n (by nlinarith [Real.pi_pos])
  have := Real.cos_le_one (2 * Real.pi * r)
  exact sub_pos.2 (lt_of_le_of_ne this hne)

theorem tendsto_cdfFrequencyIntegrand_atTop (r : ℝ) :
    Tendsto (cdfFrequencyIntegrand r) atTop (𝓝 (1 - Real.cos (2 * Real.pi * r))) := by
  have h := thetaSource.tendsto_cdfFun_atTop
  have hc : Continuous fun u : ℝ => 1 - Real.cos (2 * Real.pi * r * u) :=
    continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have := (hc.tendsto 1).comp h
  simp only [Function.comp_def, mul_one] at this
  exact this

/-- **Frequency admission is discrete**: `x ↦ 1 − cos(2πr F(x))` is integrable iff `r ∈ ℤ`. -/
theorem integrable_cdfFrequencyIntegrand_iff (r : ℝ) :
    Integrable (cdfFrequencyIntegrand r) ↔ ∃ n : ℤ, r = n := by
  constructor
  · intro hint
    by_contra hr
    push Not at hr
    set c := 1 - Real.cos (2 * Real.pi * r)
    have hc : 0 < c := one_sub_cos_two_pi_mul_pos hr
    obtain ⟨X, hX⟩ := eventually_atTop.1
      ((tendsto_cdfFrequencyIntegrand_atTop r).eventually (Ioi_mem_nhds (half_lt_self hc)))
    have hon : IntegrableOn (fun _ : ℝ => c / 2) (Ici X) := by
      refine (hint.integrableOn (s := Ici X)).mono' aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hc)]
      exact (hX x hx).le
    rw [integrableOn_const_iff] at hon
    rcases hon with h0 | hfin
    · have : (c / 2 : ℝ) ≠ 0 := (half_pos hc).ne'
      exact this (enorm_eq_zero.1 h0)
    · rw [Real.volume_Ici] at hfin
      exact (lt_irrefl _ hfin)
  · rintro ⟨n, rfl⟩
    exact integrable_cdfAction_integrand n

/-- **The real-frequency action is finite iff `r ∈ ℤ`**:
`∫ (1 − cos(2πr F(x))) dx < ∞ ↔ r ∈ ℤ`. -/
theorem lintegral_cdfFrequencyIntegrand_lt_top_iff (r : ℝ) :
    ∫⁻ x, ENNReal.ofReal (cdfFrequencyIntegrand r x) < ⊤ ↔ ∃ n : ℤ, r = n := by
  rw [← integrable_cdfFrequencyIntegrand_iff]
  have hm : AEStronglyMeasurable (cdfFrequencyIntegrand r) :=
    (continuous_cdfFrequencyIntegrand r).aestronglyMeasurable
  rw [Integrable, and_iff_right hm,
    hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => cdfFrequencyIntegrand_nonneg r x)]

end

end RHTower
