import GaloisForLFunctions.Bottcher.FigureEight

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A measurable nonvanishing analytic germ has a measurable total representative of a local
analytic square root. -/
theorem exists_measurable_analyticAt_sq_eq
    {g : ℂ → ℂ} {z₀ : ℂ} (hgMeas : Measurable g)
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, Measurable h ∧ AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, h z ^ 2 = g z := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = g z₀ :=
    IsAlgClosed.exists_pow_nat_eq (g z₀) (by norm_num)
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    exact hg0 hs.symm
  set q : ℂ → ℂ := fun z => g z / g z₀ with hq
  have hqMeas : Measurable q := by
    rw [hq]
    fun_prop
  have hqan : AnalyticAt ℂ q z₀ := hg.div analyticAt_const hg0
  have hq0 : q z₀ = 1 := by rw [hq]; field_simp
  have hmem : ∀ᶠ z in nhds z₀, q z ∈ Metric.ball (1 : ℂ) 1 := by
    have hcont : ContinuousAt q z₀ := hqan.continuousAt
    have hball : Metric.ball (1 : ℂ) 1 ∈ nhds (q z₀) := by
      rw [hq0]
      exact Metric.ball_mem_nhds _ one_pos
    exact hcont.preimage_mem_nhds hball
  have hslit : Metric.ball (1 : ℂ) 1 ⊆ Complex.slitPlane := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hb : |w.re - 1| ≤ ‖w - 1‖ := by
      calc
        |w.re - 1| = |(w - 1).re| := by rw [Complex.sub_re, Complex.one_re]
        _ ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
    have hlt := abs_lt.mp (lt_of_le_of_lt hb hw)
    linarith [hlt.1]
  let h : ℂ → ℂ := fun z =>
    s * Complex.exp ((2 : ℂ)⁻¹ * Complex.log (q z))
  have hhMeas : Measurable h := by
    dsimp [h]
    fun_prop
  refine ⟨h, hhMeas, ?_, ?_, ?_⟩
  · have hld : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
      fun x hx => (Complex.hasDerivAt_log hx).differentiableAt.differentiableWithinAt
    have hla : AnalyticAt ℂ Complex.log (q z₀) :=
      (hld.analyticOnNhd Complex.isOpen_slitPlane) (q z₀)
        (hslit (by rw [hq0]; exact Metric.mem_ball_self one_pos))
    have hlogan : AnalyticAt ℂ (fun z => Complex.log (q z)) z₀ := hla.comp hqan
    exact analyticAt_const.mul ((analyticAt_const.mul hlogan).cexp)
  · show s * Complex.exp ((2 : ℂ)⁻¹ * Complex.log (q z₀)) ≠ 0
    rw [hq0, Complex.log_one, mul_zero, Complex.exp_zero, mul_one]
    exact hsne
  · filter_upwards [hmem] with z hz
    have hqz0 : q z ≠ 0 := by
      intro hz0
      rw [hz0, Metric.mem_ball, dist_eq_norm] at hz
      simp at hz
    have hqval : q z = g z / g z₀ := rfl
    change (s * Complex.exp ((2 : ℂ)⁻¹ * Complex.log (q z))) ^ 2 = g z
    rw [mul_pow, pow_two (Complex.exp ((2 : ℂ)⁻¹ * Complex.log (q z))),
      ← Complex.exp_add,
      show (2 : ℂ)⁻¹ * Complex.log (q z) + (2 : ℂ)⁻¹ * Complex.log (q z) =
        Complex.log (q z) by ring,
      Complex.exp_log hqz0, hqval, hs]
    field_simp

/-- A prescribed nonzero square root at the base point fixes the sign of the measurable local
analytic branch. -/
theorem exists_measurable_analyticAt_sq_eq_of_value
    {g : ℂ → ℂ} {z₀ s : ℂ} (hgMeas : Measurable g)
    (hg : AnalyticAt ℂ g z₀) (hs : s ^ 2 = g z₀) (hs0 : s ≠ 0) :
    ∃ h : ℂ → ℂ, Measurable h ∧ AnalyticAt ℂ h z₀ ∧ h z₀ = s ∧
      ∀ᶠ z in nhds z₀, h z ^ 2 = g z := by
  have hg0 : g z₀ ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero 2 hs0
  obtain ⟨h, hhMeas, hhan, hh0, hhsq⟩ :=
    exists_measurable_analyticAt_sq_eq hgMeas hg hg0
  have hh0sq : h z₀ ^ 2 = g z₀ := hhsq.self_of_nhds
  let c : ℂ := s / h z₀
  have hc2 : c ^ 2 = 1 := by
    dsimp [c]
    rw [div_pow, hh0sq, hs]
    exact div_self hg0
  let H : ℂ → ℂ := fun z => c * h z
  refine ⟨H, measurable_const.mul hhMeas,
    analyticAt_const.mul hhan, ?_, ?_⟩
  · dsimp [H, c]
    field_simp
  · filter_upwards [hhsq] with z hz
    dsimp [H]
    rw [mul_pow, hc2, one_mul, hz]

end

end GaloisForLFunctions.HTGeometry
