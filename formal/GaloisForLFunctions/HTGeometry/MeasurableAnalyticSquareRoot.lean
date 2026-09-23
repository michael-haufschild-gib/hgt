import GaloisForLFunctions.Bottcher.FigureEight
import Mathlib.Analysis.RCLike.Sqrt

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The principal complex square root is Borel measurable. -/
theorem measurable_complex_sqrt : Measurable (fun z : ℂ => Complex.sqrt z) := by
  let f : ℂ → ℂ := fun z =>
    if z = 0 then 0 else Complex.exp (Complex.log z / 2)
  have hlog : Measurable (fun z : ℂ => Complex.log z) := by
    unfold Complex.log
    fun_prop
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ite
    · exact measurableSet_singleton 0
    · exact measurable_const
    · exact (hlog.div measurable_const).cexp
  have heq : (fun z : ℂ => Complex.sqrt z) = f := by
    funext z
    dsimp [f]
    by_cases hz : z = 0
    · simp [hz]
    · rw [if_neg hz, sqrt_eq_exp hz]
  rw [heq]
  exact hf

/-- The principal complex square root squares back everywhere. -/
theorem complex_sqrt_sq_measurable (z : ℂ) : Complex.sqrt z ^ (2 : ℕ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · calc
      Complex.sqrt z ^ (2 : ℕ) = Complex.exp (Complex.log z / 2) ^ (2 : ℕ) := by
        rw [sqrt_eq_exp hz]
      _ = Complex.exp (Complex.log z) := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring
      _ = z := Complex.exp_log hz

/-- A measurable nonvanishing analytic germ has a measurable total representative of a local
analytic square root. -/
theorem exists_measurable_analyticAt_sq_eq
    {g : ℂ → ℂ} {z₀ : ℂ} (hgMeas : Measurable g)
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, Measurable h ∧ AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, h z ^ (2 : ℕ) = g z := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ (2 : ℕ) = g z₀ :=
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
    change (s * Complex.exp ((2 : ℂ)⁻¹ * Complex.log (q z))) ^ (2 : ℕ) = g z
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
    (hg : AnalyticAt ℂ g z₀) (hs : s ^ (2 : ℕ) = g z₀) (hs0 : s ≠ 0) :
    ∃ h : ℂ → ℂ, Measurable h ∧ AnalyticAt ℂ h z₀ ∧ h z₀ = s ∧
      ∀ᶠ z in nhds z₀, h z ^ (2 : ℕ) = g z := by
  have hg0 : g z₀ ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero 2 hs0
  obtain ⟨h, hhMeas, hhan, hh0, hhsq⟩ :=
    exists_measurable_analyticAt_sq_eq hgMeas hg hg0
  have hh0sq : h z₀ ^ (2 : ℕ) = g z₀ := hhsq.self_of_nhds
  let c : ℂ := s / h z₀
  have hc2 : c ^ (2 : ℕ) = 1 := by
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

/-- A prescribed local analytic square root can be totalized measurably while retaining the exact
square identity at every complex point. -/
theorem exists_measurable_analyticAt_sq_eq_of_value_global
    {g : ℂ → ℂ} {z₀ s : ℂ} (hgMeas : Measurable g)
    (hg : AnalyticAt ℂ g z₀) (hs : s ^ (2 : ℕ) = g z₀) (hs0 : s ≠ 0) :
    ∃ h : ℂ → ℂ, Measurable h ∧ AnalyticAt ℂ h z₀ ∧ h z₀ = s ∧
      ∀ z : ℂ, h z ^ (2 : ℕ) = g z := by
  classical
  obtain ⟨h, hhMeas, hhan, hh0, hhsq⟩ :=
    exists_measurable_analyticAt_sq_eq_of_value hgMeas hg hs hs0
  obtain ⟨r, hr, hsqBall⟩ := Metric.mem_nhds_iff.mp hhsq
  let H : ℂ → ℂ := fun z =>
    if z ∈ ball z₀ r then h z else Complex.sqrt (g z)
  have hHMeas : Measurable H := by
    dsimp [H]
    exact Measurable.ite isOpen_ball.measurableSet hhMeas
      (measurable_complex_sqrt.comp hgMeas)
  have hHeq : H =ᶠ[nhds z₀] h := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    dsimp only [H]
    rw [if_pos hz]
  refine ⟨H, hHMeas, hhan.congr hHeq.symm, ?_, ?_⟩
  · rw [hHeq.self_of_nhds, hh0]
  · intro z
    by_cases hz : z ∈ ball z₀ r
    · rw [show H z = h z by dsimp only [H]; rw [if_pos hz], hsqBall hz]
    · rw [show H z = Complex.sqrt (g z) by dsimp only [H]; rw [if_neg hz],
        complex_sqrt_sq_measurable]

end

end GaloisForLFunctions.HTGeometry
