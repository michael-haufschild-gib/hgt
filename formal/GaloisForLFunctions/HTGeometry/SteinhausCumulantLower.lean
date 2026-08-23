import GaloisForLFunctions.HTGeometry.SteinhausWeightProfile

/-!
# An elementary linear lower bound for the circle cumulant

Restricting the Haar integral to the arc where the projection exceeds `c` gives
`I₀(x) ≥ μ_c·e^{cx}` for `x ≥ 0`, hence `log I₀(x) ≥ cx + log μ_c` for every `c < 1`.  The mass
`μ_c` is positive merely because the arc is open and nonempty, so no quantitative measure
computation is needed.  Integrated against the unit-mass profile this gives
`Λ_α(λ) ≥ cλ + log μ_c`, which is exactly what makes the Legendre transform finite below `q = 1`.
-/

open MeasureTheory Set

namespace HTGeometry

local instance phaseCirclePositiveLower : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The arc on which the projection exceeds `c`. -/
def projArc (c : ℝ) : Set PhaseCircle := {x : PhaseCircle | c < steinhausProjection x}

theorem isOpen_projArc (c : ℝ) : IsOpen (projArc c) :=
  isOpen_lt continuous_const continuous_steinhausProjection

theorem measurableSet_projArc (c : ℝ) : MeasurableSet (projArc c) :=
  (isOpen_projArc c).measurableSet

/-- The Haar mass of that arc. -/
def arcMass (c : ℝ) : ℝ := (AddCircle.haarAddCircle (projArc c)).toReal

theorem arcMass_pos {c : ℝ} (hc : c < 1) : 0 < arcMass c := by
  have hne : (projArc c).Nonempty := by
    refine ⟨0, ?_⟩
    rw [projArc, Set.mem_setOf_eq, steinhausProjection_zero]
    exact hc
  have hpos := (isOpen_projArc c).measure_pos AddCircle.haarAddCircle hne
  rw [arcMass]
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

/-- **The elementary lower envelope of the circle Laplace transform.** -/
theorem arcMass_mul_exp_le_steinhausLaplace (c : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    arcMass c * Real.exp (c * x) ≤ steinhausLaplace x := by
  have hint := steinhausLaplace_integrable x
  have hnn : ∀ y : PhaseCircle, 0 ≤ Real.exp (x * steinhausProjection y) :=
    fun y => (Real.exp_pos _).le
  have hset : (∫ y in projArc c, Real.exp (x * steinhausProjection y) ∂AddCircle.haarAddCircle)
      ≤ steinhausLaplace x := by
    rw [steinhausLaplace]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  refine le_trans ?_ hset
  have hlow : ∀ y ∈ projArc c, Real.exp (c * x) ≤ Real.exp (x * steinhausProjection y) := by
    intro y hy
    rw [projArc, Set.mem_setOf_eq] at hy
    refine Real.exp_le_exp.2 ?_
    nlinarith [hy, hx]
  have hconstint : IntegrableOn (fun _ : PhaseCircle => Real.exp (c * x))
      (projArc c) AddCircle.haarAddCircle :=
    integrableOn_const (by exact measure_ne_top _ _)
  have hmono := setIntegral_mono_on hconstint (hint.integrableOn) (measurableSet_projArc c) hlow
  refine le_trans (le_of_eq ?_) hmono
  rw [setIntegral_const, measureReal_def, smul_eq_mul, arcMass]

/-- **The linear lower bound for the circle cumulant.** -/
theorem le_steinhausLogLaplace {c : ℝ} (hc : c < 1) {x : ℝ} (hx : 0 ≤ x) :
    c * x + Real.log (arcMass c) ≤ steinhausLogLaplace x := by
  have hpos := arcMass_pos hc
  have hbound := arcMass_mul_exp_le_steinhausLaplace c hx
  have hLpos := steinhausLaplace_pos x
  rw [steinhausLogLaplace]
  have hlog := Real.log_le_log (by positivity) hbound
  rw [Real.log_mul (ne_of_gt hpos) (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

/-- **The linear lower bound for the regular-variation cumulant.** -/
theorem le_rvCumulant {α : ℝ} (hα : α < 1) {c : ℝ} (hc : c < 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    c * lam + Real.log (arcMass c) ≤ rvCumulant α lam := by
  rw [rvCumulant]
  have hint1 : IntervalIntegrable
      (fun v : ℝ => c * lam * weightProfile α v + Real.log (arcMass c)) volume 0 1 :=
    ((intervalIntegrable_weightProfile hα).const_mul (c * lam)).add intervalIntegrable_const
  have hlow : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      c * lam * weightProfile α v + Real.log (arcMass c)
        ≤ steinhausLogLaplace (lam * weightProfile α v) := by
    intro v hv
    have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα hv.1
    have hb := le_steinhausLogLaplace hc
      (show (0 : ℝ) ≤ lam * weightProfile α v by positivity)
    calc c * lam * weightProfile α v + Real.log (arcMass c)
        = c * (lam * weightProfile α v) + Real.log (arcMass c) := by ring
      _ ≤ steinhausLogLaplace (lam * weightProfile α v) := hb
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    hint1 (intervalIntegrable_rvCumulant_integrand hα lam) hlow
  refine le_trans (le_of_eq ?_) hmono
  rw [intervalIntegral.integral_add
      ((intervalIntegrable_weightProfile hα).const_mul (c * lam)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_weightProfile hα,
    intervalIntegral.integral_const]
  simp

end

end HTGeometry
