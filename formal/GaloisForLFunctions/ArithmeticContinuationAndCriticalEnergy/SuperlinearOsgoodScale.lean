import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingContinuationCriterion

/-!
# A superlinear scale that still forbids escape

The linear continuation demand asks for `−E'_T ≤ β'(ε)(1 + E_T)`.  The Osgood form asks only that
the loss be controlled by `β'(ε) Φ(E_T)` for some growth function whose reciprocal has infinite
integral.  The double logarithm

`Ψ(u) = log(1 + log(1 + u))`,  `Ψ'(u) = 1 / ((1+u)(1 + log(1+u)))`,

is such a scale: it is increasing and coercive on `[0, ∞)`, so admission still cannot escape over
a finite damping interval, while the permitted loss

`Φ(u) = (1 + u)(1 + log(1 + u))`

grows faster than linearly.  The resulting criterion is strictly weaker than the linear one: every
linear continuation budget is a superlinear one, because `1 + log(1+u) ≥ 1`.

So the arithmetic estimate that would prove RH through continuation need not be linear in the
energy.  It may lose an extra logarithm of the energy at every damping and still suffice.
-/

open Set Filter Finset

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The double-logarithmic scale. -/
def logLogScale (u : ℝ) : ℝ := Real.log (1 + Real.log (1 + u))

/-- Its derivative, the reciprocal of the permitted superlinear growth. -/
def logLogScaleDeriv (u : ℝ) : ℝ := 1 / ((1 + u) * (1 + Real.log (1 + u)))

/-- The permitted loss: superlinear in the energy. -/
def logLogGrowth (u : ℝ) : ℝ := (1 + u) * (1 + Real.log (1 + u))

theorem one_le_one_add_log_one_add {u : ℝ} (hu : 0 ≤ u) : 1 ≤ 1 + Real.log (1 + u) := by
  have : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  linarith

theorem logLogGrowth_pos {u : ℝ} (hu : 0 ≤ u) : 0 < logLogGrowth u := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (1 : ℝ) ≤ 1 + Real.log (1 + u) := one_le_one_add_log_one_add hu
  exact mul_pos h1 (by linarith)

theorem hasDerivAt_logLogScale {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt logLogScale (logLogScaleDeriv u) u := by
  have h1 : (1 : ℝ) + u ≠ 0 := by positivity
  have hinner : HasDerivAt (fun x : ℝ => 1 + Real.log (1 + x)) ((1 + u)⁻¹) u := by
    have h := ((hasDerivAt_id' (x := u)).const_add (1 : ℝ)).log h1
    simpa [one_div] using h.const_add (1 : ℝ)
  have hne : (1 : ℝ) + Real.log (1 + u) ≠ 0 := by
    have := one_le_one_add_log_one_add hu
    linarith
  have h := hinner.log hne
  refine h.congr_deriv ?_
  rw [logLogScaleDeriv]
  field_simp

theorem logLogScaleDeriv_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ logLogScaleDeriv u :=
  le_of_lt (by rw [logLogScaleDeriv, one_div]; exact inv_pos.mpr (logLogGrowth_pos hu))

theorem tendsto_logLogScale_atTop : Tendsto logLogScale atTop atTop := by
  have h1 : Tendsto (fun u : ℝ => 1 + u) atTop atTop := tendsto_atTop_add_const_left _ 1 tendsto_id
  have h2 : Tendsto (fun u : ℝ => Real.log (1 + u)) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun u : ℝ => 1 + Real.log (1 + u)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 h2
  exact Real.tendsto_log_atTop.comp h3

/-- **The superlinear continuation criterion.**  A horizon-free budget paying the loss against
`(1 + E)(1 + log(1 + E))` on every compact interval inside `(0, ½]` still gives RH. -/
theorem riemannHypothesis_of_superlinear_dampingContinuation
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∃ β β' : ℝ → ℝ,
      (∀ ε ∈ Icc a (1 / 2 : ℝ), HasDerivAt β (β' ε) ε) ∧
        ∀ T : ℕ, ∀ ε ∈ Icc a (1 / 2 : ℝ),
          -(2 * signedDampingWork ε T) ≤ β' ε * logLogGrowth (dampedMobiusEnergy ε T)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_osgoodDampingContinuation fun a ha hac => ?_
  obtain ⟨β, β', hβ, hwork⟩ := h a ha hac
  refine ⟨logLogScale, logLogScaleDeriv, β, β', fun u hu => hasDerivAt_logLogScale hu,
    fun u hu => logLogScaleDeriv_nonneg hu, tendsto_logLogScale_atTop, hβ, fun T ε hε => ?_⟩
  have hE := dampedMobiusEnergy_nonneg ε T
  have hpos : 0 < logLogGrowth (dampedMobiusEnergy ε T) := logLogGrowth_pos hE
  have hdiv : -(logLogScaleDeriv (dampedMobiusEnergy ε T) * dampedMobiusEnergyDeriv T ε) =
      -(2 * signedDampingWork ε T) / logLogGrowth (dampedMobiusEnergy ε T) := by
    rw [logLogScaleDeriv, dampedMobiusEnergyDeriv, logLogGrowth]
    field_simp
  rw [hdiv, div_le_iff₀ hpos]
  exact hwork T ε hε

/-- Every linear budget is a superlinear budget: the criterion genuinely weakens the demand. -/
theorem mul_one_add_le_mul_logLogGrowth {u b : ℝ} (hu : 0 ≤ u) (hb : 0 ≤ b) :
    b * (1 + u) ≤ b * logLogGrowth u := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (1 : ℝ) ≤ 1 + Real.log (1 + u) := one_le_one_add_log_one_add hu
  have : (1 + u) * 1 ≤ (1 + u) * (1 + Real.log (1 + u)) :=
    mul_le_mul_of_nonneg_left h2 h1.le
  rw [logLogGrowth]
  nlinarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
