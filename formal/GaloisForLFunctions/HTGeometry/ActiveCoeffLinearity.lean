import GaloisForLFunctions.HTGeometry.LogCoordDerivCoeff

/-!
# Linearity of the active coefficients, and the commuting derivations

The active coefficient is an integral, hence linear on observables whose torus
restrictions are continuous.  Combined with the multiplier identity for the
logarithmic coordinate derivatives, the torus derivation multiplies the `m`-th
active coefficient by `i (m · ω)`.

Both the torus derivation and the logarithmic coordinate derivatives are
therefore Fourier multipliers, so they commute: their two composites have the
same active coefficients, and the active coefficients determine a holomorphic
observable.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCircleActiveCoeff : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance isAddHaarMeasureCircleActiveCoeff : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Integrability of the torus integrand -/

omit [DecidableEq d] in
theorem integrable_activeIntegrand {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ) :
    Integrable
      (fun x : UnitAddTorus d =>
        UnitAddTorus.mFourier (-m) x • torusRestriction F x) volume := by
  refine Continuous.integrable_of_hasCompactSupport ?_
    (HasCompactSupport.of_compactSpace _)
  exact (UnitAddTorus.mFourier (-m)).continuous.smul
    (continuous_torusRestriction hρ hF)

/-! ### Linearity -/

omit [DecidableEq d] in
theorem activeCoeff_add {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F G : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (hG : AnalyticOnNhd ℂ G (polyannulus ρ)) (m : d → ℤ) :
    activeCoeff (fun z => F z + G z) m = activeCoeff F m + activeCoeff G m := by
  have hsplit : (fun x : UnitAddTorus d =>
        UnitAddTorus.mFourier (-m) x • torusRestriction (fun z => F z + G z) x)
      = fun x : UnitAddTorus d =>
        UnitAddTorus.mFourier (-m) x • torusRestriction F x
          + UnitAddTorus.mFourier (-m) x • torusRestriction G x := by
    funext x
    rw [torusRestriction, torusRestriction, torusRestriction, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_add]
  show (∫ x, UnitAddTorus.mFourier (-m) x •
      torusRestriction (fun z => F z + G z) x) = _
  rw [hsplit, integral_add (integrable_activeIntegrand hρ hF m)
    (integrable_activeIntegrand hρ hG m)]
  rfl

omit [DecidableEq d] in
theorem activeCoeff_const_mul (c : ℂ) (F : (d → ℂ) → ℂ) (m : d → ℤ) :
    activeCoeff (fun z => c * F z) m = c * activeCoeff F m := by
  have hsplit : (fun x : UnitAddTorus d =>
        UnitAddTorus.mFourier (-m) x • torusRestriction (fun z => c * F z) x)
      = fun x : UnitAddTorus d =>
        c • (UnitAddTorus.mFourier (-m) x • torusRestriction F x) := by
    funext x
    rw [torusRestriction, torusRestriction, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  show (∫ x, UnitAddTorus.mFourier (-m) x •
      torusRestriction (fun z => c * F z) x) = _
  rw [hsplit, integral_smul]
  rfl

omit [DecidableEq d] in
theorem activeCoeff_sum {ι : Type} [Fintype ι] {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {g : ι → (d → ℂ) → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (g i) (polyannulus ρ))
    (m : d → ℤ) :
    activeCoeff (fun z => ∑ i, g i z) m = ∑ i, activeCoeff (g i) m := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      show activeCoeff (fun _ => (0 : ℂ)) m = 0
      have hzero : (fun x : UnitAddTorus d =>
          UnitAddTorus.mFourier (-m) x •
            torusRestriction (fun _ : d → ℂ => (0 : ℂ)) x) = fun _ => 0 := by
        funext x
        rw [torusRestriction, smul_eq_mul, mul_zero]
      show (∫ x, UnitAddTorus.mFourier (-m) x •
        torusRestriction (fun _ : d → ℂ => (0 : ℂ)) x) = 0
      rw [hzero, integral_zero]
  | insert i s hi ih =>
      have hfun : (fun z => ∑ k ∈ insert i s, g k z)
          = fun z => g i z + ∑ k ∈ s, g k z := by
        funext z
        rw [Finset.sum_insert hi]
      rw [hfun, activeCoeff_add hρ (hg i)
        (Finset.analyticOnNhd_fun_sum s fun k _ => hg k) m, ih,
        Finset.sum_insert hi]

/-! ### The derivation is a Fourier multiplier -/

theorem analyticOnNhd_logCoordDeriv {ρ : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (j : d) :
    AnalyticOnNhd ℂ (logCoordDeriv F j) (polyannulus ρ) := by
  refine AnalyticOnNhd.mul ?_ (analyticOnNhd_coordDeriv hF j)
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : d => ℂ) j).analyticOnNhd _

/-- **The torus derivation is the Fourier multiplier by `i (m · ω)`.** -/
theorem activeCoeff_torusDerivation {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (omega : d → ℝ) (m : d → ℤ) :
    activeCoeff (torusDerivation omega F) m
      = (∑ j, Complex.I * (omega j : ℂ) * (m j : ℂ)) * activeCoeff F m := by
  have hfun : torusDerivation omega F
      = fun z => ∑ j, (Complex.I * (omega j : ℂ)) * logCoordDeriv F j z := by
    funext z
    rw [torusDerivation]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logCoordDeriv]
    ring
  rw [hfun, activeCoeff_sum hρ
    (fun j => analyticOnNhd_const.mul (analyticOnNhd_logCoordDeriv hF j)) m,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [activeCoeff_const_mul, activeCoeff_logCoordDeriv hρ hF m j]
  ring

/-! ### The derivations commute -/

/-- **The logarithmic coordinate derivatives commute with the torus
derivation.**  Both are Fourier multipliers, and the active coefficients
determine a holomorphic observable. -/
theorem logCoordDeriv_torusDerivation {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (omega : d → ℝ) (j : d) :
    ∀ z ∈ polyannulus ρ,
      logCoordDeriv (torusDerivation omega F) j z
        = torusDerivation omega (logCoordDeriv F j) z := by
  refine eqOn_polyannulus_of_activeCoeff_eq hρ
    (analyticOnNhd_logCoordDeriv (analyticOnNhd_torusDerivation omega hF) j)
    (analyticOnNhd_torusDerivation omega (analyticOnNhd_logCoordDeriv hF j))
    fun m => ?_
  rw [activeCoeff_logCoordDeriv hρ (analyticOnNhd_torusDerivation omega hF) m j,
    activeCoeff_torusDerivation hρ hF omega m,
    activeCoeff_torusDerivation hρ (analyticOnNhd_logCoordDeriv hF j) omega m,
    activeCoeff_logCoordDeriv hρ hF m j]
  ring

end

end GaloisForLFunctions.HTGeometry
