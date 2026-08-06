import GaloisForLFunctions.HTGeometry.CharPowAnnihilator

/-!
# The active coefficients of a logarithmic derivative

The logarithmic coordinate derivative `z_i ∂_i F` is the derivative of the
translated observable in the `i`-th translation coordinate at the identity.
Differentiating the scaling law there multiplies the `m`-th active coefficient
by the exponent `m_i`.

So the logarithmic derivatives are the Fourier multipliers by the coordinates
of the exponent, which is what turns a linear relation among them into a linear
condition on the active lattice.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The logarithmic coordinate derivative `z_i ∂_i F`. -/
def logCoordDeriv (F : (d → ℂ) → ℂ) (i : d) (z : d → ℂ) : ℂ :=
  z i * coordDeriv F i z

omit [Fintype d] [DecidableEq d] in
theorem one_mem_logAnnulus' {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j) (i : d) :
    (1 : ℂ) ∈ logAnnulus (ρ i) := one_mem_logAnnulus (hρ i)

omit [Fintype d] in
theorem update_one_self (i : d) :
    Function.update (fun _ : d => (1 : ℂ)) i 1 = fun _ : d => (1 : ℂ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]

theorem charPow_update_one (i : d) (w : ℂ) (m : d → ℤ) :
    charPow (Function.update (fun _ : d => (1 : ℂ)) i w) m = w ^ (m i) := by
  classical
  rw [charPow_update]
  have hone : ∏ j ∈ Finset.univ.erase i, ((fun _ : d => (1 : ℂ)) j) ^ (m j) = 1 :=
    Finset.prod_eq_one fun j _ => one_zpow _
  rw [hone, mul_one]

/-- **The active coefficients of a logarithmic derivative.** -/
theorem activeCoeff_logCoordDeriv {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ)
    (i : d) :
    activeCoeff (logCoordDeriv F i) m = (m i : ℂ) * activeCoeff F m := by
  classical
  have h1 : (fun _ : d => (1 : ℂ)) ∈ polyannulus ρ := one_mem_polyannulus hρ
  have hw₀ : (1 : ℂ) ∈ logAnnulus (ρ i) := one_mem_logAnnulus' hρ i
  -- differentiate under the integral sign at the identity translation
  have hderiv := hasDerivAt_slice_activeCoeff hF m h1 i hw₀
  rw [update_one_self i] at hderiv
  -- the derivative integral is the coefficient of the logarithmic derivative
  have hint : (∫ x, translatedDerivIntegrand F m i (fun _ : d => (1 : ℂ)) x)
      = activeCoeff (logCoordDeriv F i) m := by
    have hfun : (fun x : UnitAddTorus d =>
          translatedDerivIntegrand F m i (fun _ : d => (1 : ℂ)) x)
        = fun x : UnitAddTorus d =>
          UnitAddTorus.mFourier (-m) x • torusRestriction (logCoordDeriv F i) x := by
      funext x
      rw [translatedDerivIntegrand, scaledTorusPoint, torusScale_one_left,
        torusRestriction, logCoordDeriv, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [hfun]
    rfl
  rw [hint] at hderiv
  -- the same function is a monomial times a constant
  have heq : (fun w : ℂ =>
      activeCoeff (fun z => F (torusScale (Function.update
        (fun _ : d => (1 : ℂ)) i w) z)) m)
      =ᶠ[𝓝 (1 : ℂ)] fun w : ℂ => w ^ (m i) * activeCoeff F m := by
    filter_upwards [(isOpen_logAnnulus (ρ i)).mem_nhds hw₀] with w hw
    have hmem : Function.update (fun _ : d => (1 : ℂ)) i w ∈ polyannulus ρ := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact hw
      · rw [Function.update_of_ne hj]
        exact h1 j
    rw [activeCoeff_comp_torusScale_polyannulus hρ hF m _ hmem, charPow_update_one]
  have hmono : HasDerivAt (fun w : ℂ => w ^ (m i) * activeCoeff F m)
      ((m i : ℂ) * activeCoeff F m) (1 : ℂ) := by
    have hz := (hasDerivAt_zpow (m i) (1 : ℂ) (Or.inl one_ne_zero)).mul_const
      (activeCoeff F m)
    rwa [one_zpow, mul_one] at hz
  exact (hderiv.congr_of_eventuallyEq heq.symm).unique hmono

end

end GaloisForLFunctions.HTGeometry
