import GaloisForLFunctions.HTGeometry.BernsteinSzegoMomentForm

/-!
# Uniform finite Bernstein--Szegő weld bounds

The reciprocal-square Bernstein--Szegő density is continuous and strictly positive on the compact
circle.  It therefore gives equivalent unweighted and weighted polynomial `L²` quadratic forms.
This is the exact bounded/bounded-below content of the finite weld in the graph-saturation card.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial Set
open scoped ComplexOrder

noncomputable section

/-- The Bernstein--Szegő density is continuous on the multiplicative circle itself. -/
theorem bernsteinSzegoDensity_continuous {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    Continuous (bernsteinSzegoDensity c hG) := by
  apply Continuous.inv₀
  · exact Complex.continuous_normSq.comp
      ((finiteOPUCReversedPolynomial c hG).continuous.comp
        (by fun_prop : Continuous fun z : Circle => (z : ℂ)))
  · intro z
    exact Complex.normSq_eq_zero.not.mpr
      (finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG (by simp))

/-- Compactness supplies uniform positive lower and finite upper bounds for every finite
Bernstein--Szegő density. -/
theorem exists_bernsteinSzegoDensity_uniform_bounds {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ z : Circle, lower ≤ bernsteinSzegoDensity c hG z ∧
        bernsteinSzegoDensity c hG z ≤ upper := by
  have hcont := bernsteinSzegoDensity_continuous c hG
  obtain ⟨zmin, _hzmin, hzmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  obtain ⟨zmax, _hzmax, hzmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  refine ⟨bernsteinSzegoDensity c hG zmin,
    bernsteinSzegoDensity c hG zmax,
    bernsteinSzegoDensity_pos c hG zmin,
    bernsteinSzegoDensity_pos c hG zmax, ?_⟩
  intro z
  exact ⟨hzmin (Set.mem_univ z), hzmax (Set.mem_univ z)⟩

/-- The real form of the reciprocal-square weight on the ambient complex plane. -/
def bernsteinSzegoRealWeight {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (z : ℂ) : ℝ :=
  (bernsteinSzegoComplexWeight c hG z).re

/-- On the unit circle, the ambient real weight is the intrinsic Bernstein--Szegő density. -/
theorem bernsteinSzegoRealWeight_eq_density {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (z : Circle) :
    bernsteinSzegoRealWeight c hG z = bernsteinSzegoDensity c hG z := by
  simp [bernsteinSzegoRealWeight, bernsteinSzegoComplexWeight,
    bernsteinSzegoDensity]

/-- Every finite coefficient polynomial has uniformly equivalent unweighted and
Bernstein--Szegő-weighted circle quadratic forms.  This is the finite weld's exact upper and lower
operator bound before Hilbert completion. -/
theorem bernsteinSzego_polynomial_weld_quadratic_bounds
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (u : Fin (N + 1) → ℂ) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      lower * Real.circleAverage
          (fun z : ℂ => Complex.normSq (finiteCoefficientPolynomialEval u z)) 0 1 ≤
        Real.circleAverage
          (fun z : ℂ => Complex.normSq (finiteCoefficientPolynomialEval u z) *
            bernsteinSzegoRealWeight c hG z) 0 1 ∧
      Real.circleAverage
          (fun z : ℂ => Complex.normSq (finiteCoefficientPolynomialEval u z) *
            bernsteinSzegoRealWeight c hG z) 0 1 ≤
        upper * Real.circleAverage
          (fun z : ℂ => Complex.normSq (finiteCoefficientPolynomialEval u z)) 0 1 := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    exists_bernsteinSzegoDensity_uniform_bounds c hG
  let Q : ℂ → ℝ := fun z =>
    Complex.normSq (finiteCoefficientPolynomialEval u z)
  let W : ℂ → ℝ := bernsteinSzegoRealWeight c hG
  have hQcont : Continuous Q := by
    dsimp only [Q, finiteCoefficientPolynomialEval]
    fun_prop
  have hWcont : ContinuousOn W (Metric.sphere (0 : ℂ) 1) := by
    exact Complex.continuous_re.comp_continuousOn
      (bernsteinSzegoComplexWeight_continuousOn_sphere c hG)
  have hQint : CircleIntegrable Q 0 1 :=
    hQcont.continuousOn.circleIntegrable zero_le_one
  have hQWint : CircleIntegrable (fun z => Q z * W z) 0 1 :=
    (hQcont.continuousOn.mul hWcont).circleIntegrable zero_le_one
  have hlowerInt : CircleIntegrable (fun z => lower * Q z) 0 1 := by
    exact (continuous_const.mul hQcont).continuousOn.circleIntegrable zero_le_one
  have hupperInt : CircleIntegrable (fun z => upper * Q z) 0 1 := by
    exact (continuous_const.mul hQcont).continuousOn.circleIntegrable zero_le_one
  have hlowerBound : Real.circleAverage (fun z => lower * Q z) 0 1 ≤
      Real.circleAverage (fun z => Q z * W z) 0 1 := by
    apply Real.circleAverage_mono hlowerInt hQWint
    intro z hz
    have hzCircle : (z : ℂ) ∈ Metric.sphere 0 1 := by simpa using hz
    let zc : Circle := ⟨z, hzCircle⟩
    have hW : lower ≤ W z := by
      change lower ≤ bernsteinSzegoRealWeight c hG z
      rw [show z = (zc : ℂ) by rfl, bernsteinSzegoRealWeight_eq_density c hG zc]
      exact (hbounds zc).1
    nlinarith [Complex.normSq_nonneg (finiteCoefficientPolynomialEval u z)]
  have hupperBound : Real.circleAverage (fun z => Q z * W z) 0 1 ≤
      Real.circleAverage (fun z => upper * Q z) 0 1 := by
    apply Real.circleAverage_mono hQWint hupperInt
    intro z hz
    have hzCircle : (z : ℂ) ∈ Metric.sphere 0 1 := by simpa using hz
    let zc : Circle := ⟨z, hzCircle⟩
    have hW : W z ≤ upper := by
      change bernsteinSzegoRealWeight c hG z ≤ upper
      rw [show z = (zc : ℂ) by rfl, bernsteinSzegoRealWeight_eq_density c hG zc]
      exact (hbounds zc).2
    nlinarith [Complex.normSq_nonneg (finiteCoefficientPolynomialEval u z)]
  refine ⟨lower, upper, hlower, hupper, ?_, ?_⟩
  · calc
      lower * Real.circleAverage Q 0 1 =
          Real.circleAverage (fun z => lower * Q z) 0 1 := by
            simpa only [smul_eq_mul] using
              (Real.circleAverage_fun_smul (a := lower) (f := Q) (c := 0) (R := 1)).symm
      _ ≤ Real.circleAverage (fun z => Q z * W z) 0 1 := hlowerBound
  · calc
      Real.circleAverage (fun z => Q z * W z) 0 1 ≤
          Real.circleAverage (fun z => upper * Q z) 0 1 := hupperBound
      _ = upper * Real.circleAverage Q 0 1 := by
        simpa only [smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := upper) (f := Q) (c := 0) (R := 1))

end

end GaloisForLFunctions.HTGeometry
