import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaEllipticIntegrals
import Mathlib.Tactic

/-!
# Positivity of Brizard's complete elliptic integrals

For every real parameter below the singular endpoint `m=1`, both defining radicands and complete
integrals are strictly positive.  Packaging the domain as a subtype makes all results closed and
provides the nonzero denominator needed by the paper's knot-closure function.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Full real domain on which the first-kind integrand is everywhere regular. -/
abbrev SubcriticalModulus := {m : ℝ // m < 1}

noncomputable def completeKIntegrand (m θ : ℝ) : ℝ :=
  (Real.sqrt (1 - m * Real.sin θ ^ (2 : ℕ)))⁻¹

noncomputable def completeEIntegrand (m θ : ℝ) : ℝ :=
  Real.sqrt (1 - m * Real.sin θ ^ (2 : ℕ))

theorem subcriticalRadicand_pos (m : SubcriticalModulus) (θ : ℝ) :
    0 < 1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ) := by
  have hm1 : (m : ℝ) < 1 := m.property
  have hs0 : 0 ≤ Real.sin θ ^ (2 : ℕ) := sq_nonneg _
  have hs1 : Real.sin θ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  by_cases hm0 : (m : ℝ) ≤ 0
  · have hprod : (m : ℝ) * Real.sin θ ^ (2 : ℕ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hm0 hs0
    linarith
  · have hm0' : 0 ≤ (m : ℝ) := le_of_lt (lt_of_not_ge hm0)
    have hprod : (m : ℝ) * Real.sin θ ^ (2 : ℕ) ≤ (m : ℝ) :=
      by simpa using mul_le_mul_of_nonneg_left hs1 hm0'
    linarith

theorem completeKIntegrand_pos (m : SubcriticalModulus) (θ : ℝ) :
    0 < completeKIntegrand m θ := by
  rw [completeKIntegrand]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (subcriticalRadicand_pos m θ))

theorem completeEIntegrand_pos (m : SubcriticalModulus) (θ : ℝ) :
    0 < completeEIntegrand m θ := by
  rw [completeEIntegrand]
  exact Real.sqrt_pos.mpr (subcriticalRadicand_pos m θ)

theorem continuous_completeKIntegrand (m : SubcriticalModulus) :
    Continuous (completeKIntegrand m) := by
  have hbase : Continuous (fun θ : ℝ => 1 - (m : ℝ) * Real.sin θ ^ (2 : ℕ)) := by
    fun_prop
  exact (Real.continuous_sqrt.comp hbase).inv₀ fun θ =>
    ne_of_gt (Real.sqrt_pos.mpr (subcriticalRadicand_pos m θ))

theorem continuous_completeEIntegrand (m : SubcriticalModulus) :
    Continuous (completeEIntegrand m) := by
  exact Real.continuous_sqrt.comp (by fun_prop)

/-- The complete first-kind integral is nonzero everywhere below `m=1`. -/
theorem completeEllipticK_pos (m : SubcriticalModulus) :
    0 < completeEllipticK m := by
  rw [completeEllipticK]
  exact intervalIntegral.intervalIntegral_pos_of_pos
    ((continuous_completeKIntegrand m).intervalIntegrable _ _)
    (completeKIntegrand_pos m) (by positivity)

theorem completeEllipticK_ne_zero (m : SubcriticalModulus) :
    completeEllipticK m ≠ 0 := ne_of_gt (completeEllipticK_pos m)

/-- The complete second-kind integral is positive everywhere below `m=1`. -/
theorem completeEllipticE_pos (m : SubcriticalModulus) :
    0 < completeEllipticE m := by
  rw [completeEllipticE]
  exact intervalIntegral.intervalIntegral_pos_of_pos
    ((continuous_completeEIntegrand m).intervalIntegrable _ _)
    (completeEIntegrand_pos m) (by positivity)

noncomputable def negativeAsSubcritical (m : NegativeModulus) : SubcriticalModulus :=
  ⟨(m : ℝ), lt_trans m.property zero_lt_one⟩

noncomputable def classicalAsSubcritical (m : ClassicalModulus) : SubcriticalModulus :=
  ⟨m, m.property.2⟩

theorem completeEllipticK_negative_pos (m : NegativeModulus) :
    0 < completeEllipticK m := by
  simpa [negativeAsSubcritical] using completeEllipticK_pos (negativeAsSubcritical m)

theorem completeEllipticK_classical_pos (m : ClassicalModulus) :
    0 < completeEllipticK m := completeEllipticK_pos (classicalAsSubcritical m)

theorem completeEllipticE_negative_pos (m : NegativeModulus) :
    0 < completeEllipticE m := by
  simpa [negativeAsSubcritical] using completeEllipticE_pos (negativeAsSubcritical m)

theorem completeEllipticE_classical_pos (m : ClassicalModulus) :
    0 < completeEllipticE m := completeEllipticE_pos (classicalAsSubcritical m)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
