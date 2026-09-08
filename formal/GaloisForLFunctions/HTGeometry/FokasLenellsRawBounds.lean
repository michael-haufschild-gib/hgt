import GaloisForLFunctions.HTGeometry.FokasLenellsRawEvolution

/-!
# Whole-line bounds for the original spectral flow

The L¹ Picard factorial estimate controls the complete evolution by total
coefficient mass, uniformly in position. Applied to the actual raw Fokas–
Lenells family, this gives exp(|k| M) and an integrable derivative for every
real frequency, including zero. These are the bounds needed to pass a
finite-frequency expansion to the scattering endpoints.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem positiveEvolution_total_bound (A : ℝ → RawOperator) (hA : Integrable A)
    (x : ℝ) (hx : 0 ≤ x) : ‖positiveEvolution A x‖ ≤ Real.exp (∫ s : ℝ, ‖A s‖) := by
  have hp : ‖positiveEvolution A x‖ ≤ Real.exp (positiveMass A x) := by
    have hh := tsum_of_norm_bounded (Real.summable_pow_div_factorial (positiveMass A x)).hasSum
      (fun n => show ‖l1Picard A n x‖ ≤ positiveMass A x^n/(n.factorial : ℝ) from by
        simpa only [norm_one,one_mul] using norm_l1Picard_le hA.locallyIntegrable n hx)
    simpa only [positiveEvolution,Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div] using hh
  apply hp.trans (Real.exp_le_exp.mpr ?_)
  unfold positiveMass
  rw [intervalIntegral.integral_of_le hx]
  exact setIntegral_le_integral hA.norm (Eventually.of_forall fun s => norm_nonneg (A s))

private theorem caratheodoryEvolution_total_bound (A : ℝ → RawOperator) (hA : Integrable A)
    (x : ℝ) : ‖caratheodoryEvolution A x‖ ≤ Real.exp (∫ s : ℝ, ‖A s‖) := by
  by_cases hx : 0 ≤ x
  · rw [caratheodoryEvolution_of_nonneg hx]
    exact positiveEvolution_total_bound A hA x hx
  · rw [caratheodoryEvolution_of_neg (lt_of_not_ge hx)]
    have hB : Integrable (reflectedCoefficient A) := hA.comp_neg.neg
    have hh := positiveEvolution_total_bound (reflectedCoefficient A) hB (-x) (by linarith)
    have he : (∫ s : ℝ, ‖reflectedCoefficient A s‖) = ∫ s : ℝ, ‖A s‖ := by
      simp only [reflectedCoefficient,norm_neg]
      exact integral_neg_eq_self (fun s : ℝ => ‖A s‖) volume
    rw [he] at hh
    exact hh

/-- The true evolution bound depends on total coefficient mass and has no position growth. -/
theorem rawInteractionEvolution_global_bound (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    ‖rawInteractionEvolution q k x‖ ≤ Real.exp (|k| * rawInteractionMass q) :=
  (caratheodoryEvolution_total_bound (rawInteractionOperator q k) (rawInteractionOperator_integrable q k) x).trans
    (Real.exp_le_exp.mpr (integral_norm_rawInteractionOperator q k))

theorem rawInteractionSolution_global_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawInteractionSolution q k v x‖ ≤ ‖v‖*Real.exp (|k| * rawInteractionMass q) := by
  have hh := ((rawInteractionEvolution q k x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (rawInteractionEvolution_global_bound q k x) (norm_nonneg v))
  convert! hh using 1
  exact mul_comm _ _

def rawInteractionDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawInteractionOperator q k x (rawInteractionSolution q k v x)

theorem continuous_rawInteractionDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawInteractionDerivative q k v) :=
  (continuous_rawInteractionOperator q k).clm_apply (continuous_rawInteractionSolution q k v)

/-- One fixed integrable majorant controls the actual derivative on the entire line. -/
theorem rawInteractionDerivative_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawInteractionDerivative q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*|k| * rawInteractionDensity q x := by
  have hh := ((rawInteractionOperator q k x).le_opNorm (rawInteractionSolution q k v x)).trans
    (mul_le_mul_of_nonneg_right (rawInteractionOperator_bound q k x) (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (rawInteractionSolution_global_bound q k v x)
    (mul_nonneg (abs_nonneg k) (rawInteractionDensity_nonneg q x))
  exact hh.trans (hb.trans_eq (by ring))

theorem rawInteractionDerivative_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Integrable (rawInteractionDerivative q k v) :=
  ((rawInteractionDensity_integrable q).const_mul ((‖v‖*Real.exp (|k| * rawInteractionMass q))*|k|)).mono'
    (continuous_rawInteractionDerivative q k v).aestronglyMeasurable
    (Eventually.of_forall (rawInteractionDerivative_bound q k v))

/-- Total variation has the expected first-order spectral bound, uniformly for arbitrary initial vectors. -/
theorem integral_norm_rawInteractionDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    (∫ x : ℝ, ‖rawInteractionDerivative q k v x‖) ≤
      ‖v‖*Real.exp (|k| * rawInteractionMass q)*|k| * rawInteractionMass q := by
  have hh := integral_mono (rawInteractionDerivative_integrable q k v).norm
    ((rawInteractionDensity_integrable q).const_mul ((‖v‖*Real.exp (|k| * rawInteractionMass q))*|k|))
    (rawInteractionDerivative_bound q k v)
  simpa only [integral_const_mul,rawInteractionMass] using hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
