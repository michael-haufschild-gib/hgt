import GaloisForLFunctions.HTGeometry.GomesPolynomialAffineTilt
import GaloisForLFunctions.RHTower.EntireExponentialMomentPolynomialDensity

/-!
# Entire exponential windows for polynomial tensor profiles

Affine tilt closure supplies every real exponential moment of each finite raw
polynomial density. Total mass normalization also has an entire window for every
polynomial, including the zero-measure collapse of infinite-mass inputs.
-/

noncomputable section
open Polynomial MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Every real exponential is integrable against every finite raw polynomial density. -/
theorem gomesPolynomialMeasure_exp_integrable (P : GomesFinitePolynomialProfile) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gomesDilatonMeasure P.val) := by
  change Integrable _ (volume.withDensity (fun x => ENNReal.ofReal (dilatonWeight P.val x)))
  rw [integrable_withDensity_iff_integrable_smul'
    (gomesDilatonWeight_continuous P.val).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have h := (gomesDilatonMeasure_finite_iff_integrable
    (gomesPolynomialAffineTilt P.val t 0)).mp (gomesFinitePolynomialTilt P t 0).property
  apply h.congr (Eventually.of_forall (fun x => ?_))
  rw [ENNReal.toReal_ofReal (dilatonWeight_pos P.val x).le, smul_eq_mul]
  simp only [dilatonWeight, gomesPolynomialAffineTilt, eval_add, eval_mul, eval_C,
    eval_X, add_zero, Real.exp_add]

/-- The raw finite polynomial sector has an entire exponential-moment window. -/
theorem gomesPolynomialMeasure_entireExponentialMoments (P : GomesFinitePolynomialProfile) :
    RHTower.HasEntireExponentialMoments (gomesDilatonMeasure P.val) := by
  ext t
  constructor
  · intro _; exact Set.mem_univ _
  · intro _
    exact gomesPolynomialMeasure_exp_integrable P t

/-- Every normalized polynomial measure is finite, including collapsed infinite-mass inputs. -/
theorem gomesPolynomialNormalized_finite (H : ℝ[X]) :
    IsFiniteMeasure (gomesDilatonMassNormalized H) := by
  classical
  by_cases h : IsFiniteMeasure (gomesDilatonMeasure H)
  · letI : IsProbabilityMeasure (gomesDilatonMassNormalized H) :=
      (gomesDilatonMassNormalized_probability_iff H).mpr h
    infer_instance
  · have ht : gomesDilatonMeasure H Set.univ = ∞ :=
      le_antisymm le_top (not_lt.mp (fun hl => h ((isFiniteMeasure_iff _).mpr hl)))
    rw [(gomesDilatonMassNormalized_zero_iff H).mpr ht]
    infer_instance

/-- All normalized polynomial measures integrate every real exponential. -/
theorem gomesPolynomialNormalized_exp_integrable (H : ℝ[X]) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gomesDilatonMassNormalized H) := by
  classical
  by_cases h : IsFiniteMeasure (gomesDilatonMeasure H)
  · exact (gomesPolynomialMeasure_exp_integrable ⟨H, h⟩ t).smul_measure
      (ENNReal.inv_ne_top.mpr (gomesDilatonMeasure_mass_ne_zero H))
  · have ht : gomesDilatonMeasure H Set.univ = ∞ :=
      le_antisymm le_top (not_lt.mp (fun hl => h ((isFiniteMeasure_iff _).mpr hl)))
    rw [(gomesDilatonMassNormalized_zero_iff H).mpr ht]
    exact integrable_zero_measure

/-- Total normalization always has an entire window, even when it produces the zero measure. -/
theorem gomesPolynomialNormalized_entireExponentialMoments (H : ℝ[X]) :
    RHTower.HasEntireExponentialMoments (gomesDilatonMassNormalized H) := by
  ext t
  constructor
  · intro _; exact Set.mem_univ _
  · intro _
    exact gomesPolynomialNormalized_exp_integrable H t

/-- Every real exponential belongs to the raw profile's real L² space. -/
theorem gomesPolynomialMeasure_exp_memLp_two (P : GomesFinitePolynomialProfile) (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t * x)) 2 (gomesDilatonMeasure P.val) :=
  RHTower.exp_mul_memLp_two_of_entireExponentialMoments
    (gomesPolynomialMeasure_entireExponentialMoments P) t

/-- Every raw polynomial moment is represented by an actual real L² vector. -/
theorem gomesPolynomialMeasure_pow_memLp_two (P : GomesFinitePolynomialProfile) (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n) 2 (gomesDilatonMeasure P.val) :=
  RHTower.monomial_memLp_two_of_entireExponentialMoments
    (gomesPolynomialMeasure_entireExponentialMoments P) n

/-- Every normalized exponential observable belongs to L², including the zero-space case. -/
theorem gomesPolynomialNormalized_exp_memLp_two (H : ℝ[X]) (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t * x)) 2 (gomesDilatonMassNormalized H) :=
  RHTower.exp_mul_memLp_two_of_entireExponentialMoments
    (gomesPolynomialNormalized_entireExponentialMoments H) t

/-- Every normalized polynomial moment belongs to L² for every input polynomial. -/
theorem gomesPolynomialNormalized_pow_memLp_two (H : ℝ[X]) (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n) 2 (gomesDilatonMassNormalized H) :=
  RHTower.monomial_memLp_two_of_entireExponentialMoments
    (gomesPolynomialNormalized_entireExponentialMoments H) n

end GaloisForLFunctions.HTGeometry
