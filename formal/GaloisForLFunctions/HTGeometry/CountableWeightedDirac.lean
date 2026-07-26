import GaloisForLFunctions.HTGeometry.SemidefiniteCarrier
import GaloisForLFunctions.HTGeometry.ChristoffelPointMass

/-!
# Countable weighted Dirac measures

A leaf of an extremal family is carried by the zero set of an entire function, which is discrete and
countable rather than finite.  This module provides the countable analogue of the finite weighted
Dirac families of the Gauss construction: the measure `∑ₙ wₙ δ_{xₙ}` as a `Measure.sum`, its lower
integrals, and its total mass.

Everything here is independent of where the points come from.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

/-- A countable weighted sum of point masses. -/
noncomputable def countableWeightedDirac (w : ℕ → ℝ) (x : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun n => ENNReal.ofReal (w n) • Measure.dirac (x n)

/-- **Lower integration against a countable weighted Dirac family.** -/
theorem lintegral_countableWeightedDirac (w : ℕ → ℝ) (x : ℕ → ℝ) (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(countableWeightedDirac w x) = ∑' n, ENNReal.ofReal (w n) * f (x n) := by
  rw [countableWeightedDirac, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- Evaluation on a measurable set. -/
theorem countableWeightedDirac_apply (w : ℕ → ℝ) (x : ℕ → ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    countableWeightedDirac w x A = ∑' n, ENNReal.ofReal (w n) * A.indicator 1 (x n) := by
  rw [countableWeightedDirac, Measure.sum_apply _ hA]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]

/-- The total mass is the sum of the weights. -/
theorem countableWeightedDirac_univ (w : ℕ → ℝ) (x : ℕ → ℝ) :
    countableWeightedDirac w x Set.univ = ∑' n, ENNReal.ofReal (w n) := by
  rw [countableWeightedDirac_apply w x MeasurableSet.univ]
  refine tsum_congr fun n => ?_
  simp

/-- **The atom at a listed point is its weight**, when the points are distinct. -/
theorem countableWeightedDirac_singleton (w : ℕ → ℝ) {x : ℕ → ℝ}
    (hinj : Function.Injective x) (m : ℕ) :
    countableWeightedDirac w x {x m} = ENNReal.ofReal (w m) := by
  classical
  rw [countableWeightedDirac_apply w x (measurableSet_singleton (x m))]
  rw [tsum_eq_single m]
  · rw [Set.indicator_of_mem (Set.mem_singleton (x m))]
    simp
  · intro n hn
    rw [Set.indicator_of_notMem, mul_zero]
    simp only [Set.mem_singleton_iff]
    exact fun hc => hn (hinj hc)

/-- A countable weighted Dirac family with nonnegative weights has the weights as real atoms. -/
theorem countableWeightedDirac_real_singleton (w : ℕ → ℝ) {x : ℕ → ℝ}
    (hinj : Function.Injective x) (hw : ∀ n, 0 ≤ w n) (m : ℕ) :
    (countableWeightedDirac w x).real {x m} = w m := by
  rw [Measure.real, countableWeightedDirac_singleton w hinj m,
    ENNReal.toReal_ofReal (hw m)]

/-- **A countable representing measure has Christoffel-bounded weights.**  Each weight is at most
the
limit Christoffel function at its point — the constraint any N-extremal leaf must satisfy. -/
theorem weight_le_christoffelLimit {s : ℕ → ℝ} (h : PositiveMomentForm s) {w x : ℕ → ℝ}
    (hinj : Function.Injective x) (hw : ∀ n, 0 ≤ w n)
    (hrep : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (countableWeightedDirac w x)) (m : ℕ) :
    w m ≤ christoffelLimit s (x m) := by
  rw [← countableWeightedDirac_real_singleton w hinj hw m]
  exact measureReal_singleton_le_christoffelLimit_of_hasMoments h hrep (x m)

/-- The total mass of a nonnegative summable weight family is the sum of the weights. -/
theorem countableWeightedDirac_univ_ofReal {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hsum : Summable w)
    (x : ℕ → ℝ) :
    countableWeightedDirac w x Set.univ = ENNReal.ofReal (∑' n, w n) := by
  rw [countableWeightedDirac_univ, ENNReal.ofReal_tsum_of_nonneg hw hsum]

/-- **Integrability against a countable weighted Dirac family.**  A strongly measurable function is
integrable exactly when its values on the atoms are absolutely summable against the weights. -/
theorem integrable_countableWeightedDirac {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (countableWeightedDirac w x))
    (hsum : Summable fun n => w n * |f (x n)|) :
    Integrable f (countableWeightedDirac w x) := by
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_countableWeightedDirac]
  have hterm : ∀ n, ENNReal.ofReal (w n) * ‖f (x n)‖ₑ = ENNReal.ofReal (w n * |f (x n)|) := by
    intro n
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (hw n)]
  rw [tsum_congr hterm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hw n) (abs_nonneg _)) hsum]
  exact ENNReal.ofReal_lt_top

/-- **Bochner integration against a countable weighted Dirac family.** -/
theorem integral_countableWeightedDirac {w x : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {f : ℝ → ℝ} (hint : Integrable f (countableWeightedDirac w x)) :
    ∫ y, f y ∂(countableWeightedDirac w x) = ∑' n, w n * f (x n) := by
  rw [countableWeightedDirac] at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal (hw n)]

/-- Rescaling all weights by a nonnegative constant rescales the measure. -/
theorem countableWeightedDirac_const_mul {c : ℝ} (hc : 0 ≤ c) (w x : ℕ → ℝ) :
    countableWeightedDirac (fun n => c * w n) x
      = ENNReal.ofReal c • countableWeightedDirac w x := by
  ext A hA
  rw [Measure.smul_apply, countableWeightedDirac_apply _ _ hA,
    countableWeightedDirac_apply _ _ hA, smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul hc, mul_assoc]

end HTGeometry
