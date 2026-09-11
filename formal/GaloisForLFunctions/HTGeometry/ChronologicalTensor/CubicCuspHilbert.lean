import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedLine
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Graded dimensions and Hilbert series of the observation algebra and its normalization

In weight zero both the observation algebra `A` and its normalization `B = ℝ[u,c]` reduce to the
constants. In weight `n ≥ 1` the available graded piece has dimension `n` and the full homogeneous
space has dimension `n+1`, so the graded normalization defect is a line in every positive weight.
Equivalently, in the three formal power series identities below,

  `Hilb_A(z) = (1 − z + z²)/(1 − z)²`,  `Hilb_B(z) = 1/(1 − z)²`,  `Hilb_Q(z) = z/(1 − z)`.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section
open Polynomial

/-! ### Graded dimensions -/

/-- In weight zero there is no defect: a homogeneous observation of weight zero is a constant,
hence already an available cusp observation. -/
theorem cubicHomogeneousSpace_zero_available (P : cubicHomogeneousSpace 0) :
    P.val ∈ cubicCuspAlgebra := by
  rw [cubicCuspAlgebra_mem, ← cubicHomogeneousCoordinates_reconstruct 0 P]
  simp [cubicHomogeneousPolynomial]

/-- The available graded piece of weight `k+1` has dimension `k+1`. -/
theorem cubicGradedAvailable_finrank (k : ℕ) :
    Module.finrank ℝ (cubicGradedAvailable k) = k + 1 := by
  letI := cubicHomogeneousSpace_finiteDimensional (k+1)
  letI : AddCommGroup ↥(cubicHomogeneousSpace (k+1)) := inferInstance
  have hrange : LinearMap.range (cubicGradedCoefficient k) = ⊤ :=
    LinearMap.range_eq_top.mpr (cubicGradedCoefficient_surjective k)
  have h := LinearMap.finrank_range_add_finrank_ker (cubicGradedCoefficient k)
  rw [hrange, finrank_top, Module.finrank_self, cubicHomogeneousSpace_finrank] at h
  rw [cubicGradedAvailable]
  omega

/-- The graded normalization defect is one-dimensional in every positive weight; this is the
already formalized `cubicGradedLine_finrank`. -/
theorem cubicGradedDefect_finrank (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    letI := cubicGradedLineNormedSpace k
    Module.finrank ℝ (cubicGradedDefect k) = 1 :=
  cubicGradedLine_finrank k

/-! ### Hilbert series -/

theorem cuspPowerSeries_coeff_X_sq (n : ℕ) :
    (PowerSeries.coeff n) ((PowerSeries.X : PowerSeries ℝ)^2) = if n = 2 then 1 else 0 := by
  rw [pow_two]
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul]
    simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X]
    by_cases hm : m = 1
    · rw [if_pos hm, if_pos (by omega)]
    · rw [if_neg hm, if_neg (by omega)]

/-- Multiplying a generating function by `1 − z` takes first differences of its coefficients. -/
theorem cuspPowerSeries_one_sub_X_mul (f : ℕ → ℝ) :
    ((1 : PowerSeries ℝ) - PowerSeries.X) * PowerSeries.mk f
      = PowerSeries.mk (fun n => if n = 0 then f 0 else f n - f (n-1)) := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_X_mul, if_pos rfl, sub_zero]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, if_neg (by omega)]
    simp

/-- The Hilbert function of the cusp observation algebra `A = ℝ[u, c², c³]`. -/
def cuspHilbertA : ℕ → ℝ := fun n => if n = 0 then 1 else (n : ℝ)

/-- The Hilbert function of the normalization `B = ℝ[u, c]`. -/
def cuspHilbertB : ℕ → ℝ := fun n => (n : ℝ) + 1

/-- The Hilbert function of the graded normalization defect `Q = B/A`. -/
def cuspHilbertQ : ℕ → ℝ := fun n => if n = 0 then 0 else 1

theorem cuspHilbertA_finrank (k : ℕ) :
    cuspHilbertA (k+1) = (Module.finrank ℝ (cubicGradedAvailable k) : ℝ) := by
  rw [cubicGradedAvailable_finrank, cuspHilbertA, if_neg (by omega)]

theorem cuspHilbertB_finrank (k : ℕ) :
    cuspHilbertB k = (Module.finrank ℝ (cubicHomogeneousSpace k) : ℝ) := by
  rw [cubicHomogeneousSpace_finrank, cuspHilbertB]
  push_cast
  ring

theorem cuspHilbertQ_finrank (k : ℕ) :
    letI := cubicGradedLineNormedGroup k
    letI := cubicGradedLineNormedSpace k
    cuspHilbertQ (k+1) = (Module.finrank ℝ (cubicGradedDefect k) : ℝ) := by
  letI := cubicGradedLineNormedGroup k
  letI := cubicGradedLineNormedSpace k
  rw [cubicGradedDefect_finrank, cuspHilbertQ, if_neg (by omega)]
  norm_num

/-- `Hilb_A(z) = (1 − z + z²)/(1 − z)²`. -/
theorem cuspHilbertA_series :
    ((1 : PowerSeries ℝ) - PowerSeries.X)^2 * PowerSeries.mk cuspHilbertA
      = 1 - PowerSeries.X + PowerSeries.X^2 := by
  rw [pow_two, mul_assoc, cuspPowerSeries_one_sub_X_mul, cuspPowerSeries_one_sub_X_mul]
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X,
    cuspPowerSeries_coeff_X_sq]
  rcases n with _ | m
  · norm_num [cuspHilbertA]
  rcases m with _ | m
  · norm_num [cuspHilbertA]
  rcases m with _ | m
  · norm_num [cuspHilbertA]
  · rw [if_neg (by omega : ¬ (m+3 = 0)), if_neg (by omega : ¬ (m+3 = 1)),
      if_neg (by omega : ¬ (m+3 = 2))]
    simp only [cuspHilbertA, if_neg (by omega : ¬ (m+3 = 0))]
    push_cast
    ring

/-- `Hilb_B(z) = 1/(1 − z)²`. -/
theorem cuspHilbertB_series :
    ((1 : PowerSeries ℝ) - PowerSeries.X)^2 * PowerSeries.mk cuspHilbertB = 1 := by
  rw [pow_two, mul_assoc, cuspPowerSeries_one_sub_X_mul, cuspPowerSeries_one_sub_X_mul]
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases n with _ | m
  · norm_num [cuspHilbertB]
  rcases m with _ | m
  · norm_num [cuspHilbertB]
  · rw [if_neg (by omega : ¬ (m+2 = 0))]
    simp only [cuspHilbertB, if_neg (by omega : ¬ (m+2 = 0))]
    push_cast
    ring

/-- `Hilb_Q(z) = z/(1 − z)`. -/
theorem cuspHilbertQ_series :
    ((1 : PowerSeries ℝ) - PowerSeries.X) * PowerSeries.mk cuspHilbertQ = PowerSeries.X := by
  rw [cuspPowerSeries_one_sub_X_mul]
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_X]
  rcases n with _ | m
  · norm_num [cuspHilbertQ]
  rcases m with _ | m
  · norm_num [cuspHilbertQ]
  · rw [if_neg (by omega : ¬ (m+2 = 0)), if_neg (by omega : ¬ (m+2 = 1))]
    simp only [cuspHilbertQ, if_neg (by omega : ¬ (m+2 = 0))]
    split_ifs with hq
    · exact absurd hq (by omega)
    · ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
