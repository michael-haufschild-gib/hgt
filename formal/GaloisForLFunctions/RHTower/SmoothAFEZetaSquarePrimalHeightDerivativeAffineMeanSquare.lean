import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalHeightDerivativeMass
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquareInfinite

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Positive-index coefficient for the differentiated primal square-AFE source. -/
def smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient
    (N : ℕ) (center : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then 0
  else smoothAFEZetaSquarePrimalNatCoefficient N center k *
    Complex.log (k : ℂ) * (-I)

@[simp] theorem smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_zero
    (N : ℕ) (center : ℝ) :
    smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center 0 = 0 := by
  simp [smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient]

@[simp] theorem smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ
    (N : ℕ) (center : ℝ) (n : ℕ) :
    smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center (n + 1) =
      smoothAFEZetaSquarePrimalNatCoefficient N center (n + 1) *
        Complex.log (n + 1 : ℂ) * (-I) := by
  simp [smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient]

theorem norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ
    (N : ℕ) (center : ℝ) (n : ℕ) :
    ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center (n + 1)‖ =
      ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N 0 n‖ := by
  have hNcases : N = 0 ∨ N ≠ 0 := eq_or_ne N 0
  rw [smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ,
    smoothAFEZetaSquarePrimalNatCoefficient_succ]
  simp only [smoothAFEZetaSquarePrimalHeightDerivativeTerm,
    norm_mul, Complex.norm_natCast,
    norm_natSucc_cpow_linePt_sub_one_dualMass,
    norm_natSucc_cpow_neg_linePt, norm_neg, norm_I, mul_one]
  rcases hNcases with rfl | hN
  · simp [smoothAFEZetaSquarePrimalCutoff, smoothAFECutoff]
    ring
  · rw [smoothAFEZetaSquarePrimalCutoff_mul_conductor]
    · ring
    · exact_mod_cast hN

theorem norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ_sq_eq_plainMass
    (N : ℕ) (center : ℝ) (n : ℕ) :
    ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center (n + 1)‖ ^ (2 : ℕ) =
      smoothAFEZetaSquarePrimalHeightDerivativePlainMass N n := by
  rw [norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ]
  rfl

theorem natSucc_mul_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_weightedMass
    (N : ℕ) (center : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) *
        ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center (n + 1)‖ ^ (2 : ℕ) =
      smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N n := by
  rw [norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ_sq_eq_plainMass]
  rfl

theorem summable_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_affine_masses
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    Summable (fun k : ℕ =>
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖) ∧
    Summable (fun k : ℕ =>
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) ∧
    Summable (fun k : ℕ => (k : ℝ) *
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) := by
  obtain ⟨hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquarePrimalHeightDerivativeMasses hN
  constructor
  · apply (summable_nat_add_iff (f := fun k : ℕ =>
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖) 1).mp
    exact (summable_norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_zero hN).congr
      (fun n => (norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ
        N center n).symm)
  constructor
  · apply (summable_nat_add_iff (f := fun k : ℕ =>
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) 1).mp
    exact hplain.congr (fun n =>
      (norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ_sq_eq_plainMass
        N center n).symm)
  · apply (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) *
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) 1).mp
    exact hweighted.congr (fun n =>
      (natSucc_mul_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_weightedMass
        N center n).symm)

theorem tsum_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_plainMass
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    (∑' k : ℕ,
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) =
      ∑' n : ℕ, smoothAFEZetaSquarePrimalHeightDerivativePlainMass N n := by
  have hsum :=
    (summable_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_affine_masses
      hN center).2.1
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' k : ℕ,
        ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) =
      ∑' n : ℕ,
        ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center (n + 1)‖ ^ (2 : ℕ) := by
      rw [← hsplit]
      simp
    _ = ∑' n : ℕ, smoothAFEZetaSquarePrimalHeightDerivativePlainMass N n := by
      apply tsum_congr
      intro n
      exact norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_succ_sq_eq_plainMass
        N center n

theorem tsum_weighted_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_weightedMass
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    (∑' k : ℕ, (k : ℝ) *
      ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) =
      ∑' n : ℕ, smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N n := by
  have hsum :=
    (summable_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_affine_masses
      hN center).2.2
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' k : ℕ, (k : ℝ) *
        ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
        ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center (n + 1)‖ ^ (2 : ℕ) := by
      rw [← hsplit]
      simp
    _ = ∑' n : ℕ, smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N n := by
      apply tsum_congr
      intro n
      exact natSucc_mul_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_weightedMass
        N center n

/-- Infinite affine mean square for the differentiated primal source. -/
theorem exists_integral_normSq_smoothAFEZetaSquarePrimalHeightDerivativeLSeries_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : ℕ} {center H : ℝ},
      4 ≤ N → 1 ≤ H →
      (∫ y in Set.Icc (-H) H,
        ‖LSeries
          (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center)
          ((y : ℝ) * I)‖ ^ (2 : ℕ)) ≤
        5 * Real.pi * Real.exp 1 *
            (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (5 : ℕ)) +
          (5 * Real.pi / 2) *
            (B * (1 + Real.log (N : ℝ)) ^ (6 : ℕ)) * H := by
  obtain ⟨B, hB, hmass⟩ :=
    exists_tsum_smoothAFEZetaSquarePrimalHeightDerivativeMasses_le
  refine ⟨B, hB, ?_⟩
  intro N center H hN hH
  obtain ⟨habs, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_affine_masses
      hN center
  have hmv :=
    RHTower.Sieve.integral_Icc_normSq_LSeries_le_general_affine_infinite
      (a := smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center)
      (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_zero N center) 0
      (by simpa using habs) (by simpa using hplain) (by simpa using hweighted) hH
  have hmv' :
      (∫ y in Set.Icc (-H) H,
        ‖LSeries
          (smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center)
          ((y : ℝ) * I)‖ ^ (2 : ℕ)) ≤
        5 * Real.pi * Real.exp 1 *
          (∑' k : ℕ, (k : ℝ) *
            ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) +
        (5 * Real.pi / 2) *
          (∑' k : ℕ,
            ‖smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient N center k‖ ^ (2 : ℕ)) * H := by
    simpa using hmv
  obtain ⟨hweightedMass, hplainMass⟩ := hmass hN
  rw [tsum_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_plainMass
      hN center,
    tsum_weighted_norm_smoothAFEZetaSquarePrimalHeightDerivativeNatCoefficient_sq_eq_weightedMass
      hN center] at hmv'
  exact hmv'.trans (by gcongr)

end RHTower
