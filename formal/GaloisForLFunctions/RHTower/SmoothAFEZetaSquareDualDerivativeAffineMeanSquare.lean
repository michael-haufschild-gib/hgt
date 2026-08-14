import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeMass
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquareInfinite

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Positive-integer reindexing retaining the full critical Dirichlet phase. -/
def smoothAFEZetaSquareDualDerivativeNatCoefficient
    (T r center : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then 0
  else smoothAFEZetaSquareDualDerivativeCoefficient T r center (k - 1)

@[simp] theorem smoothAFEZetaSquareDualDerivativeNatCoefficient_zero
    (T r center : ℝ) :
    smoothAFEZetaSquareDualDerivativeNatCoefficient T r center 0 = 0 := by
  simp [smoothAFEZetaSquareDualDerivativeNatCoefficient]

@[simp] theorem smoothAFEZetaSquareDualDerivativeNatCoefficient_succ
    (T r center : ℝ) (n : ℕ) :
    smoothAFEZetaSquareDualDerivativeNatCoefficient T r center (n + 1) =
      smoothAFEZetaSquareDualDerivativeCoefficient T r center n := by
  simp [smoothAFEZetaSquareDualDerivativeNatCoefficient]

theorem summable_norm_smoothAFEZetaSquareDualDerivativeCoefficient
    {T r center : ℝ} (hr : 4 ≤ r) (hT : 0 < T) :
    Summable (fun n : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeCoefficient T r center n‖) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_large_power
  have hbase : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(599 / 400 : ℝ)) < -1 by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ ↦
        (n : ℝ) ^ (-(599 / 400 : ℝ))) 1).mpr h
  let A : ℝ := K * (1 + r) / T
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  exact Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _)
    (fun n ↦ hcoefficient hr hT) (hbase.mul_left A)

theorem summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
    {T r center : ℝ} (hr : 4 ≤ r) (hT : 0 < T) :
    Summable (fun k : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖) ∧
    Summable (fun k : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ 2) ∧
    Summable (fun k : ℕ ↦
      (k : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ 2) := by
  obtain ⟨hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeCoefficient_masses
      (t := center) hr hT
  have habsCoeff :=
    summable_norm_smoothAFEZetaSquareDualDerivativeCoefficient
      (center := center) hr hT
  constructor
  · apply (summable_nat_add_iff (f := fun k : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖) 1).mp
    simpa using habsCoeff
  constructor
  · apply (summable_nat_add_iff (f := fun k : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ 2) 1).mp
    simpa using hplain
  · apply (summable_nat_add_iff (f := fun k : ℕ ↦
      (k : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ 2) 1).mp
    simpa [Nat.cast_add, Nat.cast_one] using hweighted

theorem tsum_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    {T r center : ℝ} (hr : 4 ≤ r) (hT : 0 < T) :
    (∑' k : ℕ,
      ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ 2) =
      ∑' n : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r center n‖ ^ 2 := by
  have hsum :=
    (summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr hT).2.1
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simpa using hsplit.symm

theorem tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    {T r center : ℝ} (hr : 4 ≤ r) (hT : 0 < T) :
    (∑' k : ℕ,
      (k : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeNatCoefficient T r center k‖ ^ 2) =
      ∑' n : ℕ,
        (n + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient T r center n‖ ^ 2 := by
  have hsum :=
    (summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr hT).2.2
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simpa [Nat.cast_add, Nat.cast_one] using hsplit.symm

/-- Phase-faithful infinite affine mean-square bound on a centered cell. -/
theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_dyadic :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) → 1 ≤ H →
        (∫ y in Set.Icc (-H) H,
          ‖LSeries
            (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
            ((y : ℝ) * I)‖ ^ 2) ≤
          5 * Real.pi * Real.exp 1 *
              (B * (N : ℝ) ^ (-(199 / 200 : ℝ))) +
            (5 * Real.pi / 2) *
              (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * H := by
  obtain ⟨A, B, hA, hB, hmass⟩ :=
    exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_masses_le_dyadic
  refine ⟨A, B, hA, hB, ?_⟩
  intro N r center H hN hr hH
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    exact hN4real.trans hr.1
  obtain ⟨habs, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr4 hN0
  have hmv :=
    RHTower.Sieve.integral_Icc_normSq_LSeries_le_general_affine_infinite
      (a := smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
      (smoothAFEZetaSquareDualDerivativeNatCoefficient_zero _ _ _) 0
      (by simpa using habs) (by simpa using hplain) (by simpa using hweighted) hH
  have hmv' :
      (∫ y in Set.Icc (-H) H,
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (∑' k : ℕ, (k : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ 2) +
          (5 * Real.pi / 2) *
            (∑' k : ℕ,
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ 2) * H := by
    simpa using hmv
  obtain ⟨hplainMass, hweightedMass⟩ := hmass (t := center) hN hr
  rw [tsum_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    (center := center) hr4 hN0] at hmv'
  rw [tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    (center := center) hr4 hN0] at hmv'
  exact hmv'.trans (by
    gcongr)

end RHTower
