import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare
import GaloisForLFunctions.SquareRootThreshold.WindowedMeanValueDiagonalLaw
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial

/-!
# A high-frequency mass bound for logarithmic atoms

The logarithms of integers through `N` are `1/N`-separated. The interval
Montgomery–Vaughan inequality therefore retains `48 N` times coefficient
mass on `[N,101 N]`. The interval stays away from zero and is independent
of the coefficient vector, as required by a Gamma-energy lower bound.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open HTGeometry SquareRootThreshold SpacingScaleHarmonicAnalysis

/-- Normalized logarithmic frequencies have the explicit integer-separation gap. -/
theorem normalized_log_gap {N n j : ℕ} (hN : 0 < N)
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j) :
    1 / (2 * Real.pi * N) ≤
      |Real.log n / (2 * Real.pi) - Real.log j / (2 * Real.pi)| := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 1 / (N : ℝ) ≤ |Real.log n - Real.log j| := by
    rcases lt_or_gt_of_ne hnj with h | h
    · have hg := inv_le_log_sub_log (mem_Icc.mp hn).1 h
        (by exact_mod_cast (mem_Icc.mp hj).2 : (j : ℝ) ≤ N)
      rw [abs_sub_comm, abs_of_nonneg ((by positivity : (0 : ℝ) < 1 / N).le.trans hg)]
      exact hg
    · have hg := inv_le_log_sub_log (mem_Icc.mp hj).1 h
        (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ N)
      rw [abs_of_nonneg ((by positivity : (0 : ℝ) < 1 / N).le.trans hg)]
      exact hg
  rw [← sub_div, abs_div, abs_of_pos (mul_pos two_pos Real.pi_pos)]
  have h := div_le_div_of_nonneg_right hlog (mul_pos two_pos Real.pi_pos).le
  convert h using 1 <;> ring

/-- Every coefficient vector retains a fixed mass in a band proportional to its horizon. -/
theorem dirichletPoly_highBand_mass {N : ℕ} (hN : 0 < N) (x : ℕ → ℝ) :
    (48 * (N : ℝ)) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      ∫ t in (N : ℝ)..(101 * N), ‖dirichletPoly N x (t : ℂ)‖ ^ 2 := by
  classical
  let S := Icc 1 N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := interval_integral_normSq_expSum_ge
    (fun n : S => Real.log (n : ℕ) / (2 * Real.pi))
    (fun n : S => (x n : ℂ))
    (D := 1 / (2 * Real.pi * N)) (a := N) (ℓ := 100 * N)
    (by positivity)
    (fun n j hnj => normalized_log_gap hN n.property j.property
      (fun heq => hnj (Subtype.ext heq)))
  have hcost : 26 / (Real.pi * (1 / (2 * Real.pi * (N : ℝ)))) = 52 * N := by
    field_simp [Real.pi_ne_zero, hNR.ne']
    ring
  have hmass : (∑ n : S, ‖(x n : ℂ)‖ ^ 2) = ∑ n ∈ Icc 1 N, x n ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact sum_coe_sort S (fun n => x n ^ 2)
  have hpoly (t : ℝ) :
      (∑ n : S, (x n : ℂ) * mvExp (Real.log (n : ℕ) / (2 * Real.pi)) t) =
        dirichletPoly N x t := by
    have he (n : ℕ) : mvExp (Real.log n / (2 * Real.pi)) t =
        Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
      unfold mvExp
      congr 1
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    simp only [he]
    exact sum_coe_sort S (fun n => (x n : ℂ) * Complex.exp (Complex.I * t * (Real.log n : ℂ)))
  have hend : (N : ℝ) + 100 * N = 101 * N := by ring
  have hcoef : 100 * (N : ℝ) - 52 * N = 48 * N := by ring
  simpa only [hcost, hmass, hpoly, hend, hcoef] using h

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.dirichletPoly_highBand_mass
