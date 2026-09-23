import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftVariationBound
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour

/-!
# Frozen chi-ratio error against the critical divisor carrier

On a short subinterval of a dyadic height block, freeze the exact AFE chi ratio at one height.
The slow-variation theorem makes the coefficient error at most `L * H`; the existing affine
mean-square theorem then prices the entire error without summing coefficients absolutely.  This is
the first oscillation-preserving moving-coefficient transfer for the Route-T fourth-moment bridge.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower.Sieve

/-- Mean-square cost of freezing the exact chi ratio on a short interval.  No coefficientwise
triangle inequality is used: the error remains multiplied by the full critical divisor
polynomial and is charged through its affine mean square. -/
theorem integral_Icc_normSq_chiRatio_freezingError_criticalDivisor_le
    (N : ℕ) (hN : 1 ≤ N) {T a b u H v : ℝ}
    (hT : 4 ≤ T) (ha : a ∈ Set.Icc T (2 * T)) (hb : b ∈ Set.Icc T (2 * T))
    (hu : u ∈ Set.Icc a b) (hH : b - a ≤ H)
    (hv : 2 * |v| ≤ T) :
    (∫ t in Set.Icc a b,
      ‖(smoothAFEZetaChiShiftRatio (linePt t)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          smoothAFEZetaChiShiftRatio (linePt u)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) *
        criticalDivisorPolynomial N t‖ ^ (2 : ℕ)) ≤
      ((((1 + 2 * T) * (6 + 2 * Real.pi) * (1 + |v|) ^ (2 : ℕ) / T) * H) ^ (2 : ℕ)) *
        (5 * Real.pi * Real.exp 1 * ((N : ℝ) * (1 + Real.log N) ^ (3 : ℕ)) +
          (5 * Real.pi / 2) * (1 + Real.log N) ^ (4 : ℕ) * (2 * T)) := by
  let r : ℝ → ℂ := fun t => smoothAFEZetaChiShiftRatio (linePt t)
    (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))
  let P : ℝ → ℂ := criticalDivisorPolynomial N
  let L : ℝ := (1 + 2 * T) * (6 + 2 * Real.pi) * (1 + |v|) ^ (2 : ℕ) / T
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hcontR : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line t v).continuousAt
  have hcontP : Continuous P := by
    dsimp only [P, criticalDivisorPolynomial]
    exact RHTower.Sieve.continuous_LSeries_line_of_support (by simp)
      (fun _n hn => criticalDivisorSeq_support hn) 0
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖(r t - r u) * P t‖ ^ (2 : ℕ) ≤ (L * H) ^ (2 : ℕ) * ‖P t‖ ^ (2 : ℕ) := by
    intro t ht
    have htDy : t ∈ Set.Icc T (2 * T) := ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
    have huDy : u ∈ Set.Icc T (2 * T) :=
      ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
    have hvar := norm_smoothAFEZetaChiShiftRatio_sub_le_dyadic hT htDy huDy hv
    have htu : |t - u| ≤ H := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, hu.1, hu.2, hH]
    have hvarH : ‖r t - r u‖ ≤ L * H := by
      exact hvar.trans (mul_le_mul_of_nonneg_left htu hL0)
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hvarH 2)
      (sq_nonneg _)
  have hmonoPoint :
      (∫ t in Set.Icc a b, ‖(r t - r u) * P t‖ ^ (2 : ℕ)) ≤
        ∫ t in Set.Icc a b, (L * H) ^ (2 : ℕ) * ‖P t‖ ^ (2 : ℕ) := by
    apply MeasureTheory.setIntegral_mono_on
    · exact (((hcontR.sub continuous_const).mul hcontP).norm.pow 2).integrableOn_Icc
    · exact (continuous_const.mul (hcontP.norm.pow 2)).integrableOn_Icc
    · exact measurableSet_Icc
    · exact hpoint
  have hsubset : Set.Icc a b ⊆ Set.Icc (-(2 * T)) (2 * T) := by
    intro t ht
    constructor
    · linarith [hT0, ha.1, ht.1]
    · exact ht.2.trans hb.2
  have hPmono :
      (∫ t in Set.Icc a b, ‖P t‖ ^ (2 : ℕ)) ≤
        ∫ t in Set.Icc (-(2 * T)) (2 * T), ‖P t‖ ^ (2 : ℕ) := by
    exact MeasureTheory.setIntegral_mono_set (hcontP.norm.pow 2).integrableOn_Icc
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hsubset)
  have hMS := integral_Icc_normSq_criticalDivisorPolynomial_le N hN
    (T := 2 * T) (by linarith)
  have hMS' :
      (∫ t in Set.Icc (-(2 * T)) (2 * T), ‖P t‖ ^ (2 : ℕ)) ≤
        5 * Real.pi * Real.exp 1 * ((N : ℝ) * (1 + Real.log N) ^ (3 : ℕ)) +
          (5 * Real.pi / 2) * (1 + Real.log N) ^ (4 : ℕ) * (2 * T) := by
    simpa only [P] using hMS
  change (∫ t in Set.Icc a b, ‖(r t - r u) * P t‖ ^ (2 : ℕ)) ≤ _
  refine hmonoPoint.trans ?_
  rw [MeasureTheory.integral_const_mul]
  calc
    (L * H) ^ (2 : ℕ) * (∫ t in Set.Icc a b, ‖P t‖ ^ (2 : ℕ))
        ≤ (L * H) ^ (2 : ℕ) * (∫ t in Set.Icc (-(2 * T)) (2 * T), ‖P t‖ ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hPmono (sq_nonneg _)
    _ ≤ (L * H) ^ (2 : ℕ) *
        (5 * Real.pi * Real.exp 1 * ((N : ℝ) * (1 + Real.log N) ^ (3 : ℕ)) +
          (5 * Real.pi / 2) * (1 + Real.log N) ^ (4 : ℕ) * (2 * T)) := by
          exact mul_le_mul_of_nonneg_left hMS' (sq_nonneg _)
    _ = _ := by rfl

end RHTower.Sieve
