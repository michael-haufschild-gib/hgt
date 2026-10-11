import GaloisForLFunctions.RHTower.WeilLogShiftRawTransportLaw
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The raw correction and its complementary index defect are both ordered and centered. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilEdgeCorrectionProfile_hasDerivAt (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun z => finiteWeilEdgeResidualProfile k z + z)
      (((k + 2 : ℕ) : ℝ) ^ 2 /
        ((((k + 2 : ℕ) : ℝ) + x) * (((k + 2 : ℕ) : ℝ) + x + 1))) x := by
  have h : HasDerivAt (fun z => finiteWeilEdgeResidualProfile k z + z)
      (((((k + 2 : ℕ) : ℝ) ^ 2 /
        ((((k + 2 : ℕ) : ℝ) + x) * (((k + 2 : ℕ) : ℝ) + x + 1))) - 1) + 1) x :=
    (finiteWeilEdgeResidualProfile_hasDerivAt k x hx).add (hasDerivAt_id x)
  simpa only [sub_add_cancel] using h

theorem finiteWeilEdgeResidualProfile_antitoneOn (r k : ℕ) :
    AntitoneOn (finiteWeilEdgeResidualProfile k) (Set.Icc (0 : ℝ) r) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro x hx
    exact (finiteWeilEdgeResidualProfile_hasDerivAt k x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    exact (finiteWeilEdgeResidualProfile_hasDerivAt k x (interior_subset hx).1).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := (interior_subset hx).1
    rw [(finiteWeilEdgeResidualProfile_hasDerivAt k x hx0).deriv]
    apply sub_nonpos.mpr
    let A : ℝ := ((k + 2 : ℕ) : ℝ)
    have hA : 0 < A := by dsimp [A]; positivity
    change A ^ 2 / ((A + x) * (A + x + 1)) ≤ 1
    apply (div_le_one (by positivity)).mpr
    nlinarith only [sq_nonneg x, mul_nonneg hA.le hx0, hA.le, hx0]

theorem finiteWeilEdgeCorrectionProfile_monotoneOn (r k : ℕ) :
    MonotoneOn (fun x => finiteWeilEdgeResidualProfile k x + x) (Set.Icc (0 : ℝ) r) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro x hx
    exact (finiteWeilEdgeCorrectionProfile_hasDerivAt k x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    exact (finiteWeilEdgeCorrectionProfile_hasDerivAt k x (interior_subset hx).1).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := (interior_subset hx).1
    rw [(finiteWeilEdgeCorrectionProfile_hasDerivAt k x hx0).deriv]
    positivity

theorem finiteWeilCanonicalRawCorrectionValue_monotone (r k : ℕ) :
    Monotone (finiteWeilCanonicalRawCorrectionValue r k) := by
  have hm (i : Fin (r + 1)) : ((i : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) r := by
    constructor
    · positivity
    · exact_mod_cast (show (i : ℕ) ≤ r by have := i.isLt; omega)
  intro i j hij
  have h := finiteWeilEdgeCorrectionProfile_monotoneOn r k (hm i) (hm j)
    (show ((i : ℕ) : ℝ) ≤ (j : ℕ) by exact_mod_cast (show (i : ℕ) ≤ (j : ℕ) from hij))
  dsimp only at h
  rw [finiteWeilEdgeResidualProfile_at_index, finiteWeilEdgeResidualProfile_at_index] at h
  unfold finiteWeilCanonicalRawCorrectionValue
  nlinarith only [h]

theorem finiteWeilCanonicalRawDefect_monotone (r k : ℕ) :
    Monotone (fun i => finiteWeilCanonicalRawIndexValue r k i - finiteWeilCanonicalRawCorrectionValue r k i) := by
  have hm (i : Fin (r + 1)) : ((i : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) r := by
    constructor
    · positivity
    · exact_mod_cast (show (i : ℕ) ≤ r by have := i.isLt; omega)
  intro i j hij
  have h := finiteWeilEdgeResidualProfile_antitoneOn r k (hm i) (hm j)
    (show ((i : ℕ) : ℝ) ≤ (j : ℕ) by exact_mod_cast (show (i : ℕ) ≤ (j : ℕ) from hij))
  rw [finiteWeilEdgeResidualProfile_at_index, finiteWeilEdgeResidualProfile_at_index] at h
  unfold finiteWeilCanonicalRawIndexValue finiteWeilCanonicalRawCorrectionValue
  nlinarith only [h]

theorem finiteWeilCanonicalRawIndexValue_mean_zero (r k : ℕ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i * finiteWeilCanonicalRawIndexValue r k i) = 0 := by
  simp_rw [finiteWeilCanonicalRawIndexValue, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, finiteWeilCanonicalEdgeMass_sum, one_mul]
  change finiteWeilCanonicalEdgeIndexMean r k - finiteWeilCanonicalEdgeIndexMean r k = 0
  exact sub_self _

theorem finiteWeilCanonicalRawCorrectionValue_mean_zero (r k : ℕ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i * finiteWeilCanonicalRawCorrectionValue r k i) = 0 := by
  unfold finiteWeilCanonicalRawCorrectionValue
  calc
    _ = ((r + 1 : ℕ) : ℝ) * (∑ i, finiteWeilCanonicalEdgeMass r k i *
          finiteWeilCanonicalEdgeLogCorrection r k i) -
        (((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCorrection r k) *
          (∑ i, finiteWeilCanonicalEdgeMass r k i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      rw [finiteWeilCanonicalEdgeLogCorrection_mean, finiteWeilCanonicalEdgeMass_sum]
      ring

theorem finiteWeilCanonicalRawDefect_mean_zero (r k : ℕ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i *
      (finiteWeilCanonicalRawIndexValue r k i - finiteWeilCanonicalRawCorrectionValue r k i)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, finiteWeilCanonicalRawIndexValue_mean_zero,
    finiteWeilCanonicalRawCorrectionValue_mean_zero, sub_self]

end RHTower
