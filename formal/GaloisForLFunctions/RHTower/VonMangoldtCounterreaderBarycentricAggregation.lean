import GaloisForLFunctions.RHTower.VonMangoldtWeightedMarginalBoundaryAnomaly

/-!
# Von Mangoldt counterreader barycentric aggregation

The first nonconstant coefficient of the canonical symmetric Toeplitz counterreader is a moment
ratio.  Under source addition it is therefore a third-moment-weighted barycentre of the isolated
source coefficients, not their sum.  In particular, multiplying two isolated edge symbols cannot
produce the counterreader of their accumulated source: the first coefficient already differs.
-/

open scoped BigOperators

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- First nonconstant coefficient in the two-sided symbol normalization of the canonical
Hankel--Toeplitz counterreader. -/
def counterreaderFirstSymbolCoefficient (moment : ℕ → ℝ) : ℝ :=
  2 * HTGeometry.hankelToeplitzCounterweight moment 1

theorem counterreaderFirstSymbolCoefficient_eq
    (moment : ℕ → ℝ) (h3 : moment 3 ≠ 0) :
    counterreaderFirstSymbolCoefficient moment = -moment 4 / moment 3 := by
  rw [counterreaderFirstSymbolCoefficient,
    HTGeometry.hankelToeplitzCounterweight_succ]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
  field_simp
  ring

/-- Accumulated moment sequence of a finite marked edge packet. -/
def finiteEdgeAccumulatedMoment
    {E : Type*} (edges : Finset E) (moment : E → ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ e ∈ edges, moment e q

/-- **Barycentric source aggregation law.**  The first counterreader coefficient of a finite
source sum is the third-moment-weighted barycentre of the isolated coefficients. -/
theorem counterreaderFirstSymbolCoefficient_finiteEdgeAccumulatedMoment
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (moment : E → ℕ → ℝ)
    (hedge3 : ∀ e ∈ edges, moment e 3 ≠ 0)
    (htotal3 : finiteEdgeAccumulatedMoment edges moment 3 ≠ 0) :
    counterreaderFirstSymbolCoefficient
        (finiteEdgeAccumulatedMoment edges moment) =
      ∑ e ∈ edges,
        (moment e 3 / finiteEdgeAccumulatedMoment edges moment 3) *
          counterreaderFirstSymbolCoefficient (moment e) := by
  rw [counterreaderFirstSymbolCoefficient_eq _ htotal3]
  have hterm : ∀ e ∈ edges,
      (moment e 3 / finiteEdgeAccumulatedMoment edges moment 3) *
          counterreaderFirstSymbolCoefficient (moment e) =
        -moment e 4 / finiteEdgeAccumulatedMoment edges moment 3 := by
    intro e he
    rw [counterreaderFirstSymbolCoefficient_eq _ (hedge3 e he)]
    field_simp
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div]
  simp [finiteEdgeAccumulatedMoment]

/-- For two strictly positive edge packets, the accumulated first coefficient is not the first
coefficient of their symbol product. -/
theorem twoEdgeCounterreaderFirstCoefficient_ne_product
    (moment₁ moment₂ : ℕ → ℝ)
    (h13 : 0 < moment₁ 3) (h14 : 0 < moment₁ 4)
    (h23 : 0 < moment₂ 3) (h24 : 0 < moment₂ 4) :
    counterreaderFirstSymbolCoefficient (fun q => moment₁ q + moment₂ q) ≠
      counterreaderFirstSymbolCoefficient moment₁ +
        counterreaderFirstSymbolCoefficient moment₂ := by
  rw [counterreaderFirstSymbolCoefficient_eq _ (ne_of_gt (add_pos h13 h23)),
    counterreaderFirstSymbolCoefficient_eq _ (ne_of_gt h13),
    counterreaderFirstSymbolCoefficient_eq _ (ne_of_gt h23)]
  simp only
  intro h
  have hcross : 0 < moment₁ 4 * moment₂ 3 ^ 2 + moment₂ 4 * moment₁ 3 ^ 2 :=
    add_pos (mul_pos h14 (sq_pos_of_pos h23)) (mul_pos h24 (sq_pos_of_pos h13))
  field_simp at h
  nlinarith

theorem finiteVonMangoldtRealWeight_three_pos :
    0 < finiteVonMangoldtRealWeight 3 := by
  rw [finiteVonMangoldtRealWeight,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)]
  positivity

theorem vonMangoldtAdditiveLogJetDifference_three_pos
    (q : ℕ) (hq : 0 < q) :
    0 < vonMangoldtAdditiveLogJetDifference q 3 := by
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  apply sub_pos.mpr
  exact pow_lt_pow_left₀
    (Real.strictMonoOn_log
      (by norm_num : (3 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (4 : ℝ) ∈ Set.Ioi 0)
      (by norm_num))
    (Real.log_pos (by norm_num)).le
    hq.ne'

theorem vonMangoldtSuccessorRelativeMomentTerm_three_pos
    (q : ℕ) (hq : 0 < q) :
    0 < vonMangoldtSuccessorRelativeMomentTerm q 3 := by
  exact mul_pos finiteVonMangoldtRealWeight_three_pos
    (vonMangoldtAdditiveLogJetDifference_three_pos q hq)

theorem finiteVonMangoldtSuccessorRelativeMoment_two_eq_edges
    (q : ℕ) :
    finiteVonMangoldtSuccessorRelativeMoment 2 q =
      vonMangoldtSuccessorRelativeMomentTerm q 2 +
        vonMangoldtSuccessorRelativeMomentTerm q 3 := by
  simp [finiteVonMangoldtSuccessorRelativeMoment, Fin.sum_univ_two]

/-- **Literal source multiplicative anomaly.**  The counterreader of the first two actual von
Mangoldt successor edges is not the product of their isolated counterreader symbols. -/
theorem vonMangoldt_twoEdgeCounterreaderFirstCoefficient_ne_product :
    counterreaderFirstSymbolCoefficient
        (finiteVonMangoldtSuccessorRelativeMoment 2) ≠
      counterreaderFirstSymbolCoefficient
          (fun q => vonMangoldtSuccessorRelativeMomentTerm q 2) +
        counterreaderFirstSymbolCoefficient
          (fun q => vonMangoldtSuccessorRelativeMomentTerm q 3) := by
  have h := twoEdgeCounterreaderFirstCoefficient_ne_product
    (fun q => vonMangoldtSuccessorRelativeMomentTerm q 2)
    (fun q => vonMangoldtSuccessorRelativeMomentTerm q 3)
    (vonMangoldtSuccessorRelativeMomentTerm_two_pos 3 (by omega))
    (vonMangoldtSuccessorRelativeMomentTerm_two_pos 4 (by omega))
    (vonMangoldtSuccessorRelativeMomentTerm_three_pos 3 (by omega))
    (vonMangoldtSuccessorRelativeMomentTerm_three_pos 4 (by omega))
  simpa only [finiteVonMangoldtSuccessorRelativeMoment_two_eq_edges] using h

end

end RHTower
