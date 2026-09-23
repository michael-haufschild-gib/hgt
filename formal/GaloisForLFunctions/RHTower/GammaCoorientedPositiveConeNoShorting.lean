import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity

/-!
# Gamma-cooriented positive-cone no-shorting

The promoted prime-power/Gamma reflection exterior changes sign when its two
cells are swapped.  Multiplication by the simultaneously reversed physical
half-height difference removes this coordinate orientation without erasing
the horizontal displacement.

The resulting cooriented exterior is the displacement parameter times a
strictly positive source gauge on every distinct cell pair.  Hence no
nonzero finite combination with nonnegative source weights can annihilate
an off-critical displacement.  Any Route-R source null-homotopy must use a
genuinely signed cross-pair incidence before completion.

No Xi divisor, zero-location statement, target positivity assumption, or
Riemann-hypothesis premise occurs.
-/

open Complex Function Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open PrimitivePromotedCellHodgeRigidity

/-- The actual reflection-odd Gamma exterior cooriented by its own source
half-height difference.  Both factors reverse under a cell swap, so their
product is symmetric. -/
def xiGammaEulerPrimitiveCoorientedReflectionOddExterior
    (a : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  (xiGammaEulerBoundaryHalfHeight j.1 j.2 -
      xiGammaEulerBoundaryHalfHeight i.1 i.2) *
    xiGammaEulerPrimitiveReflectionOddExterior a i j

/-- Removable cooriented Gamma/Green gauge.  At the critical section the
value is the exact derivative; away from it the quotient is division-free
after multiplication by the displacement. -/
def xiGammaEulerPrimitiveCoorientedReflectionGauge
    (a : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  let b := xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
    xiGammaEulerPrimitiveBoundaryAmplitude 0 j
  let d := xiGammaEulerBoundaryHalfHeight i.1 i.2 -
    xiGammaEulerBoundaryHalfHeight j.1 j.2
  let r := xiGammaEulerPrimitiveModularRate i +
    xiGammaEulerPrimitiveModularRate j
  if a = 0 then
    (-(b * d ^ (2 : ℕ))) * r
  else
    (-(b * d ^ (2 : ℕ))) * (Real.sinh (a * r) / a)

/-- Exact hyperbolic form of the actual reflection-odd promoted Gamma
exterior on an arbitrary pair of prime-power cells. -/
theorem xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveReflectionOddExterior a i j =
      xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2) *
            Real.sinh (a * (xiGammaEulerPrimitiveModularRate i +
              xiGammaEulerPrimitiveModularRate j)) := by
  rw [xiGammaEulerPrimitiveReflectionOddExterior,
    xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq]
  rw [Real.sinh_eq]
  ring

/-- **Division-free cooriented Gamma/Green factorization.**  Every actual
cell-pair exterior is horizontal displacement times its source gauge. -/
theorem xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j =
      a * xiGammaEulerPrimitiveCoorientedReflectionGauge a i j := by
  rw [xiGammaEulerPrimitiveCoorientedReflectionOddExterior,
    xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh]
  by_cases ha : a = 0
  · simp [ha]
  · rw [xiGammaEulerPrimitiveCoorientedReflectionGauge, if_neg ha]
    field_simp
    ring

/-- The cooriented Gamma/Green comparison gauge is strictly positive on
every pair with distinct physical half-heights, including at the removable
critical section. -/
theorem xiGammaEulerPrimitiveCoorientedReflectionGauge_pos
    (a : ℝ) (i j : Nat.Primes × ℕ)
    (hheight : xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
      xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    0 < xiGammaEulerPrimitiveCoorientedReflectionGauge a i j := by
  have hbi := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 i
  have hbj := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 j
  have hd : 0 < (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
      xiGammaEulerBoundaryHalfHeight j.1 j.2) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hheight)
  have hi := xiGammaEulerBoundaryHalfHeight_pos i
  have hj := xiGammaEulerBoundaryHalfHeight_pos j
  have hr : xiGammaEulerPrimitiveModularRate i +
      xiGammaEulerPrimitiveModularRate j < 0 := by
    rw [xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
      xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
    linarith
  have hleft :
      -(xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
          (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
            xiGammaEulerBoundaryHalfHeight j.1 j.2) ^ (2 : ℕ)) < 0 := by
    exact neg_lt_zero.mpr (mul_pos (mul_pos hbi hbj) hd)
  by_cases ha : a = 0
  · rw [xiGammaEulerPrimitiveCoorientedReflectionGauge, if_pos ha]
    exact mul_pos_of_neg_of_neg hleft hr
  · rw [xiGammaEulerPrimitiveCoorientedReflectionGauge, if_neg ha]
    have hquot :
        Real.sinh (a * (xiGammaEulerPrimitiveModularRate i +
          xiGammaEulerPrimitiveModularRate j)) / a < 0 := by
      by_cases hapos : 0 < a
      · exact div_neg_of_neg_of_pos
          (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hapos hr)) hapos
      · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
        exact div_neg_of_pos_of_neg
          (Real.sinh_pos_iff.mpr (mul_pos_of_neg_of_neg haneg hr)) haneg
    exact mul_pos_of_neg_of_neg hleft hquot

/-- Distinct labelled prime-power cells have a strictly positive cooriented
comparison gauge. -/
theorem xiGammaEulerPrimitiveCoorientedReflectionGauge_pair_pos
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    0 < xiGammaEulerPrimitiveCoorientedReflectionGauge
      a ij.1.1 ij.1.2 := by
  apply xiGammaEulerPrimitiveCoorientedReflectionGauge_pos
  intro h
  exact ij.2 (xiGammaEulerBoundaryHalfHeight_cell_injective h)

/-- **Positive-cone no-shorting theorem.**  A nonzero finite packet of
cooriented actual Gamma boundary cells with nonnegative source weights has
strictly the sign of the horizontal displacement.  It cannot furnish the
Route-R source null-homotopy away from the critical section. -/
theorem xiGammaEulerPrimitiveCoorientedPositiveCone_noShorting
    (a : ℝ) (ha : a ≠ 0)
    (S : Finset XiGammaEulerCalderonWittOrderedDistinctCellPair)
    (w : XiGammaEulerCalderonWittOrderedDistinctCellPair → ℝ)
    (hw : ∀ ij ∈ S, 0 ≤ w ij)
    (hwpos : ∃ ij ∈ S, 0 < w ij) :
    0 < a * ∑ ij ∈ S, w ij *
      xiGammaEulerPrimitiveCoorientedReflectionOddExterior
        a ij.1.1 ij.1.2 := by
  have hsum : 0 < ∑ ij ∈ S, w ij *
      xiGammaEulerPrimitiveCoorientedReflectionGauge a ij.1.1 ij.1.2 := by
    apply Finset.sum_pos'
    · intro ij hij
      exact mul_nonneg (hw ij hij)
        (le_of_lt
          (xiGammaEulerPrimitiveCoorientedReflectionGauge_pair_pos a ij))
    · obtain ⟨ij, hij, hwij⟩ := hwpos
      exact ⟨ij, hij,
        mul_pos hwij
          (xiGammaEulerPrimitiveCoorientedReflectionGauge_pair_pos a ij)⟩
  calc
    a * ∑ ij ∈ S, w ij *
        xiGammaEulerPrimitiveCoorientedReflectionOddExterior
          a ij.1.1 ij.1.2 =
      a ^ (2 : ℕ) * ∑ ij ∈ S, w ij *
        xiGammaEulerPrimitiveCoorientedReflectionGauge
          a ij.1.1 ij.1.2 := by
          simp_rw [
            xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ij hij
          ring
    _ > 0 := mul_pos (sq_pos_of_ne_zero ha) hsum

/-- **Countable positive-cone no-shorting theorem.**  The same obstruction
persists after an all-pair summable completion: any nonzero nonnegative
source weight has strictly nonzero cooriented Gamma total at every nonzero
horizontal displacement. -/
theorem xiGammaEulerPrimitiveCoorientedPositiveCone_tsum_noShorting
    (a : ℝ) (ha : a ≠ 0)
    (w : XiGammaEulerCalderonWittOrderedDistinctCellPair → ℝ)
    (hw : ∀ ij, 0 ≤ w ij)
    (hwpos : ∃ ij, 0 < w ij)
    (hsummable : Summable (fun ij => w ij *
      xiGammaEulerPrimitiveCoorientedReflectionGauge
        a ij.1.1 ij.1.2)) :
    0 < a * ∑' ij, w ij *
      xiGammaEulerPrimitiveCoorientedReflectionOddExterior
        a ij.1.1 ij.1.2 := by
  obtain ⟨ij, hwij⟩ := hwpos
  have htsum : 0 < ∑' ij, w ij *
      xiGammaEulerPrimitiveCoorientedReflectionGauge
        a ij.1.1 ij.1.2 := by
    exact hsummable.tsum_pos
      (fun kl => mul_nonneg (hw kl)
        (le_of_lt
          (xiGammaEulerPrimitiveCoorientedReflectionGauge_pair_pos a kl)))
      ij
      (mul_pos hwij
        (xiGammaEulerPrimitiveCoorientedReflectionGauge_pair_pos a ij))
  calc
    a * ∑' ij, w ij *
        xiGammaEulerPrimitiveCoorientedReflectionOddExterior
          a ij.1.1 ij.1.2 =
      a ^ (2 : ℕ) * ∑' ij, w ij *
        xiGammaEulerPrimitiveCoorientedReflectionGauge
          a ij.1.1 ij.1.2 := by
          simp_rw [
            xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge,
            mul_left_comm (w _) a]
          rw [tsum_mul_left]
          ring
    _ > 0 := mul_pos (sq_pos_of_ne_zero ha) htsum

end

end RHTower
