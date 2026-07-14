import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProuhetSeamInvariant
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPacketRecombination

/-!
# Rank-two form of the reflected cofinal Haar residual

After the exact square-channel cancellation, the whole finite reflected Haar sum is not a large
collection of unrelated layers.  It is a symmetric rank-two tensor between the universal
completion character `exp (-x/2)` and one explicit remote-row residual.  This is the source-level
form of the sole off-diagonal Hermitian current that remains after cofinal polarization.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The one-variable residual left after the reflected top row, the original canonical density,
and the decaying completion character are kept in their exact coefficients. -/
def thetaSquareIndexDyadicHaarResidual (N : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ N * thetaSquareIndexDyadicDensity N
      (x - 2 * (N : ℝ) * Real.log 2) -
    thetaCuspTailSecondDensity x -
    (((2 : ℝ) ^ N - 1) / 4) * Real.exp (-x / 2)

/-- Exact rank-two factorization of the complete reflected Haar prefix. -/
theorem thetaSquareIndexDyadicHaarLayer_reflected_sum_eq_rankTwoResidual
    (N : ℕ) (x y : ℝ) :
    (∑ k ∈ Finset.range N,
      ((2 : ℝ) ^ (k + 1) *
          thetaSquareIndexDyadicOddLayer k
            (x - thetaSquareIndexDyadicReflectionShift k) *
          thetaSquareIndexDyadicOddLayer k
            (y - thetaSquareIndexDyadicReflectionShift k) -
        (2 : ℝ) ^ k *
          thetaSquareIndexDyadicParityLayer k (-x) *
            thetaSquareIndexDyadicParityLayer k (-y))) =
      (1 / 2 : ℝ) *
        (thetaSquareIndexDyadicHaarResidual N x * Real.exp (-y / 2) +
          Real.exp (-x / 2) * thetaSquareIndexDyadicHaarResidual N y) := by
  rw [thetaSquareIndexDyadicHaarLayer_reflected_sum_eq_topDifference]
  unfold thetaSquareIndexDyadicHaarResidual
  ring

/-- Reflection exposes why the residual cannot be estimated termwise: its reflected positive-cusp
form contains a growing completion character, although the rank-two combination above is finite. -/
theorem thetaSquareIndexDyadicHaarResidual_neg
    (N : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicHaarResidual N (-x) =
      (2 : ℝ) ^ N * thetaSquareIndexDyadicDensity N x -
        thetaCuspTailSecondDensity x +
        (((2 : ℝ) ^ N - 1) / 4) * Real.exp (x / 2) := by
  let a : ℝ := (N : ℝ) * Real.log 2
  unfold thetaSquareIndexDyadicHaarResidual
  rw [thetaSquareIndexDyadicDensity_eq_scaledDensity,
    thetaSquareIndexDyadicDensity_eq_scaledDensity]
  have harg :
      -x - 2 * (N : ℝ) * Real.log 2 + (N : ℝ) * Real.log 2 =
        -(x + a) := by
    dsimp only [a]
    ring
  rw [harg, thetaCuspTailSecondDensity_neg (x + a),
    thetaCuspTailSecondDensity_neg x]
  have hpow : (((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (-(N : ℝ) / 2) := by
    rw [show (((2 ^ N : ℕ) : ℝ)) = (2 : ℝ) ^ N by norm_num,
      Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ N),
      Real.log_pow,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlog : Real.exp ((N : ℝ) * Real.log 2) = (2 : ℝ) ^ N := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hposlog : Real.exp ((N : ℝ) * Real.log 2 / 2) =
      (2 : ℝ) ^ ((N : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hscale :
      (2 : ℝ) ^ N * (((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) =
        Real.exp (a / 2) := by
    rw [hpow, ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (N : ℝ) + -(N : ℝ) / 2 = (N : ℝ) / 2 by ring]
    dsimp only [a]
    exact hposlog.symm
  have hplus :
      Real.exp (a / 2) * Real.exp ((x + a) / 2) =
        (2 : ℝ) ^ N * Real.exp (x / 2) := by
    rw [← Real.exp_add, show a / 2 + (x + a) / 2 =
      x / 2 + (N : ℝ) * Real.log 2 by dsimp only [a]; ring,
      Real.exp_add, hlog]
    ring
  have hminus :
      Real.exp (a / 2) * Real.exp (-(x + a) / 2) =
        Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaCuspReflectionMode
  rw [← mul_assoc ((2 : ℝ) ^ N)
      ((((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))), hscale]
  have hdouble : Real.exp (- -x / 2) = Real.exp (x / 2) := by
    congr 1
    ring
  rw [hdouble]
  have hdensityScale :
      (2 : ℝ) ^ N *
          ((((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) *
            thetaCuspTailSecondDensity (x + (N : ℝ) * Real.log 2)) =
        Real.exp (a / 2) *
          thetaCuspTailSecondDensity (x + (N : ℝ) * Real.log 2) := by
    rw [← mul_assoc, hscale]
  rw [hdensityScale]
  dsimp only [a] at hplus hminus ⊢
  linear_combination (1 / 2 : ℝ) * hplus - (1 / 2 : ℝ) * hminus

/-! ## Even-remainder coboundary form -/

/-- The depth-`N` critical translate of the exactly even completed-density remainder. -/
def thetaSquareIndexDyadicEvenRemainderRow (N : ℕ) (x : ℝ) : ℝ :=
  (((2 ^ N : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
    thetaCuspTailSecondEvenRemainder
      (x + (N : ℝ) * Real.log 2)

/-- Reflecting the even-remainder row is exactly the remote translation occurring in the
cofinal Haar prefix. -/
theorem thetaSquareIndexDyadicEvenRemainderRow_neg
    (N : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicEvenRemainderRow N (-x) =
      thetaSquareIndexDyadicEvenRemainderRow N
        (x - 2 * (N : ℝ) * Real.log 2) := by
  unfold thetaSquareIndexDyadicEvenRemainderRow
  rw [show -x + (N : ℝ) * Real.log 2 =
      -(x - (N : ℝ) * Real.log 2) by ring,
    thetaCuspTailSecondEvenRemainder_neg]
  congr 2
  ring

/-- Exact completion-corrected form of the rank-two residual.  Its non-elementary part is a
single coboundary between two critical translates of the exactly even density remainder; the
elementary square changes to the favorable coefficient `((2^N-1)/4)`. -/
theorem thetaSquareIndexDyadicHaarResidual_eq_evenCoboundary
    (N : ℕ) (x : ℝ) :
    thetaSquareIndexDyadicHaarResidual N x =
      (2 : ℝ) ^ N * thetaSquareIndexDyadicEvenRemainderRow N (-x) -
        thetaSquareIndexDyadicEvenRemainderRow 0 x +
        (((2 : ℝ) ^ N - 1) / 4) * Real.exp (-x / 2) := by
  let a : ℝ := (N : ℝ) * Real.log 2
  have hpow : (((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (-(N : ℝ) / 2) := by
    rw [show (((2 ^ N : ℕ) : ℝ)) = (2 : ℝ) ^ N by norm_num,
      Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ N),
      Real.log_pow,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlog : Real.exp ((N : ℝ) * Real.log 2) = (2 : ℝ) ^ N := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hposlog : Real.exp ((N : ℝ) * Real.log 2 / 2) =
      (2 : ℝ) ^ ((N : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hscale :
      (2 : ℝ) ^ N * (((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) =
        Real.exp (a / 2) := by
    rw [hpow, ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (N : ℝ) + -(N : ℝ) / 2 = (N : ℝ) / 2 by ring]
    dsimp only [a]
    exact hposlog.symm
  have hcompletion :
      ((2 : ℝ) ^ N * (((2 ^ N : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(x - a) / 2) =
        (2 : ℝ) ^ N * Real.exp (-x / 2) := by
    rw [hscale, ← Real.exp_add,
      show a / 2 + -(x - a) / 2 = -x / 2 + a by ring,
      Real.exp_add, hlog]
    ring
  unfold thetaSquareIndexDyadicHaarResidual
    thetaSquareIndexDyadicEvenRemainderRow
  rw [thetaSquareIndexDyadicDensity_eq_scaledDensity]
  simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, Nat.cast_one]
  rw [show x - 2 * (N : ℝ) * Real.log 2 + (N : ℝ) * Real.log 2 =
      x - a by dsimp only [a]; ring,
    show -x + (N : ℝ) * Real.log 2 =
      -(x - a) by dsimp only [a]; ring,
    thetaCuspTailSecondEvenRemainder_neg]
  unfold thetaCuspTailSecondEvenRemainder
  norm_num
  rw [show (a - x) / 2 = -(x - a) / 2 by ring]
  norm_num at hcompletion
  rw [show (a - x) / 2 = -(x - a) / 2 by ring] at hcompletion
  linear_combination (1 / 2 : ℝ) * hcompletion

end

end RHTower
