import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMobiusConstraint

/-!
# Completion-balanced Möbius pair current

The theta-tail core atoms are even in each source coordinate.  Combining this finite polynomial
symmetry with the completion-balanced Möbius reflection law identifies the reflected right-shift
pair kernel exactly with its left-shift counterpart.  No Mertens estimate or divisor information
enters this identity.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial ArithmeticFunction Nat
open scoped BigOperators

namespace RHTower

noncomputable section

theorem thetaCuspTailSecondSection_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSection d z (-x) =
      thetaCuspTailSecondSection d z x := by
  unfold thetaCuspTailSecondSection
  apply Finset.sum_congr rfl
  intro k _hk
  push_cast
  have hpow : (-((x : ℂ))) ^ (2 * k + 2) = (x : ℂ) ^ (2 * k + 2) := by
    rw [neg_pow, pow_add, pow_mul]
    norm_num
  rw [hpow]

theorem thetaCuspTailSecondSectionDerivative_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSectionDerivative d z (-x) =
      thetaCuspTailSecondSectionDerivative d z x := by
  unfold thetaCuspTailSecondSectionDerivative
  apply Finset.sum_congr rfl
  intro k _hk
  push_cast
  have hpow : (-((x : ℂ))) ^ (2 * k + 2) = (x : ℂ) ^ (2 * k + 2) := by
    rw [neg_pow, pow_add, pow_mul]
    norm_num
  rw [hpow]

theorem thetaCuspTailSecondCoreAtom_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondCoreAtom d z (-x) =
      thetaCuspTailSecondCoreAtom d z x := by
  unfold thetaCuspTailSecondCoreAtom
  rw [thetaCuspTailSecondSection_neg]

theorem thetaCuspTailSecondCoreAtomDerivative_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondCoreAtomDerivative d z (-x) =
      thetaCuspTailSecondCoreAtomDerivative d z x := by
  unfold thetaCuspTailSecondCoreAtomDerivative
  rw [thetaCuspTailSecondSection_neg,
    thetaCuspTailSecondSectionDerivative_neg]

theorem xiCTaylorThetaTailCorePairCurrent_neg_left
    (d : ℕ) (z : ℂ) (x y : ℝ) :
    xiCTaylorThetaTailCorePairCurrent d z (-x, y) =
      xiCTaylorThetaTailCorePairCurrent d z (x, y) := by
  unfold xiCTaylorThetaTailCorePairCurrent
  rw [thetaCuspTailSecondCoreAtom_neg,
    thetaCuspTailSecondCoreAtomDerivative_neg]

theorem xiCTaylorThetaTailCorePairCurrent_neg_right
    (d : ℕ) (z : ℂ) (x y : ℝ) :
    xiCTaylorThetaTailCorePairCurrent d z (x, -y) =
      xiCTaylorThetaTailCorePairCurrent d z (x, y) := by
  unfold xiCTaylorThetaTailCorePairCurrent
  rw [thetaCuspTailSecondCoreAtom_neg,
    thetaCuspTailSecondCoreAtomDerivative_neg]

theorem xiCTaylorThetaTailCorePairCurrent_neg_neg
    (d : ℕ) (z : ℂ) (x y : ℝ) :
    xiCTaylorThetaTailCorePairCurrent d z (-x, -y) =
      xiCTaylorThetaTailCorePairCurrent d z (x, y) := by
  rw [xiCTaylorThetaTailCorePairCurrent_neg_left,
    xiCTaylorThetaTailCorePairCurrent_neg_right]

/-- Pair kernel of the two completion-balanced right-shift packets. -/
def xiCTaylorThetaTailCoreBalancedMobiusRightPairKernel
    (N d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  thetaCuspTailSecondDensityBalancedMobiusTranslate N p.1 *
    thetaCuspTailSecondDensityBalancedMobiusTranslate N p.2 *
      xiCTaylorThetaTailCorePairCurrent d z p

/-- Pair kernel of the corresponding left-shift packets. -/
def xiCTaylorThetaTailCoreBalancedMobiusLeftPairKernel
    (N d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  thetaCuspTailSecondDensityBalancedMobiusLeftShift N p.1 *
    thetaCuspTailSecondDensityBalancedMobiusLeftShift N p.2 *
      xiCTaylorThetaTailCorePairCurrent d z p

/-- Exact two-variable reflected packet identity.  The right/right pair becomes the left/left pair
with no residual completion character. -/
theorem xiCTaylorThetaTailCoreBalancedMobiusRightPairKernel_neg_neg
    (N d : ℕ) (z : ℂ) (x y : ℝ) :
    xiCTaylorThetaTailCoreBalancedMobiusRightPairKernel N d z (-x, -y) =
      xiCTaylorThetaTailCoreBalancedMobiusLeftPairKernel N d z (x, y) := by
  unfold xiCTaylorThetaTailCoreBalancedMobiusRightPairKernel
    xiCTaylorThetaTailCoreBalancedMobiusLeftPairKernel
  rw [thetaCuspTailSecondDensityBalancedMobiusTranslate_neg,
    thetaCuspTailSecondDensityBalancedMobiusTranslate_neg,
    xiCTaylorThetaTailCorePairCurrent_neg_neg]

/-- The balanced left packet paired with the core value is exactly the negative-half contribution
of the balanced right packet.  This is a genuine half-line/full-line polarization identity: the
two completion characters have already been cancelled in the source before the change of
variables. -/
theorem integral_Ioi_balancedMobiusLeft_mul_coreAtom_eq_integral_Iic_right
    (N d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
      ∫ x : ℝ in Iic 0,
        (thetaCuspTailSecondDensityBalancedMobiusTranslate N x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x := by
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensityBalancedMobiusTranslate N x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
        ∫ x : ℝ in Ioi 0, f (-x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f]
          rw [thetaCuspTailSecondDensityBalancedMobiusTranslate_neg,
            thetaCuspTailSecondCoreAtom_neg]
    _ = ∫ x : ℝ in Iic 0, f x := by
      simpa only [neg_zero] using integral_comp_neg_Ioi 0 f
    _ = _ := rfl

/-- Derivative companion to
`integral_Ioi_balancedMobiusLeft_mul_coreAtom_eq_integral_Iic_right`.  The same
orientation is retained because the core derivative is even in the source coordinate. -/
theorem integral_Ioi_balancedMobiusLeft_mul_coreAtomDerivative_eq_integral_Iic_right
    (N d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x) =
      ∫ x : ℝ in Iic 0,
        (thetaCuspTailSecondDensityBalancedMobiusTranslate N x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x := by
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensityBalancedMobiusTranslate N x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x) =
        ∫ x : ℝ in Ioi 0, f (-x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f]
          rw [thetaCuspTailSecondDensityBalancedMobiusTranslate_neg,
            thetaCuspTailSecondCoreAtomDerivative_neg]
    _ = ∫ x : ℝ in Iic 0, f x := by
      simpa only [neg_zero] using integral_comp_neg_Ioi 0 f
    _ = _ := rfl

end

end RHTower
