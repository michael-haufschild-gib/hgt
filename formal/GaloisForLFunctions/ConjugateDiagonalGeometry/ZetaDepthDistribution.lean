import GaloisForLFunctions.ConjugateDiagonalGeometry.DefectKernel
import GaloisForLFunctions.ArithmeticPolarization.HeckeInvarianceOfTheCollidedPolarizationIsRH

/-!
# The depth distribution of the collided zeta form

For every compact `C²` test, the collided weights define a finite positive
depth distribution. Its symmetric Hecke defect controls every depth tail and
its quadratic moment. All kernel moments converge by the open critical strip;
no zero-density or positivity assumption is required.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open Zeta23 ArithmeticPolarization

/-- The natural domain on which the collided zeta trace is known to converge. -/
abbrev CompactTest := {f : ℝ → ℂ // ContDiff ℝ 2 f ∧ HasCompactSupport f}

/-- Signed displacement of a nontrivial zeta zero from the critical line. -/
def zetaDepth (ρ : zetaZeroConfig.carrier) : ℝ := (ρ : ℂ).re - 1 / 2

theorem abs_zetaDepth_le (ρ : zetaZeroConfig.carrier) : |zetaDepth ρ| ≤ 1 / 2 := by
  have h := zetaZeroConfig.strip ρ ρ.2
  rw [abs_le]
  dsimp [zetaDepth]
  constructor <;> linarith only [h.1, h.2]

/-- Multiplicity times squared transform amplitude on the conjugate diagonal. -/
def zetaWeight (f : CompactTest) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f.1 ρ)

theorem zetaWeight_nonneg (f : CompactTest) (ρ : zetaZeroConfig.carrier) :
    0 ≤ zetaWeight f ρ :=
  mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem summable_zetaWeight (f : CompactTest) : Summable (zetaWeight f) :=
  zeta_summable_collided f.2.1 f.2.2

/-- All moments of the fixed-scale depth kernel converge for the actual zeta divisor. -/
theorem summable_zeta_kernel_pow (f : CompactTest) (L : ℝ) (n : ℕ) :
    Summable fun ρ => zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ n := by
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (zetaWeight_nonneg f ρ) (pow_nonneg (depthKernel_nonneg _ _) _))
    (fun ρ => ?_) ((summable_zetaWeight f).mul_right (depthKernel L (1 / 2) ^ n))
  apply mul_le_mul_of_nonneg_left _ (zetaWeight_nonneg f ρ)
  apply pow_le_pow_left₀ (depthKernel_nonneg _ _)
  exact depthKernel_mono_depth L (by simpa using abs_zetaDepth_le ρ)

/-- The symmetric Hecke defect, written as a convergent positive depth trace. -/
def heckeDefect (f : CompactTest) (L : ℝ) : ℝ :=
  ∑' ρ, zetaWeight f ρ * depthKernel L (zetaDepth ρ)

theorem summable_heckeDefect (f : CompactTest) (L : ℝ) :
    Summable fun ρ => zetaWeight f ρ * depthKernel L (zetaDepth ρ) := by
  simpa only [pow_one] using summable_zeta_kernel_pow f L 1

theorem heckeDefect_nonneg (f : CompactTest) (L : ℝ) : 0 ≤ heckeDefect f L :=
  tsum_nonneg fun ρ => mul_nonneg (zetaWeight_nonneg f ρ) (depthKernel_nonneg _ _)

/-- The positive depth trace is exactly the second translation difference of `D`. -/
theorem heckeDefect_eq_second_difference (f : CompactTest) (L : ℝ) :
    heckeDefect f L =
      collidedForm zetaZeroConfig (ArithmeticPolarization.translate L f.1) +
        collidedForm zetaZeroConfig (ArithmeticPolarization.translate (-L) f.1) -
          2 * collidedForm zetaZeroConfig f.1 := by
  have htrans (t : ℝ) :
      ContDiff ℝ 2 (ArithmeticPolarization.translate t f.1) ∧
        HasCompactSupport (ArithmeticPolarization.translate t f.1) :=
    ⟨f.2.1.comp (contDiff_id.sub contDiff_const),
      f.2.2.comp_homeomorph (Homeomorph.subRight t)⟩
  rw [collidedForm_second_difference L (summable_zetaWeight f)
    (zeta_summable_collided (htrans L).1 (htrans L).2)
    (zeta_summable_collided (htrans (-L)).1 (htrans (-L)).2)]
  apply tsum_congr
  intro ρ
  dsimp [zetaWeight, zetaDepth, depthKernel]
  ring

/-- A strip bound controls the defect at every fixed translation scale. -/
theorem heckeDefect_le_strip (f : CompactTest) (L : ℝ) :
    heckeDefect f L ≤ depthKernel L (1 / 2) * collidedForm zetaZeroConfig f.1 := by
  rw [collidedForm, ← tsum_mul_left]
  apply (summable_heckeDefect f L).tsum_le_tsum _
    ((summable_zetaWeight f).mul_left (depthKernel L (1 / 2)))
  intro ρ
  change zetaWeight f ρ * depthKernel L (zetaDepth ρ) ≤
    depthKernel L (1 / 2) * zetaWeight f ρ
  rw [mul_comm (depthKernel L (1 / 2))]
  exact mul_le_mul_of_nonneg_left
    (depthKernel_mono_depth L (by simpa using abs_zetaDepth_le ρ)) (zetaWeight_nonneg f ρ)

/-- Collided mass at absolute depth at least `|b|`. -/
def depthTail (f : CompactTest) (b : ℝ) : ℝ :=
  ∑' ρ, if |b| ≤ |zetaDepth ρ| then zetaWeight f ρ else 0

theorem summable_depthTail (f : CompactTest) (b : ℝ) :
    Summable fun ρ => if |b| ≤ |zetaDepth ρ| then zetaWeight f ρ else 0 := by
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) (summable_zetaWeight f)
  · split_ifs
    · exact zetaWeight_nonneg f ρ
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact zetaWeight_nonneg f ρ

/-- The exact hyperbolic threshold converts a defect bound into a weighted density bound. -/
theorem depthKernel_mul_tail_le (f : CompactTest) (L b : ℝ) :
    depthKernel L b * depthTail f b ≤ heckeDefect f L := by
  rw [depthTail, ← tsum_mul_left]
  apply ((summable_depthTail f b).mul_left (depthKernel L b)).tsum_le_tsum _
    (summable_heckeDefect f L)
  intro ρ
  by_cases h : |b| ≤ |zetaDepth ρ|
  · rw [if_pos h, mul_comm (depthKernel L b)]
    exact mul_le_mul_of_nonneg_left (depthKernel_mono_depth L h) (zetaWeight_nonneg f ρ)
  · rw [if_neg h, mul_zero]
    exact mul_nonneg (zetaWeight_nonneg f ρ) (depthKernel_nonneg _ _)

/-- The quadratic depth moment of the collided trace. -/
def depthSecondMoment (f : CompactTest) : ℝ :=
  ∑' ρ, zetaWeight f ρ * zetaDepth ρ ^ 2

theorem summable_depthSecondMoment (f : CompactTest) :
    Summable fun ρ => zetaWeight f ρ * zetaDepth ρ ^ 2 := by
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (zetaWeight_nonneg f ρ) (sq_nonneg _))
    (fun ρ => ?_) ((summable_zetaWeight f).mul_right (1 / 4))
  apply mul_le_mul_of_nonneg_left _ (zetaWeight_nonneg f ρ)
  have h := abs_le.mp (abs_zetaDepth_le ρ)
  nlinarith only [mul_nonneg (sub_nonneg.mpr h.2) (sub_nonneg.mpr h.1)]

/-- The defect controls the quadratic depth moment with its exact infinitesimal coefficient. -/
theorem four_mul_secondMoment_le (f : CompactTest) (L : ℝ) :
    4 * L ^ 2 * depthSecondMoment f ≤ heckeDefect f L := by
  rw [depthSecondMoment, ← tsum_mul_left]
  apply ((summable_depthSecondMoment f).mul_left (4 * L ^ 2)).tsum_le_tsum _
    (summable_heckeDefect f L)
  intro ρ
  calc 4 * L ^ 2 * (zetaWeight f ρ * zetaDepth ρ ^ 2)
      = zetaWeight f ρ * (4 * L ^ 2 * zetaDepth ρ ^ 2) := by ring
    _ ≤ zetaWeight f ρ * depthKernel L (zetaDepth ρ) :=
      mul_le_mul_of_nonneg_left (quadratic_le_depthKernel _ _) (zetaWeight_nonneg f ρ)

/-- The doubled-scale excess is the second moment of the depth kernel. -/
theorem heckeDefect_double (f : CompactTest) (L : ℝ) :
    heckeDefect f (2 * L) = 4 * heckeDefect f L +
      ∑' ρ, zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ 2 := by
  unfold heckeDefect
  rw [← tsum_mul_left, ← ((summable_heckeDefect f L).mul_left 4).tsum_add
    (summable_zeta_kernel_pow f L 2)]
  apply tsum_congr
  intro ρ
  rw [depthKernel_double]
  ring

end GaloisForLFunctions.ConjugateDiagonalGeometry
