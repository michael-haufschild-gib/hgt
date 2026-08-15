import GaloisForLFunctions.RHTower.GaussCubicSharpRelativeBound

/-!
# Literal outer defect of the cubic propagated error

The propagated vector splits into a unitary rotation of the already-vanishing relative error and
one new outer moving-translation defect.  Parseval identifies the latter exactly with a weighted
lattice energy.  This is the unique remaining analytic target for the cubic CCM component.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology
open scoped ENNReal

noncomputable section

/-- Outer moving-translation defect applied to the prime-scale relative error. -/
def gaussCubicOuterDefectVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockOf hm k p i
      (gaussPrimeScaleBlock hp (gaussPrincipalRelativeErrorVector hm k p hp i)) -
    gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      (gaussPrimeScaleBlock hp (gaussPrincipalRelativeErrorVector hm k p hp i))

/-- Exact lattice energy of the cubic outer defect. -/
def gaussCubicOuterDefectEnergy {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal
    (‖fourierCoeff ((gaussPrimeScaleBlock hp
        (gaussPrincipalRelativeErrorVector hm k p hp i) : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
      ‖gaussSampleRatioDefect k p j i‖ ^ 2)

/-- The propagated vector is the outer defect plus a unitary rotation of the old relative error. -/
theorem gaussCubicPropagatedRelativeErrorVector_eq_outer_add_rotation
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    gaussCubicPropagatedRelativeErrorVector hm k p hp i =
      gaussCubicOuterDefectVector hm k p hp i +
        gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (gaussPrincipalRelativeErrorVector hm k p hp i)) := by
  rw [gaussCubicPropagatedRelativeErrorVector, gaussCubicOuterDefectVector]
  abel

/-- Pointwise reduction of propagated convergence to the outer defect. -/
theorem norm_gaussCubicPropagatedRelativeErrorVector_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ≤
      ‖gaussCubicOuterDefectVector hm k p hp i‖ +
        Real.sqrt (p : ℝ) * ‖gaussPrincipalRelativeErrorVector hm k p hp i‖ := by
  rw [gaussCubicPropagatedRelativeErrorVector_eq_outer_add_rotation hm k p hp i]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [gaussRotationBlock_eq_translation,
    (gaussTranslationBlock
      ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))).norm_map]
  exact (gaussPrimeScaleBlock hp).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_right (norm_gaussPrimeScaleBlock_le hp) (norm_nonneg _))

/-- Parseval equality: the exact outer-defect energy is the squared propagated outer norm. -/
theorem ofReal_norm_gaussCubicOuterDefectVector_sq_eq_energy
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ENNReal.ofReal (‖gaussCubicOuterDefectVector hm k p hp i‖ ^ (2 : ℝ)) =
      gaussCubicOuterDefectEnergy hm k p hp i := by
  set u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (gaussPrincipalRelativeErrorVector hm k p hp i) with hu
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussCubicOuterDefectVector hm k p hp i with hw
  have hcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ =
        ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ *
          ‖gaussSampleRatioDefect k p j i‖ := by
    intro j
    have hsub : fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j =
        fourierCoeff ((gaussShiftedBlockOf hm k p i u : AddCircle (1 : ℝ) → ℂ)) j -
          fourierCoeff ((gaussRotationBlock
            ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) u :
              AddCircle (1 : ℝ) → ℂ)) j := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hw,
        gaussCubicOuterDefectVector, ← hu, map_sub]
      rfl
    rw [hsub, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]
  have hcongr : ∀ j : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) =
        ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j i‖ ^ 2 := by
    intro j
    rw [hcoeff j, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      ← Real.rpow_natCast (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖) 2,
      ← Real.rpow_natCast (‖gaussSampleRatioDefect k p j i‖) 2]
    norm_num
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr w)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  have hsummable' : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j i‖ ^ 2 := hsummable.congr hcongr
  rw [gaussCubicOuterDefectEnergy, ← hu]
  change ENNReal.ofReal (‖w‖ ^ (2 : ℝ)) =
    ∑' j : ℤ, ENNReal.ofReal
      (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
        ‖gaussSampleRatioDefect k p j i‖ ^ 2)
  rw [norm_sq_eq_tsum_fourierCoeff w, tsum_congr hcongr,
    ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable']

end

end RHTower
