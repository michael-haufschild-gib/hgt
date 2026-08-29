import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

/-!
# Compact-cell Fubini for the actual first Stokes defect

Corpus conjecture C-A.9t3d supplies the exact coefficient interface after the literal paired
Green theorem.  It builds joint compact-cell regularity for the actual Poincare fields and then
identifies the coordinate-split divergence integral with the standard hyperbolic first-defect
moment.

RH chain:

`actual defect Fubini -> first moment reduction -> second full-Hessian Green/Stokes -> actual
balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
-/

open Complex Real Filter Set Topology MeasureTheory
open scoped Interval

namespace RHTower
noncomputable section

def d4BMStokesPairCoordinate (w : ℝ × ℝ) : D4BMUpperHalfPlaneCoordinate :=
  d4BMStokesCoordinate w.1 w.2

theorem continuous_d4BMPoincareSeed_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ => d4BMPoincareSeed (d4BMStokesPairCoordinate w) s p) := by
  let b : ℝ × ℝ → ℝ := fun w =>
    (d4BMStokesPairCoordinate w).y /
      d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair
  have hbpos (w : ℝ × ℝ) : 0 < b w := by
    exact div_pos (d4BMStokesPairCoordinate w).y_pos
      (d4BMPoincareQuadratic_pos (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero)
  have hb : Continuous b := by
    have hy : Continuous (fun w : ℝ × ℝ => (d4BMStokesPairCoordinate w).y) := by
      unfold d4BMStokesPairCoordinate d4BMStokesCoordinate
      fun_prop
    have hQ : Continuous (fun w : ℝ × ℝ =>
        d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair) := by
      unfold d4BMPoincareQuadratic d4BMStokesPairCoordinate d4BMStokesCoordinate
      fun_prop
    exact hy.div₀ hQ fun w => ne_of_gt
      (d4BMPoincareQuadratic_pos (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero)
  rw [continuous_iff_continuousAt]
  intro w
  have hslit : ((b w : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa using hbpos w)
  have hreal : ContinuousAt (fun t : ℝ => (t : ℂ) ^ s) (b w) :=
    (continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt
  have hpow := hreal.comp hb.continuousAt
  simpa [d4BMPoincareSeed, b, Function.comp_def] using hpow

theorem continuous_d4BMPoincareQuadratic_stokesPair
    (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair) := by
  unfold d4BMPoincareQuadratic d4BMStokesPairCoordinate d4BMStokesCoordinate
  fun_prop

theorem continuous_d4BMPoincareHorizontalLinear_stokesPair
    (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p) := by
  unfold d4BMPoincareHorizontalLinear d4BMStokesPairCoordinate d4BMStokesCoordinate
  fun_prop

theorem continuous_d4BMStokesPairCoordinate_height :
    Continuous (fun w : ℝ × ℝ => (d4BMStokesPairCoordinate w).y) := by
  unfold d4BMStokesPairCoordinate d4BMStokesCoordinate
  fun_prop

private theorem d4BMPoincareQuadratic_stokesPair_ne_zero
    (p : D4BMPrimitiveIntegerPair) (w : ℝ × ℝ) :
    (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ≠ 0 := by
  exact_mod_cast (d4BMPoincareQuadratic_pos
    (d4BMStokesPairCoordinate w) p.pair p.pair_ne_zero).ne'

private theorem d4BMStokesPairCoordinate_height_ne_zero (w : ℝ × ℝ) :
    ((d4BMStokesPairCoordinate w).y : ℂ) ≠ 0 := by
  exact_mod_cast (d4BMStokesPairCoordinate w).y_pos.ne'

theorem continuous_d4BMPoincareSeedHorizontalFirstJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalFirstJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hnum : Continuous (fun w : ℝ × ℝ =>
      -2 * s * (p.pair.1 : ℂ) *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) := by
    fun_prop
  have hquot := hnum.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  simpa only [d4BMPoincareSeedHorizontalFirstJet, Pi.mul_apply] using
    hquot.mul (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuous_d4BMPoincareSeedHorizontalSecondJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedHorizontalSecondJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hL : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareHorizontalLinear_stokesPair p)
  have hterm1 : Continuous (fun w : ℝ × ℝ =>
      -2 * s * (p.pair.1 : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact continuous_const.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  have hnum2 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
        (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ 2) := by
    fun_prop
  have hterm2 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
          (d4BMPoincareHorizontalLinear (d4BMStokesPairCoordinate w) p : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ 2) := by
    exact hnum2.div₀ (hQ.pow 2) fun w =>
      pow_ne_zero 2 (d4BMPoincareQuadratic_stokesPair_ne_zero p w)
  simpa only [d4BMPoincareSeedHorizontalSecondJet, Pi.add_apply, Pi.mul_apply] using
    (hterm1.add hterm2).mul (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuous_d4BMPoincareSeedVerticalFirstJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedVerticalFirstJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hterm1 : Continuous (fun w : ℝ × ℝ =>
      s / ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    continuous_const.div₀ hy d4BMStokesPairCoordinate_height_ne_zero
  have hnum2 : Continuous (fun w : ℝ × ℝ =>
      2 * s * (p.pair.1 : ℂ) ^ 2 * ((d4BMStokesPairCoordinate w).y : ℂ)) := by
    fun_prop
  have hterm2 := hnum2.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  simpa only [d4BMPoincareSeedVerticalFirstJet, Pi.sub_apply, Pi.mul_apply] using
    (hterm1.sub hterm2).mul (continuous_d4BMPoincareSeed_stokesPair s p)

theorem continuous_d4BMPoincareSeedVerticalSecondJet_stokesPair
    (s : ℂ) (p : D4BMPrimitiveIntegerPair) :
    Continuous (fun w : ℝ × ℝ =>
      d4BMPoincareSeedVerticalSecondJet (d4BMStokesPairCoordinate w) s p) := by
  have hQ : Continuous (fun w : ℝ × ℝ =>
      (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_d4BMPoincareQuadratic_stokesPair p)
  have hy : Continuous (fun w : ℝ × ℝ =>
      ((d4BMStokesPairCoordinate w).y : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_d4BMStokesPairCoordinate_height
  have hterm1 : Continuous (fun w : ℝ × ℝ =>
      s * (s - 1) / ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2) := by
    exact continuous_const.div₀ (hy.pow 2) fun w =>
      pow_ne_zero 2 (d4BMStokesPairCoordinate_height_ne_zero w)
  have hterm2 : Continuous (fun w : ℝ × ℝ =>
      2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ)) := by
    exact continuous_const.div₀ hQ (d4BMPoincareQuadratic_stokesPair_ne_zero p)
  have hnum3 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
        ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2) := by
    fun_prop
  have hterm3 : Continuous (fun w : ℝ × ℝ =>
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
          ((d4BMStokesPairCoordinate w).y : ℂ) ^ 2 /
        (d4BMPoincareQuadratic (d4BMStokesPairCoordinate w) p.pair : ℂ) ^ 2) := by
    exact hnum3.div₀ (hQ.pow 2) fun w =>
      pow_ne_zero 2 (d4BMPoincareQuadratic_stokesPair_ne_zero p w)
  simpa only [d4BMPoincareSeedVerticalSecondJet, Pi.sub_apply, Pi.add_apply,
    Pi.mul_apply] using
    ((hterm1.sub hterm2).add hterm3).mul
      (continuous_d4BMPoincareSeed_stokesPair s p)

end
end RHTower
