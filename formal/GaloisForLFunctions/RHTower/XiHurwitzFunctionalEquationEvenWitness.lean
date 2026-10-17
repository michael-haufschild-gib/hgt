import GaloisForLFunctions.RHTower.XiWeilFunctionalEquationParity
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate

/-!
# A canonical FE-even Hurwitz witness with unchanged negative Weil energy

The original Hurwitz orientation vector is odd under pure functional-equation
reflection. Every even vector is orthogonal to it, giving a sharp approximation
obstruction. The Deninger orientation isometry moves the complete witness into
the even sector while preserving its norm and its negative Weil square exactly.
-/

open Complex

namespace RHTower

noncomputable section

/-- Pure functional-equation reflection reverses the signed Hurwitz coordinate. -/
theorem xiHurwitzOrientationCoordinate_reflect (q : XiZeroCopy) :
    xiHurwitzOrientationCoordinate (xiZeroCopyReflectEquiv q) =
      -xiHurwitzOrientationCoordinate q := by
  have hcenter : ‖((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2‖ =
      ‖(q.1 : ℂ) - 1 / 2‖ := by
    rw [← norm_xiSpectralPoint, xiSpectralPoint_reflect, norm_neg, norm_xiSpectralPoint]
  simp only [xiHurwitzOrientationCoordinate_eq_fiberCoefficient,
    xiHurwitzOrientationFiberCoefficient_eq_neg_sin_div]
  have hval : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
  rw [hcenter, hval]
  simp only [Complex.sub_re, Complex.one_re]
  rw [show 2 * Real.pi * (1 - (q.1 : ℂ).re) =
    2 * Real.pi - 2 * Real.pi * (q.1 : ℂ).re by ring, Real.sin_two_pi_sub]
  push_cast
  ring

theorem xiHurwitzOrientationVector_FE_odd :
    XiFunctionalEquationParity (-1) xiHurwitzOrientationVector := by
  intro q
  simp only [xiHurwitzOrientationVector_apply, xiHurwitzOrientationCoordinate_reflect,
    neg_one_mul]

/-- The canonical Hurwitz obstruction transported into the pure FE-even sector. -/
def xiHurwitzEvenOrientationVector : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiFEOrientationLp xiHurwitzOrientationVector

theorem xiHurwitzEvenOrientationVector_FE_even :
    XiFunctionalEquationParity 1 xiHurwitzEvenOrientationVector := by
  simpa only [neg_neg, xiHurwitzEvenOrientationVector] using
    xiFEOrientationLp_parity xiHurwitzOrientationVector_FE_odd

theorem norm_sq_xiHurwitzEvenOrientationVector :
    ‖xiHurwitzEvenOrientationVector‖ ^ (2 : ℕ) = xiHurwitzOrientationEnergy := by
  rw [xiHurwitzEvenOrientationVector, norm_xiFEOrientationLp,
    norm_sq_xiHurwitzOrientationVector]

/-- The even witness retains exactly the complete negative Hurwitz energy. -/
theorem xiWeilHilbertQuadratic_xiHurwitzEvenOrientationVector :
    xiWeilHilbertQuadratic xiHurwitzEvenOrientationVector = -xiHurwitzOrientationEnergy := by
  rw [xiHurwitzEvenOrientationVector, xiWeilHilbertQuadratic_xiFEOrientationLp,
    xiWeilHilbertQuadratic_xiHurwitzOrientationVector]

theorem riemannHypothesis_iff_xiHurwitzEvenOrientationVector_weil_nonneg :
    RiemannHypothesis ↔ 0 ≤ xiWeilHilbertQuadratic xiHurwitzEvenOrientationVector := by
  rw [xiHurwitzEvenOrientationVector, xiWeilHilbertQuadratic_xiFEOrientationLp]
  exact riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg

/-- Full FE-even Hilbert positivity still contains the complete RH obstruction. -/
theorem riemannHypothesis_iff_FE_even_weil_nonnegative :
    RiemannHypothesis ↔
      ∀ v, XiFunctionalEquationParity 1 v → 0 ≤ xiWeilHilbertQuadratic v := by
  constructor
  · intro h v _
    exact xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis h v
  · intro h
    exact riemannHypothesis_iff_xiHurwitzEvenOrientationVector_weil_nonneg.mpr
      (h _ xiHurwitzEvenOrientationVector_FE_even)

theorem riemannHypothesis_iff_FE_odd_weil_nonnegative :
    RiemannHypothesis ↔
      ∀ v, XiFunctionalEquationParity (-1) v → 0 ≤ xiWeilHilbertQuadratic v :=
  riemannHypothesis_iff_FE_even_weil_nonnegative.trans
    (xiWeilHilbertQuadratic_FE_sector_nonnegative_iff 1)

/-- Every raw FE-even vector is orthogonal to the original Hurwitz orientation vector. -/
theorem inner_xiHurwitzOrientationVector_FE_even_eq_zero
    {v : lp (fun _ : XiZeroCopy => ℂ) 2} (hv : XiFunctionalEquationParity 1 v) :
    inner ℂ xiHurwitzOrientationVector v = 0 := by
  rw [lp.inner_eq_tsum]
  let f : XiZeroCopy → ℂ := fun q => inner ℂ (xiHurwitzOrientationVector q) (v q)
  have hf (q : XiZeroCopy) : f (xiZeroCopyReflectEquiv q) = -f q := by
    dsimp only [f]
    rw [hv q, one_mul, xiHurwitzOrientationVector_apply,
      xiHurwitzOrientationCoordinate_reflect, inner_neg_left]
    rfl
  have hs := xiZeroCopyReflectEquiv.tsum_eq f
  simp_rw [hf] at hs
  rw [tsum_neg] at hs
  change (∑' q, f q) = 0
  linear_combination (-1 / 2 : ℂ) * hs

/-- Sharp approximation law: the closest raw even vector to the original witness is zero. -/
theorem norm_sq_xiHurwitzOrientationVector_sub_FE_even
    {v : lp (fun _ : XiZeroCopy => ℂ) 2} (hv : XiFunctionalEquationParity 1 v) :
    ‖xiHurwitzOrientationVector - v‖ ^ (2 : ℕ) =
      xiHurwitzOrientationEnergy + ‖v‖ ^ (2 : ℕ) := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_xiHurwitzOrientationVector_FE_even_eq_zero hv,
    map_zero, mul_zero, sub_zero, norm_sq_xiHurwitzOrientationVector]

end

end RHTower
