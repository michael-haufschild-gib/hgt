import GaloisForLFunctions.HilbertMetric.FourPointEvenParityCusp
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedRaywiseCoalescedCone
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointParityWall

/-!
# Unconditional local even four-point theta cusp

The existing strict fourth center-Hankel theorem controls the reflection-even block of the
equispaced four-point theta Gram kernel.  Hence the even wall is strictly positive near the
coalesced physical cusp.  The remaining local four-point obstruction is entirely reflection-odd.
-/

namespace RHTower

noncomputable section

/-- The reflection-even equispaced four-point theta wall is strictly positive near the cusp. -/
theorem exists_thetaCuspCenterMixed_evenParityWall_pos_right
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < thetaCuspCenterMixedEvenParityWall a t := by
  let f : ℝ → ℝ := thetaCuspCenterMixedDensity a
  have hf : ContDiff ℝ 4 f :=
    (contDiff_six_thetaCuspCenterMixedDensity ha0.le ha).of_le (by norm_num)
  have hderiv1 : iteratedDeriv 1 f = thetaCuspCenterMixedDensityFirstJet a := by
    rw [iteratedDeriv_one]
    funext t
    exact (hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t).deriv
  have hderiv2 : iteratedDeriv 2 f = thetaCuspCenterMixedDensitySecondJet a := by
    calc
      iteratedDeriv 2 f = deriv (iteratedDeriv 1 f) := by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
      _ = deriv (thetaCuspCenterMixedDensityFirstJet a) := by rw [hderiv1]
      _ = thetaCuspCenterMixedDensitySecondJet a := by
        funext t
        exact (hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha t).deriv
  have hderiv3 : iteratedDeriv 3 f = thetaCuspCenterMixedDensityThirdJet a := by
    calc
      iteratedDeriv 3 f = deriv (iteratedDeriv 2 f) := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
      _ = deriv (thetaCuspCenterMixedDensitySecondJet a) := by rw [hderiv2]
      _ = thetaCuspCenterMixedDensityThirdJet a := by
        funext t
        exact (hasDerivAt_thetaCuspCenterMixedDensitySecondJet ha0.le ha t).deriv
  have hderiv4 : iteratedDeriv 4 f = thetaCuspCenterMixedDensityFourthJet a := by
    calc
      iteratedDeriv 4 f = deriv (iteratedDeriv 3 f) := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
      _ = deriv (thetaCuspCenterMixedDensityThirdJet a) := by rw [hderiv3]
      _ = thetaCuspCenterMixedDensityFourthJet a := by
        funext t
        exact (hasDerivAt_thetaCuspCenterMixedDensityThirdJet ha0.le ha t).deriv
  have h1 : iteratedDeriv 1 f 0 = 0 := by
    rw [hderiv1]
    exact thetaCuspCenterMixedDensityFirstJet_zero a
  have h3 : iteratedDeriv 3 f 0 = 0 := by
    rw [hderiv3]
    exact thetaCuspCenterMixedDensityThirdJet_zero a
  have h4 : 0 < f 0 * iteratedDeriv 4 f 0 - iteratedDeriv 2 f 0 ^ 2 := by
    rw [hderiv4, hderiv2]
    exact thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha
  rcases HilbertMetric.exists_fourPointEvenWall_pos_right hf h1 h3 h4 with
    ⟨delta, hdelta, hwall⟩
  refine ⟨delta, hdelta, fun t ht ht_delta => ?_⟩
  simpa [thetaCuspCenterMixedEvenParityWall, toeplitzFourEvenParityWall,
    HilbertMetric.fourPointEvenWall, f] using hwall t ht ht_delta

end

end RHTower
