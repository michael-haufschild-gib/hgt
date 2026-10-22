import GaloisForLFunctions.HilbertMetric.SixthJetRaywiseCoalescedCone
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedFourthJetCuspClosure

/-!
# Unconditional raywise coalesced cone for the center-mixed theta density

The nested fourth-jet cusp allows the first gap to depend arbitrarily on the second.  This file
extracts one more source derivative and proves the stronger fixed-direction statement: for every
positive aspect ratio `lambda`, the actual three-node theta matrix at gaps `t` and `lambda * t` is
positive definite for every sufficiently small positive `t`.

The proof is source-pure.  The strict fourth Hankel jet is the unconditional theta-source theorem
from `HedenmalmCenterMixedFourthJetCuspClosure`; no Riemann-hypothesis or positivity assumption is
introduced.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Sixth center derivative of the center-mixed density. -/
def thetaCuspCenterMixedDensitySixthJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 6 0 a t -
    6 * thetaCuspCenterMixedDerivativeProductIntegral 5 1 a t +
      15 * thetaCuspCenterMixedDerivativeProductIntegral 4 2 a t -
        20 * thetaCuspCenterMixedDerivativeProductIntegral 3 3 a t +
          15 * thetaCuspCenterMixedDerivativeProductIntegral 2 4 a t -
            6 * thetaCuspCenterMixedDerivativeProductIntegral 1 5 a t +
              thetaCuspCenterMixedDerivativeProductIntegral 0 6 a t

theorem hasDerivAt_thetaCuspCenterMixedDensityFifthJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensityFifthJet a)
      (thetaCuspCenterMixedDensitySixthJet a t) t := by
  have h50 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 5 0 t
  have h41 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 4 1 t
  have h32 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 3 2 t
  have h23 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 2 3 t
  have h14 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 4 t
  have h05 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 5 t
  unfold thetaCuspCenterMixedDensityFifthJet thetaCuspCenterMixedDensitySixthJet
  convert (((((h50.sub (h41.const_mul 5)).add (h32.const_mul 10)).sub
    (h23.const_mul 10)).add (h14.const_mul 5)).sub h05) using 1
  all_goals first | rfl | ring

theorem continuous_thetaCuspCenterMixedDensitySixthJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedDensitySixthJet a) := by
  have hcont (m n : ℕ) :
      Continuous (thetaCuspCenterMixedDerivativeProductIntegral m n a) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha m n t).continuousAt
  unfold thetaCuspCenterMixedDensitySixthJet
  fun_prop

private theorem contDiff_succ_of_hasDerivAt
    {n : ℕ} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ContDiff ℝ n f') :
    ContDiff ℝ (n + 1) f := by
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
  rw [show deriv f = f' by
    funext x
    exact (hf x).deriv]
  exact hf'

/-- The center-mixed density is `C⁶`, with all six jets supplied by the source-integral
derivative chain. -/
theorem contDiff_six_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ContDiff ℝ 6 (thetaCuspCenterMixedDensity a) := by
  have h6 : ContDiff ℝ 0 (thetaCuspCenterMixedDensitySixthJet a) :=
    contDiff_zero.mpr (continuous_thetaCuspCenterMixedDensitySixthJet ha0 ha)
  have h5 : ContDiff ℝ 1 (thetaCuspCenterMixedDensityFifthJet a) :=
    contDiff_succ_of_hasDerivAt
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFifthJet ha0 ha t) h6
  have h4 : ContDiff ℝ 2 (thetaCuspCenterMixedDensityFourthJet a) :=
    contDiff_succ_of_hasDerivAt
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFourthJet ha0 ha t) h5
  have h3 : ContDiff ℝ 3 (thetaCuspCenterMixedDensityThirdJet a) :=
    contDiff_succ_of_hasDerivAt
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityThirdJet ha0 ha t) h4
  have h2 : ContDiff ℝ 4 (thetaCuspCenterMixedDensitySecondJet a) :=
    contDiff_succ_of_hasDerivAt
      (fun t => hasDerivAt_thetaCuspCenterMixedDensitySecondJet ha0 ha t) h3
  have h1 : ContDiff ℝ 5 (thetaCuspCenterMixedDensityFirstJet a) :=
    contDiff_succ_of_hasDerivAt
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0 ha t) h2
  exact contDiff_succ_of_hasDerivAt
    (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0 ha t) h1

theorem iteratedDeriv_one_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 1 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensityFirstJet a := by
  rw [iteratedDeriv_one]
  funext t
  exact (hasDerivAt_thetaCuspCenterMixedDensity ha0 ha t).deriv

theorem iteratedDeriv_two_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 2 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensitySecondJet a := by
  calc
    iteratedDeriv 2 (thetaCuspCenterMixedDensity a) =
        deriv (iteratedDeriv 1 (thetaCuspCenterMixedDensity a)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (thetaCuspCenterMixedDensityFirstJet a) := by
      rw [iteratedDeriv_one_thetaCuspCenterMixedDensity ha0 ha]
    _ = thetaCuspCenterMixedDensitySecondJet a := by
      funext t
      exact (hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0 ha t).deriv

theorem iteratedDeriv_three_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 3 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensityThirdJet a := by
  calc
    iteratedDeriv 3 (thetaCuspCenterMixedDensity a) =
        deriv (iteratedDeriv 2 (thetaCuspCenterMixedDensity a)) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (thetaCuspCenterMixedDensitySecondJet a) := by
      rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0 ha]
    _ = thetaCuspCenterMixedDensityThirdJet a := by
      funext t
      exact (hasDerivAt_thetaCuspCenterMixedDensitySecondJet ha0 ha t).deriv

theorem iteratedDeriv_four_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 4 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensityFourthJet a := by
  calc
    iteratedDeriv 4 (thetaCuspCenterMixedDensity a) =
        deriv (iteratedDeriv 3 (thetaCuspCenterMixedDensity a)) := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (thetaCuspCenterMixedDensityThirdJet a) := by
      rw [iteratedDeriv_three_thetaCuspCenterMixedDensity ha0 ha]
    _ = thetaCuspCenterMixedDensityFourthJet a := by
      funext t
      exact (hasDerivAt_thetaCuspCenterMixedDensityThirdJet ha0 ha t).deriv

theorem iteratedDeriv_five_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 5 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensityFifthJet a := by
  calc
    iteratedDeriv 5 (thetaCuspCenterMixedDensity a) =
        deriv (iteratedDeriv 4 (thetaCuspCenterMixedDensity a)) := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (thetaCuspCenterMixedDensityFourthJet a) := by
      rw [iteratedDeriv_four_thetaCuspCenterMixedDensity ha0 ha]
    _ = thetaCuspCenterMixedDensityFifthJet a := by
      funext t
      exact (hasDerivAt_thetaCuspCenterMixedDensityFourthJet ha0 ha t).deriv

/-- The literal sixth center derivative is the completed derivative-product integral jet. -/
theorem iteratedDeriv_six_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    iteratedDeriv 6 (thetaCuspCenterMixedDensity a) =
      thetaCuspCenterMixedDensitySixthJet a := by
  calc
    iteratedDeriv 6 (thetaCuspCenterMixedDensity a) =
        deriv (iteratedDeriv 5 (thetaCuspCenterMixedDensity a)) := by
      rw [show (6 : ℕ) = 5 + 1 by norm_num, iteratedDeriv_succ]
    _ = deriv (thetaCuspCenterMixedDensityFifthJet a) := by
      rw [iteratedDeriv_five_thetaCuspCenterMixedDensity ha0 ha]
    _ = thetaCuspCenterMixedDensitySixthJet a := by
      funext t
      exact (hasDerivAt_thetaCuspCenterMixedDensityFifthJet ha0 ha t).deriv

/-- **Unconditional raywise coalesced cone.**  Every fixed positive direction through the
two-gap origin enters the strict positive-definite chamber of the actual center-mixed theta
three-point matrix. -/
theorem exists_thetaCuspCenterMixed_raywiseCoalescedCone_posDef
    {a lambda : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hlambda : 0 < lambda) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a t (lambda * t)) := by
  let f := thetaCuspCenterMixedDensity a
  have hf : ContDiff ℝ 6 f := contDiff_six_thetaCuspCenterMixedDensity ha0.le ha
  have hjet1 : iteratedDeriv 1 f 0 = 0 := by
    rw [iteratedDeriv_one_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensityFirstJet_zero a
  have hjet2 : iteratedDeriv 2 f 0 < 0 := by
    rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha
  have hjet3 : iteratedDeriv 3 f 0 = 0 := by
    rw [iteratedDeriv_three_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensityThirdJet_zero a
  have hjet4 : 0 < f 0 * iteratedDeriv 4 f 0 - iteratedDeriv 2 f 0 ^ (2 : ℕ) := by
    rw [iteratedDeriv_four_thetaCuspCenterMixedDensity ha0.le ha,
      iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha
  have hjet5 : iteratedDeriv 5 f 0 = 0 := by
    rw [iteratedDeriv_five_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensityFifthJet_zero a
  rcases HilbertMetric.exists_threePointCorrelationDeterminantRay_pos_right
      hf hjet1 hjet3 hjet5 hjet2 hjet4 hlambda with ⟨delta, hdelta, hdet⟩
  refine ⟨delta, hdelta, fun t ht htδ => ?_⟩
  have hdetpos :
      0 < HilbertMetric.threePointCorrelationDeterminant
        (f 0) (f t) (f (lambda * t)) (f (t + lambda * t)) := by
    simpa [HilbertMetric.threePointCorrelationDeterminantRay,
      HilbertMetric.threePointCorrelationDeterminantPath] using hdet t ht htδ
  have hposdef := (HilbertMetric.threePointCorrelationMatrix_posDef_iff
    (thetaCuspCenterMixedDensity_pos ha0 ha 0)
    (thetaCuspCenterMixedDensity_pos ha0 ha t).le
    (thetaCuspCenterMixedDensity_lt_zero ha0 ha ht)).2 hdetpos
  simpa [thetaCuspCenterMixedThreePointMatrix, f] using hposdef

end

end RHTower
