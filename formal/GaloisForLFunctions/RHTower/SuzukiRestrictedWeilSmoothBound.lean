import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilSourceForm
import GaloisForLFunctions.RHTower.SuzukiHlogCompactEmbedding
import GaloisForLFunctions.HTGeometry.ClockGoursatGlobal

/-!
# Suzuki's literal smooth Weil block is an `L²`-bounded perturbation

Suzuki's restricted form contains the continuous kernel `r''(|x-y|)`.  The preceding source
modules identify that kernel exactly and prove its removable singularity at zero.  This file
closes the remaining functional-analytic step for that block: on every positive finite aperture,
its quadratic form is bounded below by a finite multiple of the interval `L²` energy.

The endpoint has no analytic premise.  Aperture positivity is bundled in
`SuzukiPositiveAperture`, regularity and support are bundled in `SuzukiRestrictedWeilCore`, and the
bounding constant is chosen from compactness of Suzuki's literal kernel.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Canonical finite bound for Suzuki's literal smooth kernel on the aperture difference square. -/
noncomputable def suzukiWeilRemainderApertureBound (a : ℝ) : ℝ :=
  Classical.choose (exists_abs_suzukiWeilRemainderKernel_sub_le a)

/-- The chosen source bound is nonnegative and controls every difference of aperture points. -/
theorem suzukiWeilRemainderApertureBound_spec (a : ℝ) :
    0 ≤ suzukiWeilRemainderApertureBound a ∧
      ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
        |RHTower.suzukiWeilRemainderKernel (x - y)| ≤
          suzukiWeilRemainderApertureBound a :=
  Classical.choose_spec (exists_abs_suzukiWeilRemainderKernel_sub_le a)

/-- Rectangle Schur bound in the exact normalization needed by Suzuki's smooth block. -/
theorem iteratedKernelQuadratic_abs_le
    {a C : ℝ} (ha : 0 ≤ a) {k u : ℝ → ℝ}
    (hk : Continuous k) (hu : Continuous u)
    (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a, |k (x - y)| ≤ C) :
    |∫ x in (-a)..a, (∫ y in (-a)..a, k (x - y) * u y) * u x| ≤
      2 * a * C * ∫ x in (-a)..a, u x ^ 2 := by
  let F : ℝ → ℝ → ℝ := fun x y => k (x - y) * u y * u x
  let M : ℝ → ℝ → ℝ := fun x y => C * (u y ^ 2 + u x ^ 2) / 2
  have hF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    exact ((hk.comp (continuous_fst.sub continuous_snd)).mul
      (hu.comp continuous_snd)).mul (hu.comp continuous_fst)
  have hM : Continuous fun p : ℝ × ℝ => M p.1 p.2 := by
    exact (continuous_const.mul
      ((hu.comp continuous_snd).pow 2 |>.add ((hu.comp continuous_fst).pow 2))).div_const 2
  have hrewrite :
      (∫ x in (-a)..a, (∫ y in (-a)..a, k (x - y) * u y) * u x) =
        ∫ x in (-a)..a, ∫ y in (-a)..a, F x y := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [intervalIntegral.integral_mul_const]
  rw [hrewrite]
  have hinnerF : Continuous fun x => ∫ y in (-a)..a, F x y :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_const
  have hinnerAbs : Continuous fun x => ∫ y in (-a)..a, |F x y| :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF.abs continuous_const
  have hinnerM : Continuous fun x => ∫ y in (-a)..a, M x y :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hM continuous_const
  have houterAbs :
      |∫ x in (-a)..a, ∫ y in (-a)..a, F x y| ≤
        ∫ x in (-a)..a, |∫ y in (-a)..a, F x y| :=
    abs_integral_le_integral_abs (by linarith)
  have hslice : ∀ x ∈ Icc (-a) a,
      |∫ y in (-a)..a, F x y| ≤ ∫ y in (-a)..a, |F x y| := by
    intro x _
    exact abs_integral_le_integral_abs (by linarith)
  have hone :
      (∫ x in (-a)..a, |∫ y in (-a)..a, F x y|) ≤
        ∫ x in (-a)..a, ∫ y in (-a)..a, |F x y| := by
    exact intervalIntegral.integral_mono_on (by linarith)
      (hinnerF.abs.intervalIntegrable (-a) a) (hinnerAbs.intervalIntegrable (-a) a) hslice
  have hpoint : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a, |F x y| ≤ M x y := by
    intro x hx y hy
    have hkxy := hC x hx y hy
    have hamgm : 2 * |u y * u x| ≤ u y ^ 2 + u x ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|u y| - |u x|), sq_abs (u y), sq_abs (u x)]
    dsimp [F, M]
    rw [show k (x - y) * u y * u x = k (x - y) * (u y * u x) by ring, abs_mul]
    have hprod : |k (x - y)| * |u y * u x| ≤ C * |u y * u x| :=
      mul_le_mul_of_nonneg_right hkxy (abs_nonneg _)
    calc
      |k (x - y)| * |u y * u x| ≤ C * |u y * u x| := hprod
      _ ≤ C * (u y ^ 2 + u x ^ 2) / 2 := by nlinarith
  have htwo :
      (∫ x in (-a)..a, ∫ y in (-a)..a, |F x y|) ≤
        ∫ x in (-a)..a, ∫ y in (-a)..a, M x y := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hinnerAbs.intervalIntegrable (-a) a) (hinnerM.intervalIntegrable (-a) a)
    intro x hx
    exact intervalIntegral.integral_mono_on (by linarith)
      ((hF.comp (continuous_const.prodMk continuous_id)).abs.intervalIntegrable _ _)
      ((hM.comp (continuous_const.prodMk continuous_id)).intervalIntegrable (-a) a)
      (fun y hy => hpoint x hx y hy)
  have hmodel :
      (∫ x in (-a)..a, ∫ y in (-a)..a, M x y) =
        2 * a * C * ∫ x in (-a)..a, u x ^ 2 := by
    have hsq : Continuous fun x => u x ^ 2 := hu.pow 2
    have hinner : ∀ x : ℝ,
        (∫ y in (-a)..a, M x y) =
          C / 2 * (∫ y in (-a)..a, u y ^ 2) +
            (2 * a) * (C / 2 * u x ^ 2) := by
      intro x
      have heq : M x = fun y => C / 2 * u y ^ 2 + (C / 2 * u x ^ 2) := by
        funext y
        dsimp [M]
        ring
      rw [heq, intervalIntegral.integral_add
        ((hsq.const_mul (C / 2)).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    simp_rw [hinner]
    let E : ℝ := ∫ y in (-a)..a, u y ^ 2
    have hvar : Continuous fun x : ℝ => 2 * a * (C / 2 * u x ^ 2) :=
      continuous_const.mul (hsq.const_mul (C / 2))
    rw [intervalIntegral.integral_add
      (continuous_const.intervalIntegrable _ _) (hvar.intervalIntegrable _ _)]
    have hconst : (∫ _x in (-a)..a, C / 2 * E) = 2 * a * (C / 2 * E) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hvarint : (∫ x in (-a)..a, 2 * a * (C / 2 * u x ^ 2)) =
        a * C * E := by
      change (∫ x in (-a)..a, 2 * a * (C / 2 * u x ^ 2)) =
        a * C * (∫ y in (-a)..a, u y ^ 2)
      rw [show (fun x => 2 * a * (C / 2 * u x ^ 2)) =
          fun x => (a * C) * u x ^ 2 by funext x; ring,
        intervalIntegral.integral_const_mul]
    change (∫ _x in (-a)..a, C / 2 * E) +
        (∫ x in (-a)..a, 2 * a * (C / 2 * u x ^ 2)) = 2 * a * C * E
    rw [hconst, hvarint]
    ring
  rw [hmodel] at htwo
  exact houterAbs.trans (hone.trans htwo)

/-- **Unconditional smooth-block lower bound.**  Suzuki's exact remainder block is an `L²`-bounded
perturbation on every positive aperture.  No kernel regularity or boundedness premise remains. -/
theorem suzukiRestrictedWeilSmoothBlock_lowerBound
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    -(2 * a.1 * suzukiWeilRemainderApertureBound a.1 *
        ∫ x in (-a.1)..a.1, u x ^ 2) ≤
      weilSmoothBlock a.1 RHTower.suzukiWeilRemainderKernel u u := by
  have hbound := iteratedKernelQuadratic_abs_le a.property.le
    RHTower.continuous_suzukiWeilRemainderKernel u.continuous
    (suzukiWeilRemainderApertureBound_spec a.1).1
    (suzukiWeilRemainderApertureBound_spec a.1).2
  rw [weilSmoothBlock]
  have hupper := (le_abs_self
    (∫ x in (-a.1)..a.1,
      (∫ y in (-a.1)..a.1, RHTower.suzukiWeilRemainderKernel (x - y) * u y) * u x)).trans
      hbound
  linarith

end GaloisForLFunctions.RHTower
