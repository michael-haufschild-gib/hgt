import GaloisForLFunctions.HTGeometry.ZeroFreeRadiusSelection
import GaloisForLFunctions.HTGeometry.MaxModulusCharacteristicBound
import GaloisForLFunctions.HTGeometry.DivisorMassCounting

/-!
# The divisor mass of an entire function against its characteristic

Jensen's inequality bounds the number of zeros in a disc by the logarithm of the maximum modulus on a
larger circle divided by the logarithm of the ratio of radii, and the Poisson–Jensen bound turns the
maximum modulus into the characteristic at a still larger radius.  The three radii can be taken as
close together as one likes, so the bound is usable with the tiny windows the Borel growth lemma
supplies — unlike the route through the counting function at twice the radius.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric MeromorphicOn ValueDistribution Real

/-- **The divisor mass in a disc, against the characteristic at a slightly larger radius.** -/
theorem divisorMass_le_characteristic {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, meromorphicOrderAt g z ≠ ⊤) (hg0 : ‖g 0‖ = 1)
    {R R' R'' : ℝ} (hR : 0 < R) (hRR' : R < R') (hR'R'' : R' < R'') (hR''1 : 1 ≤ R'') :
    (∑ᶠ u : ℂ, ((MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ))
      ≤ ((R'' + R') / (R'' - R')
          * (2 * characteristic g ⊤ R''
            + max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖|))
        / Real.log (R' / R) := by
  classical
  set K : ℝ := max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖| with hK
  set B : ℝ := (R'' + R') / (R'' - R') * (2 * characteristic g ⊤ R'' + K) with hB
  have hR'0 : 0 < R' := lt_trans hR hRR'
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (le_max_left _ _)
  have hT0 : 0 ≤ characteristic g ⊤ R'' := ValueDistribution.characteristic_nonneg (by linarith)
  have hfac : 0 ≤ (R'' + R') / (R'' - R') := by
    apply div_nonneg <;> linarith
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg hfac (by linarith)
  -- the maximum modulus on the circle of radius `R'`
  have hbound : ∀ z ∈ sphere (0 : ℂ) |R'|, ‖g z‖ ≤ Real.exp B := by
    intro z hz
    have hznorm : ‖z‖ = R' := by
      rw [mem_sphere_iff_norm, sub_zero] at hz
      rw [hz, abs_of_pos hR'0]
    have hpl := posLog_norm_le_characteristic hg horder hR''1 (le_of_lt hR'0) hR'R''
      (w := z) (by rw [hznorm])
    rw [← hK, ← hB] at hpl
    have h1 : ‖g z‖ ≤ Real.exp (Real.posLog ‖g z‖) := by
      rcases le_or_gt ‖g z‖ 1 with hle | hgt
      · exact le_trans hle (by simpa using Real.one_le_exp Real.posLog_nonneg)
      · rw [Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; linarith),
          Real.exp_log (by linarith)]
    exact le_trans h1 (Real.exp_le_exp.mpr hpl)
  have hM1 : (1 : ℝ) ≤ Real.exp B := Real.one_le_exp hB0
  have hg0ne : g 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hg0
    norm_num at hg0
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := R) (R := R')
    (M := Real.exp B) (f := g) (by rw [abs_of_pos hR]; exact hR)
    (by rw [abs_of_pos hR, abs_of_pos hR'0]; exact hRR') hM1
    (fun z _ => hg.analyticAt z) hg0ne hbound
  have hcast : ((∑ᶠ u : ℂ, (MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) u : ℤ) : ℤ) : ℝ)
      = ∑ᶠ u : ℂ, ((MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ) :=
    map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor g (closedBall (0 : ℂ) |R|)).finiteSupport
        (isCompact_closedBall (0 : ℂ) |R|))
  rw [hg0, div_one, Real.log_exp] at hjensen
  rw [← hcast]
  exact hjensen

end GaloisForLFunctions.HTGeometry
