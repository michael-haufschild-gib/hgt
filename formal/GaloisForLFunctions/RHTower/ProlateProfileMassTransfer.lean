import GaloisForLFunctions.RHTower.ProlateHermitePairingHypotheses
import GaloisForLFunctions.RHTower.ProlateGlobalDerivativeBounds
import GaloisForLFunctions.RHTower.ProlateL2Regularity
import GaloisForLFunctions.RHTower.ProlateHermiteRescale

/-!
# From window mass to a sup bound on the rescaled profile

A band eigenfunction is bounded by its own window mass:
`|Φ(x)| ≤ |lam|⁻¹ (|c|/π) ∫_{-1}^{1}|Φ|`.  The window mass in turn is controlled by the *rescaled*
square mass, because the elementary estimate `|w| ≤ (t + w²/t)/2` at `t = c^{-1/4}` converts a bound
`∫_{-1}^{1}w² ≤ N c^{-1/2}` into `∫_{-1}^{1}|w| ≤ (1 + N/2) c^{-1/4}`.  Since the square mass of the
Hermite-rescaled profile is uniformly bounded, the sup norm of the rescaled profile grows at most
like `c^{3/4}` — slowly enough that the ladder pin's `1/c` still wins.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace RHTower

/-- **Explicit form of the band eigenfunction bound.** -/
theorem abs_le_of_bandTransform_eigen_explicit {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) (x : ℝ) :
    |Φ x| ≤ |lam|⁻¹ * (|c| / Real.pi * ∫ y in (-1 : ℝ)..1, |Φ y|) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlam0 : (0 : ℝ) < |lam| := abs_pos.2 hlam
  have hbandeq : bandTransform c Φ x = ∫ y in (-1 : ℝ)..1, sincSmooth c (x - y) * Φ y := by
    rw [bandTransform]
    exact intervalIntegral.integral_congr fun y _ => by rw [sincKernelSmooth]
  have hstep : |∫ y in (-1 : ℝ)..1, sincSmooth c (x - y) * Φ y|
      ≤ |c| / Real.pi * ∫ y in (-1 : ℝ)..1, |Φ y| :=
    abs_bandIntegral_le (contDiff_sincSmooth c).continuous hΦ
      (fun u => GaloisForLFunctions.RHTower.abs_sincSmooth_le c u) x
  have hlamΦ : |lam| * |Φ x| ≤ |c| / Real.pi * ∫ y in (-1 : ℝ)..1, |Φ y| := by
    have h : |lam * Φ x| ≤ |c| / Real.pi * ∫ y in (-1 : ℝ)..1, |Φ y| := by
      rw [← hband x, hbandeq]
      exact hstep
    rwa [abs_mul] at h
  rw [← le_div_iff₀' hlam0] at hlamΦ
  calc |Φ x| ≤ (|c| / Real.pi * ∫ y in (-1 : ℝ)..1, |Φ y|) / |lam| := hlamΦ
    _ = |lam|⁻¹ * (|c| / Real.pi * ∫ y in (-1 : ℝ)..1, |Φ y|) := by
        rw [div_eq_inv_mul]

/-- Rescaling a square mass from the Hermite scale to the unit window. -/
theorem integral_sq_rescale {c : ℝ} (hc : 0 < c) (v : ℝ → ℝ) :
    (∫ y in (-1 : ℝ)..1, v (Real.sqrt c * y) ^ 2)
      = (Real.sqrt c)⁻¹ * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), v ξ ^ 2 := by
  have hs : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hc
  have h := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (c := Real.sqrt c) (fun ξ : ℝ => v ξ ^ 2) hs
  rw [h]
  simp [smul_eq_mul, mul_neg, mul_one]

/-- **The absolute mass from the square mass.**  The elementary bound `|w| ≤ (t + w²/t)/2` at the
balanced scale `t` turns a square-mass bound into an absolute-mass bound with the square root of the
same size. -/
theorem integral_abs_le_of_integral_sq_le {w : ℝ → ℝ} {S t : ℝ} (ht : 0 < t)
    (hw : Continuous w) (hS : (∫ y in (-1 : ℝ)..1, w y ^ 2) ≤ S) :
    (∫ y in (-1 : ℝ)..1, |w y|) ≤ t + S / (2 * t) := by
  have hint1 : IntervalIntegrable (fun y : ℝ => |w y|) volume (-1) 1 :=
    hw.abs.intervalIntegrable _ _
  have hcw : Continuous fun y : ℝ => w y ^ 2 / (2 * t) := by fun_prop
  have hint2 : IntervalIntegrable (fun y : ℝ => t / 2 + w y ^ 2 / (2 * t)) volume (-1) 1 :=
    (continuous_const.add hcw).intervalIntegrable _ _
  have hpt : ∀ y : ℝ, |w y| ≤ t / 2 + w y ^ 2 / (2 * t) := by
    intro y
    have hsq : (0 : ℝ) ≤ |w y| ^ 2 - 2 * |w y| * t + t ^ 2 := by
      have h := sq_nonneg (|w y| - t)
      nlinarith [h]
    have habs : |w y| ^ 2 = w y ^ 2 := sq_abs _
    have hkey : |w y| * (2 * t) ≤ (t / 2 + w y ^ 2 / (2 * t)) * (2 * t) := by
      have hexp : (t / 2 + w y ^ 2 / (2 * t)) * (2 * t) = t ^ 2 + w y ^ 2 := by
        field_simp
      rw [hexp]
      nlinarith [hsq, habs]
    exact le_of_mul_le_mul_right hkey (by positivity)
  have hmono : (∫ y in (-1 : ℝ)..1, |w y|)
      ≤ ∫ y in (-1 : ℝ)..1, (t / 2 + w y ^ 2 / (2 * t)) :=
    intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 fun y _ => hpt y
  have hcompute : (∫ y in (-1 : ℝ)..1, (t / 2 + w y ^ 2 / (2 * t)))
      = t + (∫ y in (-1 : ℝ)..1, w y ^ 2) / (2 * t) := by
    have hadd := intervalIntegral.integral_add (a := (-1 : ℝ)) (b := 1)
      (f := fun _ : ℝ => t / 2) (g := fun y : ℝ => w y ^ 2 / (2 * t))
      (intervalIntegrable_const (μ := volume)) (hcw.intervalIntegrable _ _)
    rw [hadd, intervalIntegral.integral_const, intervalIntegral.integral_div]
    simp
    ring
  rw [hcompute] at hmono
  have hstep : (∫ y in (-1 : ℝ)..1, w y ^ 2) / (2 * t) ≤ S / (2 * t) := by
    gcongr
  linarith


/-- **The sup bound from the rescaled square mass.**  A uniform bound `N` on the Hermite-rescaled
square mass forces the band eigenfunction's sup norm below `|lam|⁻¹ (c/π)(1+N/2) c^{-1/4}`, so the
rescaled profile grows at most like `c^{3/4}`. -/
theorem abs_le_of_rescaled_mass_le {c lam N : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x)
    (hmass : (∫ ξ in (-Real.sqrt c)..(Real.sqrt c), prolateHermiteRescale c Φ ξ ^ 2) ≤ N)
    (x : ℝ) :
    |Φ x| ≤ |lam|⁻¹ * (c / Real.pi * ((1 + N / 2) / Real.sqrt (Real.sqrt c))) := by
  have hs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.2 hc
  have hq : (0 : ℝ) < Real.sqrt (Real.sqrt c) := Real.sqrt_pos.2 hs
  have hqsq : Real.sqrt (Real.sqrt c) ^ 2 = Real.sqrt c := Real.sq_sqrt hs.le
  set q : ℝ := Real.sqrt (Real.sqrt c) with hqdef
  -- the unit-window square mass is the rescaled one, divided by `√c`
  have hpt : ∀ y : ℝ, prolateHermiteRescale c Φ (Real.sqrt c * y) = Φ y := by
    intro y
    exact congrFun (prolateHermiteRescale_sqrtScale hc Φ) y
  have hrescale : (∫ y in (-1 : ℝ)..1, Φ y ^ 2)
      = (Real.sqrt c)⁻¹ * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
          prolateHermiteRescale c Φ ξ ^ 2 := by
    rw [← integral_sq_rescale hc (prolateHermiteRescale c Φ)]
    exact intervalIntegral.integral_congr fun y _ => by rw [hpt y]
  have hsqmass : (∫ y in (-1 : ℝ)..1, Φ y ^ 2) ≤ N / q ^ 2 := by
    rw [hrescale, hqsq]
    rw [inv_mul_eq_div, div_le_div_iff₀ hs hs]
    nlinarith [hmass, hs]
  -- the absolute mass, at the balanced scale
  have habsmass : (∫ y in (-1 : ℝ)..1, |Φ y|) ≤ (1 + N / 2) / q := by
    have h := integral_abs_le_of_integral_sq_le (w := Φ) (S := N / q ^ 2) (t := q⁻¹)
      (by positivity) hΦ hsqmass
    have hid : q⁻¹ + N / q ^ 2 / (2 * q⁻¹) = (1 + N / 2) / q := by
      field_simp
    rwa [hid] at h
  -- combine with the kernel bound
  have hband' := abs_le_of_bandTransform_eigen_explicit hlam hΦ hband x
  have hc' : |c| = c := abs_of_pos hc
  rw [hc'] at hband'
  refine le_trans hband' ?_
  have hlam0 : (0 : ℝ) < |lam|⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hlam0.le
  refine mul_le_mul_of_nonneg_left habsmass (by positivity)

end RHTower

end
