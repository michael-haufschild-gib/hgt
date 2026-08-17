import GaloisForLFunctions.RHTower.XiMassConjugatedCarrier

/-!
# The conjugated carrier is uniformly of square-root size

Removing the exterior exponential from the mass profile leaves

`G(w) = e^{aZ}·2aτ·K₁(aZ)/Z`,

and the Schläfli envelope `‖K₁(ζ)‖ ≤ e^{-Re ζ}·e^{1/(2Re ζ)}·√(2π/Re ζ)` cancels the conjugating
exponential exactly.  What survives is

`‖G(w)‖ ≤ 2a‖τ‖·e^{1/(2a·Re Z)}·√(2π/(a·Re Z))/Re Z`,

which on a slope cone, where `Re Z ≳ u`, is `O(u^{-1/2})` — no oscillation and no exponential left.
That is the input the Cauchy iteration needs: the conjugated carrier is bounded, so all its
derivatives on a disc of radius comparable with the height are smaller by the corresponding power of
the height.
-/

open Complex

namespace RHTower

noncomputable section

/-- The conjugated carrier: the mass profile with its exterior exponential removed. -/
def xiMassConjugatedCarrier (a : ℝ) (τ w : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * xiMassHeightRadius τ w) * xiMassBesselHeightSide a τ w

/-- The profile is the exponential times the carrier. -/
theorem xiMassBesselHeightSide_eq_conjugated (a : ℝ) (τ w : ℂ) :
    xiMassBesselHeightSide a τ w
      = Complex.exp (-(a : ℂ) * xiMassHeightRadius τ w) * xiMassConjugatedCarrier a τ w := by
  rw [xiMassConjugatedCarrier, ← mul_assoc, ← Complex.exp_add]
  have hz : -(a : ℂ) * xiMassHeightRadius τ w + (a : ℂ) * xiMassHeightRadius τ w = 0 := by ring
  rw [hz, Complex.exp_zero, one_mul]

theorem re_mul_xiMassHeightRadius (a : ℝ) (τ w : ℂ) :
    ((a : ℂ) * xiMassHeightRadius τ w).re = a * HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
  rw [xiMassHeightRadius, Complex.mul_re, HTGeometry.csqrt_re]
  simp

/-- **The conjugated carrier is bounded by the reciprocal propagation rate.** -/
theorem norm_xiMassConjugatedCarrier_le {a : ℝ} {τ w : ℂ} (ha : 0 < a)
    (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    ‖xiMassConjugatedCarrier a τ w‖
      ≤ 2 * a * ‖τ‖ / HTGeometry.csqrtRe (τ ^ 2 + w ^ 2)
        * (Real.exp (1 / (2 * (a * HTGeometry.csqrtRe (τ ^ 2 + w ^ 2))))
          * Real.sqrt (2 * Real.pi / (a * HTGeometry.csqrtRe (τ ^ 2 + w ^ 2)))) := by
  set R : ℝ := HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) with hR
  have hR0 : (0 : ℝ) < R := HTGeometry.csqrtRe_pos hw
  have haR : (0 : ℝ) < a * R := mul_pos ha hR0
  have hre : ((a : ℂ) * xiMassHeightRadius τ w).re = a * R := re_mul_xiMassHeightRadius a τ w
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hZnorm : R ≤ ‖xiMassHeightRadius τ w‖ := by
    have h := Complex.abs_re_le_norm (xiMassHeightRadius τ w)
    have hre' : (xiMassHeightRadius τ w).re = R := by
      rw [xiMassHeightRadius, HTGeometry.csqrt_re]
    rw [hre', abs_of_pos hR0] at h
    exact h
  have hbess : ‖HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w)‖
      ≤ Real.exp (-(a * R)) * Real.exp (1 / (2 * (a * R))) * Real.sqrt (2 * Real.pi / (a * R)) := by
    have h := HTGeometry.norm_besselK1C_le (z := (a : ℂ) * xiMassHeightRadius τ w) (by rw [hre]; exact haR)
    rwa [hre] at h
  have hexp : ‖Complex.exp ((a : ℂ) * xiMassHeightRadius τ w)‖ = Real.exp (a * R) := by
    rw [Complex.norm_exp, hre]
  have hsplit : xiMassConjugatedCarrier a τ w
      = Complex.exp ((a : ℂ) * xiMassHeightRadius τ w)
        * (2 * (a : ℂ) * τ / xiMassHeightRadius τ w)
        * HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w) := by
    rw [xiMassConjugatedCarrier, xiMassBesselHeightSide, xiMassHeightRadius]
    ring
  rw [hsplit, norm_mul, norm_mul, hexp, norm_div]
  have hnum : ‖2 * (a : ℂ) * τ‖ = 2 * a * ‖τ‖ := by
    rw [show (2 : ℂ) * (a : ℂ) * τ = ((2 * a : ℝ) : ℂ) * τ by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 2 * a)]
  rw [hnum]
  have hquot : 2 * a * ‖τ‖ / ‖xiMassHeightRadius τ w‖ ≤ 2 * a * ‖τ‖ / R :=
    div_le_div_of_nonneg_left (by positivity) hR0 hZnorm
  have hb0 : (0 : ℝ) ≤ ‖HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w)‖ := norm_nonneg _
  have hstep1 : Real.exp (a * R) * (2 * a * ‖τ‖ / ‖xiMassHeightRadius τ w‖)
      ≤ Real.exp (a * R) * (2 * a * ‖τ‖ / R) :=
    mul_le_mul_of_nonneg_left hquot (Real.exp_pos _).le
  have hstep2 : Real.exp (a * R) * (2 * a * ‖τ‖ / ‖xiMassHeightRadius τ w‖)
        * ‖HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w)‖
      ≤ (Real.exp (a * R) * (2 * a * ‖τ‖ / R))
        * (Real.exp (-(a * R)) * Real.exp (1 / (2 * (a * R)))
          * Real.sqrt (2 * Real.pi / (a * R))) :=
    mul_le_mul hstep1 hbess hb0 (by positivity)
  refine le_trans hstep2 (le_of_eq ?_)
  have hcancel : Real.exp (a * R) * Real.exp (-(a * R)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc (Real.exp (a * R) * (2 * a * ‖τ‖ / R))
        * (Real.exp (-(a * R)) * Real.exp (1 / (2 * (a * R)))
          * Real.sqrt (2 * Real.pi / (a * R)))
      = (Real.exp (a * R) * Real.exp (-(a * R))) * ((2 * a * ‖τ‖ / R)
          * (Real.exp (1 / (2 * (a * R))) * Real.sqrt (2 * Real.pi / (a * R)))) := by ring
    _ = 2 * a * ‖τ‖ / R
          * (Real.exp (1 / (2 * (a * R))) * Real.sqrt (2 * Real.pi / (a * R))) := by
        rw [hcancel, one_mul]

end

end RHTower
