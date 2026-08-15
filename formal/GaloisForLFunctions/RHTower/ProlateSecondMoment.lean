import GaloisForLFunctions.RHTower.ProlateHermiteRescale
import GaloisForLFunctions.RHTower.ProlateRadialODEBridge
import GaloisForLFunctions.RHTower.ProlateSeparationEnergy

/-!
# The prolate second moment is bounded by the radial separation ratio

The exact prolate Rayleigh identity

`s · ∫_{-1}^{1} Φ² = (∫_{-1}^{1} (1−x²)Φ′²)/c² + ∫_{-1}^{1} x²Φ² ,     s = −χ/c² ,`

has a nonnegative gradient term, because `1 − x² ≥ 0` on the aperture.  Dropping it gives the
normalized second-moment bound

`∫_{-1}^{1} x²Φ² ≤ s · ∫_{-1}^{1} Φ²` .

In the Hermite variable this reads `∫ ξ²u² ≤ (c s) ∫ u²`, so the rescaled profile's second moment is
controlled by the oscillator separation constant alone — the one moment of a prolate mode that stays
finite and uniformly bounded, and the tightness that makes the fixed-window comparison give a global
conclusion.
-/

open MeasureTheory Set

namespace RHTower

/-- The prolate gradient term is nonnegative on the aperture. -/
theorem integral_prolateGradient_nonneg {Phi : ℝ → ℝ} :
    (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2 := by
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro x hx
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  nlinarith [sq_nonneg (deriv Phi x)]

/-- **Second-moment bound.**  A prolate eigenfunction's normalized second moment on the aperture is
at most its radial separation ratio. -/
theorem integral_sq_mul_sq_le_separation
    {c chi : ℝ} (hc : c ≠ 0) {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    (∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2)
      ≤ radialSeparationRatio c chi * ∫ x in (-1 : ℝ)..1, Phi x ^ 2 := by
  have hR := GaloisForLFunctions.RHTower.neg_separation_div_sq_mul_integral_sq_eq hc hsm heig
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hdivnn : (0 : ℝ)
      ≤ (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (deriv Phi x) ^ 2) / c ^ 2 :=
    div_nonneg (integral_prolateGradient_nonneg (Phi := Phi)) hc2.le
  rw [radialSeparationRatio]
  linarith [hR]

/-- Change of variables to the Hermite scale: the rescaled aperture integral is `√c` times the
unit-aperture integral. -/
theorem integral_comp_div_sqrt {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), F (xi / Real.sqrt c))
      = Real.sqrt c * ∫ x in (-1 : ℝ)..1, F x := by
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  rw [intervalIntegral.integral_comp_div F hs, neg_div, div_self hs]
  simp

/-- The rescaled profile's mass over the rescaled aperture. -/
theorem integral_rescaled_sq {c : ℝ} (hc : 0 < c) (Phi : ℝ → ℝ) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), (prolateHermiteRescale c Phi xi) ^ 2)
      = Real.sqrt c * ∫ x in (-1 : ℝ)..1, Phi x ^ 2 :=
  integral_comp_div_sqrt hc (fun x => Phi x ^ 2)

/-- The rescaled profile's integral over the rescaled aperture. -/
theorem integral_rescaled {c : ℝ} (hc : 0 < c) (Phi : ℝ → ℝ) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), prolateHermiteRescale c Phi xi)
      = Real.sqrt c * ∫ x in (-1 : ℝ)..1, Phi x :=
  integral_comp_div_sqrt hc (fun x => Phi x)

/-- The rescaled profile's second moment over the rescaled aperture. -/
theorem integral_rescaled_secondMoment {c : ℝ} (hc : 0 < c) (Phi : ℝ → ℝ) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), xi ^ 2 * (prolateHermiteRescale c Phi xi) ^ 2)
      = Real.sqrt c * (c * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2) := by
  have hs2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have hpt : ∀ xi : ℝ, xi ^ 2 * (prolateHermiteRescale c Phi xi) ^ 2
      = (fun x : ℝ => c * (x ^ 2 * Phi x ^ 2)) (xi / Real.sqrt c) := by
    intro xi
    simp only [prolateHermiteRescale]
    field_simp
    rw [hs2]
    ring
  calc (∫ xi in (-Real.sqrt c)..(Real.sqrt c), xi ^ 2 * (prolateHermiteRescale c Phi xi) ^ 2)
      = ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (fun x : ℝ => c * (x ^ 2 * Phi x ^ 2)) (xi / Real.sqrt c) := by
        exact intervalIntegral.integral_congr fun xi _ => hpt xi
    _ = Real.sqrt c * ∫ x in (-1 : ℝ)..1, c * (x ^ 2 * Phi x ^ 2) :=
        integral_comp_div_sqrt hc (fun x : ℝ => c * (x ^ 2 * Phi x ^ 2))
    _ = Real.sqrt c * (c * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2) := by
        rw [intervalIntegral.integral_const_mul]

/-- **Hermite-scale second-moment bound.**  The rescaled profile's normalized second moment over the
rescaled aperture is at most the oscillator separation constant `c·s`. -/
theorem integral_rescaled_secondMoment_le
    {c chi : ℝ} (hc : 0 < c) {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (heig : ∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Phi x = chi * Phi x) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c), xi ^ 2 * (prolateHermiteRescale c Phi xi) ^ 2)
      ≤ (c * radialSeparationRatio c chi)
        * ∫ xi in (-Real.sqrt c)..(Real.sqrt c), (prolateHermiteRescale c Phi xi) ^ 2 := by
  have hbase := integral_sq_mul_sq_le_separation (ne_of_gt hc) hsm heig
  have hs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [integral_rescaled_secondMoment hc, integral_rescaled_sq hc]
  have hmul : c * (∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2)
      ≤ c * (radialSeparationRatio c chi * ∫ x in (-1 : ℝ)..1, Phi x ^ 2) :=
    mul_le_mul_of_nonneg_left hbase hc.le
  calc Real.sqrt c * (c * ∫ x in (-1 : ℝ)..1, x ^ 2 * Phi x ^ 2)
      ≤ Real.sqrt c * (c * (radialSeparationRatio c chi * ∫ x in (-1 : ℝ)..1, Phi x ^ 2)) :=
        mul_le_mul_of_nonneg_left hmul hs.le
    _ = c * radialSeparationRatio c chi * (Real.sqrt c * ∫ x in (-1 : ℝ)..1, Phi x ^ 2) := by ring

end RHTower
