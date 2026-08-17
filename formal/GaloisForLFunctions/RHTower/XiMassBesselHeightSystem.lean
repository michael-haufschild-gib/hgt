import GaloisForLFunctions.HTGeometry.BesselK1DerivRecurrence
import GaloisForLFunctions.RHTower.XiMassBesselHeightDerivative

/-!
# The Bessel pair along the height

The mass profile is `2aτ·K₁(aZ)/Z` with `Z(w)² = τ² + w²`, so every height derivative moves inside
the Bessel pair.  Because `(K₀, K₁)` is closed under differentiation with rational coefficients,

`K₀'(ζ) = −K₁(ζ)`,  `K₁'(ζ) = −K₀(ζ) − K₁(ζ)/ζ`,

and `Z'(w) = w/Z`, the pair `(K₀(aZ), K₁(aZ))` satisfies the closed first-order height system

`∂_w K₀(aZ) = −a(w/Z)·K₁(aZ)`,
`∂_w K₁(aZ) = −a(w/Z)·K₀(aZ) − (w/Z²)·K₁(aZ)`.

Every iterated height derivative of the profile is therefore a *rational* combination of
`K₀(aZ)` and `K₁(aZ)`, with coefficients produced by a two-term recursion — no second-order Bessel
equation and no stationary-phase expansion is needed to iterate.
-/

open Complex

namespace RHTower

noncomputable section

/-- The propagation radius as a function of a complex height. -/
def xiMassHeightRadius (τ w : ℂ) : ℂ := HTGeometry.csqrt (τ ^ 2 + w ^ 2)

/-- The order-zero Bessel carrier along the height. -/
def xiMassHeightK0 (a : ℝ) (τ w : ℂ) : ℂ :=
  HTGeometry.besselK0C ((a : ℂ) * xiMassHeightRadius τ w)

/-- The order-one Bessel carrier along the height. -/
def xiMassHeightK1 (a : ℝ) (τ w : ℂ) : ℂ :=
  HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w)

theorem xiMassHeightRadius_ne_zero {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    xiMassHeightRadius τ w ≠ 0 :=
  HTGeometry.csqrt_ne_zero hw

theorem re_mul_xiMassHeightRadius_pos {a : ℝ} {τ w : ℂ} (ha : 0 < a)
    (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    0 < ((a : ℂ) * xiMassHeightRadius τ w).re := by
  have hval : ((a : ℂ) * xiMassHeightRadius τ w).re
      = a * HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
    rw [xiMassHeightRadius, Complex.mul_re, HTGeometry.csqrt_re]
    simp
  rw [hval]
  exact mul_pos ha (HTGeometry.csqrtRe_pos hw)

/-- The height derivative of the propagation radius. -/
theorem hasDerivAt_xiMassHeightRadius {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    HasDerivAt (xiMassHeightRadius τ) (w / xiMassHeightRadius τ w) w := by
  have hzne : HTGeometry.csqrt (τ ^ 2 + w ^ 2) ≠ 0 := HTGeometry.csqrt_ne_zero hw
  have hq : HasDerivAt (fun v : ℂ => τ ^ 2 + v ^ 2) (2 * w) w := by
    have h1 := (hasDerivAt_pow 2 w).const_add (τ ^ 2)
    simpa using h1
  have hz : HasDerivAt (fun v : ℂ => HTGeometry.csqrt (τ ^ 2 + v ^ 2))
      ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)) w := by
    have h1 : HasDerivAt (HTGeometry.csqrt ∘ fun v : ℂ => τ ^ 2 + v ^ 2)
        ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)) w :=
      (HTGeometry.hasStrictDerivAt_csqrt hw).hasDerivAt.comp w hq
    exact h1
  have heq : (2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)
      = w / xiMassHeightRadius τ w := by
    rw [xiMassHeightRadius]
    field_simp
  rw [← heq]
  exact hz

/-- **The order-zero half of the height system.** -/
theorem hasDerivAt_xiMassHeightK0 {a : ℝ} {τ w : ℂ} (ha : 0 < a)
    (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    HasDerivAt (xiMassHeightK0 a τ)
      (-((a : ℂ) * (w / xiMassHeightRadius τ w)) * xiMassHeightK1 a τ w) w := by
  have hre := re_mul_xiMassHeightRadius_pos ha hw
  have hinner : HasDerivAt (fun v : ℂ => (a : ℂ) * xiMassHeightRadius τ v)
      ((a : ℂ) * (w / xiMassHeightRadius τ w)) w :=
    (hasDerivAt_xiMassHeightRadius hw).const_mul _
  have hcomp := (HTGeometry.hasDerivAt_besselK0C hre).comp w hinner
  have hgoal : HasDerivAt (xiMassHeightK0 a τ)
      (-HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w)
        * ((a : ℂ) * (w / xiMassHeightRadius τ w))) w := hcomp
  convert hgoal using 1
  rw [xiMassHeightK1]
  ring

/-- **The order-one half of the height system.** -/
theorem hasDerivAt_xiMassHeightK1 {a : ℝ} {τ w : ℂ} (ha : 0 < a)
    (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    HasDerivAt (xiMassHeightK1 a τ)
      (-((a : ℂ) * (w / xiMassHeightRadius τ w)) * xiMassHeightK0 a τ w
        - (w / xiMassHeightRadius τ w ^ 2) * xiMassHeightK1 a τ w) w := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hre := re_mul_xiMassHeightRadius_pos ha hw
  have hzne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hinner : HasDerivAt (fun v : ℂ => (a : ℂ) * xiMassHeightRadius τ v)
      ((a : ℂ) * (w / xiMassHeightRadius τ w)) w :=
    (hasDerivAt_xiMassHeightRadius hw).const_mul _
  have hcomp := (HTGeometry.hasDerivAt_besselK1C_pair hre).comp w hinner
  have hgoal : HasDerivAt (xiMassHeightK1 a τ)
      (-(HTGeometry.besselK0C ((a : ℂ) * xiMassHeightRadius τ w)
          + HTGeometry.besselK1C ((a : ℂ) * xiMassHeightRadius τ w)
            / ((a : ℂ) * xiMassHeightRadius τ w))
        * ((a : ℂ) * (w / xiMassHeightRadius τ w))) w := hcomp
  convert hgoal using 1
  rw [xiMassHeightK0, xiMassHeightK1]
  field_simp
  ring

end

end RHTower
