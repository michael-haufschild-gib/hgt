import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedThreePositiveOrientationLaw
import GaloisForLFunctions.RHTower.XiRealTransverseShiftDefectDifferentialRank

/-!
# Theta center-mixed orientation and continuum differential rank

The center-mixed theta Fourier current is the unsquared transverse derivative
of the completed Xi energy.  Globally, it is the Xi norm square times twice the
real completed logarithmic derivative.  Thus the sign is a genuine normal
orientation before any divisor scalarization.

Across the full physical aperture interval, the corresponding corrected prime
normal fields have exact pointed-collision differential rank.  No finite
packet of distinct nonzero apertures admits an algebraic differential
compression, while every three-node source Gram matrix is positive
semidefinite.  This file packages those two independent source facts on one
theorem surface.
-/

open Complex Matrix
open scoped UpperEndDifferentialInstances

namespace RHTower

noncomputable section

/-- **Zero-safe normal-orientation identity.** The theta center-mixed current
is the completed Xi energy times twice the real logarithmic normal velocity.
The multiplicative form remains valid at Xi zeros. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_normSq_mul_logDeriv
    {a b : ℝ} (ha : |a| < 1) :
    let z : ℂ := (b : ℂ) - (a : ℂ) * I
    let s : ℂ := (1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I
    thetaCuspCenterMixedFourierCurrent a ha b =
      2 * Complex.normSq (XiC z) * (logDeriv xi s).re := by
  dsimp only
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  let s : ℂ := (1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp [z]
    simpa only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, mul_one, zero_sub, add_zero, abs_neg] using ha
  have hcurrent :
      thetaCuspCenterMixedFourierCurrent a ha b =
        2 * (deriv XiC z * (starRingEnd ℂ) (XiC z)).im := by
    rw [thetaCuspCenterMixedFourierCurrent_eq_tsum_shellPair ha b,
      ← xiCHorizontalCurrent_eq_tsum_thetaCuspShellPairHedenmalmCurrent hz]
    dsimp only [z]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.neg_re, Complex.neg_im, I_re, I_im]
    ring
  have hcoord : (1 : ℂ) / 2 + z * I = s := by
    dsimp [z, s]
    ring_nf
    simp
  rw [hcurrent, deriv_XiC_eq_deriv_xi_mul_I, hcoord]
  have hXi : XiC z = xi s := by
    rw [XiC, hcoord]
  rw [hXi]
  by_cases hs0 : xi s = 0
  · rw [hs0]
    simp [Complex.normSq]
  · rw [logDeriv_apply]
    rw [Complex.div_re, Complex.normSq_apply]
    have hnorm : (xi s).re ^ (2 : ℕ) + (xi s).im ^ (2 : ℕ) ≠ 0 := by
      simpa [Complex.normSq_apply, pow_two] using
        (mt Complex.normSq_eq_zero.mp hs0)
    field_simp [hnorm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, I_re, I_im]
    simp only [s, mul_comm]
    ring

/-- Away from a zero, division exposes the normalized normal velocity
literally. -/
theorem thetaCuspCenterMixedFourierCurrent_div_normSq_eq_logDeriv
    {a b : ℝ} (ha : |a| < 1)
    (hXi : XiC ((b : ℂ) - (a : ℂ) * I) ≠ 0) :
    thetaCuspCenterMixedFourierCurrent a ha b /
        Complex.normSq (XiC ((b : ℂ) - (a : ℂ) * I)) =
      2 * (logDeriv xi
        ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I)).re := by
  rw [thetaCuspCenterMixedFourierCurrent_eq_normSq_mul_logDeriv ha]
  have hnorm :
      Complex.normSq (XiC ((b : ℂ) - (a : ℂ) * I)) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hXi
  field_simp [hnorm]

/-- **Source orientation/rank universality.** At every physical aperture the
center-mixed density is pointwise positive and three-positive.  Simultaneously,
every finite packet of distinct physical apertures has full differential rank
as an actual corrected completed-Xi prime-source family. -/
theorem thetaCusp_centerMixedOrientationRank_universality
    {A : Type*} [Fintype A] [DecidableEq A]
    (aperture : A → ℝ)
    (hpos : ∀ i, 0 < aperture i)
    (hhalf : ∀ i, aperture i < 1 / 2)
    (hinj : Function.Injective aperture) :
    (∀ i t, 0 < thetaCuspCenterMixedDensity (aperture i) t) ∧
    (∀ i (x : Fin 3 → ℝ),
      Matrix.PosSemidef
        (thetaCuspCenterMixedGramThree (aperture i) x)) ∧
    GaloisForLFunctions.DifferentialIndependent
      GaloisForLFunctions.HTGeometry.upperEndRationalCoordinateField
      (fun i =>
        xiRealTransverseShiftUpperEndCarrier (aperture i)) := by
  refine ⟨fun i t =>
      thetaCuspCenterMixedDensity_pos (hpos i) (hhalf i) t,
    fun i x =>
      thetaCuspCenterMixedGramThree_posSemidef
        (hpos i) (hhalf i) x,
    xiPhysicalApertureUpperEndCarrier_differentialIndependent
      aperture hpos hhalf hinj⟩

end

end RHTower
