import GaloisForLFunctions.RHTower.HedenmalmHankelKreinChamber
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.ThetaWignerCenterMix

/-!
# Diagonal-normalized Xi aperture correlation and relative Krein curvature

The positive tilted theta-cusp source gives a canonical unit-diagonal correlation

`C_a(t) = |xi(1/2 + a + i t)|^(2 : ℕ) / xi(1/2 + a)^(2 : ℕ)`.

This module constructs `C_a` from the actual Hedenmalm theta/Xi orbit.  It proves the source
Fourier bound `0 <= C_a(t) <= 1`, constructs its squared Hilbert correlation distance, and
identifies its aperture derivative with one denominator-free relative Krein numerator.  The
normalization removes the scalar horizontal-growth channel and leaves a genuine comparison of
height `t` with the diagonal height zero.

For two apertures the refinement has zero diagonal.  Its two-point determinant is therefore the
negative square of its off-diagonal value, while its three-point determinant is the exact cubic
product.  This is the indefinite signature required by the completed aperture response, rather
than a post-hoc positive Gram factorization.

The final section performs the hostile Hadamard-factor audit.  One on-critical-line zero pair has
a normalized factor whose aperture derivative changes sign on the sharp circle
`a^(2 : ℕ) + t^(2 : ℕ) = 3 * gamma^(2 : ℕ)`.  Thus a global normalized-aperture contraction cannot be proved by
factorwise positivity; any such theorem must use collective infinite theta-source structure.
-/

open Complex Polynomial MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap Convolution ComplexConjugate

namespace RHTower

noncomputable section

theorem norm_fourier_thetaCuspRightLineSource_le_zero
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    ‖FourierTransform.fourier (thetaCuspRightLineSource a ha)
        (b / (2 * Real.pi))‖ ≤
      ‖FourierTransform.fourier (thetaCuspRightLineSource a ha) 0‖ := by
  let f : SchwartzMap ℝ ℂ := thetaCuspRightLineSource a ha
  let g : ℝ → ℝ := fun x => Real.exp (-a * x) * thetaCuspFullSource x
  have hfg (x : ℝ) : f x = (g x : ℂ) := by
    simp [f, g, thetaCuspRightLineSource_apply]
  have hg0 (x : ℝ) : 0 ≤ g x :=
    mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_nonneg x)
  change ‖FourierTransform.fourier (f : ℝ → ℂ) (b / (2 * Real.pi))‖ ≤
    ‖FourierTransform.fourier (f : ℝ → ℂ) 0‖
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  calc
    ‖∫ x : ℝ,
        Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) • f x‖ ≤
        ∫ x : ℝ,
          ‖Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) • f x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, g x := by
      apply integral_congr_ae
      filter_upwards with x
      have hphase :
          ‖Complex.exp (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I)‖ = 1 := by
        simpa using Complex.norm_exp_ofReal_mul_I
          (-2 * Real.pi * x * (b / (2 * Real.pi)))
      rw [norm_smul, hphase, one_mul, hfg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    _ = ‖∫ x : ℝ,
        Complex.exp (↑(-2 * Real.pi * x * 0) * I) • f x‖ := by
      simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
      rw [show (fun x : ℝ => f x) = fun x : ℝ => (g x : ℂ) by
        funext x
        exact hfg x]
      rw [show (∫ x : ℝ, (g x : ℂ)) = ((∫ x : ℝ, g x : ℝ) : ℂ) by
        exact integral_ofReal]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg hg0)]

def xiApertureModulusSq (a t : ℝ) : ℝ :=
  Complex.normSq (thetaXiHankelOrbitValuePlus a t)

def xiApertureKreinSlope (a t : ℝ) : ℝ :=
  hedenmalmHankelKreinForm
    (thetaXiHankelOrbitValuePlus a t)
    (thetaXiHankelOrbitTangentPlus a t)
    (thetaXiHankelOrbitValueMinus a t)
    (thetaXiHankelOrbitTangentMinus a t)

def xiNormalizedApertureCorrelation (a t : ℝ) : ℝ :=
  xiApertureModulusSq a t / xiApertureModulusSq a 0

def xiNormalizedApertureRelativeKreinNumerator (a t : ℝ) : ℝ :=
  xiApertureKreinSlope a t * xiApertureModulusSq a 0 -
    xiApertureModulusSq a t * xiApertureKreinSlope a 0

def xiNormalizedApertureRefinement (a b t : ℝ) : ℝ :=
  xiNormalizedApertureCorrelation a t - xiNormalizedApertureCorrelation b t

def xiNormalizedApertureHilbertDistanceSq (a t : ℝ) : ℝ :=
  2 * (1 - xiNormalizedApertureCorrelation a t)

theorem thetaXiHankelOrbitValuePlus_zero_ne (a : ℝ) :
    thetaXiHankelOrbitValuePlus a 0 ≠ 0 := by
  rw [thetaXiHankelOrbitValuePlus]
  apply XiC_ne_zero_of_abs_re_le_nine_halves
  norm_num

theorem xiApertureModulusSq_zero_pos (a : ℝ) :
    0 < xiApertureModulusSq a 0 := by
  rw [xiApertureModulusSq, Complex.normSq_pos]
  exact thetaXiHankelOrbitValuePlus_zero_ne a

theorem xiNormalizedApertureCorrelation_zero (a : ℝ) :
    xiNormalizedApertureCorrelation a 0 = 1 := by
  rw [xiNormalizedApertureCorrelation]
  exact div_self (xiApertureModulusSq_zero_pos a).ne'

theorem xiApertureModulusSq_neg (a t : ℝ) :
    xiApertureModulusSq a (-t) = xiApertureModulusSq a t := by
  rw [xiApertureModulusSq, xiApertureModulusSq,
    thetaXiHankelOrbitValuePlus_eq_xi,
    thetaXiHankelOrbitValuePlus_eq_xi]
  have harg :
      (1 / 2 : ℂ) + (a : ℂ) + ((-t : ℝ) : ℂ) * I =
        (starRingEnd ℂ) ((1 / 2 : ℂ) + (a : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [harg, xi_conj, Complex.normSq_conj]

theorem xiNormalizedApertureCorrelation_neg (a t : ℝ) :
    xiNormalizedApertureCorrelation a (-t) =
      xiNormalizedApertureCorrelation a t := by
  rw [xiNormalizedApertureCorrelation, xiNormalizedApertureCorrelation,
    xiApertureModulusSq_neg]

theorem xiNormalizedApertureCorrelation_nonneg (a t : ℝ) :
    0 ≤ xiNormalizedApertureCorrelation a t := by
  exact div_nonneg (Complex.normSq_nonneg _)
    (xiApertureModulusSq_zero_pos a).le

theorem norm_thetaXiHankelOrbitValuePlus_le_zero
    {a : ℝ} (ha : |a| < 1) (t : ℝ) :
    ‖thetaXiHankelOrbitValuePlus a t‖ ≤
      ‖thetaXiHankelOrbitValuePlus a 0‖ := by
  rw [thetaXiHankelOrbitValuePlus_eq_xi,
    thetaXiHankelOrbitValuePlus_eq_xi,
    ← fourier_thetaCuspRightLineSource_scaled ha t,
    ← fourier_thetaCuspRightLineSource_scaled ha 0]
  simpa using norm_fourier_thetaCuspRightLineSource_le_zero ha t

theorem xiApertureModulusSq_le_zero
    {a : ℝ} (ha : |a| < 1) (t : ℝ) :
    xiApertureModulusSq a t ≤ xiApertureModulusSq a 0 := by
  rw [xiApertureModulusSq, xiApertureModulusSq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hnorm := norm_thetaXiHankelOrbitValuePlus_le_zero ha t
  nlinarith [norm_nonneg (thetaXiHankelOrbitValuePlus a t),
    norm_nonneg (thetaXiHankelOrbitValuePlus a 0)]

theorem xiNormalizedApertureCorrelation_le_one
    {a : ℝ} (ha : |a| < 1) (t : ℝ) :
    xiNormalizedApertureCorrelation a t ≤ 1 := by
  rw [xiNormalizedApertureCorrelation]
  exact (div_le_one (xiApertureModulusSq_zero_pos a)).mpr
    (xiApertureModulusSq_le_zero ha t)

theorem xiNormalizedApertureHilbertDistanceSq_mem_Icc
    {a : ℝ} (ha : |a| < 1) (t : ℝ) :
    xiNormalizedApertureHilbertDistanceSq a t ∈ Set.Icc 0 2 := by
  constructor
  · rw [xiNormalizedApertureHilbertDistanceSq]
    nlinarith [xiNormalizedApertureCorrelation_le_one ha t]
  · rw [xiNormalizedApertureHilbertDistanceSq]
    nlinarith [xiNormalizedApertureCorrelation_nonneg a t]

theorem xiNormalizedApertureHilbertDistanceSq_zero (a : ℝ) :
    xiNormalizedApertureHilbertDistanceSq a 0 = 0 := by
  rw [xiNormalizedApertureHilbertDistanceSq,
    xiNormalizedApertureCorrelation_zero]
  ring

theorem xiNormalizedApertureCorrelation_le_iff_distance_ge
    (a b t : ℝ) :
    xiNormalizedApertureCorrelation a t ≤
        xiNormalizedApertureCorrelation b t ↔
      xiNormalizedApertureHilbertDistanceSq b t ≤
        xiNormalizedApertureHilbertDistanceSq a t := by
  unfold xiNormalizedApertureHilbertDistanceSq
  constructor <;> intro h <;> linarith

theorem xiNormalizedApertureCorrelation_eq_zero_iff (a t : ℝ) :
    xiNormalizedApertureCorrelation a t = 0 ↔
      thetaXiHankelOrbitValuePlus a t = 0 := by
  rw [xiNormalizedApertureCorrelation, div_eq_zero_iff,
    xiApertureModulusSq, Complex.normSq_eq_zero]
  simp [(xiApertureModulusSq_zero_pos a).ne']

theorem hasDerivAt_xiApertureModulusSq (a t : ℝ) :
    HasDerivAt (fun u : ℝ => xiApertureModulusSq u t)
      (xiApertureKreinSlope a t) a := by
  exact hasDerivAt_thetaXiHankelOrbit_normSq a t

theorem hasDerivAt_xiNormalizedApertureCorrelation (a t : ℝ) :
    HasDerivAt (fun u : ℝ => xiNormalizedApertureCorrelation u t)
      (xiNormalizedApertureRelativeKreinNumerator a t /
        xiApertureModulusSq a 0 ^ (2 : ℕ)) a := by
  have hfun :
      (fun u : ℝ => xiNormalizedApertureCorrelation u t) =
        (fun u : ℝ => xiApertureModulusSq u t) /
          fun u : ℝ => xiApertureModulusSq u 0 := by
    funext u
    rfl
  rw [hfun]
  simpa only [xiNormalizedApertureRelativeKreinNumerator] using!
    (hasDerivAt_xiApertureModulusSq a t).div
      (hasDerivAt_xiApertureModulusSq a 0)
      (xiApertureModulusSq_zero_pos a).ne'

theorem xiNormalizedApertureRefinement_zero (a b : ℝ) :
    xiNormalizedApertureRefinement a b 0 = 0 := by
  simp [xiNormalizedApertureRefinement,
    xiNormalizedApertureCorrelation_zero]

theorem xiNormalizedApertureRefinement_neg (a b t : ℝ) :
    xiNormalizedApertureRefinement a b (-t) =
      xiNormalizedApertureRefinement a b t := by
  rw [xiNormalizedApertureRefinement, xiNormalizedApertureRefinement,
    xiNormalizedApertureCorrelation_neg,
    xiNormalizedApertureCorrelation_neg]

theorem xiNormalizedApertureRefinement_twoPoint_det
    (a b x y : ℝ) :
    xiNormalizedApertureRefinement a b 0 ^ (2 : ℕ) -
        xiNormalizedApertureRefinement a b (x - y) *
          xiNormalizedApertureRefinement a b (y - x) =
      -(xiNormalizedApertureRefinement a b (x - y)) ^ (2 : ℕ) := by
  rw [xiNormalizedApertureRefinement_zero]
  have hneg : y - x = -(x - y) := by ring
  rw [hneg, xiNormalizedApertureRefinement_neg]
  ring

theorem xiNormalizedApertureRefinement_threePoint_det
    (a b x y z : ℝ) :
    xiNormalizedApertureRefinement a b (x - y) *
          xiNormalizedApertureRefinement a b (y - z) *
          xiNormalizedApertureRefinement a b (z - x) +
        xiNormalizedApertureRefinement a b (x - z) *
          xiNormalizedApertureRefinement a b (z - y) *
          xiNormalizedApertureRefinement a b (y - x) =
      2 * xiNormalizedApertureRefinement a b (x - y) *
        xiNormalizedApertureRefinement a b (x - z) *
        xiNormalizedApertureRefinement a b (y - z) := by
  have hzx : z - x = -(x - z) := by ring
  have hzy : z - y = -(y - z) := by ring
  have hyx : y - x = -(x - y) := by ring
  rw [hzx, hzy, hyx,
    xiNormalizedApertureRefinement_neg,
    xiNormalizedApertureRefinement_neg,
    xiNormalizedApertureRefinement_neg]
  ring

def xiOnLineZeroNormalizedFactor (gamma a t : ℝ) : ℝ :=
  (((gamma ^ (2 : ℕ) + a ^ (2 : ℕ) - t ^ (2 : ℕ)) ^ (2 : ℕ) + 4 * a ^ (2 : ℕ) * t ^ (2 : ℕ)) /
    (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (2 : ℕ))

theorem hasDerivAt_xiOnLineZeroNormalizedFactor
    {gamma : ℝ} (hgamma : gamma ≠ 0) (a t : ℝ) :
    HasDerivAt (fun u : ℝ => xiOnLineZeroNormalizedFactor gamma u t)
      (4 * a * t ^ (2 : ℕ) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) /
        (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ)) a := by
  have hden : gamma ^ (2 : ℕ) + a ^ (2 : ℕ) ≠ 0 := by positivity
  have hbase : HasDerivAt (fun u : ℝ => gamma ^ (2 : ℕ) + u ^ (2 : ℕ)) (2 * a) a := by
    simpa using! (hasDerivAt_pow 2 a).const_add (gamma ^ (2 : ℕ))
  have hshift :
      HasDerivAt (fun u : ℝ => gamma ^ (2 : ℕ) + u ^ (2 : ℕ) - t ^ (2 : ℕ)) (2 * a) a := by
    simpa using! hbase.sub_const (t ^ (2 : ℕ))
  have hquadratic : HasDerivAt
      (fun u : ℝ => 4 * u ^ (2 : ℕ) * t ^ (2 : ℕ)) ((4 * t ^ (2 : ℕ)) * (2 * a)) a := by
    have hraw :=
      ((hasDerivAt_pow 2 a).const_mul (4 : ℝ)).mul_const (t ^ (2 : ℕ))
    have hraw' := hraw.congr_deriv
      (g' := (4 * t ^ (2 : ℕ)) * (2 * a)) (by
        norm_num
        ring)
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using! hraw'
  have hnum : HasDerivAt
      (fun u : ℝ =>
        (gamma ^ (2 : ℕ) + u ^ (2 : ℕ) - t ^ (2 : ℕ)) ^ (2 : ℕ) + 4 * u ^ (2 : ℕ) * t ^ (2 : ℕ))
      (2 * (gamma ^ (2 : ℕ) + a ^ (2 : ℕ) - t ^ (2 : ℕ)) * (2 * a) +
        (4 * t ^ (2 : ℕ)) * (2 * a)) a := by
    have hraw := (hshift.pow 2).add hquadratic
    have hraw' := hraw.congr_deriv
      (g' := 2 * (gamma ^ (2 : ℕ) + a ^ (2 : ℕ) - t ^ (2 : ℕ)) * (2 * a) +
        (4 * t ^ (2 : ℕ)) * (2 * a)) (by norm_num)
    simpa only [Pi.add_apply, Pi.pow_apply] using! hraw'
  have hdenDeriv : HasDerivAt
      (fun u : ℝ => (gamma ^ (2 : ℕ) + u ^ (2 : ℕ)) ^ (2 : ℕ))
      (2 * (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) * (2 * a)) a := by
    have hraw := hbase.pow 2
    have hraw' := hraw.congr_deriv
      (g' := 2 * (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) * (2 * a)) (by norm_num)
    simpa only [Pi.pow_apply] using! hraw'
  have hquot := hnum.div hdenDeriv (pow_ne_zero 2 hden)
  have hquot' := hquot.congr_deriv
    (g' := 4 * a * t ^ (2 : ℕ) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) /
      (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ)) (by
        field_simp [hden]
        ring)
  have hfun :
      (fun u : ℝ => xiOnLineZeroNormalizedFactor gamma u t) =
        (fun u : ℝ =>
          (gamma ^ (2 : ℕ) + u ^ (2 : ℕ) - t ^ (2 : ℕ)) ^ (2 : ℕ) + 4 * u ^ (2 : ℕ) * t ^ (2 : ℕ)) /
          fun u : ℝ => (gamma ^ (2 : ℕ) + u ^ (2 : ℕ)) ^ (2 : ℕ) := by
    funext u
    rfl
  rw [hfun]
  exact hquot'

theorem xiOnLineZeroNormalizedFactor_deriv_pos_iff
    {gamma a t : ℝ} (ha : 0 < a) (ht : t ≠ 0) :
    0 < 4 * a * t ^ (2 : ℕ) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) /
        (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ) ↔
      a ^ (2 : ℕ) + t ^ (2 : ℕ) < 3 * gamma ^ (2 : ℕ) := by
  have ht2 : 0 < t ^ (2 : ℕ) := sq_pos_of_ne_zero ht
  have hden : 0 < (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ) := by positivity
  rw [div_pos_iff_of_pos_right hden]
  have hcoef : 0 < 4 * a * t ^ (2 : ℕ) := by positivity
  rw [mul_pos_iff]
  constructor
  · intro h
    rcases h with h | h
    · nlinarith
    · nlinarith
  · intro h
    left
    constructor <;> nlinarith

theorem xiOnLineZeroNormalizedFactor_deriv_neg_iff
    {gamma a t : ℝ} (ha : 0 < a) (ht : t ≠ 0) :
    4 * a * t ^ (2 : ℕ) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) /
        (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ) < 0 ↔
      3 * gamma ^ (2 : ℕ) < a ^ (2 : ℕ) + t ^ (2 : ℕ) := by
  have ht2 : 0 < t ^ (2 : ℕ) := sq_pos_of_ne_zero ht
  have hden : 0 < (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ) := by positivity
  rw [div_lt_iff₀ hden]
  simp only [zero_mul]
  have hcoef : 0 < 4 * a * t ^ (2 : ℕ) := by positivity
  constructor
  · intro hprod
    have hscaled :
        (4 * a * t ^ (2 : ℕ)) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) <
          (4 * a * t ^ (2 : ℕ)) * 0 := by simpa using hprod
    have hlast : 3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ) < 0 :=
      (mul_lt_mul_iff_of_pos_left hcoef).mp hscaled
    nlinarith
  · intro h
    have hlast : 3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ) < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg hcoef hlast

theorem xiOnLineZeroNormalizedFactor_deriv_eq_zero_iff
    {gamma a t : ℝ} (ha : 0 < a) (ht : t ≠ 0) :
    4 * a * t ^ (2 : ℕ) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) /
        (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ) = 0 ↔
      a ^ (2 : ℕ) + t ^ (2 : ℕ) = 3 * gamma ^ (2 : ℕ) := by
  have hden : (gamma ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (3 : ℕ) ≠ 0 := by positivity
  have hcoef : 4 * a * t ^ (2 : ℕ) ≠ 0 := by positivity
  constructor
  · intro hquot
    have hnum :
        4 * a * t ^ (2 : ℕ) * (3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ)) = 0 :=
      (div_eq_zero_iff.mp hquot).resolve_right hden
    have hlast : 3 * gamma ^ (2 : ℕ) - a ^ (2 : ℕ) - t ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp hnum).resolve_left hcoef
    nlinarith
  · intro hcircle
    apply div_eq_zero_iff.mpr
    left
    apply mul_eq_zero_of_right
    nlinarith

end

end RHTower
