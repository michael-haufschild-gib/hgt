/-
Mellin reflection at the source cusps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspRadialKernels

/-!
# Mellin reflection at the source cusps

Term-by-term Mellin transformation of the Bessel cusp expansions. The reflected cubic Gamma
ratio, the smoothing kernel `paperKernel` and the completed sum `completedT` give the
reflection of the source cusp with an absolutely convergent dual Dirichlet series.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics

lemma derivative_coefficient_weighted_summable (F : O → ℂ) (A : ℂ)
    (hF : Summable (fun h : O => if h = 0 then (0 : ℝ) else ‖F h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ))) :
    Summable (fun h : O => if h = 0 then (0 : ℝ) else
      ‖A * cuspFrequency h * star (F h)‖ * ‖cuspFrequency h‖ ^ (-5 : ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · rw [mul_zero]
  · have hx := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp : ‖cuspFrequency h‖ * ‖cuspFrequency h‖ ^ (-5 : ℝ) = ‖cuspFrequency h‖ ^ (-4 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one ‖cuspFrequency h‖]
      rw [← Real.rpow_add hx]
      norm_num
    rw [norm_mul, norm_mul, norm_star, ← hp]
    ring

lemma radial_inverse_weight (x : ℝ) (hx : 0 < x) : (x ^ 2) ^ (-3 / 2 : ℝ) / x ^ 2 = x ^ (-5 : ℝ) := by
  calc
    _ = (x ^ 2) ^ (-3 / 2 : ℝ) * (x ^ 2) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; rfl
    _ = (x ^ 2) ^ (-5 / 2 : ℝ) := by
      rw [← Real.rpow_add (sq_pos_of_pos hx)]
      congr 1
      norm_num
    _ = _ := by
      rw [← Real.rpow_natCast_mul hx.le]
      congr 1
      norm_num

lemma radialCoefficient_weighted_summable_of_fourth (F : O → ℂ) (A : ℂ)
    (hF : Summable (fun h : O => if h = 0 then (0 : ℝ) else ‖F h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ))) :
    Summable (fun h : O => if h = 0 then (0 : ℝ) else
      ‖A * cuspFrequency h * star (F h) / ((‖ringComplex h‖ ^ 2 : ℝ) : ℂ)‖ *
        (‖ringComplex h‖ ^ 2) ^ (-3 / 2 : ℝ)) := by
  let D : ℝ := ‖(3 : ℂ) * ringComplex traceLambda‖
  have hD : 0 < D := norm_pos_iff.mpr (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
  have hp : D ^ (-5 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hD _).ne'
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D ^ (-5 : ℝ))).congr
  intro h
  split_ifs with hh
  · rw [mul_zero]
  · have hx := norm_pos_iff.mpr (ringComplex_ne_zero hh)
    have hf : ‖cuspFrequency h‖ = ‖ringComplex h‖ / D := by rw [cuspFrequency, norm_div]
    have hw : D ^ (-5 : ℝ) * (‖ringComplex h‖ / D) ^ (-5 : ℝ) = ‖ringComplex h‖ ^ (-5 : ℝ) := by
      rw [Real.div_rpow hx.le hD.le]
      field_simp [hp]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ = ‖A * cuspFrequency h * star (F h)‖ * (D ^ (-5 : ℝ) * (‖ringComplex h‖ / D) ^ (-5 : ℝ)) := by rw [hf]; ring
      _ = ‖A * cuspFrequency h * star (F h)‖ * ‖ringComplex h‖ ^ (-5 : ℝ) := by rw [hw]
      _ = _ := by rw [← radial_inverse_weight _ hx]; ring

theorem sourceCuspRadialCoefficient_weighted_summable (j : Fin 3) (z : ℂ) :
    Summable (fun h : O => ‖sourceCuspRadialCoefficient j z h‖ *
      sourceCuspRadialLength h ^ (-3 / 2 : ℝ)) := by
  let A : ℂ := (-2 * Real.pi * Complex.I) / (sourceCuspScale j : ℂ) ^ 2
  have hs := radialCoefficient_weighted_summable_of_fourth (sourceCuspCoefficient j) A
    (sourceCuspCoefficient_weighted_summable j)
  apply hs.congr
  intro h
  by_cases hh : h = 0
  · subst h
    simp only [if_true, sourceCuspRadialCoefficient_zero, norm_zero, zero_mul]
  · rw [if_neg hh, sourceCuspRadialCoefficient_norm, sourceCuspRadialBaseCoefficient,
      sourceCuspRadialLength, if_neg hh]
    congr 1
    apply congrArg norm
    dsimp only [A]
    ring

lemma cubic_bessel_mellin_norm_scale (s : ℂ) (r : ℝ) (hr : 0 < r) :
    (∫ v : ℝ in Ioi 0, ‖(v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * r * v)‖) =
      r ^ (-(2 * s.re + 1)) *
        (∫ v : ℝ in Ioi 0, ‖(v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * v)‖) := by
  let g : ℝ → ℝ := fun v => ‖(v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * v)‖
  have he (v : ℝ) (hv : 0 < v) :
      ‖(v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * r * v)‖ =
        r ^ (-(2 * s.re)) * g (r * v) := by
    dsimp only [g]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hr hv)]
    simp only [show (2 * s).re = 2 * s.re by simp]
    rw [Real.mul_rpow hr.le hv.le, show 4 * Real.pi * r * v = 4 * Real.pi * (r * v) by ring]
    have hc : r ^ (-(2 * s.re)) * r ^ (2 * s.re) = 1 := by
      rw [← Real.rpow_add hr]
      simp only [neg_add_cancel, Real.rpow_zero]
    calc
      _ = (r ^ (-(2 * s.re)) * r ^ (2 * s.re)) *
          (v ^ (2 * s.re) * ‖schlafliBesselK (1 / 3) (4 * Real.pi * (r * v))‖) := by rw [hc, one_mul]
      _ = _ := by ring
  calc
    _ = ∫ v : ℝ in Ioi 0, r ^ (-(2 * s.re)) * g (r * v) := setIntegral_congr_fun measurableSet_Ioi he
    _ = r ^ (-(2 * s.re)) * (r⁻¹ * ∫ v : ℝ in Ioi 0, g v) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hr]
      simp only [mul_zero, smul_eq_mul]
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hr]
      congr 2
      ring

lemma weighted_cubic_bessel_integral_norm (s freq a : ℂ) (hf : freq ≠ 0) :
    (∫ v : ℝ in Ioi 0, ‖a * ((v : ℂ) ^ (2 * s) *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖freq‖ * v))‖) =
      (‖a‖ * ‖freq‖ ^ (-(2 * s.re + 1))) *
        (∫ v : ℝ in Ioi 0, ‖(v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * v)‖) := by
  simp only [norm_mul, integral_const_mul]
  have he := cubic_bessel_mellin_norm_scale s ‖freq‖ (norm_pos_iff.mpr hf)
  simp only [norm_mul] at he
  rw [he]
  ring

/-- Absolute integral bounds justify Mellin transformation of the Bessel series term by term. -/
theorem cubic_bessel_series_mellin {ι : Type*} [Countable ι]
    (freq a : ι → ℂ) (hf : ∀ i, freq i ≠ 0) (s : ℂ) (hs : -(1 / 3) < s.re)
    (ha : Summable (fun i => ‖a i‖ * ‖freq i‖ ^ (-(2 * s.re + 1)))) :
    (∫ v : ℝ in Ioi 0, ∑' i, a i * ((v : ℂ) ^ (2 * s) *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖freq i‖ * v))) =
      ∑' i, a i * (((2 : ℂ) ^ (2 * s - 1) * Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)) /
        ((4 * Real.pi * ‖freq i‖ : ℝ) : ℂ) ^ (2 * s + 1)) := by
  have hi (i : ι) := (source_cubic_bessel_mellin_integrable s (freq i) hs (hf i)).const_mul (a i)
  have hsum : Summable (fun i => ∫ v : ℝ in Ioi 0,
      ‖a i * ((v : ℂ) ^ (2 * s) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖freq i‖ * v))‖) := by
    simp only [weighted_cubic_bessel_integral_norm s _ _ (hf _)]
    exact ha.mul_right _
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_congr
  intro i
  rw [integral_const_mul, source_cubic_bessel_mellin s (freq i) hs (hf i)]

lemma positive_sqrt_cpow_twice (r : ℝ) (hr : 0 < r) (s : ℂ) :
    (Real.sqrt r : ℂ) ^ (2 * s + 1) = (r : ℂ) ^ (s + 1 / 2) := by
  have he : (r : ℂ) = (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) := by
    rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  conv_rhs => rw [he, Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg r),
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne')]
  congr 1
  ring

lemma radial_bessel_coefficient_norm (r q σ : ℝ) (hr : 0 < r) (hq : 0 < q) (a : ℂ) :
    ‖a * (r : ℂ)‖ * ‖((q * Real.sqrt r : ℝ) : ℂ)‖ ^ (-(2 * σ + 1)) =
      q ^ (-(2 * σ + 1)) * (‖a‖ * r ^ (1 / 2 - σ)) := by
  rw [norm_mul, Complex.norm_of_nonneg hr.le,
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr hr)).le,
    Real.mul_rpow hq.le (Real.sqrt_nonneg r), Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
  have hp : r * r ^ ((1 / 2) * (-(2 * σ + 1))) = r ^ (1 / 2 - σ) := by
    conv_lhs => lhs; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = q ^ (-(2 * σ + 1)) * (‖a‖ * (r * r ^ ((1 / 2) * (-(2 * σ + 1))))) := by ring
    _ = _ := by rw [hp]

lemma radial_bessel_coefficient_identity (r q : ℝ) (hr : 0 < r) (hq : 0 < q) (a B s : ℂ) :
    (a * (r : ℂ)) * (B / ((q * Real.sqrt r : ℝ) : ℂ) ^ (2 * s + 1)) =
      (B / (q : ℂ) ^ (2 * s + 1)) * (a * (r : ℂ) ^ (1 / 2 - s)) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hq.le (Real.sqrt_nonneg r),
    positive_sqrt_cpow_twice r hr s]
  have hp : (r : ℂ) / (r : ℂ) ^ (s + 1 / 2) = (r : ℂ) ^ (1 / 2 - s) := by
    have he := Complex.cpow_sub (1 : ℂ) (s + 1 / 2) (Complex.ofReal_ne_zero.mpr hr.ne')
    rw [Complex.cpow_one] at he
    simpa only [show (1 : ℂ) - (s + 1 / 2) = 1 / 2 - s by ring] using he.symm
  calc
    _ = (B / (q : ℂ) ^ (2 * s + 1)) * (a * ((r : ℂ) / (r : ℂ) ^ (s + 1 / 2))) := by ring
    _ = _ := by rw [hp]

theorem radialBesselProfile_mellin {ι : Type*} [Countable ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ι → ℂ) (q : ℝ) (hq : 0 < q)
    (s : ℂ) (hs : -(1 / 3) < s.re)
    (ha : Summable (fun i => ‖a i‖ * (r i) ^ (1 / 2 - s.re))) :
    mellin (radialBesselProfile r a q) (2 * s) =
      (((2 : ℂ) ^ (2 * s - 1) * Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)) /
        ((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1)) * (∑' i, a i * (r i : ℂ) ^ (1 / 2 - s)) := by
  let f : ι → ℂ := fun i => ((q * Real.sqrt (r i) : ℝ) : ℂ)
  have hf (i : ι) : f i ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos hq (Real.sqrt_pos.mpr (hr i))).ne'
  have hn (i : ι) : ‖f i‖ = q * Real.sqrt (r i) :=
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
  have has : Summable (fun i => ‖a i * (r i : ℂ)‖ * ‖f i‖ ^ (-(2 * s.re + 1))) := by
    simp only [f, radial_bessel_coefficient_norm _ q s.re (hr _) hq]
    exact ha.mul_left _
  have hid := cubic_bessel_series_mellin f (fun i => a i * (r i : ℂ)) hf s hs has
  calc
    _ = ∫ v : ℝ in Ioi 0, ∑' i, (a i * (r i : ℂ)) * ((v : ℂ) ^ (2 * s) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖f i‖ * v)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only [radialBesselProfile]
      simp only [smul_eq_mul]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro i
      have hp : (v : ℂ) ^ (2 * s - 1) * (v : ℂ) = (v : ℂ) ^ (2 * s) := by
        conv_lhs => rhs; rw [← Complex.cpow_one (v : ℂ)]
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne'), sub_add_cancel]
      rw [hn i, show 4 * Real.pi * q * Real.sqrt (r i) * v = 4 * Real.pi * (q * Real.sqrt (r i)) * v by ring]
      change (v : ℂ) ^ (2 * s - 1) * _ = _
      linear_combination (a i * (r i : ℂ)) * schlafliBesselK (1 / 3) (4 * Real.pi * (q * Real.sqrt (r i)) * v) * hp
    _ = _ := by
      rw [hid, ← tsum_mul_left]
      apply tsum_congr
      intro i
      rw [hn i, show 4 * Real.pi * (q * Real.sqrt (r i)) = (4 * Real.pi * q) * Real.sqrt (r i) by ring]
      exact radial_bessel_coefficient_identity (r i) (4 * Real.pi * q) (hr i) (by positivity) (a i) _ s

/-- The Mellin factor of the cubic radial Bessel kernel. -/
def besselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((2 : ℂ) ^ (2 * s - 1) * Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)) /
    ((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1)

def inverseBesselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1) * (2 : ℂ) ^ (1 - 2 * s) *
    (Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3))⁻¹

lemma inverseBesselMellinFactor_mul (q : ℝ) (hq : 0 < q) (s : ℂ)
    (hs : -(1 / 3) < s.re) :
    inverseBesselMellinFactor q s * besselMellinFactor q s = 1 := by
  have hq0 : (((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s + 1 / 3) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : Complex.Gamma (s + 2 / 3) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hp : (2 : ℂ) ^ (1 - 2 * s) * (2 : ℂ) ^ (2 * s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    simp
  unfold inverseBesselMellinFactor besselMellinFactor
  calc
    _ = ((((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1)) /
          (((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1))) *
        ((2 : ℂ) ^ (1 - 2 * s) * (2 : ℂ) ^ (2 * s - 1)) *
        ((Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3))⁻¹ *
          (Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3))) := by ring
    _ = 1 := by rw [div_self hq0, hp, inv_mul_cancel₀ (mul_ne_zero h1 h2)]; ring

/-- Removing the Bessel factor leaves an entire function whenever the cusp Mellin transform is entire. -/
def continuedBesselDirichlet (F : ℝ → ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q s * mellin F (2 * s)

lemma sourceCuspRadialLength_one_le (h : O) : 1 ≤ sourceCuspRadialLength h := by
  by_cases hh : h = 0
  · simp only [sourceCuspRadialLength, if_pos hh, le_refl]
  · rw [sourceCuspRadialLength, if_neg hh]
    simpa only [Complex.normSq_eq_norm_sq] using one_le_normSq_embedding h hh

theorem sourceCuspRadialCoefficient_summable (j : Fin 3) (z : ℂ) (σ : ℝ) (hσ : 2 ≤ σ) :
    Summable (fun h : O => ‖sourceCuspRadialCoefficient j z h‖ *
      sourceCuspRadialLength h ^ (1 / 2 - σ)) := by
  apply (sourceCuspRadialCoefficient_weighted_summable j z).of_nonneg_of_le
    (fun h => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sourceCuspRadialLength_pos h).le _))
  intro h
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (sourceCuspRadialLength_one_le h) (by linarith)) (norm_nonneg _)

def sourceCuspRadialDirichlet (j : Fin 3) (z s : ℂ) : ℂ :=
  ∑' h : O, sourceCuspRadialCoefficient j z h * (sourceCuspRadialLength h : ℂ) ^ (1 / 2 - s)

/-- The actual cusp expansion, Mellin transformed in its half-plane of absolute convergence. -/
theorem sourceCuspZFamily_mellin (j : Fin 3) (z s : ℂ) (hs : 2 ≤ s.re) :
    mellin (sourceCuspZFamily j z) (2 * s) =
      besselMellinFactor (sourceCuspRadialScale j) s * sourceCuspRadialDirichlet j z s := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have he : mellin (sourceCuspZFamily j z) (2 * s) =
      mellin (radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient j z)
        (sourceCuspRadialScale j)) (2 * s) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [sourceCuspZFamily_eq_radialBesselProfile j z v hv]
  rw [he]
  exact radialBesselProfile_mellin sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient j z) (sourceCuspRadialScale j) (sourceCuspRadialScale_pos j)
    s (by linarith) (sourceCuspRadialCoefficient_summable j z s.re hs)

theorem sourceCuspZFamily_dirichlet (j : Fin 3) (z s : ℂ) (hs : 2 ≤ s.re) :
    continuedBesselDirichlet (sourceCuspZFamily j z) (sourceCuspRadialScale j) s =
      sourceCuspRadialDirichlet j z s := by
  rw [continuedBesselDirichlet, sourceCuspZFamily_mellin j z s hs, ← mul_assoc,
    inverseBesselMellinFactor_mul _ (sourceCuspRadialScale_pos j) s (by linarith), one_mul]

/-- The reflected cubic Gamma ratio; its argument is the Mellin variable of the smoothing kernel. -/
def cubicReflectionGamma (w : ℂ) : ℂ :=
  (Complex.Gamma (7 / 6 + w) * Complex.Gamma (5 / 6 + w)) /
    (Complex.Gamma (7 / 6 - w) * Complex.Gamma (5 / 6 - w))

def besselReflectionFactor (q d : ℝ) (s : ℂ) : ℂ :=
  ((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1) * (2 : ℂ) ^ (2 - 4 * s) /
    ((4 * Real.pi * d : ℝ) : ℂ) ^ (3 - 2 * s)

lemma besselMellinFactor_reflection (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q s * besselMellinFactor d (1 - s) =
      besselReflectionFactor q d s * cubicReflectionGamma (1 / 2 - s) := by
  have hp : (2 : ℂ) ^ (1 - 2 * s) * (2 : ℂ) ^ (1 - 2 * s) = (2 : ℂ) ^ (2 - 4 * s) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor besselReflectionFactor cubicReflectionGamma
  rw [show (2 : ℂ) * (1 - s) - 1 = 1 - 2 * s by ring,
    show (2 : ℂ) * (1 - s) + 1 = 3 - 2 * s by ring,
    show (1 : ℂ) - s + 1 / 3 = 4 / 3 - s by ring,
    show (1 : ℂ) - s + 2 / 3 = 5 / 3 - s by ring,
    show (7 / 6 : ℂ) + (1 / 2 - s) = 5 / 3 - s by ring,
    show (5 / 6 : ℂ) + (1 / 2 - s) = 4 / 3 - s by ring,
    show (7 / 6 : ℂ) - (1 / 2 - s) = s + 2 / 3 by ring,
    show (5 / 6 : ℂ) - (1 / 2 - s) = s + 1 / 3 by ring]
  have he := congrArg (fun x : ℂ =>
    (((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + 1) *
      (Complex.Gamma (s + 1 / 3))⁻¹ * (Complex.Gamma (s + 2 / 3))⁻¹ *
      Complex.Gamma (4 / 3 - s) * Complex.Gamma (5 / 3 - s) *
      (((4 * Real.pi * d : ℝ) : ℂ) ^ (3 - 2 * s))⁻¹) * x) hp
  simp only [div_eq_mul_inv, mul_inv_rev] at he ⊢
  linear_combination he

/-- Reflection of the actual source cusp, with an absolutely convergent dual Dirichlet series. -/
theorem SourceCuspDatum.dirichlet_reflection (d : SourceCuspDatum) (q : ℝ)
    (s : ℂ) (hs : s.re ≤ -1) :
    continuedBesselDirichlet
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point) q s =
      (d.multiplier * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        besselReflectionFactor q (sourceCuspRadialScale d.index) s) *
        cubicReflectionGamma (1 / 2 - s) * sourceCuspRadialDirichlet d.index d.dualPoint (1 - s) := by
  have hs' : 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hm := sourceCuspZFamily_mellin d.index d.dualPoint (1 - s) hs'
  rw [show (2 : ℂ) * (1 - s) = 2 - 2 * s by ring] at hm
  rw [continuedBesselDirichlet, d.mellin_reflection, hm]
  calc
    _ = d.multiplier * (d.heightScale : ℂ) ^ (2 - 2 * s) *
        (inverseBesselMellinFactor q s * besselMellinFactor (sourceCuspRadialScale d.index) (1 - s)) *
        sourceCuspRadialDirichlet d.index d.dualPoint (1 - s) := by ring
    _ = _ := by rw [besselMellinFactor_reflection]; ring

lemma finiteMellin_linearCombination_eq {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (f : ι → ℝ → ℂ) (s : ℂ)
    (hc : ∀ i, MellinConvergent (f i) s) :
    mellin (fun v => ∑ i, weight i * f i v) s = ∑ i, weight i * mellin (f i) s := by
  have hi (i : ι) : Integrable
      (fun v : ℝ => (v : ℂ) ^ (s - 1) * (weight i * f i v))
      (volume.restrict (Set.Ioi 0)) := by
    have hh := (hc i).const_smul (weight i)
    simp only [MellinConvergent, smul_eq_mul, IntegrableOn] at hh
    convert! hh using 1
  unfold mellin
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hmem
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall (fun v => by ring))

/-- Finite arithmetic twists inherit the exact reflection into all three cusp series. -/
theorem traceTwistedBarProfile_dirichlet_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (q : ℝ) (s : ℂ) (hs : s.re ≤ -1) :
    continuedBesselDirichlet (traceTwistedBarProfile c hc φ) q s =
      ∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
        (((finiteTwistCusp c hc h).multiplier *
          ((finiteTwistCusp c hc h).heightScale : ℂ) ^ (2 - 2 * s) *
          besselReflectionFactor q (sourceCuspRadialScale (finiteTwistCusp c hc h).index) s) *
          cubicReflectionGamma (1 / 2 - s) *
          sourceCuspRadialDirichlet (finiteTwistCusp c hc h).index
            (finiteTwistCusp c hc h).dualPoint (1 - s)) := by
  unfold continuedBesselDirichlet traceTwistedBarProfile
  rw [finiteMellin_linearCombination_eq
      (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ)
      (fun h => cuspBarProfile (fun w => star (cubicSourceResidualFunction w))
        (thetaFourierTranslation c h)) (2 * s)
      (fun h => (conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc).1 _),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← mul_assoc, mul_comm (inverseBesselMellinFactor q s), mul_assoc]
  congr 1
  rw [← finiteTwistCusp_point c hc h]
  exact (finiteTwistCusp c hc h).dirichlet_reflection q s hs

lemma rpow_between_endpoints (y a b σ : ℝ) (hy : 0<y) (ha : a ≤ σ) (hb : σ ≤ b) :
    y^σ ≤ y^a+y^b := by
  by_cases h1 : 1 ≤ y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

theorem mellin_uniform_strip_bound (f : ℝ→ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ)) :
    ∃C : ℝ,0 ≤ C ∧ ∀s : ℂ,a ≤ s.re→s.re ≤ b→‖mellin f s‖ ≤ C := by
  let B : ℝ→ℝ := fun y=>‖(y:ℂ)^((a:ℂ)-1)*f y‖+‖(y:ℂ)^((b:ℂ)-1)*f y‖
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact ha.norm.add hb.norm
  refine ⟨∫y in Set.Ioi 0,B y,integral_nonneg (fun y=>add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0<y at hy
  have hp := rpow_between_endpoints y (a-1) (b-1) (s.re-1) hy (by linarith) (by linarith)
  change ‖(y:ℂ)^(s-1)*f y‖ ≤ B y
  dsimp only [B]
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

theorem inverseBesselMellinFactor_differentiable (q : ℝ) (hq : 0<q) :
    Differentiable ℂ (inverseBesselMellinFactor q) := by
  have hq0 : ((4*Real.pi*q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : Differentiable ℂ (fun s : ℂ=>((4*Real.pi*q:ℝ):ℂ)^(2*s+1)) :=
    (show Differentiable ℂ (fun s : ℂ=>2*s+1) from by fun_prop).const_cpow (Or.inl hq0)
  have h2 : Differentiable ℂ (fun s : ℂ=>(2:ℂ)^(1-2*s)) :=
    (show Differentiable ℂ (fun s : ℂ=>1-2*s) from by fun_prop).const_cpow
      (Or.inl (by norm_num : (2:ℂ)≠0))
  have h3 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+1/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have h4 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+2/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  convert! (h1.mul h2).mul (h4.mul h3) using 1
  ext s
  simp only [inverseBesselMellinFactor,Pi.mul_apply,mul_inv_rev]

theorem continuedBesselDirichlet_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) :
    Differentiable ℂ (continuedBesselDirichlet F q) :=
  (inverseBesselMellinFactor_differentiable q hq).mul (hF.comp (by fun_prop))

open scoped ContDiff FourierTransform SchwartzMap

/-! The beta integral bounds the reflected Gamma quotient. Repeated integration by parts
gives uniform Mellin decay for compact smooth tests. -/
lemma Gamma_vertical_conj (a t : ℝ) :
    Complex.Gamma ((a : ℂ) - t * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + t * Complex.I)) := by
  have he : (a : ℂ) - t * Complex.I = star ((a : ℂ) + t * Complex.I) := by
    simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [he]
  exact Complex.Gamma_conj _

def realBeta (a b : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem realBeta_nonneg (a b : ℝ) : 0 ≤ realBeta a b := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤ Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤ Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

open scoped ContDiff FourierTransform SchwartzMap

/-! Mellin inversion and absolute convergence commute the weighted series and vertical integral. -/
open scoped ContDiff FourierTransform SchwartzMap


def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (mellinLogFamily V σ) :=
    (mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=mellinLogFamily V σ := rfl
  simpa only [mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0<r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0<r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0<r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_div_cpow (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  apply (eq_div_iff (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))).mpr
  have he := Complex.mul_cpow_ofReal_nonneg (div_nonneg hx hy.le) hy.le s
  simpa only [← Complex.ofReal_mul, div_mul_cancel₀ x hy.ne'] using he.symm

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0<r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [positive_div_cpow r X hr.le hX,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

def besselSmoothingIntegrand (F : ℝ→ℂ) (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s-1/2)*(X:ℂ)^(s-1/2)*continuedBesselDirichlet F q s

lemma besselSmoothingIntegrand_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) : Differentiable ℂ (besselSmoothingIntegrand F q V X) := by
  have hm := (compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ=>(X:ℂ)^(s-1/2)) :=
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (continuedBesselDirichlet_differentiable F q hq hF)

/-! The reflected Mellin kernel has integrable vertical lines and admits contour shifts. -/
theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem cubicReflectionGamma_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ cubicReflectionGamma s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert! ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [cubicReflectionGamma, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * cubicReflectionGamma t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (cubicReflectionGamma_differentiableAt s hs)

def mellinData (V : ℝ → ℂ) (s : ℂ) : ℂ := mellin V (-s) * cubicReflectionGamma s

def mellinEulerData (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ := (-s) ^ j * mellinData V s

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

def inverseMellinIntegrand (V : ℝ → ℂ) (j : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (-s) * mellinEulerData V j s

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

lemma weighted_vertical_series_continuous {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    Continuous (fun t : ℝ=>∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  apply continuous_tsum
    (fun i=>continuous_const.mul (positive_cpow_negative_vertical_continuous (r i) σ (hr i))) hc
  intro i t
  change ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖ ≤ ‖c i‖*(r i)^(-σ)
  rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]

lemma weighted_vertical_series_norm {α : Type*}
    (r : α→ℝ) (hr : ∀i,0<r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) (t : ℝ) :
    ‖∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖ ≤ ∑'i,‖c i‖*(r i)^(-σ) := by
  have he (i : α) : ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=‖c i‖*(r i)^(-σ) := by
    rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]
  simpa only [he] using norm_tsum_le_tsum_norm (hc.congr (fun i=>(he i).symm))

/-! The cubic scale identifies the reflected inverse Mellin kernel and its weighted series. -/
/-- Scale matching the cubic Gamma-ratio Mellin kernel. -/
def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27

lemma paperScale_pos : 0 < paperScale := by unfold paperScale; positivity

def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun s => mellin V (-s) * cubicReflectionGamma s) (paperScale * x)

lemma positive_nat_pow_cpow (x:ℝ) (hx:0 ≤ x) (n:ℕ) (s:ℂ) :
    ((x^n:ℝ):ℂ)^s=((x:ℂ)^s)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx,
        hn,pow_succ]

lemma positive_reflection_powers (Q u d X r:ℝ)
    (hQ:0<Q) (hu:0<u) (hd:0<d) (hX:0<X) (hr:0<r) (w:ℂ) :
    (Q:ℂ)^(1+2*w)*(u:ℂ)^(2-2*w)*(2:ℂ)^(4*w)/(d:ℂ)^(2+2*w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(u/d)^2:ℝ):ℂ)*((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^(-w) := by
  have hQ0:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hu0:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hu.ne'
  have hd0:(d:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hd.ne'
  have hX0:(X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hX.ne'
  have hr0:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hQp:(Q:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0)
  have hup:(u:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hu0)
  have hdp:(d:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have hXp:(X:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hX0)
  have hrp:(r:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hr0)
  have h2p:(2:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have h16:((16:ℝ):ℂ)^w=((2:ℂ)^w)^4 := by
    have hh:=positive_nat_pow_cpow 2 (by norm_num) 4 w
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hh
    exact hh
  have hy:((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^w=
      (((u:ℂ)^w)^2*((d:ℂ)^w)^2*(X:ℂ)^w*(r:ℂ)^w)/
        (((2:ℂ)^w)^4*((Q:ℂ)^w)^2) := by
    rw [positive_div_cpow _ _ (by positivity) (by positivity)]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hr.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hX.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    rw [positive_nat_pow_cpow u hu.le,positive_nat_pow_cpow d hd.le,
      positive_nat_pow_cpow Q hQ.le,h16]
  rw [Complex.cpow_add _ _ hQ0,Complex.cpow_one,
    Complex.cpow_sub _ _ hu0,Complex.cpow_add _ _ hd0]
  simp only [Complex.cpow_ofNat_mul,Complex.cpow_ofNat]
  rw [Complex.cpow_neg,Complex.cpow_neg,Complex.cpow_neg,hy]
  push_cast
  field_simp

theorem bessel_reflection_scale (q d Q X r:ℝ)
    (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X) (hr:0<r) (w:ℂ) :
    (Q:ℂ)^(2-2*(1/2-w))*besselReflectionFactor q d (1/2-w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(q/d)^2:ℝ):ℂ)*
        ((paperScale*(27*q^2*d^2*X*r/Q^2):ℝ):ℂ)^(-w) := by
  have he:=positive_reflection_powers Q (4*Real.pi*q) (4*Real.pi*d) X r
    hQ (by positivity) (by positivity) hX hr w
  have hp:Q*((4*Real.pi*q)/(4*Real.pi*d))^2=Q*(q/d)^2 := by
    field_simp
  have hy:(4*Real.pi*q)^2*(4*Real.pi*d)^2*X*r/(16*Q^2)=
      paperScale*(27*q^2*d^2*X*r/Q^2) := by
    unfold paperScale
    ring
  rw [hp,hy] at he
  unfold besselReflectionFactor
  convert he using 1 ; congr 2 ; ring_nf

/-! The initial source series uses the conjugate horizontal frequency. Its norm is unchanged. -/
/-- Changing Wirtinger derivative only rotates each nonzero Fourier coefficient. -/
def sourceBarRadialCoefficient (z : ℂ) (h : O) : ℂ :=
  (star (cuspFrequency h) / cuspFrequency h) * sourceCuspRadialCoefficient 0 z h

lemma sourceBarRadialCoefficient_norm (z : ℂ) (h : O) :
    ‖sourceBarRadialCoefficient z h‖ = ‖sourceCuspRadialCoefficient 0 z h‖ := by
  by_cases hh : h = 0
  · subst h
    simp only [sourceBarRadialCoefficient, sourceCuspRadialCoefficient_zero, mul_zero]
  · rw [sourceBarRadialCoefficient, norm_mul, norm_div, norm_star,
      div_self (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh)), one_mul]

lemma sourceZBesselTerm_eq_rotated (z : ℂ) (v : ℝ) (h : O) :
    star (cubicBesselTerm sourceZBesselCoefficient h (v, z)) =
      (star (cuspFrequency h) / cuspFrequency h) * sourceCuspZTerm 0 z v h := by
  by_cases hh : h = 0
  · subst h
    simp only [sourceCuspZTerm_zero, mul_zero, cubicBesselTerm, cubicBesselAmplitude,
      if_true, zero_mul, star_zero]
  · have hc : star (sourceZBesselCoefficient h) =
        (star (cuspFrequency h) / cuspFrequency h) * star (sourceBarBesselCoefficient h) := by
      simp only [sourceZBesselCoefficient, sourceBarBesselCoefficient, star_mul, star_star]
      field_simp [cuspFrequency_ne_zero h hh]
    simp only [sourceCuspZTerm, sourceCuspBarCoefficient, sourceCuspScale,
      Matrix.cons_val_zero, div_one, Complex.ofReal_one]
    simp only [cubicBesselTerm, cubicBesselAmplitude, if_neg hh, star_mul]
    rw [hc]
    ring

lemma sourceBarProfile_eq_radial (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z v =
      radialBesselProfile sourceCuspRadialLength (sourceBarRadialCoefficient z)
        (sourceCuspRadialScale 0) v := by
  rw [conjugateSource_barProfile z v hv, cuspZProfile_positive _ _ _ hv,
    cubicSource_wirtingerZ_bessel v hv z, tsum_star]
  unfold radialBesselProfile
  apply tsum_congr
  intro h
  rw [sourceZBesselTerm_eq_rotated, sourceCuspZTerm_eq_radial 0 z v hv h]
  unfold sourceBarRadialCoefficient
  ring

lemma sourceBarRadialCoefficient_summable (z : ℂ) (σ : ℝ) (hσ : 2 ≤ σ) :
    Summable (fun h : O => ‖sourceBarRadialCoefficient z h‖ *
      sourceCuspRadialLength h ^ (1 / 2 - σ)) := by
  simp only [sourceBarRadialCoefficient_norm]
  exact sourceCuspRadialCoefficient_summable 0 z σ hσ

def sourceBarRadialDirichlet (z s : ℂ) : ℂ :=
  ∑' h : O, sourceBarRadialCoefficient z h * (sourceCuspRadialLength h : ℂ) ^ (1 / 2 - s)

theorem sourceBarProfile_mellin (z s : ℂ) (hs : 2 ≤ s.re) :
    mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z) (2 * s) =
      besselMellinFactor (sourceCuspRadialScale 0) s * sourceBarRadialDirichlet z s := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have he : mellin (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z) (2 * s) =
      mellin (radialBesselProfile sourceCuspRadialLength (sourceBarRadialCoefficient z)
        (sourceCuspRadialScale 0)) (2 * s) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [sourceBarProfile_eq_radial z v hv]
  rw [he]
  exact radialBesselProfile_mellin sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceBarRadialCoefficient z) (sourceCuspRadialScale 0) (sourceCuspRadialScale_pos 0)
    s (by linarith) (sourceBarRadialCoefficient_summable z s.re hs)

theorem sourceBarProfile_dirichlet (z s : ℂ) (hs : 2 ≤ s.re) :
    continuedBesselDirichlet (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z)
      (sourceCuspRadialScale 0) s = sourceBarRadialDirichlet z s := by
  rw [continuedBesselDirichlet, sourceBarProfile_mellin z s hs, ← mul_assoc,
    inverseBesselMellinFactor_mul _ (sourceCuspRadialScale_pos 0) s (by linarith), one_mul]

/-- The dual radial scale determined by a rational cusp. -/
def SourceCuspDatum.smoothingScale (d : SourceCuspDatum) (X : ℝ) : ℝ :=
  27 * (sourceCuspRadialScale 0) ^ 2 * (sourceCuspRadialScale d.index) ^ 2 * X / d.heightScale ^ 2

def SourceCuspDatum.smoothingMultiplier (d : SourceCuspDatum) : ℂ :=
  d.multiplier * ((d.heightScale * (sourceCuspRadialScale 0 / sourceCuspRadialScale d.index) ^ 2 : ℝ) : ℂ)

lemma SourceCuspDatum.smoothingScale_pos (d : SourceCuspDatum) (X : ℝ) (hX : 0 < X) :
    0 < d.smoothingScale X := by
  unfold SourceCuspDatum.smoothingScale
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num)
    (sq_pos_of_pos (sourceCuspRadialScale_pos 0)))
    (sq_pos_of_pos (sourceCuspRadialScale_pos d.index))) hX) (sq_pos_of_pos d.heightScale_pos)

lemma SourceCuspDatum.smoothing_reflected_line (d : SourceCuspDatum)
    (V : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (t : ℝ) :
    besselSmoothingIntegrand
      (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point)
      (sourceCuspRadialScale 0) V X ((-1 : ℂ) + (-t) * Complex.I) =
      d.smoothingMultiplier *
        ((∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
          (sourceCuspRadialLength h : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) *
          (((paperScale * d.smoothingScale X : ℝ) : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I)) *
            mellinEulerData V 0 ((3 / 2 : ℂ) + t * Complex.I))) := by
  let s : ℂ := (-1 : ℂ) + (-t) * Complex.I
  let w : ℂ := (3 / 2 : ℂ) + t * Complex.I
  have hw : 1 / 2 - s = w := by dsimp [s, w]; ring
  have hsw : s - 1 / 2 = -w := by dsimp [s, w]; ring
  have hws : 1 / 2 - w = s := by dsimp [s, w]; ring
  have hp := bessel_reflection_scale (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index)
    d.heightScale X 1 (sourceCuspRadialScale_pos 0) (sourceCuspRadialScale_pos d.index)
    d.heightScale_pos hX (by norm_num) w
  simp only [hws, Complex.ofReal_one, Complex.one_cpow, mul_one] at hp
  have hd : sourceCuspRadialDirichlet d.index d.dualPoint (1 - s) =
      ∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
        (sourceCuspRadialLength h : ℂ) ^ (-w) := by
    unfold sourceCuspRadialDirichlet
    rw [show (1 / 2 : ℂ) - (1 - s) = -w by rw [← hsw]; ring]
  change besselSmoothingIntegrand _ _ V X s = _
  rw [besselSmoothingIntegrand, d.dirichlet_reflection _ s (by dsimp [s]; norm_num), hw, hsw, hd]
  change _ = d.smoothingMultiplier *
    ((∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
      (sourceCuspRadialLength h : ℂ) ^ (-w)) *
      (((paperScale * d.smoothingScale X : ℝ) : ℂ) ^ (-w) * mellinEulerData V 0 w))
  rw [mellinEulerData, pow_zero, one_mul, mellinData]
  calc
    _ = (d.multiplier * mellin V (-w) * cubicReflectionGamma w *
          (∑' h : O, sourceCuspRadialCoefficient d.index d.dualPoint h *
            (sourceCuspRadialLength h : ℂ) ^ (-w))) *
        ((d.heightScale : ℂ) ^ (2 - 2 * s) *
          besselReflectionFactor (sourceCuspRadialScale 0) (sourceCuspRadialScale d.index) s *
          (X : ℂ) ^ (-w)) := by ring
    _ = _ := by
      rw [hp]
      unfold SourceCuspDatum.smoothingMultiplier SourceCuspDatum.smoothingScale
      ring

lemma weighted_vertical_sum_mul_integrable {α : Type*}
    (r : α → ℝ) (hr : ∀ i, 0 < r i) (a : α → ℂ) (σ : ℝ)
    (ha : Summable (fun i => ‖a i‖ * (r i) ^ (-σ)))
    (M : ℝ → ℂ) (hM : Integrable M) :
    Integrable (fun t : ℝ => (∑' i, a i * (r i : ℂ) ^ (-((σ : ℂ) + t * Complex.I))) * M t) := by
  have hD := weighted_vertical_series_continuous r hr a σ ha
  have hDb := weighted_vertical_series_norm r hr a σ ha
  simpa only [mul_comm] using hM.mul_bdd hD.aestronglyMeasurable (Eventually.of_forall hDb)

lemma sourceBar_smoothing_initial_line (z : ℂ) (V : ℝ → ℂ) (X : ℝ) (t : ℝ) :
    besselSmoothingIntegrand (cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) z)
      (sourceCuspRadialScale 0) V X ((2 : ℂ) + t * Complex.I) =
      mellin V ((3 / 2 : ℂ) + t * Complex.I) * (X : ℂ) ^ ((3 / 2 : ℂ) + t * Complex.I) *
        (∑' h : O, sourceBarRadialCoefficient z h *
          (sourceCuspRadialLength h : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) := by
  rw [besselSmoothingIntegrand, sourceBarProfile_dirichlet z _ (by norm_num), sourceBarRadialDirichlet]
  rw [show (2 : ℂ) + t * Complex.I - 1 / 2 = 3 / 2 + t * Complex.I by ring,
    show (1 / 2 : ℂ) - (2 + t * Complex.I) = -(3 / 2 + t * Complex.I) by ring]

lemma compactMellin_power_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖V x‖ ≤ C * x ^ (-σ) := by
  let C : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖ *
    ∫ t : ℝ, ‖mellin V ((σ : ℂ) + t * Complex.I)‖
  refine ⟨C, mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro x hx
  rw [compactMellin_inversion V a b ha hVs hV σ x hx, norm_mul]
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ∫ t : ℝ, ‖(x : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
          mellin V ((σ : ℂ) + t * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = C * x ^ (-σ) := by
      simp only [norm_mul, positive_cpow_negative_vertical_norm x σ _ hx, integral_const_mul]
      dsimp only [C]
      ring

lemma weighted_compact_test_norm_summable {α : Type*}
    (r : α → ℝ) (hr : ∀ i, 0 < r i) (c : α → ℂ) (σ : ℝ)
    (hc : Summable (fun i => ‖c i‖ * (r i) ^ (-σ)))
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) : Summable (fun i => ‖c i * V (r i / X)‖) := by
  obtain ⟨C, hC, hb⟩ := compactMellin_power_bound V a b ha hVs hV σ
  apply (hc.mul_left (C / X ^ (-σ))).of_nonneg_of_le (fun i => norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _ ≤ ‖c i‖ * (C * (r i / X) ^ (-σ)) :=
      mul_le_mul_of_nonneg_left (hb _ (div_pos (hr i) hX)) (norm_nonneg _)
    _ = _ := by rw [Real.div_rpow (hr i).le hX.le]; ring

lemma sourceBarRadialCoefficient_phase (z : ℂ) (h : O) :
    sourceBarRadialCoefficient z h =
      sourceBarRadialCoefficient 0 h * tracePhase (-cuspFrequency h * z) := by
  simp only [sourceBarRadialCoefficient, sourceCuspRadialCoefficient, sourceCuspScale,
    Matrix.cons_val_zero, Complex.ofReal_one, div_one, mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring

lemma sourceBarRadialCoefficient_at_zero (h : O) :
    sourceBarRadialCoefficient 0 h = star (rationalSourceResidualFourierCoefficient h) *
      ((-2 * Real.pi * Complex.I * star (cuspFrequency h)) / (sourceCuspRadialLength h : ℂ)) := by
  by_cases hh : h = 0
  · subst h
    simp only [sourceBarRadialCoefficient, sourceCuspRadialCoefficient_zero, mul_zero,
      cuspFrequency, map_zero, zero_div, star_zero, zero_mul]
  · simp only [sourceBarRadialCoefficient, sourceCuspRadialCoefficient, sourceCuspRadialBaseCoefficient,
      sourceCuspCoefficient, sourceCuspScale, Matrix.cons_val_zero, Complex.ofReal_one,
      one_pow, one_mul, div_one, mul_zero, AddChar.map_zero_eq_one, mul_one]
    field_simp [cuspFrequency_ne_zero h hh]
    <;> ring

lemma sourceBar_smoothed_finite_translation (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (W : O → ℂ) (hW : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h * W h‖)) :
    (∑ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ i *
      ∑' h : O, sourceBarRadialCoefficient (thetaFourierTranslation c i) h * W h) =
      ∑' h : O, φ (Ideal.Quotient.mk _ h) * sourceBarRadialCoefficient 0 h * W h := by
  let coeff : O → ℂ := fun h => star (sourceBarRadialCoefficient 0 h * W h)
  have hs : Summable (fun h => ‖coeff h‖) := by simpa only [coeff, norm_star] using hW
  have he := conjugate_cuspCharacterSeries_finite_translation coeff hs
    (thetaFourierTranslation c) (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ) 0
  simp only [zero_add, thetaFourierTranslation_inversion c hc, mul_zero,
    AddChar.map_zero_eq_one, mul_one, coeff, star_star] at he
  calc
    _ = ∑ i, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ i *
        star (cuspCharacterSeries coeff (thetaFourierTranslation c i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [conjugate_cuspCharacterSeries]
      apply tsum_congr
      intro h
      rw [sourceBarRadialCoefficient_phase]
      simp only [coeff, star_star]
      ring
    _ = _ := by simpa only [mul_assoc] using he

/-- The smoothed squarefree-times-cube cubic Gauss sum, with its horizontal derivative weight. -/
def thetaSmoothedGaussSum (Ψ : O →* ℂ) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : ThetaPrimaryCubePair,
    ((‖ringComplex (primaryIdealGenerator p.2.val)‖ : ℂ) *
      normalizedCubicUnitGauss (primaryIdealGenerator p.1.val) *
      Ψ (primaryIdealGenerator p.1.val) * (Ψ (primaryIdealGenerator p.2.val)) ^ 3) *
      (((-2 * Real.pi * Complex.I * star (cuspFrequency
        (primaryIdealGenerator p.1.val * (primaryIdealGenerator p.2.val) ^ 3))) /
        (sourceCuspRadialLength (primaryIdealGenerator p.1.val *
          (primaryIdealGenerator p.2.val) ^ 3) : ℂ)) *
        V (sourceCuspRadialLength (primaryIdealGenerator p.1.val *
          (primaryIdealGenerator p.2.val) ^ 3) / X))

lemma sourceCuspRadialScale_ratio (j : Fin 3) :
    sourceCuspRadialScale 0 / sourceCuspRadialScale j = sourceCuspScale j := by
  have h0 : sourceCuspRadialScale 0 = thetaBesselScale := by
    simp only [sourceCuspRadialScale, sourceCuspScale, Matrix.cons_val_zero, div_one]
  rw [h0, sourceCuspRadialScale]
  field_simp [thetaBesselScale_pos.ne']

/-- The cusp denominator cancels from the reflected amplitude. -/
lemma SourceCuspDatum.smoothingMultiplier_norm (d : SourceCuspDatum) :
    ‖d.smoothingMultiplier‖ = (sourceCuspScale d.index) ^ 2 := by
  rw [SourceCuspDatum.smoothingMultiplier, sourceCuspRadialScale_ratio,
    norm_mul, d.multiplier_norm, Complex.norm_of_nonneg
      (mul_nonneg d.heightScale_pos.le (sq_nonneg _)), ← mul_assoc,
    inv_mul_cancel₀ d.heightScale_pos.ne', one_mul]

lemma SourceCuspDatum.smoothingMultiplier_norm_le (d : SourceCuspDatum) :
    ‖d.smoothingMultiplier‖ ≤ 9 := by
  rw [d.smoothingMultiplier_norm]
  rcases d with ⟨G, j, hj⟩
  fin_cases j <;> norm_num [sourceCuspScale]

/-- The square-root weight converting the radial derivative into the completed Gauss sum. -/
def Vstar (W : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * W y

lemma Vstar_support (W : ℝ → ℂ) (a b : ℝ)
    (hW : Function.support W ⊆ Set.Icc a b) : Function.support (Vstar W) ⊆ Set.Icc a b := by
  intro x hx
  apply hW
  intro hz
  exact hx (by simp only [Vstar, hz, mul_zero])

lemma Vstar_contDiff (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Vstar W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : Vstar W =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y = 0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp only [Vstar, hw, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_sqrt hx)).mul hW.contDiffAt

def thetaRadialDerivativeScalar : ℂ := (-2 * Real.pi * Complex.I) * star thetaFrequencyScale

def thetaDerivativeScalar : ℂ := thetaRadialDerivativeScalar * rationalSourceThetaScalar

lemma thetaRadialDerivativeScalar_ne_zero : thetaRadialDerivativeScalar ≠ 0 := by
  unfold thetaRadialDerivativeScalar
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (star_ne_zero.mpr (norm_pos_iff.mp thetaBesselScale_pos))

lemma thetaDerivativeScalar_ne_zero : thetaDerivativeScalar ≠ 0 :=
  mul_ne_zero thetaRadialDerivativeScalar_ne_zero rationalSourceThetaScalar_ne_zero

lemma sourceBarRadialWeight_eq_div (h : O) (hh : h ≠ 0) :
    (-2 * Real.pi * Complex.I * star (cuspFrequency h)) / (sourceCuspRadialLength h : ℂ) =
      thetaRadialDerivativeScalar / ringComplex h := by
  have hq := ringComplex_ne_zero hh
  have hn : ((‖ringComplex h‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hq))
  have hnorm : star (ringComplex h) * ringComplex h = ((‖ringComplex h‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' (ringComplex h)
  rw [sourceCuspRadialLength, if_neg hh, cuspFrequency_eq_thetaFrequencyScale, star_mul]
  apply (div_eq_div_iff hn hq).mpr
  calc
    _ = thetaRadialDerivativeScalar * (star (ringComplex h) * ringComplex h) := by
      unfold thetaRadialDerivativeScalar
      ring
    _ = _ := by rw [hnorm]

/-- The squarefree and cube coefficients, with the angular factor retained. -/
def completedMellinCoefficient (Ψ : O →* ℂ) (p : ThetaPrimaryCubePair) : ℂ :=
  ((‖ringComplex (primaryIdealGenerator p.2.val)‖ : ℂ) *
    normalizedCubicUnitGauss (primaryIdealGenerator p.1.val) *
    Ψ (primaryIdealGenerator p.1.val) * Ψ (primaryIdealGenerator p.2.val) ^ 3) /
      ringComplex (primaryIdealGenerator p.1.val * primaryIdealGenerator p.2.val ^ 3)

def completedMellinLength (p : ThetaPrimaryCubePair) : ℝ :=
  sourceCuspRadialLength (primaryIdealGenerator p.1.val * primaryIdealGenerator p.2.val ^ 3)

def completedT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : ThetaPrimaryCubePair, completedMellinCoefficient Ψ p * Vstar W (completedMellinLength p / X)

lemma thetaSmoothedGaussSum_eq_completedT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    thetaSmoothedGaussSum Ψ (Vstar W) X = thetaRadialDerivativeScalar * completedT Ψ W X := by
  rw [thetaSmoothedGaussSum, completedT, ← tsum_mul_left]
  apply tsum_congr
  intro p
  dsimp only [thetaSmoothedGaussSum, completedMellinCoefficient, completedMellinLength]
  rw [sourceBarRadialWeight_eq_div _ (mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property))]
  ring

/-- Absolute radial mass is independent of the horizontal cusp coordinate. -/
def sourceCuspRadialMass (j : Fin 3) : ℝ :=
  ∑' h : O, ‖sourceCuspRadialCoefficient j 0 h‖ * sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))

lemma sourceCuspRadialMass_nonneg (j : Fin 3) : 0 ≤ sourceCuspRadialMass j :=
  tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (sourceCuspRadialLength_pos h).le _))

theorem sourceCuspRadialMass_sum (j : Fin 3) (z : ℂ) :
    (∑' h : O, ‖sourceCuspRadialCoefficient j z h‖ * sourceCuspRadialLength h ^ (-(3 / 2 : ℝ))) =
      sourceCuspRadialMass j := by
  unfold sourceCuspRadialMass
  simp only [sourceCuspRadialCoefficient_norm]

/-- An integral primitive cusp column divides every denominator representing its point. -/
lemma SourceCuspDatum.heightScale_le_of_point (d : SourceCuspDatum) (a c : O) (hc : c ≠ 0)
    (hp : d.point = ringComplex a / ringComplex c) : d.heightScale ≤ ‖ringComplex c‖ ^ 2 := by
  let M : SL(2, O) := (d.gamma : SL(2, O)) * cuspRepresentative d.index
  have hM : integralComplexMatrix M = d.matrix := by
    dsimp only [M, SourceCuspDatum.matrix]
    exact map_mul integralComplexMatrix _ _
  have he (i j : Fin 2) : ringComplex (M i j) = d.matrix i j := by
    exact congrArg (fun A : SL(2, ℂ) => A i j) hM
  have hp' : M 0 0 * c = a * M 1 0 := by
    apply ringComplex_injective
    have hpC : d.matrix 0 0 * ringComplex c = ringComplex a * d.matrix 1 0 :=
      (div_eq_div_iff (show d.matrix 1 0 ≠ 0 from d.lower_ne_zero)
        (ringComplex_ne_zero hc)).mp hp
    simpa only [map_mul, he] using hpC
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  let k : O := a * M 1 1 - M 0 1 * c
  have hk : M 1 0 * k = c := by
    calc
      _ = (a * M 1 0) * M 1 1 - M 0 1 * M 1 0 * c := by dsimp [k]; ring
      _ = (M 0 0 * M 1 1 - M 0 1 * M 1 0) * c := by rw [← hp']; ring
      _ = c := by rw [hd, one_mul]
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hk
    exact hc hk.symm
  have hk1 : 1 ≤ ‖ringComplex k‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq] using one_le_normSq_embedding k hk0
  have hn : ‖ringComplex c‖ ^ 2 = ‖d.matrix 1 0‖ ^ 2 * ‖ringComplex k‖ ^ 2 := by
    rw [← hk, map_mul, norm_mul, mul_pow, he]
  change ‖d.matrix 1 0‖ ^ 2 ≤ _
  rw [hn]
  exact le_mul_of_one_le_right (sq_nonneg _) hk1

lemma finiteTwistCusp_heightScale_le (c : O) (hc : c ≠ 0) (h : O ⧸ Ideal.span {c}) :
    (finiteTwistCusp c hc h).heightScale ≤ ‖ringComplex c‖ ^ 2 := by
  apply SourceCuspDatum.heightScale_le_of_point _ (-3 * Quotient.out h) c hc
  exact rationalSourceCusp_point _ _ hc

lemma finiteThetaTwist_norm_le_one (c : O) (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (hΨ : ∀ x, ‖Ψ x‖ ≤ 1) (x : O ⧸ Ideal.span {9 * c}) : ‖finiteThetaTwist c Ψ x‖ ≤ 1 := by
  rw [finiteThetaTwist, fixedThetaTwist_norm]
  split_ifs
  · exact hΨ _
  · norm_num

lemma finiteAdditiveFourierCoeff_norm_le_one {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) (h : R) :
    ‖finiteAdditiveFourierCoeff ψ φ h‖ ≤ 1 := by
  apply (finiteAdditiveFourierCoeff_norm_le ψ φ h).trans
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul] using
    Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hφ x)

/-- The smallest of the three cusp scales, before division by the cusp denominator. -/
def sourceReflectionScale : ℝ := 3 * thetaBesselScale ^ 4

lemma sourceReflectionScale_pos : 0 < sourceReflectionScale :=
  mul_pos (by norm_num) (pow_pos thetaBesselScale_pos 4)

lemma SourceCuspDatum.smoothingScale_lower (d : SourceCuspDatum) (a c : O) (hc : c ≠ 0)
    (hp : d.point = ringComplex a / ringComplex c) (X : ℝ) (hX : 0 < X) :
    sourceReflectionScale * X / ‖ringComplex c‖ ^ 4 ≤ d.smoothingScale X := by
  have hQ := d.heightScale_le_of_point a c hc hp
  have hQ2 : d.heightScale ^ 2 ≤ ‖ringComplex c‖ ^ 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr hQ)
      (add_nonneg (sq_nonneg ‖ringComplex c‖) d.heightScale_pos.le)
    nlinarith only [hp]
  have hj : sourceReflectionScale ≤
      27 * sourceCuspRadialScale 0 ^ 2 * sourceCuspRadialScale d.index ^ 2 := by
    rcases d with ⟨G, j, hj⟩
    fin_cases j <;> dsimp [sourceReflectionScale, sourceCuspRadialScale, sourceCuspScale] <;>
      nlinarith only [sq_nonneg (thetaBesselScale ^ 2)]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hc)) 4)).mpr
  calc
    _ ≤ (27 * sourceCuspRadialScale 0 ^ 2 * sourceCuspRadialScale d.index ^ 2) * X :=
      mul_le_mul_of_nonneg_right hj hX.le
    _ = d.smoothingScale X * d.heightScale ^ 2 := by
      rw [SourceCuspDatum.smoothingScale, div_mul_cancel₀ _ (pow_ne_zero 2 d.heightScale_pos.ne')]
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ2 (d.smoothingScale_pos X hX).le

lemma unramifiedResidualCoefficient_prime_normalized (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    unramifiedResidualCoefficient (h * p) = ringComplex (symbol h p) *
      star (normalizedCubicUnitGauss p) * unramifiedResidualCoefficient h := by
  have hp1 : ¬ p ∣ (1 : O) := fun hd => hp.2.1 (isUnit_of_dvd_one hd)
  rw [unramifiedResidualCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary h hph, primeCubicGauss_two_eq_star p hp hprimary 1 hp1,
    normalizedCubicUnitGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The normalized unramified coefficient retains the cubic symbol of its base frequency. -/
theorem unramifiedResidualCoefficient_prime_product {ι : Type*}
    (s : Finset ι) (p : ι → O) (hp : ∀ i ∈ s, Prime (p i))
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (p i) (p j))
    (h : O) (hph : ∀ i ∈ s, ¬ p i ∣ h) :
    unramifiedResidualCoefficient (h * (∏ i ∈ s, p i)) =
      ringComplex (symbol h (∏ i ∈ s, p i)) * star (normalizedCubicUnitGauss (∏ i ∈ s, p i)) *
        unramifiedResidualCoefficient h := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one, symbol_one, map_one, normalizedCubicUnitGauss_one, star_one, one_mul]
  | @insert i s hi ih =>
    have hpi := hp i (Finset.mem_insert_self _ _)
    have hpri := hprimary i (Finset.mem_insert_self _ _)
    have hps : ∀ j ∈ s, Prime (p j) := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hprs : ∀ j ∈ s, lambda ^ 2 ∣ p j - 1 := fun j hj => hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi : IsCoprime (p i) (∏ j ∈ s, p j) := IsCoprime.prod_right (fun j hj =>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact hi hj))
    have hbs : (∏ j ∈ s, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j hj => (hps j hj).ne_zero)
    have hpb : ¬ p i ∣ h * (∏ j ∈ s, p j) := by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd | hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.2.1 (hcpi.isUnit_of_dvd hd)
    have hih := ih hps hprs
      (fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj => hph j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, show h * (p i * (∏ j ∈ s, p j)) = (h * (∏ j ∈ s, p j)) * p i by ring,
      unramifiedResidualCoefficient_prime_normalized (p i) hpi hpri _ hpb, hih]
    rw [mul_comm (p i) (∏ j ∈ s, p j), normalizedCubicUnitGauss_coprime_product _ _ hbs hpi.ne_zero
      (primary_finset_product s p hprs) hpri hcpi.symm, symbol_mul_denominator, map_mul,
      symbol_mul_numerator, map_mul]
    ring

lemma ramified_primaryPrime_not_dvd (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (u : Oˣ) (m : ℕ) (P : Ideal O) (hP : P ∈ primeSupport I) :
    ¬ primaryIdealPrime P ∣ (u : O) * lambda ^ m := by
  have hp := primaryIdealPrime_isPrime_of_mem I P hI hP
  have hpp := (primaryIdealPrime_spec P
    (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  intro hd
  exact hp.2.1 ((ramified_primary_coprime u m _ hpp).of_mul_left_right.symm.isUnit_of_dvd hd)

/-- Exact squarefree–cube factorization, including the ramified cubic-symbol phase. -/
theorem rationalSourceResidualFourierCoefficient_full_squarefree_cube (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    rationalSourceResidualFourierCoefficient
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3) =
      (‖ringComplex (primaryIdealGenerator J)‖ : ℂ) *
        ringComplex (symbol (9 * ((u : O) * lambda ^ m)) (primaryIdealGenerator I)) *
        star (normalizedCubicUnitGauss (primaryIdealGenerator I)) *
        rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) := by
  have he := rationalSourceResidualFourierCoefficient_prime_product (primeSupport I) primaryIdealPrime
    (fun P hP => primaryIdealPrime_isPrime_of_mem I P hI hP)
    (fun P hP => (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2)
    (primaryIdealPrime_support_coprime I hI) ((u : O) * lambda ^ m)
    (ramified_primaryPrime_not_dvd I hI u m)
  rw [← primaryIdealGenerator_squarefree_support I hI hsq] at he
  rw [rationalSourceResidualFourierCoefficient_primary_cube _ hJ (primaryIdealGenerator_spec J hJ).2 _
    (mul_ne_zero (ramifiedElement_ne_zero u m) hI), he]
  ring

/-- Exact unramified-residue factorization with the base-frequency symbol. -/
theorem unramifiedResidualCoefficient_full_squarefree_cube (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    unramifiedResidualCoefficient
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3) =
      (‖ringComplex (primaryIdealGenerator J)‖ : ℂ) *
        ringComplex (symbol ((u : O) * lambda ^ m) (primaryIdealGenerator I)) *
        star (normalizedCubicUnitGauss (primaryIdealGenerator I)) *
        unramifiedResidualCoefficient ((u : O) * lambda ^ m) := by
  have he := unramifiedResidualCoefficient_prime_product (primeSupport I) primaryIdealPrime
    (fun P hP => primaryIdealPrime_isPrime_of_mem I P hI hP)
    (fun P hP => (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2)
    (primaryIdealPrime_support_coprime I hI) ((u : O) * lambda ^ m)
    (ramified_primaryPrime_not_dvd I hI u m)
  rw [← primaryIdealGenerator_squarefree_support I hI hsq] at he
  rw [unramifiedResidualCoefficient_primary_cube _ hJ (primaryIdealGenerator_spec J hJ).2, he]
  ring

/-- Bessel normalization removes the ramified frequency multiplier before squarefree–cube factorization. -/
theorem normalizedRamifiedGaussTerm_full_squarefree_cube (v : Oˣ) (n : ℕ)
    (I J : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0)
    (hsq : Squarefree I) (u : Oˣ) (m : ℕ) :
    sourceBesselNormalizer (((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3) *
      unramifiedGaussResidue (((v : O) * lambda ^ n) *
        (((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3)) =
      ((‖ringComplex (primaryIdealGenerator J)‖ : ℂ) *
        ringComplex (symbol (((v * u : Oˣ) : O) * lambda ^ (n + m)) (primaryIdealGenerator I)) *
        star (normalizedCubicUnitGauss (primaryIdealGenerator I)) *
        unramifiedResidualCoefficient (((v * u : Oˣ) : O) * lambda ^ (n + m))) /
          (‖ringComplex ((v : O) * lambda ^ n)‖ : ℂ) ^ (1 / 3 : ℂ) := by
  let a : O := (v : O) * lambda ^ n
  let h : O := ((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3
  have ha : a ≠ 0 := ramifiedElement_ne_zero v n
  have ha0 : (‖ringComplex a‖ : ℂ) ^ (1 / 3 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (ringComplex_ne_zero ha))))
  have he : a * h = (((v * u : Oˣ) : O) * lambda ^ (n + m)) *
      primaryIdealGenerator I * primaryIdealGenerator J ^ 3 := by
    simp only [a, h, Units.val_mul, pow_add]
    ring
  have hn : sourceBesselNormalizer h * unramifiedGaussResidue (a * h) *
      (‖ringComplex a‖ : ℂ) ^ (1 / 3 : ℂ) = unramifiedResidualCoefficient (a * h) := by
    rw [unramifiedResidualCoefficient, mul_comm a h, sourceBesselNormalizer_mul h a]
    ring
  apply (eq_div_iff ha0).mpr
  change sourceBesselNormalizer h * unramifiedGaussResidue (a * h) *
    (‖ringComplex a‖ : ℂ) ^ (1 / 3 : ℂ) = _
  rw [hn, he, unramifiedResidualCoefficient_full_squarefree_cube I J hI hJ hsq]

/-- Each ramified cusp is a finite sum of explicit squarefree Gauss branches. -/
theorem ramifiedResidualFourierCoefficient_full_squarefree_cube (v t : Oˣ)
    (I J : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0)
    (hsq : Squarefree I) (u : Oˣ) (m : ℕ) :
    let h := ((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3
    ramifiedResidualFourierCoefficient v t h =
      ((3 : ℂ) ^ (4 / 3 : ℂ) / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) *
        ∑ i : RamifiedSixBranch, ramifiedSixWeight v t h i (4 / 3) *
          (((‖ringComplex (primaryIdealGenerator J)‖ : ℂ) *
            ringComplex (symbol (((ramifiedSixUnit v t i * u : Oˣ) : O) *
              lambda ^ (ramifiedSixPower i + m)) (primaryIdealGenerator I)) *
            star (normalizedCubicUnitGauss (primaryIdealGenerator I)) *
            unramifiedResidualCoefficient (((ramifiedSixUnit v t i * u : Oˣ) : O) *
              lambda ^ (ramifiedSixPower i + m))) /
                (‖ringComplex ((ramifiedSixUnit v t i : O) * lambda ^ ramifiedSixPower i)‖ : ℂ) ^ (1 / 3 : ℂ)) := by
  dsimp only
  let h := ((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3
  have he : ramifiedResidualFourierCoefficient v t h =
      ((3 : ℂ) ^ (4 / 3 : ℂ) / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) *
        (sourceBesselNormalizer h * ramifiedArithmeticResidue v t h) := by
    unfold ramifiedResidualFourierCoefficient sourceBesselNormalizer
    ring
  change ramifiedResidualFourierCoefficient v t h = _
  rw [he]
  congr 1
  rw [ramifiedArithmeticResidue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hw : ramifiedSixWeight v t h i (4 / 3) = 0
  · rw [hw, zero_mul, mul_zero, zero_mul]
  rw [ramifiedSixIndex_multiplier v t h i hw]
  calc
    _ = ramifiedSixWeight v t h i (4 / 3) *
        (sourceBesselNormalizer h * unramifiedGaussResidue
          (((ramifiedSixUnit v t i : O) * lambda ^ ramifiedSixPower i) * h)) := by ring
    _ = _ := by
      rw [normalizedRamifiedGaussTerm_full_squarefree_cube (ramifiedSixUnit v t i)
        (ramifiedSixPower i) I J hI hJ hsq u m]

lemma sourceCuspCoefficient_full_squarefree_cube_support (j : Fin 3) (h : O)
    (hh : h ≠ 0) (hc : sourceCuspCoefficient j h ≠ 0) :
    ∃ p : ThetaFullIndex, thetaFullFrequency p = h := by
  have hs : ∃ (u : Oˣ) (m : ℕ) (I J : Ideal O), Squarefree I ∧
      primaryIdealGenerator I ≠ 0 ∧ primaryIdealGenerator J ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I * primaryIdealGenerator J ^ 3 := by
    fin_cases j
    · exact rationalSourceResidualFourierCoefficient_full_squarefree_cube_support h hh hc
    · exact ramifiedBesselCoefficient_full_squarefree_cube_support false h hh hc
    · exact ramifiedBesselCoefficient_full_squarefree_cube_support true h hh hc
  obtain ⟨u, m, I, J, hs, hI, hJ, he⟩ := hs
  exact ⟨(u, m, (⟨I, hs, hI⟩, ⟨J, hJ⟩)), he.symm⟩

/-- Every reflected radial series is indexed exactly by unit, ramified, squarefree, and cube factors. -/
theorem sourceCuspRadial_tsum_full_index (j : Fin 3) (z : ℂ) (W : O → ℂ) :
    (∑' h : O, sourceCuspRadialCoefficient j z h * W h) =
      ∑' p : ThetaFullIndex, sourceCuspRadialCoefficient j z (thetaFullFrequency p) * W (thetaFullFrequency p) := by
  let f : O → ℂ := fun h => sourceCuspRadialCoefficient j z h * W h
  change (∑' h : O, f h) = ∑' p : ThetaFullIndex, f (thetaFullFrequency p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p : Function.support (fun p : ThetaFullIndex => f (thetaFullFrequency p)) => thetaFullFrequency p.val)
  · exact thetaFullFrequency_injective.comp Subtype.val_injective
  · intro h hh
    have hh0 : h ≠ 0 := by
      intro hz
      exact hh (by simp only [f, hz, sourceCuspRadialCoefficient_zero, zero_mul])
    have hf : sourceCuspCoefficient j h ≠ 0 := by
      intro hz
      exact hh (by simp only [f, sourceCuspRadialCoefficient, sourceCuspRadialBaseCoefficient,
        hz, star_zero, mul_zero, zero_div, zero_mul])
    obtain ⟨p, hp⟩ := sourceCuspCoefficient_full_squarefree_cube_support j h hh0 hf
    exact ⟨⟨p, by change f (thetaFullFrequency p) ≠ 0; rwa [hp]⟩, hp⟩
  · intro p
    rfl

lemma thetaFullFrequency_radialLength (p : ThetaFullIndex) :
    sourceCuspRadialLength (thetaFullFrequency p) =
      ‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2 := by
  have hp : primaryIdealGenerator p.2.2.1.val * primaryIdealGenerator p.2.2.2.val ^ 3 ≠ 0 :=
    mul_ne_zero p.2.2.1.property.2 (pow_ne_zero 3 p.2.2.2.property)
  rw [sourceCuspRadialLength, if_neg (thetaFullFrequency_ne_zero p), completedMellinLength,
    sourceCuspRadialLength, if_neg hp]
  simp only [thetaFullFrequency, map_mul, map_pow, norm_mul, norm_pow, norm_ringComplex_unit, one_mul]
  rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm p.2.1 2]
  ring

/-- The affine local Gauss weight depends only on the frequency modulo `9q`. -/
lemma scaledAffineGaussWeight_congr (q : O) (hq : q ≠ 0) (u : Oˣ) (n : ℕ)
    (h k : O) (hmod : 9 * q ∣ h - k) (s : ℂ) :
    scaledAffineGaussWeight q u n h s = scaledAffineGaussWeight q u n k s := by
  obtain ⟨r, hr⟩ := hmod
  have hdiff : h = k + q * (9 * r) := by linear_combination hr
  have hdq : q ∣ h - k := ⟨9 * r, by linear_combination hr⟩
  have hdiv : q ∣ h ↔ q ∣ k := by
    constructor
    · intro hh
      convert dvd_sub hh hdq using 1 <;> ring
    · intro hk
      convert dvd_add hk hdq using 1 <;> ring
  by_cases hh : q ∣ h
  · have hk := hdiv.mp hh
    have he : Classical.choose hh = Classical.choose hk + 9 * r := by
      apply mul_left_cancel₀ hq
      rw [← Classical.choose_spec hh, mul_add, ← Classical.choose_spec hk]
      exact hdiff
    have heq : (3 : O) ∣ Classical.choose hh + ramifiedArithmeticPhase u n ↔
        (3 : O) ∣ Classical.choose hk + ramifiedArithmeticPhase u n := by
      rw [he]
      have hd : (3 : O) ∣ 9 * r := ⟨3 * r, by ring⟩
      constructor
      · intro ht
        convert dvd_sub ht hd using 1 <;> ring
      · intro ht
        convert dvd_add ht hd using 1 <;> ring
    have hphase : tracePhase (cuspFrequency h / ringComplex (3 * q)) =
        tracePhase (cuspFrequency k / ringComplex (3 * q)) := by
      have he' : cuspFrequency h / ringComplex (3 * q) =
          cuspFrequency k / ringComplex (3 * q) + cuspFrequency r * 3 := by
        rw [hdiff]
        simp only [cuspFrequency, map_add, map_mul, map_ofNat]
        field_simp [ringComplex_ne_zero hq, ringComplex_ne_zero traceLambda_ne_zero]
        ring
      rw [he', AddChar.map_add_eq_mul]
      have hp : tracePhase (cuspFrequency r * 3) = 1 := by
        simpa only [map_one, mul_one] using cuspFrequency_period r 1
      rw [hp, mul_one]
    rw [scaledAffineGaussWeight, dif_pos hh, scaledAffineGaussWeight, dif_pos hk]
    by_cases ht : (3 : O) ∣ Classical.choose hh + ramifiedArithmeticPhase u n
    · rw [if_pos ht, if_pos (heq.mp ht), hphase]
    · rw [if_neg ht, if_neg (fun hk => ht (heq.mpr hk))]
  · rw [scaledAffineGaussWeight, dif_neg hh, scaledAffineGaussWeight,
      dif_neg (fun hk => hh (hdiv.mpr hk))]

lemma cuspFrequency_div_three_phase_congr (a h k : O) (hmod : (9 : O) ∣ h - k) :
    tracePhase (cuspFrequency h * (ringComplex a / 3)) =
      tracePhase (cuspFrequency k * (ringComplex a / 3)) := by
  obtain ⟨r, hr⟩ := hmod
  have he : h = k + 9 * r := by linear_combination hr
  have he' : cuspFrequency h * (ringComplex a / 3) =
      cuspFrequency k * (ringComplex a / 3) + cuspFrequency r * (3 * ringComplex a) := by
    rw [he]
    simp only [cuspFrequency, map_add, map_mul, map_ofNat]
    ring
  rw [he', AddChar.map_add_eq_mul, cuspFrequency_period, mul_one]

lemma onceCuspScale_mul_root_dvd_three (t : Oˣ) (j : ℕ) : onceCuspScale t * omega ^ j ∣ (3 : O) := by
  let v : Oˣ := t * cuspOmegaUnit ^ j
  have hv : onceCuspScale t * omega ^ j = (v : O) * traceLambda := by
    simp only [v, onceCuspScale, Units.val_mul, Units.val_pow_eq_pow_val, cuspOmegaUnit_val]
    ring
  have htrace : traceLambda ^ 2 = (-3 : O) := by
    unfold traceLambda
    linear_combination 4 * cusp_omega_relation
  rw [hv]
  refine ⟨(v⁻¹ : Oˣ) * (-traceLambda), ?_⟩
  calc
    (3 : O) = -traceLambda ^ 2 := by rw [htrace]; ring
    _ = ((v : O) * (v⁻¹ : Oˣ)) * (-traceLambda ^ 2) := by rw [Units.mul_inv]; ring
    _ = _ := by ring

/-- The six ramified weights have one fixed period, independent of the prime factors. -/
lemma ramifiedSixWeight_congr_mod_twentySeven (u t : Oˣ) (h k : O)
    (hmod : (27 : O) ∣ h - k) (i : RamifiedSixBranch) (s : ℂ) :
    ramifiedSixWeight u t h i s = ramifiedSixWeight u t k i s := by
  have hphase := cuspFrequency_div_three_phase_congr (u⁻¹ : Oˣ) h k
    ((show (9 : O) ∣ 27 from ⟨3, by norm_num⟩).trans hmod)
  have hq (q : O) (hq : q ≠ 0) (hq3 : q ∣ 3) (v : Oˣ) (n : ℕ) :
      scaledAffineGaussWeight q v n h s = scaledAffineGaussWeight q v n k s := by
    apply scaledAffineGaussWeight_congr q hq v n h k _ s
    exact (show 9 * q ∣ (27 : O) from by
      convert mul_dvd_mul_left (9 : O) hq3 using 1 <;> norm_num).trans hmod
  rcases i with i | i
  · simp only [ramifiedSixWeight]
    rw [hq (u : O) u.ne_zero (show (u : O) ∣ 3 from u.isUnit.dvd) u 0]
  rcases i with i | i
  · simp only [ramifiedSixWeight]
    rw [hphase, hq (-(u : O)) (neg_ne_zero.mpr u.ne_zero) (show -(u : O) ∣ 3 from (-u).isUnit.dvd)]
  rcases i with i | j
  · simp only [ramifiedSixWeight]
    rw [hphase, hq 1 one_ne_zero (one_dvd _)]
  · simp only [ramifiedSixWeight]
    rw [hphase, hq (onceCuspScale t * omega ^ j.val)
      (mul_ne_zero (onceCusp_scale_ne_zero t) (pow_ne_zero _
        (omega_primitive.isUnit (by decide)).ne_zero)) (onceCuspScale_mul_root_dvd_three t j.val)]

lemma ramified_symbol_primary_congr_mod_nine (u : Oˣ) (m : ℕ) (a b : O)
    (ha : lambda ^ 2 ∣ a - 1) (hb : lambda ^ 2 ∣ b - 1) (hab : (9 : O) ∣ a - b) :
    symbol ((u : O) * lambda ^ m) a = symbol ((u : O) * lambda ^ m) b := by
  rw [symbol_mul_numerator, symbol_mul_numerator,
    symbol_pow_numerator _ a ha, symbol_pow_numerator _ b hb,
    symbol_unit_congr_mod_nine u.val a b u.isUnit ha hb hab,
    symbol_lambda_congr_mod_nine a b ha hb hab]

lemma ramified_symbol_primary_exponent_mod_three (u : Oˣ) (m : ℕ) (a : O)
    (ha : lambda ^ 2 ∣ a - 1) :
    symbol ((u : O) * lambda ^ m) a = symbol ((u : O) * lambda ^ (m % 3)) a := by
  have hc : IsCoprime lambda a := coprime_of_dvd_sub_one lambda a
    ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans ha)
  have hz := symbol_cube_of_isCoprime lambda a ha hc
  rw [symbol_mul_numerator, symbol_mul_numerator,
    symbol_pow_numerator _ a ha, symbol_pow_numerator _ a ha]
  congr 1
  calc
    _ = symbol lambda a ^ (m % 3 + 3 * (m / 3)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add, pow_mul, hz, one_pow, mul_one]

/-- Reduction modulo three labels the finitely many integral cusp configurations. -/
def fixedCuspReduction : SL(2, O) →* SL(2, O ⧸ Ideal.span {(3 : O)}) :=
  Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(3 : O)}))

abbrev FixedCuspSector := fixedCuspReduction.range

instance : Finite FixedCuspSector := by
  letI : Finite (O ⧸ Ideal.span {(3 : O)}) :=
    (Ideal.span {(3 : O)}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  infer_instance

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
