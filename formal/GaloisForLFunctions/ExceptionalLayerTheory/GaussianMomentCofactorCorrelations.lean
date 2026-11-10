import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentTypeIPole

/-!
# Complete correlations of critical Gaussian moment cofactors

The long-variable height phase cancels in a pair. Its continuous Gram
entry is an integer power of a complex Gaussian covariance. Rotation
then suppresses separated cofactors geometrically in the moment order;
the complete lattice retains an explicit Bernoulli remainder.
-/

open Complex MeasureTheory Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The critical Mellin exponent of the normalized moment. -/
def gaussianCriticalMomentExponent (r : ℕ) (t : ℝ) : ℂ :=
  ((2 * r : ℕ) : ℂ) - (((1 / 2 : ℝ) : ℂ) + t * I)

/-- The part of a cofactor column independent of its long variable. -/
def gaussianCofactorAmplitude (r : ℕ) (t : ℝ) (ε : ℂ) (m : ℝ) : ℂ :=
  (ε / (t : ℂ)) ^ r * (m : ℂ) ^ gaussianCriticalMomentExponent r t

/-- Complex damping after pairing two dilated Gaussian columns. -/
def gaussianCofactorPairDamping (ε : ℂ) (m k : ℝ) : ℂ :=
  ε * (m : ℂ) ^ 2 + (starRingEnd ℂ) ε * (k : ℂ) ^ 2

/-- The exact continuous pair correlation. -/
def gaussianCofactorCorrelationMain (r : ℕ) (t : ℝ) (ε : ℂ) (m k : ℝ) : ℂ :=
  gaussianCofactorAmplitude r t ε m * (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k) *
    ((1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)) /
      gaussianCofactorPairDamping ε m k ^ (2 * r)

/-- The positive geometric scale of the two diagonal continuum entries. -/
def gaussianCofactorCorrelationScale (r : ℕ) (t : ℝ) (ε : ℂ) (m k : ℝ) : ℝ :=
  ‖gaussianCofactorAmplitude r t ε m‖ * ‖gaussianCofactorAmplitude r t ε k‖ *
    ‖(1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)‖ /
      (2 * ε.re * m * k) ^ (2 * r)

/-- The dimensionless overlap of the two continuum columns. -/
def gaussianCofactorOverlap (r : ℕ) (ε : ℂ) (m k : ℝ) : ℝ :=
  ((2 * ε.re * m * k) ^ 2 / ‖gaussianCofactorPairDamping ε m k‖ ^ 2) ^ r

theorem gaussianCofactorPairDamping_re (ε : ℂ) (m k : ℝ) :
    (gaussianCofactorPairDamping ε m k).re = ε.re * (m ^ 2 + k ^ 2) := by
  simp only [gaussianCofactorPairDamping, Complex.add_re, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, sub_zero]
  ring

theorem gaussianCofactorPairDamping_im (ε : ℂ) (m k : ℝ) :
    (gaussianCofactorPairDamping ε m k).im = ε.im * (m ^ 2 - k ^ 2) := by
  simp only [gaussianCofactorPairDamping, Complex.add_im, Complex.mul_im,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, zero_add]
  ring

theorem gaussianCofactorPairDamping_re_pos {ε : ℂ} (hε : 0 < ε.re)
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    0 < (gaussianCofactorPairDamping ε m k).re := by
  rw [gaussianCofactorPairDamping_re]
  positivity

private theorem pairDamping_ne_zero {ε : ℂ} (hε : 0 < ε.re)
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    gaussianCofactorPairDamping ε m k ≠ 0 := by
  intro h
  have hh := gaussianCofactorPairDamping_re_pos hε hm hk
  rw [h, Complex.zero_re] at hh
  exact lt_irrefl _ hh

/-- The squared covariance norm records both scale separation and rotation. -/
theorem norm_sq_gaussianCofactorPairDamping (ε : ℂ) (m k : ℝ) :
    ‖gaussianCofactorPairDamping ε m k‖ ^ 2 =
      (2 * ε.re * m * k) ^ 2 +
        (ε.re ^ 2 + ε.im ^ 2) * (m ^ 2 - k ^ 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, gaussianCofactorPairDamping_re,
    gaussianCofactorPairDamping_im]
  ring

theorem gaussianCofactorOverlap_nonneg (r : ℕ) (ε : ℂ) (m k : ℝ) :
    0 ≤ gaussianCofactorOverlap r ε m k := by
  unfold gaussianCofactorOverlap
  positivity

/-- The exact normalized continuum overlap, including the near-diagonal band. -/
theorem gaussianCofactorOverlap_eq (r : ℕ) {ε : ℂ} (hε : 0 < ε.re)
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    gaussianCofactorOverlap r ε m k =
      (1 + (1 + (ε.im / ε.re) ^ 2) * ((m ^ 2 - k ^ 2) / (2 * m * k)) ^ 2)⁻¹ ^ r := by
  unfold gaussianCofactorOverlap
  rw [norm_sq_gaussianCofactorPairDamping]
  congr 1
  field_simp [hε.ne', hm.ne', hk.ne']

theorem gaussianCofactorOverlap_le_one (r : ℕ) {ε : ℂ} (hε : 0 < ε.re)
    {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    gaussianCofactorOverlap r ε m k ≤ 1 := by
  unfold gaussianCofactorOverlap
  apply pow_le_one₀ (by positivity)
  apply (div_le_one (sq_pos_of_pos (norm_pos_iff.mpr (pairDamping_ne_zero hε hm hk)))).mpr
  rw [norm_sq_gaussianCofactorPairDamping]
  exact le_add_of_nonneg_right (by positivity)

/-- Cofactors separated by a factor of two lose one height power per moment. -/
theorem gaussianCofactorOverlap_le_height (r : ℕ) {ε : ℂ} {t m k : ℝ}
    (hε : 0 < ε.re) (ht : 4 ≤ t) (hm : 0 < m) (hk : 0 < k)
    (hsep : 2 * k ≤ m) (hrot : ε.re * t ≤ |ε.im|) :
    gaussianCofactorOverlap r ε m k ≤ (1 / t) ^ r := by
  have ht0 : 0 < t := by linarith only [ht]
  have hdiff : m * k ≤ m ^ 2 - k ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hsep) hm.le,
      mul_nonneg (sub_nonneg.mpr hsep) hk.le, sq_nonneg k]
  have hrot2 : ε.re ^ 2 * t ^ 2 ≤ ε.im ^ 2 := by
    have hh := pow_le_pow_left₀ (mul_pos hε ht0).le hrot 2
    simpa only [mul_pow, sq_abs] using hh
  have hdiff2 : (m * k) ^ 2 ≤ (m ^ 2 - k ^ 2) ^ 2 :=
    pow_le_pow_left₀ (mul_pos hm hk).le hdiff 2
  have hnorm : t * (2 * ε.re * m * k) ^ 2 ≤
      ‖gaussianCofactorPairDamping ε m k‖ ^ 2 := by
    rw [norm_sq_gaussianCofactorPairDamping]
    have hprod := mul_le_mul hrot2 hdiff2 (sq_nonneg (m * k)) (sq_nonneg ε.im)
    have htime : 4 * t ≤ t ^ 2 := by nlinarith only [ht]
    have hscaled := mul_le_mul_of_nonneg_right htime
      (mul_nonneg (sq_nonneg ε.re) (sq_nonneg (m * k)))
    nlinarith only [hprod, hscaled,
      mul_nonneg (sq_nonneg ε.re) (sq_nonneg (m ^ 2 - k ^ 2)),
      sq_nonneg (2 * ε.re * m * k)]
  unfold gaussianCofactorOverlap
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_div_iff₀
    (sq_pos_of_pos (norm_pos_iff.mpr (pairDamping_ne_zero hε hm hk))) ht0).mpr
  simpa only [one_mul, mul_comm] using hnorm

private theorem criticalExponent_add_conj (r : ℕ) (t : ℝ) :
    gaussianCriticalMomentExponent r t +
      (starRingEnd ℂ) (gaussianCriticalMomentExponent r t) = ((4 * r : ℕ) : ℂ) - 1 := by
  simp only [gaussianCriticalMomentExponent, map_sub, map_add, map_mul,
    Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem criticalMoment_dilate (r : ℕ) (t : ℝ) (ε : ℂ)
    {m x : ℝ} (hm : 0 < m) (hx : 0 < x) :
    (ε / (t : ℂ)) ^ r * gaussianMellinWeight (gaussianCriticalMomentExponent r t) ε (m * x) =
      gaussianCofactorAmplitude r t ε m *
        gaussianMellinWeight (gaussianCriticalMomentExponent r t) (ε * (m : ℂ) ^ 2) x := by
  simp only [gaussianMellinWeight, gaussianCofactorAmplitude, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hm.le hx.le]
  rw [show ε * ((m : ℂ) * (x : ℂ)) ^ 2 = (ε * (m : ℂ) ^ 2) * (x : ℂ) ^ 2 by ring]
  ring

private theorem mellin_pair (r : ℕ) (t : ℝ) (a b : ℂ) {x : ℝ} (hx : 0 < x) :
    gaussianMellinWeight (gaussianCriticalMomentExponent r t) a x *
      (starRingEnd ℂ) (gaussianMellinWeight (gaussianCriticalMomentExponent r t) b x) =
      gaussianMellinWeight (((4 * r : ℕ) : ℂ) - 1) (a + (starRingEnd ℂ) b) x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hc : (starRingEnd ℂ) ((x : ℂ) ^ gaussianCriticalMomentExponent r t) =
      (x : ℂ) ^ ((starRingEnd ℂ) (gaussianCriticalMomentExponent r t)) := by
    rw [Complex.cpow_conj _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_ne_zero.symm), Complex.conj_ofReal]
  simp only [gaussianMellinWeight, map_mul, ← Complex.exp_conj, map_neg,
    map_pow, Complex.conj_ofReal]
  calc
    _ = ((x : ℂ) ^ gaussianCriticalMomentExponent r t *
        (starRingEnd ℂ) ((x : ℂ) ^ gaussianCriticalMomentExponent r t)) *
        (Complex.exp (-(a * (x : ℂ) ^ 2)) *
          Complex.exp (-((starRingEnd ℂ) b * (x : ℂ) ^ 2))) := by ring
    _ = _ := by
      rw [hc, ← Complex.cpow_add _ _ hx0, criticalExponent_add_conj,
        ← Complex.exp_add]
      congr 2
      ring

/-- The literal cofactor pair has one scalar height phase and one Gaussian
with integer Mellin exponent in the long variable. -/
theorem gaussianCriticalMoment_pair (r : ℕ) (t : ℝ) (ε : ℂ)
    {m k x : ℝ} (hm : 0 < m) (hk : 0 < k) (hx : 0 < x) :
    ((ε / (t : ℂ)) ^ r *
      gaussianMellinWeight (gaussianCriticalMomentExponent r t) ε (m * x)) *
      (starRingEnd ℂ) ((ε / (t : ℂ)) ^ r *
        gaussianMellinWeight (gaussianCriticalMomentExponent r t) ε (k * x)) =
      (gaussianCofactorAmplitude r t ε m *
        (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k)) *
        gaussianMellinWeight (((4 * r : ℕ) : ℂ) - 1)
          (gaussianCofactorPairDamping ε m k) x := by
  rw [criticalMoment_dilate r t ε hm hx, criticalMoment_dilate r t ε hk hx, map_mul]
  calc
    _ = (gaussianCofactorAmplitude r t ε m *
        (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k)) *
        (gaussianMellinWeight (gaussianCriticalMomentExponent r t) (ε * (m : ℂ) ^ 2) x *
          (starRingEnd ℂ) (gaussianMellinWeight (gaussianCriticalMomentExponent r t)
            (ε * (k : ℂ) ^ 2) x)) := by ring
    _ = _ := by
      rw [mellin_pair r t _ _ hx]
      simp only [map_mul, map_pow, Complex.conj_ofReal, gaussianCofactorPairDamping]

/-- The Gaussian pair formula holds for the original arithmetic moment samples. -/
theorem gaussianHigherPrimeMomentWeight_pair (r : ℕ) (t : ℝ) (ε : ℂ)
    {m k d : ℕ} (hm : 0 < m) (hk : 0 < k) (hd : 0 < d) :
    gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * d) *
      (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * d)) =
      (gaussianCofactorAmplitude r t ε m *
        (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k)) *
        gaussianMellinWeight (((4 * r : ℕ) : ℂ) - 1)
          (gaussianCofactorPairDamping ε m k) d := by
  simpa only [gaussianHigherPrimeMomentWeight, gaussianCriticalMomentExponent, Nat.cast_mul]
    using gaussianCriticalMoment_pair r t ε
      (by exact_mod_cast hm : (0 : ℝ) < m) (by exact_mod_cast hk : (0 : ℝ) < k)
      (by exact_mod_cast hd : (0 : ℝ) < d)

theorem summable_gaussianHigherPrimeMoment_pair (r : ℕ) (t : ℝ)
    {ε : ℂ} (hε : 0 < ε.re) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    Summable (fun d : ℕ => gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
      (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * (d + 1)))) := by
  have hs := summable_gaussianMellinWeight_lattice_all
    (w := ((4 * r : ℕ) : ℂ) - 1)
    (gaussianCofactorPairDamping_re_pos hε
      (by exact_mod_cast hm : (0 : ℝ) < m) (by exact_mod_cast hk : (0 : ℝ) < k))
    (by norm_num : (0 : ℝ) < 1)
  simp only [one_mul] at hs
  apply (hs.mul_left (gaussianCofactorAmplitude r t ε m *
    (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k))).congr
  intro d
  simpa only [Nat.cast_add, Nat.cast_one] using
    (gaussianHigherPrimeMomentWeight_pair r t ε hm hk (by omega : 0 < d + 1)).symm

private theorem pair_main_simplify (r : ℕ) (z : ℂ) :
    (1 / 2 : ℂ) * Complex.Gamma (((((4 * r : ℕ) : ℂ) - 1) + 1) / 2) *
      z ^ (-((((4 * r : ℕ) : ℂ) - 1) + 1) / 2) =
      ((1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)) / z ^ (2 * r) := by
  have harg : (((((4 * r : ℕ) : ℂ) - 1) + 1) / 2) = ((2 * r : ℕ) : ℂ) := by
    push_cast
    ring
  rw [show -((((4 * r : ℕ) : ℂ) - 1) + 1) / 2 =
    -(((((4 * r : ℕ) : ℂ) - 1) + 1) / 2) by ring,
    harg, Complex.cpow_neg, Complex.cpow_natCast]
  simp only [div_eq_mul_inv]

/-- The rational Gaussian covariance is the exact integral of the original
critical moment pair, not a substitute kernel. -/
theorem integral_gaussianCriticalMoment_pair {r : ℕ} (hr : r ≠ 0)
    (t : ℝ) {ε : ℂ} (hε : 0 < ε.re) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    (∫ x in Set.Ioi (0 : ℝ),
      ((ε / (t : ℂ)) ^ r *
        gaussianMellinWeight (gaussianCriticalMomentExponent r t) ε (m * x)) *
        (starRingEnd ℂ) ((ε / (t : ℂ)) ^ r *
          gaussianMellinWeight (gaussianCriticalMomentExponent r t) ε (k * x))) =
      gaussianCofactorCorrelationMain r t ε m k := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hw : 0 < (((4 * r : ℕ) : ℂ) - 1).re := by
    have hre : (((4 * r : ℕ) : ℂ) - 1).re = 4 * (r : ℝ) - 1 := by simp
    rw [hre]
    linarith only [hrR]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
    gaussianCriticalMoment_pair r t ε hm hk hx), integral_const_mul,
    integral_gaussianMellinWeight hw (gaussianCofactorPairDamping_re_pos hε hm hk),
    pair_main_simplify]
  unfold gaussianCofactorCorrelationMain
  ring

/-- The complete arithmetic pair differs from its exact continuum correlation
by the high-order Gaussian lattice remainder. -/
theorem norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le {r : ℕ} (hr : r ≠ 0)
    (t : ℝ) {ε : ℂ} (hε : 0 < ε.re) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    ‖(∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
        (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * (d + 1)))) -
      gaussianCofactorCorrelationMain r t ε m k‖ ≤
      ‖gaussianCofactorAmplitude r t ε m *
        (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k)‖ *
        (|((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ)) *
        gaussianMellinJetVariation (2 * r) (((4 * r : ℕ) : ℂ) - 1)
          (gaussianCofactorPairDamping ε m k) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrR : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero hr)
  have hw : ((2 * r : ℕ) : ℝ) - 1 < (((4 * r : ℕ) : ℂ) - 1).re := by
    have hre : (((4 * r : ℕ) : ℂ) - 1).re = 4 * (r : ℝ) - 1 := by simp
    rw [hre]
    push_cast
    linarith only [hrR]
  have hb := norm_tsum_gaussianMellinWeight_sub_main_higher_le r hr hw
    (gaussianCofactorPairDamping_re_pos hε hmR hkR) (by norm_num : (0 : ℝ) < 1)
  simp only [one_mul, one_pow, Complex.ofReal_one, inv_one, pair_main_simplify] at hb
  rw [tsum_congr (fun d => gaussianHigherPrimeMomentWeight_pair r t ε hm hk (by omega)),
    tsum_mul_left]
  have he :
      (gaussianCofactorAmplitude r t ε m * (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k)) *
        (∑' d : ℕ, gaussianMellinWeight (((4 * r : ℕ) : ℂ) - 1)
          (gaussianCofactorPairDamping ε m k) (d + 1)) -
        gaussianCofactorCorrelationMain r t ε m k =
      (gaussianCofactorAmplitude r t ε m * (starRingEnd ℂ) (gaussianCofactorAmplitude r t ε k)) *
        ((∑' d : ℕ, gaussianMellinWeight (((4 * r : ℕ) : ℂ) - 1)
          (gaussianCofactorPairDamping ε m k) (d + 1)) -
            ((1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)) /
              gaussianCofactorPairDamping ε m k ^ (2 * r)) := by
    unfold gaussianCofactorCorrelationMain
    ring
  simp only [Nat.cast_add, Nat.cast_one]
  rw [he, norm_mul]
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)

theorem gaussianCofactorCorrelationScale_nonneg (r : ℕ) (t : ℝ)
    {ε : ℂ} (hε : 0 < ε.re) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    0 ≤ gaussianCofactorCorrelationScale r t ε m k := by
  unfold gaussianCofactorCorrelationScale
  positivity

/-- Normalization separates the exact scalar size from phase cancellation. -/
theorem norm_gaussianCofactorCorrelationMain (r : ℕ) (t : ℝ)
    {ε : ℂ} (hε : 0 < ε.re) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    ‖gaussianCofactorCorrelationMain r t ε m k‖ =
      gaussianCofactorCorrelationScale r t ε m k * gaussianCofactorOverlap r ε m k := by
  have hd : 2 * ε.re * m * k ≠ 0 := ne_of_gt (by positivity)
  have hz : ‖gaussianCofactorPairDamping ε m k‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (pairDamping_ne_zero hε hm hk))
  simp only [gaussianCofactorCorrelationMain, norm_div, norm_mul, norm_pow, Complex.norm_conj,
    gaussianCofactorCorrelationScale, gaussianCofactorOverlap, div_pow, ← pow_mul]
  field_simp

/-- A separated continuum cofactor pair is exponentially small in the order. -/
theorem norm_gaussianCofactorCorrelationMain_le_height (r : ℕ) {t : ℝ}
    {ε : ℂ} (hε : 0 < ε.re) (ht : 4 ≤ t) {m k : ℝ} (hm : 0 < m) (hk : 0 < k)
    (hsep : 2 * k ≤ m) (hrot : ε.re * t ≤ |ε.im|) :
    ‖gaussianCofactorCorrelationMain r t ε m k‖ ≤
      gaussianCofactorCorrelationScale r t ε m k * (1 / t) ^ r := by
  rw [norm_gaussianCofactorCorrelationMain r t hε hm hk]
  exact mul_le_mul_of_nonneg_left (gaussianCofactorOverlap_le_height r hε ht hm hk hsep hrot)
    (gaussianCofactorCorrelationScale_nonneg r t hε hm hk)

private theorem overlap_self (r : ℕ) {ε : ℂ} (hε : 0 < ε.re)
    {m : ℝ} (hm : 0 < m) : gaussianCofactorOverlap r ε m m = 1 := by
  rw [gaussianCofactorOverlap_eq r hε hm hm]
  simp only [sub_self, zero_div, zero_pow (by omega : (2 : ℕ) ≠ 0),
    mul_zero, add_zero, inv_one, one_pow]

/-- The normalization is exactly the geometric mean of the diagonal
continuum norms. -/
theorem gaussianCofactorCorrelationScale_sq (r : ℕ) (t : ℝ)
    {ε : ℂ} (hε : 0 < ε.re) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    gaussianCofactorCorrelationScale r t ε m k ^ 2 =
      ‖gaussianCofactorCorrelationMain r t ε m m‖ *
        ‖gaussianCofactorCorrelationMain r t ε k k‖ := by
  rw [norm_gaussianCofactorCorrelationMain r t hε hm hm,
    norm_gaussianCofactorCorrelationMain r t hε hk hk, overlap_self r hε hm,
    overlap_self r hε hk, mul_one, mul_one]
  have hden : ((2 * ε.re * m * k) ^ (2 * r)) ^ 2 =
      (2 * ε.re * m * m) ^ (2 * r) * (2 * ε.re * k * k) ^ (2 * r) := by
    calc
      _ = ((2 * ε.re * m * k) ^ 2) ^ (2 * r) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = _ := by
        rw [show (2 * ε.re * m * k) ^ 2 =
          (2 * ε.re * m * m) * (2 * ε.re * k * k) by ring, mul_pow]
  unfold gaussianCofactorCorrelationScale
  rw [div_pow, hden, div_mul_div_comm]
  congr 1
  ring

#print axioms gaussianCofactorOverlap_eq
#print axioms gaussianCofactorOverlap_le_height
#print axioms gaussianHigherPrimeMomentWeight_pair
#print axioms summable_gaussianHigherPrimeMoment_pair
#print axioms integral_gaussianCriticalMoment_pair
#print axioms norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le
#print axioms norm_gaussianCofactorCorrelationMain_le_height
#print axioms gaussianCofactorCorrelationScale_sq

end GaloisForLFunctions.ExceptionalLayerTheory
