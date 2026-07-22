import GaloisForLFunctions.RHTower.SuzukiCausalDepthFrostmanTransfer

/-!
# Suzuki causal-depth rectangular Carathéodory growth

After the source-forced half-prime-log phase is removed, each causal depth-fused prime ray has
strictly increasing real part in observer aperture.  Equivalently, every positive fixed-width
observer rectangle lies strictly in the demodulated right half-plane at every real height.
The demodulator is then identified exactly with the actual unstarred depth-zero Gamma--Euler
boundary coordinate, up to a strictly positive source amplitude.  Hence the corresponding literal
boundary pairing has positive rectangular real part; no fitted phase is introduced.

The proof first establishes a stronger source-independent radial law: for `0 < c < 1` and every
real `s ≤ 1`, the rational real part

`(1-x)^2 (1-c*x^2*s) / (1-2*c*x^2*s+c^2*x^4)`

is strictly decreasing on `0 < x < 1`.  The lower bound `-1 ≤ s` is unnecessary.  The Suzuki
depth recursion then identifies `x` with the aperture disk node, which decreases strictly with
aperture, and supplies a positive aperture-independent base amplitude.

No RH premise, Xi-zero information, numerical computation, fitted phase, or target positivity
hypothesis is used.  Identifying this now-explicit boundary pairing inside the concrete
restricted-Weil/Robin/Gamma/holonomy rectangular trace remains open.
-/

open Complex Set
open scoped ComplexConjugate

namespace RHTower

noncomputable section

def causalDepthRadialRealPart (c s x : ℝ) : ℝ :=
  (1 - x) ^ 2 * (1 - c * x ^ 2 * s) /
    (1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4)

private theorem one_sub_mul_pos {b s : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hs : s ≤ 1) :
    0 < 1 - b * s := by
  have hbs : b * s ≤ b * 1 := mul_le_mul_of_nonneg_left hs hb0.le
  nlinarith

private theorem radial_den_pos {b s : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hs : s ≤ 1) :
    0 < 1 - 2 * b * s + b ^ 2 := by
  have hid : 1 - 2 * b * s + b ^ 2 =
      (1 - b) ^ 2 + 2 * b * (1 - s) := by ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr hb1))
    (mul_nonneg (mul_nonneg (by norm_num) hb0.le) (sub_nonneg.mpr hs))

private theorem causalDepthRadialPhaseCross_le {b s : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hs : s ≤ 1) :
    (1 - b) * (s * (1 + b ^ 2) - 2 * b) ≤
      (1 - b * s) * (1 - 2 * b * s + b ^ 2) := by
  have hfactor : 0 ≤ 1 + 2 * b - b ^ 2 - 2 * b ^ 2 * s := by
    have hlow : (1 - b) * (1 + 3 * b) ≤
        1 + 2 * b - b ^ 2 - 2 * b ^ 2 * s := by
      nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hs)]
    have : 0 < (1 - b) * (1 + 3 * b) :=
      mul_pos (sub_pos.mpr hb1) (by nlinarith)
    linarith
  have hprod : 0 ≤ (1 - s) * (1 + 2 * b - b ^ 2 - 2 * b ^ 2 * s) :=
    mul_nonneg (sub_nonneg.mpr hs) hfactor
  have hid :
      (1 - b * s) * (1 - 2 * b * s + b ^ 2) -
          (1 - b) * (s * (1 + b ^ 2) - 2 * b) =
        (1 - s) * (1 + 2 * b - b ^ 2 - 2 * b ^ 2 * s) := by
    ring
  nlinarith

private theorem causalDepthRadialRealPart_pos
    {c s x : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : s ≤ 1) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < causalDepthRadialRealPart c s x := by
  let b := c * x ^ 2
  have hb0 : 0 < b := mul_pos hc0 (sq_pos_of_pos hx0)
  have hb1 : b < 1 := by
    have hxsq : x ^ 2 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
    exact mul_lt_one_of_nonneg_of_lt_one_left hc0.le hc1 hxsq.le
  have hnum := one_sub_mul_pos hb0 hb1 hs
  have hden := radial_den_pos hb0 hb1 hs
  have hden' : 0 < 1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4 := by
    convert hden using 1
    all_goals ring
  rw [causalDepthRadialRealPart]
  exact div_pos (mul_pos (sq_pos_of_pos (sub_pos.mpr hx1)) hnum) hden'

private theorem hasDerivAt_causalDepthRadialRealPart
    {c s x : ℝ} (hden : 1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4 ≠ 0) :
    HasDerivAt (causalDepthRadialRealPart c s)
      ((((-2 * (1 - x)) * (1 - c * x ^ 2 * s) +
            (1 - x) ^ 2 * (-c * (2 * x) * s)) *
          (1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4) -
        (1 - x) ^ 2 * (1 - c * x ^ 2 * s) *
          (-2 * c * (2 * x) * s + c ^ 2 * (4 * x ^ 3))) /
          (1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4) ^ 2) x := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x 1).sub (hasDerivAt_id x)
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hfour : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    convert (hasDerivAt_id x).pow 4 using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hn : HasDerivAt
      (fun y : ℝ => (1 - y) ^ 2 * (1 - c * y ^ 2 * s))
      ((-2 * (1 - x)) * (1 - c * x ^ 2 * s) +
        (1 - x) ^ 2 * (-c * (2 * x) * s)) x := by
    convert (hsub.pow 2).mul
      ((hasDerivAt_const x 1).sub ((hsq.const_mul c).mul_const s)) using 1
    all_goals simp only [Pi.pow_apply, Pi.sub_apply]
    all_goals ring
  have hd : HasDerivAt
      (fun y : ℝ => 1 - 2 * c * y ^ 2 * s + c ^ 2 * y ^ 4)
      (-2 * c * (2 * x) * s + c ^ 2 * (4 * x ^ 3)) x := by
    convert ((hasDerivAt_const x 1).sub
      ((hsq.const_mul (2 * c)).mul_const s)).add
        (hfour.const_mul (c ^ 2)) using 1
    all_goals ring_nf
  exact hn.div hd hden

theorem causalDepthRadialRealPart_strictAntiOn
    {c s : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hs : s ≤ 1) :
    StrictAntiOn (causalDepthRadialRealPart c s) (Ioo 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro x hx
    have hb0 : 0 < c * x ^ 2 := mul_pos hc0 (sq_pos_of_pos hx.1)
    have hb1 : c * x ^ 2 < 1 := by
      have hxsq : x ^ 2 < 1 := pow_lt_one₀ hx.1.le hx.2 (by norm_num)
      exact mul_lt_one_of_nonneg_of_lt_one_left hc0.le hc1 hxsq.le
    have hden := radial_den_pos hb0 hb1 hs
    have hden' : 0 < 1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4 := by
      convert hden using 1
      all_goals ring
    exact (hasDerivAt_causalDepthRadialRealPart hden'.ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    let b := c * x ^ 2
    let D := 1 - 2 * b * s + b ^ 2
    let M := s * (1 + b ^ 2) - 2 * b
    have hb0 : 0 < b := mul_pos hc0 (sq_pos_of_pos hx.1)
    have hb1 : b < 1 := by
      have hxsq : x ^ 2 < 1 := pow_lt_one₀ hx.1.le hx.2 (by norm_num)
      exact mul_lt_one_of_nonneg_of_lt_one_left hc0.le hc1 hxsq.le
    have hnum := one_sub_mul_pos hb0 hb1 hs
    have hD : 0 < D := radial_den_pos hb0 hb1 hs
    have hcross : (1 - b) * M ≤ (1 - b * s) * D := by
      exact causalDepthRadialPhaseCross_le hb0 hb1 hs
    have hk0 : 0 < c * x * (1 - x) :=
      mul_pos (mul_pos hc0 hx.1) (sub_pos.mpr hx.2)
    have hk : c * x * (1 - x) < 1 - b := by
      dsimp [b]
      nlinarith [mul_lt_one_of_nonneg_of_lt_one_left hc0.le hc1 hx.2.le]
    have hinner :
        -(1 - b * s) * D + c * x * (1 - x) * M < 0 := by
      by_cases hM : M ≤ 0
      · have : c * x * (1 - x) * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le hM
        nlinarith [mul_pos hnum hD]
      · have hM0 : 0 < M := lt_of_not_ge hM
        have hkm : c * x * (1 - x) * M < (1 - b) * M :=
          mul_lt_mul_of_pos_right hk hM0
        linarith
    have hfactor :
        ((-2 * (1 - x)) * (1 - c * x ^ 2 * s) +
              (1 - x) ^ 2 * (-c * (2 * x) * s)) *
            (1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4) -
          (1 - x) ^ 2 * (1 - c * x ^ 2 * s) *
            (-2 * c * (2 * x) * s + c ^ 2 * (4 * x ^ 3)) =
          2 * (1 - x) *
            (-(1 - b * s) * D + c * x * (1 - x) * M) := by
      dsimp [b, D, M]
      ring
    have hnumDeriv :
        ((-2 * (1 - x)) * (1 - c * x ^ 2 * s) +
              (1 - x) ^ 2 * (-c * (2 * x) * s)) *
            (1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4) -
          (1 - x) ^ 2 * (1 - c * x ^ 2 * s) *
            (-2 * c * (2 * x) * s + c ^ 2 * (4 * x ^ 3)) < 0 := by
      rw [hfactor]
      exact mul_neg_of_pos_of_neg
        (mul_pos (by norm_num) (sub_pos.mpr hx.2)) hinner
    have hden' : 0 < 1 - 2 * c * x ^ 2 * s + c ^ 2 * x ^ 4 := by
      dsimp [D, b] at hD
      convert hD using 1
      all_goals ring
    have hderiv := hasDerivAt_causalDepthRadialRealPart (c := c) (s := s) hden'.ne'
    rw [hderiv.deriv]
    exact div_neg_of_neg_of_pos hnumDeriv (sq_pos_of_pos hden')

/-! Source specialization. -/

def suzukiCriticalApertureDepthFusionBaseRadius (p : Nat.Primes) : ℝ :=
  Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ))

def suzukiCriticalApertureDepthFusionDiskCoordinate
    (h a : ℝ) (p : Nat.Primes) : ℝ :=
  xiMobiusContinuousApertureDiskNode ((h / 2) * a) p

def suzukiCriticalApertureDepthFusionBaseAmplitude
    (h : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt
      (Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, 0) : ℝ) *
        Real.exp ((1 / 2 : ℝ) *
          Real.log (xiGammaEulerValuationNat (p, 0) : ℝ))) *
    (h * Real.sqrt h)⁻¹ *
      (xiTransversePrimeApertureDiskNode 1 p /
        (1 + xiTransversePrimeApertureDiskNode 1 p))

/-- Positive depth-zero Gamma--Euler boundary amplitude which supplies the source demodulator. -/
def suzukiCriticalDepthZeroGammaBoundaryAmplitude (p : Nat.Primes) : ℝ :=
  Real.sqrt
    (Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, 0) : ℝ) *
      Real.exp ((1 / 2 : ℝ) *
        Real.log (xiGammaEulerValuationNat (p, 0) : ℝ)))

def suzukiCriticalApertureDepthFusedDemodulatedAtom
    (h a t : ℝ) (p : Nat.Primes) : ℂ :=
  star (suzukiCriticalApertureDepthFusionPhase t p) *
    suzukiCriticalApertureDepthFusedAtom h a t p

theorem suzukiCriticalApertureDepthFusionBaseRadius_pos (p : Nat.Primes) :
    0 < suzukiCriticalApertureDepthFusionBaseRadius p := by
  exact Real.exp_pos _

theorem suzukiCriticalApertureDepthFusionBaseRadius_lt_one (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionBaseRadius p < 1 := by
  rw [suzukiCriticalApertureDepthFusionBaseRadius, Real.exp_lt_one_iff]
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  nlinarith

theorem suzukiCriticalApertureDepthFusionDiskCoordinate_pos
    (h a : ℝ) (p : Nat.Primes) :
    0 < suzukiCriticalApertureDepthFusionDiskCoordinate h a p := by
  exact xiMobiusContinuousApertureDiskNode_pos _ p

theorem suzukiCriticalApertureDepthFusionDiskCoordinate_lt_one
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionDiskCoordinate h a p < 1 := by
  exact xiMobiusContinuousApertureDiskNode_lt_one
    (mul_pos (half_pos hh) ha) p

theorem suzukiCriticalApertureDepthFusionDiskCoordinate_strictAnti
    {h a b : ℝ} (hh : 0 < h) (hab : a < b) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionDiskCoordinate h b p <
      suzukiCriticalApertureDepthFusionDiskCoordinate h a p := by
  rw [suzukiCriticalApertureDepthFusionDiskCoordinate,
    suzukiCriticalApertureDepthFusionDiskCoordinate,
    xiMobiusContinuousApertureDiskNode,
    xiMobiusContinuousApertureDiskNode, Real.exp_lt_exp]
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hmul := mul_lt_mul_of_pos_right hab (mul_pos (half_pos hh) hp)
  calc
    -(h / 2 * b) * Real.log (p : ℝ) =
        -(b * ((h / 2) * Real.log (p : ℝ))) := by ring
    _ < -(a * ((h / 2) * Real.log (p : ℝ))) := neg_lt_neg hmul
    _ = -(h / 2 * a) * Real.log (p : ℝ) := by ring

theorem suzukiCriticalApertureDepthFusionBaseAmplitude_pos
    {h : ℝ} (hh : 0 < h) (p : Nat.Primes) :
    0 < suzukiCriticalApertureDepthFusionBaseAmplitude h p := by
  rw [suzukiCriticalApertureDepthFusionBaseAmplitude]
  have hn : 0 < xiGammaEulerValuationNat (p, 0) := pow_pos p.property.pos _
  have hdensity : 0 <
      Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, 0) : ℝ) *
        Real.exp ((1 / 2 : ℝ) * Real.log (xiGammaEulerValuationNat (p, 0) : ℝ)) := by
    exact mul_pos
      (div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
        (by exact_mod_cast hn)) (Real.exp_pos _)
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  exact mul_pos
    (mul_pos (Real.sqrt_pos.2 hdensity)
      (inv_pos.mpr (mul_pos hh (Real.sqrt_pos.2 hh))))
    (div_pos hq (by linarith))

theorem suzukiCriticalDepthZeroGammaBoundaryAmplitude_pos (p : Nat.Primes) :
    0 < suzukiCriticalDepthZeroGammaBoundaryAmplitude p := by
  rw [suzukiCriticalDepthZeroGammaBoundaryAmplitude]
  have hn : 0 < xiGammaEulerValuationNat (p, 0) := pow_pos p.property.pos _
  exact Real.sqrt_pos.2
    (mul_pos
      (div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
        (by exact_mod_cast hn))
      (Real.exp_pos _))

/-- The required half-prime-log demodulator is the literal depth-zero Gamma--Euler boundary
coordinate, up to a strictly positive source amplitude. -/
theorem xiGammaEulerHeightBoundaryFeature_critical_depth_zero_eq_amplitude_mul_star_phase
    (t : ℝ) (p : Nat.Primes) :
    xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0) =
      (suzukiCriticalDepthZeroGammaBoundaryAmplitude p : ℂ) *
        star (suzukiCriticalApertureDepthFusionPhase t p) := by
  rw [xiGammaEulerHeightBoundaryFeature,
    suzukiCriticalDepthZeroGammaBoundaryAmplitude,
    suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue]
  simp only [xiGammaEulerValuationNat, zero_add, pow_one]
  simp only [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num]
  congr 1
  change Complex.exp _ = conj (Complex.exp _)
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem suzukiCriticalEntryWallEndpointAmplitude_zero_eq_base_mul_disk
    (h a : ℝ) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 =
      suzukiCriticalApertureDepthFusionBaseAmplitude h p *
        (1 - suzukiCriticalApertureDepthFusionDiskCoordinate h a p) ^ 2 := by
  rw [suzukiCriticalEntryWallEndpointAmplitude,
    suzukiCriticalApertureDepthFusionBaseAmplitude,
    xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature,
    suzukiCriticalApertureDepthFusionDiskCoordinate]
  simp only [pow_zero, mul_one]
  ring

theorem suzukiCriticalApertureDepthFusionRadius_eq_base_mul_disk
    (h a : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionRadius h a p =
      suzukiCriticalApertureDepthFusionBaseRadius p *
        suzukiCriticalApertureDepthFusionDiskCoordinate h a p ^ 2 := by
  rfl

theorem suzukiCriticalApertureDepthFusedDemodulatedAtom_eq_radial
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusedDemodulatedAtom h a t p =
      (suzukiCriticalApertureDepthFusionBaseAmplitude h p : ℂ) *
        ((1 - suzukiCriticalApertureDepthFusionDiskCoordinate h a p) ^ 2 : ℝ) *
        (1 - (suzukiCriticalApertureDepthFusionBaseRadius p : ℂ) *
          suzukiCriticalApertureDepthFusionDiskCoordinate h a p ^ 2 *
            suzukiCriticalApertureDepthFusionPhase t p)⁻¹ := by
  rw [suzukiCriticalApertureDepthFusedDemodulatedAtom,
    suzukiCriticalApertureDepthFusedAtom_eq_mobius hh ha,
    suzukiCriticalEntryWallEndpointAmplitude_zero_eq_base_mul_disk,
    suzukiCriticalApertureDepthFusionRadius_eq_base_mul_disk]
  have hz : star (suzukiCriticalApertureDepthFusionPhase t p) *
      suzukiCriticalApertureDepthFusionPhase t p = 1 := by
    change (starRingEnd ℂ) (suzukiCriticalApertureDepthFusionPhase t p) *
      suzukiCriticalApertureDepthFusionPhase t p = 1
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
      suzukiCriticalApertureDepthFusionPhase, HTGeometry.norm_phaseClockValue]
    norm_num
  push_cast
  calc
    star (suzukiCriticalApertureDepthFusionPhase t p) *
        ((suzukiCriticalApertureDepthFusionBaseAmplitude h p : ℂ) *
            (1 - (suzukiCriticalApertureDepthFusionDiskCoordinate h a p : ℂ)) ^ 2 *
          suzukiCriticalApertureDepthFusionPhase t p *
            (1 -
              (suzukiCriticalApertureDepthFusionBaseRadius p : ℂ) *
                (suzukiCriticalApertureDepthFusionDiskCoordinate h a p : ℂ) ^ 2 *
                  suzukiCriticalApertureDepthFusionPhase t p)⁻¹) =
        (suzukiCriticalApertureDepthFusionBaseAmplitude h p : ℂ) *
          (1 - (suzukiCriticalApertureDepthFusionDiskCoordinate h a p : ℂ)) ^ 2 *
            (star (suzukiCriticalApertureDepthFusionPhase t p) *
              suzukiCriticalApertureDepthFusionPhase t p) *
                (1 -
                  (suzukiCriticalApertureDepthFusionBaseRadius p : ℂ) *
                    (suzukiCriticalApertureDepthFusionDiskCoordinate h a p : ℂ) ^ 2 *
                      suzukiCriticalApertureDepthFusionPhase t p)⁻¹ := by ring
    _ = _ := by rw [hz]; ring

private theorem re_causalDepthRadialTransfer_exp
    (c x θ : ℝ) :
    (((((1 - x) ^ 2 : ℝ) : ℂ) *
      (1 - ((c * x ^ 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I))⁻¹).re) =
      causalDepthRadialRealPart c (Real.cos θ) x := by
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.inv_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.normSq_apply, Complex.sub_im,
    Complex.one_im, Complex.mul_im, zero_sub, mul_one]
  simp only [zero_add]
  rw [causalDepthRadialRealPart]
  have hden :
      (1 - c * x ^ 2 * Real.cos θ) * (1 - c * x ^ 2 * Real.cos θ) +
          (-(c * x ^ 2 * Real.sin θ)) * (-(c * x ^ 2 * Real.sin θ)) =
        1 - 2 * c * x ^ 2 * Real.cos θ + c ^ 2 * x ^ 4 := by
    calc
      _ = 1 - 2 * c * x ^ 2 * Real.cos θ +
          c ^ 2 * x ^ 4 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring
  rw [hden]
  ring

theorem re_suzukiCriticalApertureDepthFusedDemodulatedAtom_eq_radial
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    (suzukiCriticalApertureDepthFusedDemodulatedAtom h a t p).re =
      suzukiCriticalApertureDepthFusionBaseAmplitude h p *
        causalDepthRadialRealPart
          (suzukiCriticalApertureDepthFusionBaseRadius p)
          (Real.cos (t * Real.log (p : ℝ) / 2))
          (suzukiCriticalApertureDepthFusionDiskCoordinate h a p) := by
  rw [suzukiCriticalApertureDepthFusedDemodulatedAtom_eq_radial hh ha]
  rw [suzukiCriticalApertureDepthFusionPhase, HTGeometry.phaseClockValue]
  have hθ : Real.log (p : ℝ) * (t / 2) = t * Real.log (p : ℝ) / 2 := by ring
  rw [hθ]
  have hre := re_causalDepthRadialTransfer_exp
    (suzukiCriticalApertureDepthFusionBaseRadius p)
    (suzukiCriticalApertureDepthFusionDiskCoordinate h a p)
    (t * Real.log (p : ℝ) / 2)
  push_cast at hre ⊢
  rw [mul_assoc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]

theorem re_suzukiCriticalApertureDepthFusedDemodulatedAtom_strictMono
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hab : a < b)
    (t : ℝ) (p : Nat.Primes) :
    (suzukiCriticalApertureDepthFusedDemodulatedAtom h a t p).re <
      (suzukiCriticalApertureDepthFusedDemodulatedAtom h b t p).re := by
  have hb : 0 < b := ha.trans hab
  rw [re_suzukiCriticalApertureDepthFusedDemodulatedAtom_eq_radial hh ha,
    re_suzukiCriticalApertureDepthFusedDemodulatedAtom_eq_radial hh hb]
  apply mul_lt_mul_of_pos_left _
    (suzukiCriticalApertureDepthFusionBaseAmplitude_pos hh p)
  apply causalDepthRadialRealPart_strictAntiOn
    (suzukiCriticalApertureDepthFusionBaseRadius_pos p)
    (suzukiCriticalApertureDepthFusionBaseRadius_lt_one p)
    (Real.cos_le_one _)
  · exact ⟨suzukiCriticalApertureDepthFusionDiskCoordinate_pos h b p,
      suzukiCriticalApertureDepthFusionDiskCoordinate_lt_one hh hb p⟩
  · exact ⟨suzukiCriticalApertureDepthFusionDiskCoordinate_pos h a p,
      suzukiCriticalApertureDepthFusionDiskCoordinate_lt_one hh ha p⟩
  · exact suzukiCriticalApertureDepthFusionDiskCoordinate_strictAnti hh hab p

theorem re_suzukiCriticalApertureDepthFusedAtom_rectangle_demodulated_pos
    {h a L : ℝ} (hh : 0 < h) (ha : 0 < a) (hL : 0 < L)
    (t : ℝ) (p : Nat.Primes) :
    0 < (star (suzukiCriticalApertureDepthFusionPhase t p) *
      (suzukiCriticalApertureDepthFusedAtom h (a + L) t p -
        suzukiCriticalApertureDepthFusedAtom h a t p)).re := by
  have hmono := re_suzukiCriticalApertureDepthFusedDemodulatedAtom_strictMono
    hh ha (lt_add_of_pos_right a hL) t p
  rw [suzukiCriticalApertureDepthFusedDemodulatedAtom,
    suzukiCriticalApertureDepthFusedDemodulatedAtom] at hmono
  rw [mul_sub, Complex.sub_re]
  exact sub_pos.mpr hmono

/-- Pairing the causal aperture rectangle with the actual unstarred depth-zero Gamma--Euler
boundary coordinate is exactly positive source amplitude times the demodulated rectangle. -/
theorem xiGammaEulerHeightBoundaryFeature_mul_fusedAtom_rectangle_eq_boundaryAmplitude_mul_demodulated
    (h a L t : ℝ) (p : Nat.Primes) :
    xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0) *
        (suzukiCriticalApertureDepthFusedAtom h (a + L) t p -
          suzukiCriticalApertureDepthFusedAtom h a t p) =
      (suzukiCriticalDepthZeroGammaBoundaryAmplitude p : ℂ) *
        (star (suzukiCriticalApertureDepthFusionPhase t p) *
          (suzukiCriticalApertureDepthFusedAtom h (a + L) t p -
            suzukiCriticalApertureDepthFusedAtom h a t p)) := by
  rw [xiGammaEulerHeightBoundaryFeature_critical_depth_zero_eq_amplitude_mul_star_phase]
  ring

/-- **Gamma-boundary rectangular Carathéodory growth.**  The source-selected Gamma--Euler
boundary pairing has strictly positive real part on every positive observer rectangle. -/
theorem re_xiGammaEulerHeightBoundaryFeature_mul_fusedAtom_rectangle_pos
    {h a L : ℝ} (hh : 0 < h) (ha : 0 < a) (hL : 0 < L)
    (t : ℝ) (p : Nat.Primes) :
    0 < (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0) *
      (suzukiCriticalApertureDepthFusedAtom h (a + L) t p -
        suzukiCriticalApertureDepthFusedAtom h a t p)).re := by
  rw [xiGammaEulerHeightBoundaryFeature_mul_fusedAtom_rectangle_eq_boundaryAmplitude_mul_demodulated]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (suzukiCriticalDepthZeroGammaBoundaryAmplitude_pos p)
    (re_suzukiCriticalApertureDepthFusedAtom_rectangle_demodulated_pos hh ha hL t p)

end

end RHTower
