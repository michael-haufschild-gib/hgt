import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveDefectBoundary
import GaloisForLFunctions.HTGeometry.ApertureFourierPairing
import GaloisForLFunctions.HTGeometry.LowerBoundedSourceResolvent

/-!
# The negative-shift escape of the finite-aperture Livšic carrier

Suzuki's finite-aperture carrier is built from the deficiency vector `v = (A - λ)⁻¹ exp` of a
lower-bounded self-adjoint operator `A` on `L²(-a, a)`, through the Fourier pairing

`F_v (z) = ∫_{-a}^{a} v x exp (i z x) dx`,   `Θ_v (z) = ((z - i) F_v z) / ((z + i) F_v (-z))`.

The admissible shift range `λ < inf spec A` is a half-line, and its far end is universal: as
`λ → -∞` the normalized resolvent forgets `A` entirely and `-λ v` converges in `L²(-a, a)` to
`exp`.  Since `Θ` is invariant under a common nonzero rescaling of the two channels, the carrier
converges to the free-interval carrier

`Θ_a^free (z) = (exp (-2a) - exp (2 i a z)) / (1 - exp (-2a) exp (2 i a z))`,

which itself tends to zero locally uniformly as the aperture grows.

The consequence proved here is exact: along every cofinal aperture sequence one can choose
admissible shifts so negative that the carriers converge to the zero Schur function locally
uniformly on the upper half-plane.  Hence noncollapse cannot hold uniformly over the admissible
shift half-line.  No spectral theorem, no numerical estimate, and no RH input occur.
-/

namespace GaloisForLFunctions.RHTower

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The carrier of an aperture density -/

/-- The finite-aperture Livšic carrier of a square-integrable deficiency density. -/
def suzukiApertureCarrier (a : ℝ) (v : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) : ℂ :=
  suzukiLivsicQuotient (suzukiFourierNumerator (apertureFourier a v))
    (suzukiFourierDenominator (apertureFourier a v)) z

theorem suzukiApertureCarrier_eq (a : ℝ) (v : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) :
    suzukiApertureCarrier a v z =
      ((z - I) * apertureFourier a v z) / ((z + I) * apertureFourier a v (-z)) := rfl

theorem apertureFourier_smul (a : ℝ) (c : ℂ) (v : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) :
    apertureFourier a (c • v) z = c * apertureFourier a v z := by
  rw [apertureFourier, apertureFourier, inner_smul_right]

/-- **Projective invariance.**  A common nonzero rescaling of the density is invisible to the
carrier. -/
theorem suzukiApertureCarrier_smul (a : ℝ) {c : ℂ} (hc : c ≠ 0)
    (v : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) :
    suzukiApertureCarrier a (c • v) z = suzukiApertureCarrier a v z := by
  rw [suzukiApertureCarrier_eq, suzukiApertureCarrier_eq, apertureFourier_smul,
    apertureFourier_smul]
  rw [show (z - I) * (c * apertureFourier a v z) = c * ((z - I) * apertureFourier a v z) by ring,
    show (z + I) * (c * apertureFourier a v (-z)) = c * ((z + I) * apertureFourier a v (-z)) by
      ring]
  exact mul_div_mul_left _ _ hc

/-! ## The free carrier -/

theorem apertureFourier_apertureExp_norm_lower (a : ℝ) (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) :
    Real.exp (a * (1 + z.im)) - Real.exp (-(a * (1 + z.im)))
      ≤ ‖1 - I * z‖ * ‖apertureFourier a (apertureExp a) (-z)‖ := by
  have hw : (1 : ℂ) + I * (-z) ≠ 0 := by
    intro h
    have him : (1 - I * z).re = 1 + z.im := by simp [Complex.mul_re]
    have : ((1 : ℂ) - I * z) = 0 := by
      rw [show (1 : ℂ) - I * z = 1 + I * (-z) by ring]; exact h
    rw [this] at him
    simp at him
    linarith
  have hform := apertureFourier_apertureExp_eq a ha.le hw
  have hsub : (1 : ℂ) + I * (-z) = 1 - I * z := by ring
  rw [hsub] at hform
  rw [hform, norm_div, mul_div_cancel₀ _ (by
    intro h
    rw [hsub] at hw
    exact hw (by simpa using (norm_eq_zero.mp h)))]
  refine le_trans ?_ (norm_sub_norm_le _ _)
  have h1 : ‖Complex.exp ((1 - I * z) * (a : ℂ))‖ = Real.exp (a * (1 + z.im)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have h2 : ‖Complex.exp (-((1 - I * z) * (a : ℂ)))‖ = Real.exp (-(a * (1 + z.im))) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [h1, h2]

/-- The exact scalar identity behind the free carrier: after the Cayley factors cancel the two
Fourier channels, the finite-aperture quotient is the free-interval Möbius ratio. -/
theorem free_carrier_algebra {p t Q E : ℂ} (hp : p ≠ 0) (ht : t ≠ 0)
    (hQ : Q = p⁻¹ * p⁻¹) (hE : E = t * t)
    (hd1 : p * t⁻¹ - p⁻¹ * t ≠ 0) (hd2 : 1 - Q * E ≠ 0) :
    (-I * (p * t - (p * t)⁻¹)) / (I * (p * t⁻¹ - p⁻¹ * t)) = (Q - E) / (1 - Q * E) := by
  subst hQ
  subst hE
  rw [show (-I) * (p * t - (p * t)⁻¹) = I * (-(p * t - (p * t)⁻¹)) by ring,
    mul_div_mul_left _ _ Complex.I_ne_zero, div_eq_div_iff hd1 hd2]
  field_simp
  ring

theorem one_add_I_mul_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : (1 : ℂ) + I * (-z) ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) + I * (-z)).re = 0 := by rw [h]; simp
  simp [Complex.add_re, Complex.mul_re] at hre
  linarith

theorem one_add_I_mul_ne_zero_of_ne_I {z : ℂ} (hz : z ≠ I) : (1 : ℂ) + I * z ≠ 0 := by
  intro h
  apply hz
  have hre : ((1 : ℂ) + I * z).re = 0 := by rw [h]; simp
  have him : ((1 : ℂ) + I * z).im = 0 := by rw [h]; simp
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im] at hre him
  refine Complex.ext ?_ ?_
  · simpa using him
  · simp only [Complex.I_im]
    linarith

/-- **The far-negative limit carrier is the free-interval carrier.**  The Fourier transform of the
free density `exp x` produces exactly Suzuki's universal free representative. -/
theorem suzukiApertureCarrier_apertureExp (a : ℝ) (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    suzukiApertureCarrier a (apertureExp a) z = suzukiFreeLivsic a z := by
  by_cases hI : z = I
  · subst hI
    rw [suzukiApertureCarrier_eq, suzukiFreeLivsic_I_eq_zero]
    simp
  have hw : (1 : ℂ) + I * z ≠ 0 := one_add_I_mul_ne_zero_of_ne_I hI
  have hw' : (1 : ℂ) + I * (-z) ≠ 0 := one_add_I_mul_ne_zero_of_im_pos hz
  have hp0 : Complex.exp ((a : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have ht0 : Complex.exp (I * (a : ℂ) * z) ≠ 0 := Complex.exp_ne_zero _
  have e1 : Complex.exp ((1 + I * z) * (a : ℂ))
      = Complex.exp ((a : ℂ)) * Complex.exp (I * (a : ℂ) * z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-((1 + I * z) * (a : ℂ)))
      = (Complex.exp ((a : ℂ)) * Complex.exp (I * (a : ℂ) * z))⁻¹ := by
    rw [Complex.exp_neg, e1]
  have e3 : Complex.exp ((1 + I * (-z)) * (a : ℂ))
      = Complex.exp ((a : ℂ)) * (Complex.exp (I * (a : ℂ) * z))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
  have e4 : Complex.exp (-((1 + I * (-z)) * (a : ℂ)))
      = (Complex.exp ((a : ℂ)))⁻¹ * Complex.exp (I * (a : ℂ) * z) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
  -- the denominator of the free channel does not vanish
  have hgap : 0 < Real.exp (a * (1 + z.im)) - Real.exp (-(a * (1 + z.im))) := by
    have : -(a * (1 + z.im)) < a * (1 + z.im) := by nlinarith
    linarith [Real.exp_lt_exp.mpr this]
  have hlower := apertureFourier_apertureExp_norm_lower a ha hz.le
  have hFne : apertureFourier a (apertureExp a) (-z) ≠ 0 := by
    intro h
    rw [h] at hlower
    simp at hlower
    nlinarith
  have hd1 : Complex.exp ((a : ℂ)) * (Complex.exp (I * (a : ℂ) * z))⁻¹
      - (Complex.exp ((a : ℂ)))⁻¹ * Complex.exp (I * (a : ℂ) * z) ≠ 0 := by
    intro h
    apply hFne
    rw [apertureFourier_apertureExp_eq a ha.le hw', e3, e4, h, zero_div]
  -- the free Möbius denominator does not vanish
  have hQE : ‖((Real.exp (-2 * a) : ℝ) : ℂ) * Complex.exp (2 * I * (a : ℂ) * z)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      norm_suzukiFreeOscillator]
    have h1 : Real.exp (-2 * a) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    have h2 : Real.exp (-2 * a * z.im) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith [Real.exp_pos (-2 * a), Real.exp_pos (-2 * a * z.im)]
  have hd2 : (1 : ℂ) - ((Real.exp (-2 * a) : ℝ) : ℂ) * Complex.exp (2 * I * (a : ℂ) * z) ≠ 0 := by
    intro h
    have : ((Real.exp (-2 * a) : ℝ) : ℂ) * Complex.exp (2 * I * (a : ℂ) * z) = 1 := by
      linear_combination -h
    rw [this] at hQE
    simp at hQE
  -- identify the two constants
  have hQ : ((Real.exp (-2 * a) : ℝ) : ℂ)
      = (Complex.exp ((a : ℂ)))⁻¹ * (Complex.exp ((a : ℂ)))⁻¹ := by
    rw [Complex.ofReal_exp, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hE : Complex.exp (2 * I * (a : ℂ) * z)
      = Complex.exp (I * (a : ℂ) * z) * Complex.exp (I * (a : ℂ) * z) := by
    rw [← Complex.exp_add]; congr 1; ring
  -- assemble
  rw [suzukiApertureCarrier_eq, apertureFourier_apertureExp_eq a ha.le hw,
    apertureFourier_apertureExp_eq a ha.le hw', e1, e2, e3, e4, suzukiFreeLivsic]
  have hnum : (z - I) * ((Complex.exp ((a : ℂ)) * Complex.exp (I * (a : ℂ) * z)
        - (Complex.exp ((a : ℂ)) * Complex.exp (I * (a : ℂ) * z))⁻¹) / (1 + I * z))
      = -I * (Complex.exp ((a : ℂ)) * Complex.exp (I * (a : ℂ) * z)
        - (Complex.exp ((a : ℂ)) * Complex.exp (I * (a : ℂ) * z))⁻¹) := by
    rw [show z - I = -I * (1 + I * z) by linear_combination (z : ℂ) * Complex.I_mul_I]
    field_simp
  have hden : (z + I) * ((Complex.exp ((a : ℂ)) * (Complex.exp (I * (a : ℂ) * z))⁻¹
        - (Complex.exp ((a : ℂ)))⁻¹ * Complex.exp (I * (a : ℂ) * z)) / (1 + I * (-z)))
      = I * (Complex.exp ((a : ℂ)) * (Complex.exp (I * (a : ℂ) * z))⁻¹
        - (Complex.exp ((a : ℂ)))⁻¹ * Complex.exp (I * (a : ℂ) * z)) := by
    rw [show z + I = I * (1 + I * (-z)) by linear_combination (z : ℂ) * Complex.I_mul_I,
      mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hw']
  rw [hnum, hden]
  exact free_carrier_algebra hp0 ht0 hQ hE hd1 hd2

/-! ## Explicit strip estimates -/

/-- The explicit lower bound for the reflected free channel on the strip `η ≤ Im z`,
`‖z‖ ≤ R`. -/
def freeDenomLower (a η R : ℝ) : ℝ :=
  (Real.exp (a * (1 + η)) - Real.exp (-(a * (1 + η)))) / (1 + R)

theorem freeDenomLower_pos {a η R : ℝ} (ha : 0 < a) (hη : 0 ≤ η) (hR : 0 ≤ R) :
    0 < freeDenomLower a η R := by
  have hpos : 0 < a * (1 + η) := by nlinarith
  have hlt : Real.exp (-(a * (1 + η))) < Real.exp (a * (1 + η)) :=
    Real.exp_lt_exp.mpr (by linarith)
  exact div_pos (by linarith) (by linarith)

theorem norm_freeDenominator_ge {a η R : ℝ} (ha : 0 < a) (hη : 0 ≤ η) (hR : 0 ≤ R)
    {z : ℂ} (hz1 : η ≤ z.im) (hz2 : ‖z‖ ≤ R) :
    freeDenomLower a η R ≤ ‖(z + I) * apertureFourier a (apertureExp a) (-z)‖ := by
  have hzim : 0 ≤ z.im := le_trans hη hz1
  have hlower := apertureFourier_apertureExp_norm_lower a ha hzim
  have hmono : Real.exp (a * (1 + η)) - Real.exp (-(a * (1 + η)))
      ≤ Real.exp (a * (1 + z.im)) - Real.exp (-(a * (1 + z.im))) := by
    have hle : a * (1 + η) ≤ a * (1 + z.im) := by nlinarith
    have h1 : Real.exp (a * (1 + η)) ≤ Real.exp (a * (1 + z.im)) := Real.exp_monotone hle
    have h2 : Real.exp (-(a * (1 + z.im))) ≤ Real.exp (-(a * (1 + η))) :=
      Real.exp_monotone (by linarith)
    linarith
  have hw : ‖(1 : ℂ) - I * z‖ ≤ 1 + R := by
    refine le_trans (norm_sub_le _ _) ?_
    have : ‖I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [this, norm_one]
    linarith
  have hFnn : 0 ≤ ‖apertureFourier a (apertureExp a) (-z)‖ := norm_nonneg _
  have hchain : Real.exp (a * (1 + η)) - Real.exp (-(a * (1 + η)))
      ≤ (1 + R) * ‖apertureFourier a (apertureExp a) (-z)‖ := by
    refine le_trans (le_trans hmono hlower) ?_
    exact mul_le_mul_of_nonneg_right hw hFnn
  have hFge : freeDenomLower a η R ≤ ‖apertureFourier a (apertureExp a) (-z)‖ := by
    rw [freeDenomLower, div_le_iff₀ (by linarith : (0:ℝ) < 1 + R)]
    linarith [hchain]
  have hzI : (1 : ℝ) ≤ ‖z + I‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm (z + I))
    have : (z + I).im = z.im + 1 := by simp
    rw [this, abs_of_nonneg (by linarith)]
    linarith
  rw [norm_mul]
  calc freeDenomLower a η R ≤ ‖apertureFourier a (apertureExp a) (-z)‖ := hFge
    _ = 1 * ‖apertureFourier a (apertureExp a) (-z)‖ := (one_mul _).symm
    _ ≤ ‖z + I‖ * ‖apertureFourier a (apertureExp a) (-z)‖ :=
        mul_le_mul_of_nonneg_right hzI hFnn

/-- The explicit majorant of the free carrier on the closed upper half-plane. -/
def freeCarrierBound (a : ℝ) : ℝ := 2 / (1 - Real.exp (-2 * a))

theorem freeCarrierBound_pos {a : ℝ} (ha : 0 < a) : 0 < freeCarrierBound a := by
  have h : Real.exp (-2 * a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  exact div_pos (by norm_num) (by linarith)

theorem norm_suzukiFreeLivsic_le_bound {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖suzukiFreeLivsic a z‖ ≤ freeCarrierBound a := by
  have hq : ‖((Real.exp (-2 * a) : ℝ) : ℂ)‖ = Real.exp (-2 * a) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hb : ‖Complex.exp (2 * I * (a : ℂ) * z)‖ = Real.exp (-2 * a * z.im) :=
    norm_suzukiFreeOscillator a z
  have hq1 : Real.exp (-2 * a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hb1 : Real.exp (-2 * a * z.im) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  have hnum : ‖((Real.exp (-2 * a) : ℝ) : ℂ) - Complex.exp (2 * I * (a : ℂ) * z)‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [hq, hb]
    linarith
  have hprod : ‖((Real.exp (-2 * a) : ℝ) : ℂ) * Complex.exp (2 * I * (a : ℂ) * z)‖
      ≤ Real.exp (-2 * a) := by
    rw [norm_mul, hq, hb]
    nlinarith [Real.exp_pos (-2 * a), Real.exp_pos (-2 * a * z.im)]
  have hden : 1 - Real.exp (-2 * a)
      ≤ ‖1 - ((Real.exp (-2 * a) : ℝ) : ℂ) * Complex.exp (2 * I * (a : ℂ) * z)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (((Real.exp (-2 * a) : ℝ) : ℂ)
      * Complex.exp (2 * I * (a : ℂ) * z))
    rw [norm_one] at this
    linarith
  rw [suzukiFreeLivsic, norm_div, freeCarrierBound, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [norm_nonneg (((Real.exp (-2 * a) : ℝ) : ℂ) - Complex.exp (2 * I * (a : ℂ) * z))]

/-- The Cauchy–Schwarz transfer constant of the aperture window at radius `R`. -/
def carrierTransfer (a R : ℝ) : ℝ := (R + 1) * apertureWindow a * Real.exp (R * a) + 1

theorem carrierTransfer_pos {a R : ℝ} (hR : 0 ≤ R) : 0 < carrierTransfer a R := by
  have h : 0 ≤ (R + 1) * apertureWindow a * Real.exp (R * a) := by
    have := apertureWindow_nonneg a
    have := (Real.exp_pos (R * a)).le
    positivity
  rw [carrierTransfer]
  linarith

theorem norm_channel_sub_le {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (v : Lp ℂ 2 (apertureMeasure a)) {c z : ℂ} (hc : ‖c‖ ≤ R + 1) (hz : ‖z‖ ≤ R) :
    ‖c * apertureFourier a v z - c * apertureFourier a (apertureExp a) z‖
      ≤ carrierTransfer a R * ‖v - apertureExp a‖ := by
  have him : |z.im| ≤ R := le_trans (Complex.abs_im_le_norm z) hz
  have hcs := norm_apertureFourier_sub_le_of_im_bound (M := R) v (apertureExp a) him ha
  have hstep : ‖c * apertureFourier a v z - c * apertureFourier a (apertureExp a) z‖
      = ‖c‖ * ‖apertureFourier a v z - apertureFourier a (apertureExp a) z‖ := by
    rw [← mul_sub, norm_mul]
  rw [hstep]
  have h1 : ‖c‖ * ‖apertureFourier a v z - apertureFourier a (apertureExp a) z‖
      ≤ (R + 1) * (apertureWindow a * Real.exp (R * a) * ‖v - apertureExp a‖) := by
    refine mul_le_mul hc hcs (norm_nonneg _) (by linarith)
  refine le_trans h1 ?_
  have hnn : 0 ≤ ‖v - apertureExp a‖ := norm_nonneg _
  rw [carrierTransfer]
  nlinarith [apertureWindow_nonneg a, (Real.exp_pos (R * a)).le]

/-- The exact three-term decomposition of a quotient perturbation. -/
theorem quotient_perturbation {N₀ D₀ Nv Dv : ℂ} (h0 : D₀ ≠ 0) (hv : Dv ≠ 0) :
    Nv / Dv - N₀ / D₀ = ((Nv - N₀) + (N₀ / D₀) * (D₀ - Dv)) / Dv := by
  field_simp
  ring

/-- **The strip estimate.**  Once the density is close to the free density in `L²`, the carrier
is close to the free carrier uniformly on the strip. -/
theorem norm_suzukiApertureCarrier_sub_free_le
    {a η R : ℝ} (ha : 0 < a) (hη : 0 < η) (hR : 0 ≤ R)
    {v : Lp ℂ 2 (apertureMeasure a)}
    (hsmall : carrierTransfer a R * ‖v - apertureExp a‖ ≤ freeDenomLower a η R / 2)
    {z : ℂ} (hz1 : η ≤ z.im) (hz2 : ‖z‖ ≤ R) :
    ‖suzukiApertureCarrier a v z - suzukiFreeLivsic a z‖
      ≤ 2 * (carrierTransfer a R * ‖v - apertureExp a‖) * (1 + freeCarrierBound a)
          / freeDenomLower a η R := by
  set κ := carrierTransfer a R * ‖v - apertureExp a‖ with hκ
  set c := freeDenomLower a η R with hc
  have hcpos : 0 < c := freeDenomLower_pos ha hη.le hR
  have hzpos : 0 < z.im := lt_of_lt_of_le hη hz1
  have hκnn : 0 ≤ κ := by
    rw [hκ]
    exact mul_nonneg (carrierTransfer_pos hR).le (norm_nonneg _)
  have hzI : ‖z - I‖ ≤ R + 1 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_I]
    linarith
  have hzI' : ‖z + I‖ ≤ R + 1 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_I]
    linarith
  have hnegz : ‖(-z)‖ ≤ R := by rwa [norm_neg]
  have hN : ‖(z - I) * apertureFourier a v z
      - (z - I) * apertureFourier a (apertureExp a) z‖ ≤ κ :=
    norm_channel_sub_le ha.le hR v hzI hz2
  have hD : ‖(z + I) * apertureFourier a v (-z)
      - (z + I) * apertureFourier a (apertureExp a) (-z)‖ ≤ κ :=
    norm_channel_sub_le ha.le hR v hzI' hnegz
  have hD0 : c ≤ ‖(z + I) * apertureFourier a (apertureExp a) (-z)‖ :=
    norm_freeDenominator_ge ha hη.le hR hz1 hz2
  have hDv : c / 2 ≤ ‖(z + I) * apertureFourier a v (-z)‖ := by
    have hrev : ‖(z + I) * apertureFourier a (apertureExp a) (-z)
        - (z + I) * apertureFourier a v (-z)‖ ≤ κ := by rwa [norm_sub_rev]
    have := norm_sub_norm_le ((z + I) * apertureFourier a (apertureExp a) (-z))
      ((z + I) * apertureFourier a v (-z))
    linarith
  have hD0ne : (z + I) * apertureFourier a (apertureExp a) (-z) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hD0
    linarith
  have hDvne : (z + I) * apertureFourier a v (-z) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDv
    linarith
  have hfree : suzukiFreeLivsic a z
      = ((z - I) * apertureFourier a (apertureExp a) z)
        / ((z + I) * apertureFourier a (apertureExp a) (-z)) := by
    rw [← suzukiApertureCarrier_eq]
    exact (suzukiApertureCarrier_apertureExp a ha hzpos).symm
  rw [suzukiApertureCarrier_eq, hfree, quotient_perturbation hD0ne hDvne, norm_div]
  have hBf : ‖suzukiFreeLivsic a z‖ ≤ freeCarrierBound a :=
    norm_suzukiFreeLivsic_le_bound ha hzpos.le
  have hnum : ‖((z - I) * apertureFourier a v z - (z - I) * apertureFourier a (apertureExp a) z)
      + (((z - I) * apertureFourier a (apertureExp a) z
          / ((z + I) * apertureFourier a (apertureExp a) (-z)))
        * ((z + I) * apertureFourier a (apertureExp a) (-z)
          - (z + I) * apertureFourier a v (-z)))‖
      ≤ κ * (1 + freeCarrierBound a) := by
    refine le_trans (norm_add_le _ _) ?_
    have hrev : ‖(z + I) * apertureFourier a (apertureExp a) (-z)
        - (z + I) * apertureFourier a v (-z)‖ ≤ κ := by rwa [norm_sub_rev]
    have hq : ‖(z - I) * apertureFourier a (apertureExp a) z
        / ((z + I) * apertureFourier a (apertureExp a) (-z))‖ ≤ freeCarrierBound a := by
      rw [← hfree]; exact hBf
    have := mul_le_mul hq hrev (norm_nonneg _) (freeCarrierBound_pos ha).le
    rw [norm_mul]
    nlinarith [hN, norm_nonneg ((z - I) * apertureFourier a v z
      - (z - I) * apertureFourier a (apertureExp a) z)]
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < ‖(z + I) * apertureFourier a v (-z)‖) hcpos]
  have hcoef : (0:ℝ) ≤ 2 * κ * (1 + freeCarrierBound a) := by
    have hBn := (freeCarrierBound_pos ha).le
    nlinarith [hκnn]
  nlinarith [mul_le_mul_of_nonneg_right hnum hcpos.le,
    mul_le_mul_of_nonneg_left hDv hcoef]

/-- **Fixed-aperture approach to the free carrier.**  Every tolerance on every bounded strip is
met by all densities close enough to the free density. -/
theorem exists_delta_carrier_close (a η R ε : ℝ) (ha : 0 < a) (hη : 0 < η) (hR : 0 ≤ R)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : Lp ℂ 2 (apertureMeasure a), ‖v - apertureExp a‖ < δ →
      ∀ z : ℂ, η ≤ z.im → ‖z‖ ≤ R →
        ‖suzukiApertureCarrier a v z - suzukiFreeLivsic a z‖ < ε := by
  set T := carrierTransfer a R with hT
  set c := freeDenomLower a η R with hc
  set B := freeCarrierBound a with hB
  have hTpos : 0 < T := carrierTransfer_pos hR
  have hcpos : 0 < c := freeDenomLower_pos ha hη.le hR
  have hBpos : 0 < B := freeCarrierBound_pos ha
  refine ⟨min (c / (2 * T)) (ε * c / (4 * T * (1 + B))), lt_min (by positivity) (by positivity),
    ?_⟩
  intro v hv z hz1 hz2
  have hvnn : 0 ≤ ‖v - apertureExp a‖ := norm_nonneg _
  have hv1 : ‖v - apertureExp a‖ < c / (2 * T) := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v - apertureExp a‖ < ε * c / (4 * T * (1 + B)) :=
    lt_of_lt_of_le hv (min_le_right _ _)
  have hsmall : T * ‖v - apertureExp a‖ ≤ c / 2 := by
    have := mul_lt_mul_of_pos_left hv1 hTpos
    rw [mul_div_assoc'] at this
    have hTne : (2 * T) ≠ 0 := by positivity
    have hrw : T * c / (2 * T) = c / 2 := by field_simp
    rw [hrw] at this
    linarith
  have hmain := norm_suzukiApertureCarrier_sub_free_le ha hη hR hsmall hz1 hz2
  refine lt_of_le_of_lt hmain ?_
  rw [div_lt_iff₀ hcpos]
  have hkey : T * ‖v - apertureExp a‖ * (4 * (1 + B)) < ε * c := by
    have h4 : (0:ℝ) < 4 * T * (1 + B) := by positivity
    have := mul_lt_mul_of_pos_left hv2 hTpos
    have hrw : T * (ε * c / (4 * T * (1 + B))) = ε * c / (4 * (1 + B)) := by
      field_simp
    rw [hrw] at this
    have h5 : (0:ℝ) < 4 * (1 + B) := by positivity
    calc T * ‖v - apertureExp a‖ * (4 * (1 + B))
        < (ε * c / (4 * (1 + B))) * (4 * (1 + B)) :=
          mul_lt_mul_of_pos_right this h5
      _ = ε * c := by field_simp
  nlinarith [hkey, hcpos, hBpos]

/-! ## Escape at a fixed aperture -/

/-- Beyond an explicit shift threshold every deficiency vector of the source produces a carrier
within the prescribed tolerance of the free carrier on the prescribed strip. -/
theorem exists_shift_threshold_carrier_close
    (a η R ε : ℝ) (ha : 0 < a) (hη : 0 < η) (hR : 0 ≤ R) (hε : 0 < ε)
    (S : LowerBoundedSource (Lp ℂ 2 (apertureMeasure a))) :
    ∃ R₀ : ℝ, ∀ r : ℝ, R₀ < r → 0 < r → ∀ x : S.domain,
      S.shift r x = apertureExp a →
      ∀ z : ℂ, η ≤ z.im → ‖z‖ ≤ R →
        ‖suzukiApertureCarrier a (x : Lp ℂ 2 (apertureMeasure a)) z
          - suzukiFreeLivsic a z‖ < ε := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_carrier_close a η R ε ha hη hR hε
  obtain ⟨R₀, hR₀⟩ := S.exists_threshold_norm_smul_sub_lt (apertureExp a) hδpos
  refine ⟨R₀, fun r hr hrpos x hx z hz1 hz2 => ?_⟩
  have hclose : ‖(r : ℂ) • (x : Lp ℂ 2 (apertureMeasure a)) - apertureExp a‖ < δ :=
    hR₀ r hr x hx
  have hrne : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hrpos
  have := hδ ((r : ℂ) • (x : Lp ℂ 2 (apertureMeasure a))) hclose z hz1 hz2
  rwa [suzukiApertureCarrier_smul a hrne] at this

/-! ## The cofinal escape theorem -/

/-- **Negative-shift escape.**  Along every cofinal aperture sequence and for every family of
lower-bounded self-adjoint sources there are admissible shifts, one per aperture and all strictly
below the corresponding spectral floor, whose finite-aperture Livšic carriers converge to the zero
Schur function locally uniformly on the upper half-plane.

Consequently noncollapse and shift independence cannot hold uniformly over the admissible shift
half-line: the far-negative end of that half-line is the universal free boundary. -/
theorem suzuki_negativeShift_escape
    {a : ℕ → ℝ} (hapos : ∀ n, 0 < a n) (ha : Filter.Tendsto a atTop atTop)
    (S : ∀ n, LowerBoundedSource (Lp ℂ 2 (apertureMeasure (a n)))) :
    ∃ lam : ℕ → ℝ, (∀ n, lam n < (S n).floor) ∧
      ∀ x : (n : ℕ) → (S n).domain,
        (∀ n, (S n).shift (-(lam n)) (x n) = apertureExp (a n)) →
        TendstoLocallyUniformlyOn
          (fun n z => suzukiApertureCarrier (a n)
            ((x n : Lp ℂ 2 (apertureMeasure (a n)))) z)
          (fun _ => (0 : ℂ)) atTop {z : ℂ | 0 < z.im} := by
  classical
  -- the threshold produced by the fixed-aperture escape at the `n`-th strip
  have hthr : ∀ n : ℕ, ∃ R₀ : ℝ, ∀ r : ℝ, R₀ < r → 0 < r → ∀ x : (S n).domain,
      (S n).shift r x = apertureExp (a n) →
      ∀ z : ℂ, 1 / ((n : ℝ) + 1) ≤ z.im → ‖z‖ ≤ (n : ℝ) + 1 →
        ‖suzukiApertureCarrier (a n) (x : Lp ℂ 2 (apertureMeasure (a n))) z
          - suzukiFreeLivsic (a n) z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact exists_shift_threshold_carrier_close (a n) (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
      (1 / ((n : ℝ) + 1)) (hapos n) (by positivity) (by positivity) (by positivity) (S n)
  choose R₀ hR₀ using hthr
  set r : ℕ → ℝ := fun n => max (max (R₀ n) |(S n).floor|) 0 + 1 with hrdef
  have hrpos : ∀ n, 0 < r n := by
    intro n
    have : (0 : ℝ) ≤ max (max (R₀ n) |(S n).floor|) 0 := le_max_right _ _
    rw [hrdef]
    linarith
  have hrgt : ∀ n, R₀ n < r n := by
    intro n
    have h1 : R₀ n ≤ max (max (R₀ n) |(S n).floor|) 0 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hrdef]
    linarith
  have hrfloor : ∀ n, -(r n) < (S n).floor := by
    intro n
    have h1 : |(S n).floor| ≤ max (max (R₀ n) |(S n).floor|) 0 :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 : -(S n).floor ≤ |(S n).floor| := neg_le_abs _
    have : -(S n).floor < r n := by rw [hrdef]; linarith
    linarith
  refine ⟨fun n => -(r n), fun n => hrfloor n, ?_⟩
  intro x hx
  have hxr : ∀ n, (S n).shift (r n) (x n) = apertureExp (a n) := by
    intro n
    have := hx n
    rwa [neg_neg] at this
  -- the diagonal estimate against the free carriers
  have hdiag : ∀ n : ℕ, ∀ z : ℂ, 1 / ((n : ℝ) + 1) ≤ z.im → ‖z‖ ≤ (n : ℝ) + 1 →
      ‖suzukiApertureCarrier (a n) ((x n : Lp ℂ 2 (apertureMeasure (a n)))) z
        - suzukiFreeLivsic (a n) z‖ < 1 / ((n : ℝ) + 1) :=
    fun n => hR₀ n (r n) (hrgt n) (hrpos n) (x n) (hxr n)
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change 0 < z.im at hz
  set η : ℝ := z.im / 2 with hηdef
  set Rad : ℝ := ‖z‖ + 1 with hRaddef
  have hη : 0 < η := half_pos hz
  set t : Set ℂ := {w : ℂ | η < w.im} ∩ {w : ℂ | ‖w‖ < Rad} with htdef
  have htOpen : IsOpen t := by
    refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_im) ?_
    exact isOpen_lt continuous_norm continuous_const
  have hzt : z ∈ t := by
    constructor
    · change z.im / 2 < z.im
      linarith
    · change ‖z‖ < ‖z‖ + 1
      linarith
  refine ⟨t, Filter.Eventually.filter_mono nhdsWithin_le_nhds (htOpen.mem_nhds hzt), ?_⟩
  -- uniform convergence of the free carriers along the aperture sequence
  have hfree : TendstoUniformlyOn (fun b : ℝ => suzukiFreeLivsic b) (0 : ℂ → ℂ) atTop
      {w : ℂ | η < w.im} := suzukiFreeLivsic_tendstoUniformlyOn_upperStrip hη
  rw [SeminormedAddGroup.tendstoUniformlyOn_zero] at hfree
  change TendstoUniformlyOn
    (fun n z => suzukiApertureCarrier (a n) ((x n : Lp ℂ 2 (apertureMeasure (a n)))) z)
    (0 : ℂ → ℂ) atTop t
  rw [SeminormedAddGroup.tendstoUniformlyOn_zero]
  intro ε hε
  have hfreeε := ha.eventually (hfree (ε / 2) (by linarith))
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds (by linarith))
  have hstrip : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ η :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_le_nhds hη)
  have hrad : ∀ᶠ n : ℕ in atTop, Rad ≤ (n : ℝ) + 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop Rad] with n hn
    linarith
  filter_upwards [hfreeε, hsmall, hstrip, hrad] with n hn1 hn2 hn3 hn4
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  change η < w.im at hw1
  change ‖w‖ < Rad at hw2
  have hgap := hdiag n w (le_trans hn3 hw1.le) (le_trans hw2.le hn4)
  have hfw : ‖suzukiFreeLivsic (a n) w‖ < ε / 2 := hn1 w hw1
  have hsplit : ‖suzukiApertureCarrier (a n) ((x n : Lp ℂ 2 (apertureMeasure (a n)))) w‖
      ≤ ‖suzukiApertureCarrier (a n) ((x n : Lp ℂ 2 (apertureMeasure (a n)))) w
          - suzukiFreeLivsic (a n) w‖ + ‖suzukiFreeLivsic (a n) w‖ := by
    simpa using norm_add_le
      (suzukiApertureCarrier (a n) ((x n : Lp ℂ 2 (apertureMeasure (a n)))) w
        - suzukiFreeLivsic (a n) w) (suzukiFreeLivsic (a n) w)
  linarith

/-! ## Non-vacuity of the escape hypotheses -/

/-- The zero source on the aperture window solves every positively shifted equation. -/
theorem freeSource_shift_solution (a r : ℝ) (hr : 0 < r) (f : Lp ℂ 2 (apertureMeasure a)) :
    (freeSource (Lp ℂ 2 (apertureMeasure a))).shift r
      ⟨(r : ℂ)⁻¹ • f, Submodule.mem_top⟩ = f := by
  have hr0 : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hr
  have hop : (freeSource (Lp ℂ 2 (apertureMeasure a))).op
      ⟨(r : ℂ)⁻¹ • f, Submodule.mem_top⟩ = 0 := rfl
  rw [LowerBoundedSource.shift, hop, zero_add]
  show (r : ℂ) • ((r : ℂ)⁻¹ • f) = f
  rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]

/-- **The escape hypotheses are satisfiable.**  For the zero source at every aperture the
conclusion of the escape theorem holds with explicitly constructed deficiency vectors. -/
theorem suzuki_negativeShift_escape_freeSource
    {a : ℕ → ℝ} (hapos : ∀ n, 0 < a n) (ha : Filter.Tendsto a atTop atTop) :
    ∃ lam : ℕ → ℝ, (∀ n, lam n < 0) ∧
      TendstoLocallyUniformlyOn
        (fun n z => suzukiApertureCarrier (a n)
          ((((-(lam n) : ℝ)) : ℂ)⁻¹ • apertureExp (a n)) z)
        (fun _ => (0 : ℂ)) atTop {z : ℂ | 0 < z.im} := by
  obtain ⟨lam, hlam, hconv⟩ :=
    suzuki_negativeShift_escape hapos ha (fun n => freeSource (Lp ℂ 2 (apertureMeasure (a n))))
  have hlam0 : ∀ n, lam n < 0 := by
    intro n
    have := hlam n
    simpa using this
  refine ⟨lam, hlam0, ?_⟩
  exact hconv (fun n => ⟨(((-(lam n) : ℝ)) : ℂ)⁻¹ • apertureExp (a n), Submodule.mem_top⟩)
    (fun n => freeSource_shift_solution (a n) (-(lam n)) (by linarith [hlam0 n]) _)

end

end GaloisForLFunctions.RHTower
