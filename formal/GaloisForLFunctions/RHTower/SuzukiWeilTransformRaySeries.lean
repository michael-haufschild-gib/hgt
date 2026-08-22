import GaloisForLFunctions.RHTower.SuzukiWeilPropOneThree

/-!
# Suzuki eq. (3.7): the transform expanded over the Xi zeros

Masatoshi Suzuki, arXiv:2301.00421v3, eq. (3.7): for a test function `phi`,

`Phat_phi(z) = sum over gamma of sqrt(pi m_gamma) ((phihat(gamma) - phihat(0))/gamma) F_gamma(z)`.

The formalized form keeps the divisor multiplicity exact (the index is `XiZeroCopy`) and works with
the conjugate `suzukiPHatConj`, whose spectral points appear *unconjugated*:

`conj(Phat_phi)(z) = (i/2)(1 + Theta^#(z)) * sum over q of
     (integral of (e^{-i gamma_q t} - 1) conj(phi t) dt) / (gamma_q (z - gamma_q))`.

Two things make this legitimate.  The series is **absolutely** convergent — the extra `1/gamma_q`
is exactly what the printed `sum_gamma m_gamma psihat(gamma)/(z-gamma)` of (3.8) lacks — and the
Fubini exchange is dominated because every Xi zero satisfies `|Im gamma| < 1/2`
(`norm_suzukiPtZeroExp_le`), so on the compact support of `phi` the exponential factor is bounded by
`e^{T/2} + 1` uniformly in `q`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## The zero-ray expansion of the transform (Suzuki eq. (3.7)) -/

/-- The conjugated transform: `conj (𝒫̂_φ)` on the real axis.  Working with it keeps every
spectral point unconjugated. -/
def suzukiPHatConj (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, suzukiFrakSFull t z * (starRingEnd ℂ) (φ t)

theorem suzukiPHat_ofReal_eq_conj (φ : ℝ → ℂ) (x : ℝ) :
    suzukiPHat φ ((x : ℝ) : ℂ) = (starRingEnd ℂ) (suzukiPHatConj φ ((x : ℝ) : ℂ)) := by
  have hpt : ∀ t : ℝ, suzukiFrakSSharp t ((x : ℝ) : ℂ) * φ t
      = (starRingEnd ℂ) (suzukiFrakSFull t ((x : ℝ) : ℂ) * (starRingEnd ℂ) (φ t)) := by
    intro t
    rw [suzukiFrakSSharp_ofReal, map_mul, Complex.conj_conj]
  rw [suzukiPHat, suzukiPHatConj, ← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- The `q`-th ray of the transform. -/
def suzukiPHatRayTerm (φ : ℝ → ℂ) (z : ℂ) (q : XiZeroCopy) : ℂ :=
  (∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) (φ t))
    / (xiSpectralPoint q * (z - xiSpectralPoint q))

theorem norm_conj_phi_bound {φ : ℝ → ℂ} {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → φ t = 0)
    (q : XiZeroCopy) (t : ℝ) :
    ‖(Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) (φ t)‖
      ≤ (Real.exp (T / 2) + 1) * ‖φ t‖ := by
  rcases le_or_gt |t| T with h | h
  · have hnum : ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖ ≤ Real.exp (T / 2) + 1 := by
      have h1 := norm_suzukiPtZeroExp_le t q
      have h2 : Real.exp (|t| / 2) ≤ Real.exp (T / 2) := Real.exp_le_exp.mpr (by linarith)
      calc ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖
          ≤ ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ Real.exp (T / 2) + 1 := by simp only [norm_one]; linarith
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
  · rw [hsupp t h]
    simp

theorem integrable_suzukiPHatIntegrand {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : Integrable φ)
    {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) (q : XiZeroCopy) :
    Integrable (fun t : ℝ =>
      (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) (φ t)) := by
  refine Integrable.mono' (hφ.norm.const_mul (Real.exp (T / 2) + 1)) ?_ ?_
  · have h1 : Measurable (fun t : ℝ =>
        (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)) := by fun_prop
    exact (h1.mul (Complex.continuous_conj.measurable.comp hφm)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (norm_conj_phi_bound hsupp q)

theorem integral_suzukiPtZeroSum_mul {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : Integrable φ)
    {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) (z : ℂ) :
    (∫ t : ℝ, suzukiPtZeroSum t z * (starRingEnd ℂ) (φ t))
      = ∑' q : XiZeroCopy, suzukiPHatRayTerm φ z q := by
  have hden : ∀ (q : XiZeroCopy) (t : ℝ),
      suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t)
        = ((Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) (φ t))
          / (xiSpectralPoint q * (z - xiSpectralPoint q)) := by
    intro q t
    rw [suzukiPtZeroTerm]
    ring
  have hint : ∀ q : XiZeroCopy,
      Integrable (fun t : ℝ => suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t)) := by
    intro q
    refine ((integrable_suzukiPHatIntegrand hφm hφ hsupp q).div_const
      (xiSpectralPoint q * (z - xiSpectralPoint q))).congr ?_
    exact Filter.Eventually.of_forall fun t => (hden q t).symm
  have hbound : ∀ (q : XiZeroCopy) (t : ℝ),
      ‖suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t)‖
      ≤ ((Real.exp (T / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖) * ‖φ t‖ := by
    intro q t
    rw [hden q t, norm_div]
    have hrw : ‖xiSpectralPoint q * (z - xiSpectralPoint q)‖
        = ‖(xiSpectralPoint q * (xiSpectralPoint q - z))‖ := by
      rw [show xiSpectralPoint q * (z - xiSpectralPoint q)
          = -(xiSpectralPoint q * (xiSpectralPoint q - z)) by ring, norm_neg]
    rw [hrw]
    rcases eq_or_ne (‖xiSpectralPoint q * (xiSpectralPoint q - z)‖) 0 with h0 | h0
    · rw [h0, norm_inv, h0]
      simp
    · have hpos : (0 : ℝ) < ‖xiSpectralPoint q * (xiSpectralPoint q - z)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [div_le_iff₀ hpos, norm_inv]
      have hnb := norm_conj_phi_bound hsupp q t
      calc ‖(Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) (φ t)‖
          ≤ (Real.exp (T / 2) + 1) * ‖φ t‖ := hnb
        _ = ((Real.exp (T / 2) + 1) * ‖xiSpectralPoint q * (xiSpectralPoint q - z)‖⁻¹ * ‖φ t‖)
              * ‖xiSpectralPoint q * (xiSpectralPoint q - z)‖ := by
            field_simp
  have hsummable : Summable (fun q : XiZeroCopy =>
      ∫ t : ℝ, ‖suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t)‖) := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _)
      (fun q => ?_)
      (((summable_xiResolventProduct_norm z).mul_left (Real.exp (T / 2) + 1)).mul_right
        (∫ t : ℝ, ‖φ t‖))
    calc ∫ t : ℝ, ‖suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t)‖
        ≤ ∫ t : ℝ, ((Real.exp (T / 2) + 1)
            * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖) * ‖φ t‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (hφ.norm.const_mul _) (Filter.Eventually.of_forall (hbound q))
      _ = ((Real.exp (T / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖)
            * ∫ t : ℝ, ‖φ t‖ := integral_const_mul _ _
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable
  have hray : ∀ q : XiZeroCopy,
      (∫ t : ℝ, suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t)) = suzukiPHatRayTerm φ z q := by
    intro q
    rw [suzukiPHatRayTerm, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => hden q t)
  have hpt : ∀ t : ℝ, suzukiPtZeroSum t z * (starRingEnd ℂ) (φ t)
      = ∑' q : XiZeroCopy, suzukiPtZeroTerm t z q * (starRingEnd ℂ) (φ t) := by
    intro t
    rw [suzukiPtZeroSum, tsum_mul_right]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), ← hswap]
  exact tsum_congr hray

theorem suzukiPHatConj_eq_tsum {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : Integrable φ)
    {T : ℝ} (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) (z : ℂ) :
    suzukiPHatConj φ z
      = I * (1 + suzukiThetaSharp z) / 2 * ∑' q : XiZeroCopy, suzukiPHatRayTerm φ z q := by
  have hpt : ∀ t : ℝ, suzukiFrakSFull t z * (starRingEnd ℂ) (φ t)
      = I * (1 + suzukiThetaSharp z) / 2 * (suzukiPtZeroSum t z * (starRingEnd ℂ) (φ t)) := by
    intro t
    rw [suzukiFrakSFull]
    ring
  rw [suzukiPHatConj, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_suzukiPtZeroSum_mul hφm hφ hsupp]

end
end RHTower

