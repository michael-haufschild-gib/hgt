import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.TrigammaVertical
import GaloisForLFunctions.RHTower.DigammaBinetFourthOrder
import GaloisForLFunctions.RHTower.ZetaFarRightDecay
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.XiHorizontalStripComparison
import GaloisForLFunctions.HTGeometry.HalfPlaneLogarithm
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients

/-!
# The Gamma factor of `ξ` near a saddle point

In the variable `τ = s − 1/2`, `ξ(1/2 + τ) = G(τ) ζ(1/2 + τ)` with `G(τ) = (s(s−1)/2) Γ_ℝ(s)`. This module gives the
slope `a = G'/G` and the bounds that make `G` an exponential at the scale of a saddle point:

* `‖a'(τ)‖ ≤ 6/‖τ‖` on `Re τ ≥ 0`, `‖τ‖ ≥ 4` (`norm_gammaSlopeDeriv_le`), from the partial fraction
  `ψ'(z) = Σ_n (z + n)^{−2}`, valid up to the imaginary axis;
* `|Re a(τ) − ½ log‖τ‖| ≤ 6` and `|Im a(τ)| ≤ 5` on `Re τ ≥ 1` (Stirling);
* a logarithm of `G` on `Re τ > 1/2`, normalized at `τ = 1`;
* the polynomial bound of `ζ` on `Re s ≥ 1/2` and its exponential approach to `1`.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- `G(τ) = (s(s−1)/2) Γ_ℝ(s)`, `s = 1/2 + τ`. -/
def gammaFactor (τ : ℂ) : ℂ := (1 / 2 + τ) * (τ - 1 / 2) / 2 * Complex.Gammaℝ (1 / 2 + τ)

/-- The slope `a = G'/G`. -/
def gammaSlope (τ : ℂ) : ℂ :=
  1 / (1 / 2 + τ) + 1 / (τ - 1 / 2) +
    (Complex.digamma ((1 / 2 + τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)

/-- The derivative of the slope. -/
def gammaSlopeDeriv (τ : ℂ) : ℂ :=
  -(1 / (1 / 2 + τ) ^ 2) - 1 / (τ - 1 / 2) ^ 2 + deriv Complex.digamma ((1 / 2 + τ) / 2) / 4

theorem re_half_add_pos {τ : ℂ} (hτ : 0 ≤ τ.re) : 0 < (1 / 2 + τ).re := by
  simp only [add_re, div_ofNat_re, one_re]
  linarith

theorem half_add_ne_zero {τ : ℂ} (hτ : 0 ≤ τ.re) : (1 / 2 + τ) ≠ 0 := fun h => by
  have := re_half_add_pos hτ
  rw [h, zero_re] at this
  exact lt_irrefl _ this

theorem xi_half_add_eq {τ : ℂ} (hτ : 0 ≤ τ.re) (hτ' : τ ≠ 1 / 2) :
    xi (1 / 2 + τ) = gammaFactor τ * riemannZeta (1 / 2 + τ) := by
  have hs1 : (1 / 2 + τ) ≠ 1 := fun h => hτ' (by linear_combination h)
  rw [xi_eq_mul_Gammaℝ_mul_riemannZeta (half_add_ne_zero hτ) hs1 (re_half_add_pos hτ), gammaFactor]
  have : (1 / 2 + τ - 1 : ℂ) = τ - 1 / 2 := by ring
  rw [this]
  ring

theorem gammaFactor_ne_zero {τ : ℂ} (hτ : 0 ≤ τ.re) (hτ' : τ ≠ 1 / 2) : gammaFactor τ ≠ 0 := by
  have h1 := half_add_ne_zero hτ
  have h2 : τ - 1 / 2 ≠ 0 := sub_ne_zero.2 hτ'
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h1 h2) two_ne_zero)
    (Complex.Gammaℝ_ne_zero_of_re_pos (re_half_add_pos hτ))

theorem hasDerivAt_gammaFactor {τ : ℂ} (hτ : 0 ≤ τ.re) (hτ' : τ ≠ 1 / 2) :
    HasDerivAt gammaFactor (gammaSlope τ * gammaFactor τ) τ := by
  have h1 := half_add_ne_zero hτ
  have h2 : τ - 1 / 2 ≠ 0 := sub_ne_zero.2 hτ'
  have hΓ : HasDerivAt (fun z : ℂ => Complex.Gammaℝ (1 / 2 + z))
      (Complex.Gammaℝ (1 / 2 + τ) *
        (Complex.digamma ((1 / 2 + τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)) τ := by
    have h := (hasDerivAt_Gammaℝ_of_re_pos (re_half_add_pos hτ)).comp τ
      ((hasDerivAt_id τ).const_add (1 / 2 : ℂ))
    simpa [Function.comp_def] using h
  have hp : HasDerivAt (fun z : ℂ => (1 / 2 + z) * (z - 1 / 2) / 2) τ τ := by
    have h := (((hasDerivAt_id τ).const_add (1 / 2 : ℂ)).mul ((hasDerivAt_id τ).sub_const (1 / 2 : ℂ))).div_const 2
    refine h.congr_deriv ?_
    simp only [id]
    ring
  refine (hp.mul hΓ).congr_deriv ?_
  simp only [gammaSlope, gammaFactor]
  field_simp
  ring

theorem hasDerivAt_gammaSlope {τ : ℂ} (hτ : 0 ≤ τ.re) (hτ' : τ ≠ 1 / 2) :
    HasDerivAt gammaSlope (gammaSlopeDeriv τ) τ := by
  have h1 := half_add_ne_zero hτ
  have h2 : τ - 1 / 2 ≠ 0 := sub_ne_zero.2 hτ'
  have hz : 0 < ((1 / 2 + τ) / 2).re := by
    rw [re_div_two]
    have := re_half_add_pos hτ
    linarith
  have hψ := (digamma_analyticOnNhd_re_pos _ hz).differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun z : ℂ => (1 / 2 + z) / 2) (1 / 2) τ := by
    simpa using ((hasDerivAt_id τ).const_add (1 / 2 : ℂ)).div_const 2
  have hψ' : HasDerivAt (fun z : ℂ => Complex.digamma ((1 / 2 + z) / 2))
      (deriv Complex.digamma ((1 / 2 + τ) / 2) * (1 / 2)) τ := hψ.comp τ hinner
  have ha : HasDerivAt (fun z : ℂ => 1 / (1 / 2 + z)) (-(1 / (1 / 2 + τ) ^ 2)) τ := by
    have h := ((hasDerivAt_id τ).const_add (1 / 2 : ℂ)).inv h1
    simp only [one_div]
    refine h.congr_deriv ?_
    simp [id]
  have hb : HasDerivAt (fun z : ℂ => 1 / (z - 1 / 2)) (-(1 / (τ - 1 / 2) ^ 2)) τ := by
    have h := ((hasDerivAt_id τ).sub_const (1 / 2 : ℂ)).inv h2
    simp only [one_div]
    refine h.congr_deriv ?_
    simp [id]
  have h := ((ha.add hb).add ((hψ'.div_const 2).sub_const ((Real.log Real.pi : ℂ) / 2)))
  refine h.congr_deriv ?_
  simp only [gammaSlopeDeriv]
  ring

/-! ## The trigamma bound -/

theorem sum_inv_sq_le {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), 1 / (σ + n) ^ 2 ≤ 1 / σ ^ 2 + 1 / σ - 1 / (σ + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hu : 0 < σ + N := by positivity
    have h : 1 / (σ + (N + 1 : ℕ)) ^ 2 ≤ 1 / (σ + N) - 1 / (σ + (N + 1 : ℕ)) := by
      push_cast
      have hu1 : 0 < σ + N + 1 := by linarith
      rw [show σ + (N + 1 : ℝ) = σ + N + 1 by ring, div_sub_div _ _ hu.ne' hu1.ne',
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem deriv_digamma_conj {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv Complex.digamma z) := by
  have hz' : 0 < ((starRingEnd ℂ) z).re := by simpa using hz
  have h1 := deriv_digamma_partialSum_tendsto hz'
  have h2 := (Complex.continuous_conj.tendsto _).comp (deriv_digamma_partialSum_tendsto hz)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp [map_sum]

/-- **Trigamma on the right half-plane**: `‖ψ'(z)‖ ≤ 8/‖z‖` for `Re z > 0`, `‖z‖ ≥ 1`. -/
theorem norm_deriv_digamma_le {z : ℂ} (hz : 0 < z.re) (hz1 : 1 ≤ ‖z‖) :
    ‖deriv Complex.digamma z‖ ≤ 8 / ‖z‖ := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hsq : 1 / ‖z‖ ^ 2 ≤ 1 / ‖z‖ := by
    apply one_div_le_one_div_of_le hzpos
    nlinarith
  have hπ := Real.pi_lt_four
  by_cases ht : ‖z‖ / 2 ≤ |z.im|
  · -- the vertical bound
    have hvert : ∀ w : ℂ, 0 < w.re → 0 < w.im → ‖z‖ / 2 ≤ w.im →
        ‖deriv Complex.digamma w‖ ≤ 8 / ‖z‖ := by
      intro w hw0 hw1 hw2
      have h := norm_deriv_digamma_vertical_le hw0 hw1
      rw [show (w.re : ℂ) + (w.im : ℂ) * I = w from Complex.re_add_im w] at h
      refine h.trans ?_
      have h1 : 1 / w.im ^ 2 ≤ 4 / ‖z‖ := by
        calc 1 / w.im ^ 2 ≤ 1 / (‖z‖ / 2) ^ 2 := by
              apply one_div_le_one_div_of_le (by positivity)
              exact pow_le_pow_left₀ (by positivity) hw2 2
          _ = 4 * (1 / ‖z‖ ^ 2) := by field_simp; norm_num
          _ ≤ 4 * (1 / ‖z‖) := by gcongr
          _ = 4 / ‖z‖ := by ring
      have h2 : Real.pi / (2 * w.im) ≤ 4 / ‖z‖ := by
        rw [div_le_div_iff₀ (by positivity) hzpos]
        nlinarith
      calc _ ≤ 4 / ‖z‖ + 4 / ‖z‖ := add_le_add h1 h2
        _ = 8 / ‖z‖ := by ring
    rcases le_or_gt 0 z.im with h0 | h0
    · rw [abs_of_nonneg h0] at ht
      exact hvert z hz (lt_of_lt_of_le (by positivity) ht) ht
    · rw [abs_of_neg h0] at ht
      have h := hvert ((starRingEnd ℂ) z) (by simpa using hz) (by simpa using h0) (by simpa using ht)
      rwa [deriv_digamma_conj hz, RCLike.norm_conj] at h
  · -- the horizontal bound
    push_neg at ht
    have hσ : ‖z‖ / 2 ≤ z.re := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz] at h
      linarith
    have hσ0 : 0 < z.re := hz
    have hlim := (deriv_digamma_partialSum_tendsto hz).norm
    refine le_of_tendsto' ((tendsto_add_atTop_iff_nat 1).2 hlim) fun N => ?_
    calc ‖∑ n ∈ Finset.range (N + 1), ((z + (n : ℂ)) ^ (2 : ℕ))⁻¹‖
        ≤ ∑ n ∈ Finset.range (N + 1), 1 / (z.re + n) ^ 2 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_inv, norm_pow, one_div]
          have hre : z.re + n ≤ ‖z + (n : ℂ)‖ := by
            have := Complex.re_le_norm (z + (n : ℂ))
            simpa using this
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hre 2)
      _ ≤ 1 / z.re ^ 2 + 1 / z.re - 1 / (z.re + N) := sum_inv_sq_le hz N
      _ ≤ 1 / z.re ^ 2 + 1 / z.re := by
          have : 0 ≤ 1 / (z.re + N) := by positivity
          linarith
      _ ≤ 4 * (1 / ‖z‖) + 2 / ‖z‖ := by
          refine add_le_add ?_ ?_
          · calc 1 / z.re ^ 2 ≤ 1 / (‖z‖ / 2) ^ 2 := by
                  apply one_div_le_one_div_of_le (by positivity)
                  exact pow_le_pow_left₀ (by positivity) hσ 2
              _ = 4 * (1 / ‖z‖ ^ 2) := by field_simp; norm_num
              _ ≤ _ := by gcongr
          · calc 1 / z.re ≤ 1 / (‖z‖ / 2) := one_div_le_one_div_of_le (by positivity) hσ
              _ = 2 / ‖z‖ := by field_simp
      _ ≤ 8 / ‖z‖ := by
          have : 0 ≤ 1 / ‖z‖ := by positivity
          have e : 8 / ‖z‖ = 8 * (1 / ‖z‖) := by ring
          have e2 : 2 / ‖z‖ = 2 * (1 / ‖z‖) := by ring
          rw [e, e2]
          linarith

theorem norm_gammaSlopeDeriv_le {τ : ℂ} (hτ : 0 ≤ τ.re) (h4 : 4 ≤ ‖τ‖) :
    ‖gammaSlopeDeriv τ‖ ≤ 6 / ‖τ‖ := by
  have hτ0 : 0 < ‖τ‖ := by linarith
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hl1 : (7 / 8) * ‖τ‖ ≤ ‖1 / 2 + τ‖ := by
    have h := norm_sub_norm_le τ (-(1 / 2 : ℂ))
    rw [sub_neg_eq_add, add_comm, norm_neg, hhalf] at h
    linarith
  have hl2 : (7 / 8) * ‖τ‖ ≤ ‖τ - 1 / 2‖ := by
    have h := norm_sub_norm_le τ (1 / 2 : ℂ)
    rw [hhalf] at h
    linarith
  have hb : ∀ u : ℝ, (7 / 8) * ‖τ‖ ≤ u → 1 / u ^ 2 ≤ (1 / 2) / ‖τ‖ := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
    rw [div_le_div_iff₀ (by positivity) hτ0]
    have hu2 : ((7 / 8) * ‖τ‖) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
    nlinarith
  have hzre : 0 < ((1 / 2 + τ) / 2).re := by
    rw [re_div_two]
    have := re_half_add_pos hτ
    linarith
  have hznorm : ‖(1 / 2 + τ) / 2‖ = ‖1 / 2 + τ‖ / 2 := by
    rw [norm_div]
    norm_num
  have hz1 : 1 ≤ ‖(1 / 2 + τ) / 2‖ := by
    rw [hznorm]
    linarith
  have hψ := norm_deriv_digamma_le hzre hz1
  have hψ2 : ‖deriv Complex.digamma ((1 / 2 + τ) / 2)‖ / 4 ≤ 5 / ‖τ‖ := by
    have h3 : 8 / ‖(1 / 2 + τ) / 2‖ ≤ 20 / ‖τ‖ := by
      rw [hznorm, div_le_div_iff₀ (by linarith) hτ0]
      nlinarith
    linarith [hψ.trans h3, show (20 : ℝ) / ‖τ‖ / 4 = 5 / ‖τ‖ by ring]
  calc ‖gammaSlopeDeriv τ‖
      ≤ ‖-(1 / (1 / 2 + τ) ^ 2)‖ + ‖1 / (τ - 1 / 2) ^ 2‖ +
          ‖deriv Complex.digamma ((1 / 2 + τ) / 2) / 4‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ = 1 / ‖1 / 2 + τ‖ ^ 2 + 1 / ‖τ - 1 / 2‖ ^ 2 +
          ‖deriv Complex.digamma ((1 / 2 + τ) / 2)‖ / 4 := by
        simp only [norm_neg, norm_div, norm_one, norm_pow]
        norm_num
    _ ≤ (1 / 2) / ‖τ‖ + (1 / 2) / ‖τ‖ + 5 / ‖τ‖ := add_le_add (add_le_add (hb _ hl1) (hb _ hl2)) hψ2
    _ = 6 / ‖τ‖ := by ring

/-! ## Stirling -/

theorem norm_gammaSlope_sub_log_le {τ : ℂ} (hτ : 1 ≤ τ.re) :
    ‖gammaSlope τ - (Complex.log ((1 / 2 + τ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)‖ ≤ 4 := by
  set w := (1 / 2 + τ) / 2 with hw
  have hwre : 3 / 4 ≤ w.re := by
    rw [hw, re_div_two]
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have hwnorm : 3 / 4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hs := norm_digamma_sub_stirling_le (w := w) (by linarith)
  have h1 : 1 / (120 * w.re ^ 4) ≤ 1 / 3 := by
    have : (3 / 4 : ℝ) ^ 4 ≤ w.re ^ 4 := pow_le_pow_left₀ (by norm_num) hwre 4
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : ‖1 / (2 * w)‖ ≤ 2 / 3 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h3 : ‖1 / (12 * w ^ 2)‖ ≤ 1 / 6 := by
    rw [norm_div, norm_one, norm_mul, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hψ : ‖Complex.digamma w - Complex.log w‖ ≤ 7 / 6 := by
    have e : Complex.digamma w - Complex.log w =
        (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)) - 1 / (2 * w) -
          1 / (12 * w ^ 2) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := (norm_sub_le (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2))
      (1 / (2 * w)))
    linarith [hs.trans h1]
  have hs1 : ‖1 / (1 / 2 + τ)‖ ≤ 2 / 3 := by
    have hre : 3 / 2 ≤ (1 / 2 + τ).re := by
      simp only [add_re, div_ofNat_re, one_re]
      linarith
    have hn := hre.trans (Complex.re_le_norm _)
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hs2 : ‖1 / (τ - 1 / 2)‖ ≤ 2 := by
    have hre : 1 / 2 ≤ (τ - 1 / 2).re := by
      simp only [sub_re, div_ofNat_re, one_re]
      linarith
    have hn := hre.trans (Complex.re_le_norm _)
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  have e : gammaSlope τ - (Complex.log w / 2 - (Real.log Real.pi : ℂ) / 2) =
      1 / (1 / 2 + τ) + 1 / (τ - 1 / 2) + (Complex.digamma w - Complex.log w) / 2 := by
    simp only [gammaSlope, hw]
    ring
  rw [e]
  have h5 : ‖(Complex.digamma w - Complex.log w) / 2‖ ≤ 7 / 12 := by
    rw [norm_div, Complex.norm_two]
    linarith
  calc _ ≤ ‖1 / (1 / 2 + τ)‖ + ‖1 / (τ - 1 / 2)‖ + ‖(Complex.digamma w - Complex.log w) / 2‖ :=
        norm_add₃_le
    _ ≤ 2 / 3 + 2 + 7 / 12 := add_le_add (add_le_add hs1 hs2) h5
    _ ≤ 4 := by norm_num

theorem log_pi_le_three : Real.log Real.pi ≤ 3 := by
  have h := Real.log_le_sub_one_of_pos Real.pi_pos
  linarith [Real.pi_lt_four]

theorem log_pi_nonneg : 0 ≤ Real.log Real.pi :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

/-- **Stirling for the slope, real part.** -/
theorem abs_re_gammaSlope_sub_le {τ : ℂ} (hτ : 1 ≤ τ.re) :
    |(gammaSlope τ).re - Real.log ‖τ‖ / 2| ≤ 7 := by
  set w := (1 / 2 + τ) / 2 with hw
  have h := Complex.abs_re_le_norm (gammaSlope τ - (Complex.log w / 2 - (Real.log Real.pi : ℂ) / 2))
  have h4 := norm_gammaSlope_sub_log_le hτ
  have hre : (gammaSlope τ - (Complex.log w / 2 - (Real.log Real.pi : ℂ) / 2)).re =
      (gammaSlope τ).re - (Real.log ‖w‖ / 2 - Real.log Real.pi / 2) := by
    simp only [sub_re, div_ofNat_re, Complex.log_re, ofReal_re]
  rw [hre] at h
  have hτ0 : 0 < ‖τ‖ := lt_of_lt_of_le one_pos (hτ.trans (Complex.re_le_norm τ))
  have hτ1 : 1 ≤ ‖τ‖ := hτ.trans (Complex.re_le_norm τ)
  have hwn : ‖w‖ = ‖1 / 2 + τ‖ / 2 := by
    rw [hw, norm_div, Complex.norm_two]
  have hs1 : ‖1 / 2 + τ‖ ≤ ‖τ‖ + 1 / 2 := by
    refine (norm_add_le _ _).trans ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    linarith
  have hs2 : ‖τ‖ / 2 ≤ ‖1 / 2 + τ‖ := by
    have h := norm_sub_norm_le τ (-(1 / 2 : ℂ))
    rw [sub_neg_eq_add, add_comm, norm_neg] at h
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    linarith
  have hwpos : 0 < ‖w‖ := by
    rw [hwn]
    have : 0 < ‖τ‖ / 2 := by positivity
    linarith
  have hu : Real.log ‖w‖ ≤ Real.log ‖τ‖ := by
    refine Real.log_le_log hwpos ?_
    rw [hwn]
    linarith
  have hl : Real.log ‖τ‖ - 2 ≤ Real.log ‖w‖ := by
    have h1 : ‖τ‖ / 4 ≤ ‖w‖ := by
      rw [hwn]
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div hτ0.ne' (by norm_num)] at h2
    have h3 : Real.log 4 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 2 by norm_num)
      have e : Real.log 4 = Real.log (4 / 2) + Real.log 2 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      have h2' := Real.log_two_lt_d9
      rw [e]
      norm_num at this ⊢
      linarith
    linarith
  have hπ1 := log_pi_le_three
  have hπ0 := log_pi_nonneg
  rw [abs_le] at h ⊢
  have h' := abs_le.1 (show |_| ≤ _ from (abs_le.2 h).trans h4)
  constructor <;> linarith [h'.1, h'.2]

/-- **Stirling for the slope, imaginary part.** -/
theorem abs_im_gammaSlope_le {τ : ℂ} (hτ : 1 ≤ τ.re) : |(gammaSlope τ).im| ≤ 5 := by
  set w := (1 / 2 + τ) / 2 with hw
  have h := Complex.abs_im_le_norm (gammaSlope τ - (Complex.log w / 2 - (Real.log Real.pi : ℂ) / 2))
  have h4 := norm_gammaSlope_sub_log_le hτ
  have him : (gammaSlope τ - (Complex.log w / 2 - (Real.log Real.pi : ℂ) / 2)).im =
      (gammaSlope τ).im - Complex.arg w / 2 := by
    simp [Complex.log_im]
  rw [him] at h
  have hwre : 0 ≤ w.re := by
    rw [hw, re_div_two]
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have harg : |Complex.arg w| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.2 hwre
  have hπ := Real.pi_lt_four
  have h' := abs_le.1 (h.trans h4)
  have harg' := abs_le.1 harg
  rw [abs_le]
  constructor <;> linarith [h'.1, h'.2, harg'.1, harg'.2]

theorem norm_gammaSlope_le {τ : ℂ} (hτ : 1 ≤ τ.re) : ‖gammaSlope τ‖ ≤ Real.log ‖τ‖ / 2 + 12 := by
  have h1 := abs_le.1 (abs_re_gammaSlope_sub_le hτ)
  have h2 := abs_im_gammaSlope_le hτ
  have hτ1 : 1 ≤ ‖τ‖ := hτ.trans (Complex.re_le_norm τ)
  have hl : 0 ≤ Real.log ‖τ‖ := Real.log_nonneg hτ1
  have h3 := Complex.norm_le_abs_re_add_abs_im (gammaSlope τ)
  have h4 : |(gammaSlope τ).re| ≤ Real.log ‖τ‖ / 2 + 7 := by
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  linarith

/-! ## The logarithm of the Gamma factor -/

theorem re_ne_half {τ : ℂ} (hτ : 1 / 2 < τ.re) : τ ≠ 1 / 2 := fun h => by
  rw [h] at hτ
  norm_num at hτ

theorem digamma_conj (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have h := iteratedDeriv_conj_of_schwarzReal (f := Complex.Gamma) (fun w => Complex.Gamma_conj w) 1 z
  simp only [iteratedDeriv_one] at h
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, h, Complex.Gamma_conj, map_div₀]

theorem gammaSlope_conj (τ : ℂ) :
    gammaSlope ((starRingEnd ℂ) τ) = (starRingEnd ℂ) (gammaSlope τ) := by
  have e : (1 / 2 + (starRingEnd ℂ) τ) / 2 = (starRingEnd ℂ) ((1 / 2 + τ) / 2) := by
    simp [map_div₀, map_add]
  simp only [gammaSlope]
  rw [e, digamma_conj]
  simp [map_div₀, map_add, map_sub, Complex.conj_ofReal]

/-- A logarithm of `G/G(1)` on `Re τ > 1/2` whose derivative is the slope. -/
theorem exists_gammaFactor_log :
    ∃ P : ℂ → ℂ, P 1 = 0 ∧ (∀ z : ℂ, 1 / 2 < z.re → HasDerivAt P (gammaSlope z) z) ∧
      ∀ z : ℂ, 1 / 2 < z.re → Complex.exp (P z) = gammaFactor z / gammaFactor 1 := by
  have h10 : (1 : ℂ) ≠ 1 / 2 := by norm_num
  have hG1 : gammaFactor 1 ≠ 0 := gammaFactor_ne_zero (by norm_num) h10
  refine exists_halfPlane_exp_primitive (a := 1 / 2) (b := 1) (Φ := gammaSlope)
    (f := fun z => gammaFactor z / gammaFactor 1) ?_ ?_ (by norm_num) (div_self hG1)
  · intro z hz
    have hz' : 1 / 2 < z.re := hz
    exact (hasDerivAt_gammaSlope (by linarith) (re_ne_half hz')).differentiableAt.differentiableWithinAt
  · intro z hz
    have h := (hasDerivAt_gammaFactor (by linarith) (re_ne_half hz)).div_const (gammaFactor 1)
    refine h.congr_deriv ?_
    ring

/-! ## The zeta factor -/

/-- `‖ζ(1/2 + τ)‖ ≤ 5‖τ‖²` on `Re τ ≥ 0`, `‖τ‖ ≥ 4`. -/
theorem norm_zeta_half_add_le {τ : ℂ} (hτ : 0 ≤ τ.re) (h4 : 4 ≤ ‖τ‖) :
    ‖riemannZeta (1 / 2 + τ)‖ ≤ 5 * ‖τ‖ ^ 2 := by
  by_cases ht : 1 ≤ |τ.im|
  · have hσ : (1 / 2 : ℝ) ≤ 1 / 2 + τ.re := by linarith
    have hB : |1 / 2 + τ.re| ≤ 1 / 2 + ‖τ‖ := by
      rw [abs_of_nonneg (by linarith)]
      linarith [Complex.re_le_norm τ]
    have h := norm_riemannZeta_le_linear_of_re_ge_half hσ hB ht
    have hs : ((1 / 2 + τ.re : ℝ) : ℂ) + (τ.im : ℂ) * I = 1 / 2 + τ := by
      push_cast
      rw [add_assoc, Complex.re_add_im]
    rw [hs] at h
    have hsqrt : Real.sqrt (1 / 2 + ‖τ‖ + 3) ≤ ‖τ‖ := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have him : |τ.im| ≤ ‖τ‖ := Complex.abs_im_le_norm τ
    calc _ ≤ 5 * Real.sqrt (1 / 2 + ‖τ‖ + 3) * |τ.im| := h
      _ ≤ 5 * ‖τ‖ * ‖τ‖ := by gcongr
      _ = 5 * ‖τ‖ ^ 2 := by ring
  · push_neg at ht
    have hre : 3 ≤ τ.re := by
      have h := Complex.norm_le_abs_re_add_abs_im τ
      rw [abs_of_nonneg hτ] at h
      linarith
    have hs : (3 : ℝ) ≤ (1 / 2 + τ).re := by
      simp only [add_re, div_ofNat_re, one_re]
      linarith
    have h := norm_riemannZeta_sub_one_le_of_three_le hs
    have h1 : ‖riemannZeta (1 / 2 + τ)‖ ≤ ‖riemannZeta (1 / 2 + τ) - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (riemannZeta (1 / 2 + τ) - 1) 1
    rw [norm_one] at h1
    nlinarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.norm_gammaSlopeDeriv_le
#print axioms FiniteFreeProbability.abs_re_gammaSlope_sub_le
#print axioms FiniteFreeProbability.exists_gammaFactor_log
