import GaloisForLFunctions.RHTower.XiGaussianHeatWindowPrimeTwoMargin
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelSincLevelWitness
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearHorizon
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# RH is positivity of the heat Hankel sections on the pole hyperplane

**Theorem** (`riemannHypothesis_iff_forall_eventually_poleHyperplane_pos`).  RH holds iff for every
`K > 0`, for all large `n` and every `0 < a ≤ K/n`, the heat moment section
`(M_{i+j}(a))_{i,j ≤ n}` is positive definite on the pole hyperplane `Σ_i x_i (−1/4)^i = 0`.

Together with the window theorem `eventually_re_heatHankel_pos_of_polarGroundEnergy` (a
pole-vanishing Weil margin at aperture `A` gives every window `K < A²/4`), this yields
`riemannHypothesis_of_forall_polarGroundEnergy_pos`: positivity of the pole-vanishing ground energy
at every aperture implies RH, through the heat Hankel sections.

Mechanism.
* **Pole-vanishing witnesses** (`exists_poleVanishing_zeroSide_witness`).  If `Φ` is an even entire
  zero-side witness of exponential type, then so is `Φ − Φ(i/2) Ψ_t` for large `t`, where
  `Ψ_t(z) = (sinc(tz)/sinc(it/2))²` is `1` at `i/2` and `O(e^{−t(1 − 2|Im z|)}/|z|²)` at the
  zeros, so it vanishes in the limit by dominated convergence (`|Im z_q| < ½`).
* **Taylor correction** (`tendsto_heatHankel_poleCorrected`).  The even Taylor polynomial
  `T_nΦ` takes the value `T_nΦ(−1/4) = O(4^{−n})` at the pole, and subtracting this constant
  changes `H_{K/n}` by `O(n 4^{−n})`, since `H_a(T_nΦ, 1)` and `H_a(1, 1)` grow only like `1/a`.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology Matrix
open GaloisForLFunctions.HTGeometry (leadingMatrix hermQuad hermNegIndex)

namespace RHTower

noncomputable section

/-! ## The pole bump -/

theorem entireSinc_mul_I_half {t : ℝ} (ht : 0 < t) :
    entireSinc ((t : ℂ) * (I / 2)) = ((Real.sinh (t / 2) / (t / 2) : ℝ) : ℂ) := by
  have he : (t : ℂ) * (I / 2) = ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have hne : ((t / 2 : ℝ) : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by positivity : (t / 2 : ℝ) ≠ 0)) I_ne_zero
  rw [he, entireSinc_of_ne_zero hne, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  push_cast
  field_simp

theorem one_le_sinh_div {t : ℝ} (ht : 0 < t) : 1 ≤ Real.sinh (t / 2) / (t / 2) := by
  rw [le_div_iff₀ (by positivity), one_mul]
  exact Real.self_le_sinh_iff.2 (by positivity)

/-- `Ψ_t(z) = (sinc(tz)/sinc(it/2))²`. -/
def poleBump (t : ℝ) (z : ℂ) : ℂ :=
  (entireSinc ((t : ℂ) * z) / entireSinc ((t : ℂ) * (I / 2))) ^ 2

theorem poleBump_I_half {t : ℝ} (ht : 0 < t) : poleBump t (I / 2) = 1 := by
  have h : entireSinc ((t : ℂ) * (I / 2)) ≠ 0 := by
    rw [entireSinc_mul_I_half ht]
    exact_mod_cast (lt_of_lt_of_le one_pos (one_le_sinh_div ht)).ne'
  rw [poleBump, div_self h, one_pow]

theorem differentiable_poleBump (t : ℝ) : Differentiable ℂ (poleBump t) :=
  ((differentiable_entireSinc.comp (differentiable_const _ |>.mul differentiable_id)).div_const
    _).pow 2

theorem poleBump_neg (t : ℝ) (z : ℂ) : poleBump t (-z) = poleBump t z := by
  simp only [poleBump, mul_neg, entireSinc_neg]

theorem norm_sinc_I_half {t : ℝ} (ht : 0 < t) :
    ‖entireSinc ((t : ℂ) * (I / 2))‖ = Real.sinh (t / 2) / (t / 2) := by
  rw [entireSinc_mul_I_half ht, Complex.norm_real, Real.norm_of_nonneg
    (le_trans zero_le_one (one_le_sinh_div ht))]

theorem norm_poleBump_le_exp {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖poleBump t z‖ ≤ 4 * Real.exp (2 * t * ‖z‖) := by
  have hs := one_le_sinh_div ht
  have h1 : ‖entireSinc ((t : ℂ) * z)‖ ≤ 2 * Real.exp (t * ‖z‖) := by
    have := norm_entireSinc_le ((t : ℂ) * z)
    rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
  have h2 : ‖entireSinc ((t : ℂ) * z) / entireSinc ((t : ℂ) * (I / 2))‖ ≤
      2 * Real.exp (t * ‖z‖) := by
    rw [norm_div, norm_sinc_I_half ht, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (entireSinc ((t : ℂ) * z)), Real.exp_pos (t * ‖z‖)]
  rw [poleBump, norm_pow]
  calc ‖entireSinc ((t : ℂ) * z) / entireSinc ((t : ℂ) * (I / 2))‖ ^ 2
      ≤ (2 * Real.exp (t * ‖z‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = 4 * Real.exp (2 * t * ‖z‖) := by
        rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf

theorem quarter_exp_le_sinh {y : ℝ} (hy : 1 ≤ y) : Real.exp y / 4 ≤ Real.sinh y := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-y) ≤ Real.exp y / 2 := by
    have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have h3 : 2 ≤ Real.exp y * Real.exp y := by
      rw [← Real.exp_add]
      have := Real.add_one_le_exp (y + y)
      linarith
    nlinarith [Real.exp_pos y, Real.exp_pos (-y)]
  linarith

/-- **The pole bump at a zero.**  `|Ψ_t(z)| ≤ 4 e^{−t(1 − 2|Im z|)}/|z|²` for `t ≥ 2`, `z ≠ 0`. -/
theorem norm_poleBump_le_of_ne {t : ℝ} (ht : 2 ≤ t) {z : ℂ} (hz : z ≠ 0) :
    ‖poleBump t z‖ ≤ 4 * Real.exp (-(t * (1 - 2 * |z.im|))) / ‖z‖ ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hne : (t : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast ht0.ne') hz
  have h1 : ‖entireSinc ((t : ℂ) * z)‖ ≤ Real.exp (t * |z.im|) / (t * ‖z‖) := by
    have := norm_entireSinc_le_of_ne hne
    have him : ((t : ℂ) * z).im = t * z.im := by simp
    rwa [him, abs_mul, abs_of_pos ht0, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht0.le] at this
  have hsinh : Real.exp (t / 2) / 4 ≤ Real.sinh (t / 2) := quarter_exp_le_sinh (by linarith)
  have hs : Real.exp (t / 2) / (2 * t) ≤ Real.sinh (t / 2) / (t / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hspos : 0 < Real.exp (t / 2) / (2 * t) := by positivity
  have h2 : ‖entireSinc ((t : ℂ) * z) / entireSinc ((t : ℂ) * (I / 2))‖ ≤
      2 * Real.exp (t * |z.im| - t / 2) / ‖z‖ := by
    rw [norm_div, norm_sinc_I_half ht0]
    calc ‖entireSinc ((t : ℂ) * z)‖ / (Real.sinh (t / 2) / (t / 2))
        ≤ (Real.exp (t * |z.im|) / (t * ‖z‖)) / (Real.exp (t / 2) / (2 * t)) :=
          div_le_div₀ (by positivity) h1 hspos hs
      _ = 2 * Real.exp (t * |z.im| - t / 2) / ‖z‖ := by
          rw [Real.exp_sub]; field_simp
  rw [poleBump, norm_pow]
  calc ‖entireSinc ((t : ℂ) * z) / entireSinc ((t : ℂ) * (I / 2))‖ ^ 2
      ≤ (2 * Real.exp (t * |z.im| - t / 2) / ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = 4 * Real.exp (-(t * (1 - 2 * |z.im|))) / ‖z‖ ^ 2 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul]
        congr 2
        · norm_num
        · push_cast; ring_nf

theorem norm_poleBump_le_strip {t : ℝ} (ht : 2 ≤ t) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖poleBump t z‖ ≤ 8 * Real.exp (2 * t) / (1 + ‖z‖) := by
  have ht0 : 0 < t := by linarith
  have he1 : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by positivity)
  rcases lt_or_ge ‖z‖ 1 with h1 | h1
  · have hb := norm_poleBump_le_exp ht0 z
    have : Real.exp (2 * t * ‖z‖) ≤ Real.exp (2 * t) :=
      Real.exp_le_exp.2 (by nlinarith [norm_nonneg z])
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg z, norm_nonneg (poleBump t z)]
  · have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
    have hb := norm_poleBump_le_of_ne ht hz0
    have hexp : Real.exp (-(t * (1 - 2 * |z.im|))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg z.im])
    have hz2 : 4 * Real.exp (-(t * (1 - 2 * |z.im|))) / ‖z‖ ^ 2 ≤ 8 / (1 + ‖z‖) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc ‖poleBump t z‖ ≤ 8 / (1 + ‖z‖) := hb.trans hz2
      _ ≤ 8 * Real.exp (2 * t) / (1 + ‖z‖) := by
          apply div_le_div_of_nonneg_right _ (by positivity); nlinarith

/-! ## Pole-vanishing witnesses -/

theorem one_le_norm_xiSpectralPoint (q : XiZeroCopy) : 1 ≤ ‖xiSpectralPoint q‖ := by
  have h := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  nlinarith [norm_nonneg (xiSpectralPoint q)]

theorem tendsto_poleBump_zero {z : ℂ} (hz : z ≠ 0) (him : |z.im| < 1 / 2) :
    Tendsto (fun t : ℝ => poleBump t z) atTop (𝓝 0) := by
  have hδ : 0 < 1 - 2 * |z.im| := by linarith
  have hlim : Tendsto (fun t : ℝ => 4 * Real.exp (-(t * (1 - 2 * |z.im|))) / ‖z‖ ^ 2) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -(t * (1 - 2 * |z.im|))) atTop atBot := by
      have := tendsto_id.atTop_mul_const hδ
      exact tendsto_neg_atTop_atBot.comp this
    have := ((Real.tendsto_exp_atBot.comp h1).const_mul 4).div_const (‖z‖ ^ 2)
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with t ht
  exact norm_poleBump_le_of_ne ht hz

theorem norm_sub_poleBump_le {Φ : ℂ → ℂ} {D : ℝ}
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖)) (c : ℂ) {t : ℝ} (ht : 2 ≤ t)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) (hz1 : 1 ≤ ‖z‖) :
    ‖Φ z - c * poleBump t z‖ ≤ (D + 8 * ‖c‖) / (1 + ‖z‖) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hb := norm_poleBump_le_of_ne ht hz0
  have hexp : Real.exp (-(t * (1 - 2 * |z.im|))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg z.im])
  have hz2 : 4 * Real.exp (-(t * (1 - 2 * |z.im|))) / ‖z‖ ^ 2 ≤ 8 / (1 + ‖z‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ‖Φ z - c * poleBump t z‖ ≤ ‖Φ z‖ + ‖c‖ * ‖poleBump t z‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ D / (1 + ‖z‖) + ‖c‖ * (8 / (1 + ‖z‖)) :=
        add_le_add (hdecay z hz) (mul_le_mul_of_nonneg_left (hb.trans hz2) (norm_nonneg _))
    _ = (D + 8 * ‖c‖) / (1 + ‖z‖) := by ring

/-- **Pole-vanishing witnesses.**  An even entire zero-side witness of exponential type with strip
decay can be corrected to one that also vanishes at `i/2`. -/
theorem exists_poleVanishing_zeroSide_witness {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B D : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖))
    (hneg : (∑' q : XiZeroCopy, Φ (xiSpectralPoint q) *
      (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q)))).re < 0) :
    ∃ (Ψ : ℂ → ℂ) (C' B' D' : ℝ), Differentiable ℂ Ψ ∧ (∀ z, Ψ (-z) = Ψ z) ∧ 0 ≤ B' ∧
      (∀ z, ‖Ψ z‖ ≤ C' * Real.exp (B' * ‖z‖)) ∧
      (∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Ψ z‖ ≤ D' / (1 + ‖z‖)) ∧ Ψ (I / 2) = 0 ∧
      (∑' q : XiZeroCopy, Ψ (xiSpectralPoint q) *
        (starRingEnd ℂ) (Ψ ((starRingEnd ℂ) (xiSpectralPoint q)))).re < 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = Φ (I / 2) := ⟨_, rfl⟩
  have hD : 0 ≤ D := by
    have h := hdecay 0 (by simp)
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  have hC := nonneg_of_growth hgrowth
  -- convergence of the corrected zero-side sums
  have hpt : ∀ q : XiZeroCopy, Tendsto (fun t : ℝ =>
      (Φ (xiSpectralPoint q) - c * poleBump t (xiSpectralPoint q)) *
        (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q)) -
          c * poleBump t ((starRingEnd ℂ) (xiSpectralPoint q)))) atTop
      (𝓝 (Φ (xiSpectralPoint q) * (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q))))) := by
    intro q
    have hz0 := xiSpectralPoint_ne_zero q
    have hzc0 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ 0 := by
      rwa [_root_.map_ne_zero]
    have him := abs_im_xiSpectralPoint_lt_half q
    have himc : |((starRingEnd ℂ) (xiSpectralPoint q)).im| < 1 / 2 := by
      rwa [Complex.conj_im, abs_neg]
    have h1 := (tendsto_const_nhds (x := Φ (xiSpectralPoint q))).sub
      ((tendsto_poleBump_zero hz0 him).const_mul c)
    have h2 := (tendsto_const_nhds (x := Φ ((starRingEnd ℂ) (xiSpectralPoint q)))).sub
      ((tendsto_poleBump_zero hzc0 himc).const_mul c)
    have h3 := (Complex.continuous_conj.tendsto _).comp h2
    simpa using h1.mul h3
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ q : XiZeroCopy,
      ‖(Φ (xiSpectralPoint q) - c * poleBump t (xiSpectralPoint q)) *
        (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q)) -
          c * poleBump t ((starRingEnd ℂ) (xiSpectralPoint q)))‖ ≤
        (D + 8 * ‖c‖) ^ 2 * (1 / (1 + ‖xiHeatFrequency q‖)) := by
    filter_upwards [eventually_ge_atTop 2] with t ht q
    set z := xiSpectralPoint q
    have hz := abs_im_xiSpectralPoint_le_half q
    have hzc : |((starRingEnd ℂ) z).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hz
    have hz1 := one_le_norm_xiSpectralPoint q
    have hzc1 : 1 ≤ ‖(starRingEnd ℂ) z‖ := by rwa [Complex.norm_conj]
    have b1 := norm_sub_poleBump_le hdecay c ht hz hz1
    have b2 := norm_sub_poleBump_le hdecay c ht hzc hzc1
    rw [Complex.norm_conj] at b2
    have hw : ‖xiHeatFrequency q‖ = ‖z‖ ^ 2 := by
      rw [show xiHeatFrequency q = z ^ 2 from rfl, norm_pow]
    rw [norm_mul, Complex.norm_conj, hw]
    have hden : 1 + ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
    calc ‖Φ z - c * poleBump t z‖ *
          ‖Φ ((starRingEnd ℂ) z) - c * poleBump t ((starRingEnd ℂ) z)‖
        ≤ (D + 8 * ‖c‖) / (1 + ‖z‖) * ((D + 8 * ‖c‖) / (1 + ‖z‖)) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ = (D + 8 * ‖c‖) ^ 2 / (1 + ‖z‖) ^ 2 := by rw [div_mul_div_comm, ← pow_two, ← pow_two]
      _ ≤ (D + 8 * ‖c‖) ^ 2 * (1 / (1 + ‖z‖ ^ 2)) := by
          rw [mul_one_div]
          gcongr
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_inv_one_add_norm_xiHeatFrequency.mul_left ((D + 8 * ‖c‖) ^ 2)) hpt hbound
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  obtain ⟨t, ht2, htneg⟩ := ((eventually_ge_atTop (2 : ℝ)).and
    (hre.eventually (gt_mem_nhds hneg))).exists
  have ht0 : 0 < t := by linarith
  refine ⟨fun z => Φ z - c * poleBump t z, C + 4 * ‖c‖, max B (2 * t),
    D + ‖c‖ * (8 * Real.exp (2 * t)), hΦ.sub ((differentiable_poleBump t).const_mul c),
    fun z => by simp only [heven, poleBump_neg], le_max_of_le_left hB, fun z => ?_, fun z hz => ?_,
    by simp only [poleBump_I_half ht0, hc, mul_one, sub_self], htneg⟩
  · have e1 : Real.exp (B * ‖z‖) ≤ Real.exp (max B (2 * t) * ‖z‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have e2 : Real.exp (2 * t * ‖z‖) ≤ Real.exp (max B (2 * t) * ‖z‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hb := norm_poleBump_le_exp ht0 z
    calc ‖Φ z - c * poleBump t z‖ ≤ ‖Φ z‖ + ‖c‖ * ‖poleBump t z‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ C * Real.exp (B * ‖z‖) + ‖c‖ * (4 * Real.exp (2 * t * ‖z‖)) :=
          add_le_add (hgrowth z) (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
      _ ≤ C * Real.exp (max B (2 * t) * ‖z‖) + ‖c‖ * (4 * Real.exp (max B (2 * t) * ‖z‖)) := by
          gcongr
      _ = (C + 4 * ‖c‖) * Real.exp (max B (2 * t) * ‖z‖) := by ring
  · have hb := norm_poleBump_le_strip ht2 hz
    calc ‖Φ z - c * poleBump t z‖ ≤ ‖Φ z‖ + ‖c‖ * ‖poleBump t z‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ D / (1 + ‖z‖) + ‖c‖ * (8 * Real.exp (2 * t) / (1 + ‖z‖)) :=
          add_le_add (hdecay z hz) (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
      _ = (D + ‖c‖ * (8 * Real.exp (2 * t))) / (1 + ‖z‖) := by ring

/-! ## Taylor correction at the pole -/

/-- `H_a(P − c, P − c) = H_a(P, P) − c̄ H_a(P, 1) − c H_a(1, P) + |c|² H_a(1, 1)`. -/
theorem heatHankel_sub_C {a : ℝ} (ha : 0 < a) (P : ℂ[X]) (c : ℂ) :
    heatHankel a (P - Polynomial.C c) (P - Polynomial.C c) =
      heatHankel a P P - (starRingEnd ℂ) c * heatHankel a P 1 - c * heatHankel a 1 P +
        (Complex.normSq c : ℂ) * heatHankel a 1 1 := by
  unfold heatHankel
  have s1 := summable_heatHankelTermAt ha P P
  have s2 := (summable_heatHankelTermAt ha P 1).mul_left ((starRingEnd ℂ) c)
  have s3 := (summable_heatHankelTermAt ha 1 P).mul_left c
  have s4 := (summable_heatHankelTermAt ha 1 1).mul_left (Complex.normSq c : ℂ)
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← s1.tsum_sub s2,
    ← (s1.sub s2).tsum_sub s3, ← ((s1.sub s2).sub s3).tsum_add s4]
  refine tsum_congr fun q => ?_
  simp only [heatHankelTermAt, eval_sub, eval_C, eval_one, map_sub, map_one, mul_one]
  rw [← Complex.mul_conj]
  ring

theorem one_add_mul_exp_neg_le_one_add_inv {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    (1 + r) * Real.exp (-(a * r)) ≤ 1 + 1 / a := by
  have h1 : Real.exp (-(a * r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : a * r * Real.exp (-(a * r)) ≤ 1 := by
    have := Real.add_one_le_exp (a * r)
    have h3 : Real.exp (a * r) * Real.exp (-(a * r)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(a * r)), Real.exp_pos (a * r)]
  have h4 : r * Real.exp (-(a * r)) ≤ 1 / a := by
    rw [le_div_iff₀ ha]; linarith
  nlinarith

theorem re_sq_ge (z : ℂ) (hz : |z.im| ≤ 1 / 2) : ‖z‖ ^ 2 - 1 / 2 ≤ (z ^ 2).re := by
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have : z.im ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  linarith

/-- The heat weight at a zero: `e^{−a Re w/2}/(1 + |z|) ≤ e^{a/4}(1 + 2/a)/(1 + |w|)`. -/
theorem exp_half_div_le {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Real.exp (-(a * (z ^ 2).re) / 2) / (1 + ‖z‖) ≤
      Real.exp (a / 4) * (1 + 2 / a) * (1 / (1 + ‖z ^ 2‖)) := by
  have h1 := re_sq_ge z hz
  have he : Real.exp (-(a * (z ^ 2).re) / 2) ≤ Real.exp (a / 4) * Real.exp (-(a / 2 * ‖z‖ ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hb := one_add_mul_exp_neg_le_one_add_inv (a := a / 2) (by positivity) (sq_nonneg ‖z‖)
  have hw : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow _ _
  rw [hw, div_le_iff₀ (by positivity)]
  have hz1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have e2 : 1 / (a / 2) = 2 / a := by field_simp
  rw [e2] at hb
  calc Real.exp (-(a * (z ^ 2).re) / 2)
      ≤ Real.exp (a / 4) * Real.exp (-(a / 2 * ‖z‖ ^ 2)) := he
    _ ≤ Real.exp (a / 4) * ((1 + 2 / a) / (1 + ‖z‖ ^ 2)) := by
        gcongr
        rw [le_div_iff₀ (by positivity)]; linarith
    _ ≤ Real.exp (a / 4) * (1 + 2 / a) * (1 / (1 + ‖z‖ ^ 2)) * (1 + ‖z‖) := by
        have : 0 ≤ Real.exp (a / 4) * (1 + 2 / a) * (1 / (1 + ‖z‖ ^ 2)) := by positivity
        calc Real.exp (a / 4) * ((1 + 2 / a) / (1 + ‖z‖ ^ 2))
            = Real.exp (a / 4) * (1 + 2 / a) * (1 / (1 + ‖z‖ ^ 2)) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hz1 this

theorem exp_neg_re_le {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Real.exp (-(a * (z ^ 2).re)) ≤ Real.exp (a / 2) * (1 + 1 / a) * (1 / (1 + ‖z ^ 2‖)) := by
  have h1 := re_sq_ge z hz
  have he : Real.exp (-(a * (z ^ 2).re)) ≤ Real.exp (a / 2) * Real.exp (-(a * ‖z‖ ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  have hb := one_add_mul_exp_neg_le_one_add_inv ha (sq_nonneg ‖z‖)
  rw [norm_pow]
  calc Real.exp (-(a * (z ^ 2).re)) ≤ Real.exp (a / 2) * Real.exp (-(a * ‖z‖ ^ 2)) := he
    _ ≤ Real.exp (a / 2) * ((1 + 1 / a) / (1 + ‖z‖ ^ 2)) := by
        gcongr
        rw [le_div_iff₀ (by positivity)]; linarith
    _ = _ := by ring

/-- **The constant correction is negligible.**  With `P_n = T_nΦ`, `Φ(i/2) = 0` and
`c_n = P_n(−1/4)`, `H_{K/n}(P_n − c_n, P_n − c_n) − H_{K/n}(P_n, P_n) → 0`. -/
theorem tendsto_heatHankel_poleCorrected {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (heven : ∀ z, Φ (-z) = Φ z) {C B D K : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖))
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖)) (hpole : Φ (I / 2) = 0)
    (hK : (B * Real.exp 1 + 1) ^ 2 < 4 * K) :
    Tendsto (fun n : ℕ => heatHankel (K / n)
      (evenTaylorPoly Φ n - Polynomial.C ((evenTaylorPoly Φ n).eval (-1 / 4)))
      (evenTaylorPoly Φ n - Polynomial.C ((evenTaylorPoly Φ n).eval (-1 / 4)))) atTop
      (𝓝 (∑' q : XiZeroCopy, Φ (xiSpectralPoint q) *
        (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q))))) := by
  have hK0 : 0 < K := by nlinarith [sq_nonneg (B * Real.exp 1 + 1)]
  have hC := nonneg_of_growth hgrowth
  have hD : 0 ≤ D := by
    have h := hdecay 0 (by simp)
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  have hmain := tendsto_heatHankel_evenTaylorPoly hΦ heven hB hgrowth hdecay hK
  set S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) with hS_def
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set E := Real.exp (1 / 8) * D + 1 with hE_def
  have hE : 0 ≤ E := by positivity
  set L := 2 * C * Real.exp B with hL_def
  have hL : 0 ≤ L := by positivity
  -- the pole value of the Taylor polynomial
  have hc : ∀ n : ℕ, ‖(evenTaylorPoly Φ n).eval (-1 / 4)‖ ≤ L * (1 / 4) ^ (n + 1) := fun n => by
    have h := norm_sub_eval_evenTaylorPoly_le hΦ heven hgrowth one_pos (I / 2)
      (by simp) n
    have hsq : (I / 2 : ℂ) ^ 2 = -1 / 4 := by ring_nf; rw [I_sq]; ring
    have hn : ‖(I / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [hsq, hpole, zero_sub, norm_neg, hn, mul_one, div_one] at h
    calc ‖(evenTaylorPoly Φ n).eval (-1 / 4)‖ ≤ 2 * (C * Real.exp B) * (1 / 2) ^ (2 * n + 2) := h
      _ = L * (1 / 4) ^ (n + 1) := by
          rw [hL_def, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]; norm_num; ring
  -- the error bound
  set err : ℕ → ℝ := fun n => L * (1 / 4) ^ (n + 1) *
    (2 * (Real.exp 1 * (1 + 2 * n / K) * E * S) + L * (Real.exp 1 * (1 + n / K) * S)) with herr
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have h4 : |(1 / 4 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
    have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
    have hp1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 h4
    have e : err = fun n : ℕ => (L / 4) * ((2 * Real.exp 1 * E * S + L * Real.exp 1 * S) *
        (1 / 4 : ℝ) ^ n + (4 * Real.exp 1 * E * S / K + L * Real.exp 1 * S / K) *
          ((n : ℝ) ^ 1 * (1 / 4) ^ n)) := by
      funext n; rw [herr, pow_succ]; field_simp; ring
    rw [e]
    simpa using ((hp0.const_mul (2 * Real.exp 1 * E * S + L * Real.exp 1 * S)).add
      (hp1.const_mul (4 * Real.exp 1 * E * S / K + L * Real.exp 1 * S / K))).const_mul (L / 4)
  have hdiff : Tendsto (fun n : ℕ =>
      heatHankel (K / n) (evenTaylorPoly Φ n - Polynomial.C ((evenTaylorPoly Φ n).eval (-1 / 4)))
        (evenTaylorPoly Φ n - Polynomial.C ((evenTaylorPoly Φ n).eval (-1 / 4))) -
      heatHankel (K / n) (evenTaylorPoly Φ n) (evenTaylorPoly Φ n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr0
    filter_upwards [eventually_heatWeighted_norm_evenTaylorPoly_le hΦ heven hB hgrowth hdecay hK]
      with n hn
    obtain ⟨hn0, hKn, hbd⟩ := hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    set a := K / (n : ℝ) with ha_def
    have ha : 0 < a := div_pos hK0 hn'
    have ha1 : a ≤ 1 := hKn.le
    have hinv : 1 / a = n / K := by rw [ha_def]; field_simp
    set P := evenTaylorPoly Φ n
    set c := P.eval (-1 / 4)
    rw [heatHankel_sub_C ha P c]
    have e1 : heatHankel a P P - (starRingEnd ℂ) c * heatHankel a P 1 - c * heatHankel a 1 P +
        (Complex.normSq c : ℂ) * heatHankel a 1 1 - heatHankel a P P =
        -((starRingEnd ℂ) c * heatHankel a P 1) - c * heatHankel a 1 P +
          (Complex.normSq c : ℂ) * heatHankel a 1 1 := by ring
    rw [e1]
    have ea4 : Real.exp (a / 4) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    have ea2 : Real.exp (a / 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    -- `|H(P, 1)|` and `|H(1, P)|`
    have hP1 : ∀ R₁ R₂ : ℂ[X], (R₁ = P ∧ R₂ = 1) ∨ (R₁ = 1 ∧ R₂ = P) →
        ‖heatHankel a R₁ R₂‖ ≤ Real.exp 1 * (1 + 2 * n / K) * E * S := by
      intro R₁ R₂ hR
      unfold heatHankel
      have hsum := summable_inv_one_add_norm_xiHeatFrequency.mul_left
        (Real.exp (a / 4) * (1 + 2 / a) * E)
      have hterm : ∀ q : XiZeroCopy, ‖heatHankelTermAt a R₁ R₂ (xiHeatFrequency q)‖ ≤
          Real.exp (a / 4) * (1 + 2 / a) * E * (1 / (1 + ‖xiHeatFrequency q‖)) := fun q => by
        set z := xiSpectralPoint q
        have hz := abs_im_xiSpectralPoint_le_half q
        have hzc : |((starRingEnd ℂ) z).im| ≤ 1 / 2 := by
          rw [Complex.conj_im, abs_neg]; exact hz
        have hw : xiHeatFrequency q = z ^ 2 := rfl
        have hrec : ((starRingEnd ℂ) z ^ 2).re = (z ^ 2).re := by
          rw [← map_pow, Complex.conj_re]
        have hexp : ‖Complex.exp (-(a : ℂ) * xiHeatFrequency q)‖ =
            Real.exp (-(a * (z ^ 2).re) / 2) * Real.exp (-(a * (z ^ 2).re) / 2) := by
          rw [Complex.norm_exp, ← Real.exp_add, hw]; congr 1; simp
        have hwt := exp_half_div_le ha hz
        have hpos := Real.exp_pos (-(a * (z ^ 2).re) / 2)
        rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hb := hbd z hz
          rw [heatHankelTermAt, norm_mul, norm_mul, hexp, eval_one, map_one, norm_one, mul_one, hw]
          calc Real.exp (-(a * (z ^ 2).re) / 2) * Real.exp (-(a * (z ^ 2).re) / 2) *
                ‖P.eval (z ^ 2)‖
              = Real.exp (-(a * (z ^ 2).re) / 2) *
                  (Real.exp (-(a * (z ^ 2).re) / 2) * ‖P.eval (z ^ 2)‖) := by ring
            _ ≤ Real.exp (-(a * (z ^ 2).re) / 2) * (E / (1 + ‖z‖)) :=
                mul_le_mul_of_nonneg_left hb hpos.le
            _ = E * (Real.exp (-(a * (z ^ 2).re) / 2) / (1 + ‖z‖)) := by ring
            _ ≤ E * (Real.exp (a / 4) * (1 + 2 / a) * (1 / (1 + ‖z ^ 2‖))) :=
                mul_le_mul_of_nonneg_left hwt hE
            _ = _ := by ring
        · have hb := hbd _ hzc
          rw [hrec, Complex.norm_conj] at hb
          rw [heatHankelTermAt, norm_mul, norm_mul, hexp, eval_one, norm_one, mul_one,
            Complex.norm_conj, hw, map_pow]
          calc Real.exp (-(a * (z ^ 2).re) / 2) * Real.exp (-(a * (z ^ 2).re) / 2) *
                ‖P.eval ((starRingEnd ℂ) z ^ 2)‖
              = Real.exp (-(a * (z ^ 2).re) / 2) *
                  (Real.exp (-(a * (z ^ 2).re) / 2) * ‖P.eval ((starRingEnd ℂ) z ^ 2)‖) := by
                ring
            _ ≤ Real.exp (-(a * (z ^ 2).re) / 2) * (E / (1 + ‖z‖)) :=
                mul_le_mul_of_nonneg_left hb hpos.le
            _ = E * (Real.exp (-(a * (z ^ 2).re) / 2) / (1 + ‖z‖)) := by ring
            _ ≤ E * (Real.exp (a / 4) * (1 + 2 / a) * (1 / (1 + ‖z ^ 2‖))) :=
                mul_le_mul_of_nonneg_left hwt hE
            _ = _ := by ring
      calc ‖∑' q : XiZeroCopy, heatHankelTermAt a R₁ R₂ (xiHeatFrequency q)‖
          ≤ ∑' q : XiZeroCopy, Real.exp (a / 4) * (1 + 2 / a) * E *
              (1 / (1 + ‖xiHeatFrequency q‖)) :=
            tsum_of_norm_bounded hsum.hasSum hterm
        _ = Real.exp (a / 4) * (1 + 2 / a) * E * S := by rw [tsum_mul_left]
        _ ≤ Real.exp 1 * (1 + 2 * n / K) * E * S := by
            rw [show 2 / a = 2 * n / K by rw [ha_def]; field_simp]
            gcongr
    have h11 : ‖heatHankel a 1 1‖ ≤ Real.exp 1 * (1 + n / K) * S := by
      unfold heatHankel
      have hsum := summable_inv_one_add_norm_xiHeatFrequency.mul_left
        (Real.exp (a / 2) * (1 + 1 / a))
      have hterm : ∀ q : XiZeroCopy, ‖heatHankelTermAt a 1 1 (xiHeatFrequency q)‖ ≤
          Real.exp (a / 2) * (1 + 1 / a) * (1 / (1 + ‖xiHeatFrequency q‖)) := fun q => by
        have hz := abs_im_xiSpectralPoint_le_half q
        rw [heatHankelTermAt, eval_one, eval_one, map_one, mul_one, mul_one, Complex.norm_exp,
          show xiHeatFrequency q = xiSpectralPoint q ^ 2 from rfl]
        have : (-(a : ℂ) * xiSpectralPoint q ^ 2).re = -(a * (xiSpectralPoint q ^ 2).re) := by
          simp
        rw [this]
        exact exp_neg_re_le ha hz
      calc ‖∑' q : XiZeroCopy, heatHankelTermAt a 1 1 (xiHeatFrequency q)‖
          ≤ ∑' q : XiZeroCopy, Real.exp (a / 2) * (1 + 1 / a) * (1 / (1 + ‖xiHeatFrequency q‖)) :=
            tsum_of_norm_bounded hsum.hasSum hterm
        _ = Real.exp (a / 2) * (1 + 1 / a) * S := by rw [tsum_mul_left]
        _ ≤ Real.exp 1 * (1 + n / K) * S := by rw [hinv]; gcongr
    have hcn := hc n
    have hcn0 : 0 ≤ ‖c‖ := norm_nonneg _
    have hA := hP1 P 1 (Or.inl ⟨rfl, rfl⟩)
    have hB' := hP1 1 P (Or.inr ⟨rfl, rfl⟩)
    have hnormSq : ‖(Complex.normSq c : ℂ)‖ = ‖c‖ * ‖c‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg c),
        Complex.normSq_eq_norm_sq, sq]
    calc ‖-((starRingEnd ℂ) c * heatHankel a P 1) - c * heatHankel a 1 P +
          (Complex.normSq c : ℂ) * heatHankel a 1 1‖
        ≤ ‖c‖ * ‖heatHankel a P 1‖ + ‖c‖ * ‖heatHankel a 1 P‖ +
            ‖c‖ * ‖c‖ * ‖heatHankel a 1 1‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
          · rw [norm_neg, norm_mul, norm_mul, Complex.norm_conj]
          · rw [norm_mul, hnormSq]
      _ ≤ L * (1 / 4) ^ (n + 1) * (Real.exp 1 * (1 + 2 * n / K) * E * S) +
            L * (1 / 4) ^ (n + 1) * (Real.exp 1 * (1 + 2 * n / K) * E * S) +
            L * (1 / 4) ^ (n + 1) * (L * (1 / 4) ^ (n + 1)) *
              (Real.exp 1 * (1 + n / K) * S) := by
          gcongr
      _ ≤ err n := by
          rw [herr]
          have hq : (1 / 4 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          have hX : 0 ≤ L * (Real.exp 1 * (1 + n / K) * S) := by positivity
          have hY : L * (1 / 4) ^ (n + 1) * (L * (1 / 4) ^ (n + 1)) *
              (Real.exp 1 * (1 + n / K) * S) ≤
              L * (1 / 4) ^ (n + 1) * (L * (Real.exp 1 * (1 + n / K) * S)) := by
            have h0 : 0 ≤ L * (1 / 4) ^ (n + 1) := by positivity
            calc L * (1 / 4) ^ (n + 1) * (L * (1 / 4) ^ (n + 1)) * (Real.exp 1 * (1 + n / K) * S)
                = L * (1 / 4) ^ (n + 1) * ((1 / 4) ^ (n + 1) * (L * (Real.exp 1 * (1 + n / K) * S))) := by
                  ring
              _ ≤ L * (1 / 4) ^ (n + 1) * (1 * (L * (Real.exp 1 * (1 + n / K) * S))) := by
                  gcongr
              _ = _ := by ring
          nlinarith
  have := hmain.add hdiff
  simpa using this

/-! ## The criterion -/

theorem heatCoeffPoly_coeff_eq {n : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ n) :
    heatCoeffPoly (fun i : Fin (n + 1) => P.coeff i) = P := by
  ext k
  rw [coeff_heatCoeffPoly]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem poleFunctional_coeff_eq {n : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ n) :
    poleFunctional (n + 1) (fun i => P.coeff i) = P.eval (-1 / 4) := by
  change ∑ i : Fin (n + 1), P.coeff i * (-1 / 4 : ℂ) ^ (i : ℕ) = _
  rw [eval_eq_sum_range' (n := n + 1) (by omega), Fin.sum_univ_eq_sum_range
    (fun i => P.coeff i * (-1 / 4 : ℂ) ^ i)]

/-- **Below RH the pole hyperplane fails at scale `1/N`.**  If RH fails, there is `K > 0` such that
for all large `n` the section at time `K/n` is not positive on the pole hyperplane. -/
theorem exists_eventually_poleHyperplane_neg_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ x : Fin (n + 1) → ℂ, poleFunctional (n + 1) x = 0 ∧
      hermQuad (heatMomentSection (K / n) (n + 1)) x < 0 := by
  obtain ⟨Φ, C, B, D, hΦ, heven, hB, hgrowth, hdecay, hneg⟩ :=
    exists_exponentialType_zeroSide_witness_of_not_riemannHypothesis hRH
  obtain ⟨Ψ, C', B', D', hΨ, heven', hB', hgrowth', hdecay', hpole, hneg'⟩ :=
    exists_poleVanishing_zeroSide_witness hΦ heven hB hgrowth hdecay hneg
  set K := (B' * Real.exp 1 + 1) ^ 2 / 4 + 1 with hK_def
  have hK : (B' * Real.exp 1 + 1) ^ 2 < 4 * K := by rw [hK_def]; linarith
  have hK0 : 0 < K := by rw [hK_def]; positivity
  refine ⟨K, hK0, ?_⟩
  have hlim := tendsto_heatHankel_poleCorrected hΨ heven' hB' hgrowth' hdecay' hpole hK
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  filter_upwards [hre.eventually (gt_mem_nhds hneg'), eventually_gt_atTop 0] with n hn hn0
  set P := evenTaylorPoly Ψ n - Polynomial.C ((evenTaylorPoly Ψ n).eval (-1 / 4)) with hP
  have hdeg : P.natDegree ≤ n :=
    (natDegree_sub_C.le).trans (natDegree_evenTaylorPoly_le Ψ n)
  refine ⟨fun i => P.coeff i, ?_, ?_⟩
  · rw [poleFunctional_coeff_eq hdeg, hP, eval_sub, eval_C, sub_self]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [hermQuad_heatMomentSection (div_pos hK0 hn') (Nat.succ_pos n), heatCoeffPoly_coeff_eq hdeg]
    exact hn

/-- **RH is positivity of the heat sections on the pole hyperplane in every window.** -/
theorem riemannHypothesis_iff_forall_eventually_poleHyperplane_pos :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ K / n →
      ∀ x : Fin (n + 1) → ℂ, poleFunctional (n + 1) x = 0 → x ≠ 0 →
        0 < hermQuad (heatMomentSection a (n + 1)) x := by
  constructor
  · intro hRH K _
    obtain ⟨C, -, hpos⟩ := exists_linear_height_heatHankel_re_pos
    refine Filter.Eventually.of_forall fun n a ha _ x _ hx => ?_
    rw [hermQuad_heatMomentSection ha (Nat.succ_pos n)]
    refine hpos n (fun q hq => absurd ((riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1
      hRH q) hq) a ha _ ?_ (Nat.lt_succ_iff.1 (natDegree_heatCoeffPoly_lt (Nat.succ_pos n) x))
    intro h0
    apply hx
    apply heatCoeffPolyMap_injective (n + 1)
    rw [heatCoeffPolyMap_apply, h0, map_zero]
  · intro h
    by_contra hRH
    obtain ⟨K, hK0, hneg⟩ := exists_eventually_poleHyperplane_neg_of_not_riemannHypothesis hRH
    obtain ⟨n, hn1, hn2, hn0⟩ := ((h K hK0).and (hneg.and (eventually_gt_atTop 0))).exists
    obtain ⟨x, hx0, hxneg⟩ := hn2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hxne : x ≠ 0 := by
      rintro rfl
      simp [hermQuad] at hxneg
    have := hn1 (K / n) (div_pos hK0 hn') le_rfl x hx0 hxne
    linarith

/-- **Positive pole-vanishing Weil ground energy at every aperture implies RH**, through the heat
Hankel sections: the margin gives every window on the pole hyperplane. -/
theorem riemannHypothesis_of_forall_polarGroundEnergy_pos
    (h : ∀ A : SuzukiPositiveAperture, 0 < ccmRestrictedWeilPolarGroundEnergy A) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_eventually_poleHyperplane_pos.2 fun K hK => ?_
  set A : SuzukiPositiveAperture := ⟨2 * Real.sqrt K + 1, by positivity⟩
  have hKA : 4 * K < A.1 ^ 2 := by
    change 4 * K < (2 * Real.sqrt K + 1) ^ 2
    have hs := Real.sq_sqrt hK.le
    nlinarith [Real.sqrt_nonneg K]
  filter_upwards [eventually_re_heatHankel_pos_of_polarGroundEnergy (h A) hK hKA] with n hn a ha haK
    x hx hx0
  exact hermQuad_heatMomentSection_pos_of_real ha (hn a ha haK) x hx hx0

end

end RHTower
