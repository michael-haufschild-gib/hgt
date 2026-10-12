import GaloisForLFunctions.RHTower.XiGaussianHeatSharpWitnessAsymptotics

/-!
# The sharp witness: a Weil-negative source of half-width `A` kills every window `K > A²/4`

**Theorem** (`eventually_exists_poleHyperplane_heatHankel_neg_of_source`).  Let `u` be a smooth even
real function vanishing outside `[−A, A]`, with `∫ u e^{x/2} = 0` and negative Weil energy
`Re Σ_q F_u(z_q)² < 0`.  If `A² < 4K`, then for all large `n` there is a real polynomial `P` of
degree `≤ n` with `P(−1/4) = 0` and `Re H_{K/n}(P, P) < 0`.

Together with `eventually_le_re_heatHankel_of_polarGroundEnergy` (a pole-vanishing Weil margin at
aperture `A` gives positivity in every window `K < A²/4`) the window constant on the pole hyperplane
is exactly a quarter of the square of the even pole-vanishing Weil aperture.

The witness is the degree-`2n` Hermite truncation of the heat smoothing `u ⋆ G_{K/n}` at width
`(2πK/n)^{1/2}`.  The smoothing is a superposition of translated Gaussians, whose Hermite energy is
Poisson with parameter `≤ A²n/(2K) = 2nθ`, `θ = A²/(4K) < 1`, so the truncation error is
`O((θ e^{1-θ})^{2n})`.  Every other loss is polynomial in `n`.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun mul_exp_one_sub_lt_one continuous_gaussPolyFun
  sq_integral_abs_gaussPolyFun_mul_exp_half_le)

namespace RHTower

noncomputable section

theorem tendsto_succ_pow_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (p : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ p * r ^ n) atTop (𝓝 0) := by
  rcases hr0.eq_or_lt with rfl | hr
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [zero_pow hn.ne', mul_zero]
  have habs : |r| < 1 := by rw [abs_of_pos hr]; exact hr1
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one p habs).comp (tendsto_add_atTop_nat 1)
  have h2 := h.const_mul r⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply]
  push_cast
  rw [pow_succ]
  field_simp

/-- **The smoothed sources converge on the zeros.**  `Σ_q F_{u_{K/n}}(z_q)² → Σ_q F_u(z_q)²`. -/
theorem tendsto_tsum_heatSmooth_sq {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {K : ℝ} (hK0 : 0 < K) :
    Tendsto (fun n : ℕ => ∑' q : XiZeroCopy, heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) atTop
      (𝓝 (∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2)) := by
  set Fu := fun z => heatStripTransform (fun x => ((u x : ℝ) : ℂ)) z with hFu
  set U2 := stripMass (deriv (deriv u))
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n ∧ K / n ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0, (tendsto_const_div_atTop_nhds_zero_nat K).eventually
      (ge_mem_nhds one_pos)] with n hn h1
    exact ⟨hn, h1⟩
  have hformula : ∀ᶠ n : ℕ in atTop, ∀ q : XiZeroCopy, heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2 =
      (Complex.exp (-((K / n : ℝ) : ℂ) * xiSpectralPoint q ^ 2 / 2) * Fu (xiSpectralPoint q)) ^ 2 := by
    filter_upwards [hev] with n hn q
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn.1
    rw [heatStripTransform_heatSmooth (div_pos hK0 hn') hu.continuous hcpt]
  have hexp0 : Tendsto (fun n : ℕ => ((K / n : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat K)
    simpa [Function.comp_def] using this
  have hpt : ∀ q : XiZeroCopy, Tendsto (fun n : ℕ => heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) atTop
      (𝓝 (Fu (xiSpectralPoint q) ^ 2)) := fun q => by
    have he : Tendsto (fun n : ℕ => Complex.exp (-((K / n : ℝ) : ℂ) * xiSpectralPoint q ^ 2 / 2))
        atTop (𝓝 1) := by
      have := ((hexp0.neg.mul_const (xiSpectralPoint q ^ 2)).div_const 2).cexp
      simpa using this
    have h := (he.mul_const (Fu (xiSpectralPoint q))).pow 2
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [hformula] with n hn
    rw [hn q]
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ q : XiZeroCopy, ‖heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2‖ ≤
      (Real.exp (1 / 8) * U2) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    filter_upwards [hformula, hev] with n hn hev' q
    rw [hn q, norm_pow, norm_mul]
    set z := xiSpectralPoint q
    have hz := abs_im_xiSpectralPoint_le_half q
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
    have hz1 : 1 ≤ ‖z‖ ^ 2 := by have := oneHundredFifty_lt_norm_xiSpectralPoint_sq q; linarith
    have he : ‖Complex.exp (-((K / n : ℝ) : ℂ) * z ^ 2 / 2)‖ ≤ Real.exp (1 / 8) :=
      (norm_cexp_heat_le (div_pos hK0 (by exact_mod_cast hev'.1)).le hz).trans
        (Real.exp_le_exp.2 (by linarith [hev'.2]))
    have hF := sq_norm_mul_heatStripTransform_source_le hu hcpt hz
    have hU2 : 0 ≤ U2 := integral_nonneg fun _ => by positivity
    have hF' : ‖Fu z‖ ≤ U2 / ‖z‖ ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hF
    have h1 : ‖Complex.exp (-((K / n : ℝ) : ℂ) * z ^ 2 / 2)‖ * ‖Fu z‖ ≤
        Real.exp (1 / 8) * (U2 / ‖z‖ ^ 2) := mul_le_mul he hF' (norm_nonneg _) (Real.exp_pos _).le
    calc (‖Complex.exp (-((K / n : ℝ) : ℂ) * z ^ 2 / 2)‖ * ‖Fu z‖) ^ 2
        ≤ (Real.exp (1 / 8) * (U2 / ‖z‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = (Real.exp (1 / 8) * U2) ^ 2 * (1 / ‖z‖ ^ 2) * (1 / ‖z‖ ^ 2) := by ring
      _ ≤ (Real.exp (1 / 8) * U2) ^ 2 * (1 / ‖z‖ ^ 2) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact hz1
      _ = _ := by ring
  exact tendsto_tsum_of_dominated_convergence
    (xiSpectralPoint_inv_sq_summable.mul_left ((Real.exp (1 / 8) * U2) ^ 2)) hpt hbound

/-- The collected comparison error. -/
def witnessErr (ι τu σ Y G E U S₂ S : ℝ) : ℝ :=
  (Real.sqrt E * G * (ι * Y + τu * Y) + E * G ^ 2 * (σ * Y)) * (1 + 2 * Real.exp (1 / 8)) * S₂ +
    (ι + τu + Real.sqrt E * G * σ) * Real.exp (1 / 8) * U * S₂ +
    3 * (ι ^ 2 * (1 + Y) + τu ^ 2 * (1 + Y) + E * G ^ 2 * (σ ^ 2 + σ * (σ * Y))) *
      Real.exp (1 / 2) * S

/-- The `L²` truncation error bound. -/
def witnessE1 (u : ℝ → ℝ) (a θ : ℝ) (n : ℕ) : ℝ :=
  heatHermiteScale a * (((∫ t, |u t|) / heatHermiteScale a) ^ 2 *
    ‖(GaloisForLFunctions.coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 *
      ((θ * Real.exp (1 - θ)) ^ (2 * n + 1) / (1 - θ)))

/-- The `L²`-scale of the truncated test. -/
def witnessG (u : ℝ → ℝ) (B X : ℝ) : ℝ :=
  Real.sqrt (2 + 2 * (B * (2 * X * (B * Real.exp (X / 2)) + 4 * ∫ t, |u t|)))

/-- **The per-time error in collected form.** -/
theorem exists_poleCorrected_err_le {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hXA : 2 * A ≤ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * (2 * n + 1 : ℕ)) {k : ℕ}
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : heatMomentRatio (n + 1) k a X ^ k = σ ^ 2) (he1 : witnessE1 u a θ n ≤ 1) :
    ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      ‖heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ ≤
        witnessErr (Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n))
          (4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a)))) σ (4 * (1 / (2 * a)) * (2 * n + 3))
          (witnessG u B X) (heatStripConstant X) (stripMass (deriv (deriv u)))
          (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)
          (∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) := by
  obtain ⟨P, hPd, hPe, hcmp⟩ := exists_poleCorrected_near_smoothed hu hcpt hsupp heven hpole ha
    ha16 n
  refine ⟨P, hPd, hPe, hcmp.trans ?_⟩
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have ha1 : a < 1 := by linarith
  have hX0 : 0 < X := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set U₁ := ∫ t, |u t| with hU₁
  have hU₁0 : 0 ≤ U₁ := integral_nonneg fun _ => abs_nonneg _
  set e1 := witnessE1 u a θ n with he1_def
  have he10 : 0 ≤ e1 := by
    have : 0 ≤ (θ * Real.exp (1 - θ)) ^ (2 * n + 1) / (1 - θ) :=
      div_nonneg (pow_nonneg (mul_nonneg hθ0 (Real.exp_pos _).le) _) (by linarith)
    have := heatHermiteScale_pos ha
    rw [he1_def, witnessE1]
    positivity
  set Bw := 2 * X * (B * Real.exp (X / 2)) + 4 * U₁ with hBw
  set G := Real.sqrt (2 + 2 * (B * Bw)) with hG
  have hG2 : G ^ 2 = 2 + 2 * (B * Bw) := Real.sq_sqrt (by positivity)
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  set ι := Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * e1) with hι
  have hι2 : ι ^ 2 = 2 * Real.exp 1 * π * Real.exp (X ^ 2) * e1 := Real.sq_sqrt (by positivity)
  set τu := 4 * U₁ * Real.exp (-(X ^ 2 / (32 * a))) with hτu
  set Y := 4 * (1 / (2 * a)) * (2 * n + 3) with hY
  set E := heatStripConstant X with hE
  have hE0 : 0 ≤ E := by rw [hE, heatStripConstant]; positivity
  set g := truncHeatTest u hu hcpt ha n with hg_def
  have hgQ : g = gaussPolyFun (truncHeatPoly u hu hcpt ha (2 * n + 1)) (1 / (2 * a)) := rfl
  have hQd : (truncHeatPoly u hu hcpt ha (2 * n + 1)).natDegree ≤ 2 * n :=
    (natDegree_truncHeatPoly_le u hu hcpt ha _).trans (by omega)
  -- the `L²` error
  have hE1 : ∫ x, (g x - heatSmooth a u x) ^ 2 ≤ e1 := by
    have h := integral_sq_truncHeatTest_sub_le u hu hcpt hsupp ha hθ0 hθ1 hN
    rw [integral_norm_scaledSource hu hcpt (heatHermiteScale_pos ha)] at h
    rw [he1_def, witnessE1]
    exact h
  -- `∫ u_a² ≤ B Bw`
  obtain ⟨hua_int, hua⟩ := integral_heatSmooth_sq_le hu hcpt hsupp ha ha16 hB
  have hBw := stripMass_heatSmooth_le hu hcpt hsupp ha ha16 hB hX1 hXA
  have hua2 : ∫ x, heatSmooth a u x ^ 2 ≤ B * Bw := hua.trans (mul_le_mul_of_nonneg_left hBw hB0)
  -- `∫ g² ≤ G²`
  have hg_int : Integrable (fun x => g x ^ 2) :=
    GaloisForLFunctions.integrable_gaussPolyFun_sq _ (by linarith)
  have hd_int : Integrable (fun x => (g x - heatSmooth a u x) ^ 2) := by
    refine ((hg_int.add hua_int).const_mul 2).mono'
      (((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    have key : 2 * (g x ^ 2 + heatSmooth a u x ^ 2) - (g x - heatSmooth a u x) ^ 2 =
        (g x + heatSmooth a u x) ^ 2 := by ring
    linarith [sq_nonneg (g x + heatSmooth a u x)]
  have hg2 : ∫ x, g x ^ 2 ≤ G ^ 2 := by
    have hpt : ∀ x, g x ^ 2 ≤ 2 * (g x - heatSmooth a u x) ^ 2 + 2 * heatSmooth a u x ^ 2 :=
      fun x => by
        have key : 2 * (g x - heatSmooth a u x) ^ 2 + 2 * heatSmooth a u x ^ 2 - g x ^ 2 =
            (g x - 2 * heatSmooth a u x) ^ 2 := by ring
        linarith [sq_nonneg (g x - 2 * heatSmooth a u x)]
    have := integral_mono hg_int ((hd_int.const_mul 2).add (hua_int.const_mul 2)) hpt
    simp only [Pi.add_apply] at this
    rw [integral_add (hd_int.const_mul 2) (hua_int.const_mul 2), integral_const_mul,
      integral_const_mul] at this
    rw [hG2]
    linarith
  have hgV0 : 0 ≤ ∫ x, g x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  -- tails and second derivative
  have hτg : stripMassOn g (heatTailSet X) ≤ Real.sqrt E * σ * G := by
    have h := sq_stripMassOn_tail_le hQd ha ha1 hX0 k hk
    rw [hσ, ← hgQ] at h
    have h2 : stripMassOn g (heatTailSet X) ^ 2 ≤ (Real.sqrt E * σ * G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
      calc stripMassOn g (heatTailSet X) ^ 2 ≤ E * σ ^ 2 * ∫ x, g x ^ 2 := h
        _ ≤ E * σ ^ 2 * G ^ 2 := by gcongr
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  have hNg2 : stripMass (truncHeatTestDD u hu hcpt ha n) ≤ Real.sqrt E * Y * G := by
    have h := sq_stripMass_dd_le hQd ha ha1 hX0 k hk
    have h2 : stripMass (truncHeatTestDD u hu hcpt ha n) ^ 2 ≤ (Real.sqrt E * Y * G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
      calc stripMass (truncHeatTestDD u hu hcpt ha n) ^ 2 ≤ E * Y ^ 2 * ∫ x, g x ^ 2 := h
        _ ≤ E * Y ^ 2 * G ^ 2 := by gcongr
    have hY0 : 0 ≤ Y := by positivity
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  -- the inner part and the source tail
  have hinner : ∫ x in Ioo (-X) X, |g x - heatSmooth a u x| * Real.exp (|x| / 2) ≤ ι := by
    obtain ⟨-, h⟩ := sq_setIntegral_inner_abs_mul_exp_half_le
      ((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)) hd_int hX0.le
    have h2 : (∫ x in Ioo (-X) X, |g x - heatSmooth a u x| * Real.exp (|x| / 2)) ^ 2 ≤ ι ^ 2 := by
      rw [hι2]
      calc _ ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) * ∫ x, (g x - heatSmooth a u x) ^ 2 := h
        _ ≤ _ := by gcongr
    have hι0 : 0 ≤ ι := Real.sqrt_nonneg _
    exact abs_le_of_sq_le_sq' h2 hι0 |>.2
  obtain ⟨-, htail⟩ := integrableOn_tail_heatSmooth hu hcpt hsupp ha ha16 hX1 hXA
  have hNgu : stripMass (fun x => g x - heatSmooth a u x) ≤
      ι + stripMassOn g (heatTailSet X) + τu := by
    have h := stripMass_sub_le (f₁ := g) (continuous_gaussPolyFun _ _)
      (continuous_heatSmooth hu hcpt ha)
      (sq_integral_abs_gaussPolyFun_mul_exp_half_le (truncHeatPoly u hu hcpt ha (2 * n + 1)) hβ
        one_pos 0).1
      (integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp) X
    have h3 : stripMassOn (heatSmooth a u) (heatTailSet X) ≤ τu := htail
    linarith
  -- collect
  have hN0 : 0 ≤ stripMass (fun x => g x - heatSmooth a u x) :=
    integral_nonneg fun _ => by positivity
  have hM0 : 0 ≤ stripMass (truncHeatTestDD u hu hcpt ha n) := integral_nonneg fun _ => by positivity
  have hU2 : 0 ≤ stripMass (deriv (deriv u)) := integral_nonneg fun _ => by positivity
  have hinv : 1 / a ≤ Y := by
    rw [hY]
    have : (1 : ℝ) / a = 2 * (1 / (2 * a)) := by field_simp
    rw [this]
    have h3 : (0 : ℝ) < 1 / (2 * a) := by positivity
    have h4 : (2 : ℝ) ≤ 4 * (2 * n + 3) := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith only [this]
    calc 2 * (1 / (2 * a)) ≤ (4 * (2 * n + 3)) * (1 / (2 * a)) :=
          mul_le_mul_of_nonneg_right h4 h3.le
      _ = 4 * (1 / (2 * a)) * (2 * n + 3) := by ring
  have hfinal := comparison_error_le (N := stripMass (fun x => g x - heatSmooth a u x))
    (M := stripMass (truncHeatTestDD u hu hcpt ha n)) (ι := ι) (τg := stripMassOn g (heatTailSet X))
    (τu := τu) (σ := σ) (Y := Y) (G := G) (E := E) (U := stripMass (deriv (deriv u)))
    (S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)
    (S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (n := 1) (K := a)
    (c := Real.exp (1 / 8)) (e := Real.exp (1 / 2)) hN0 (Real.sqrt_nonneg _) (by positivity) hσ0
    hG0 hE0 hU2 (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity)
    (Real.exp_pos _).le (Real.exp_pos _).le (by positivity) hinv hNgu hτg hNg2 hM0
  exact hfinal

/-- `witnessErr` is at most `ξ C₀` when all its small inputs are at most `ξ ≤ 1`. -/
theorem witnessErr_le {ι τu σ Y G E U S₂ S ξ : ℝ} (hι : 0 ≤ ι) (hσ : 0 ≤ σ)
    (hY : 0 ≤ Y) (hG : 0 ≤ G) (hE : 0 ≤ E) (hU : 0 ≤ U) (hS₂ : 0 ≤ S₂) (hS : 0 ≤ S) (hξ1 : ξ ≤ 1)
    (h1 : ι ≤ ξ) (h2 : ι * Y ≤ ξ) (h3 : ι ^ 2 * (1 + Y) ≤ ξ) (h4 : τu ≤ ξ) (h5 : τu * Y ≤ ξ)
    (h6 : τu ^ 2 * (1 + Y) ≤ ξ) (h7 : σ ≤ ξ) (h8 : σ * Y ≤ ξ) :
    witnessErr ι τu σ Y G E U S₂ S ≤ ξ * ((2 * Real.sqrt E * G + E * G ^ 2) *
      (1 + 2 * Real.exp (1 / 8)) * S₂ + (2 + Real.sqrt E * G) * Real.exp (1 / 8) * U * S₂ +
        (6 + 6 * (E * G ^ 2)) * Real.exp (1 / 2) * S) := by
  have hξ : 0 ≤ ξ := hι.trans h1
  have hsE := Real.sqrt_nonneg E
  have hEG : 0 ≤ E * G ^ 2 := by positivity
  have hc : 0 ≤ 1 + 2 * Real.exp (1 / 8) := by positivity
  have hc8 := (Real.exp_pos (1 / 8)).le
  have hc2 := (Real.exp_pos (1 / 2)).le
  have hσσ : σ * (σ * Y) ≤ ξ * ξ := mul_le_mul h7 h8 (by positivity) hξ
  have hσ2 : σ ^ 2 ≤ ξ * ξ := by rw [sq]; exact mul_le_mul h7 h7 hσ hξ
  have hξξ : ξ * ξ ≤ ξ := mul_le_of_le_one_left hξ hξ1
  have t1 : Real.sqrt E * G * (ι * Y + τu * Y) + E * G ^ 2 * (σ * Y) ≤
      ξ * (2 * Real.sqrt E * G + E * G ^ 2) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h2 h5) (mul_nonneg hsE hG)
    have := mul_le_mul_of_nonneg_left h8 hEG
    nlinarith
  have t2 : ι + τu + Real.sqrt E * G * σ ≤ ξ * (2 + Real.sqrt E * G) := by
    have := mul_le_mul_of_nonneg_left h7 (mul_nonneg hsE hG)
    nlinarith
  have t3 : ι ^ 2 * (1 + Y) + τu ^ 2 * (1 + Y) + E * G ^ 2 * (σ ^ 2 + σ * (σ * Y)) ≤
      ξ * (2 + 2 * (E * G ^ 2)) := by
    have := mul_le_mul_of_nonneg_left (add_le_add (hσ2.trans hξξ) (hσσ.trans hξξ)) hEG
    nlinarith
  unfold witnessErr
  have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right t1 hc) hS₂
  have e2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right t2 hc8) hU) hS₂
  have e3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left t3 (by norm_num : (0 : ℝ) ≤ 3)) hc2) hS
  nlinarith

/-- `(1 + Y_n)² ≤ (1 + 6/K)² (n + 1)⁴` for `Y_n = 4 (n/(2K)) (2n + 3)`. -/
theorem one_add_Y_sq_le {K : ℝ} (hK : 0 < K) (n : ℕ) :
    (1 + 4 * (1 / (2 * (K / n))) * (2 * n + 3)) ^ 2 ≤ (1 + 6 / K) ^ 2 * ((n : ℝ) + 1) ^ 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hY : 4 * (1 / (2 * (K / n))) * (2 * n + 3) ≤ 6 / K * ((n : ℝ) + 1) ^ 2 := by
    rcases hn.eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · rw [show 4 * (1 / (2 * (K / n))) * (2 * n + 3) = 2 * n * (2 * n + 3) / K by
        field_simp; norm_num]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
      nlinarith
  have h1 : 1 + 4 * (1 / (2 * (K / n))) * (2 * n + 3) ≤ (1 + 6 / K) * ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have h6 : 0 ≤ 6 / K := by positivity
    nlinarith
  have h0 : 0 ≤ 1 + 4 * (1 / (2 * (K / n))) * (2 * n + 3) := by
    rcases hn.eq_or_lt with h | h
    · rw [← h]; simp
    · positivity
  calc (1 + 4 * (1 / (2 * (K / n))) * (2 * n + 3)) ^ 2 ≤ ((1 + 6 / K) * ((n : ℝ) + 1) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = _ := by ring

theorem witnessE1_nonneg (u : ℝ → ℝ) {a θ : ℝ} (ha : 0 ≤ heatHermiteScale a)
    (hρ : 0 ≤ θ * Real.exp (1 - θ)) (hθ : 0 ≤ 1 - θ) (n : ℕ) : 0 ≤ witnessE1 u a θ n :=
  mul_nonneg ha (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (div_nonneg (pow_nonneg hρ _) hθ))

/-- The constant of the geometric truncation decay. -/
def witnessTruncD (u : ℝ → ℝ) (K θ : ℝ) : ℝ :=
  (∫ t, |u t|) ^ 2 * ‖(GaloisForLFunctions.coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 /
    (1 - θ) * (1 + 1 / (2 * π * K))

/-- The truncation error decays geometrically: `e₁(n) ≤ D (n + 1) ρⁿ`, `ρ = θ e^{1-θ}`. -/
theorem witnessE1_le (u : ℝ → ℝ) {K θ : ℝ} (hK : 0 < K) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {n : ℕ}
    (hn : 0 < n) :
    witnessE1 u (K / n) θ n ≤
      witnessTruncD u K θ * (((n : ℝ) + 1) * (θ * Real.exp (1 - θ)) ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < K / n := div_pos hK hn'
  set s := heatHermiteScale (K / n) with hs
  have hs0 : 0 < s := heatHermiteScale_pos ha
  have hs2 : s ^ 2 = 2 * π * (K / n) := heatHermiteScale_sq ha
  set ρ := θ * Real.exp (1 - θ) with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg hθ0 (Real.exp_pos _).le
  have hρ1 : ρ < 1 := mul_exp_one_sub_lt_one hθ0 hθ1
  have hθ' : 0 < 1 - θ := by linarith
  set C := (∫ t, |u t|) ^ 2 * ‖(GaloisForLFunctions.coherentGauss 0).toLp 2 (volume : Measure ℝ)‖ ^ 2 /
    (1 - θ) with hC
  have hC0 : 0 ≤ C := by positivity
  have he : witnessE1 u (K / n) θ n = C * (ρ ^ (2 * n + 1) * (1 / s)) := by
    rw [witnessE1, ← hs, hC, hρ]
    field_simp
  have hinv : 1 / s ≤ (1 + 1 / (2 * π * K)) * ((n : ℝ) + 1) := by
    have h1 : 1 / s ≤ 1 + (1 / s) ^ 2 := by nlinarith [sq_nonneg (1 / s - 1)]
    have h2 : (1 / s) ^ 2 = n / (2 * π * K) := by
      rw [div_pow, hs2]; field_simp
    rw [h2] at h1
    have h3 : (n : ℝ) / (2 * π * K) ≤ (n + 1) * (1 / (2 * π * K)) := by
      rw [div_eq_mul_one_div]; gcongr; linarith
    nlinarith [hn'.le]
  have hpow : ρ ^ (2 * n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
  rw [he]
  calc C * (ρ ^ (2 * n + 1) * (1 / s)) ≤ C * (ρ ^ n * ((1 + 1 / (2 * π * K)) * ((n : ℝ) + 1))) := by
        gcongr
    _ = C * (1 + 1 / (2 * π * K)) * (((n : ℝ) + 1) * ρ ^ n) := by ring

/-- The constant of the collected comparison error. -/
def witnessConst (u : ℝ → ℝ) (B X : ℝ) : ℝ :=
  (2 * Real.sqrt (heatStripConstant X) * witnessG u B X +
      heatStripConstant X * witnessG u B X ^ 2) * (1 + 2 * Real.exp (1 / 8)) *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 +
    (2 + Real.sqrt (heatStripConstant X) * witnessG u B X) * Real.exp (1 / 8) *
      stripMass (deriv (deriv u)) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 +
    (6 + 6 * (heatStripConstant X * witnessG u B X ^ 2)) * Real.exp (1 / 2) *
      ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)

theorem heatStripConstant_nonneg (X : ℝ) : 0 ≤ heatStripConstant X := by
  unfold heatStripConstant; positivity

theorem stripMass_nonneg (f : ℝ → ℝ) : 0 ≤ stripMass f :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem witnessConst_nonneg (u : ℝ → ℝ) (B X : ℝ) : 0 ≤ witnessConst u B X := by
  have hS₂ : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have hS : 0 ≤ ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) := tsum_nonneg fun _ => by positivity
  have hE := heatStripConstant_nonneg X
  have hG : 0 ≤ witnessG u B X := Real.sqrt_nonneg _
  have hU := stripMass_nonneg (deriv (deriv u))
  unfold witnessConst
  positivity

/-- The constant in front of `(n + 1)⁵ ρⁿ` in the truncation smallness conditions. -/
def witnessTruncConst (u : ℝ → ℝ) (K X θ : ℝ) : ℝ :=
  2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessTruncD u K θ * (1 + 6 / K) ^ 2 +
    witnessTruncD u K θ

/-- The truncation error is small: `e₁ ≤ 1` and `C₁ e₁ (1 + Y)² ≤ ξ²`. -/
theorem witness_trunc_small {W Yn D C r K ξ : ℝ} {n : ℕ} (hW : W ≤ D * (((n : ℝ) + 1) * r ^ n))
    (hYb : (1 + Yn) ^ 2 ≤ (1 + 6 / K) ^ 2 * ((n : ℝ) + 1) ^ 4) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (h : (C * D * (1 + 6 / K) ^ 2 + D) * (((n : ℝ) + 1) ^ 5 * r ^ n) ≤ min (ξ ^ 2) 1) :
    W ≤ 1 ∧ C * W * (1 + Yn) ^ 2 ≤ ξ ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hρn : 0 ≤ ((n : ℝ) + 1) * r ^ n := mul_nonneg (zero_le_one.trans hn1) (pow_nonneg hr n)
  have hpow5 : 0 ≤ ((n : ℝ) + 1) ^ 5 * r ^ n :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hn1) 5) (pow_nonneg hr n)
  have hK6 : 0 ≤ (1 + 6 / K) ^ 2 := sq_nonneg _
  have hCD : 0 ≤ C * D * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 5 * r ^ n) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hD) hK6) hpow5
  have hDp : 0 ≤ D * (((n : ℝ) + 1) ^ 5 * r ^ n) := mul_nonneg hD hpow5
  have hsplit : (C * D * (1 + 6 / K) ^ 2 + D) * (((n : ℝ) + 1) ^ 5 * r ^ n) =
      C * D * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 5 * r ^ n) + D * (((n : ℝ) + 1) ^ 5 * r ^ n) := by
    ring
  rw [hsplit] at h
  have h3 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 5 := by
    calc ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((n : ℝ) + 1) ^ 5 := pow_le_pow_right₀ hn1 (by norm_num)
  have hW5 : W ≤ D * (((n : ℝ) + 1) ^ 5 * r ^ n) :=
    hW.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (pow_nonneg hr _)) hD)
  refine ⟨hW5.trans ((le_add_of_nonneg_left hCD).trans (h.trans (min_le_right _ _))), ?_⟩
  have hpoly : W * (1 + Yn) ^ 2 ≤ D * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 5 * r ^ n) := by
    calc W * (1 + Yn) ^ 2
        ≤ (D * (((n : ℝ) + 1) * r ^ n)) * ((1 + 6 / K) ^ 2 * ((n : ℝ) + 1) ^ 4) :=
          mul_le_mul hW hYb (sq_nonneg _) (mul_nonneg hD hρn)
      _ = D * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 5 * r ^ n) := by ring
  calc C * W * (1 + Yn) ^ 2 = C * (W * (1 + Yn) ^ 2) := by ring
    _ ≤ C * (D * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 5 * r ^ n)) := mul_le_mul_of_nonneg_left hpoly hC
    _ = C * D * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 5 * r ^ n) := by ring
    _ ≤ _ := (le_add_of_nonneg_right hDp).trans (h.trans (min_le_left _ _))

/-- The source tail is small: `(4 U rⁿ)² (1 + Y)² ≤ ξ²`. -/
theorem witness_tail_small {U r Yn K ξ : ℝ} {n : ℕ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hYb : (1 + Yn) ^ 2 ≤ (1 + 6 / K) ^ 2 * ((n : ℝ) + 1) ^ 4)
    (h : 16 * U ^ 2 * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 4 * r ^ n) ≤ ξ ^ 2) :
    (4 * U * r ^ n) ^ 2 * (1 + Yn) ^ 2 ≤ ξ ^ 2 := by
  have hr2n : (r ^ n) ^ 2 ≤ r ^ n := by
    rw [← pow_mul]; exact pow_le_pow_of_le_one hr0 hr1 (by omega)
  have hU16 : 0 ≤ 16 * U ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  calc (4 * U * r ^ n) ^ 2 * (1 + Yn) ^ 2 = 16 * U ^ 2 * (r ^ n) ^ 2 * (1 + Yn) ^ 2 := by ring
    _ ≤ 16 * U ^ 2 * r ^ n * ((1 + 6 / K) ^ 2 * ((n : ℝ) + 1) ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr2n hU16) hYb (sq_nonneg _)
          (mul_nonneg hU16 (pow_nonneg hr0 n))
    _ = 16 * U ^ 2 * (1 + 6 / K) ^ 2 * (((n : ℝ) + 1) ^ 4 * r ^ n) := by ring
    _ ≤ ξ ^ 2 := h

theorem small_of_sq_mul_le {v Y ξ : ℝ} (hv : 0 ≤ v) (hY : 0 ≤ Y) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (h : v ^ 2 * (1 + Y) ^ 2 ≤ ξ ^ 2) : v ≤ ξ ∧ v * Y ≤ ξ ∧ v ^ 2 * (1 + Y) ≤ ξ := by
  have h1Y : 1 ≤ 1 + Y := le_add_of_nonneg_right hY
  have hvY : v * (1 + Y) ≤ ξ :=
    (abs_le_of_sq_le_sq' (show (v * (1 + Y)) ^ 2 ≤ ξ ^ 2 by rw [mul_pow]; exact h) hξ0).2
  have hξξ : ξ ^ 2 ≤ ξ := by rw [sq]; exact mul_le_of_le_one_left hξ0 hξ1
  refine ⟨?_, ?_, ?_⟩
  · have : v ≤ v * (1 + Y) := le_mul_of_one_le_right hv h1Y
    linarith only [this, hvY]
  · have : v * (1 + Y) = v + v * Y := by ring
    linarith only [this, hvY, hv]
  · have h3 : (1 + Y) ≤ (1 + Y) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (zero_le_one.trans h1Y) h1Y
    have h2 : v ^ 2 * (1 + Y) ≤ v ^ 2 * (1 + Y) ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg v)
    linarith only [h2, h, hξξ]

/-- **The witness at one heat time.**  If all error inputs are below `ξ` and `ξ C₀ < ε`, and the
smoothed source sum is `ε`-close to `Z` with `Re Z + 2ε ≤ 0`, the pole hyperplane carries a
negative direction of the heat Hankel form. -/
theorem exists_poleHyperplane_re_neg_of_small {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hXA : 2 * A ≤ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * (2 * n + 1 : ℕ)) {k : ℕ}
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : heatMomentRatio (n + 1) k a X ^ k = σ ^ 2) {ξ ε : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hξC : ξ * witnessConst u B X < ε) (he1 : witnessE1 u a θ n ≤ 1)
    (hι : 2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2)
    (hτ : (4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a)))) ^ 2 *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2)
    (hσξ : σ ≤ ξ) (hσY : σ * (4 * (1 / (2 * a)) * (2 * n + 3)) ≤ ξ) {Z : ℂ}
    (hZ : Z.re + 2 * ε ≤ 0)
    (hconv : ‖(∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
      (xiSpectralPoint q) ^ 2) - Z‖ < ε) :
    ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re < 0 := by
  obtain ⟨P, hPd, hPe, hcmp⟩ := exists_poleCorrected_err_le hu hcpt hsupp heven hpole hB ha ha16 n
    hX1 hXA hθ0 hθ1 hN hk hσ0 hσ he1
  refine ⟨P, hPd, hPe, ?_⟩
  have hY0 : 0 ≤ 4 * (1 / (2 * a)) * (2 * (n : ℝ) + 3) :=
    mul_nonneg (mul_nonneg (by norm_num) (one_div_nonneg.2 (mul_pos two_pos ha).le)) (by positivity)
  have he10 : 0 ≤ witnessE1 u a θ n :=
    witnessE1_nonneg u (heatHermiteScale_pos ha).le (mul_nonneg hθ0 (Real.exp_pos _).le)
      (sub_nonneg.2 hθ1.le) n
  have hC₁ : 0 ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) := by positivity
  have hι2 : Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n) ^ 2 *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg hC₁ he10)]; exact hι
  have hU₁ : 0 ≤ ∫ t, |u t| := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨hι1, hι2', hι3⟩ := small_of_sq_mul_le (Real.sqrt_nonneg _) hY0 hξ0 hξ1 hι2
  obtain ⟨hτ1, hτ2', hτ3⟩ := small_of_sq_mul_le
    (mul_nonneg (mul_nonneg (by norm_num) hU₁) (Real.exp_pos _).le) hY0 hξ0 hξ1 hτ
  have herr := witnessErr_le (G := witnessG u B X) (E := heatStripConstant X)
    (U := stripMass (deriv (deriv u))) (S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)
    (S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (Real.sqrt_nonneg _) hσ0 hY0
    (Real.sqrt_nonneg _) (heatStripConstant_nonneg X) (stripMass_nonneg _)
    (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity) hξ1 hι1 hι2' hι3
    hτ1 hτ2' hτ3 hσξ hσY
  have hlt := (hcmp.trans herr).trans_lt hξC
  have hre1 := Complex.re_le_norm (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
      ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
        (xiSpectralPoint q) ^ 2)
  have hre2 := Complex.re_le_norm ((∑' q : XiZeroCopy, heatStripTransform
      (fun x => ((heatSmooth a u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) - Z)
  rw [Complex.sub_re] at hre1 hre2
  linarith only [hlt, hre1, hre2, hconv, hZ]

/-- **The witness at level `n`**, heat time `K/n`. -/
theorem exists_poleHyperplane_re_neg_at_level {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {K : ℝ} (hK0 : 0 < K) {X : ℝ} (hX1 : 1 ≤ X) (hXA : 2 * A ≤ X)
    {θ : ℝ} (hθ : θ = A ^ 2 / (4 * K)) (hθ1 : θ < 1) {ξ ε : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 2)
    (hξC : ξ * witnessConst u B X < ε) {Z : ℂ} (hZ : Z.re + 2 * ε ≤ 0) {m n : ℕ}
    (hn1 : 16 * K < n)
    (hn2 : ∀ a : ℝ, 0 < a → a ≤ 2 * K / ((n + 1 : ℕ) : ℝ) → a < 1 ∧
      heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) a X ^ ((n + 1) / m + 1) ≤ ξ ∧
      heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) a X ^ ((n + 1) / m + 1) *
        (4 * (1 / (2 * a)) * (2 * ((n + 1 : ℕ) : ℝ) + 1)) ≤ ξ)
    (hn3 : witnessTruncConst u K X θ * (((n : ℝ) + 1) ^ 5 * (θ * Real.exp (1 - θ)) ^ n) ≤
      min (ξ ^ 2) 1)
    (hn4 : 16 * (∫ t, |u t|) ^ 2 * (1 + 6 / K) ^ 2 *
      (((n : ℝ) + 1) ^ 4 * Real.exp (-(X ^ 2 / (32 * K))) ^ n) ≤ ξ ^ 2)
    (hn5 : ‖(∑' q : XiZeroCopy, heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) - Z‖ < ε) :
    ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re < 0 := by
  have hn' : (0 : ℝ) < n := (mul_pos (by norm_num) hK0).trans hn1
  have hnpos : 0 < n := by exact_mod_cast hn'
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have ha : 0 < K / n := div_pos hK0 hn'
  have ha16 : K / n ≤ 1 / 16 := by
    rw [div_le_iff₀ hn']; linarith only [hn1]
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hρ0 : 0 ≤ θ * Real.exp (1 - θ) := mul_nonneg hθ0 (Real.exp_pos _).le
  have hN : π * (A / heatHermiteScale (K / n)) ^ 2 ≤ θ * ((2 * n + 1 : ℕ) : ℝ) := by
    have e : π * (A / heatHermiteScale (K / n)) ^ 2 = θ * (2 * n) := by
      rw [div_pow, heatHermiteScale_sq ha, hθ]
      field_simp
      ring
    rw [e]
    push_cast
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hθ0
  have ha2 : K / n ≤ 2 * K / ((n + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hn' (by positivity)]
    push_cast
    linarith only [mul_le_mul_of_nonneg_left hn1' hK0.le]
  obtain ⟨ha1, hσδ, hσY⟩ := hn2 (K / n) ha ha2
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hσ0 : 0 ≤ heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ ((n + 1) / m + 1) :=
    pow_nonneg (heatMomentRatio_pos ha ha1 hX0).le _
  have hσsq : heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ (2 * ((n + 1) / m + 1)) =
      (heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ ((n + 1) / m + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm ((n + 1) / m + 1) 2]
  have hk : heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ (2 * ((n + 1) / m + 1)) ≤
      1 / 2 := by
    rw [hσsq]
    calc _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hσ0 (hσδ.trans hξ1) 2
      _ ≤ 1 / 2 := by norm_num
  have hY : 4 * (1 / (2 * (K / n))) * (2 * ((n + 1 : ℕ) : ℝ) + 1) =
      4 * (1 / (2 * (K / n))) * (2 * n + 3) := by
    push_cast; ring
  rw [hY] at hσY
  have hYb := one_add_Y_sq_le hK0 n
  obtain ⟨he1, hι⟩ := witness_trunc_small (C := 2 * Real.exp 1 * π * Real.exp (X ^ 2))
    (witnessE1_le u hK0 hθ0 hθ1 hnpos) hYb
    (by
      unfold witnessTruncD
      have : 0 < 1 - θ := sub_pos.2 hθ1
      positivity)
    (by positivity) hρ0 hn3
  have hr₀ : 0 ≤ Real.exp (-(X ^ 2 / (32 * K))) := (Real.exp_pos _).le
  have hr₁ : Real.exp (-(X ^ 2 / (32 * K))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hτ := witness_tail_small hr₀ hr₁ hYb hn4
  have hτu_eq : Real.exp (-(X ^ 2 / (32 * K))) ^ n = Real.exp (-(X ^ 2 / (32 * (K / n)))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hτu_eq] at hτ
  exact exists_poleHyperplane_re_neg_of_small hu hcpt hsupp heven hpole hB ha ha16 n hX1 hXA hθ0 hθ1
    hN hk hσ0 hσsq hξ0.le (hξ1.trans (by norm_num)) hξC he1 hι hτ hσδ hσY hZ hn5

/-- **The sharp witness.**  A smooth even pole-vanishing source of half-width `A` with negative
Weil energy makes the heat Hankel form negative on the pole hyperplane at `a = K/n` for all large
`n`, for every `K > A²/4`. -/
theorem eventually_exists_poleHyperplane_heatHankel_neg_of_source {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {A : ℝ}
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (heven : ∀ x, u (-x) = u x)
    (hpole : ∫ x, u x * Real.exp (x / 2) = 0)
    (hneg : (∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ))
      (xiSpectralPoint q) ^ 2).re < 0) {K : ℝ} (hK0 : 0 < K) (hK : A ^ 2 < 4 * K) :
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re < 0 := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∑' q : XiZeroCopy,
      heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2 := ⟨_, rfl⟩
  rw [← hZ] at hneg
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = -Z.re / 3 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; linarith only [hneg]
  have hZε : Z.re + 2 * ε ≤ 0 := by rw [hε_def]; linarith only [hneg]
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuous hu.continuous
  have hB' : ∀ t, |u t| ≤ B := fun t => by rw [← Real.norm_eq_abs]; exact hB t
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 * |A| + 3 * Real.sqrt K + 1 := ⟨_, rfl⟩
  have hsK := Real.sqrt_nonneg K
  have hsK2 := Real.sq_sqrt hK0.le
  have hA0 := abs_nonneg A
  have hX1 : 1 ≤ X := by rw [hX]; linarith only [hsK, hA0]
  have hXA : 2 * A ≤ X := by rw [hX]; linarith only [hsK, le_abs_self A]
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hX8 : 4 * (2 * K) < X ^ 2 := by
    have h3 : 3 * Real.sqrt K < X := by rw [hX]; linarith only [hA0]
    have h2 : (3 * Real.sqrt K) ^ 2 < X ^ 2 :=
      pow_lt_pow_left₀ h3 (mul_nonneg (by norm_num) hsK) two_ne_zero
    rw [mul_pow, hsK2] at h2
    linarith only [h2, hK0]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = A ^ 2 / (4 * K) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; exact hK
  have hρ0 : 0 ≤ θ * Real.exp (1 - θ) := mul_nonneg hθ0 (Real.exp_pos _).le
  have hρ1 : θ * Real.exp (1 - θ) < 1 := mul_exp_one_sub_lt_one hθ0 hθ1
  have hC₀0 := witnessConst_nonneg u B X
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = min (1 / 2) (ε / (witnessConst u B X + 1)) := ⟨_, rfl⟩
  have hξ0 : 0 < ξ := by
    rw [hξ]; exact lt_min (by norm_num) (div_pos hε (by linarith only [hC₀0]))
  have hξ1 : ξ ≤ 1 / 2 := by rw [hξ]; exact min_le_left _ _
  have hξC : ξ * witnessConst u B X < ε := by
    have h1 : ξ ≤ ε / (witnessConst u B X + 1) := by rw [hξ]; exact min_le_right _ _
    calc ξ * witnessConst u B X ≤ ε / (witnessConst u B X + 1) * witnessConst u B X :=
          mul_le_mul_of_nonneg_right h1 hC₀0
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith only [hC₀0])]
          nlinarith only [hε, hC₀0]
  obtain ⟨m, -, hmom⟩ := exists_heatMomentOrder (K := 2 * K) (L := X) (by positivity) hX0 hX8
  have hmom' := (tendsto_add_atTop_nat 1).eventually (hmom ξ hξ0)
  have hdec1 := (tendsto_succ_pow_mul_pow hρ0 hρ1 5).const_mul (witnessTruncConst u K X θ)
  rw [mul_zero] at hdec1
  have hr₀ : 0 ≤ Real.exp (-(X ^ 2 / (32 * K))) := (Real.exp_pos _).le
  have hr₁ : Real.exp (-(X ^ 2 / (32 * K))) < 1 :=
    (Real.exp_lt_exp.2 (neg_lt_zero.2 (by positivity))).trans_eq Real.exp_zero
  have hdec2 := (tendsto_succ_pow_mul_pow hr₀ hr₁ 4).const_mul
    (16 * (∫ t, |u t|) ^ 2 * (1 + 6 / K) ^ 2)
  rw [mul_zero] at hdec2
  have hconv := tendsto_tsum_heatSmooth_sq hu hcpt hK0
  rw [← hZ] at hconv
  have hev5 : ∀ᶠ n : ℕ in atTop, ‖(∑' q : XiZeroCopy, heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) - Z‖ < ε :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hconv).eventually (gt_mem_nhds hε)
  have hev1 : ∀ᶠ n : ℕ in atTop, 16 * K < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  have hev3 : ∀ᶠ n : ℕ in atTop, witnessTruncConst u K X θ *
      (((n : ℝ) + 1) ^ 5 * (θ * Real.exp (1 - θ)) ^ n) ≤ min (ξ ^ 2) 1 :=
    hdec1.eventually (ge_mem_nhds (lt_min (pow_pos hξ0 2) one_pos))
  have hev4 : ∀ᶠ n : ℕ in atTop, 16 * (∫ t, |u t|) ^ 2 * (1 + 6 / K) ^ 2 *
      (((n : ℝ) + 1) ^ 4 * Real.exp (-(X ^ 2 / (32 * K))) ^ n) ≤ ξ ^ 2 :=
    hdec2.eventually (ge_mem_nhds (pow_pos hξ0 2))
  filter_upwards [hev1, hmom', hev5, hev3, hev4] with n hn1 hn2 hn5 hn3 hn4
  exact exists_poleHyperplane_re_neg_at_level hu hcpt hsupp heven hpole hB' hK0 hX1 hXA hθ hθ1 hξ0
    hξ1 hξC hZε hn1 hn2 hn3 hn4 hn5

end

end RHTower
