import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-!
# A bounded overlap rate sees a semilocal window

Let `φ` be a logarithmic Denjoy–Carleman profile, `∫ |φ^{(q)}| ≤ A B_φ^q q! (log(q + 3))^{2q}`,
and let `κ_N` be a dilation sequence: atoms of width `1/κ_N`, overlap `c_N = N/κ_N`. Measure the
overlap in units of the Denjoy–Carleman scale: the **rate** is `c_N / (ℓ ℓ₂²)`, `ℓ = log log κ_N`,
`ℓ₂ = log ℓ` (`dcRate`).

* **A bounded rate sees a bounded window.** If the rate is eventually at least `K` and the atomic
  families are eventually nonnegative, then Weil's form is nonnegative on every `C²` test supported
  in `[−R, R]` with `24 e B_φ ⌈1 + e^{2R+2}⌉ < K` (`nonneg_of_atomicFamilies_nonneg_of_rate`).
  The window radius grows like `½ log K`: a test of radius `R` is synthesized on the block
  `[N/B, N]`, `B = ⌈1 + e^{2R+2}⌉`, whose lowest atoms see overlap `c_N/B`.
* **RH is the union of the bounded rates.** RH holds iff for every `K ≥ 1` the atomic families at
  overlap `K L (log L)²`, `L = log log N`, are eventually nonnegative
  (`riemannHypothesis_iff_forall_bounded_rate`).
* **Every divergent rate is a receiver.** If `c_N/(L (log L)²) → ∞` and `N/c_N → ∞`, RH holds iff
  the atomic families at overlap `c_N` are eventually nonnegative
  (`riemannHypothesis_iff_nonneg_of_divergent_rate`).
-/

noncomputable section

open MeasureTheory Filter Topology RHTower
open scoped Real ContDiff

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The Denjoy–Carleman rate of a dilation sequence: overlap `N/κ_N` over `ℓ ℓ₂²`,
`ℓ = log log κ_N`. -/
def dcRate (κ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) / κ N) / (Real.log (Real.log (κ N)) * Real.log (Real.log (Real.log (κ N))) ^ 2)

/-- The Denjoy–Carleman scale `L (log L)²`, `L = log log N`, in length coordinates. -/
def dcScale (N : ℕ) : ℝ := Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2

/-! ### Quadrature ratio at a bounded rate -/

private theorem rate_dcSynthRatio_nonneg {b Bφ k : ℝ} (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ) (hk : 0 ≤ k)
    (n : ℕ) : 0 ≤ dcSynthRatio b Bφ k n := by
  unfold dcSynthRatio
  have hlog0 : 0 ≤ Real.log (((2 * gevOrder k + 2 : ℕ) : ℝ) + 3) ^ 2 := sq_nonneg _
  positivity

private theorem rate_dcSynthRatio_le {b Bφ : ℝ} (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ) {k : ℝ} {n B : ℕ}
    (hk1 : 1 ≤ k) (hn : 1 ≤ n) (hℓ9 : 9 ≤ Real.log (Real.log k))
    (hll1 : 1 ≤ Real.log (Real.log (Real.log k)))
    (hK1 : 1 ≤ ((n * B : ℕ) : ℝ) / k /
      (Real.log (Real.log k) * Real.log (Real.log (Real.log k)) ^ 2)) :
    dcSynthRatio b Bφ k n ≤
      24 * b * (Real.log ((n * B : ℕ) : ℝ) ^ (3 : ℝ) / n) +
      144 * (Real.log ((n * B : ℕ) : ℝ) ^ (4 : ℝ) / n) +
      24 * Bφ * B * (((n * B : ℕ) : ℝ) / k /
        (Real.log (Real.log k) * Real.log (Real.log (Real.log k)) ^ 2))⁻¹ := by
  set ℓ := Real.log (Real.log k)
  set ℓ₂ := Real.log ℓ
  set W := ℓ * ℓ₂ ^ 2
  have hk0 : 0 < k := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hW1 : 1 ≤ W := by
    have : 1 ≤ ℓ₂ ^ 2 := by nlinarith only [hll1]
    nlinarith only [hℓ9, this]
  have hW0 : 0 < W := by linarith
  have hK'1 : 1 ≤ ((n * B : ℕ) : ℝ) / k := by
    have heq : ((n * B : ℕ) : ℝ) / k = (((n * B : ℕ) : ℝ) / k / W) * W := by field_simp [hW0.ne']
    nlinarith only [hK1, hW1, heq]
  have hkN : k ≤ ((n * B : ℕ) : ℝ) := by
    have := (le_div_iff₀ hk0).mp hK'1; linarith
  have hlogk : 1 < Real.log k := by
    by_contra h; push Not at h
    have : ℓ ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
    linarith
  set L := Real.log ((n * B : ℕ) : ℝ)
  have hℓL : ℓ ≤ L := by
    have h1 : ℓ ≤ Real.log k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact h1.trans (Real.log_le_log hk0 hkN)
  have hL0 : 0 < L := by linarith
  set p : ℝ := ((2 * gevOrder k + 2 : ℕ) : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp6 : p ≤ 6 * ℓ := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ ℓ by linarith)
    simp only [p, gevOrder]; push_cast; linarith
  have hp3_sq : p + 3 ≤ ℓ ^ 2 := by nlinarith only [hp6, hℓ9]
  have hlogp : Real.log (p + 3) ≤ 2 * ℓ₂ := by
    calc Real.log (p + 3) ≤ Real.log (ℓ ^ 2) := Real.log_le_log (by positivity) hp3_sq
      _ = 2 * ℓ₂ := by rw [Real.log_pow]; push_cast; rfl
  have hlogp0 : 0 ≤ Real.log (p + 3) := (Real.log_pos (by linarith [hp0])).le
  have hlogp_sq : Real.log (p + 3) ^ 2 ≤ 4 * ℓ₂ ^ 2 := by
    calc Real.log (p + 3) ^ 2 ≤ (2 * ℓ₂) ^ 2 := pow_le_pow_left₀ hlogp0 hlogp 2
      _ = 4 * ℓ₂ ^ 2 := by ring
  have hpW : p * Real.log (p + 3) ^ 2 ≤ 24 * W := by
    calc p * Real.log (p + 3) ^ 2 ≤ (6 * ℓ) * (4 * ℓ₂ ^ 2) :=
          mul_le_mul hp6 hlogp_sq (sq_nonneg _) (by linarith)
      _ = 24 * W := by dsimp [W]; ring
  have hℓ₂L : ℓ₂ ≤ L := by
    have : ℓ₂ ≤ ℓ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact this.trans hℓL
  have hWL3 : W ≤ L ^ (3 : ℝ) := by
    have h3 : L ^ (3 : ℝ) = L * L ^ 2 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [h3]
    have hsq : ℓ₂ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hℓ₂L 2
    exact mul_le_mul hℓL hsq (sq_nonneg _) hL0.le
  have hL4 : L ^ (4 : ℝ) = L ^ (3 : ℝ) * L := by
    rw [show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add_one hL0.ne']
  set Kq := ((n * B : ℕ) : ℝ) / k / W
  have hB0 : (0 : ℝ) < B := by
    rcases Nat.eq_zero_or_pos B with hBzero | hBpos
    · have hknonpos : k ≤ 0 := by
        simpa only [hBzero, Nat.mul_zero, Nat.cast_zero] using hkN
      exact False.elim ((not_le_of_gt hk0) hknonpos)
    · exact_mod_cast hBpos
  have hkn : k / n = B * Kq⁻¹ * W⁻¹ := by
    dsimp only [Kq]; push_cast; field_simp [hk0.ne', hn0.ne', hW0.ne', hB0.ne']
  have hρe : dcSynthRatio b Bφ k n =
      (p * Real.log (p + 3) ^ 2) * b / n + Bφ * ((p * Real.log (p + 3) ^ 2) * (k / n)) +
        (p * Real.log (p + 3) ^ 2) * p / n := by
    simp only [dcSynthRatio, p]; ring
  rw [hρe, hL4]
  have hpL3 : p * Real.log (p + 3) ^ 2 ≤ 24 * L ^ (3 : ℝ) :=
    hpW.trans (mul_le_mul_of_nonneg_left hWL3 (by norm_num))
  have t1 : (p * Real.log (p + 3) ^ 2) * b / n ≤ 24 * b * (L ^ (3 : ℝ) / n) := by
    rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
    nlinarith [mul_le_mul_of_nonneg_right hpL3 hb]
  have t2 : Bφ * ((p * Real.log (p + 3) ^ 2) * (k / n)) ≤ 24 * Bφ * B * Kq⁻¹ := by
    rw [hkn]
    have hKi : 0 ≤ Kq⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : (p * Real.log (p + 3) ^ 2) * (B * Kq⁻¹ * W⁻¹) ≤
        (24 * W) * (B * Kq⁻¹ * W⁻¹) :=
      mul_le_mul_of_nonneg_right hpW (by positivity)
    have h2 : (24 * W) * (B * Kq⁻¹ * W⁻¹) = 24 * B * Kq⁻¹ := by field_simp [hW0.ne']
    calc Bφ * ((p * Real.log (p + 3) ^ 2) * (B * Kq⁻¹ * W⁻¹))
        ≤ Bφ * ((24 * W) * (B * Kq⁻¹ * W⁻¹)) := mul_le_mul_of_nonneg_left h1 hBφ
      _ = 24 * Bφ * B * Kq⁻¹ := by rw [h2]; ring
  have t3 : (p * Real.log (p + 3) ^ 2) * p / n ≤ 144 * (L ^ (3 : ℝ) * L / n) := by
    rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
    have hpL : p ≤ 6 * L := hp6.trans (by linarith)
    have hpW0 : 0 ≤ p * Real.log (p + 3) ^ 2 := mul_nonneg hp0 (sq_nonneg _)
    nlinarith [mul_le_mul hpL3 hpL hp0 (by positivity)]
  linarith


/-- At rate at least `K > 24 e B_φ B` the synthesis errors still vanish: the quadrature ratio
stays below `e^{−1}`, so the error of order `2⌈log log κ⌉ + 2` is `O((log κ)^{-2})`. -/
private theorem tendsto_dcLogSynthesis_of_rate {κ : ℕ → ℝ} (hk : Tendsto κ atTop atTop)
    {K : ℝ} (hK1 : 1 ≤ K) (hK : ∀ᶠ N : ℕ in atTop, K ≤ dcRate κ N) {B : ℕ} (hB : 1 ≤ B)
    {M b A Bφ A0 : ℝ} (hMA : 0 ≤ M * A) (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ)
    (hKB : 24 * Bφ * B * Real.exp 1 < K) (M' A' : ℕ → ℝ) (R' : ℝ) :
    Tendsto (fun n : ℕ => dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => synthLevy R'
      (dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n)
      (emLip M' A' (κ (n * B)) n) (κ (n * B))) atTop (𝓝 0) := by
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have hK' : Tendsto (fun n => κ (n * B)) atTop atTop := hk.comp hNB
  have hlogK : Tendsto (fun n => Real.log (κ (n * B))) atTop atTop :=
    Real.tendsto_log_atTop.comp hK'
  have hℓ : Tendsto (fun n => Real.log (Real.log (κ (n * B)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogK
  have hℓ₂ : Tendsto (fun n => Real.log (Real.log (Real.log (κ (n * B))))) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓ
  have hKn : ∀ᶠ n : ℕ in atTop, K ≤ ((n * B : ℕ) : ℝ) / κ (n * B) /
      (Real.log (Real.log (κ (n * B))) * Real.log (Real.log (Real.log (κ (n * B)))) ^ 2) :=
    hNB.eventually hK
  have hev := (hK'.eventually_ge_atTop 1).and ((eventually_ge_atTop 1).and
    ((hℓ.eventually_ge_atTop 9).and ((hℓ₂.eventually_ge_atTop 1).and hKn)))
  have hK0 : 0 < K := by linarith
  -- the bounded-rate part `24 B_φ B / K` of the ratio is strictly below `e^{−1}`
  have hδ : 0 < Real.exp (-1) - 24 * Bφ * B / K := by
    rw [sub_pos, div_lt_iff₀ hK0]
    have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1)]
  have hsmall : Tendsto (fun n : ℕ => 24 * b * (Real.log ((n * B : ℕ) : ℝ) ^ (3 : ℝ) / n) +
      144 * (Real.log ((n * B : ℕ) : ℝ) ^ (4 : ℝ) / n)) atTop (𝓝 0) := by
    have := ((tendsto_log_rpow_div (r := 3) hB).const_mul (24 * b)).add
      ((tendsto_log_rpow_div (r := 4) hB).const_mul 144)
    simpa using this
  have hρ1 : ∀ᶠ n : ℕ in atTop, dcSynthRatio b Bφ (κ (n * B)) n ≤ Real.exp (-1) := by
    filter_upwards [hev, hsmall.eventually (gt_mem_nhds hδ)] with n ⟨hk1, hn, hℓ9, hll1, hKq⟩ hs
    have h := rate_dcSynthRatio_le hb hBφ hk1 hn hℓ9 hll1 (hK1.trans hKq)
    have hinv : 24 * Bφ * B * (((n * B : ℕ) : ℝ) / κ (n * B) /
        (Real.log (Real.log (κ (n * B))) * Real.log (Real.log (Real.log (κ (n * B)))) ^ 2))⁻¹ ≤
        24 * Bφ * B / K := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hK0 hKq) (by positivity)
    linarith
  have he₁ : ∀ᶠ n : ℕ in atTop,
      0 ≤ M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) ∧
      M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) ≤
        M * A * (1 / Real.log (κ (n * B)) ^ 2) := by
    filter_upwards [hev, hρ1] with n ⟨hk1, _, hℓ9, _, _⟩ hρn
    have hρ0 := rate_dcSynthRatio_nonneg (k := κ (n * B)) hb hBφ
      (by linarith only [hk1]) n
    refine ⟨mul_nonneg hMA (pow_nonneg hρ0 _), mul_le_mul_of_nonneg_left ?_ hMA⟩
    have hlogk : 1 < Real.log (κ (n * B)) := by
      by_contra h; push Not at h
      have : Real.log (Real.log (κ (n * B))) ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
      linarith
    have h2p : 2 * Real.log (Real.log (κ (n * B))) ≤ ((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ) := by
      have := Nat.le_ceil (Real.log (Real.log (κ (n * B))))
      simp only [gevOrder]; push_cast; linarith
    have h1 := pow_le_pow_left₀ hρ0 hρn (2 * gevOrder (κ (n * B)) + 2)
    have h2 : Real.exp (-1) ^ (2 * gevOrder (κ (n * B)) + 2) =
        Real.exp (-((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (-((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ)) ≤
        Real.exp (-(2 * Real.log (Real.log (κ (n * B))))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-(2 * Real.log (Real.log (κ (n * B))))) =
        1 / Real.log (κ (n * B)) ^ 2 := by
      rw [Real.exp_neg,
        show (2 : ℝ) * Real.log (Real.log (κ (n * B))) =
          ((2 : ℕ) : ℝ) * Real.log (Real.log (κ (n * B))) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith), one_div]
    linarith
  have hinvlog2 : Tendsto (fun n => 1 / Real.log (κ (n * B)) ^ 2) atTop (𝓝 0) := by
    simp only [one_div]
    exact ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlogK).inv_tendsto_atTop
  have hinv : Tendsto (fun n => 1 / κ (n * B)) atTop (𝓝 0) := by
    simp only [one_div]; exact hK'.inv_tendsto_atTop
  have he₁t : Tendsto (fun n => M * A * dcSynthRatio b Bφ (κ (n * B)) n ^
      (2 * gevOrder (κ (n * B)) + 2)) atTop (𝓝 0) := by
    have hup' := hinvlog2.const_mul (M * A)
    rw [mul_zero] at hup'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup'
      (he₁.mono fun n h => h.1) (he₁.mono fun n h => h.2)
  have herr_eq : ∀ n, dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n =
      M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) +
        M * b * dcLogWeight 1 * (1 / κ (n * B)) * A0 := fun _ => rfl
  have he : Tendsto (fun n : ℕ => dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n)
      atTop (𝓝 0) := by
    simp_rw [herr_eq]
    simpa using he₁t.add ((hinv.const_mul (M * b * dcLogWeight 1)).mul_const A0)
  refine ⟨he, ?_⟩
  have hLE : Tendsto (fun n => Real.log (κ (n * B)) *
      dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n ^ 2) atTop (𝓝 0) := by
    simp_rw [herr_eq]
    exact log_mul_sq_tendsto (k := fun n => κ (n * B)) hK' he₁
  -- overlap over `ℓ` is at least `K ℓ₂² → ∞`, which drives the Lipschitz part
  have hK'ℓ1 : Tendsto (fun n : ℕ => ((n * B : ℕ) : ℝ) / κ (n * B) /
      Real.log (Real.log (κ (n * B))) ^ (1 : ℝ)) atTop atTop := by
    have hsq : Tendsto (fun n => K * Real.log (Real.log (Real.log (κ (n * B)))) ^ 2)
        atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hℓ₂).const_mul_atTop hK0
    refine tendsto_atTop_mono' atTop ?_ hsq
    filter_upwards [hev] with n ⟨hk1, _, hℓ9, hll1, hKq⟩
    rw [Real.rpow_one]
    have hℓpos : 0 < Real.log (Real.log (κ (n * B))) := by linarith
    have hℓ₂pos : 0 < Real.log (Real.log (Real.log (κ (n * B)))) ^ 2 := by positivity
    have heq : ((n * B : ℕ) : ℝ) / κ (n * B) / Real.log (Real.log (κ (n * B))) =
        ((n * B : ℕ) : ℝ) / κ (n * B) /
          (Real.log (Real.log (κ (n * B))) * Real.log (Real.log (Real.log (κ (n * B)))) ^ 2) *
          Real.log (Real.log (Real.log (κ (n * B)))) ^ 2 := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hKq hℓ₂pos.le
  have hev1 : ∀ᶠ n : ℕ in atTop, 1 ≤ κ (n * B) ∧ 1 ≤ n ∧
      1 ≤ Real.log (Real.log (κ (n * B))) ∧
      1 ≤ ((n * B : ℕ) : ℝ) / κ (n * B) / Real.log (Real.log (κ (n * B))) ^ (1 : ℝ) := by
    filter_upwards [hev, hK'ℓ1.eventually_ge_atTop 1] with n ⟨hk1, hn, hℓ9, _, _⟩ h1
    exact ⟨hk1, hn, by linarith, h1⟩
  exact tendsto_synthLevy_of he hLE (gevrey_lip_tendsto zero_le_one hK' hK'ℓ1 hev1 M' A')

private theorem rate_abs_iteratedDeriv_mollify_le {φ g : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hg : Continuous g)
    {Mg : ℝ} (hgM : ∀ t, |g t| ≤ Mg) {m : ℝ} (hm : 0 < m) {A Bφ : ℝ}
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    (l : ℕ) (x : ℝ) :
    |iteratedDeriv l (mollify g φ m) x| ≤ Mg * A * (Bφ * m) ^ l * dcLogWeight l := by
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM 0)
  have hψ : ContDiff ℝ ∞ (iteratedDeriv l (dilate m φ)) := by
    rw [iteratedDeriv_eq_iterate]; exact (contDiff_dilate_smooth hφ m).iterate_deriv l
  have hψc := hasCompactSupport_iteratedDeriv (hasCompactSupport_dilate_of hφ1 hm) l
  rw [iteratedDeriv_mollify hφ hφ1 hg hm l]
  refine (abs_integral_mul_le_sup_mul hgM
    (hψ.continuous.integrable_of_hasCompactSupport hψc) x).trans ?_
  rw [integral_abs_iteratedDeriv_dilate hφ hm l]
  have := mul_le_mul_of_nonneg_left (hA l) (mul_nonneg hMg (pow_nonneg hm.le l))
  calc Mg * (m ^ l * ∫ t, |iteratedDeriv l φ t|) = Mg * m ^ l * ∫ t, |iteratedDeriv l φ t| := by
        ring
    _ ≤ Mg * m ^ l * (A * Bφ ^ l * dcLogWeight l) := this
    _ = _ := by rw [mul_pow]; ring


/-! ### The window of a bounded rate -/

/-- **A bounded rate sees a bounded window.** If the Denjoy–Carleman rate of `κ` is eventually at
least `K` and a stable form is eventually nonnegative on the atomic families of width `1/κ_N`,
then it is nonnegative on every `C²` test supported in `[−R, R]` with
`24 e B_φ ⌈1 + e^{2(R+1)}⌉ < K`. Mechanism: mollify a negative test, synthesize it on the block
`[N/B, N]`, `B = blockSize (R + 1)`; the quadrature ratio there is at most `24 B_φ B/K < e^{−1}`. -/
theorem nonneg_of_atomicFamilies_nonneg_of_rate {Φ : (ℝ → ℝ) → ℝ} (hΦ : StableForm Φ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {κ : ℕ → ℝ} (hk : Tendsto κ atTop atTop) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ᶠ N : ℕ in atTop, K ≤ dcRate κ N)
    (H : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ, 0 ≤ Φ (atomicTest N x (dilate (κ N) φ)))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgR : SupportedIn R g)
    (hRK : 24 * Bφ * blockSize (R + 1) * Real.exp 1 < K) : 0 ≤ Φ g := by
  by_contra hneg0
  push Not at hneg0
  have hgc : HasCompactSupport g := hasCompactSupport_of_vanishes hgR
  obtain ⟨-, Mg, Lg, -, -, hgM, hgL⟩ := exists_test_bounds hg hgc
  -- 1. mollify `g` by `φ` into a negative smooth test `G` supported in `[−(R+1), R+1]`
  obtain ⟨Err0, hErr0, hle0⟩ := hΦ.2 g hg hgc (R + 1) (by linarith)
    (fun u hu => hgR u (by linarith))
  obtain ⟨he0, hV0, -, -⟩ := tendsto_mollifyErr Lg (∫ s, |φ s|) Mg (∫ s, |deriv φ s|) (R + 1)
  obtain ⟨m0, hm0_err, hm0_1⟩ := (((hErr0 _ _ he0 hV0).eventually (gt_mem_nhds
    (show (0 : ℝ) < -Φ g by linarith))).and (eventually_ge_atTop 1)).exists
  have hm0_r : (1 : ℝ) ≤ m0 := by exact_mod_cast hm0_1
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM 0)
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa [dcLogWeight_zero] using this
  set G := mollify g φ m0
  have hG : ContDiff ℝ ∞ G := contDiff_mollify hφ hφ1 hg.continuous (by linarith)
  have hGR : SupportedIn (R + 1) G := mollify_supportedIn hφ1 hgR hm0_r
  have hGc : HasCompactSupport G := hasCompactSupport_of_vanishes hGR
  have hGneg : Φ G < 0 := by
    obtain ⟨hD2, hDR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint hg hgR hgM hgL hm0_r
    have h := hle0 _ _ _ _ hD2 hDR hsup hlip hm0_r
    have he' : (fun u => g u + (mollify g φ m0 u - g u)) = G := by funext u; dsimp [G]; ring
    rw [he'] at h; linarith
  have hGM : ∀ l t, |iteratedDeriv l G t| ≤ (Mg * A) * (Bφ * m0) ^ l * dcLogWeight l :=
    fun l t => rate_abs_iteratedDeriv_mollify_le hφ hφ1 hg.continuous hgM
      (by linarith) hA l t
  -- 2. synthesize `G` on the block of size `blockSize (R + 1)` at the bounded rate
  have hG2 : ContDiff ℝ 2 G := hG.of_le (natCast_le_infty 2)
  obtain ⟨Err, hErr, hle⟩ := hΦ.2 G hG2 hGc (R + 1 + 1) (by linarith)
    (fun u hu => hGR u (by linarith))
  set B := blockSize (R + 1)
  have hB : 1 ≤ B := one_le_blockSize (R + 1)
  obtain ⟨he, hV⟩ := tendsto_dcLogSynthesis_of_rate hk hK1 hK hB (M := Mg * A) (b := Bφ * m0)
    (A := A) (Bφ := Bφ) (A0 := ∫ s, |φ s|) (by positivity) (by positivity) hBφ hRK
    (fun l => (Mg * A) * (Bφ * m0) ^ l * dcLogWeight l)
    (fun q => ∫ s, |iteratedDeriv q φ s|) (R + 1 + 1)
  have h1 := (hErr _ _ he hV).eventually (gt_mem_nhds (show (0 : ℝ) < -Φ G by linarith))
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have h3 := hNB.eventually (hk.eventually_ge_atTop 1)
  have hfr : ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ, Φ (atomicTest N x (dilate (κ N) φ)) < 0 := by
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨n, hn1, hk', hn3, hna⟩ :=
      (h1.and (h3.and ((eventually_ge_atTop 2).and (eventually_ge_atTop a)))).exists
    refine ⟨n * B, hna.trans (Nat.le_mul_of_pos_right n hB), ?_⟩
    obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ := exists_dcLogSynthesis hφ hφ1 hφint hG hGR
      (by positivity) (by positivity) hBφ hGM hA hn3 hk' (gevOrder (κ (n * B)))
    refine ⟨x, ?_⟩
    rw [hx, hΦ.1 _ (hG2.add hD2) (hGc.add (hasCompactSupport_of_vanishes hDR))]
    have := hle D _ _ _ hD2 hDR hsup hlip hk'
    linarith
  obtain ⟨N, ⟨x, hx⟩, hN⟩ := (hfr.and_eventually H).exists
  exact absurd (hN x) (not_le.mpr hx)

/-! ### Length coordinates -/

private theorem loglog_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem logloglog_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N))) atTop atTop :=
  Real.tendsto_log_atTop.comp loglog_atTop

theorem dcScale_atTop : Tendsto dcScale atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ loglog_atTop
  filter_upwards [loglog_atTop.eventually_ge_atTop 0, logloglog_atTop.eventually_ge_atTop 1]
    with N h0 h1
  unfold dcScale
  have : (1 : ℝ) ≤ Real.log (Real.log (Real.log N)) ^ 2 := by nlinarith
  nlinarith

/-- The scale `L (log L)²` is `o(N)`: the dilation `N/(K L (log L)²)` tends to infinity. -/
theorem tendsto_div_const_mul_dcScale {K : ℝ} (hK : 0 < K) :
    Tendsto (fun N : ℕ => (N : ℝ) / (K * dcScale N)) atTop atTop := by
  have h3 := (overlapGrowthSuperGevrey_of_two_lt (show (2 : ℝ) < 3 by norm_num)).1
  refine tendsto_atTop_mono' atTop ?_ (h3.const_mul_atTop (inv_pos.mpr hK))
  filter_upwards [loglog_atTop.eventually_ge_atTop 1, logloglog_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with N hL hu hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 < dcScale N := by unfold dcScale; positivity
  have hle : dcScale N ≤ superGevreyRatio 3 N := by
    unfold dcScale superGevreyRatio
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : Real.log (Real.log (Real.log N)) ^ 2 ≤ Real.log (Real.log (Real.log N)) ^ 3 :=
      pow_le_pow_right₀ hu (by norm_num)
    exact mul_le_mul_of_nonneg_left this (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, ← mul_assoc, mul_comm K⁻¹ (N : ℝ)]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hS hle) (by positivity)

/-- At overlap `c_N ≥ 1` with dilation `κ_N = N/c_N → ∞`, the rate is at least `c_N/(L (log L)²)`,
since `log log κ_N ≤ log log N`. -/
theorem eventually_div_dcScale_le_dcRate {c : ℕ → ℝ}
    (hcN : Tendsto (fun N : ℕ => (N : ℝ) / c N) atTop atTop) (hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ c N) :
    ∀ᶠ N : ℕ in atTop, c N / dcScale N ≤ dcRate (fun N : ℕ => (N : ℝ) / c N) N := by
  have hl := Real.tendsto_log_atTop.comp hcN
  have hll := Real.tendsto_log_atTop.comp hl
  have hlll := Real.tendsto_log_atTop.comp hll
  filter_upwards [hc1, hlll.eventually_gt_atTop 0, hl.eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with N hc hu hl0 hN
  simp only [Function.comp] at hu hl0
  set κ := (N : ℝ) / c N with hκ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := by linarith
  have hκ0 : 0 < κ := div_pos hN0 hc0
  have hκN : κ ≤ N := div_le_self hN0.le hc
  have hℓ1 : 1 < Real.log (Real.log κ) := by
    by_contra h; push Not at h
    have : Real.log (Real.log (Real.log κ)) ≤ 0 := by
      rcases le_or_gt (Real.log (Real.log κ)) 0 with h0 | h0
      · exact Real.log_nonpos_of_nonpos h0
      · exact Real.log_nonpos h0.le h
    linarith
  have hlogκ : Real.log κ ≤ Real.log N := Real.log_le_log hκ0 hκN
  have hll : Real.log (Real.log κ) ≤ Real.log (Real.log N) := Real.log_le_log hl0 hlogκ
  have hlll : Real.log (Real.log (Real.log κ)) ≤ Real.log (Real.log (Real.log N)) :=
    Real.log_le_log (by linarith) hll
  have hden : Real.log (Real.log κ) * Real.log (Real.log (Real.log κ)) ^ 2 ≤ dcScale N :=
    mul_le_mul hll (pow_le_pow_left₀ hu.le hlll 2) (sq_nonneg _) (by linarith)
  have hden0 : 0 < Real.log (Real.log κ) * Real.log (Real.log (Real.log κ)) ^ 2 := by positivity
  have hNκ : (N : ℝ) / κ = c N := by rw [hκ, div_div_cancel₀ hN0.ne']
  show c N / dcScale N ≤ (N : ℝ) / κ / (Real.log (Real.log κ) * Real.log (Real.log (Real.log κ)) ^ 2)
  rw [hNκ]
  exact div_le_div_of_nonneg_left hc0.le hden0 hden

/-! ### RH in terms of the rate -/

private theorem weilQuad_atomicTest_nonneg_of_RH (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ1 : VanishesOff φ) {k : ℝ} (hk : 0 < k) (N : ℕ) (x : ℕ → ℝ) :
    0 ≤ weilQuad (atomicTest N x (dilate k φ)) := by
  obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
  exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc

/-- **Every divergent rate is a receiver.** If `c_N/(L (log L)²) → ∞` and `N/c_N → ∞`, then RH
holds iff Weil's form is eventually nonnegative on the atomic families at overlap `c_N`. -/
theorem riemannHypothesis_iff_nonneg_of_divergent_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {c : ℕ → ℝ} (hc : Tendsto (fun N => c N / dcScale N) atTop atTop)
    (hcN : Tendsto (fun N : ℕ => (N : ℝ) / c N) atTop atTop) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / c N) φ)) := by
  have hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ c N := by
    filter_upwards [hc.eventually_ge_atTop 1, dcScale_atTop.eventually_ge_atTop 1] with N h hS
    have hS0 : 0 < dcScale N := by linarith
    rw [le_div_iff₀ hS0] at h
    linarith
  refine riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey hφ hφ1 hφint hBφ hA
    ⟨hcN, tendsto_atTop_mono' atTop (eventually_div_dcScale_le_dcRate hcN hc1) hc⟩

/-- **RH is the union of the bounded rates.** RH holds iff for every `K ≥ 1`, Weil's form is
eventually nonnegative on the atomic families at overlap `K L (log L)²`, `L = log log N`. A single
bounded rate only sees the window of `nonneg_of_atomicFamilies_nonneg_of_rate`. -/
theorem riemannHypothesis_iff_forall_bounded_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    {A Bφ : ℝ} (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q) :
    RiemannHypothesis ↔ ∀ K : ℝ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * dcScale N)) φ)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  constructor
  · intro hRH K hK
    filter_upwards [(tendsto_div_const_mul_dcScale (by linarith : (0 : ℝ) < K)).eventually_gt_atTop 0]
      with N hk x
    exact weilQuad_atomicTest_nonneg_of_RH hRH hφ2 hφ1 hk N x
  · intro H
    refine RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mpr fun g hg hgc => ?_
    obtain ⟨R, -, -, hR, hgR, -, -⟩ := exists_test_bounds hg hgc
    set K : ℝ := max 1 (24 * Bφ * blockSize (R + 1) * Real.exp 1 + 1)
    have hK1 : 1 ≤ K := le_max_left _ _
    have hcN := tendsto_div_const_mul_dcScale (by linarith : (0 : ℝ) < K)
    have hrate : ∀ᶠ N : ℕ in atTop, K ≤ dcRate (fun N : ℕ => (N : ℝ) / (K * dcScale N)) N := by
      have hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ K * dcScale N := by
        filter_upwards [dcScale_atTop.eventually_ge_atTop 1] with N hS
        nlinarith
      filter_upwards [eventually_div_dcScale_le_dcRate hcN hc1,
        dcScale_atTop.eventually_gt_atTop 0] with N h hS
      rwa [mul_div_assoc, div_self hS.ne', mul_one] at h
    exact nonneg_of_atomicFamilies_nonneg_of_rate stableForm_weilQuad hφ hφ1 hφint hBφ hA hcN hK1
      hrate (H K hK1) hg hR hgR (by
        have := le_max_right 1 (24 * Bφ * blockSize (R + 1) * Real.exp 1 + 1)
        linarith)

/-- **The Steklov window.** For the fixed Steklov profile, eventual nonnegativity at overlap
`K L (log L)²` gives Weil positivity on every `C²` test supported in `[−R, R]` with
`288 e ⌈1 + e^{2(R+1)}⌉ < K`. -/
theorem steklovDCProfile_window {K : ℝ} (hK1 : 1 ≤ K)
    (H : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * dcScale N)) steklovDCProfile)))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgR : SupportedIn R g)
    (hRK : 288 * blockSize (R + 1) * Real.exp 1 < K) : 0 ≤ weilQuad g := by
  have hcN := tendsto_div_const_mul_dcScale (by linarith : (0 : ℝ) < K)
  have hrate : ∀ᶠ N : ℕ in atTop, K ≤ dcRate (fun N : ℕ => (N : ℝ) / (K * dcScale N)) N := by
    have hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ K * dcScale N := by
      filter_upwards [dcScale_atTop.eventually_ge_atTop 1] with N hS
      nlinarith
    filter_upwards [eventually_div_dcScale_le_dcRate hcN hc1,
      dcScale_atTop.eventually_gt_atTop 0] with N h hS
    rwa [mul_div_assoc, div_self hS.ne', mul_one] at h
  exact nonneg_of_atomicFamilies_nonneg_of_rate stableForm_weilQuad contDiff_steklovDCProfile
    steklovDCProfile_vanishesOff integral_steklovDCProfile (by norm_num : (0 : ℝ) ≤ 12)
    integral_abs_iteratedDeriv_steklovDCProfile_le hcN hK1 hrate H hg hR hgR (by linarith)

end GaloisForLFunctions.TransMetzlerWeilPositivity
