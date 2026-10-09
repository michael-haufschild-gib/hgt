import GaloisForLFunctions.RHTower.LittlewoodWindowTest
import Zeta23.Final
import Zeta23.GammaFacts.Complete
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

/-!
# Short windows of zeros under RH (Littlewood)

Under the Riemann hypothesis every window `(t, t + C/log log t]` eventually contains at least `m`
zeros of `ξ`, for every `m` (`riemannHypothesis_eventually_xiZeroCount_window_ge`).

**Proof.**  Weil's explicit formula (Zeta23, unconditional) for the window
`f_k(u) = Φ_ℓ^{(k)}(u)e^{−iTu}`, supported in `[−ℓ, ℓ]`, reads under RH
`Σ_ρ m_ρ ψ_k(γ_ρ − T) = ∫ ψ_k(τ − T) ν_X(τ) dτ`, with `ψ_k = |(Φ_ℓ^{(k)})^|²` and `X = e^{2ℓ}`
(`explicitFormula_window`).  Since `ψ₁(x) = x² ψ₀(x)` and `ψ₀ ≤ (ℓA)²`,
`ψ₀(x) ≤ (ℓA)² 1_{(−δ,δ]}(x) + ψ₁(x)/δ²`, so

  `Σ m ψ₀(γ − T) ≤ (ℓA)² N(T − δ, T + δ) + δ⁻² Σ m ψ₁(γ − T)`.

The density `ν_X = μ + Π_X + P_X` satisfies `|ν_X − μ| ≤ K(X) ≪ √X`.  The archimedean density `μ` is
monotone in `|τ|` with Stirling asymptotics `μ(τ) = log(|τ|/2π)/2π + O(τ^{−2})`.  Plancherel gives
`∫ψ₀ = 2πℓE` and `∫ψ₁ = 2πF₁/ℓ`.  With `δ = D/ℓ`, `D² > 2F₁/E` and `e^ℓ ≪ (log T)^{1/4}`, the
window count is `≫ log T/ℓ`.
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-- `ψ_k(y) = |(Φ_ℓ^{(k)})^(y)|²`. -/
def psi (ℓ : ℝ) (k : ℕ) (y : ℝ) : ℝ := ‖paperFT (cb ℓ k) (y : ℂ)‖ ^ 2

theorem psi_nonneg (ℓ : ℝ) (k : ℕ) (y : ℝ) : 0 ≤ psi ℓ k y := sq_nonneg _

/-! ## The window spectra -/

/-- `∫|Φ^{(k)}|`. -/
def mass (k : ℕ) : ℝ := ∫ v, |iteratedDeriv k bump v|

/-- `∫(Φ^{(k)})²`. -/
def energy (k : ℕ) : ℝ := ∫ v, iteratedDeriv k bump v ^ 2

theorem mass_nonneg (k : ℕ) : 0 ≤ mass k := integral_nonneg fun _ => abs_nonneg _

theorem energy_nonneg (k : ℕ) : 0 ≤ energy k := integral_nonneg fun _ => sq_nonneg _

theorem energy_zero_pos : 0 < energy 0 := by
  have hc : Continuous (fun v => iteratedDeriv 0 bump v ^ 2) :=
    ((contDiff_iteratedDeriv_bump 0 (n := 0)).continuous).pow 2
  have hs : HasCompactSupport (fun v => iteratedDeriv 0 bump v ^ 2) := by
    refine hasCompactSupport_of_support_subset_abs (Λ := 1) (fun v hv => ?_)
    by_contra h
    exact hv (by simp [iteratedDeriv_bump_eq_zero 0 (not_le.mp h)])
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs (fun v => sq_nonneg _)
    (x := 0) (by simp [bump_zero])

theorem continuous_paperFT_cb {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    Continuous (fun y : ℝ => paperFT (cb ℓ k) (y : ℂ)) := by
  have hf := integrable_cb hℓ k
  unfold paperFT
  refine continuous_of_dominated (bound := fun u => ‖cb ℓ k u‖) (fun r => ?_) (fun r => ?_)
    hf.norm ?_
  · exact hf.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_cexp_I_mul]
    simp
  · exact Eventually.of_forall fun u => by fun_prop

/-- `|ĥ(y)|(1 + y²) ≤ ∫|h| + ∫|h″|` for `h = Φ_ℓ^{(k)}`. -/
theorem norm_paperFT_cb_mul_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (y : ℝ) :
    ‖paperFT (cb ℓ k) y‖ * (1 + y ^ 2) ≤
      ℓ ^ (1 - (k : ℤ)) * mass k + ℓ ^ (1 - ((k + 2 : ℕ) : ℤ)) * mass (k + 2) := by
  have h1 := norm_paperFT_cb_le hℓ k y
  have hb : 0 ≤ ℓ ^ (1 - ((k + 2 : ℕ) : ℤ)) * mass (k + 2) :=
    mul_nonneg (zpow_nonneg hℓ.le _) (mass_nonneg _)
  have h2 : ‖paperFT (cb ℓ k) y‖ * y ^ 2 ≤ ℓ ^ (1 - ((k + 2 : ℕ) : ℤ)) * mass (k + 2) := by
    rcases eq_or_ne y 0 with rfl | hy
    · simpa using hb
    · have := norm_paperFT_cb_le_div hℓ k hy
      rw [le_div_iff₀ (by positivity)] at this
      exact this
  simp only [mass] at h1 h2 hb ⊢
  nlinarith

theorem integrable_psi {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) : Integrable (psi ℓ k) := by
  set a := ℓ ^ (1 - (k : ℤ)) * mass k
  set b := ℓ ^ (1 - ((k + 2 : ℕ) : ℤ)) * mass (k + 2)
  have ha : 0 ≤ a := mul_nonneg (zpow_nonneg hℓ.le _) (mass_nonneg _)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (a * (a + b)))
    ((continuous_paperFT_cb hℓ k).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h1 := norm_paperFT_cb_le hℓ k y
  have h2 := norm_paperFT_cb_mul_le hℓ k y
  have hn := norm_nonneg (paperFT (cb ℓ k) (y : ℂ))
  have hy : 0 < 1 + y ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg ℓ k y), psi, ← div_eq_mul_inv,
    le_div_iff₀ hy]
  calc ‖paperFT (cb ℓ k) y‖ ^ 2 * (1 + y ^ 2)
      = ‖paperFT (cb ℓ k) y‖ * (‖paperFT (cb ℓ k) y‖ * (1 + y ^ 2)) := by ring
    _ ≤ a * (a + b) := mul_le_mul h1 h2 (by positivity) ha

/-- **Plancherel**: `∫ψ_k = 2π ℓ^{1−2k} ∫(Φ^{(k)})²`. -/
theorem integral_psi {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    ∫ y, psi ℓ k y = 2 * Real.pi * (ℓ ^ (1 - 2 * (k : ℤ)) * energy k) :=
  integral_norm_sq_paperFT_cb hℓ k

theorem integral_psi_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y, psi ℓ 0 y = 2 * Real.pi * ℓ * energy 0 := by
  rw [integral_psi hℓ 0]; simp; ring

theorem integral_psi_one {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y, psi ℓ 1 y = 2 * Real.pi * energy 1 / ℓ := by
  rw [integral_psi hℓ 1]; norm_num; ring

theorem integral_psi_two {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ y, psi ℓ 2 y = 2 * Real.pi * energy 2 / ℓ ^ 3 := by
  rw [integral_psi hℓ 2]; norm_num; field_simp

/-! ## The density `ν_X` -/

theorem abs_PiX_le {X : ℝ} (hX : 1 ≤ X) (τ : ℝ) : |PiX X τ| ≤ 2 / Real.pi * (X + 2) := by
  have hπ := Real.pi_pos
  have hsre : (1 / 2 + I * (τ : ℂ)).re = 1 / 2 := by simp
  have hsn : (1 : ℝ) / 2 ≤ ‖(1 / 2 + I * (τ : ℂ))‖ := by
    have := Complex.abs_re_le_norm (1 / 2 + I * (τ : ℂ))
    rw [hsre] at this
    exact (le_abs_self _).trans this
  have hXs : ‖(X : ℂ) ^ (1 / 2 + I * (τ : ℂ))‖ ≤ X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hsre]
    calc X ^ (1 / 2 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = X := Real.rpow_one X
  have hq : ‖((X : ℂ) ^ (1 / 2 + I * (τ : ℂ)) - 1) / (1 / 2 + I * (τ : ℂ))‖ ≤ 2 * (X + 1) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    have h := norm_sub_le ((X : ℂ) ^ (1 / 2 + I * (τ : ℂ))) 1
    rw [norm_one] at h
    nlinarith
  have h3 := (Complex.abs_re_le_norm _).trans hq
  have h1 : 0 < 1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) := by positivity
  have h2 : 1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) ≤ 2 / Real.pi := by
    rw [div_le_div_iff₀ (by positivity) hπ]; nlinarith [sq_nonneg τ]
  have e : PiX X τ = 1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) *
      (((X : ℂ) ^ (1 / 2 + I * (τ : ℂ)) - 1) / (1 / 2 + I * (τ : ℂ))).re := rfl
  rw [e]
  rw [abs_le] at h3 ⊢
  have hπi : 0 < 1 / Real.pi := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left h3.1 hπi.le
    have e2 : 1 / Real.pi * -(2 * (X + 1)) = -(2 / Real.pi * (X + 1)) := by ring
    have e3 : 2 / Real.pi * (X + 2) = 2 / Real.pi * (X + 1) + 2 / Real.pi := by ring
    linarith
  · have := mul_le_mul_of_nonneg_left h3.2 hπi.le
    have e2 : 1 / Real.pi * (2 * (X + 1)) = 2 / Real.pi * (X + 1) := by ring
    have e3 : 2 / Real.pi * (X + 2) = 2 / Real.pi * (X + 1) + 2 / Real.pi := by ring
    linarith

theorem abs_PX_le {X : ℝ} (hX : 0 ≤ X) (τ : ℝ) : |PX X τ| ≤ X ^ 2 / Real.pi := by
  have hπ := Real.pi_pos
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      |ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (τ * Real.log n)| ≤ X := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hX)
    have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hlog : ArithmeticFunction.vonMangoldt n ≤ n :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        (by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)])
    rw [abs_mul, abs_of_nonneg (div_nonneg hΛ (Real.sqrt_nonneg _))]
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * |Real.cos (τ * Real.log n)|
        ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (div_nonneg hΛ (Real.sqrt_nonneg _))
      _ ≤ ArithmeticFunction.vonMangoldt n := by rw [mul_one]; exact div_le_self hΛ hsq
      _ ≤ X := hlog.trans hnX
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm)
  rw [Nat.card_Ioc, nsmul_eq_mul] at hsum
  have hfl : ((⌊X⌋₊ - 0 : ℕ) : ℝ) ≤ X := by simp [Nat.floor_le hX]
  have e : PX X τ = -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (τ * Real.log n) := rfl
  rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  calc 1 / Real.pi * |∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (τ * Real.log n)|
      ≤ 1 / Real.pi * (X * X) :=
        mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hfl hX)) (by positivity)
    _ = X ^ 2 / Real.pi := by ring

/-- `|ν_X − μ| ≤ 3X²` for `X ≥ 1`. -/
theorem abs_nuX_sub_mu_le {X : ℝ} (hX : 1 ≤ X) (τ : ℝ) : |nuX X τ - mu τ| ≤ 3 * X ^ 2 := by
  have h1 := abs_PiX_le hX τ
  have h2 := abs_PX_le (X := X) (by linarith) τ
  have hπ := Real.pi_gt_three
  have e : nuX X τ - mu τ = PiX X τ + PX X τ := by unfold nuX; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h3 : 2 / Real.pi * (X + 2) + X ^ 2 / Real.pi = (2 * X + 4 + X ^ 2) / Real.pi := by ring
  have h4 : (2 * X + 4 + X ^ 2) / Real.pi ≤ 3 * X ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-! ## The archimedean density `μ` -/

theorem mu_abs (τ : ℝ) : mu |τ| = mu τ := by
  rcases le_or_gt 0 τ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, gammaFacts.even]

theorem neg_one_lt_mu (τ : ℝ) : -1 < mu τ :=
  gammaFacts.neg_one_lt_mu_zero.trans_le (gammaFacts.mu_zero_le τ)

theorem mu_le_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) : mu a ≤ mu b := by
  rw [← mu_abs a, ← mu_abs b]
  exact gammaFacts.monotoneOn (abs_nonneg a) (abs_nonneg b) h

theorem mu_mono {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : mu a ≤ mu b :=
  mu_le_of_abs_le (by rw [abs_of_nonneg ha, abs_of_nonneg (ha.trans h)]; exact h)

/-- A nonnegative Stirling constant: `|μ(τ) − log(|τ|/2π)/2π| ≤ C/τ²` for `|τ| ≥ 1`. -/
theorem exists_stirling : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  refine ⟨max C 0, le_max_right _ _, fun τ hτ => (hC τ hτ).trans ?_⟩
  exact div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

/-! ## The zeros under RH -/

/-- Under RH every nontrivial zero has real spectral coordinate `γ_ρ = Im ρ`. -/
theorem gammaOf_eq_im_of_RH (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) : gammaOf ρ = (ρ.im : ℂ) := by
  rw [zetaZeroConfig_carrier] at hρ
  obtain ⟨hz, hre0, hre1⟩ := hρ
  have hre : ρ.re = 1 / 2 := by
    refine hRH ρ hz ?_ ?_
    · rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re < 0 := by
        simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
          Complex.add_im, Complex.natCast_im, Complex.one_im]
        norm_num
        positivity
      linarith
    · intro h; rw [h] at hre1; simp at hre1
  unfold gammaOf
  apply Complex.ext
  · simp [hre]
  · simp [hre]

theorem wsummand_window (hRH : RiemannHypothesis) (ℓ T : ℝ) (k : ℕ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ =
      (((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k (ρ.im - T) : ℝ) : ℂ) := by
  unfold ZeroConfig.Wsummand
  rw [gammaOf_eq_im_of_RH hRH hρ, Complex.conj_ofReal, paperFT_window]
  rw [show (ρ.im : ℂ) - T = ((ρ.im - T : ℝ) : ℂ) by push_cast; ring]
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [psi]
  push_cast
  ring

theorem integrand_window (ℓ T X : ℝ) (k : ℕ) (τ : ℝ) :
    paperFT (window ℓ T k) τ * (starRingEnd ℂ) (paperFT (window ℓ T k) τ) * (nuX X τ : ℂ) =
      ((psi ℓ k (τ - T) * nuX X τ : ℝ) : ℂ) := by
  rw [paperFT_window, show (τ : ℂ) - T = ((τ - T : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [psi]
  push_cast
  ring

/-- **The explicit formula for the windows under RH.** -/
theorem explicitFormula_window (hRH : RiemannHypothesis) {ℓ : ℝ} (hℓ : 0 < ℓ) (T : ℝ) (k : ℕ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T)) ∧
      Integrable (fun τ : ℝ => psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ) ∧
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) =
        ∫ τ : ℝ, psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ := by
  obtain ⟨hs, hi, he⟩ := paperInputs_zeta.EF (2 * ℓ) (by positivity) (window ℓ T k)
    (window ℓ T k) (contDiff_window ℓ T k) (contDiff_window ℓ T k) (tsupport_window hℓ T k)
    (tsupport_window hℓ T k)
  have hsum : (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand (window ℓ T k) (window ℓ T k) ρ) =
      fun ρ : zetaZeroConfig.carrier =>
        (((zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ) := by
    funext ρ; exact wsummand_window hRH ℓ T k ρ.2
  have hint : (fun τ : ℝ => paperFT (window ℓ T k) τ *
      (starRingEnd ℂ) (paperFT (window ℓ T k) τ) * (nuX (Real.exp (2 * ℓ)) τ : ℂ)) =
      fun τ => ((psi ℓ k (τ - T) * nuX (Real.exp (2 * ℓ)) τ : ℝ) : ℂ) := by
    funext τ; exact integrand_window ℓ T _ k τ
  rw [hsum] at hs
  rw [hint] at hi
  refine ⟨Complex.summable_ofReal.mp hs, hi.re, ?_⟩
  have hW : zetaZeroConfig.W (window ℓ T k) (window ℓ T k) =
      ((∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ k ((ρ : ℂ).im - T) : ℝ) : ℂ) := by
    unfold ZeroConfig.W
    rw [hsum, Complex.ofReal_tsum]
  rw [hW, hint, integral_complex_ofReal] at he
  exact_mod_cast he

/-! ## Counting -/

/-- `A = ∫Φ`. -/
def bumpMass : ℝ := ∫ v, |iteratedDeriv 0 bump v|

theorem psi_succ_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) (x : ℝ) :
    psi ℓ (k + 1) x = x ^ 2 * psi ℓ k x := by
  simp only [psi]
  rw [paperFT_cb_succ hℓ k (x : ℂ), norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem psi_one_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) : psi ℓ 1 x = x ^ 2 * psi ℓ 0 x :=
  psi_succ_eq hℓ 0 x

theorem psi_zero_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) : psi ℓ 0 x ≤ (ℓ * bumpMass) ^ 2 := by
  have h := norm_paperFT_cb_le hℓ 0 x
  simp only [Nat.cast_zero, sub_zero, zpow_one] at h
  simp only [psi, bumpMass]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `ψ₀(x) ≤ (ℓA)²·1_{(−δ,δ]}(x) + ψ₁(x)/δ²`. -/
theorem psi_zero_le_window {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (x : ℝ) :
    psi ℓ 0 x ≤ (ℓ * bumpMass) ^ 2 * (if -δ < x ∧ x ≤ δ then 1 else 0) + psi ℓ 1 x / δ ^ 2 := by
  rw [psi_one_eq hℓ]
  have hψ := psi_nonneg ℓ 0 x
  split_ifs with h
  · have h1 := psi_zero_le hℓ x
    have h2 : 0 ≤ x ^ 2 * psi ℓ 0 x / δ ^ 2 := by positivity
    linarith
  · have hx : δ ≤ |x| := by
      by_contra hc
      push Not at hc
      exact h ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have hx2 : δ ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ hδ.le hx 2
    rw [mul_zero, zero_add, le_div_iff₀ (by positivity)]
    nlinarith

/-- The multiplicity-weighted indicator of a window sums to the window count. -/
theorem tsum_window_mult (T₁ T₂ : ℝ) :
    ∑' ρ : zetaZeroConfig.carrier,
        (if T₁ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₂ then (zetaZeroConfig.mult ρ : ℝ) else 0) =
      (zetaZeroConfig.N T₁ T₂ : ℝ) := by
  classical
  set W := zetaZeroConfig.window T₁ T₂ with hW
  have hfin : W.Finite := zetaZeroConfig.finite_window T₁ T₂
  set s : Finset zetaZeroConfig.carrier :=
    (hfin.preimage Subtype.val_injective.injOn).toFinset with hs
  have hmem : ∀ b : zetaZeroConfig.carrier,
      b ∈ s ↔ T₁ < (b : ℂ).im ∧ (b : ℂ).im ≤ T₂ := by
    intro b
    simp only [hs, Set.Finite.mem_toFinset, Set.mem_preimage, hW, ZeroConfig.window,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
  rw [tsum_eq_sum (s := s) (fun b hb => by rw [if_neg (fun h => hb ((hmem b).mpr h))])]
  rw [Finset.sum_congr rfl (fun b hb => by rw [if_pos ((hmem b).mp hb)])]
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  have himage : hfin.toFinset = s.map (Function.Embedding.subtype _) := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · intro hρ
      exact ⟨⟨ρ, hρ.1⟩, (hmem _).mpr hρ.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, (hmem b).mp hb⟩
  rw [himage, Finset.sum_map]
  rfl

/-- **Counting inequality.**  Under RH, for `δ > 0`,
`Σ m ψ₀(γ − T) ≤ (ℓA)² N(T − δ, T + δ) + δ⁻² Σ m ψ₁(γ − T)`. -/
theorem tsum_psi_zero_le (hRH : RiemannHypothesis) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (T : ℝ) :
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) ≤
      (ℓ * bumpMass) ^ 2 * (zetaZeroConfig.N (T - δ) (T + δ) : ℝ) +
        (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T)) / δ ^ 2 := by
  classical
  obtain ⟨hs1, -, -⟩ := explicitFormula_window hRH hℓ T 1
  obtain ⟨hs0, -, -⟩ := explicitFormula_window hRH hℓ T 0
  set g : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (if T - δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + δ then (zetaZeroConfig.mult ρ : ℝ) else 0) with hg
  have hgs : Summable g := by
    have hfin := zetaZeroConfig.finite_window (T - δ) (T + δ)
    refine summable_of_hasFiniteSupport ((hfin.preimage Subtype.val_injective.injOn).subset ?_)
    intro b hb
    simp only [Function.mem_support, hg, ne_eq, ite_eq_right_iff, not_forall] at hb
    obtain ⟨h, -⟩ := hb
    exact ⟨b.2, h⟩
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) ≤
        (ℓ * bumpMass) ^ 2 * g ρ +
          (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2 := by
    intro ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have h := mul_le_mul_of_nonneg_left (psi_zero_le_window hℓ hδ ((ρ : ℂ).im - T)) hm
    have hiff : (-δ < (ρ : ℂ).im - T ∧ (ρ : ℂ).im - T ≤ δ) ↔
        (T - δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + δ) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [hg]
    by_cases hw : T - δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + δ
    · rw [if_pos (hiff.mpr hw)] at h; rw [if_pos hw]
      calc (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * ((ℓ * bumpMass) ^ 2 * 1 +
              psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2) := h
        _ = _ := by ring
    · rw [if_neg (fun h' => hw (hiff.mp h'))] at h; rw [if_neg hw]
      calc (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * ((ℓ * bumpMass) ^ 2 * 0 +
              psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2) := h
        _ = _ := by ring
  have hR : Summable fun ρ : zetaZeroConfig.carrier => (ℓ * bumpMass) ^ 2 * g ρ +
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 1 ((ρ : ℂ).im - T) / δ ^ 2 :=
    (hgs.mul_left _).add (hs1.div_const _)
  refine (Summable.tsum_le_tsum hpt hs0 hR).trans (le_of_eq ?_)
  rw [hgs.mul_left _ |>.tsum_add (hs1.div_const _), tsum_mul_left, tsum_div_const,
    tsum_window_mult]

/-! ## Comparison with the archimedean density -/

/-- `μ(T/2)ψ₀(x) − (μ(T/2)+1)(4/T²)ψ₁(x) ≤ ψ₀(x)μ(x+T)`: on `|x| ≤ T/2` by monotonicity of `μ`,
and on `|x| > T/2` from `μ > −1` and `4x²/T² ≥ 1`. -/
theorem psi_zero_mul_mu_ge {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T) (x : ℝ) :
    mu (T / 2) * psi ℓ 0 x - (mu (T / 2) + 1) * (4 / T ^ 2) * psi ℓ 1 x ≤
      psi ℓ 0 x * mu (x + T) := by
  rw [psi_one_eq hℓ]
  have hp := psi_nonneg ℓ 0 x
  have hm1 : 0 ≤ mu (T / 2) + 1 := by linarith [neg_one_lt_mu (T / 2)]
  by_cases hx : |x| ≤ T / 2
  · have hle : mu (T / 2) ≤ mu (x + T) :=
      mu_mono (by linarith) (by linarith [neg_abs_le x])
    have h1 := mul_le_mul_of_nonneg_left hle hp
    have h2 : 0 ≤ (mu (T / 2) + 1) * (4 / T ^ 2) * (x ^ 2 * psi ℓ 0 x) := by positivity
    linarith
  · push Not at hx
    have hT2 : T ^ 2 ≤ 4 * x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
    have hq : 1 ≤ 4 / T ^ 2 * x ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    have h1 : -psi ℓ 0 x ≤ psi ℓ 0 x * mu (x + T) := by
      nlinarith [neg_one_lt_mu (x + T)]
    have h2 := mul_nonneg (mul_nonneg hm1 hp) (sub_nonneg.mpr hq)
    nlinarith

/-- `μ(x+T) ≤ μ(3T/2) + (1/2π + C)·4x²/T²` for `T ≥ 1`, with `C ≥ 0` a Stirling constant: on
`|x| ≤ T/2` by monotonicity, and on `|x| > T/2` by `μ(x+T) ≤ μ(3|x|)`, Stirling at `3|x|` and
`3T/2`, and `log y ≤ y − 1 ≤ y²` for `y = 2|x|/T`. -/
theorem mu_add_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {T : ℝ} (hT : 1 ≤ T) (x : ℝ) :
    mu (x + T) ≤ mu (3 * T / 2) + (1 / (2 * Real.pi) + C) * (4 / T ^ 2 * x ^ 2) := by
  have hπ := Real.pi_pos
  have hnn : 0 ≤ (1 / (2 * Real.pi) + C) * (4 / T ^ 2 * x ^ 2) := by positivity
  by_cases hx : |x| ≤ T / 2
  · have := mu_mono (a := x + T) (b := 3 * T / 2) (by linarith [neg_abs_le x])
      (by linarith [le_abs_self x])
    linarith
  · push Not at hx
    have hxpos : 0 < |x| := by linarith
    have hy1 : 1 < 2 * |x| / T := by rw [lt_div_iff₀ (by linarith)]; linarith
    have hy2 : (2 * |x| / T) ^ 2 = 4 / T ^ 2 * x ^ 2 := by
      rw [div_pow, mul_pow, sq_abs]; ring
    have h1 : mu (x + T) ≤ mu (3 * |x|) := by
      apply mu_le_of_abs_le
      rw [abs_of_pos (by linarith : (0 : ℝ) < 3 * |x|)]
      calc |x + T| ≤ |x| + |T| := abs_add_le x T
        _ = |x| + T := by rw [abs_of_pos (by linarith : (0 : ℝ) < T)]
        _ ≤ 3 * |x| := by linarith
    have hA := hC (3 * |x|) (by rw [abs_of_pos (by linarith)]; linarith)
    have hB := hC (3 * T / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [abs_of_pos (by linarith : (0 : ℝ) < 3 * |x|)] at hA
    rw [abs_of_pos (by linarith : (0 : ℝ) < 3 * T / 2)] at hB
    rw [abs_le] at hA hB
    have hlog : Real.log (3 * |x| / (2 * Real.pi)) - Real.log (3 * T / 2 / (2 * Real.pi)) ≤
        2 * |x| / T - 1 := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have e : 3 * |x| / (2 * Real.pi) / (3 * T / 2 / (2 * Real.pi)) = 2 * |x| / T := by
        field_simp
      rw [e]; exact Real.log_le_sub_one_of_pos (by linarith)
    have hc1 : C / (3 * |x|) ^ 2 ≤ C / 2 :=
      div_le_div_of_nonneg_left hC0 (by norm_num) (by nlinarith)
    have hc2 : C / (3 * T / 2) ^ 2 ≤ C / 2 :=
      div_le_div_of_nonneg_left hC0 (by norm_num) (by nlinarith)
    have hl := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    have hyy : 2 * |x| / T - 1 ≤ (2 * |x| / T) ^ 2 := by nlinarith
    have hl2 := mul_le_mul_of_nonneg_left hyy (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    have hCy : C ≤ C * (2 * |x| / T) ^ 2 := le_mul_of_one_le_right hC0 (by nlinarith)
    rw [← hy2]
    nlinarith

/-- `μ(T/2) ≤ T + C` for `T ≥ 2`. -/
theorem mu_half_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {T : ℝ} (hT : 2 ≤ T) : mu (T / 2) ≤ T + C := by
  have hπ := Real.pi_gt_three
  have h := hC (T / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (by linarith : (0 : ℝ) < T / 2), abs_le] at h
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / 2 / (2 * Real.pi))
  have h1 : T / 2 / (2 * Real.pi) ≤ T := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 : 1 / (2 * Real.pi) * Real.log (T / 2 / (2 * Real.pi)) ≤ T := by
    have h3 : 1 / (2 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    rcases le_or_gt (Real.log (T / 2 / (2 * Real.pi))) 0 with hl | hl
    · nlinarith [show (0 : ℝ) ≤ 1 / (2 * Real.pi) by positivity]
    · nlinarith
  have hc : C / (T / 2) ^ 2 ≤ C := div_le_self hC0 (by nlinarith)
  linarith [h.2]

/-- `μ(T/2) − μ(3T/2)/2 ≥ (log T − log 12π)/4π − 2C` for `T ≥ 2`. -/
theorem mu_half_sub_ge {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {T : ℝ} (hT : 2 ≤ T) :
    (Real.log T - Real.log (12 * Real.pi)) / (4 * Real.pi) - 2 * C ≤
      mu (T / 2) - mu (3 * T / 2) / 2 := by
  have hπ := Real.pi_pos
  have hA := hC (T / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hB := hC (3 * T / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (by linarith : (0 : ℝ) < T / 2), abs_le] at hA
  rw [abs_of_pos (by linarith : (0 : ℝ) < 3 * T / 2), abs_le] at hB
  have e1 : Real.log (T / 2 / (2 * Real.pi)) = Real.log T - Real.log (4 * Real.pi) := by
    rw [show T / 2 / (2 * Real.pi) = T / (4 * Real.pi) by ring,
      Real.log_div (by linarith) (by positivity)]
  have e2 : Real.log (3 * T / 2 / (2 * Real.pi)) =
      Real.log 3 + Real.log T - Real.log (4 * Real.pi) := by
    rw [show 3 * T / 2 / (2 * Real.pi) = 3 * T / (4 * Real.pi) by ring,
      Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by linarith)]
  have e3 : Real.log (12 * Real.pi) = Real.log 3 + Real.log (4 * Real.pi) := by
    rw [show 12 * Real.pi = 3 * (4 * Real.pi) by ring, Real.log_mul (by norm_num) (by positivity)]
  rw [e1] at hA
  rw [e2] at hB
  have hc1 : C / (T / 2) ^ 2 ≤ C := div_le_self hC0 (by nlinarith)
  have hc2 : C / (3 * T / 2) ^ 2 ≤ C := div_le_self hC0 (by nlinarith)
  have e4 : (Real.log T - Real.log (12 * Real.pi)) / (4 * Real.pi) =
      1 / (2 * Real.pi) * (Real.log T - Real.log (4 * Real.pi)) -
        1 / (2 * Real.pi) * (Real.log 3 + Real.log T - Real.log (4 * Real.pi)) / 2 := by
    rw [e3]; field_simp; ring
  rw [e4]
  linarith [hA.1, hB.2]

/-! ## The two sides of the explicit formula -/

/-- Lower bound for the `ψ₀`-side: `∫ψ₀(τ−T)ν_X ≥ (μ(T/2) − K)∫ψ₀ − (μ(T/2)+1)(4/T²)∫ψ₁`,
with `X = e^{2ℓ}` and `K = 1 + 3X²`. -/
theorem integral_psi_zero_nuX_ge {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T)
    (hi : Integrable (fun τ => psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ)) :
    (mu (T / 2) - (1 + 3 * Real.exp (2 * ℓ) ^ 2)) * (2 * Real.pi * ℓ * energy 0) -
        (mu (T / 2) + 1) * (4 / T ^ 2) * (2 * Real.pi * energy 1 / ℓ) ≤
      ∫ τ, psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ := by
  have hX : 1 ≤ Real.exp (2 * ℓ) := Real.one_le_exp (by positivity)
  have hi0 := (integrable_psi hℓ 0).comp_sub_right T
  have hi1 := (integrable_psi hℓ 1).comp_sub_right T
  have hint : ∫ τ, ((mu (T / 2) - (1 + 3 * Real.exp (2 * ℓ) ^ 2)) * psi ℓ 0 (τ - T) -
      (mu (T / 2) + 1) * (4 / T ^ 2) * psi ℓ 1 (τ - T)) =
      (mu (T / 2) - (1 + 3 * Real.exp (2 * ℓ) ^ 2)) * (2 * Real.pi * ℓ * energy 0) -
        (mu (T / 2) + 1) * (4 / T ^ 2) * (2 * Real.pi * energy 1 / ℓ) := by
    rw [integral_sub (hi0.const_mul _) (hi1.const_mul _), integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self (psi ℓ 0) T, integral_sub_right_eq_self (psi ℓ 1) T,
      integral_psi_zero hℓ, integral_psi_one hℓ]
  rw [← hint]
  refine integral_mono ((hi0.const_mul _).sub (hi1.const_mul _)) hi (fun τ => ?_)
  have hν := (abs_le.mp (abs_nuX_sub_mu_le hX τ)).1
  have hp := psi_nonneg ℓ 0 (τ - T)
  have hpt := psi_zero_mul_mu_ge hℓ hT (τ - T)
  rw [sub_add_cancel] at hpt
  have h1 : psi ℓ 0 (τ - T) * (mu τ - (1 + 3 * Real.exp (2 * ℓ) ^ 2)) ≤
      psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ :=
    mul_le_mul_of_nonneg_left (by linarith) hp
  simp only
  linarith

/-- Upper bound for the `ψ₁`-side: `∫ψ₁(τ−T)ν_X ≤ (μ(3T/2) + K)∫ψ₁ + (1/2π + C)(4/T²)∫ψ₂`. -/
theorem integral_psi_one_nuX_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 1 ≤ T)
    (hi : Integrable (fun τ => psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ)) :
    ∫ τ, psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ ≤
      (mu (3 * T / 2) + (1 + 3 * Real.exp (2 * ℓ) ^ 2)) * (2 * Real.pi * energy 1 / ℓ) +
        (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3) := by
  have hX : 1 ≤ Real.exp (2 * ℓ) := Real.one_le_exp (by positivity)
  have hi1 := (integrable_psi hℓ 1).comp_sub_right T
  have hi2 := (integrable_psi hℓ 2).comp_sub_right T
  have hint : ∫ τ, ((mu (3 * T / 2) + (1 + 3 * Real.exp (2 * ℓ) ^ 2)) * psi ℓ 1 (τ - T) +
      (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * psi ℓ 2 (τ - T)) =
      (mu (3 * T / 2) + (1 + 3 * Real.exp (2 * ℓ) ^ 2)) * (2 * Real.pi * energy 1 / ℓ) +
        (1 / (2 * Real.pi) + C) * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3) := by
    rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self (psi ℓ 1) T, integral_sub_right_eq_self (psi ℓ 2) T,
      integral_psi_one hℓ, integral_psi_two hℓ]
  rw [← hint]
  refine integral_mono hi ((hi1.const_mul _).add (hi2.const_mul _)) (fun τ => ?_)
  have hν := (abs_le.mp (abs_nuX_sub_mu_le hX τ)).2
  have hp := psi_nonneg ℓ 1 (τ - T)
  have hmu := mu_add_le hC0 hC hT (τ - T)
  rw [sub_add_cancel] at hmu
  have h2 : psi ℓ 2 (τ - T) = (τ - T) ^ 2 * psi ℓ 1 (τ - T) := psi_succ_eq hℓ 1 (τ - T)
  have h1 : psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ ≤
      psi ℓ 1 (τ - T) * (mu (3 * T / 2) + (1 / (2 * Real.pi) + C) * (4 / T ^ 2 * (τ - T) ^ 2) +
        (1 + 3 * Real.exp (2 * ℓ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hp
  simp only
  rw [h2]
  linarith

/-! ## The window count -/

/-- The window half-width constant `D = √(2F₁/E + 1)`, so that `F₁/D² ≤ E/2`. -/
def windowD : ℝ := Real.sqrt (2 * energy 1 / energy 0 + 1)

theorem windowD_sq : windowD ^ 2 = 2 * energy 1 / energy 0 + 1 := by
  have := energy_nonneg 1
  have := energy_zero_pos
  exact Real.sq_sqrt (by positivity)

theorem one_le_windowD : 1 ≤ windowD := by
  have := energy_nonneg 1
  have := energy_zero_pos
  have h : 0 ≤ 2 * energy 1 / energy 0 := by positivity
  exact Real.one_le_sqrt.mpr (by linarith)

/-- **Window count under RH.**  For `ℓ ≥ 1` and `T ≥ 2`, with `N` the multiplicity count of
`(T − D/ℓ, T + D/ℓ]`,

  `ℓ A² N ≥ (E/2) log T − M − 3πE(1 + 3e^{4ℓ})`.

The explicit formula for `Φ_ℓ e^{−iTu}` and `Φ_ℓ′ e^{−iTu}`, the counting inequality, the two
density bounds and Plancherel give `ℓ²A²N ≥ ℓQ` with
`Q = 2π(μ(T/2) − K)E − 8π(μ(T/2)+1)F₁/(Tℓ)² − 2π(μ(3T/2)+K)F₁/D² − 8πcF₂/(DTℓ)²`; Stirling bounds
`μ(T/2) − μ(3T/2)/2` from below and `μ(T/2)` from above. -/
theorem exists_window_count_bound (hRH : RiemannHypothesis) :
    ∃ M : ℝ, ∀ ℓ T : ℝ, 1 ≤ ℓ → 2 ≤ T →
      energy 0 / 2 * Real.log T - M - 3 * Real.pi * energy 0 * (1 + 3 * Real.exp (2 * ℓ) ^ 2) ≤
        ℓ * bumpMass ^ 2 * (zetaZeroConfig.N (T - windowD / ℓ) (T + windowD / ℓ) : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_stirling
  refine ⟨energy 0 / 2 * Real.log (12 * Real.pi) + 4 * Real.pi * energy 0 * C +
    8 * Real.pi * energy 1 * (C + 2) + 8 * Real.pi * (1 / (2 * Real.pi) + C) * energy 2,
    fun ℓ T hℓ hT => ?_⟩
  have hℓ0 : 0 < ℓ := by linarith
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hE0 := energy_zero_pos
  have hE1 := energy_nonneg 1
  have hE2 := energy_nonneg 2
  have hD := one_le_windowD
  have hD2 := windowD_sq
  have hDpos : 0 < windowD := by linarith
  obtain ⟨-, hi0, he0⟩ := explicitFormula_window hRH hℓ0 T 0
  obtain ⟨-, hi1, he1⟩ := explicitFormula_window hRH hℓ0 T 1
  have hcount := tsum_psi_zero_le hRH hℓ0 (by positivity : 0 < windowD / ℓ) T
  rw [he0, he1] at hcount
  have hlow := integral_psi_zero_nuX_ge hℓ0 hT0 hi0
  have hup := integral_psi_one_nuX_le hC0 hC hℓ0 (by linarith) hi1
  set D := windowD
  set K := 1 + 3 * Real.exp (2 * ℓ) ^ 2 with hK
  have hK1 : 1 ≤ K := by have := sq_nonneg (Real.exp (2 * ℓ)); linarith
  set m₁ := mu (T / 2)
  set m₃ := mu (3 * T / 2)
  set c := 1 / (2 * Real.pi) + C with hc
  have hc0 : 0 ≤ c := by positivity
  set N : ℝ := (zetaZeroConfig.N (T - D / ℓ) (T + D / ℓ) : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set S₀ := ∫ τ, psi ℓ 0 (τ - T) * nuX (Real.exp (2 * ℓ)) τ
  set S₁ := ∫ τ, psi ℓ 1 (τ - T) * nuX (Real.exp (2 * ℓ)) τ
  set Q := 2 * Real.pi * (m₁ - K) * energy 0 -
    (m₁ + 1) * (8 * Real.pi * energy 1) / (T ^ 2 * ℓ ^ 2) -
    2 * Real.pi * (m₃ + K) * energy 1 / D ^ 2 -
    8 * Real.pi * c * energy 2 / (D ^ 2 * T ^ 2 * ℓ ^ 2) with hQ
  have hdiv : S₁ / (D / ℓ) ^ 2 ≤ ((m₃ + K) * (2 * Real.pi * energy 1 / ℓ) +
      c * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3)) / (D / ℓ) ^ 2 :=
    div_le_div_of_nonneg_right hup (by positivity)
  have hℓne : ℓ ≠ 0 := hℓ0.ne'
  have hTne : T ≠ 0 := hT0.ne'
  have hDne : D ≠ 0 := hDpos.ne'
  have hid : (m₁ - K) * (2 * Real.pi * ℓ * energy 0) -
      (m₁ + 1) * (4 / T ^ 2) * (2 * Real.pi * energy 1 / ℓ) -
      ((m₃ + K) * (2 * Real.pi * energy 1 / ℓ) +
        c * (4 / T ^ 2) * (2 * Real.pi * energy 2 / ℓ ^ 3)) / (D / ℓ) ^ 2 = ℓ * Q := by
    rw [hQ]; field_simp; ring
  have hsq : (ℓ * bumpMass) ^ 2 * N = ℓ * (ℓ * bumpMass ^ 2 * N) := by ring
  have hkey : ℓ * Q ≤ ℓ * (ℓ * bumpMass ^ 2 * N) := by linarith
  have hQle : Q ≤ ℓ * bumpMass ^ 2 * N := le_of_mul_le_mul_left hkey hℓ0
  have hm3K : 0 ≤ m₃ + K := by linarith [neg_one_lt_mu (3 * T / 2)]
  have hb1 : 2 * Real.pi * (m₃ + K) * energy 1 / D ^ 2 ≤ Real.pi * (m₃ + K) * energy 0 := by
    rw [div_le_iff₀ (by positivity), hD2]
    have h : energy 1 ≤ energy 0 / 2 * (2 * energy 1 / energy 0 + 1) := by
      have e : energy 0 / 2 * (2 * energy 1 / energy 0 + 1) = energy 1 + energy 0 / 2 := by
        field_simp
      rw [e]; linarith
    calc 2 * Real.pi * (m₃ + K) * energy 1
        ≤ 2 * Real.pi * (m₃ + K) * (energy 0 / 2 * (2 * energy 1 / energy 0 + 1)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.pi * (m₃ + K) * energy 0 * (2 * energy 1 / energy 0 + 1) := by ring
  have hm1 : m₁ + 1 ≤ (C + 2) * (T ^ 2 * ℓ ^ 2) := by
    have h := mu_half_le hC0 hC hT
    have hT2 : T ≤ T ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hT0.le (by linarith)
    have hl2 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ
    have hT1 : 1 ≤ T ^ 2 := one_le_pow₀ (by linarith)
    have h3 : (C + 2) * T ^ 2 ≤ (C + 2) * (T ^ 2 * ℓ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ (C + 2) * T ^ 2)
      linarith
    have h4 : C + 1 ≤ (C + 1) * T ^ 2 := le_mul_of_one_le_right (by linarith) hT1
    linarith
  have hb2 : (m₁ + 1) * (8 * Real.pi * energy 1) / (T ^ 2 * ℓ ^ 2) ≤
      8 * Real.pi * energy 1 * (C + 2) := by
    rw [div_le_iff₀ (by positivity)]
    calc (m₁ + 1) * (8 * Real.pi * energy 1)
        ≤ (C + 2) * (T ^ 2 * ℓ ^ 2) * (8 * Real.pi * energy 1) :=
          mul_le_mul_of_nonneg_right hm1 (by positivity)
      _ = 8 * Real.pi * energy 1 * (C + 2) * (T ^ 2 * ℓ ^ 2) := by ring
  have hb3 : 8 * Real.pi * c * energy 2 / (D ^ 2 * T ^ 2 * ℓ ^ 2) ≤ 8 * Real.pi * c * energy 2 := by
    apply div_le_self (by positivity)
    have h1 : 1 ≤ D ^ 2 := one_le_pow₀ hD
    have h2 : 1 ≤ T ^ 2 := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ
    have h4 : 1 ≤ D ^ 2 * T ^ 2 := one_le_mul_of_one_le_of_one_le h1 h2
    exact one_le_mul_of_one_le_of_one_le h4 h3
  have hst := mu_half_sub_ge hC0 hC hT
  have hst2 : energy 0 / 2 * (Real.log T - Real.log (12 * Real.pi)) - 4 * Real.pi * energy 0 * C ≤
      2 * Real.pi * energy 0 * (m₁ - m₃ / 2) := by
    have h := mul_le_mul_of_nonneg_left hst (by positivity : (0 : ℝ) ≤ 2 * Real.pi * energy 0)
    have e : 2 * Real.pi * energy 0 *
        ((Real.log T - Real.log (12 * Real.pi)) / (4 * Real.pi) - 2 * C) =
        energy 0 / 2 * (Real.log T - Real.log (12 * Real.pi)) - 4 * Real.pi * energy 0 * C := by
      field_simp; ring
    linarith
  have hQ2 : Q = 2 * Real.pi * energy 0 * (m₁ - m₃ / 2) - 3 * Real.pi * energy 0 * K -
      (m₁ + 1) * (8 * Real.pi * energy 1) / (T ^ 2 * ℓ ^ 2) -
      (2 * Real.pi * (m₃ + K) * energy 1 / D ^ 2 - Real.pi * (m₃ + K) * energy 0) -
      8 * Real.pi * c * energy 2 / (D ^ 2 * T ^ 2 * ℓ ^ 2) := by
    rw [hQ]; ring
  linarith

/-- For `0 ≤ a ≤ b`, `N_ξ(b) − N_ξ(a)` is the multiplicity count of the zeros with
`a < Im ρ ≤ b`. -/
theorem xiZeroCount_sub_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    xiZeroCount b - xiZeroCount a = (zetaZeroConfig.N a b : ℤ) := by
  have hN : ∀ T, zetaZeroConfig.N 0 T = xiPosZeroCount T := fun T => by
    rw [← zeta23_Ncount_zero_eq_xiPosZeroCount]; exact zetaZeros_N zetaSeam 0 T
  have h := Assembly.N_add zetaZeroConfig ha hab
  rw [← xiPosZeroCount_eq_xiZeroCount ha, ← xiPosZeroCount_eq_xiZeroCount (ha.trans hab),
    ← hN, ← hN, h]
  push_cast
  ring

/-- **Littlewood's short windows under RH.**  There is `C > 0` such that for every `m`, every
window `(t, t + C/log log t]` with `t` large contains at least `m` zeros of `ξ` counted with
multiplicity.  Take `ℓ = (log log t)/8` in `exists_window_count_bound`: then `e^{4ℓ} = √(log t)`,
the right side is `≥ (E/4) log t`, and `ℓ ≤ √(log t)/4` gives `A²N ≥ E√(log t)`. -/
theorem riemannHypothesis_eventually_xiZeroCount_window_ge (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      (m : ℤ) ≤ xiZeroCount (t + C / Real.log (Real.log t)) - xiZeroCount t := by
  obtain ⟨M, hM⟩ := exists_window_count_bound hRH
  have hD := one_le_windowD
  refine ⟨16 * windowD, by positivity, fun m => ?_⟩
  have hE := energy_zero_pos
  have hπ := Real.pi_pos
  set E := energy 0 with hEdef
  set A := bumpMass
  set B := 4 * (|M| + 3 * Real.pi * E) / E with hB
  have hB0 : 0 ≤ B := by positivity
  set S := max (max (Real.exp 4) (36 * Real.pi + B + 1)) ((m : ℝ) * A ^ 2 / E + 1) with hS
  have hS1 : Real.exp 4 ≤ S := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS2 : 36 * Real.pi + B + 1 ≤ S := le_trans (le_max_right _ _) (le_max_left _ _)
  have hS3 : (m : ℝ) * A ^ 2 / E + 1 ≤ S := le_max_right _ _
  have he4 : 5 ≤ Real.exp 4 := by linarith [Real.add_one_le_exp 4]
  have hS0 : 1 ≤ S := by linarith
  refine ⟨Real.exp (S ^ 2), fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hL : S ^ 2 ≤ Real.log t := by
    rw [← Real.log_exp (S ^ 2)]; exact Real.log_le_log (Real.exp_pos _) ht
  have hS21 : 1 ≤ S ^ 2 := one_le_pow₀ hS0
  have hLpos : 0 < Real.log t := by linarith
  have hsS : S ≤ Real.sqrt (Real.log t) := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ S)]; exact Real.sqrt_le_sqrt hL
  set s := Real.sqrt (Real.log t) with hsdef
  have hs1 : 1 ≤ s := hS0.trans hsS
  have hsL : s ^ 2 = Real.log t := Real.sq_sqrt hLpos.le
  have hlogs : Real.log (Real.log t) = 2 * Real.log s := by
    rw [← hsL, Real.log_pow]; push_cast; ring
  have hlog4 : 4 ≤ Real.log s := by
    rw [← Real.log_exp 4]; exact Real.log_le_log (Real.exp_pos _) (hS1.trans hsS)
  set ℓ := Real.log (Real.log t) / 8 with hℓdef
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef, hlogs]; linarith
  have hℓs : ℓ ≤ s / 4 := by
    rw [hℓdef, hlogs]; linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < s)]
  have hexp : Real.exp (2 * ℓ) ^ 2 = s := by
    rw [sq, ← Real.exp_add, show 2 * ℓ + 2 * ℓ = Real.log s by rw [hℓdef, hlogs]; ring,
      Real.exp_log (by linarith)]
  have hδ : 0 ≤ windowD / ℓ := by positivity
  have htS : S ^ 2 + 1 ≤ t := (Real.add_one_le_exp _).trans ht
  have hT2 : 2 ≤ t + windowD / ℓ := by linarith
  have hbound := hM ℓ (t + windowD / ℓ) hℓ1 hT2
  rw [hexp, show t + windowD / ℓ - windowD / ℓ = t by ring] at hbound
  have hwin : t + 16 * windowD / Real.log (Real.log t) = t + windowD / ℓ + windowD / ℓ := by
    rw [hℓdef]; field_simp; ring
  rw [← hwin] at hbound
  set N := zetaZeroConfig.N t (t + 16 * windowD / Real.log (Real.log t))
  have hlogT : Real.log t ≤ Real.log (t + windowD / ℓ) := Real.log_le_log ht0 (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA0 : 0 ≤ A ^ 2 := sq_nonneg _
  -- the main term dominates
  have h1 : B + 1 ≤ s - 36 * Real.pi := by linarith
  have h2 : E / 4 * (B + 1) ≤ E / 4 * s * (s - 36 * Real.pi) := by
    have h3 : E / 4 * (B + 1) ≤ E / 4 * (s - 36 * Real.pi) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : E / 4 * (s - 36 * Real.pi) ≤ E / 4 * s * (s - 36 * Real.pi) := by
      have := mul_le_mul_of_nonneg_left hs1
        (mul_nonneg (by positivity) (by linarith) : (0 : ℝ) ≤ E / 4 * (s - 36 * Real.pi))
      linarith
    linarith
  have h3 : E / 4 * (B + 1) = |M| + 3 * Real.pi * E + E / 4 := by
    rw [hB]; field_simp
  have hM' : M ≤ |M| := le_abs_self M
  have hlog2 : E / 2 * s ^ 2 ≤ E / 2 * Real.log (t + windowD / ℓ) := by
    rw [hsL]; exact mul_le_mul_of_nonneg_left hlogT (by positivity)
  have hmain : E / 4 * s ^ 2 ≤ ℓ * A ^ 2 * N := by linarith
  have hAN : ℓ * A ^ 2 * N ≤ s / 4 * (A ^ 2 * N) := by
    have := mul_le_mul_of_nonneg_right hℓs (mul_nonneg hA0 hN0)
    linarith
  have hEs : E * s ≤ A ^ 2 * N := by
    have h5 : s / 4 * (E * s) ≤ s / 4 * (A ^ 2 * N) := by linarith
    exact le_of_mul_le_mul_left h5 (by positivity)
  have hmE : (m : ℝ) * A ^ 2 + E ≤ E * s := by
    have h6 : (m : ℝ) * A ^ 2 / E + 1 ≤ s := hS3.trans hsS
    have h7 := mul_le_mul_of_nonneg_left h6 hE.le
    have e : E * ((m : ℝ) * A ^ 2 / E + 1) = (m : ℝ) * A ^ 2 + E := by field_simp
    linarith
  have hmN : (m : ℝ) < N := by
    by_contra hc
    push Not at hc
    have := mul_le_mul_of_nonneg_left hc hA0
    linarith
  have hmN' : m < N := by exact_mod_cast hmN
  have hwin0 : t ≤ t + 16 * windowD / Real.log (Real.log t) := by
    rw [hwin]; linarith
  rw [xiZeroCount_sub_eq ht0.le hwin0]
  exact_mod_cast hmN'.le

/-- **Littlewood's short windows under RH**, for a fixed number `m` of zeros. -/
theorem riemannHypothesis_xiZeroCount_window_ge (hRH : RiemannHypothesis) (m : ℕ) :
    ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      (m : ℤ) ≤ xiZeroCount (t + C / Real.log (Real.log t)) - xiZeroCount t := by
  obtain ⟨C, -, hC⟩ := riemannHypothesis_eventually_xiZeroCount_window_ge hRH
  obtain ⟨t₀, ht₀⟩ := hC m
  exact ⟨C, t₀, ht₀⟩

end

end RHTower.Littlewood
