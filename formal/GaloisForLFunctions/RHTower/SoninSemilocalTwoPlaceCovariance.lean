import Mathlib
import GaloisForLFunctions.RHTower.GammaEvenBoundaryParityNoGo
import GaloisForLFunctions.RHTower.CCMMetaplecticGammaMomentDeterminacy
import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation

/-!
# Semilocal Sonin two-place positive association: the full covariance

Let `dμ_∞(s) = (2π)^{-3/2} |Γ(1/4 + i s/2)|² ds` be the normalized archimedean cyclic spectral
measure (`RHTower.semilocalArchimedeanGammaMeasure`), whose characteristic function is
`φ(t) = (cosh t)^{-1/2}` (`RHTower.integral_cexp_semilocalArchimedeanGammaMeasure`).  For a
radius `r ∈ (0,1)` and a frequency `ℓ > 0` put

`G(s) = |1 - r e^{i ℓ s}|^{-2}`   (`primeFactor`, see `primeFactor_eq_norm_zpow`).

The card's theorem is `covariance_pos` / `semilocal_twoPlace_association`:

`∫ G₁ G₂ dμ_∞ > (∫ G₁ dμ_∞)(∫ G₂ dμ_∞)`,

equivalently `Z_{p,q} Z_∅ > Z_p Z_q` and hence
`log Z_{p,q} − log Z_p − log Z_q + log Z_∅ > 0`
(`semilocal_twoPlace_log_crossEffect`).  `semilocal_prime_twoPlace_association` is the prime
specialization `r_p = p^{-1/2}`, `ℓ_p = log p`.

The proof is the card's:

* `integral_cos_mul_cos_gamma` — evenness and the characteristic function give
  `∫ cos(us) cos(vs) dμ_∞ = (φ(u+v) + φ(u−v))/2`.
* `gammaCosCovariance_pos` — strict convexity of `x ↦ x^{-1/2}` (the already-formalized
  `RHTower.semilocalArchimedean_twoFrequencyAssociation_pos`) makes every pair of positive
  cosine frequencies strictly positively correlated.
* `hasSum_poissonExpansion` — the Poisson expansion
  `|1 − r e^{iθ}|^{-2} = (1−r²)^{-1}(1 + 2 Σ_{n≥1} r^n cos nθ)`, obtained by taking real parts
  of the geometric series for `(1 − r e^{iθ})^{-1}`.
* `integral_primeFactor`, `integral_primeFactor_mul`, `integral_mul_integral_primeFactor` —
  uniform absolute convergence and `MeasureTheory.integral_tsum` integrate the (double) series
  term by term.
* `covariance_eq_tsum` — the two expansions differ exactly by the double series of cosine
  covariances, and `covariance_pos` bounds it below by its `(1,1)` term.

All frequencies enter only through positivity, so the theorem holds for any two positive
frequencies; distinctness of the primes is not used.
-/

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped ENNReal

namespace RHTower.SemilocalTwoPlace

open RHTower

open Complex Filter MeasureTheory Real Set
open scoped ENNReal




/-! ## The cosine Gram of the archimedean Gamma measure -/

theorem integrable_cos_gamma (t : ℝ) :
    Integrable (fun s : ℝ => Real.cos (t * s)) semilocalArchimedeanGammaMeasure := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards with s
  simpa using abs_cos_le_one (t * s)

theorem integral_cos_mul_cos_gamma (u v : ℝ) :
    (∫ s : ℝ, Real.cos (u * s) * Real.cos (v * s) ∂semilocalArchimedeanGammaMeasure)
      = (semilocalArchimedeanCharacteristic (u + v)
          + semilocalArchimedeanCharacteristic (u - v)) / 2 := by
  have hfun : (fun s : ℝ => Real.cos (u * s) * Real.cos (v * s))
      = fun s : ℝ => (Real.cos ((u + v) * s) + Real.cos ((u - v) * s)) / 2 := by
    funext s
    have h1 : (u + v) * s = u * s + v * s := by ring
    have h2 : (u - v) * s = u * s - v * s := by ring
    rw [h1, h2]
    have h3 := Real.two_mul_cos_mul_cos (u * s) (v * s)
    linarith
  rw [hfun, integral_div, integral_add (integrable_cos_gamma (u + v))
    (integrable_cos_gamma (u - v)), integral_cos_semilocalArchimedeanGammaMeasure,
    integral_cos_semilocalArchimedeanGammaMeasure]

/-- The cosine covariance of two Fourier modes against the archimedean Gamma measure. -/
def gammaCosCovariance (u v : ℝ) : ℝ :=
  (semilocalArchimedeanCharacteristic (u + v) + semilocalArchimedeanCharacteristic (u - v)) / 2
    - semilocalArchimedeanCharacteristic u * semilocalArchimedeanCharacteristic v

theorem semilocalArchimedeanCharacteristic_zero :
    semilocalArchimedeanCharacteristic 0 = 1 := by
  rw [semilocalArchimedeanCharacteristic, Real.cosh_zero, Real.one_rpow]

theorem semilocalArchimedeanCharacteristic_neg (t : ℝ) :
    semilocalArchimedeanCharacteristic (-t) = semilocalArchimedeanCharacteristic t := by
  rw [semilocalArchimedeanCharacteristic, semilocalArchimedeanCharacteristic, Real.cosh_neg]

theorem semilocalArchimedeanCharacteristic_pos (t : ℝ) :
    0 < semilocalArchimedeanCharacteristic t :=
  Real.rpow_pos_of_pos (Real.cosh_pos t) _

theorem gammaCosCovariance_eq_integral (u v : ℝ) :
    gammaCosCovariance u v
      = (∫ s : ℝ, Real.cos (u * s) * Real.cos (v * s) ∂semilocalArchimedeanGammaMeasure)
        - (∫ s : ℝ, Real.cos (u * s) ∂semilocalArchimedeanGammaMeasure)
          * (∫ s : ℝ, Real.cos (v * s) ∂semilocalArchimedeanGammaMeasure) := by
  rw [integral_cos_mul_cos_gamma, integral_cos_semilocalArchimedeanGammaMeasure,
    integral_cos_semilocalArchimedeanGammaMeasure, gammaCosCovariance]

theorem gammaCosCovariance_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 < gammaCosCovariance u v :=
  sub_pos.mpr (semilocalArchimedean_twoFrequencyAssociation_pos hu hv)

theorem gammaCosCovariance_zero_left (v : ℝ) : gammaCosCovariance 0 v = 0 := by
  rw [gammaCosCovariance, semilocalArchimedeanCharacteristic_zero, zero_add, zero_sub,
    semilocalArchimedeanCharacteristic_neg]
  ring

theorem gammaCosCovariance_zero_right (u : ℝ) : gammaCosCovariance u 0 = 0 := by
  rw [gammaCosCovariance, semilocalArchimedeanCharacteristic_zero, add_zero, sub_zero]
  ring

theorem gammaCosCovariance_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ gammaCosCovariance u v := by
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, gammaCosCovariance_zero_left]
  rcases eq_or_lt_of_le hv with h' | h'
  · rw [← h', gammaCosCovariance_zero_right]
  exact (gammaCosCovariance_pos h h').le


/-! ## The Poisson expansion of a prime factor -/

/-- The Poisson weights `w_0 = 1`, `w_n = 2 r^n` (`n ≥ 1`). -/
def poissonWeight (r : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else 2 * r ^ n

theorem poissonWeight_eq (r : ℝ) (n : ℕ) :
    poissonWeight r n = 2 * r ^ n - (if n = 0 then 1 else 0) := by
  rw [poissonWeight]
  by_cases h : n = 0
  · simp [h]; norm_num
  · simp [h]

theorem poissonWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ poissonWeight r n := by
  rw [poissonWeight]
  by_cases h : n = 0
  · simp [h]
  · simp only [h, if_false]
    positivity

theorem summable_poissonWeight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (poissonWeight r) := by
  have h1 : Summable (fun n : ℕ => 2 * r ^ n) :=
    ((summable_geometric_of_lt_one hr0 hr1)).mul_left 2
  have h2 : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 0 (1 : ℝ)).summable
  have h3 := h1.sub h2
  refine h3.congr (fun n => ?_)
  rw [poissonWeight_eq]

theorem normSq_one_sub_expIθ (r θ : ℝ) :
    Complex.normSq (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = 1 - 2 * r * Real.cos θ + r ^ 2 := by
  have hre : (Complex.exp ((θ : ℂ) * Complex.I)).re = Real.cos θ :=
    Complex.exp_ofReal_mul_I_re θ
  have him : (Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ :=
    Complex.exp_ofReal_mul_I_im θ
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem poissonDenom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
  nlinarith [Real.cos_le_one θ, sq_nonneg (1 - r)]

/-- The Poisson (prime) factor `G(s) = |1 - r e^{i ℓ s}|^{-2}`. -/
def primeFactor (r ℓ s : ℝ) : ℝ := (1 - 2 * r * Real.cos (ℓ * s) + r ^ 2)⁻¹

theorem primeFactor_eq_normSq_inv (r ℓ s : ℝ) :
    primeFactor r ℓ s
      = (Complex.normSq (1 - (r : ℂ) * Complex.exp (((ℓ * s : ℝ) : ℂ) * Complex.I)))⁻¹ := by
  rw [primeFactor, normSq_one_sub_expIθ]

theorem primeFactor_eq_norm_zpow (r ℓ s : ℝ) :
    primeFactor r ℓ s
      = ‖1 - (r : ℂ) * Complex.exp (((ℓ * s : ℝ) : ℂ) * Complex.I)‖ ^ (-2 : ℤ) := by
  rw [primeFactor_eq_normSq_inv, Complex.normSq_eq_norm_sq]
  rw [zpow_neg, zpow_two, ← pow_two]

theorem primeFactor_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ s : ℝ) :
    0 < primeFactor r ℓ s := inv_pos.mpr (poissonDenom_pos hr0 hr1 _)

theorem hasSum_poissonExpansion {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    HasSum (fun n : ℕ => poissonWeight r n * Real.cos ((n : ℝ) * θ))
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)) := by
  set z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hnorm : ‖z‖ = r := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
  have hlt : ‖z‖ < 1 := by rw [hnorm]; exact hr1
  have hgeo : HasSum (fun n : ℕ => z ^ n) (1 - z)⁻¹ := hasSum_geometric_of_norm_lt_one hlt
  have hpow : ∀ n : ℕ, (z ^ n).re = r ^ n * Real.cos ((n : ℝ) * θ) := by
    intro n
    have hzn : z ^ n = ((r ^ n : ℝ) : ℂ) * Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [hz, mul_pow, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [hzn, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hD : (0 : ℝ) < 1 - 2 * r * Real.cos θ + r ^ 2 := poissonDenom_pos hr0 hr1 θ
  have hSre : (1 - z)⁻¹.re = (1 - r * Real.cos θ) / (1 - 2 * r * Real.cos θ + r ^ 2) := by
    rw [Complex.inv_re]
    congr 1
    · simp only [Complex.sub_re, Complex.one_re, hz, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
    · exact normSq_one_sub_expIθ r θ
  have hre : HasSum (fun n : ℕ => (z ^ n).re) ((1 - z)⁻¹.re) := Complex.hasSum_re hgeo
  have hre2 : HasSum (fun n : ℕ => 2 * (z ^ n).re) (2 * (1 - z)⁻¹.re) := hre.mul_left 2
  have hone : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 (1 : ℝ)
  have hdiff := hre2.sub hone
  have hcongr : ∀ n : ℕ,
      poissonWeight r n * Real.cos ((n : ℝ) * θ)
        = 2 * (z ^ n).re - (if n = 0 then (1 : ℝ) else 0) := by
    intro n
    rw [hpow n, poissonWeight]
    by_cases h : n = 0
    · simp [h]; norm_num
    · simp only [h, if_false]
      ring
  have hfinal : (2 * (1 - z)⁻¹.re - 1)
      = (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2) := by
    rw [hSre]
    field_simp
    ring
  rw [← hfinal]
  exact hdiff.congr_fun hcongr

theorem hasSum_primeFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ s : ℝ) :
    HasSum (fun n : ℕ => (1 - r ^ 2)⁻¹ * (poissonWeight r n * Real.cos (((n : ℝ) * ℓ) * s)))
      (primeFactor r ℓ s) := by
  have hr2 : (1 : ℝ) - r ^ 2 ≠ 0 := by nlinarith
  have h := (hasSum_poissonExpansion hr0 hr1 (ℓ * s)).mul_left (1 - r ^ 2)⁻¹
  have hval : (1 - r ^ 2)⁻¹ * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (ℓ * s) + r ^ 2))
      = primeFactor r ℓ s := by
    rw [primeFactor]
    field_simp
  rw [← hval]
  refine h.congr_fun (fun n => ?_)
  have hmul : ((n : ℝ) * ℓ) * s = (n : ℝ) * (ℓ * s) := by ring
  rw [hmul]


/-! ## Integration term by term -/

theorem integral_tsum_gamma {ι : Type} [Countable ι] {f : ι → ℝ → ℝ} {c : ι → ℝ}
    (hmeas : ∀ i, Continuous (f i)) (hb : ∀ i s, ‖f i s‖ ≤ c i) (hc : Summable c) :
    (∫ s, ∑' i, f i s ∂semilocalArchimedeanGammaMeasure)
      = ∑' i, ∫ s, f i s ∂semilocalArchimedeanGammaMeasure := by
  refine MeasureTheory.integral_tsum (fun i => (hmeas i).aestronglyMeasurable) ?_
  have hcn : ∀ i, 0 ≤ c i := fun i => le_trans (norm_nonneg (f i 0)) (hb i 0)
  have hle : ∀ i, (∫⁻ s, ‖f i s‖ₑ ∂semilocalArchimedeanGammaMeasure)
      ≤ ENNReal.ofReal (c i) := by
    intro i
    calc (∫⁻ s, ‖f i s‖ₑ ∂semilocalArchimedeanGammaMeasure)
        ≤ ∫⁻ _s : ℝ, ENNReal.ofReal (c i) ∂semilocalArchimedeanGammaMeasure := by
          refine lintegral_mono (fun s => ?_)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hb i s)
      _ = ENNReal.ofReal (c i) * (semilocalArchimedeanGammaMeasure Set.univ) := lintegral_const _
      _ = ENNReal.ofReal (c i) := by rw [measure_univ, mul_one]
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_)
  rw [← ENNReal.ofReal_tsum_of_nonneg hcn hc]
  exact ENNReal.ofReal_lt_top

/-- The `n`-th Poisson coefficient of a prime factor. -/
def pfCoeff (r : ℝ) (n : ℕ) : ℝ := (1 - r ^ 2)⁻¹ * poissonWeight r n

/-- The `n`-th Poisson mode of a prime factor. -/
def pfMode (r ℓ : ℝ) (n : ℕ) (s : ℝ) : ℝ := pfCoeff r n * Real.cos (((n : ℝ) * ℓ) * s)

theorem pfCoeff_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) : 0 ≤ pfCoeff r n := by
  have h : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
  exact mul_nonneg (le_of_lt (inv_pos.mpr h)) (poissonWeight_nonneg hr0 n)

theorem summable_pfCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Summable (pfCoeff r) :=
  (summable_poissonWeight hr0 hr1).mul_left _

theorem norm_pfMode_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℝ) (n : ℕ) (s : ℝ) :
    ‖pfMode r ℓ n s‖ ≤ pfCoeff r n := by
  rw [pfMode, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pfCoeff_nonneg hr0 hr1 n)]
  calc pfCoeff r n * |Real.cos (((n : ℝ) * ℓ) * s)| ≤ pfCoeff r n * 1 :=
        mul_le_mul_of_nonneg_left (abs_cos_le_one _) (pfCoeff_nonneg hr0 hr1 n)
    _ = pfCoeff r n := mul_one _

theorem continuous_pfMode (r ℓ : ℝ) (n : ℕ) : Continuous (pfMode r ℓ n) := by
  unfold pfMode
  fun_prop

theorem hasSum_pfMode {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ s : ℝ) :
    HasSum (fun n : ℕ => pfMode r ℓ n s) (primeFactor r ℓ s) := by
  have h := hasSum_primeFactor hr0 hr1 ℓ s
  refine h.congr_fun (fun n => ?_)
  rw [pfMode, pfCoeff, mul_assoc]

theorem integral_pfMode (r ℓ : ℝ) (n : ℕ) :
    (∫ s, pfMode r ℓ n s ∂semilocalArchimedeanGammaMeasure)
      = pfCoeff r n * semilocalArchimedeanCharacteristic ((n : ℝ) * ℓ) := by
  show (∫ s, pfCoeff r n * Real.cos (((n : ℝ) * ℓ) * s)
      ∂semilocalArchimedeanGammaMeasure) = _
  rw [MeasureTheory.integral_const_mul, integral_cos_semilocalArchimedeanGammaMeasure]

theorem integral_primeFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℝ) :
    (∫ s, primeFactor r ℓ s ∂semilocalArchimedeanGammaMeasure)
      = ∑' n : ℕ, pfCoeff r n * semilocalArchimedeanCharacteristic ((n : ℝ) * ℓ) := by
  have hpf : (fun s : ℝ => primeFactor r ℓ s)
      = fun s : ℝ => ∑' n : ℕ, pfMode r ℓ n s :=
    funext (fun s => ((hasSum_pfMode hr0 hr1 ℓ s).tsum_eq).symm)
  rw [hpf, integral_tsum_gamma (c := pfCoeff r) (continuous_pfMode r ℓ)
    (fun n s => norm_pfMode_le hr0 hr1 ℓ n s) (summable_pfCoeff hr0 hr1)]
  exact tsum_congr (fun n => integral_pfMode r ℓ n)


/-! ## The two-place Gram integral and the covariance -/

theorem semilocalArchimedeanCharacteristic_le_one (t : ℝ) :
    semilocalArchimedeanCharacteristic t ≤ 1 := by
  rw [semilocalArchimedeanCharacteristic]
  exact Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh t) (by norm_num)

theorem summable_pfCoeff_prod {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h11 : r₁ < 1)
    (h20 : 0 ≤ r₂) (h21 : r₂ < 1) :
    Summable (fun mn : ℕ × ℕ => pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2) :=
  Summable.mul_of_nonneg (summable_pfCoeff h10 h11) (summable_pfCoeff h20 h21)
    (fun n => pfCoeff_nonneg h10 h11 n) (fun n => pfCoeff_nonneg h20 h21 n)

theorem hasSum_pfMode_prod {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h11 : r₁ < 1)
    (h20 : 0 ≤ r₂) (h21 : r₂ < 1) (ℓ₁ ℓ₂ s : ℝ) :
    HasSum (fun mn : ℕ × ℕ => pfMode r₁ ℓ₁ mn.1 s * pfMode r₂ ℓ₂ mn.2 s)
      (primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s) := by
  refine (hasSum_pfMode h10 h11 ℓ₁ s).mul (hasSum_pfMode h20 h21 ℓ₂ s) ?_
  refine Summable.of_norm_bounded (summable_pfCoeff_prod h10 h11 h20 h21) (fun mn => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_pfMode_le h10 h11 ℓ₁ mn.1 s) (norm_pfMode_le h20 h21 ℓ₂ mn.2 s)
    (norm_nonneg _) (pfCoeff_nonneg h10 h11 mn.1)

theorem integral_pfMode_prod (r₁ r₂ ℓ₁ ℓ₂ : ℝ) (m n : ℕ) :
    (∫ s, pfMode r₁ ℓ₁ m s * pfMode r₂ ℓ₂ n s ∂semilocalArchimedeanGammaMeasure)
      = pfCoeff r₁ m * pfCoeff r₂ n
        * ((semilocalArchimedeanCharacteristic ((m : ℝ) * ℓ₁ + (n : ℝ) * ℓ₂)
            + semilocalArchimedeanCharacteristic ((m : ℝ) * ℓ₁ - (n : ℝ) * ℓ₂)) / 2) := by
  have hfun : (fun s : ℝ => pfMode r₁ ℓ₁ m s * pfMode r₂ ℓ₂ n s)
      = fun s : ℝ => (pfCoeff r₁ m * pfCoeff r₂ n)
        * (Real.cos (((m : ℝ) * ℓ₁) * s) * Real.cos (((n : ℝ) * ℓ₂) * s)) := by
    funext s
    show (pfCoeff r₁ m * Real.cos (((m : ℝ) * ℓ₁) * s))
        * (pfCoeff r₂ n * Real.cos (((n : ℝ) * ℓ₂) * s)) = _
    ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_cos_mul_cos_gamma]

theorem integral_primeFactor_mul {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h11 : r₁ < 1)
    (h20 : 0 ≤ r₂) (h21 : r₂ < 1) (ℓ₁ ℓ₂ : ℝ) :
    (∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
      = ∑' mn : ℕ × ℕ, pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
          * ((semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁ + (mn.2 : ℝ) * ℓ₂)
              + semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁ - (mn.2 : ℝ) * ℓ₂)) / 2) := by
  have hpf : (fun s : ℝ => primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s)
      = fun s : ℝ => ∑' mn : ℕ × ℕ, pfMode r₁ ℓ₁ mn.1 s * pfMode r₂ ℓ₂ mn.2 s :=
    funext (fun s => ((hasSum_pfMode_prod h10 h11 h20 h21 ℓ₁ ℓ₂ s).tsum_eq).symm)
  rw [hpf, integral_tsum_gamma
    (f := fun mn : ℕ × ℕ => fun s : ℝ => pfMode r₁ ℓ₁ mn.1 s * pfMode r₂ ℓ₂ mn.2 s)
    (c := fun mn : ℕ × ℕ => pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2)
    (fun mn => (continuous_pfMode r₁ ℓ₁ mn.1).mul (continuous_pfMode r₂ ℓ₂ mn.2))
    (fun mn s => by
      rw [norm_mul]
      exact mul_le_mul (norm_pfMode_le h10 h11 ℓ₁ mn.1 s) (norm_pfMode_le h20 h21 ℓ₂ mn.2 s)
        (norm_nonneg _) (pfCoeff_nonneg h10 h11 mn.1))
    (summable_pfCoeff_prod h10 h11 h20 h21)]
  exact tsum_congr (fun mn => integral_pfMode_prod r₁ r₂ ℓ₁ ℓ₂ mn.1 mn.2)

theorem summable_pfSpectrum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℝ) :
    Summable (fun n : ℕ => pfCoeff r n * semilocalArchimedeanCharacteristic ((n : ℝ) * ℓ)) := by
  refine Summable.of_norm_bounded (summable_pfCoeff hr0 hr1) (fun n => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pfCoeff_nonneg hr0 hr1 n),
    abs_of_nonneg (semilocalArchimedeanCharacteristic_pos _).le]
  calc pfCoeff r n * semilocalArchimedeanCharacteristic ((n : ℝ) * ℓ)
      ≤ pfCoeff r n * 1 :=
        mul_le_mul_of_nonneg_left (semilocalArchimedeanCharacteristic_le_one _)
          (pfCoeff_nonneg hr0 hr1 n)
    _ = pfCoeff r n := mul_one _

theorem integral_mul_integral_primeFactor {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h11 : r₁ < 1)
    (h20 : 0 ≤ r₂) (h21 : r₂ < 1) (ℓ₁ ℓ₂ : ℝ) :
    (∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
        * (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
      = ∑' mn : ℕ × ℕ, pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
          * (semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁)
              * semilocalArchimedeanCharacteristic ((mn.2 : ℝ) * ℓ₂)) := by
  have hA := (summable_pfSpectrum h10 h11 ℓ₁).hasSum
  have hB := (summable_pfSpectrum h20 h21 ℓ₂).hasSum
  have hprodsum : Summable (fun mn : ℕ × ℕ =>
      (pfCoeff r₁ mn.1 * semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁))
        * (pfCoeff r₂ mn.2 * semilocalArchimedeanCharacteristic ((mn.2 : ℝ) * ℓ₂))) := by
    refine Summable.of_norm_bounded (summable_pfCoeff_prod h10 h11 h20 h21) (fun mn => ?_)
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (pfCoeff_nonneg h10 h11 mn.1)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pfCoeff_nonneg h10 h11 mn.1)
        (semilocalArchimedeanCharacteristic_pos _).le)]
      calc pfCoeff r₁ mn.1 * semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁)
          ≤ pfCoeff r₁ mn.1 * 1 :=
            mul_le_mul_of_nonneg_left (semilocalArchimedeanCharacteristic_le_one _)
              (pfCoeff_nonneg h10 h11 mn.1)
        _ = pfCoeff r₁ mn.1 := mul_one _
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pfCoeff_nonneg h20 h21 mn.2)
        (semilocalArchimedeanCharacteristic_pos _).le)]
      calc pfCoeff r₂ mn.2 * semilocalArchimedeanCharacteristic ((mn.2 : ℝ) * ℓ₂)
          ≤ pfCoeff r₂ mn.2 * 1 :=
            mul_le_mul_of_nonneg_left (semilocalArchimedeanCharacteristic_le_one _)
              (pfCoeff_nonneg h20 h21 mn.2)
        _ = pfCoeff r₂ mn.2 := mul_one _
  have hmul := hA.mul hB hprodsum
  rw [integral_primeFactor h10 h11 ℓ₁, integral_primeFactor h20 h21 ℓ₂, ← hmul.tsum_eq]
  exact tsum_congr (fun mn => by ring)


/-! ## Strict positivity of the two-place covariance -/

theorem summable_pfProd_mul {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h11 : r₁ < 1)
    (h20 : 0 ≤ r₂) (h21 : r₂ < 1) (g : ℕ × ℕ → ℝ) (hg : ∀ mn, |g mn| ≤ 2) :
    Summable (fun mn : ℕ × ℕ => pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2 * g mn) := by
  refine Summable.of_norm_bounded
    ((summable_pfCoeff_prod h10 h11 h20 h21).mul_left 2) (fun mn => ?_)
  have hab : 0 ≤ pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2 :=
    mul_nonneg (pfCoeff_nonneg h10 h11 mn.1) (pfCoeff_nonneg h20 h21 mn.2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hab]
  calc pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2 * |g mn|
      ≤ pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2 * 2 := mul_le_mul_of_nonneg_left (hg mn) hab
    _ = 2 * (pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2) := by ring

theorem abs_gammaCosCovariance_le (u v : ℝ) : |gammaCosCovariance u v| ≤ 2 := by
  have h1 := semilocalArchimedeanCharacteristic_le_one (u + v)
  have h2 := semilocalArchimedeanCharacteristic_le_one (u - v)
  have h3 := semilocalArchimedeanCharacteristic_le_one u
  have h4 := semilocalArchimedeanCharacteristic_le_one v
  have p1 := (semilocalArchimedeanCharacteristic_pos (u + v)).le
  have p2 := (semilocalArchimedeanCharacteristic_pos (u - v)).le
  have p3 := (semilocalArchimedeanCharacteristic_pos u).le
  have p4 := (semilocalArchimedeanCharacteristic_pos v).le
  rw [gammaCosCovariance, abs_le]
  constructor <;> nlinarith

theorem covariance_eq_tsum {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h11 : r₁ < 1)
    (h20 : 0 ≤ r₂) (h21 : r₂ < 1) (ℓ₁ ℓ₂ : ℝ) :
    (∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
        - (∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
          * (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
      = ∑' mn : ℕ × ℕ, pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
          * gammaCosCovariance ((mn.1 : ℝ) * ℓ₁) ((mn.2 : ℝ) * ℓ₂) := by
  have hS1 : Summable (fun mn : ℕ × ℕ => pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
      * ((semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁ + (mn.2 : ℝ) * ℓ₂)
          + semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁ - (mn.2 : ℝ) * ℓ₂)) / 2)) := by
    refine summable_pfProd_mul h10 h11 h20 h21 _ (fun mn => ?_)
    have h1 := semilocalArchimedeanCharacteristic_le_one ((mn.1 : ℝ) * ℓ₁ + (mn.2 : ℝ) * ℓ₂)
    have h2 := semilocalArchimedeanCharacteristic_le_one ((mn.1 : ℝ) * ℓ₁ - (mn.2 : ℝ) * ℓ₂)
    have p1 := (semilocalArchimedeanCharacteristic_pos ((mn.1 : ℝ) * ℓ₁ + (mn.2 : ℝ) * ℓ₂)).le
    have p2 := (semilocalArchimedeanCharacteristic_pos ((mn.1 : ℝ) * ℓ₁ - (mn.2 : ℝ) * ℓ₂)).le
    rw [abs_le]
    constructor <;> linarith
  have hS2 : Summable (fun mn : ℕ × ℕ => pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
      * (semilocalArchimedeanCharacteristic ((mn.1 : ℝ) * ℓ₁)
          * semilocalArchimedeanCharacteristic ((mn.2 : ℝ) * ℓ₂))) := by
    refine summable_pfProd_mul h10 h11 h20 h21 _ (fun mn => ?_)
    have h1 := semilocalArchimedeanCharacteristic_le_one ((mn.1 : ℝ) * ℓ₁)
    have h2 := semilocalArchimedeanCharacteristic_le_one ((mn.2 : ℝ) * ℓ₂)
    have p1 := (semilocalArchimedeanCharacteristic_pos ((mn.1 : ℝ) * ℓ₁)).le
    have p2 := (semilocalArchimedeanCharacteristic_pos ((mn.2 : ℝ) * ℓ₂)).le
    rw [abs_le]
    constructor <;> nlinarith
  rw [integral_primeFactor_mul h10 h11 h20 h21,
    integral_mul_integral_primeFactor h10 h11 h20 h21, ← Summable.tsum_sub hS1 hS2]
  refine tsum_congr (fun mn => ?_)
  rw [gammaCosCovariance]
  ring

theorem covariance_pos {r₁ r₂ ℓ₁ ℓ₂ : ℝ} (h10 : 0 < r₁) (h11 : r₁ < 1)
    (h20 : 0 < r₂) (h21 : r₂ < 1) (hl1 : 0 < ℓ₁) (hl2 : 0 < ℓ₂) :
    (∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
        * (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
      < ∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure := by
  have hkey : 0 < (∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s
        ∂semilocalArchimedeanGammaMeasure)
      - (∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
        * (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure) := by
    rw [covariance_eq_tsum h10.le h11 h20.le h21]
    have hnn : ∀ mn : ℕ × ℕ, 0 ≤ pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
        * gammaCosCovariance ((mn.1 : ℝ) * ℓ₁) ((mn.2 : ℝ) * ℓ₂) := by
      intro mn
      refine mul_nonneg (mul_nonneg (pfCoeff_nonneg h10.le h11 mn.1)
        (pfCoeff_nonneg h20.le h21 mn.2)) ?_
      exact gammaCosCovariance_nonneg (mul_nonneg (Nat.cast_nonneg _) hl1.le)
        (mul_nonneg (Nat.cast_nonneg _) hl2.le)
    have hsum : Summable (fun mn : ℕ × ℕ => pfCoeff r₁ mn.1 * pfCoeff r₂ mn.2
        * gammaCosCovariance ((mn.1 : ℝ) * ℓ₁) ((mn.2 : ℝ) * ℓ₂)) :=
      summable_pfProd_mul h10.le h11 h20.le h21 _
        (fun mn => abs_gammaCosCovariance_le _ _)
    have hpf1 : 0 < pfCoeff r₁ 1 := by
      have hd : (0 : ℝ) < 1 - r₁ ^ 2 := by nlinarith
      have hw : poissonWeight r₁ 1 = 2 * r₁ := by rw [poissonWeight]; norm_num
      rw [pfCoeff, hw]
      positivity
    have hpf2 : 0 < pfCoeff r₂ 1 := by
      have hd : (0 : ℝ) < 1 - r₂ ^ 2 := by nlinarith
      have hw : poissonWeight r₂ 1 = 2 * r₂ := by rw [poissonWeight]; norm_num
      rw [pfCoeff, hw]
      positivity
    have hterm : 0 < pfCoeff r₁ ((1, 1) : ℕ × ℕ).1 * pfCoeff r₂ ((1, 1) : ℕ × ℕ).2
        * gammaCosCovariance ((((1, 1) : ℕ × ℕ).1 : ℝ) * ℓ₁)
          ((((1, 1) : ℕ × ℕ).2 : ℝ) * ℓ₂) := by
      have hc1 : (((1, 1) : ℕ × ℕ).1 : ℝ) * ℓ₁ = ℓ₁ := by norm_num
      have hc2 : (((1, 1) : ℕ × ℕ).2 : ℝ) * ℓ₂ = ℓ₂ := by norm_num
      rw [hc1, hc2]
      exact mul_pos (mul_pos hpf1 hpf2) (gammaCosCovariance_pos hl1 hl2)
    exact lt_of_lt_of_le hterm (hsum.le_tsum ((1, 1) : ℕ × ℕ) (fun j _ => hnn j))
  linarith


/-! ## The partition masses `Z_T` -/

theorem continuous_primeFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℝ) :
    Continuous (primeFactor r ℓ) := by
  have hden : Continuous (fun s : ℝ => 1 - 2 * r * Real.cos (ℓ * s) + r ^ 2) := by fun_prop
  exact hden.inv₀ (fun s => (poissonDenom_pos hr0 hr1 (ℓ * s)).ne')

theorem primeFactor_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ s : ℝ) :
    primeFactor r ℓ s ≤ ((1 - r) ^ 2)⁻¹ := by
  have hlow : (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos (ℓ * s) + r ^ 2 := by
    nlinarith [Real.cos_le_one (ℓ * s)]
  have hpos : (0 : ℝ) < (1 - r) ^ 2 := by nlinarith
  rw [primeFactor]
  gcongr

theorem primeFactor_ge {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ s : ℝ) :
    ((1 + r) ^ 2)⁻¹ ≤ primeFactor r ℓ s := by
  have hup : 1 - 2 * r * Real.cos (ℓ * s) + r ^ 2 ≤ (1 + r) ^ 2 := by
    nlinarith [Real.neg_one_le_cos (ℓ * s)]
  rw [primeFactor]
  have hd := poissonDenom_pos hr0 hr1 (ℓ * s)
  gcongr

theorem integrable_primeFactor {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℝ) :
    Integrable (primeFactor r ℓ) semilocalArchimedeanGammaMeasure := by
  refine Integrable.of_bound (continuous_primeFactor hr0 hr1 ℓ).aestronglyMeasurable
    ((1 - r) ^ 2)⁻¹ ?_
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_of_nonneg (primeFactor_pos hr0 hr1 ℓ s).le]
  exact primeFactor_le hr0 hr1 ℓ s

theorem integral_primeFactor_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℝ) :
    0 < ∫ s, primeFactor r ℓ s ∂semilocalArchimedeanGammaMeasure := by
  have hmono := MeasureTheory.integral_mono
    (MeasureTheory.integrable_const (((1 + r) ^ 2)⁻¹)) (integrable_primeFactor hr0 hr1 ℓ)
    (fun s => primeFactor_ge hr0 hr1 ℓ s)
  rw [MeasureTheory.integral_const] at hmono
  simp only [MeasureTheory.probReal_univ, one_smul] at hmono
  have hp : (0 : ℝ) < ((1 + r) ^ 2)⁻¹ := by positivity
  linarith

theorem integral_one_gamma :
    (∫ _s : ℝ, (1 : ℝ) ∂semilocalArchimedeanGammaMeasure) = 1 := by
  rw [MeasureTheory.integral_const]
  simp

/-- **Semilocal Sonin two-place positive association.**  For any two positive frequencies and
any two Poisson radii in `(0,1)`, the unnormalized degree-zero Gram mass strictly exceeds the
product of the one-place masses:  `Z_{p,q} · Z_∅ > Z_p · Z_q`. -/
theorem semilocal_twoPlace_association {r₁ r₂ ℓ₁ ℓ₂ : ℝ} (h10 : 0 < r₁) (h11 : r₁ < 1)
    (h20 : 0 < r₂) (h21 : r₂ < 1) (hl1 : 0 < ℓ₁) (hl2 : 0 < ℓ₂) :
    (∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
        * (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
      < (∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
        * (∫ _s : ℝ, (1 : ℝ) ∂semilocalArchimedeanGammaMeasure) := by
  rw [integral_one_gamma, mul_one]
  exact covariance_pos h10 h11 h20 h21 hl1 hl2

/-- **The strictly positive mixed logarithmic cross-effect.**
`log Z_{p,q} − log Z_p − log Z_q + log Z_∅ > 0`. -/
theorem semilocal_twoPlace_log_crossEffect {r₁ r₂ ℓ₁ ℓ₂ : ℝ} (h10 : 0 < r₁) (h11 : r₁ < 1)
    (h20 : 0 < r₂) (h21 : r₂ < 1) (hl1 : 0 < ℓ₁) (hl2 : 0 < ℓ₂) :
    0 < Real.log (∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s
          ∂semilocalArchimedeanGammaMeasure)
        - Real.log (∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
        - Real.log (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure)
        + Real.log (∫ _s : ℝ, (1 : ℝ) ∂semilocalArchimedeanGammaMeasure) := by
  have hZ1 : 0 < ∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure :=
    integral_primeFactor_pos h10.le h11 ℓ₁
  have hZ2 : 0 < ∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure :=
    integral_primeFactor_pos h20.le h21 ℓ₂
  have hlt := covariance_pos h10 h11 h20 h21 hl1 hl2
  have hlog : Real.log ((∫ s, primeFactor r₁ ℓ₁ s ∂semilocalArchimedeanGammaMeasure)
        * (∫ s, primeFactor r₂ ℓ₂ s ∂semilocalArchimedeanGammaMeasure))
      < Real.log (∫ s, primeFactor r₁ ℓ₁ s * primeFactor r₂ ℓ₂ s
          ∂semilocalArchimedeanGammaMeasure) :=
    Real.log_lt_log (mul_pos hZ1 hZ2) hlt
  rw [Real.log_mul hZ1.ne' hZ2.ne'] at hlog
  rw [integral_one_gamma, Real.log_one]
  linarith

/-! ## The prime specialization -/

theorem primeRadius_pos {p : ℕ} (hp : 2 ≤ p) : 0 < (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  exact Real.rpow_pos_of_pos this _

theorem primeRadius_lt_one {p : ℕ} (hp : 2 ≤ p) : (p : ℝ) ^ (-(1 : ℝ) / 2) < 1 := by
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num)

theorem primeLog_pos {p : ℕ} (hp : 2 ≤ p) : 0 < Real.log (p : ℝ) := by
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  exact Real.log_pos h1

/-- **The card's theorem for two primes.**  With `r_p = p^{-1/2}` and `ℓ_p = log p`, the
degree-zero Gram mass of two prime Poisson factors against the archimedean Gamma measure has a
strictly positive two-place mixed cross-effect. -/
theorem semilocal_prime_twoPlace_association {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (∫ s, primeFactor ((p : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log p) s
        ∂semilocalArchimedeanGammaMeasure)
      * (∫ s, primeFactor ((q : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log q) s
        ∂semilocalArchimedeanGammaMeasure)
    < ∫ s, primeFactor ((p : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log p) s
        * primeFactor ((q : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log q) s
        ∂semilocalArchimedeanGammaMeasure :=
  covariance_pos (primeRadius_pos hp) (primeRadius_lt_one hp)
    (primeRadius_pos hq) (primeRadius_lt_one hq) (primeLog_pos hp) (primeLog_pos hq)


end RHTower.SemilocalTwoPlace

end
