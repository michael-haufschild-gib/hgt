import GaloisForLFunctions.BiScaleUncertainty.CramerTailMeanSquare
import GaloisForLFunctions.BiScaleUncertainty.CramerLiminfLaw
import GaloisForLFunctions.BiScaleUncertainty.ChebyshevGaugeNyquistCellQuadrature
import GaloisForLFunctions.BiScaleUncertainty.BandSlopeZeroEnergyLaw

/-!
# Cramér's limit law: the asymptotic mean square of the normalized Chebyshev error is the zero energy

Under the Riemann hypothesis, the mean-square band of the normalized Chebyshev error
`Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)` has a definite asymptotic slope equal to the multiplicity-weighted
reciprocal-norm-square sum over all nontrivial zeros:

`lim_{M → ∞} (1/M) ∫_0^M Ẽ(t)² dt = Σ_ρ m_ρ² / |ρ|²`.

This resolves Open Problem 7.1a of the bi-scale uncertainty programme: the band constant of the raw
Chebyshev error is the zero energy itself.

**Mechanism.**
* **Lower bound (`cramer_liminf_law_zeroEnergy`).** Gauge-delta probes show that every finite part
  of `Σ_ρ m_ρ²/|ρ|²` is eventually below `(1/M) ∫_0^M Ẽ²`.
* **Upper bound (`cramer_limsup_law_zeroEnergy`).** Summing the `r = 1` dyadic decomposition
  `dyadic_chebyshev_sq_div_le` over dyadic blocks `[2^j, 2^{j+1}]` bounds `∫_0^M Ẽ²` by `(1+η)` times
  the log-coordinate mean square of the finite low-ordinate sum `lowZeroSum K₀ (e^t)` plus a
  geometric tail `O((1 + 1/η) (5/6)^{K₀} M)` and `O(1 + 1/η)`. Under RH, the frequencies of distinct
  support points of `ξ` are distinct, so `tendsto_mean_normSq_tsum` evaluates the mean square of
  `lowZeroSum K₀ (e^t)` as the partial zero energy `Σ_{|γ_ρ|≤2^{K₀}} m_ρ²/|ρ|² ≤ Σ_ρ m_ρ²/|ρ|²`.
  Letting `K₀ → ∞` and `η → 0⁺` closes the upper bound.

**Corollaries.**
1. **Physical-coordinate limit (`tendsto_mean_sq_chebyshevError_log`):**
   `(1 / log X) ∫_1^X ((ψ(x) − x)/x)² dx → Σ_ρ m_ρ² / |ρ|²` as `X → ∞`.
2. **Sliding-window sublinearity (`tendsto_window_sq_normalizedLogError_div`):**
   for every fixed window width `W ≥ 0`, `(1/L) ∫_{L−W}^L Ẽ(t)² dt → 0` as `L → ∞`.
3. **Discrete Nyquist-cell and classical discrete limits (`tendsto_centeredCellSum_div_log`,
   `tendsto_discreteChebyshevSum_div_log`):**
   `(1 / log M) Σ_{n<M} (ψ(n) − m_n)²/(n(n+1)) → Σ_ρ m_ρ²/|ρ|²` and
   `(1 / log M) Σ_{n<M} (ψ(n) − n)²/(n(n+1)) → Σ_ρ m_ρ²/|ρ|²`.
4. **Sharp asymptotic band slope (`isLeast_asymptoticBandSlope_zeroEnergy`):**
   every `C > Σ_ρ m_ρ²/|ρ|²` is a valid linear band slope (`∃ K ≥ 0, ∀ L ≥ 0, ∫_0^L Ẽ² ≤ C L + K`),
   and `Σ_ρ m_ρ²/|ρ|²` is the infimum of all valid linear band slopes.
-/

open Complex Finset MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar _root_.RHTower

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- The total zero energy `Σ_ρ m_ρ² / |ρ|²` over all nontrivial zeros of `ζ`. -/
def totalZeroEnergy : ℝ :=
  ∑' ρ : 𝒵, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2

theorem totalZeroEnergy_nonneg : 0 ≤ totalZeroEnergy :=
  tsum_nonneg fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem summable_zetaZeroEnergy_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Summable fun ρ : 𝒵 => (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2 := by
  have hs := summable_zeroEnergy_of_riemannHypothesis hRH
  let e : 𝒵 ≃ criticalZeros :=
    ⟨fun ρ => ⟨ρ, re_eq_half_of_mem hRH ρ⟩, fun ρ => ρ.1, fun _ => rfl, fun _ => rfl⟩
  exact e.summable_iff.mpr hs

theorem summable_xiDivisorSupport_zeroEnergy_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Summable fun ρ : XiDivisorSupport => (xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2 := by
  rw [← xiDivisorSupportEquivCarrier.symm.summable_iff]
  refine (summable_zetaZeroEnergy_of_riemannHypothesis hRH).congr fun ρ => ?_
  simp only [Function.comp_apply, xiDivisorSupportEquivCarrier_symm_coe,
    xiSupportMultiplicity_eq_zetaZeroMult]

/-! ## Log-coordinate representation and Parseval limit of `lowZeroSum` -/

/-- Support points of `ξ` with ordinate `|γ_ρ| ≤ 2^{K₀}`. -/
def lowSupportFinset (K₀ : ℕ) : Finset XiDivisorSupport :=
  by classical exact (xiCopiesBelow ((2 : ℝ) ^ K₀)).image Sigma.fst

theorem mem_lowSupportFinset_iff {K₀ : ℕ} {ρ : XiDivisorSupport} :
    ρ ∈ lowSupportFinset K₀ ↔ |(ρ : ℂ).im| ≤ (2 : ℝ) ^ K₀ := by
  classical
  unfold lowSupportFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact mem_xiCopiesBelow.mp hq
  · intro hρ
    refine ⟨firstCopy ρ, mem_xiCopiesBelow.mpr hρ, rfl⟩

theorem xiCopiesBelow_eq_sigma_lowSupportFinset (K₀ : ℕ) :
    xiCopiesBelow ((2 : ℝ) ^ K₀) =
      (lowSupportFinset K₀).sigma (fun ρ =>
        (Finset.univ : Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)))))) := by
  classical
  ext q
  rw [Finset.mem_sigma, mem_lowSupportFinset_iff, mem_xiCopiesBelow]
  simp only [Finset.mem_univ, and_true]
  rfl

/-- Multiplicity-weighted coefficient `−m_ρ / ρ` on `lowSupportFinset K₀`. -/
def lowSupportCoeff (K₀ : ℕ) (ρ : XiDivisorSupport) : ℂ :=
  by classical exact if ρ ∈ lowSupportFinset K₀ then -(xiSupportMultiplicity ρ : ℂ) / (ρ : ℂ) else 0

theorem summable_norm_lowSupportCoeff (K₀ : ℕ) :
    Summable fun ρ : XiDivisorSupport => ‖lowSupportCoeff K₀ ρ‖ := by
  classical
  refine summable_of_ne_finset_zero (s := lowSupportFinset K₀) fun ρ hρ => ?_
  unfold lowSupportCoeff
  rw [if_neg hρ, norm_zero]

theorem norm_sq_lowSupportCoeff_le (K₀ : ℕ) (ρ : XiDivisorSupport) :
    ‖lowSupportCoeff K₀ ρ‖ ^ 2 ≤ (xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2 := by
  unfold lowSupportCoeff
  split_ifs
  · rw [norm_div, norm_neg, Complex.norm_natCast, div_pow]
  · rw [norm_zero, sq, zero_mul]
    positivity

theorem tsum_norm_sq_lowSupportCoeff_le (hRH : RiemannHypothesis) (K₀ : ℕ) :
    (∑' ρ : XiDivisorSupport, ‖lowSupportCoeff K₀ ρ‖ ^ 2) ≤ totalZeroEnergy := by
  have hs2 : Summable fun ρ : XiDivisorSupport => ‖lowSupportCoeff K₀ ρ‖ ^ 2 := by
    classical
    refine summable_of_ne_finset_zero (s := lowSupportFinset K₀) fun ρ hρ => ?_
    unfold lowSupportCoeff
    rw [if_neg hρ, norm_zero, sq, zero_mul]
  rw [totalZeroEnergy, ← tsum_xiDivisorSupport_zeroEnergy_eq]
  exact hs2.tsum_le_tsum (norm_sq_lowSupportCoeff_le K₀)
    (summable_xiDivisorSupport_zeroEnergy_of_riemannHypothesis hRH)

/-- Under RH, the ordinate map `ρ ↦ Im ρ` on `XiDivisorSupport` is injective. -/
theorem im_injective_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Function.Injective (fun ρ : XiDivisorSupport => (ρ : ℂ).im) := by
  intro ρ₁ ρ₂ h
  apply Subtype.ext
  have h1 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH (firstCopy ρ₁)
  have h2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH (firstCopy ρ₂)
  exact Complex.ext (h1.trans h2.symm) h

/-- Under RH, `e^{−t/2} lowZeroSum K₀ (e^t)` is the trigonometric polynomial with coefficients
`lowSupportCoeff K₀`. -/
theorem exp_neg_half_mul_lowZeroSum_eq (hRH : RiemannHypothesis) (K₀ : ℕ) (t : ℝ) :
    (Real.exp (-t / 2) : ℂ) * lowZeroSum K₀ (Real.exp t) =
      ∑' ρ : XiDivisorSupport,
        lowSupportCoeff K₀ ρ * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) := by
  classical
  have htsum : (∑' ρ : XiDivisorSupport,
      lowSupportCoeff K₀ ρ * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I)) =
      ∑ ρ ∈ lowSupportFinset K₀,
        (-(xiSupportMultiplicity ρ : ℂ) / (ρ : ℂ)) *
          Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) := by
    rw [tsum_eq_sum (s := lowSupportFinset K₀) fun ρ hρ => by
      unfold lowSupportCoeff; rw [if_neg hρ, zero_mul]]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    unfold lowSupportCoeff
    rw [if_pos hρ]
  rw [htsum, lowZeroSum, Finset.mul_sum, xiCopiesBelow_eq_sigma_lowSupportFinset, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hre : (ρ : ℂ).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH (firstCopy ρ)
  have hρ_eq : (ρ : ℂ) = 1 / 2 + ((ρ : ℂ).im : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im (ρ : ℂ)]
    rw [hre]; push_cast; ring
  have hcpow : ((Real.exp t : ℝ) : ℂ) ^ (ρ : ℂ) =
      (Real.exp (t / 2) : ℂ) * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
    have hexp : Complex.exp ((t : ℂ) * (ρ : ℂ)) =
        Complex.exp (((t / 2 : ℝ) : ℂ) + ((((ρ : ℂ).im * t : ℝ) : ℂ) * I)) := by
      congr 1; conv_lhs => rw [hρ_eq]
      push_cast; ring
    rw [hexp, Complex.exp_add, Complex.ofReal_exp]
  have hcancel : (Real.exp (-t / 2) : ℂ) * (Real.exp (t / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
    simp
  have hconst : ∀ i ∈ (Finset.univ :
      Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))))),
      (Real.exp (-t / 2) : ℂ) *
        ((-1 / (((⟨ρ, i⟩ : XiZeroCopy).1 : XiDivisorSupport) : ℂ)) *
          ((Real.exp t : ℝ) : ℂ) ^ ((((⟨ρ, i⟩ : XiZeroCopy).1 : XiDivisorSupport) : ℂ))) =
        (-1 / (ρ : ℂ)) * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) := fun _ _ => by
    change (Real.exp (-t / 2) : ℂ) * ((-1 / (ρ : ℂ)) * ((Real.exp t : ℝ) : ℂ) ^ (ρ : ℂ)) = _
    rw [hcpow]
    linear_combination ((-1 / (ρ : ℂ)) * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I)) * hcancel
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  change (xiSupportMultiplicity ρ : ℂ) *
      ((-1 / (ρ : ℂ)) * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I)) = _
  ring

/-- Log-coordinate identity `‖lowZeroSum K₀ (e^t)‖² / e^t = ‖Σ_ρ lowSupportCoeff K₀ ρ e^{iγ_ρ t}‖²`. -/
theorem norm_sq_lowZeroSum_exp_div_eq (hRH : RiemannHypothesis) (K₀ : ℕ) (t : ℝ) :
    ‖lowZeroSum K₀ (Real.exp t)‖ ^ 2 / Real.exp t =
      ‖∑' ρ : XiDivisorSupport,
        lowSupportCoeff K₀ ρ * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I)‖ ^ 2 := by
  rw [← exp_neg_half_mul_lowZeroSum_eq hRH K₀ t, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  have he : Real.exp (-t / 2) ^ 2 = (Real.exp t)⁻¹ := by
    rw [sq, ← Real.exp_add, show -t / 2 + -t / 2 = -t by ring, Real.exp_neg]
  rw [he, div_eq_inv_mul]

/-- Change of variables `∫_1^{e^L} ‖lowZeroSum K₀ x‖² / x² dx = ∫_0^L ‖Σ_ρ lowSupportCoeff K₀ ρ e^{iγ_ρ t}‖² dt`. -/
theorem integral_lowZeroSum_sq_div_exp_eq (hRH : RiemannHypothesis) (K₀ : ℕ) {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ x in (1 : ℝ)..Real.exp L, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) =
      ∫ t in (0 : ℝ)..L,
        ‖∑' ρ : XiDivisorSupport,
          lowSupportCoeff K₀ ρ * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I)‖ ^ 2 := by
  have hexpL : 1 ≤ Real.exp L := Real.one_le_exp hL
  rw [intervalIntegral.integral_of_le hexpL, intervalIntegral.integral_of_le hL,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have himg : Icc (1 : ℝ) (Real.exp L) = Real.exp '' Icc 0 L := by
    rw [Real.image_exp_Icc, Real.exp_zero]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [abs_of_pos (Real.exp_pos t), smul_eq_mul, ← norm_sq_lowZeroSum_exp_div_eq hRH K₀ t]
  have hpos := (Real.exp_pos t).ne'
  field_simp

/-- Under RH, the mean square of `lowZeroSum K₀` on `[1, e^L]` is asymptotically at most
`totalZeroEnergy`. -/
theorem tendsto_mean_lowZeroSum_sq_div (hRH : RiemannHypothesis) (K₀ : ℕ) :
    Tendsto (fun L : ℝ => (∫ x in (1 : ℝ)..Real.exp L, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) / L)
      atTop (𝓝 (∑' ρ : XiDivisorSupport, ‖lowSupportCoeff K₀ ρ‖ ^ 2)) := by
  have hP := tendsto_mean_normSq_tsum (summable_norm_lowSupportCoeff K₀)
    (im_injective_of_riemannHypothesis hRH)
  refine hP.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  rw [integral_lowZeroSum_sq_div_exp_eq hRH K₀ hL]

/-! ## Summing the dyadic Chebyshev decomposition across `[1, 2^{m+1}]` -/

private theorem integrableOn_chebyshev_sq_div (b : ℝ) :
    IntegrableOn (fun x => (Chebyshev.psi x - x) ^ 2 / x ^ 2) (Icc 1 b) := by
  refine Measure.integrableOn_of_bounded (M := (Chebyshev.psi b + b) ^ 2) measure_Icc_lt_top.ne
    (((Chebyshev.psi_mono.measurable.sub measurable_id).pow_const 2).div
      (measurable_id.pow_const 2)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall fun x hx => ?_
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  refine (div_le_self (sq_nonneg _) hx2).trans ?_
  rw [← sq_abs]
  have hψ := Chebyshev.psi_nonneg x
  have hψb := Chebyshev.psi_mono hx.2
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

private theorem intervalIntegrable_chebyshev_sq_div {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => (Chebyshev.psi x - x) ^ 2 / x ^ 2) volume a b :=
  ((integrableOn_chebyshev_sq_div b).mono_set (by
    rw [uIcc_of_le hab]; exact Icc_subset_Icc ha le_rfl)).intervalIntegrable

private theorem intervalIntegrable_lowZeroSum_sq_div (K₀ : ℕ) {a b : ℝ} (ha : 1 ≤ a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun x => ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact continuousOn_lowZeroSum_sq_div K₀ (by linarith)

/-- Inductive dyadic bound on `[2, 2^{m+1}]`. -/
private theorem integral_chebyshev_sq_div_two_pow_succ_le (hRH : RiemannHypothesis) (K₀ : ℕ)
    {η : ℝ} (hη : 0 < η) (m : ℕ) :
    ∫ x in (2 : ℝ)..(2 : ℝ) ^ (m + 1), (Chebyshev.psi x - x) ^ 2 / x ^ 2 ≤
      (1 + η) * (∫ x in (2 : ℝ)..(2 : ℝ) ^ (m + 1), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        3 * (1 + 1 / η) *
          (8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * m +
            (|Real.log (2 * Real.pi)| + 2) ^ 2 * (1 - (1 / 2 : ℝ) ^ m)) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hm2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hm1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by linarith
    have hm_le : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ (m + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_chebyshev_sq_div (by norm_num) hm2)
      (intervalIntegrable_chebyshev_sq_div hm1 hm_le),
      ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_lowZeroSum_sq_div K₀ (by norm_num) hm2)
      (intervalIntegrable_lowZeroSum_sq_div K₀ hm1 hm_le)]
    have hpow : (2 : ℝ) ^ (m + 2) = 2 * (2 : ℝ) ^ (m + 1) := by rw [pow_succ']
    have hstep : ∫ x in (2 : ℝ) ^ (m + 1)..(2 : ℝ) ^ (m + 2),
        (Chebyshev.psi x - x) ^ 2 / x ^ 2 ≤
        (1 + η) * (∫ x in (2 : ℝ) ^ (m + 1)..(2 : ℝ) ^ (m + 2),
          ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
          3 * (1 + 1 / η) *
            (8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ +
              (|Real.log (2 * Real.pi)| + 2) ^ 2 / (2 : ℝ) ^ (m + 1)) := by
      rw [hpow]
      exact dyadic_chebyshev_sq_div_le hRH K₀ hm2 hη
    have hgeom : 1 - (1 / 2 : ℝ) ^ m + 1 / (2 : ℝ) ^ (m + 1) = 1 - (1 / 2 : ℝ) ^ (m + 1) := by
      rw [one_div_pow, one_div_pow, pow_succ]
      set p : ℝ := (2 : ℝ) ^ m
      have hp : p ≠ 0 := by positivity
      field_simp
      ring
    push_cast
    linear_combination ih + hstep +
      3 * (1 + 1 / η) * (|Real.log (2 * Real.pi)| + 2) ^ 2 * hgeom

/-- Cumulative dyadic bound on `[1, 2^{m+1}]`. -/
theorem integral_chebyshev_sq_div_one_to_two_pow_le (hRH : RiemannHypothesis) (K₀ : ℕ)
    {η : ℝ} (hη : 0 < η) (m : ℕ) :
    ∫ x in (1 : ℝ)..(2 : ℝ) ^ (m + 1), (Chebyshev.psi x - x) ^ 2 / x ^ 2 ≤
      (1 + η) * (∫ x in (1 : ℝ)..(2 : ℝ) ^ (m + 1), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        ((∫ x in (1 : ℝ)..2, (Chebyshev.psi x - x) ^ 2 / x ^ 2) +
          3 * (1 + 1 / η) * (|Real.log (2 * Real.pi)| + 2) ^ 2) +
        24 * (1 + 1 / η) * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * m := by
  have hm2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_chebyshev_sq_div le_rfl (by norm_num))
    (intervalIntegrable_chebyshev_sq_div (by norm_num) hm2)]
  have hlow_split := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_lowZeroSum_sq_div K₀ le_rfl (by norm_num))
    (intervalIntegrable_lowZeroSum_sq_div K₀ (by norm_num) hm2)
  have hlow_nonneg : 0 ≤ ∫ x in (1 : ℝ)..2, ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hlow_le : ∫ x in (2 : ℝ)..(2 : ℝ) ^ (m + 1), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2 ≤
      ∫ x in (1 : ℝ)..(2 : ℝ) ^ (m + 1), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2 := by
    linarith [hlow_split]
  have hind := integral_chebyshev_sq_div_two_pow_succ_le hRH K₀ hη m
  have hhalf : 1 - (1 / 2 : ℝ) ^ m ≤ 1 := by
    have : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
    linarith
  have hη1 : 0 ≤ 3 * (1 + 1 / η) := by positivity
  have hB : (|Real.log (2 * Real.pi)| + 2) ^ 2 * (1 - (1 / 2 : ℝ) ^ m) ≤
      (|Real.log (2 * Real.pi)| + 2) ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg _) hhalf
  have h1 : 3 * (1 + 1 / η) *
      (8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * m +
        (|Real.log (2 * Real.pi)| + 2) ^ 2 * (1 - (1 / 2 : ℝ) ^ m)) ≤
      3 * (1 + 1 / η) *
      (8 * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * m +
        (|Real.log (2 * Real.pi)| + 2) ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hB) hη1
  have h2 := mul_le_mul_of_nonneg_left hlow_le (by linarith : 0 ≤ 1 + η)
  linarith

/-! ## Cramér's limsup and limit laws -/

/-- Continuous-time bound on `∫_0^M Ẽ²` in terms of `lowZeroSum K₀` at the next dyadic scale
`L(M) = (⌊M / log 2⌋₊ + 1) log 2`. -/
private theorem integral_normalizedLogError_sq_le_dyadic (hRH : RiemannHypothesis) (K₀ : ℕ)
    {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) :
    ∫ t in Icc 0 M, normalizedLogError t ^ 2 ≤
      (1 + η) * (∫ x in (1 : ℝ)..Real.exp ((⌊M / Real.log 2⌋₊ + 1 : ℕ) * Real.log 2),
        ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
        ((∫ x in (1 : ℝ)..2, (Chebyshev.psi x - x) ^ 2 / x ^ 2) +
          3 * (1 + 1 / η) * (|Real.log (2 * Real.pi)| + 2) ^ 2) +
        (24 * (1 + 1 / η) * cramerTailEnergyConstant / Real.log 2) * (5 / 6 : ℝ) ^ K₀ * M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set m := ⌊M / Real.log 2⌋₊
  have hm_le : (m : ℝ) ≤ M / Real.log 2 := Nat.floor_le (div_nonneg hM hlog2.le)
  have hM_lt : M < ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [ ← div_lt_iff₀ hlog2]
    exact_mod_cast Nat.lt_floor_add_one (M / Real.log 2)
  have hexp_eq : Real.exp (((m + 1 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ (m + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hexp_le : Real.exp M ≤ (2 : ℝ) ^ (m + 1) := by
    rw [← hexp_eq]
    exact Real.exp_le_exp.mpr hM_lt.le
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := one_le_pow₀ (by norm_num)
  rw [integral_normalizedLogError_sq_eq M, hexp_eq]
  have hmono : (∫ x in Icc 1 (Real.exp M), (Chebyshev.psi x - x) ^ 2 / x ^ 2) ≤
      ∫ x in (1 : ℝ)..(2 : ℝ) ^ (m + 1), (Chebyshev.psi x - x) ^ 2 / x ^ 2 := by
    rw [intervalIntegral.integral_of_le hpow1, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set (integrableOn_chebyshev_sq_div _)
      (Eventually.of_forall fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
      (Icc_subset_Icc le_rfl hexp_le).eventuallyLE
  refine hmono.trans ?_
  have hdy := integral_chebyshev_sq_div_one_to_two_pow_le hRH K₀ hη m
  refine hdy.trans ?_
  have hC0 : 0 ≤ 24 * (1 + 1 / η) * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ := by
    have := cramerTailEnergyConstant_nonneg
    positivity
  have htail : 24 * (1 + 1 / η) * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * (m : ℝ) ≤
      (24 * (1 + 1 / η) * cramerTailEnergyConstant / Real.log 2) * (5 / 6 : ℝ) ^ K₀ * M := by
    calc 24 * (1 + 1 / η) * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * (m : ℝ)
        ≤ 24 * (1 + 1 / η) * cramerTailEnergyConstant * (5 / 6 : ℝ) ^ K₀ * (M / Real.log 2) :=
          mul_le_mul_of_nonneg_left hm_le hC0
      _ = (24 * (1 + 1 / η) * cramerTailEnergyConstant / Real.log 2) * (5 / 6 : ℝ) ^ K₀ * M := by
          ring
  linarith

/-- The dyadic ceiling `L(M) = (⌊M / log 2⌋₊ + 1) log 2` tends to `∞` and satisfies `L(M)/M → 1`. -/
private theorem tendsto_dyadicCeiling_atTop :
    Tendsto (fun M : ℝ => ((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * Real.log 2) atTop atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine tendsto_atTop_mono (fun M => ?_) tendsto_id
  by_cases hM : 0 ≤ M
  · have := (div_lt_iff₀ hlog2).mp (by
      exact_mod_cast Nat.lt_floor_add_one (M / Real.log 2) :
        M / Real.log 2 < ((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ))
    exact this.le
  · have : 0 ≤ ((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
    simp only [id]
    linarith

private theorem tendsto_dyadicCeiling_div :
    Tendsto (fun M : ℝ => (((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * Real.log 2) / M) atTop (𝓝 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hupper : Tendsto (fun M : ℝ => 1 + Real.log 2 / M) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    rw [one_le_div hM]
    have := (div_lt_iff₀ hlog2).mp (by
      exact_mod_cast Nat.lt_floor_add_one (M / Real.log 2) :
        M / Real.log 2 < ((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ))
    exact this.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    have hfl : (⌊M / Real.log 2⌋₊ : ℝ) ≤ M / Real.log 2 := Nat.floor_le (div_nonneg hM.le hlog2.le)
    have hle : ((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * Real.log 2 ≤ M + Real.log 2 := by
      push_cast
      have := mul_le_mul_of_nonneg_right hfl hlog2.le
      rw [div_mul_cancel₀ _ hlog2.ne'] at this
      linarith
    calc (((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * Real.log 2) / M
        ≤ (M + Real.log 2) / M := div_le_div_of_nonneg_right hle hM.le
      _ = 1 + Real.log 2 / M := by rw [add_div, div_self hM.ne']

/-- **Cramér limsup law, full zero energy.** Under RH, for every `ε > 0`, eventually
`(1/M) ∫_0^M Ẽ² ≤ Σ_ρ m_ρ²/|ρ|² + ε`. -/
theorem cramer_limsup_law_zeroEnergy (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℝ in atTop,
      (∫ t in Icc 0 M, normalizedLogError t ^ 2) / M ≤ totalZeroEnergy + ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hZ0 : 0 ≤ totalZeroEnergy := totalZeroEnergy_nonneg
  set η := ε / (4 * (totalZeroEnergy + 1))
  have hη : 0 < η := by positivity
  have hηZ : (1 + η) * totalZeroEnergy ≤ totalZeroEnergy + ε / 4 := by
    have : η * totalZeroEnergy ≤ ε / 4 := by
      simp only [η]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  -- choose `K₀` so that the geometric tail is at most `ε / 4`
  set A := 24 * (1 + 1 / η) * cramerTailEnergyConstant / Real.log 2
  have hA0 : 0 ≤ A := by
    have := cramerTailEnergyConstant_nonneg
    positivity
  have htail_lim : Tendsto (fun K₀ : ℕ => A * (5 / 6 : ℝ) ^ K₀) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6)
        (by norm_num : (5 / 6 : ℝ) < 1)).const_mul A
  obtain ⟨K₀, hK₀⟩ := (htail_lim.eventually (gt_mem_nhds (show 0 < ε / 4 by linarith))).exists
  -- control the low-ordinate mean square via `tendsto_mean_lowZeroSum_sq_div`
  set Z_low := ∑' ρ : XiDivisorSupport, ‖lowSupportCoeff K₀ ρ‖ ^ 2
  have hZ_low_le : Z_low ≤ totalZeroEnergy := tsum_norm_sq_lowSupportCoeff_le hRH K₀
  set LM : ℝ → ℝ := fun M => ((⌊M / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * Real.log 2
  have hlow_lim : Tendsto (fun M : ℝ =>
      (1 + η) * ((∫ x in (1 : ℝ)..Real.exp (LM M), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) / LM M) *
        (LM M / M)) atTop (𝓝 ((1 + η) * Z_low * 1)) :=
    (tendsto_const_nhds.mul
      ((tendsto_mean_lowZeroSum_sq_div hRH K₀).comp tendsto_dyadicCeiling_atTop)).mul
      tendsto_dyadicCeiling_div
  rw [mul_one] at hlow_lim
  have hlow_ev : ∀ᶠ M : ℝ in atTop,
      (1 + η) * (∫ x in (1 : ℝ)..Real.exp (LM M), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) / M <
        (1 + η) * Z_low + ε / 4 := by
    filter_upwards [hlow_lim.eventually (gt_mem_nhds (show (1 + η) * Z_low <
        (1 + η) * Z_low + ε / 4 by linarith)), eventually_gt_atTop (0 : ℝ)] with M hM hM0
    have hLM0 : 0 < LM M := by simp only [LM]; positivity
    have heq : (1 + η) * (∫ x in (1 : ℝ)..Real.exp (LM M), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) / M =
        (1 + η) * ((∫ x in (1 : ℝ)..Real.exp (LM M), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) / LM M) *
          (LM M / M) := by
      field_simp [hLM0.ne', hM0.ne']
    rwa [heq]
  -- control the constant `O(1/M)` term
  set C₀ := (∫ x in (1 : ℝ)..2, (Chebyshev.psi x - x) ^ 2 / x ^ 2) +
    3 * (1 + 1 / η) * (|Real.log (2 * Real.pi)| + 2) ^ 2
  have hC₀_ev : ∀ᶠ M : ℝ in atTop, C₀ / M < ε / 4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds (by linarith))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlow_ev, hC₀_ev] with M hM0 hlowM hC₀M
  have hdy := integral_normalizedLogError_sq_le_dyadic hRH K₀ hη hM0.le
  have hdiv := div_le_div_of_nonneg_right hdy hM0.le
  have hsplit : ((1 + η) * (∫ x in (1 : ℝ)..Real.exp (LM M), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) +
      C₀ + A * (5 / 6 : ℝ) ^ K₀ * M) / M =
      (1 + η) * (∫ x in (1 : ℝ)..Real.exp (LM M), ‖lowZeroSum K₀ x‖ ^ 2 / x ^ 2) / M +
        C₀ / M + A * (5 / 6 : ℝ) ^ K₀ := by
    field_simp [hM0.ne']
  change (∫ t in Icc 0 M, normalizedLogError t ^ 2) / M ≤ _ at hdiv
  rw [hsplit] at hdiv
  have hZ_step : (1 + η) * Z_low ≤ (1 + η) * totalZeroEnergy :=
    mul_le_mul_of_nonneg_left hZ_low_le (by positivity)
  linarith

/-- **Cramér's limit law (gauge coordinates).** Under the Riemann hypothesis, the asymptotic mean
square of the normalized Chebyshev error `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)` equals the zero energy:
`lim_{M → ∞} (1/M) ∫_0^M Ẽ(t)² dt = Σ_ρ m_ρ² / |ρ|²`. -/
theorem tendsto_mean_sq_normalizedLogError (hRH : RiemannHypothesis) :
    Tendsto (fun M : ℝ => (∫ t in Icc 0 M, normalizedLogError t ^ 2) / M) atTop
      (𝓝 totalZeroEnergy) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [cramer_liminf_law_zeroEnergy hRH (half_pos hε),
    cramer_limsup_law_zeroEnergy hRH (half_pos hε)] with M hlo hhi
  rw [Real.dist_eq, abs_lt]
  change totalZeroEnergy - ε / 2 ≤ _ at hlo
  constructor <;> linarith

/-- Interval-integral form of Cramér's limit law. -/
theorem tendsto_intervalIntegral_sq_normalizedLogError (hRH : RiemannHypothesis) :
    Tendsto (fun M : ℝ => (∫ t in (0 : ℝ)..M, normalizedLogError t ^ 2) / M) atTop
      (𝓝 totalZeroEnergy) := by
  refine (tendsto_mean_sq_normalizedLogError hRH).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
  rw [intervalIntegral.integral_of_le hM, integral_Icc_eq_integral_Ioc]

/-! ## Corollaries of Cramér's limit law -/

/-- **Corollary 1 (Physical-coordinate limit law).** Under RH,
`lim_{X → ∞} (1 / log X) ∫_1^X ((ψ(x) − x) / x)² dx = Σ_ρ m_ρ² / |ρ|²`. -/
theorem tendsto_mean_sq_chebyshevError_log (hRH : RiemannHypothesis) :
    Tendsto (fun X : ℝ => (∫ x in Icc 1 X, (Chebyshev.psi x - x) ^ 2 / x ^ 2) / Real.log X)
      atTop (𝓝 totalZeroEnergy) := by
  have h := (tendsto_mean_sq_normalizedLogError hRH).comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  simp only [Function.comp_apply, integral_normalizedLogError_sq_eq, Real.exp_log hX]

/-- **Corollary 2 (Sliding-window sublinearity of the band).** Under RH, for every fixed window
width `W ≥ 0`, `(1/L) ∫_{L−W}^L Ẽ(t)² dt → 0` as `L → ∞`. -/
theorem tendsto_window_sq_normalizedLogError_div (hRH : RiemannHypothesis) {W : ℝ} (hW : 0 ≤ W) :
    Tendsto (fun L : ℝ => (∫ t in (L - W)..L, normalizedLogError t ^ 2) / L) atTop (𝓝 0) := by
  have h1 := tendsto_intervalIntegral_sq_normalizedLogError hRH
  have hshift : Tendsto (fun L : ℝ => L - W) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-W) tendsto_id
  have hratio : Tendsto (fun L : ℝ => (L - W) / L) atTop (𝓝 1) := by
    have hsub : Tendsto (fun L : ℝ => 1 - W / L) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    field_simp [hL.ne']
  have h2 : Tendsto (fun L : ℝ =>
      ((∫ t in (0 : ℝ)..(L - W), normalizedLogError t ^ 2) / (L - W)) * ((L - W) / L))
      atTop (𝓝 (totalZeroEnergy * 1)) :=
    (h1.comp hshift).mul hratio
  rw [mul_one] at h2
  have hdiff := h1.sub h2
  rw [sub_self] at hdiff
  refine hdiff.congr' ?_
  filter_upwards [eventually_gt_atTop W] with L hL
  have hLW : 0 < L - W := sub_pos.mpr hL
  have hL0 : 0 < L := by linarith
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_normalizedLogError_sq 0 (L - W))
    (intervalIntegrable_normalizedLogError_sq (L - W) L)
  rw [div_mul_div_cancel₀ hLW.ne', ← sub_div, ← hadj, add_sub_cancel_left]

/-- Set-integral form of sliding-window sublinearity on `Icc (L − W) L`. -/
theorem tendsto_setIntegral_window_sq_normalizedLogError_div (hRH : RiemannHypothesis) {W : ℝ}
    (hW : 0 ≤ W) :
    Tendsto (fun L : ℝ => (∫ t in Icc (L - W) L, normalizedLogError t ^ 2) / L) atTop (𝓝 0) := by
  refine (tendsto_window_sq_normalizedLogError_div hRH hW).congr' ?_
  filter_upwards [eventually_ge_atTop W] with L _
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

/-- **Corollary 3a (Discrete Nyquist-cell mean-square limit).** Under RH, the centred discrete
Chebyshev cell sum satisfies
`lim_{M → ∞} (1 / log M) Σ_{k < M−1} (ψ(k+1) − m_{k+1})² / ((k+1)(k+2)) = Σ_ρ m_ρ² / |ρ|²`. -/
theorem tendsto_centeredCellSum_div_log (hRH : RiemannHypothesis) :
    Tendsto (fun M : ℕ =>
      (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) / Real.log (M : ℝ))
      atTop (𝓝 totalZeroEnergy) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcont := (tendsto_mean_sq_normalizedLogError hRH).comp hlog
  have hrem : Tendsto (fun M : ℕ => (2 : ℝ) / Real.log (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlo : Tendsto (fun M : ℕ =>
      (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) / Real.log (M : ℝ) -
        2 / Real.log (M : ℝ)) atTop (𝓝 totalZeroEnergy) := by
    simpa using hcont.sub hrem
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hcont ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with M hM
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
    have hup := (sum_center_sq_le_integral_le (by omega : 1 ≤ M)).2
    rw [← sub_div, div_le_div_iff_of_pos_right hlogM]
    linarith
  · filter_upwards [eventually_ge_atTop 2] with M hM
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
    have hlow := (sum_center_sq_le_integral_le (by omega : 1 ≤ M)).1
    exact div_le_div_of_nonneg_right hlow hlogM.le

/-- **Corollary 3b (Classical discrete Chebyshev mean-square limit).** Under RH,
`lim_{M → ∞} (1 / log M) Σ_{k < M−1} (ψ(k+1) − (k+1))² / ((k+1)(k+2)) = Σ_ρ m_ρ² / |ρ|²`. -/
theorem tendsto_discreteChebyshevSum_div_log (hRH : RiemannHypothesis) :
    Tendsto (fun M : ℕ =>
      (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) / Real.log (M : ℝ))
      atTop (𝓝 totalZeroEnergy) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hZ0 : 0 ≤ totalZeroEnergy := totalZeroEnergy_nonneg
  have hZ1 : 0 < totalZeroEnergy + 1 := by linarith
  set η := ε / (2 * (totalZeroEnergy + 1))
  have hη : 0 < η := by positivity
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcent := tendsto_centeredCellSum_div_log hRH
  have h1 := ((tendsto_const_nhds (x := 1 + η)).mul hcent).add
    ((tendsto_const_nhds (x := 1 + 1 / η)).div_atTop hlog)
  rw [add_zero] at h1
  have h2 := ((tendsto_const_nhds (x := 1 / (1 + η))).mul hcent).sub
    ((tendsto_const_nhds (x := 1 / η)).div_atTop hlog)
  rw [sub_zero] at h2
  have hhi_lt : (1 + η) * totalZeroEnergy < totalZeroEnergy + ε := by
    have : η * totalZeroEnergy ≤ ε / 2 := by
      simp only [η]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hlo_gt : totalZeroEnergy - ε < (1 / (1 + η)) * totalZeroEnergy := by
    rw [one_div_mul_eq_div, lt_div_iff₀ (by positivity)]
    have : totalZeroEnergy * η ≤ ε / 2 := by
      simp only [η]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith [hε]
  filter_upwards [eventually_ge_atTop 2, h1.eventually (gt_mem_nhds hhi_lt),
    h2.eventually (lt_mem_nhds hlo_gt)] with M hM hM_hi hM_lo
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  -- telescoping weight sum `Σ_{k<M−1} 1/((k+1)(k+2)) ≤ 1`
  have hweight : (∑ k ∈ Finset.range (M - 1),
      1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) ≤ 1 := by
    have h := Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 1)) (M - 1)
    have hterm : ∀ k ∈ Finset.range (M - 1),
        1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) =
          1 / ((k : ℝ) + 1) - 1 / (((k + 1 : ℕ) : ℝ) + 1) := fun k _ => by
      push_cast; field_simp; ring
    rw [Finset.sum_congr rfl hterm, h]
    simp only [Nat.cast_zero, zero_add, div_one]
    have : 0 ≤ 1 / (((M - 1 : ℕ) : ℝ) + 1) := by positivity
    linarith
  set S_class := ∑ k ∈ Finset.range (M - 1),
    (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
      (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))
  set S_cent := ∑ k ∈ Finset.range (M - 1),
    (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
      (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))
  -- two-sided `(1 ± η)` comparison between `S_class` and `S_cent`
  have hpt : ∀ k ∈ Finset.range (M - 1),
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ≤
        (1 + η) * ((Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
          (1 + 1 / η) * (1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) ∧
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ≤
        (1 + η) * ((Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
          (1 + 1 / η) * (1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) := by
    intro k _
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hd : 0 < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by positivity
    have hd1 : (cellCenter (k + 1) - ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_cellCenter_sub_le hk)
    set E := Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)
    set C := Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)
    set d := cellCenter (k + 1) - ((k + 1 : ℕ) : ℝ)
    have hEC : (-d - C) ^ 2 = E ^ 2 := by dsimp [E, C, d]; ring
    have hCE : (d - E) ^ 2 = C ^ 2 := by dsimp [E, C, d]; ring
    have hw1 := sub_sq_le_weighted hη (-d) C
    rw [neg_sq, hEC] at hw1
    have hw2 := sub_sq_le_weighted hη d E
    rw [hCE] at hw2
    have hη1 : 0 ≤ 1 + 1 / η := by positivity
    constructor
    · have hnum : E ^ 2 ≤ (1 + η) * C ^ 2 + (1 + 1 / η) * 1 :=
        hw1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd1 hη1))
      calc E ^ 2 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))
          ≤ ((1 + η) * C ^ 2 + (1 + 1 / η) * 1) /
              (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hnum hd.le
        _ = _ := by ring
    · have hnum : C ^ 2 ≤ (1 + η) * E ^ 2 + (1 + 1 / η) * 1 :=
        hw2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd1 hη1))
      calc C ^ 2 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))
          ≤ ((1 + η) * E ^ 2 + (1 + 1 / η) * 1) /
              (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hnum hd.le
        _ = _ := by ring
  have hsum1 := Finset.sum_le_sum fun k hk => (hpt k hk).1
  have hsum2 := Finset.sum_le_sum fun k hk => (hpt k hk).2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum1 hsum2
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  have hS_up : S_class ≤ (1 + η) * S_cent + (1 + 1 / η) :=
    hsum1.trans (add_le_add le_rfl (mul_le_of_le_one_right hη1 hweight))
  have hS_lo : S_cent ≤ (1 + η) * S_class + (1 + 1 / η) :=
    hsum2.trans (add_le_add le_rfl (mul_le_of_le_one_right hη1 hweight))
  have hdiv_up : S_class / Real.log (M : ℝ) ≤
      (1 + η) * (S_cent / Real.log (M : ℝ)) + (1 + 1 / η) / Real.log (M : ℝ) := by
    calc S_class / Real.log (M : ℝ)
        ≤ ((1 + η) * S_cent + (1 + 1 / η)) / Real.log (M : ℝ) :=
          div_le_div_of_nonneg_right hS_up hlogM.le
      _ = _ := by ring
  have hS_lo' : (1 / (1 + η)) * S_cent - 1 / η ≤ S_class := by
    have hη_pos : 0 < 1 + η := by positivity
    have h1 : (1 / (1 + η)) * S_cent - 1 / η = (S_cent - (1 + 1 / η)) / (1 + η) := by
      field_simp; ring
    rw [h1, div_le_iff₀ hη_pos]
    linarith [hS_lo]
  have hdiv_lo : (1 / (1 + η)) * (S_cent / Real.log (M : ℝ)) - (1 / η) / Real.log (M : ℝ) ≤
      S_class / Real.log (M : ℝ) := by
    calc (1 / (1 + η)) * (S_cent / Real.log (M : ℝ)) - (1 / η) / Real.log (M : ℝ)
        = ((1 / (1 + η)) * S_cent - 1 / η) / Real.log (M : ℝ) := by ring
      _ ≤ S_class / Real.log (M : ℝ) := div_le_div_of_nonneg_right hS_lo' hlogM.le
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hM_lo, hM_hi, hdiv_lo, hdiv_up]

/-- **Corollary 4 (Sharp asymptotic band slope).** A slope `C` is an asymptotic linear band slope
if `∫_0^L Ẽ(t)² dt ≤ C L + K` for all `L ≥ 0` and some `K ≥ 0`. -/
def IsAsymptoticBandSlope (C : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * L + K

/-- Under RH, every `C > totalZeroEnergy` is an asymptotic linear band slope. -/
theorem isAsymptoticBandSlope_of_gt (hRH : RiemannHypothesis) {C : ℝ} (hC : totalZeroEnergy < C) :
    IsAsymptoticBandSlope C := by
  have hε : 0 < C - totalZeroEnergy := sub_pos.mpr hC
  obtain ⟨L₀, hL₀⟩ := (eventually_atTop.mp (cramer_limsup_law_zeroEnergy hRH hε))
  set M₀ := max L₀ 1
  have hM₀ : 0 ≤ M₀ := by positivity
  refine ⟨∫ t in Icc 0 M₀, normalizedLogError t ^ 2,
    setIntegral_nonneg measurableSet_Icc (fun _ _ => sq_nonneg _), fun L hL => ?_⟩
  rcases le_or_gt L M₀ with hle | hgt
  · have hmono := integral_normalizedLogError_sq_mono hle
    have hC0 : 0 ≤ C * L := mul_nonneg (totalZeroEnergy_nonneg.trans hC.le) hL
    linarith
  · have hL_ge : L₀ ≤ L := (le_max_left L₀ 1).trans hgt.le
    have hL_pos : 0 < L := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ M₀) hgt
    have hbound := (div_le_iff₀ hL_pos).mp (hL₀ L hL_ge)
    have hK0 : 0 ≤ ∫ t in Icc 0 M₀, normalizedLogError t ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
    linarith

/-- Under RH, every asymptotic linear band slope is at least `totalZeroEnergy`. -/
theorem totalZeroEnergy_le_of_isAsymptoticBandSlope (hRH : RiemannHypothesis) {C : ℝ}
    (hC : IsAsymptoticBandSlope C) : totalZeroEnergy ≤ C := by
  obtain ⟨K, _, hK⟩ := hC
  by_contra hlt
  rw [not_le] at hlt
  set ε := (totalZeroEnergy - C) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hrem : ∀ᶠ L : ℝ in atTop, K / L < ε :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hε)
  obtain ⟨L, hL0, hlo, hKL⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and
      ((cramer_liminf_law_zeroEnergy hRH hε).and hrem)).exists
  have hup : (∫ t in Icc 0 L, normalizedLogError t ^ 2) / L ≤ C + K / L := by
    have := div_le_div_of_nonneg_right (hK L hL0.le) hL0.le
    rwa [add_div, mul_div_cancel_right₀ C hL0.ne'] at this
  change totalZeroEnergy - ε ≤ _ at hlo
  simp only [ε] at hlo hKL
  linarith

/-- **Characterization of the minimal asymptotic band slope:** under RH, `totalZeroEnergy` is the
greatest lower bound of all valid linear band slopes. -/
theorem isGLB_asymptoticBandSlope_zeroEnergy (hRH : RiemannHypothesis) :
    IsGLB {C : ℝ | IsAsymptoticBandSlope C} totalZeroEnergy := by
  refine ⟨fun C hC => totalZeroEnergy_le_of_isAsymptoticBandSlope hRH hC, fun b hb => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hmid : totalZeroEnergy < (totalZeroEnergy + b) / 2 := by linarith
  have hle := hb (isAsymptoticBandSlope_of_gt hRH hmid)
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
