import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalPrimeChannelUniformBound
import GaloisForLFunctions.«arithmetic-positivity-theory».CollaredCriticalCompleteFormPositivity

/-!
# Positive definiteness of the complete critical form on high dyadic blocks

The complete critical energy of a critical source `g_b` in Gamma–Lévy form is
`E_crit(g_b) = Lévy(g_b) + Ω(0) ac(0) + 2 R E - 2 P`. Its channels on a dyadic block
`M ≤ n + 1 ≤ 2M` have the following sizes:

* **archimedean:** `Lévy(g_b) ≥ s (log M - c₀) ∑ b_n²`, the logarithmic coercivity of critical
  sources;
* **Gamma:** `ac(0) = ∫_{v>1} v^{-2} B_b² ≤ (π²/6) J ∑ b_n²`, from unit windows;
* **polar:** `|R E| ≤ 576 (∑ |b_n|/(n+1))² ≤ 576 ∑ b_n²`;
* **prime:** `|P| ≤ C_P ∑ b_n²`, the `ℓ²`-uniform critical prime channel.

Every channel except the archimedean one is therefore `ℓ²`-bounded, and the archimedean one grows
like `log M` on `ℓ²`. So there is an absolute scale `M₀` beyond which the complete critical form is
positive definite on every dyadic block, for every number and every position of the atoms. In
particular every nonzero pattern with offsets at most `n`, translated to a scale `n ≥ M₀`, has
positive complete critical energy, with no bound on the size of the pattern.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
open _root_.Zeta23

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- **`ℓ²` ceiling of the critical mass.** `ac(0) = ∫ g_b² ≤ U ∑ b_n²`. -/
theorem criticalAutocorrelation_zero_le_sq (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalAutocorrelation S b 0 ≤ criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
  have h := criticalFactorialSource_correlation_eq S b (r := 1) le_rfl
  simp only [Real.log_one, sub_zero, Real.sqrt_one, inv_one, one_mul] at h
  have hup := integral_Ioi_one_rpow_neg_two_mul_norm_sq_le S (fun n => (b n : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hup
  unfold criticalAutocorrelation
  rw [show (fun y => criticalFactorialSource S b y * criticalFactorialSource S b (y - 0)) =
    fun y => criticalFactorialSource S b y * criticalFactorialSource S b y by simp, h]
  refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_) hup
  have hre : ‖factorialPhaseCombination S (fun n => (b n : ℂ)) v‖ ^ 2 =
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re ^ 2 := by
    have h' : (((factorialPhaseCombination S (fun n => (b n : ℂ)) v).re : ℝ) : ℂ) =
        factorialPhaseCombination S (fun n => (b n : ℂ)) v := factorialPhaseCombination_ofReal_re S b v
    rw [← h', Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_re]
  rw [hre]
  ring

/-- Channel constant `K = |Ω(0)| U + 1152 + 2 C_P` of the complete critical form. -/
def criticalCompleteChannelConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper + 1152 + 2 * criticalPrimeChannelConstant

/-- **`ℓ²` channel bound.** On a dyadic block (`M ≥ 2`) the Gamma, polar and prime channels of the
complete critical form cost at most `K ∑ b_n²`. -/
theorem neg_le_criticalArithmeticChannels_sq (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) :
    -(criticalCompleteChannelConstant * ∑ n ∈ S, b n ^ 2) ≤ criticalArithmeticChannels S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hac0 : 0 ≤ criticalAutocorrelation S b 0 := by
    unfold criticalAutocorrelation
    simp only [sub_zero]
    exact integral_nonneg fun y => mul_self_nonneg _
  have hac := criticalAutocorrelation_zero_le_sq S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤
      EF.gammaBracket 0 * criticalAutocorrelation S b 0 := by
    have h1 := neg_abs_le (EF.gammaBracket 0 * criticalAutocorrelation S b 0)
    rw [abs_mul, abs_of_nonneg hac0] at h1
    nlinarith [abs_nonneg (EF.gammaBracket 0)]
  have hT2 : T ^ 2 ≤ E := (sq_sum_abs_div_succ_le S b hM fun n hn => (hS n hn).1).trans (by
    have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM2
    nlinarith)
  have hpol : |criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b| ≤ 576 * E := by
    rw [abs_mul]
    calc _ ≤ (24 * T) * (24 * T) := mul_le_mul (abs_criticalFactorialPolarReadout_le S b)
          (criticalFactorialPolarEndpoint_bound S b) (abs_nonneg _) (by positivity)
      _ = 576 * T ^ 2 := by ring
      _ ≤ 576 * E := by linarith
  have hpr := abs_criticalPrimeEnergy_le_of_dyadic (by omega) hS b
  have h2 := neg_abs_le (criticalFactorialPolarReadout S b * criticalFactorialPolarEndpoint S b)
  have h3 := le_abs_self (criticalPrimeEnergy S b)
  unfold criticalArithmeticChannels criticalCompleteChannelConstant
  nlinarith

/-- **Complete critical form on dyadic blocks.** For every family on a dyadic block `[M, 2M]`
(`M ≥ 2`) and every real coefficient vector, `E_crit(g_b) ≥ (s (log M - c₀) - K) ∑ b_n²`. -/
theorem criticalCompleteEnergy_ge_of_dyadic (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) :
    (((criticalArchLogSlope * (Real.log M - criticalArchLogOffset) -
        criticalCompleteChannelConstant) * ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalCompleteEnergy S b := by
  set E := ∑ n ∈ S, b n ^ 2
  set X := criticalArchLogSlope * (Real.log M - criticalArchLogOffset) * E
  have hlev : (X : EReal) ≤ (criticalLevyEnergy S b : EReal) := by
    have h1 := ofReal_le_criticalLevyEnergy S b hM fun n hn => (hS n hn).1
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalArithmeticChannels_sq S b hM hS
  unfold criticalCompleteEnergy
  rw [show (criticalArchLogSlope * (Real.log M - criticalArchLogOffset) -
      criticalCompleteChannelConstant) * E = X + -(criticalCompleteChannelConstant * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Positive definiteness of the complete critical form on high dyadic blocks.** There is a
scale `M₀` such that for every `M ≥ M₀`, every family on the dyadic block `[M, 2M]` and every
nonzero real coefficient vector, the complete critical energy is strictly positive — with no
restriction on the number or positions of the atoms. -/
theorem exists_criticalCompleteEnergy_pos :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ S : Finset ℕ, DyadicScaleBlock S M → ∀ b : ℕ → ℝ,
      (∃ n ∈ S, b n ≠ 0) → 0 < criticalCompleteEnergy S b := by
  have hs := criticalArchLogSlope_pos
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (criticalArchLogOffset + criticalCompleteChannelConstant / criticalArchLogSlope)).and
      (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hgap : 0 < criticalArchLogSlope * (Real.log M - criticalArchLogOffset) -
      criticalCompleteChannelConstant := by
    have h1 : criticalCompleteChannelConstant / criticalArchLogSlope <
        Real.log M - criticalArchLogOffset := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    linarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap hE)) (criticalCompleteEnergy_ge_of_dyadic S b hM2 hS)

/-- **Translated patterns of any size.** Beyond an absolute scale `N₀`, every nonzero pattern
whose offsets are at most `n`, translated to scale `n`, has strictly positive complete critical
energy; no bound on the number of atoms is needed. -/
theorem exists_criticalTranslatedCompleteEnergy_pos :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ S : Finset ℕ, (∀ j ∈ S, j ≤ n) → ∀ b : ℕ → ℝ,
      (∃ j ∈ S, b j ≠ 0) → 0 < criticalTranslatedCompleteEnergy S b n := by
  obtain ⟨M₀, hM₀⟩ := exists_criticalCompleteEnergy_pos
  refine ⟨M₀, fun n hn S hS b hb => ?_⟩
  rw [criticalTranslatedCompleteEnergy_eq]
  refine hM₀ (n + 1) (by omega) _ (fun q hq => ?_) _ ?_
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have := hS j hj
    constructor <;> omega
  · obtain ⟨j, hj, hbj⟩ := hb
    exact ⟨n + j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, by simpa using hbj⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
