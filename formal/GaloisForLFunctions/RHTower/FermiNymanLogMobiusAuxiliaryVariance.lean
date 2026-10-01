import GaloisForLFunctions.RHTower.FermiNymanFiniteCoefficientError
import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The canonical logarithmic Fermi error controls an exact arithmetic variance

The auxiliary Nyman error equals `[B_N/t - ψ(1/t)]/log N` beyond `1/(N+1)`.
Reciprocal change of variables identifies its squared tail norm with
`(log N)⁻² ∫_(0,N+1) (B_N - ψ(x)/x)² dx`. Source integrability is established
independently before this identity. Full-half-line coercivity transfers it to the
literal canonical Fermi error.

The variance splits exactly into `(N+1)(B_N-m_N)²` and the intrinsic variance of
`ψ(x)/x` around its mean `m_N`. Both nonnegative terms receive separate canonical
error bounds. The unconditional scalar limit `B_N → 1` supplies no rate for either
term; no canonical convergence or RH conclusion is asserted here.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
noncomputable section
namespace RHTower

/-- The actual logarithmically weighted harmonic Möbius sum. -/
def logMobiusHarmonicSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) *
    Real.log ((N : ℝ) / d)

/-- Literal logarithmic coefficients in the auxiliary finite Nyman error. -/
def logMobiusNymanError (N : ℕ) : ℝ → ℂ :=
  finiteNymanError N (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    Real.log ((N : ℝ) / d) / Real.log N)

theorem tendsto_logMobiusHarmonicSum_one :
    Tendsto logMobiusHarmonicSum atTop (𝓝 1) := Sieve.tendsto_sum_moebius_log_div_one

theorem sum_logMobius_nymanGen (N : ℕ) (t : ℝ) :
    (∑ d ∈ Finset.Icc 1 N,
      ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) /
        Real.log N : ℝ) : ℂ) * nymanGen (d : ℝ) t) =
      (((logMobiusHarmonicSum N / t - ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) *
          (⌊(1 / t) / d⌋ : ℝ)) / Real.log N : ℝ) : ℂ) := by
  rw [logMobiusHarmonicSum, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  unfold nymanGen Int.fract
  rw [show 1 / ((d : ℝ) * t) = (1 / t) / d by ring]
  push_cast
  ring

/-- Finite floor inversion identifies the auxiliary error beyond the literal cutoff. -/
theorem logMobiusNymanError_eq_chebyshev (N : ℕ) (hN : 2 ≤ N) {t : ℝ}
    (ht : 1 / ((N : ℝ) + 1) < t) :
    logMobiusNymanError N t =
      (((logMobiusHarmonicSum N / t - Chebyshev.psi (1 / t)) / Real.log N : ℝ) : ℂ) := by
  have hNp : (0 : ℝ) < N + 1 := by positivity
  have ht0 : 0 < t := lt_trans (one_div_pos.mpr hNp) ht
  have hx : 0 ≤ 1 / t := by positivity
  have hxN : 1 / t < (N : ℝ) + 1 := by
    apply (div_lt_iff₀ ht0).mpr
    have h := (div_lt_iff₀ hNp).mp ht
    nlinarith
  have hfloor : ⌊1 / t⌋₊ ≤ N := by
    have h : (⌊1 / t⌋₊ : ℝ) < (N : ℝ) + 1 := lt_of_le_of_lt (Nat.floor_le hx) hxN
    exact Nat.le_of_lt_succ (by exact_mod_cast h)
  have hlogR : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlog : (Real.log (N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogR.ne'
  rw [logMobiusNymanError, finiteNymanError, sum_logMobius_nymanGen,
    sum_moebius_log_div_mul_floor N (by omega) hx hfloor]
  by_cases ht1 : t ≤ 1
  · have hx1 : 1 ≤ 1 / t := (le_div_iff₀ ht0).mpr (by simpa using ht1)
    rw [if_pos hx1, indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1⟩)]
    push_cast at hlog ⊢
    field_simp
    ring
  · have hx1 : ¬1 ≤ 1 / t := by
      rw [le_div_iff₀ ht0]
      simpa using ht1
    rw [if_neg hx1, indicator_of_notMem (fun h => ht1 h.2)]
    simp

theorem measurable_logMobiusNymanError (N : ℕ) : Measurable (logMobiusNymanError N) :=
  measurable_finiteNymanError N _

theorem integrableOn_normSq_logMobiusNymanError (N : ℕ) :
    IntegrableOn (fun t => ‖logMobiusNymanError N t‖ ^ 2) (Ioi (0 : ℝ)) :=
  integrableOn_normSq_finiteNymanError N _

theorem integral_normSq_logMobiusNymanError_le_six (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖logMobiusNymanError N t‖ ^ 2) ≤
      6 * logMobiusFermiErrorEnergy N := by
  simpa only [logMobiusNymanError, logMobiusFermiErrorEnergy, logMobiusFermiApprox,
    sub_neg_eq_add] using integral_normSq_finiteNymanError_le_six N
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) / Real.log N)

/-- The prime profile is bounded even at the open zero endpoint. -/
theorem abs_sub_psi_div_le (B : ℝ) {x : ℝ} (hx : 0 < x) :
    |B - Chebyshev.psi x / x| ≤ |B| + (Real.log 4 + 4) := by
  have hψ0 : 0 ≤ Chebyshev.psi x / x := div_nonneg (Chebyshev.psi_nonneg _) hx.le
  calc
    _ ≤ |B| + |Chebyshev.psi x / x| := by simpa only [Real.norm_eq_abs] using norm_sub_le B (Chebyshev.psi x / x)
    _ ≤ _ := by
      rw [abs_of_nonneg hψ0]
      exact add_le_add le_rfl ((div_le_iff₀ hx).mpr (Chebyshev.psi_le_const_mul_self hx.le))

theorem integrableOn_sq_sub_psi_div (B R : ℝ) :
    IntegrableOn (fun x : ℝ => (B - Chebyshev.psi x / x) ^ 2) (Ioo 0 R) := by
  refine Measure.integrableOn_of_bounded (M := (|B| + (Real.log 4 + 4)) ^ 2)
    measure_Ioo_lt_top.ne
    ((measurable_const.sub (Chebyshev.psi_mono.measurable.div measurable_id)).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_psi_div_le B hx.1) 2

theorem image_inv_Ioo_zero (R : ℝ) (hR : 0 < R) :
    (fun x : ℝ => x⁻¹) '' Ioo 0 R = Ioi R⁻¹ := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (inv_lt_inv₀ hR hx.1).mpr hx.2
  · intro ht
    have ht0 : 0 < t := lt_trans (inv_pos.mpr hR) ht
    refine ⟨t⁻¹, ⟨inv_pos.mpr ht0, ?_⟩, inv_inv t⟩
    simpa only [inv_inv] using (inv_lt_inv₀ ht0 (inv_pos.mpr hR)).mpr ht

/-- The exact finite arithmetic variance carried by the auxiliary reciprocal tail. -/
def logMobiusChebyshevVariance (N : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) ((N : ℝ) + 1), (logMobiusHarmonicSum N - Chebyshev.psi x / x) ^ 2

theorem logMobiusChebyshevVariance_nonneg (N : ℕ) : 0 ≤ logMobiusChebyshevVariance N :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem integral_normSq_logMobiusNymanError_tail (N : ℕ) (hN : 2 ≤ N) :
    (∫ t in Ioi (1 / ((N : ℝ) + 1)), ‖logMobiusNymanError N t‖ ^ 2) =
      logMobiusChebyshevVariance N / Real.log N ^ 2 := by
  have hR : (0 : ℝ) < N + 1 := by positivity
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x (hx : x ∈ Ioo (0 : ℝ) ((N : ℝ) + 1)) =>
      (hasDerivAt_inv hx.1.ne').hasDerivWithinAt)
    (inv_injective.injOn) (fun t : ℝ => ‖logMobiusNymanError N t‖ ^ 2)
  rw [image_inv_Ioo_zero _ hR] at hj
  rw [one_div, hj, logMobiusChebyshevVariance, ← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hcut : 1 / ((N : ℝ) + 1) < x⁻¹ := by
    simpa only [one_div] using (inv_lt_inv₀ hR hx.1).mpr hx.2
  have hx0 : x ≠ 0 := hx.1.ne'
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  dsimp
  rw [logMobiusNymanError_eq_chebyshev N hN hcut,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_neg, abs_inv, abs_sq]
  simp only [one_div, inv_inv]
  field_simp

/-- Canonical error must control this normalized finite prime/Möbius variance. -/
theorem logMobiusChebyshevVariance_le_six_error (N : ℕ) (hN : 2 ≤ N) :
    logMobiusChebyshevVariance N / Real.log N ^ 2 ≤ 6 * logMobiusFermiErrorEnergy N := by
  rw [← integral_normSq_logMobiusNymanError_tail N hN]
  refine le_trans ?_ (integral_normSq_logMobiusNymanError_le_six N)
  apply setIntegral_mono_set (integrableOn_normSq_logMobiusNymanError N)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  exact Filter.Eventually.of_forall (fun t ht => lt_trans (by positivity) ht)

/-- Every scalar translate of the prime profile is integrable on a finite source interval. -/
theorem integrableOn_sub_psi_div (B R : ℝ) :
    IntegrableOn (fun x : ℝ => B - Chebyshev.psi x / x) (Ioo 0 R) := by
  refine Measure.integrableOn_of_bounded (M := |B| + (Real.log 4 + 4))
    measure_Ioo_lt_top.ne
    (measurable_const.sub (Chebyshev.psi_mono.measurable.div measurable_id)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact abs_sub_psi_div_le B hx.1

/-- The exact mean prime profile at the same cutoff as the Möbius approximation. -/
def chebyshevProfileMean (N : ℕ) : ℝ :=
  (∫ x in Ioo (0 : ℝ) ((N : ℝ) + 1), Chebyshev.psi x / x) / ((N : ℝ) + 1)

/-- Intrinsic prime-profile fluctuations, with no Möbius coefficient in their definition. -/
def chebyshevProfileVariance (N : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) ((N : ℝ) + 1),
    (chebyshevProfileMean N - Chebyshev.psi x / x) ^ 2

theorem chebyshevProfileVariance_nonneg (N : ℕ) : 0 ≤ chebyshevProfileVariance N :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem integral_sub_chebyshevProfileMean (N : ℕ) :
    (∫ x in Ioo (0 : ℝ) ((N : ℝ) + 1), chebyshevProfileMean N - Chebyshev.psi x / x) = 0 := by
  have hR : (0 : ℝ) < N + 1 := by positivity
  have hf : IntegrableOn (fun x : ℝ => Chebyshev.psi x / x) (Ioo 0 ((N : ℝ) + 1)) := by
    simpa using (integrableOn_sub_psi_div 0 ((N : ℝ) + 1)).neg
  have hc : IntegrableOn (fun _ : ℝ => chebyshevProfileMean N)
      (Ioo 0 ((N : ℝ) + 1)) := integrableOn_const measure_Ioo_lt_top.ne
  rw [integral_sub hc hf, setIntegral_const,
    Real.volume_real_Ioo_of_le hR.le, sub_zero, smul_eq_mul, chebyshevProfileMean]
  field_simp
  ring

/-- Exact separation of scalar normalization error from intrinsic prime fluctuations. -/
theorem logMobiusChebyshevVariance_decomposition (N : ℕ) :
    logMobiusChebyshevVariance N =
      ((N : ℝ) + 1) * (logMobiusHarmonicSum N - chebyshevProfileMean N) ^ 2 +
        chebyshevProfileVariance N := by
  have hR : (0 : ℝ) < N + 1 := by positivity
  have hi := integrableOn_sq_sub_psi_div (chebyshevProfileMean N) ((N : ℝ) + 1)
  have hl := integrableOn_sub_psi_div (chebyshevProfileMean N) ((N : ℝ) + 1)
  have hc : IntegrableOn (fun _ : ℝ => (logMobiusHarmonicSum N - chebyshevProfileMean N) ^ 2)
      (Ioo 0 ((N : ℝ) + 1)) := integrableOn_const measure_Ioo_lt_top.ne
  have his : IntegrableOn (fun x : ℝ =>
      (chebyshevProfileMean N - Chebyshev.psi x / x) ^ 2 +
        (logMobiusHarmonicSum N - chebyshevProfileMean N) ^ 2)
      (Ioo 0 ((N : ℝ) + 1)) := hi.add hc
  rw [logMobiusChebyshevVariance]
  calc
    _ = ∫ x in Ioo (0 : ℝ) ((N : ℝ) + 1),
        (chebyshevProfileMean N - Chebyshev.psi x / x) ^ 2 +
        (logMobiusHarmonicSum N - chebyshevProfileMean N) ^ 2 +
        (2 * (logMobiusHarmonicSum N - chebyshevProfileMean N)) *
          (chebyshevProfileMean N - Chebyshev.psi x / x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x _
      dsimp
      ring
    _ = _ := by
      rw [integral_add his (hl.const_mul _), integral_add hi hc,
        integral_const_mul, integral_sub_chebyshevProfileMean,
        mul_zero, add_zero, setIntegral_const, Real.volume_real_Ioo_of_le hR.le,
        sub_zero, smul_eq_mul]
      exact add_comm _ _

theorem logMobiusNormalizationBudget_le_six_error (N : ℕ) (hN : 2 ≤ N) :
    (((N : ℝ) + 1) * (logMobiusHarmonicSum N - chebyshevProfileMean N) ^ 2) /
      Real.log N ^ 2 ≤ 6 * logMobiusFermiErrorEnergy N := by
  refine le_trans ?_ (logMobiusChebyshevVariance_le_six_error N hN)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [logMobiusChebyshevVariance_decomposition]
  exact le_add_of_nonneg_right (chebyshevProfileVariance_nonneg N)

theorem chebyshevProfileVarianceBudget_le_six_error (N : ℕ) (hN : 2 ≤ N) :
    chebyshevProfileVariance N / Real.log N ^ 2 ≤ 6 * logMobiusFermiErrorEnergy N := by
  refine le_trans ?_ (logMobiusChebyshevVariance_le_six_error N hN)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [logMobiusChebyshevVariance_decomposition]
  exact le_add_of_nonneg_left (by positivity)

end RHTower
