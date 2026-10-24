import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalPolePairing
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalWeilNormalization
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalKernelContinuity

/-!
# The finite arithmetic assembly at the critical Suzuki shift

Compact correlation support supplies one common arithmetic cutoff. Translation
at each logarithmic cusp then differentiates only a finite sum. Every nonunit
Euler coefficient contributes its exact tangent `2 Λ(n)`.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators
open GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

/-- The literal full arithmetic source paired with a compact autocorrelation. -/
def suzukiCriticalSourcePairing (f : ℝ → ℝ) (omega : ℝ) : ℝ :=
  ∫ t in Ioi 0, autocorr f t *
    (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re)

/-- Compact autocorrelation support supplies a positive common aperture. -/
theorem exists_suzukiCriticalCorrelation_cutoff {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, A ≤ t → autocorr f t = 0 := by
  obtain ⟨R, hR⟩ := (hasCompactSupport_autocorr hfc).bddAbove
  refine ⟨|R| + 1, by positivity, ?_⟩
  intro t ht
  by_contra hz
  have hs : t ∈ tsupport (autocorr f) := subset_closure (Function.mem_support.mpr hz)
  have hle := hR hs
  linarith [le_abs_self R]

private theorem sourceDensity_zero {omega t : ℝ} (ht : t ≤ 0) :
    suzukiCriticalSourceDensity omega t = 0 := by
  unfold suzukiCriticalSourceDensity suzukiSourceG
  have he : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (by linarith)
  rw [if_neg (fun h => (not_lt_of_ge he) h.2)]
  simp

private theorem integrable_sourceCusp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {omega u : ℝ} (homega : 0 < omega)
    (homega5 : omega < 5 / 2) (hu : 0 ≤ u) :
    IntegrableOn (fun t => autocorr f (u + t) * suzukiCriticalSourceDensity omega t) (Ioi 0) := by
  obtain ⟨A, hA, hcut⟩ := exists_suzukiCriticalCorrelation_cutoff hfc
  have hB := integrableOn_suzukiCriticalPrimaryCusp_integrand hf hfc homega homega5 u
  have hP := integrableOn_suzukiCriticalPoleCusp_integrand hf hfc hA hu hcut homega homega5
  apply (hB.sub (hP.const_mul (2 * omega))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t -
    2 * omega * (autocorr f (u + t) * suzukiCriticalPoleDensity omega t) = _
  rw [suzukiCriticalSourceDensity_eq omega ht]
  ring

private theorem integrable_sourceCusp_full {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {omega u : ℝ} (homega : 0 < omega)
    (homega5 : omega < 5 / 2) (hu : 0 ≤ u) :
    Integrable (fun t => autocorr f (u + t) * suzukiCriticalSourceDensity omega t) := by
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrable_sourceCusp hf hfc homega homega5 hu)
  apply hi.congr
  filter_upwards with t
  by_cases ht : 0 < t
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht, sourceDensity_zero (le_of_not_gt ht), mul_zero]

private theorem integrable_shifted_source {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {omega u : ℝ} (homega : 0 < omega)
    (homega5 : omega < 5 / 2) (hu : 0 ≤ u) :
    IntegrableOn (fun t => autocorr f t * suzukiCriticalSourceDensity omega (t - u)) (Ioi 0) := by
  have hi := (integrable_sourceCusp_full hf hfc homega homega5 hu).comp_add_left (-u)
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro t _
  change autocorr f (u + (-u + t)) * suzukiCriticalSourceDensity omega (-u + t) = _
  rw [show u + (-u + t) = t by ring, show -u + t = t - u by ring]

private theorem shifted_source_integral {f : ℝ → ℝ} {omega u : ℝ} (hu : 0 ≤ u) :
    (∫ t in Ioi 0, autocorr f t * suzukiCriticalSourceDensity omega (t - u)) =
      suzukiCriticalSourceCusp f omega u := by
  have hleft : (∫ t in Ioi 0, autocorr f t * suzukiCriticalSourceDensity omega (t - u)) =
      ∫ t, autocorr f t * suzukiCriticalSourceDensity omega (t - u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht0 : t ≤ 0 := le_of_not_gt ht
    rw [sourceDensity_zero (by linarith : t - u ≤ 0), mul_zero]
  have hright : (∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalSourceDensity omega t) =
      ∫ t, autocorr f (u + t) * suzukiCriticalSourceDensity omega t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [sourceDensity_zero (le_of_not_gt ht), mul_zero]
  rw [hleft, suzukiCriticalSourceCusp, hright,
    ← integral_add_left_eq_self (fun t => autocorr f t *
      suzukiCriticalSourceDensity omega (t - u)) u]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only
  rw [add_sub_cancel_left]

private theorem source_log_atom (omega t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-t / 2) * (suzukiSourceG omega (n / Real.exp t)).re =
      Real.exp (-Real.log n / 2) * suzukiCriticalSourceDensity omega (t - Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (n : ℝ) / Real.exp t = Real.exp (-(t - Real.log n)) := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hn0]
  have he : Real.exp (-Real.log n / 2) * Real.exp (-(t - Real.log n) / 2) =
      Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hx, suzukiCriticalSourceDensity, ← mul_assoc, he]

private theorem source_pairing_integrand {f : ℝ → ℝ} {A : ℝ}
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) (omega t : ℝ) :
    autocorr f t * (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          (autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n)) := by
  by_cases ht : A ≤ t
  · simp only [hcut t ht, zero_mul, mul_zero, Finset.sum_const_zero]
  · have hN : ⌊Real.exp t⌋₊ ≤ ⌊Real.exp A⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.mpr (le_of_not_ge ht))
    rw [suzukiSourceHFinite_eq_fixedSum (Real.exp_pos t) hN]
    rw [show (1 / (Real.exp t : ℂ)) = ((1 / Real.exp t : ℝ) : ℂ) by push_cast; rfl]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.re_sum]
    rw [← mul_assoc (Real.exp (t / 2)), mul_one_div, ← Real.exp_sub,
      show t / 2 - t = -t / 2 by ring]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only
    have he := source_log_atom omega t (Finset.mem_Icc.mp hn).1
    linear_combination autocorr f t * suzukiShiftedCoefficient omega n * he

/-- The literal arithmetic pairing is an absolutely integrable compact test. -/
theorem integrableOn_suzukiCriticalSourcePairing {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {omega : ℝ} (homega : 0 < omega)
    (homega5 : omega < 5 / 2) :
    IntegrableOn (fun t => autocorr f t *
      (Real.exp (t / 2) * (suzukiSourceHFinite omega (Real.exp t)).re)) (Ioi 0) := by
  obtain ⟨A, _hA, hcut⟩ := exists_suzukiCriticalCorrelation_cutoff hfc
  have hi : IntegrableOn (fun t => ∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        (autocorr f t * suzukiCriticalSourceDensity omega (t - Real.log n))) (Ioi 0) := by
    apply integrable_finsetSum
    intro n hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    exact (integrable_shifted_source hf hfc homega homega5 hlog).const_mul _
  exact hi.congr (Eventually.of_forall fun t => (source_pairing_integrand hcut omega t).symm)

/-- A single common cutoff represents the tested literal arithmetic source exactly. -/
theorem suzukiCriticalSourcePairing_eq_finite {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {A omega : ℝ} (_hA : 0 < A)
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) (homega : 0 < omega)
    (homega5 : omega < 5 / 2) :
    suzukiCriticalSourcePairing f omega =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n) := by
  have hlog {n : ℕ} (hn : n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊) : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  rw [suzukiCriticalSourcePairing]
  simp_rw [source_pairing_integrand hcut]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul, shifted_source_integral (hlog hn)]
  · intro n hn
    exact (integrable_shifted_source hf hfc homega homega5 (hlog hn)).const_mul _

private theorem coefficient_zero {n : ℕ} (hn : 2 ≤ n) :
    suzukiShiftedCoefficient 0 n = 0 := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  rw [suzukiShiftedCoefficient,
    Finset.prod_eq_zero hp (by simp : 1 - (p : ℝ) ^ (-2 * (0 : ℝ)) = 0)]
  simp

private theorem coefficient_tangent {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun omega : ℝ => suzukiShiftedCoefficient omega n / omega) (𝓝[>] 0)
      (𝓝 (2 * ArithmeticFunction.vonMangoldt n)) := by
  simpa only [zero_add, coefficient_zero hn, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_suzukiShiftedCoefficient (by omega : 1 ≤ n)).tendsto_slope_zero_right

/-- The complete literal source has a finite-aperture first variation, with every prime-power
cusp retained and with no sign or asymptotic arithmetic premise. -/
theorem tendsto_suzukiCriticalSourcePairing_firstVariation_finite {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {A : ℝ} (hA : 0 < A)
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) :
    Tendsto (fun omega : ℝ =>
      (autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega) (𝓝[>] 0)
      (𝓝 (-(((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) -
        2 * ∫ t in Ioi 0, Real.exp (t / 2) * autocorr f t) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr f (Real.log n))) := by
  have hfinite : Tendsto (fun omega : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n)) (𝓝[>] 0)
      (𝓝 (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr f (Real.log n))) := by
    apply tendsto_finset_sum
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact ((coefficient_tangent hn2).mul_const _).mul
      (tendsto_suzukiCriticalSourceCusp hf hfc hlog)
  have hl := (tendsto_suzukiCriticalSourceCusp_firstVariation hf hfc).neg.sub hfinite
  apply hl.congr'
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  change 0 < omega at homega
  have hN : 1 ≤ ⌊Real.exp A⌋₊ := by
    simpa using Nat.floor_mono (Real.one_le_exp_iff.mpr hA.le)
  have hsplit : (∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n)) =
      (suzukiShiftedCoefficient omega 1 * Real.exp (-Real.log 1 / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log 1) +
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n) := by
    have hset : Finset.Icc 1 ⌊Real.exp A⌋₊ = insert 1 (Finset.Icc 2 ⌊Real.exp A⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp)]
  have hunit : (suzukiShiftedCoefficient omega 1 * Real.exp (-Real.log 1 / 2)) *
      suzukiCriticalSourceCusp f omega (Real.log 1) = suzukiCriticalSourceCusp f omega 0 := by
    simp [suzukiShiftedCoefficient]
  have hdiv : (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log n)) =
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)) / omega := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hdiv, suzukiCriticalSourcePairing_eq_finite hf hfc hA hcut homega (by linarith),
    hsplit, hunit]
  ring

end
end RHTower
