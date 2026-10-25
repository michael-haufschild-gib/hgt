import GaloisForLFunctions.SignedSuccessorArithmetic.TheHalfDampingBorderlineSplitsBySign
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanDilationProfileResidueGapBudget
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLogPower
import GaloisForLFunctions.HTGeometry.FourierTailSup
import GaloisForLFunctions.HTGeometry.NearZeroTruncatedPower

/-!
# The signed prime-divisor endpoint at half damping (`ε = 1/2`, `σ = 1`)

Below half damping (`-1/2 ≤ ε < 1/2`), `TheHypercubeDirichletFormIsUnbounded` proves that the
prime-divisor Möbius hypercube form

  `Q_ε(P) = ∑_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{-1/2-ε} Φ_r(d₁ / d₂)`

is unbounded over squarefree `P`. At the critical-strip boundary `ε = 1/2` (`σ = 1`),
`TheHalfDampingBorderlineSplitsBySign` established cutoff-uniform boundedness for the size-truncated
Möbius form `sizeHypercubeForm hr (1/2) D` and logarithmic divergence to `+∞` for the prime-divisor
`+1` parity twin along `roughPrimeProd r X = ∏_{r < p ≤ X} p`, leaving the signed prime-divisor
form `Q_{1/2}(P)` itself open.

This module resolves both structured and selective prime-divisor regimes at `ε = 1/2`
unconditionally for every Ramanujan modulus `r > 1`:

1. **Essential boundedness and dyadic decay of the Mellin spectral weight `stepSpectralWeight hr`:**
   * The half-density pullback of `pmRamanujanStepSource r` vanishes on `(-∞, 0)` and is bounded by
     `pmRamanujanPrimitiveBound r · e^{-x/2}` on `(0, ∞)`, hence has `L¹(ℝ)` mass at most
     `2 · pmRamanujanPrimitiveBound r`. Consequently `stepSpectralWeight hr ξ ≤ 4 B_r²` almost
     everywhere (`stepSpectralWeight_ae_le`).
   * Testing the spectral representation `Φ_r(1) - Φ_r(c) = ∫ W_r(ξ) (1 - cos(2πξ log c)) dξ` at
     rational scales `c = (N + 1) / N` with `N = 3 · 2^k` against
     `ramanujanDilationProfile_defect_le_gap_budget` forces `cos(2πξ log c) ≤ 0` across the entire
     dyadic shell `2^k ≤ |ξ| ≤ 2^{k+1}`, yielding explicit `O((k + 5) / 2^k)` shell decay
     (`stepSpectralWeight_dyadic_shell_le`), `L¹` integrability against `(1 + |ξ|)^{1/4}` and all
     logarithmic powers `(log(|2πξ| + e))^m`, and integrability against `|ξ|^{-1/3}` near `ξ = 0`.
2. **Uniform boundedness of primorial and finite-deletion primorial forms at `ε = 1/2`:**
   * Combining `eventually_mulDistSqPair_moebiusC_ge_logPower` with Mertens' second theorem bounds
     the full smooth Euler product `eulerProductSq 1 t (Nat.primesLE z) ≤ C · (log(|t| + e))^{22}`
     uniformly in `z` and `t`. Since every prime factor satisfies `eulerFactorSq 1 t p ≥ 1/4`,
     deleting any finite set `E` of primes loses at most `4^{|E|}`.
   * Integrating against `stepSpectralWeight hr` proves that for every `r > 1` and every finite set
     `E : Finset ℕ`, `hypercubeDilationDirichletForm (1/2) (∏ p ∈ Nat.primesLE z \ E, p) r hr` is
     uniformly bounded across all `z : ℕ` (`hypercubeDilationDirichletForm_half_sdiff_bounded`),
     settling both the primorial sequence (`E = ∅`) and `roughPrimeProd r X` (`E = Nat.primesLE r`)
     in direct head-to-head contrast with the diverging `+1` parity twin.
3. **Sub-linear `O_r((log z)^{17/24})` ceiling across all `2^{π(z)}` prime subsets `S ⊆ primesLE z`:**
   * Using the exact two-squares trigonometric polynomial majorant
     `17/24 - cos θ + (1/3) cos(2θ) = (2/3)(cos θ - 3/4)² = -2 cos θ + (2/3)(cos θ + 3/4)²`,
     every subset `S ⊆ Nat.primesLE z` simultaneously satisfies
     `∑_{p ∈ S} (-2 cos(t log p) / p) ≤ (17/24) ∑_{p ≤ z} 1/p - ∑_{p ≤ z} cos(t log p)/p + (1/3) ∑_{p ≤ z} cos(2t log p)/p`.
   * Bounding `-∑ cos(t log p)/p` via `ZetaOneLineUniformLower` (zero `log log z` loss) and
     `(1/3) ∑ cos(2t log p)/p` via `norm_riemannZeta_ge_one_log_le` for `|t| ≥ 1/2` and compactness
     of `zetaEntire` on `[1, 2] × [-1, 1]` (`|t|^{-1/3}` pole singularity, integrable near `t = 0`)
     proves `hypercubeDilationDirichletForm (1/2) (∏ p ∈ S, p) r hr ≤ C_r (log z)^{17/24} = o(log z)`
     uniformly over all `S ⊆ Nat.primesLE z`, strictly below the `≍_r log z` parity-twin growth.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Set Filter Topology
open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators FourierTransform ArithmeticFunction.Moebius

/-! ## §1. Essential `L^∞` bound and dyadic decay of `stepSpectralWeight` -/

private theorem integrable_tsum_of_nonneg {F : ℕ → ℝ → ℝ}
    (hF : ∀ k, Integrable (F k) volume) (h0 : ∀ k ξ, 0 ≤ F k ξ)
    (hs : ∀ᵐ ξ ∂volume, Summable fun k => F k ξ)
    (hsum : Summable fun k => ∫ ξ, F k ξ) :
    Integrable (fun ξ => ∑' k, F k ξ) volume := by
  have hmeas : AEStronglyMeasurable (fun ξ => ∑' k, F k ξ) volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ξ => ∑ k ∈ Finset.range N, F k ξ)
      (fun N => (integrable_finsetSum _ fun k _ => hF k).aestronglyMeasurable) ?_
    filter_upwards [hs] with ξ hξ
    exact hξ.hasSum.tendsto_sum_nat
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ᵐ ξ ∂volume, ‖∑' k, F k ξ‖ₑ = ∑' k, ENNReal.ofReal (F k ξ) := by
    filter_upwards [hs] with ξ hξ
    rw [Real.enorm_eq_ofReal (tsum_nonneg fun k => h0 k ξ),
      ENNReal.ofReal_tsum_of_nonneg (fun k => h0 k ξ) hξ]
  rw [lintegral_congr_ae hpt, lintegral_tsum fun k =>
    (hF k).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  have hi : ∀ k, ∫⁻ ξ, ENNReal.ofReal (F k ξ) = ENNReal.ofReal (∫ ξ, F k ξ) := fun k =>
    (ofReal_integral_eq_lintegral_ofReal (hF k) (Eventually.of_forall fun ξ => h0 k ξ)).symm
  simp_rw [hi]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun ξ => h0 k ξ) hsum]
  exact ENNReal.ofReal_lt_top

private theorem sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have h : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]

private theorem norm_halfDensityPullback_stepSource_le_of_pos {r : ℕ} (hr : 1 < r)
    {x : ℝ} (_hx : 0 < x) :
    ‖halfDensityPullback (pmRamanujanStepSource r) x‖ ≤
      pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * x) := by
  have hb : ∀ N : ℕ, |(pmRamanujanPrimitive r N).re| ≤ pmRamanujanPrimitiveBound r :=
    fun N => (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr N)
  unfold halfDensityPullback pmRamanujanStepSource
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    sqrt_exp_eq]
  have hstep := norm_stepFun_le hb (Real.exp_pos x)
  calc Real.exp (x / 2) * ‖stepFun (fun N => (pmRamanujanPrimitive r N).re) (Real.exp x)‖
      ≤ Real.exp (x / 2) * (pmRamanujanPrimitiveBound r * (Real.exp x)⁻¹) :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ = pmRamanujanPrimitiveBound r * (Real.exp (x / 2) * Real.exp (-x)) := by
        rw [← Real.exp_neg]; ring
    _ = pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * x) := by
        rw [← Real.exp_add]; congr 2; ring

private theorem halfDensityPullback_stepSource_eq_zero_of_neg {r : ℕ} {x : ℝ} (hx : x < 0) :
    halfDensityPullback (pmRamanujanStepSource r) x = 0 := by
  have hexp : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  simp [halfDensityPullback, pmRamanujanStepSource, stepFun, Nat.floor_eq_zero.mpr hexp,
    pmRamanujanPrimitive]

private theorem measurable_halfDensityPullback_stepSource (r : ℕ) :
    Measurable (halfDensityPullback (pmRamanujanStepSource r)) :=
  (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp Real.measurable_exp)).mul
    ((measurable_stepFun _).comp Real.measurable_exp)

private theorem integrable_and_integral_norm_halfDensityPullback_le {r : ℕ} (hr : 1 < r) :
    Integrable (halfDensityPullback (pmRamanujanStepSource r)) ∧
      ∫ x, ‖halfDensityPullback (pmRamanujanStepSource r) x‖ ≤
        2 * pmRamanujanPrimitiveBound r := by
  have hg_int : Integrable ((Ioi (0 : ℝ)).indicator
      (fun x : ℝ => pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * x))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      ((integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0).const_mul _)
  have hae_ne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [Filter.eventually_iff, mem_ae_iff]; simp
  have hae : ∀ᵐ x : ℝ ∂volume, ‖halfDensityPullback (pmRamanujanStepSource r) x‖ ≤
      (Ioi (0 : ℝ)).indicator
        (fun y : ℝ => pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * y)) x := by
    filter_upwards [hae_ne] with x hx0
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      exact norm_halfDensityPullback_stepSource_le_of_pos hr hx
    · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
      rw [halfDensityPullback_stepSource_eq_zero_of_neg hneg, norm_zero,
        indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
  have hint : Integrable (halfDensityPullback (pmRamanujanStepSource r)) :=
    hg_int.mono' (measurable_halfDensityPullback_stepSource r).aestronglyMeasurable hae
  refine ⟨hint, ?_⟩
  calc ∫ x, ‖halfDensityPullback (pmRamanujanStepSource r) x‖
      ≤ ∫ x, (Ioi (0 : ℝ)).indicator
          (fun y : ℝ => pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * y)) x :=
        integral_mono_ae hint.norm hg_int hae
    _ = ∫ x in Ioi (0 : ℝ), pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * x) :=
        integral_indicator measurableSet_Ioi
    _ = pmRamanujanPrimitiveBound r * ∫ x in Ioi (0 : ℝ), Real.exp (-(1 / 2) * x) :=
        integral_const_mul _ _
    _ = 2 * pmRamanujanPrimitiveBound r := by
        rw [integral_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0]
        simp only [mul_zero, Real.exp_zero]
        ring

/-- **Essential `L^∞` bound for the Mellin spectral weight of the Ramanujan step vector.**
For every `r > 1`, `stepSpectralWeight hr ξ ≤ 4 · (pmRamanujanPrimitiveBound r)²` almost
everywhere on `ℝ`. -/
theorem stepSpectralWeight_ae_le {r : ℕ} (hr : 1 < r) :
    ∀ᵐ ξ : ℝ ∂volume, stepSpectralWeight hr ξ ≤ 4 * pmRamanujanPrimitiveBound r ^ 2 := by
  obtain ⟨hint, hmass⟩ := integrable_and_integral_norm_halfDensityPullback_le hr
  have hU : (halfLineExpUnitary (stepHalfLine hr) : ℝ → ℂ) =ᵐ[volume]
      halfDensityPullback (pmRamanujanStepSource r) :=
    halfLineExpUnitary_ae_halfDensityPullback (stepHalfLine_ae_eq hr)
  have hUint : Integrable (halfLineExpUnitary (stepHalfLine hr) : ℝ → ℂ) := hint.congr hU.symm
  have hF := coeFn_fourierTransform_eq_fourierIntegral (halfLineExpUnitary (stepHalfLine hr)) hUint
  change ((halfLineMellinUnitary (stepHalfLine hr) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
    _ at hF
  filter_upwards [hF] with ξ hξ
  unfold stepSpectralWeight
  rw [hξ, Real.fourier_congr_ae hU ξ]
  have hpt : ‖𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ‖ ≤
      2 * pmRamanujanPrimitiveBound r :=
    (norm_fourierIntegral_le_mass _ ξ).trans hmass
  calc ‖𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ‖ ^ 2
      ≤ (2 * pmRamanujanPrimitiveBound r) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hpt 2
    _ = 4 * pmRamanujanPrimitiveBound r ^ 2 := by ring

/-- Symmetric dyadic high-frequency shell `2^k ≤ |ξ| ≤ 2^{k+1}`. -/
def dyadicFreqShell (k : ℕ) : Set ℝ :=
  {ξ : ℝ | (2 : ℝ) ^ k ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (k + 1)}

private theorem measurableSet_dyadicFreqShell (k : ℕ) : MeasurableSet (dyadicFreqShell k) :=
  ((isClosed_le continuous_const continuous_abs).inter
    (isClosed_le continuous_abs continuous_const)).measurableSet

private theorem log_succ_div_mem {N : ℕ} (hN : 3 ≤ N) :
    3 / (4 * (N : ℝ)) ≤ Real.log (((N : ℝ) + 1) / (N : ℝ)) ∧
      Real.log (((N : ℝ) + 1) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hhi : Real.log (((N : ℝ) + 1) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    have h1 := Real.log_le_log (by positivity) (Real.add_one_le_exp (1 / (N : ℝ)))
    rw [Real.log_exp, show 1 / (N : ℝ) + 1 = ((N : ℝ) + 1) / (N : ℝ) by field_simp; ring] at h1
    exact h1
  have hlo1 : 1 / ((N : ℝ) + 1) ≤ Real.log (((N : ℝ) + 1) / (N : ℝ)) := by
    have hdiv : -1 / ((N : ℝ) + 1) + 1 = (N : ℝ) / ((N : ℝ) + 1) := by field_simp; ring
    have hexp := Real.add_one_le_exp (-1 / ((N : ℝ) + 1))
    rw [hdiv] at hexp
    have hlog := Real.log_le_log (by positivity) hexp
    have hneg : -1 / ((N : ℝ) + 1) = -(1 / ((N : ℝ) + 1)) := by ring
    rw [Real.log_exp, ← inv_div, Real.log_inv, hneg] at hlog
    linarith
  have hlo0 : 3 / (4 * (N : ℝ)) ≤ 1 / ((N : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact ⟨hlo0.trans hlo1, hhi⟩

private theorem cos_dyadic_shell_nonpos (k : ℕ) {ξ : ℝ} (hξ : ξ ∈ dyadicFreqShell k) :
    Real.cos (2 * Real.pi *
      (Real.log ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ)) * ξ)) ≤ 0 := by
  have hN3 : 3 ≤ 3 * 2 ^ k := by
    have := Nat.one_le_two_pow (n := k); omega
  obtain ⟨hlo, hhi⟩ := log_succ_div_mem hN3
  have hcast : (((3 * 2 ^ k + 1 : ℕ) : ℝ)) = ((3 * 2 ^ k : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have habs_cos : Real.cos (2 * Real.pi *
        (Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * ξ)) =
      Real.cos (2 * Real.pi *
        (Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ|)) := by
    rcases le_total 0 ξ with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_nonpos h0,
        show 2 * Real.pi *
          (Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * (-ξ)) =
          -(2 * Real.pi *
            (Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * ξ)) by ring,
        Real.cos_neg]
  rw [habs_cos]
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hN_eq : ((3 * 2 ^ k : ℕ) : ℝ) = 3 * (2 : ℝ) ^ k := by push_cast; ring
  have hL_pos : 0 < Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) :=
    lt_of_lt_of_le (by rw [hN_eq]; positivity) hlo
  refine Real.cos_nonpos_of_pi_div_two_le_of_le ?_ ?_
  · have hprod_lo : 1 / 4 ≤
        Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ| := by
      calc (1 : ℝ) / 4
          = 3 / (4 * (3 * (2 : ℝ) ^ k)) * (2 : ℝ) ^ k := by
              field_simp [h2k_pos.ne']
        _ = 3 / (4 * ((3 * 2 ^ k : ℕ) : ℝ)) * (2 : ℝ) ^ k := by rw [hN_eq]
        _ ≤ Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ| :=
            mul_le_mul hlo hξ.1 h2k_pos.le hL_pos.le
    calc Real.pi / 2 = 2 * Real.pi * (1 / 4) := by ring
      _ ≤ 2 * Real.pi *
          (Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ|) :=
          mul_le_mul_of_nonneg_left hprod_lo (by positivity)
  · have hprod_hi :
        Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ| ≤ 3 / 4 := by
      have hξ_hi : |ξ| ≤ 2 * (2 : ℝ) ^ k := by
        simpa [pow_succ, mul_comm] using hξ.2
      calc Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ|
          ≤ 1 / ((3 * 2 ^ k : ℕ) : ℝ) * (2 * (2 : ℝ) ^ k) :=
            mul_le_mul hhi hξ_hi (abs_nonneg ξ) (by positivity)
        _ = 2 / 3 := by
            rw [hN_eq]; field_simp [h2k_pos.ne']
        _ ≤ 3 / 4 := by norm_num
    calc 2 * Real.pi *
          (Real.log ((((3 * 2 ^ k : ℕ) : ℝ) + 1) / ((3 * 2 ^ k : ℕ) : ℝ)) * |ξ|)
        ≤ 2 * Real.pi * (3 / 4) := mul_le_mul_of_nonneg_left hprod_hi (by positivity)
      _ = Real.pi + Real.pi / 2 := by ring

private theorem residueGapPronicBudget_succ_le {N : ℕ} (hN : 3 ≤ N) :
    residueGapPronicBudget (N + 1) N ≤ 3 + Real.log (N : ℝ) := by
  have hne : N + 1 ≠ N := by omega
  have hmin : min (N + 1) N = N := Nat.min_eq_right (Nat.le_succ N)
  have hmax : max (N + 1) N = N + 1 := Nat.max_eq_left (Nat.le_succ N)
  have hsub : N + 1 - N = 1 := by omega
  simp only [residueGapPronicBudget, hne, ite_false, hmin, hmax, hsub, Nat.div_one,
    Nat.cast_one, one_mul]
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  have hN0 : (0 : ℝ) < N := by positivity
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hfrac : ((N + 1 : ℕ) : ℝ) ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) ≤ 2 := by
    rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 by push_cast; ring, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

private theorem ramanujanDilationResidueBudget_nonneg (r : ℕ) :
    0 ≤ ramanujanDilationResidueBudget r := by
  unfold ramanujanDilationResidueBudget
  positivity

/-- **Quantitative dyadic high-frequency decay of `stepSpectralWeight`.**
For every modulus `r > 1` and every `k : ℕ`, the spectral weight mass in `2^k ≤ |ξ| ≤ 2^{k+1}`
decays as `O_r((k + 5) / 2^k)`. -/
theorem stepSpectralWeight_dyadic_shell_le {r : ℕ} (hr : 1 < r) (k : ℕ) :
    ∫ ξ in dyadicFreqShell k, stepSpectralWeight hr ξ ≤
      ramanujanDilationResidueBudget r * ((k : ℝ) + 5) / (6 * (2 : ℝ) ^ k) := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : ℕ, r = r₀ + 2 := ⟨r - 2, (Nat.sub_add_cancel (by omega : 2 ≤ r)).symm⟩
  have hN3 : 3 ≤ 3 * 2 ^ k := by have := Nat.one_le_two_pow (n := k); omega
  have hc_pos : 0 < (((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ) := by positivity
  have hcos_int : Integrable fun ξ : ℝ =>
      stepSpectralWeight hr ξ * Real.cos (2 * Real.pi *
        (Real.log ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ)) * ξ)) := by
    refine (integrable_stepSpectralWeight_mul_cos hr
      (Real.log ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ)))).congr
      (Eventually.of_forall fun ξ => ?_)
    ring_nf
  have hshell_le_def : ∫ ξ in dyadicFreqShell k, stepSpectralWeight hr ξ ≤
      pmRamanujanPrimitiveGram (r₀ + 2) (r₀ + 2) -
        pmRamanujanDilationProfile (r₀ + 2) hr
          ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ)) := by
    rw [← integral_indicator (measurableSet_dyadicFreqShell k),
      ← pmRamanujanDilationProfile_one (r := r₀ + 2) (hr := hr),
      dilationProfile_eq_integral hr one_pos,
      dilationProfile_eq_integral hr hc_pos]
    simp only [Real.log_one, zero_mul, mul_zero, Real.cos_zero, mul_one]
    rw [← integral_sub (integrable_stepSpectralWeight hr) hcos_int]
    refine integral_mono
      ((integrable_stepSpectralWeight hr).indicator (measurableSet_dyadicFreqShell k))
      ((integrable_stepSpectralWeight hr).sub hcos_int) fun ξ => ?_
    dsimp only [Pi.sub_apply]
    by_cases hξ : ξ ∈ dyadicFreqShell k
    · rw [indicator_of_mem hξ]
      have hcos := cos_dyadic_shell_nonpos k hξ
      have hw := stepSpectralWeight_nonneg hr ξ
      nlinarith
    · rw [indicator_of_notMem hξ]
      have hcos := Real.cos_le_one (2 * Real.pi *
        (Real.log ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ)) * ξ))
      have hw := stepSpectralWeight_nonneg hr ξ
      nlinarith
  have hgap := ramanujanDilationProfile_defect_le_gap_budget r₀
    ⟨3 * 2 ^ k + 1, by positivity⟩ ⟨3 * 2 ^ k, by positivity⟩
  have hdef_nonneg : 0 ≤ pmRamanujanPrimitiveGram (r₀ + 2) (r₀ + 2) -
      pmRamanujanDilationProfile (r₀ + 2) hr
        ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ)) := hgap.1
  have hsqrt_le : 2 * ((3 * 2 ^ k : ℕ) : ℝ) ≤
      2 * Real.sqrt ((3 * 2 ^ k + 1 : ℕ) : ℝ) * Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ) := by
    have hle : Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ) ≤ Real.sqrt ((3 * 2 ^ k + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (3 * 2 ^ k))
    calc 2 * ((3 * 2 ^ k : ℕ) : ℝ)
        = 2 * Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ) * Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ) := by
            rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      _ ≤ 2 * Real.sqrt ((3 * 2 ^ k + 1 : ℕ) : ℝ) * Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ) := by
            nlinarith [Real.sqrt_nonneg ((3 * 2 ^ k : ℕ) : ℝ)]
  have hsq_gram_nn : 0 ≤
      (Real.sqrt ((3 * 2 ^ k + 1 : ℕ) : ℝ) - Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ)) ^ 2 *
        pmRamanujanPrimitiveGram (r₀ + 2) (r₀ + 2) :=
    mul_nonneg (sq_nonneg _) (pmRamanujanPrimitiveGram_pos hr).le
  have hmul_le : 2 * ((3 * 2 ^ k : ℕ) : ℝ) *
      (pmRamanujanPrimitiveGram (r₀ + 2) (r₀ + 2) -
        pmRamanujanDilationProfile (r₀ + 2) hr
          ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ))) ≤
      ramanujanDilationResidueBudget (r₀ + 2) *
        residueGapPronicBudget (3 * 2 ^ k + 1) (3 * 2 ^ k) := by
    have h1 := mul_le_mul_of_nonneg_right hsqrt_le hdef_nonneg
    have h2 : 2 * Real.sqrt ((3 * 2 ^ k + 1 : ℕ) : ℝ) * Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ) *
        (pmRamanujanPrimitiveGram (r₀ + 2) (r₀ + 2) -
          pmRamanujanDilationProfile (r₀ + 2) hr
            ((((3 * 2 ^ k + 1 : ℕ) : ℝ)) / ((3 * 2 ^ k : ℕ) : ℝ))) ≤
        ramanujanDilationResidueBudget (r₀ + 2) *
          residueGapPronicBudget (3 * 2 ^ k + 1) (3 * 2 ^ k) -
          (Real.sqrt ((3 * 2 ^ k + 1 : ℕ) : ℝ) - Real.sqrt ((3 * 2 ^ k : ℕ) : ℝ)) ^ 2 *
            pmRamanujanPrimitiveGram (r₀ + 2) (r₀ + 2) := hgap.2
    linarith
  have hlogN : 3 + Real.log ((3 * 2 ^ k : ℕ) : ℝ) ≤ (k : ℝ) + 5 := by
    have he2 : (4 : ℝ) ≤ Real.exp 2 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_log (by norm_num) (show (3 : ℝ) ≤ Real.exp 2 by linarith)
      rwa [Real.log_exp] at h
    have hlog2 : Real.log 2 ≤ 1 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h := Real.log_le_log (by norm_num) he1
      rwa [Real.log_exp] at h
    rw [show ((3 * 2 ^ k : ℕ) : ℝ) = 3 * (2 : ℝ) ^ k by push_cast; ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  have hbud_le : ramanujanDilationResidueBudget (r₀ + 2) *
      residueGapPronicBudget (3 * 2 ^ k + 1) (3 * 2 ^ k) ≤
      ramanujanDilationResidueBudget (r₀ + 2) * ((k : ℝ) + 5) :=
    mul_le_mul_of_nonneg_left ((residueGapPronicBudget_succ_le hN3).trans hlogN)
      (ramanujanDilationResidueBudget_nonneg (r₀ + 2))
  have h6 : 2 * ((3 * 2 ^ k : ℕ) : ℝ) = 6 * (2 : ℝ) ^ k := by push_cast; ring
  refine hshell_le_def.trans ?_
  rw [le_div_iff₀ (by positivity), mul_comm, ← h6]
  exact hmul_le.trans hbud_le

private theorem exists_mem_dyadicFreqShell {ξ : ℝ} (hξ : 1 ≤ |ξ|) :
    ∃ k : ℕ, ξ ∈ dyadicFreqShell k := by
  have hstep : ∀ M : ℕ, |ξ| ≤ (2 : ℝ) ^ M → ∃ k : ℕ, ξ ∈ dyadicFreqShell k := by
    intro M
    induction M with
    | zero =>
      intro hle
      exact ⟨0, by simpa using hξ, by simpa using hle.trans (by norm_num)⟩
    | succ M ih =>
      intro hle
      by_cases hM : |ξ| ≤ (2 : ℝ) ^ M
      · exact ih hM
      · exact ⟨M, (not_le.mp hM).le, hle⟩
  refine hstep ⌈|ξ|⌉₊ ?_
  calc |ξ| ≤ (⌈|ξ|⌉₊ : ℝ) := Nat.le_ceil |ξ|
    _ ≤ (2 ^ ⌈|ξ|⌉₊ : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := ⌈|ξ|⌉₊)).le
    _ = (2 : ℝ) ^ ⌈|ξ|⌉₊ := by push_cast; rfl

private theorem linear_le_five_mul_pow (k : ℕ) :
    (k : ℝ) + 5 ≤ 5 * (5 / 4 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    push_cast [pow_succ]
    linarith

/-- **Sub-polynomial moment integrability of `stepSpectralWeight`.**
For every `r > 1`, `stepSpectralWeight hr ξ · (1 + |ξ|)^{1/4}` is integrable on `ℝ`. -/
theorem integrable_stepSpectralWeight_mul_fourthRoot {r : ℕ} (hr : 1 < r) :
    Integrable fun ξ : ℝ => stepSpectralWeight hr ξ * Real.sqrt (Real.sqrt (1 + |ξ|)) := by
  let f : ℝ → ℝ := fun ξ => stepSpectralWeight hr ξ * Real.sqrt (Real.sqrt (1 + |ξ|))
  have hf_meas : AEStronglyMeasurable f volume :=
    (integrable_stepSpectralWeight hr).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun ξ : ℝ => Real.sqrt (Real.sqrt (1 + |ξ|))).aestronglyMeasurable
  have hf_nn : ∀ ξ : ℝ, 0 ≤ f ξ := fun ξ =>
    mul_nonneg (stepSpectralWeight_nonneg hr ξ) (Real.sqrt_nonneg _)
  let F : ℕ → ℝ → ℝ := fun k => (dyadicFreqShell k).indicator f
  have hF_bound : ∀ k : ℕ, ∀ ξ ∈ dyadicFreqShell k,
      Real.sqrt (Real.sqrt (1 + |ξ|)) ≤ 2 * (3 / 2 : ℝ) ^ k := by
    intro k ξ hξ
    have h1 : 1 + |ξ| ≤ 16 * ((3 / 2 : ℝ) ^ 4) ^ k := by
      have h2le : (2 : ℝ) ^ k ≤ ((3 / 2 : ℝ) ^ 4) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ (3 / 2) ^ 4) k
      have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hhi : |ξ| ≤ 2 * (2 : ℝ) ^ k := by simpa [pow_succ, mul_comm] using hξ.2
      linarith
    have hsqrt1 : Real.sqrt (1 + |ξ|) ≤ 4 * ((3 / 2 : ℝ) ^ 2) ^ k := by
      calc Real.sqrt (1 + |ξ|)
          ≤ Real.sqrt ((4 * ((3 / 2 : ℝ) ^ 2) ^ k) * (4 * ((3 / 2 : ℝ) ^ 2) ^ k)) := by
              refine Real.sqrt_le_sqrt (h1.trans_eq ?_)
              rw [← pow_mul, ← pow_mul]
              ring
        _ = 4 * ((3 / 2 : ℝ) ^ 2) ^ k := Real.sqrt_mul_self (by positivity)
    calc Real.sqrt (Real.sqrt (1 + |ξ|))
        ≤ Real.sqrt ((2 * (3 / 2 : ℝ) ^ k) * (2 * (3 / 2 : ℝ) ^ k)) := by
            refine Real.sqrt_le_sqrt (hsqrt1.trans_eq ?_)
            rw [← pow_mul]
            ring
      _ = 2 * (3 / 2 : ℝ) ^ k := Real.sqrt_mul_self (by positivity)
  have hF_int : ∀ k : ℕ, Integrable (F k) volume := fun k => by
    refine (((integrable_stepSpectralWeight hr).indicator (measurableSet_dyadicFreqShell k)).const_mul
      (2 * (3 / 2 : ℝ) ^ k)).mono'
      (hf_meas.indicator (measurableSet_dyadicFreqShell k))
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun y _ => hf_nn y) ξ)]
    by_cases hξ : ξ ∈ dyadicFreqShell k
    · dsimp only [F, f]
      rw [indicator_of_mem hξ, indicator_of_mem hξ]
      calc stepSpectralWeight hr ξ * Real.sqrt (Real.sqrt (1 + |ξ|))
          ≤ stepSpectralWeight hr ξ * (2 * (3 / 2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left (hF_bound k ξ hξ) (stepSpectralWeight_nonneg hr ξ)
        _ = 2 * (3 / 2 : ℝ) ^ k * stepSpectralWeight hr ξ := mul_comm _ _
    · dsimp only [F]
      rw [indicator_of_notMem hξ, indicator_of_notMem hξ, mul_zero]
  have hF_summable_pt : ∀ᵐ ξ : ℝ ∂volume, Summable fun k : ℕ => F k ξ := by
    refine Eventually.of_forall fun ξ => ?_
    refine summable_of_ne_finset_zero (s := Finset.range (⌈|ξ|⌉₊ + 1)) fun k hk => ?_
    have hk_ge : ⌈|ξ|⌉₊ + 1 ≤ k := by simp only [Finset.mem_range, not_lt] at hk; exact hk
    have hlt : |ξ| < (2 : ℝ) ^ k := by
      calc |ξ| ≤ (⌈|ξ|⌉₊ : ℝ) := Nat.le_ceil |ξ|
        _ < (⌈|ξ|⌉₊ : ℝ) + 1 := by linarith
        _ ≤ (k : ℝ) := by exact_mod_cast hk_ge
        _ ≤ (2 ^ k : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
        _ = (2 : ℝ) ^ k := by push_cast; rfl
    exact indicator_of_notMem (fun hmem => not_le_of_gt hlt hmem.1) f
  have hF_sum_int : Summable fun k : ℕ => ∫ ξ, F k ξ := by
    have hgeom : Summable fun k : ℕ =>
        ramanujanDilationResidueBudget r * (5 / 3) * (15 / 16 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun ξ => indicator_nonneg (fun y _ => hf_nn y) ξ)
      (fun k => ?_) hgeom
    have hle_pt : ∀ ξ : ℝ, F k ξ ≤
        2 * (3 / 2 : ℝ) ^ k * (dyadicFreqShell k).indicator (stepSpectralWeight hr) ξ := by
      intro ξ
      by_cases hξ : ξ ∈ dyadicFreqShell k
      · dsimp only [F, f]
        rw [indicator_of_mem hξ]
        calc stepSpectralWeight hr ξ * Real.sqrt (Real.sqrt (1 + |ξ|))
            ≤ stepSpectralWeight hr ξ * (2 * (3 / 2 : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_left (hF_bound k ξ hξ) (stepSpectralWeight_nonneg hr ξ)
          _ = 2 * (3 / 2 : ℝ) ^ k * stepSpectralWeight hr ξ := mul_comm _ _
      · dsimp only [F]
        rw [indicator_of_notMem hξ, mul_zero]
    calc ∫ ξ, F k ξ
        ≤ ∫ ξ, 2 * (3 / 2 : ℝ) ^ k * (dyadicFreqShell k).indicator (stepSpectralWeight hr) ξ :=
          integral_mono (hF_int k)
            (((integrable_stepSpectralWeight hr).indicator
              (measurableSet_dyadicFreqShell k)).const_mul _) hle_pt
      _ = 2 * (3 / 2 : ℝ) ^ k * ∫ ξ in dyadicFreqShell k, stepSpectralWeight hr ξ := by
          rw [integral_const_mul, integral_indicator (measurableSet_dyadicFreqShell k)]
      _ ≤ 2 * (3 / 2 : ℝ) ^ k *
          (ramanujanDilationResidueBudget r * ((k : ℝ) + 5) / (6 * (2 : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left (stepSpectralWeight_dyadic_shell_le hr k) (by positivity)
      _ ≤ 2 * (3 / 2 : ℝ) ^ k *
          (ramanujanDilationResidueBudget r * (5 * (5 / 4 : ℝ) ^ k) / (6 * (2 : ℝ) ^ k)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (linear_le_five_mul_pow k)
              (ramanujanDilationResidueBudget_nonneg r)) (by positivity)
      _ = ramanujanDilationResidueBudget r * (5 / 3) * (15 / 16 : ℝ) ^ k := by
          have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
          have hpow : (3 / 2 : ℝ) ^ k * (5 / 4 : ℝ) ^ k / (2 : ℝ) ^ k = (15 / 16 : ℝ) ^ k := by
            rw [← mul_pow, ← div_pow]
            norm_num
          calc 2 * (3 / 2 : ℝ) ^ k *
                (ramanujanDilationResidueBudget r * (5 * (5 / 4 : ℝ) ^ k) / (6 * (2 : ℝ) ^ k))
              = ramanujanDilationResidueBudget r * (5 / 3) *
                  ((3 / 2 : ℝ) ^ k * (5 / 4 : ℝ) ^ k / (2 : ℝ) ^ k) := by
                  field_simp [h2k]; ring
            _ = ramanujanDilationResidueBudget r * (5 / 3) * (15 / 16 : ℝ) ^ k := by rw [hpow]
  have htsum_int := integrable_tsum_of_nonneg hF_int
    (fun k ξ => indicator_nonneg (fun y _ => hf_nn y) ξ) hF_summable_pt hF_sum_int
  refine ((integrable_stepSpectralWeight hr).const_mul 2 |>.add htsum_int).mono' hf_meas
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn ξ), Pi.add_apply]
  by_cases hξ : 1 ≤ |ξ|
  · obtain ⟨k₀, hk₀⟩ := exists_mem_dyadicFreqShell hξ
    have h1 : f ξ ≤ ∑' k : ℕ, F k ξ := by
      have hsum : Summable fun k : ℕ => F k ξ := by
        refine summable_of_ne_finset_zero (s := Finset.range (⌈|ξ|⌉₊ + 1)) fun k hk => ?_
        have hk_ge : ⌈|ξ|⌉₊ + 1 ≤ k := by simp only [Finset.mem_range, not_lt] at hk; exact hk
        have hlt : |ξ| < (2 : ℝ) ^ k := by
          calc |ξ| ≤ (⌈|ξ|⌉₊ : ℝ) := Nat.le_ceil |ξ|
            _ < (⌈|ξ|⌉₊ : ℝ) + 1 := by linarith
            _ ≤ (k : ℝ) := by exact_mod_cast hk_ge
            _ ≤ (2 ^ k : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
            _ = (2 : ℝ) ^ k := by push_cast; rfl
        exact indicator_of_notMem (fun hmem => not_le_of_gt hlt hmem.1) f
      calc f ξ = F k₀ ξ := (indicator_of_mem hk₀ f).symm
        _ ≤ ∑' k : ℕ, F k ξ := hsum.le_tsum k₀ fun k _ =>
            indicator_nonneg (fun y _ => hf_nn y) ξ
    have h0 : 0 ≤ 2 * stepSpectralWeight hr ξ :=
      mul_nonneg (by norm_num) (stepSpectralWeight_nonneg hr ξ)
    linarith
  · have hlt : |ξ| < 1 := not_le.mp hξ
    have hsqrt_le2 : Real.sqrt (Real.sqrt (1 + |ξ|)) ≤ 2 := by
      calc Real.sqrt (Real.sqrt (1 + |ξ|))
          ≤ Real.sqrt (Real.sqrt 16) :=
            Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by linarith))
        _ = 2 := by
            rw [show (16 : ℝ) = 4 * 4 by norm_num, Real.sqrt_mul_self (by norm_num),
              show (4 : ℝ) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]
    have hle : f ξ ≤ 2 * stepSpectralWeight hr ξ := by
      dsimp [f]
      calc stepSpectralWeight hr ξ * Real.sqrt (Real.sqrt (1 + |ξ|))
          ≤ stepSpectralWeight hr ξ * 2 :=
            mul_le_mul_of_nonneg_left hsqrt_le2 (stepSpectralWeight_nonneg hr ξ)
        _ = 2 * stepSpectralWeight hr ξ := mul_comm _ _
    have htsum_nn : 0 ≤ ∑' k : ℕ, F k ξ :=
      tsum_nonneg fun k => indicator_nonneg (fun y _ => hf_nn y) ξ
    linarith

private theorem log_pow_le_fourthRoot (m : ℕ) (ξ : ℝ) :
    (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m ≤
      2 * (4 * ((m : ℝ) + 1)) ^ m * Real.sqrt (Real.sqrt (1 + |ξ|)) := by
  have harg_pos : 0 < |2 * Real.pi * ξ| + Real.exp 1 := by
    linarith [abs_nonneg (2 * Real.pi * ξ), Real.exp_pos 1]
  have hlog_ge1 : 1 ≤ Real.log (|2 * Real.pi * ξ| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |2 * Real.pi * ξ| + Real.exp 1 by linarith [abs_nonneg (2 * Real.pi * ξ)])
    rwa [Real.log_exp] at h
  have hlog_nn : 0 ≤ Real.log (|2 * Real.pi * ξ| + Real.exp 1) := by linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  let y : ℝ := Real.log (|2 * Real.pi * ξ| + Real.exp 1) / (4 * ((m : ℝ) + 1))
  have hy_nn : 0 ≤ y := div_nonneg hlog_nn (by positivity)
  have hy_exp : y ^ m ≤ Real.exp (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 4) := by
    calc y ^ m ≤ (y + 1) ^ m := pow_le_pow_left₀ hy_nn (by linarith) m
      _ ≤ (Real.exp y) ^ m := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp y) m
      _ = Real.exp ((m : ℝ) * y) := (Real.exp_nat_mul y m).symm
      _ ≤ Real.exp ((((m : ℝ) + 1)) * y) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
      _ = Real.exp (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 4) := by
          congr 1; dsimp [y]; field_simp [hm_pos.ne']
  have hexp_fourth : Real.exp (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 4) ≤
      2 * Real.sqrt (Real.sqrt (1 + |ξ|)) := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have habs : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    have harg_le : |2 * Real.pi * ξ| + Real.exp 1 ≤ 16 * (1 + |ξ|) := by
      rw [habs]; nlinarith [abs_nonneg ξ]
    have hsq1 : Real.exp (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 2) =
        Real.sqrt (|2 * Real.pi * ξ| + Real.exp 1) := by
      rw [← sqrt_exp_eq, Real.exp_log harg_pos]
    have hsq2 : Real.exp (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 4) =
        Real.sqrt (Real.sqrt (|2 * Real.pi * ξ| + Real.exp 1)) := by
      have hhalf : Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 4 =
          (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 2) / 2 := by ring
      rw [hhalf, ← sqrt_exp_eq, hsq1]
    rw [hsq2]
    calc Real.sqrt (Real.sqrt (|2 * Real.pi * ξ| + Real.exp 1))
        ≤ Real.sqrt (Real.sqrt (16 * (1 + |ξ|))) :=
          Real.sqrt_le_sqrt (Real.sqrt_le_sqrt harg_le)
      _ = 2 * Real.sqrt (Real.sqrt (1 + |ξ|)) := by
          rw [Real.sqrt_mul (by norm_num),
            show (16 : ℝ) = 4 * 4 by norm_num, Real.sqrt_mul_self (by norm_num),
            Real.sqrt_mul (by norm_num),
            show (4 : ℝ) = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]
  calc (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m
      = (4 * ((m : ℝ) + 1) * y) ^ m := by
          congr 1; dsimp [y]; field_simp [hm_pos.ne']
    _ = (4 * ((m : ℝ) + 1)) ^ m * y ^ m := mul_pow _ _ m
    _ ≤ (4 * ((m : ℝ) + 1)) ^ m * Real.exp (Real.log (|2 * Real.pi * ξ| + Real.exp 1) / 4) :=
        mul_le_mul_of_nonneg_left hy_exp (by positivity)
    _ ≤ (4 * ((m : ℝ) + 1)) ^ m * (2 * Real.sqrt (Real.sqrt (1 + |ξ|))) :=
        mul_le_mul_of_nonneg_left hexp_fourth (by positivity)
    _ = 2 * (4 * ((m : ℝ) + 1)) ^ m * Real.sqrt (Real.sqrt (1 + |ξ|)) := by ring

/-- **All logarithmic frequency powers are integrable against `stepSpectralWeight`.** -/
theorem integrable_stepSpectralWeight_mul_log_pow {r : ℕ} (hr : 1 < r) (m : ℕ) :
    Integrable fun ξ : ℝ =>
      stepSpectralWeight hr ξ * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m := by
  have hcont : Continuous fun ξ : ℝ => (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m := by
    refine Continuous.pow (Continuous.log ?_ ?_) m
    · fun_prop
    · intro ξ; linarith [abs_nonneg (2 * Real.pi * ξ), Real.exp_pos 1]
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => stepSpectralWeight hr ξ * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m)
      volume :=
    (integrable_stepSpectralWeight hr).aestronglyMeasurable.mul hcont.aestronglyMeasurable
  refine ((integrable_stepSpectralWeight_mul_fourthRoot hr).const_mul
    (2 * (4 * ((m : ℝ) + 1)) ^ m)).mono' hmeas (Eventually.of_forall fun ξ => ?_)
  have hlog_nn : 0 ≤ (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m := by
    refine pow_nonneg (Real.log_nonneg ?_) m
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (0 : ℝ), Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1)]
    linarith [abs_nonneg (2 * Real.pi * ξ)]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stepSpectralWeight_nonneg hr ξ) hlog_nn)]
  calc stepSpectralWeight hr ξ * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ m
      ≤ stepSpectralWeight hr ξ *
          (2 * (4 * ((m : ℝ) + 1)) ^ m * Real.sqrt (Real.sqrt (1 + |ξ|))) :=
        mul_le_mul_of_nonneg_left (log_pow_le_fourthRoot m ξ) (stepSpectralWeight_nonneg hr ξ)
    _ = 2 * (4 * ((m : ℝ) + 1)) ^ m *
          (stepSpectralWeight hr ξ * Real.sqrt (Real.sqrt (1 + |ξ|))) := by ring

/-- **Integrability of `stepSpectralWeight` against `|ξ|^{-1/3}` near `ξ = 0`.** -/
theorem integrable_stepSpectralWeight_mul_nearZero_rpow {r : ℕ} (hr : 1 < r) :
    Integrable fun ξ : ℝ =>
      stepSpectralWeight hr ξ * (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ := by
  let gpos : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (fun t : ℝ => t ^ (-(1 / 3 : ℝ)))
  have hgpos : Integrable gpos volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_rpow_Ioo_zero (by norm_num))
  have hgneg : Integrable (fun ξ : ℝ => gpos ((-1 : ℝ) * ξ)) volume :=
    hgpos.comp_mul_left' (by norm_num)
  have hae_ne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [Filter.eventually_iff, mem_ae_iff]; simp
  have hg_sym : Integrable ((Ioo (-1 : ℝ) 1).indicator (fun y : ℝ => |y| ^ (-(1 / 3 : ℝ))))
      volume := by
    refine (hgpos.add hgneg).congr ?_
    filter_upwards [hae_ne] with ξ hξ0
    simp only [Pi.add_apply, gpos, neg_one_mul]
    rcases lt_or_gt_of_ne hξ0 with hneg | hpos
    · have hnotpos : ξ ∉ Ioo (0 : ℝ) 1 := fun h => not_lt_of_gt hneg h.1
      rw [indicator_of_notMem hnotpos, zero_add]
      by_cases hgt : -1 < ξ
      · rw [indicator_of_mem (show -ξ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩),
          indicator_of_mem (show ξ ∈ Ioo (-1 : ℝ) 1 from ⟨hgt, by linarith⟩), abs_of_neg hneg]
      · rw [indicator_of_notMem (show -ξ ∉ Ioo (0 : ℝ) 1 from fun h => hgt (by linarith [h.2])),
          indicator_of_notMem (show ξ ∉ Ioo (-1 : ℝ) 1 from fun h => hgt h.1)]
    · have hnotneg : -ξ ∉ Ioo (0 : ℝ) 1 := fun h => by linarith [h.1]
      rw [indicator_of_notMem hnotneg, add_zero]
      by_cases hlt : ξ < 1
      · rw [indicator_of_mem (show ξ ∈ Ioo (0 : ℝ) 1 from ⟨hpos, hlt⟩),
          indicator_of_mem (show ξ ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hlt⟩), abs_of_pos hpos]
      · rw [indicator_of_notMem (show ξ ∉ Ioo (0 : ℝ) 1 from fun h => hlt h.2),
          indicator_of_notMem (show ξ ∉ Ioo (-1 : ℝ) 1 from fun h => hlt h.2)]
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => stepSpectralWeight hr ξ *
        (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ) volume :=
    (integrable_stepSpectralWeight hr).aestronglyMeasurable.mul hg_sym.aestronglyMeasurable
  refine (hg_sym.const_mul (4 * pmRamanujanPrimitiveBound r ^ 2)).mono' hmeas ?_
  filter_upwards [stepSpectralWeight_ae_le hr] with ξ hW
  have hind_nn : 0 ≤ (Ioo (-1 : ℝ) 1).indicator (fun y : ℝ => |y| ^ (-(1 / 3 : ℝ))) ξ :=
    indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stepSpectralWeight_nonneg hr ξ) hind_nn)]
  exact mul_le_mul_of_nonneg_right hW hind_nn

/-! ## §2. Uniform boundedness of primorial and finite-deletion primorial forms at `ε = 1/2` -/

private theorem eulerFactorSq_one_le_exp (t : ℝ) (p : ℕ) :
    eulerFactorSq 1 t p ≤
      Real.exp (1 / (p : ℝ) ^ 2 - 2 * Real.cos (t * Real.log p) / (p : ℝ)) := by
  have heq : eulerFactorSq 1 t p =
      (1 / (p : ℝ) ^ 2 - 2 * Real.cos (t * Real.log p) / (p : ℝ)) + 1 := by
    unfold eulerFactorSq
    rw [Real.rpow_neg_one]
    ring
  rw [heq]
  exact Real.add_one_le_exp _

theorem eulerProductSq_one_le_exp (t : ℝ) (S : Finset ℕ) :
    eulerProductSq 1 t S ≤
      Real.exp ((∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
        ∑ p ∈ S, (-2 * Real.cos (t * Real.log p) / (p : ℝ))) := by
  unfold eulerProductSq
  calc ∏ p ∈ S, eulerFactorSq 1 t p
      ≤ ∏ p ∈ S, Real.exp (1 / (p : ℝ) ^ 2 - 2 * Real.cos (t * Real.log p) / (p : ℝ)) :=
        Finset.prod_le_prod (fun p _ => eulerFactorSq_nonneg 1 t p)
          (fun p _ => eulerFactorSq_one_le_exp t p)
    _ = Real.exp (∑ p ∈ S, (1 / (p : ℝ) ^ 2 - 2 * Real.cos (t * Real.log p) / (p : ℝ))) :=
        (Real.exp_sum S _).symm
    _ = Real.exp ((∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
          ∑ p ∈ S, (-2 * Real.cos (t * Real.log p) / (p : ℝ))) := by
        congr 1
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring

private theorem quarter_le_eulerFactorSq_one (t : ℝ) {p : ℕ} (hp : p.Prime) :
    1 / 4 ≤ eulerFactorSq 1 t p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hinv_le : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have hcos : Real.cos (t * Real.log p) ≤ 1 := Real.cos_le_one _
  have hid : eulerFactorSq 1 t p =
      (1 - 1 / (p : ℝ)) ^ 2 + 2 * (1 / (p : ℝ)) * (1 - Real.cos (t * Real.log p)) := by
    unfold eulerFactorSq
    rw [Real.rpow_neg_one]
    ring
  rw [hid]
  have h1 : 0 ≤ 2 * (1 / (p : ℝ)) * (1 - Real.cos (t * Real.log p)) :=
    mul_nonneg (by positivity) (by linarith)
  have h2 : (1 / 2 : ℝ) ^ 2 ≤ (1 - 1 / (p : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  linarith

private theorem eulerProductSq_one_sdiff_le (t : ℝ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (E : Finset ℕ) :
    eulerProductSq 1 t (S \ E) ≤ (4 : ℝ) ^ E.card * eulerProductSq 1 t S := by
  have hsplit : eulerProductSq 1 t S =
      eulerProductSq 1 t (S \ E) * eulerProductSq 1 t (S ∩ E) := by
    unfold eulerProductSq
    conv_lhs => rw [← Finset.sdiff_union_inter S E]
    exact Finset.prod_union (Finset.disjoint_sdiff_inter S E)
  have hinter_ge : (1 / 4 : ℝ) ^ E.card ≤ eulerProductSq 1 t (S ∩ E) := by
    calc (1 / 4 : ℝ) ^ E.card
        ≤ (1 / 4 : ℝ) ^ (S ∩ E).card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (Finset.card_le_card Finset.inter_subset_right)
      _ = ∏ _p ∈ S ∩ E, (1 / 4 : ℝ) := by simp
      _ ≤ eulerProductSq 1 t (S ∩ E) :=
          Finset.prod_le_prod (fun _ _ => by norm_num) fun p hp =>
            quarter_le_eulerFactorSq_one t (hS p (Finset.mem_inter.mp hp).1)
  have hnn : 0 ≤ eulerProductSq 1 t (S \ E) := eulerProductSq_nonneg 1 t (S \ E)
  calc eulerProductSq 1 t (S \ E)
      = (4 : ℝ) ^ E.card * ((1 / 4 : ℝ) ^ E.card * eulerProductSq 1 t (S \ E)) := by
          rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ (4 : ℝ) ^ E.card * (eulerProductSq 1 t (S ∩ E) * eulerProductSq 1 t (S \ E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinter_ge hnn) (by positivity)
    _ = (4 : ℝ) ^ E.card * eulerProductSq 1 t S := by rw [hsplit, mul_comm (eulerProductSq 1 t (S \ E))]

/-- **Uniform upper bound on `-∑_{p ≤ z} cos(t log p) / p` across all `z : ℕ` and `t : ℝ`.**
Extracted from `eventually_mulDistSqPair_moebiusC_ge_logPower` with zero `log log z` loss. -/
theorem exists_neg_sum_cos_div_primesLE_le :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ z : ℕ, ∀ t : ℝ,
      -(∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)) ≤
        C₁ + 11 * Real.log (Real.log (|t| + Real.exp 1)) := by
  obtain ⟨C₀, hev⟩ := RHTower.Sieve.eventually_mulDistSqPair_moebiusC_ge_logPower
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.mp hev
  let Z := max Z₀ 2
  let C₁ : ℝ := |RHTower.Sieve.mertensSecondUpperConst + C₀| + (Z : ℝ) + 1
  refine ⟨C₁, by dsimp [C₁]; positivity, fun z t => ?_⟩
  have hL1 : 1 ≤ Real.log (|t| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
    rwa [Real.log_exp] at h
  have hlogL_nn : 0 ≤ Real.log (Real.log (|t| + Real.exp 1)) := Real.log_nonneg hL1
  by_cases hzZ : Z ≤ z
  · have hz2 : 2 ≤ z := le_trans (le_max_right Z₀ 2) hzZ
    have hD := hZ₀ z (le_trans (le_max_left Z₀ 2) hzZ) t
    have hf : ∀ p ∈ Nat.primesLE z, RHTower.Sieve.moebiusC p = -1 :=
      fun p hp => RHTower.Sieve.moebiusC_prime (Nat.mem_primesLE.mp hp).2
    rw [RHTower.Sieve.mulDistSqPair_neg_one_charFn hf t] at hD
    have hsplit : (∑ p ∈ Nat.primesLE z, (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ)) =
        (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) +
          ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hsplit] at hD
    have hmert := RHTower.Sieve.mertensS_le hz2
    unfold RHTower.Sieve.mertensS RHTower.Sieve.logLog at hmert
    have hZ_nn : (0 : ℝ) ≤ (Z : ℝ) := Nat.cast_nonneg Z
    have hleC : RHTower.Sieve.mertensSecondUpperConst + C₀ ≤ C₁ := by
      dsimp [C₁]
      linarith [le_abs_self (RHTower.Sieve.mertensSecondUpperConst + C₀)]
    linarith
  · have hcard : (Nat.primesLE z).card ≤ z := by
      calc (Nat.primesLE z).card
          ≤ (Finset.Icc 2 z).card := Finset.card_le_card fun p hp => by
              have hp' := Nat.mem_primesLE.mp hp
              exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, hp'.1⟩
        _ ≤ z := by simp
    have habs : |∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)| ≤ (Z : ℝ) := by
      calc |∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)|
          ≤ ∑ p ∈ Nat.primesLE z, |Real.cos (t * Real.log p) / (p : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p ∈ Nat.primesLE z, (1 : ℝ) := Finset.sum_le_sum fun p hp => by
            have hp2 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
            have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp2
            rw [abs_div, abs_of_pos hp0]
            exact div_le_one_of_le₀ ((Real.abs_cos_le_one _).trans hp2) hp0.le
        _ = ((Nat.primesLE z).card : ℝ) := by simp
        _ ≤ (z : ℝ) := by exact_mod_cast hcard
        _ ≤ (Z : ℝ) := by exact_mod_cast (not_le.mp hzZ).le
    have hneg := neg_le_abs (∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ))
    dsimp [C₁]
    linarith [abs_nonneg (RHTower.Sieve.mertensSecondUpperConst + C₀)]

/-- **Smooth Euler product log-power bound at `σ = 1`.**
There is an explicit constant `C > 0` such that for all `z : ℕ` and all `t : ℝ`,
`eulerProductSq 1 t (Nat.primesLE z) ≤ C · (log(|t| + e))^{22}`. -/
theorem exists_eulerProductSq_one_primesLE_le_logPower :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, ∀ t : ℝ,
      eulerProductSq 1 t (Nat.primesLE z) ≤
        C * (Real.log (|t| + Real.exp 1)) ^ (22 : ℕ) := by
  obtain ⟨C₁, _, hcos⟩ := exists_neg_sum_cos_div_primesLE_le
  refine ⟨Real.exp (Real.pi ^ 2 / 6 + 2 * C₁), Real.exp_pos _, fun z t => ?_⟩
  have hL0 : 0 < Real.log (|t| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
    rw [Real.log_exp] at h
    linarith
  have hsq := RHTower.Sieve.sum_inv_sq_primesLE_le_pi z
  have hsum_neg : ∑ p ∈ Nat.primesLE z, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) =
      -2 * ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hexp_le : (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2) +
      ∑ p ∈ Nat.primesLE z, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
      (Real.pi ^ 2 / 6 + 2 * C₁) + 22 * Real.log (Real.log (|t| + Real.exp 1)) := by
    rw [hsum_neg]
    linarith [hcos z t]
  calc eulerProductSq 1 t (Nat.primesLE z)
      ≤ Real.exp ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2) +
          ∑ p ∈ Nat.primesLE z, (-2 * Real.cos (t * Real.log p) / (p : ℝ))) :=
        eulerProductSq_one_le_exp t (Nat.primesLE z)
    _ ≤ Real.exp ((Real.pi ^ 2 / 6 + 2 * C₁) +
          22 * Real.log (Real.log (|t| + Real.exp 1))) := Real.exp_le_exp.mpr hexp_le
    _ = Real.exp (Real.pi ^ 2 / 6 + 2 * C₁) *
          (Real.log (|t| + Real.exp 1)) ^ (22 : ℕ) := by
        rw [Real.exp_add, show (22 : ℝ) = ((22 : ℕ) : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log hL0]

/-- **Unconditional uniform boundedness of finite-deletion primorial hypercube forms at `ε = 1/2`.**
For every modulus `r > 1` and every finite set `E : Finset ℕ`, the signed prime-divisor hypercube
form along `∏ p ∈ Nat.primesLE z \ E, p` is uniformly bounded across all `z : ℕ`. -/
theorem hypercubeDilationDirichletForm_half_sdiff_bounded {r : ℕ} (hr : 1 < r) (E : Finset ℕ) :
    ∃ B : ℝ, ∀ z : ℕ,
      hypercubeDilationDirichletForm (1 / 2) (∏ p ∈ Nat.primesLE z \ E, p) r hr ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_eulerProductSq_one_primesLE_le_logPower
  have hint := integrable_stepSpectralWeight_mul_log_pow hr 22
  refine ⟨(4 : ℝ) ^ E.card * C *
      ∫ ξ, stepSpectralWeight hr ξ * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 22, fun z => ?_⟩
  have hSp : ∀ p ∈ Nat.primesLE z \ E, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  rw [hypercubeDilationDirichletForm_eq_integral hr (1 / 2) hSp,
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ← integral_const_mul]
  have hint_prod : Integrable fun ξ : ℝ =>
      stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) (Nat.primesLE z \ E) := by
    have hmeas : AEStronglyMeasurable
        (fun ξ : ℝ => stepSpectralWeight hr ξ *
          eulerProductSq 1 (2 * Real.pi * ξ) (Nat.primesLE z \ E)) volume :=
      (integrable_stepSpectralWeight hr).aestronglyMeasurable.mul
        ((continuous_eulerProductSq 1 (Nat.primesLE z \ E)).comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable
    refine (hint.const_mul ((4 : ℝ) ^ E.card * C)).mono' hmeas (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stepSpectralWeight_nonneg hr ξ)
      (eulerProductSq_nonneg 1 (2 * Real.pi * ξ) _))]
    have hsdiff := eulerProductSq_one_sdiff_le (2 * Real.pi * ξ) (Nat.primesLE z)
      (fun p hp => (Nat.mem_primesLE.mp hp).2) E
    have hfull := hC z (2 * Real.pi * ξ)
    calc stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) (Nat.primesLE z \ E)
        ≤ stepSpectralWeight hr ξ *
            ((4 : ℝ) ^ E.card * (C * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 22)) :=
          mul_le_mul_of_nonneg_left (hsdiff.trans (mul_le_mul_of_nonneg_left hfull (by positivity)))
            (stepSpectralWeight_nonneg hr ξ)
      _ = (4 : ℝ) ^ E.card * C *
            (stepSpectralWeight hr ξ * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 22) := by
          ring
  refine integral_mono hint_prod (hint.const_mul _) fun ξ => ?_
  have hsdiff := eulerProductSq_one_sdiff_le (2 * Real.pi * ξ) (Nat.primesLE z)
    (fun p hp => (Nat.mem_primesLE.mp hp).2) E
  have hfull := hC z (2 * Real.pi * ξ)
  calc stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) (Nat.primesLE z \ E)
      ≤ stepSpectralWeight hr ξ *
          ((4 : ℝ) ^ E.card * (C * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 22)) :=
        mul_le_mul_of_nonneg_left (hsdiff.trans (mul_le_mul_of_nonneg_left hfull (by positivity)))
          (stepSpectralWeight_nonneg hr ξ)
    _ = (4 : ℝ) ^ E.card * C *
          (stepSpectralWeight hr ξ * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 22) := by
        ring

/-- **Unconditional uniform boundedness of the primorial hypercube form at `ε = 1/2`.** -/
theorem hypercubeDilationDirichletForm_half_primesLE_bounded {r : ℕ} (hr : 1 < r) :
    ∃ B : ℝ, ∀ z : ℕ,
      hypercubeDilationDirichletForm (1 / 2) (∏ p ∈ Nat.primesLE z, p) r hr ≤ B := by
  obtain ⟨B, hB⟩ := hypercubeDilationDirichletForm_half_sdiff_bounded hr ∅
  exact ⟨B, fun z => by simpa using hB z⟩

private theorem roughPrimeProd_eq_sdiff (r X : ℕ) :
    roughPrimeProd r X = ∏ p ∈ Nat.primesLE X \ Nat.primesLE r, p := by
  unfold roughPrimeProd
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hrp, hpX⟩, hp⟩
    exact ⟨⟨hpX, hp⟩, fun h => by omega⟩
  · rintro ⟨⟨hpX, hp⟩, hnot⟩
    exact ⟨⟨by by_contra hle; exact hnot ⟨by omega, hp⟩, hpX⟩, hp⟩

/-- **Unconditional uniform boundedness of `hypercubeDilationDirichletForm` along `roughPrimeProd`
at `ε = 1/2`.** -/
theorem hypercubeDilationDirichletForm_half_roughPrimeProd_bounded {r : ℕ} (hr : 1 < r) :
    ∃ B : ℝ, ∀ X : ℕ,
      hypercubeDilationDirichletForm (1 / 2) (roughPrimeProd r X) r hr ≤ B := by
  obtain ⟨B, hB⟩ := hypercubeDilationDirichletForm_half_sdiff_bounded hr (Nat.primesLE r)
  exact ⟨B, fun X => by rw [roughPrimeProd_eq_sdiff]; exact hB X⟩

/-- **Head-to-head prime-divisor sign separation along `roughPrimeProd` at half damping (`ε = 1/2`).**
Evaluated on the identical squarefree sequence `roughPrimeProd r X = ∏_{r < p ≤ X} p` coprime to
`r`, the signed Möbius hypercube form is uniformly bounded in `X`, whereas its `+1` parity twin
diverges to `+∞`. -/
theorem hypercube_roughPrimeProd_half_damping_sign_split {r : ℕ} (hr : 1 < r) :
    (∃ B : ℝ, ∀ X : ℕ, hypercubeDilationDirichletForm (1 / 2) (roughPrimeProd r X) r hr ≤ B) ∧
      Tendsto (fun X : ℕ => hypercubeTwinDilationDirichletForm (1 / 2) (roughPrimeProd r X) r hr)
        atTop atTop :=
  ⟨hypercubeDilationDirichletForm_half_roughPrimeProd_bounded hr,
    tendsto_hypercubeTwinDilationDirichletForm_half_roughPrimeProd hr⟩

/-! ## §3. Sub-linear `O_r((log z)^{17/24})` ceiling across all `2^{π(z)}` prime subsets -/

theorem two_squares_cos_majorant (θ : ℝ) :
    0 ≤ 17 / 24 - Real.cos θ + 1 / 3 * Real.cos (2 * θ) ∧
      -2 * Real.cos θ ≤ 17 / 24 - Real.cos θ + 1 / 3 * Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  exact ⟨by nlinarith [sq_nonneg (Real.cos θ - 3 / 4)],
    by nlinarith [sq_nonneg (Real.cos θ + 3 / 4)]⟩

private theorem sum_subset_neg_two_cos_div_prime_le {z : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Nat.primesLE z) (t : ℝ) :
    ∑ p ∈ S, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
      17 / 24 * (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) -
        (∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)) +
        1 / 3 * (∑ p ∈ Nat.primesLE z, Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
  calc ∑ p ∈ S, (-2 * Real.cos (t * Real.log p) / (p : ℝ))
      ≤ ∑ p ∈ S, (17 / 24 - Real.cos (t * Real.log p) +
          1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
        Finset.sum_le_sum fun p _ =>
          div_le_div_of_nonneg_right (two_squares_cos_majorant (t * Real.log p)).2
            (Nat.cast_nonneg p)
    _ ≤ ∑ p ∈ Nat.primesLE z, (17 / 24 - Real.cos (t * Real.log p) +
          1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun p _ _ =>
          div_nonneg (two_squares_cos_majorant (t * Real.log p)).1 (Nat.cast_nonneg p)
    _ = 17 / 24 * (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) -
          (∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)) +
          1 / 3 * (∑ p ∈ Nat.primesLE z, Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring]
        ring

/-- **Upper bound on the finite prime cosine sum from an upper bound on `‖riemannZeta‖`.** -/
theorem sum_cos_div_prime_le_of_zeta_upper {z : ℕ} {u B : ℝ} (hz : 3 ≤ z)
    (hB : ‖riemannZeta ((((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ≤ B) :
    ∑ p ∈ Nat.primesLE z, Real.cos (u * Real.log p) / (p : ℝ) ≤
      Real.log B + Real.pi ^ 2 / 6 +
        2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
        (1 + Real.log 4) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  let σ : ℝ := 1 + 1 / Real.log (z : ℝ)
  have hσ1 : (1 : ℝ) < σ := by
    dsimp [σ]
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hre : (1 : ℝ) < ((σ : ℂ) + (u : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    exact hσ1
  have hz_ne : riemannZeta ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hre.le
  have hlog_zeta : Real.log ‖riemannZeta ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ Real.log B :=
    Real.log_le_log (norm_pos_iff.mpr hz_ne) hB
  have hcomp := abs_le.1 (RHTower.Sieve.abs_log_norm_riemannZeta_sub_tsum_re_le hre)
  have hsq : (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) =
      ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    rw [RHTower.Sieve.tsum_norm_sq_eq]
    congr 1; ext p; congr 2
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
  have htail_sq : (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ))) ≤ Real.pi ^ 2 / 6 :=
    RHTower.Sieve.tsum_prime_rpow_le hσ1.le
  rw [hsq] at hcomp
  have htsum_le : ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * Complex.I))).re ≤
      Real.log B + Real.pi ^ 2 / 6 := by
    linarith [hcomp.1, hlog_zeta, htail_sq]
  have hsplit := RHTower.Sieve.tsum_re_prime_cpow_split (z := z) (t := u) hσ1
  have htail := abs_le.1 (RHTower.Sieve.abs_tsum_prime_tail_re_le (z := z) (t := u) hσ1)
  have htailC := RHTower.Sieve.tsum_primeTailTerm_le hz
  change ∑' p : Nat.Primes, RHTower.Sieve.primeTailTerm z σ p ≤ _ at htailC
  have hshift := abs_le.1 (RHTower.Sieve.abs_sum_weight_shift_le (z := z) (by omega) hσ1.le
    (w := fun p : ℕ => Real.cos (u * Real.log (p : ℝ))) (fun p => Real.abs_cos_le_one _))
  have hshiftC : (σ - 1) * (Real.log z + Real.log 4) ≤ 1 + Real.log 4 := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hval : (σ - 1) * (Real.log z + Real.log 4) = 1 + Real.log 4 / Real.log (z : ℝ) := by
      dsimp [σ]; field_simp; ring
    have hdiv : Real.log 4 / Real.log (z : ℝ) ≤ Real.log 4 := by
      rw [div_le_iff₀ hlogz0]; nlinarith
    linarith
  have hident : ∑ p ∈ Nat.primesLE z, Real.cos (u * Real.log (p : ℝ)) / (p : ℝ) =
      (∑ n ∈ Nat.primesLE z, ((n : ℝ)) ^ (-σ) * Real.cos (u * Real.log n)) +
        ∑ p ∈ Nat.primesLE z, Real.cos (u * Real.log (p : ℝ)) * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hident]
  linarith [htsum_le, hsplit, htail.1, htail.2, htailC, hshift.1, hshift.2, hshiftC]

/-- Compactness maximum of `‖zetaEntire‖` on the pole-straddling box `[1, 2] × [-1, 1]`. -/
private theorem exists_upper_bound_zetaEntire_box :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ M := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn
    (RHTower.differentiable_zetaEntire.continuous.continuousOn (s := Metric.closedBall (0 : ℂ) 4))
  refine ⟨max 1 K₀, le_max_left _ _, fun σ hσ u hu => ?_⟩
  have hmem : ((σ : ℂ) + (u : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖((σ : ℂ) + (u : ℂ) * Complex.I)‖
        ≤ ‖(σ : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |σ| + |u| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 + 1 := by
          have h1 : |σ| ≤ 2 := abs_of_nonneg (by linarith [hσ.1]) ▸ hσ.2
          have h2 : |u| ≤ 1 := abs_le.mpr hu
          linarith
      _ ≤ 4 := by norm_num
  exact (hK₀ _ hmem).trans (le_max_right _ _)

private theorem sum_cos_two_mul_le_of_half_le {z : ℕ} (hz : 3 ≤ z) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    ∑ p ∈ Nat.primesLE z, Real.cos (2 * t * Real.log p) / (p : ℝ) ≤
      Real.log 5 + Real.log (Real.log (|t| + Real.exp 1)) +
        (Real.pi ^ 2 / 6 +
          2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
          (1 + Real.log 4)) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
  have hσ_lo : (1 : ℝ) ≤ 1 + 1 / Real.log (z : ℝ) := by
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hσ_hi : 1 + 1 / Real.log (z : ℝ) ≤ 2 := by
    have : 1 / Real.log (z : ℝ) ≤ 1 := div_le_one_of_le₀ hlogz1 hlogz_pos.le
    linarith
  have hre : (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re =
      1 + 1 / Real.log (z : ℝ) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
  have him : (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).im = 2 * t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have him_abs : |(((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).im| =
      2 * |t| := by
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hzeta_hi := RHTower.Sieve.norm_riemannZeta_ge_one_log_le
    (w := ((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
    (by rw [hre]; exact hσ_lo) (by rw [hre]; exact hσ_hi) (by rw [him_abs]; linarith)
  rw [him_abs] at hzeta_hi
  have hL1 : 1 ≤ Real.log (|t| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
    rwa [Real.log_exp] at h
  have hL_pos : 0 < Real.log (|t| + Real.exp 1) := by linarith
  have hB_le : 3 + Real.log (4 + 2 * |t|) ≤ 5 * Real.log (|t| + Real.exp 1) := by
    have harg : 4 + 2 * |t| ≤ 2 * (|t| + Real.exp 1) := by linarith [Real.exp_one_gt_d9]
    have hlog_arg : Real.log (4 + 2 * |t|) ≤ Real.log 2 + Real.log (|t| + Real.exp 1) :=
      (Real.log_le_log (by positivity) harg).trans_eq
        (Real.log_mul (by norm_num) (by linarith [Real.exp_pos 1]))
    have hlog2 : Real.log 2 ≤ 1 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      simpa [Real.log_exp] using Real.log_le_log (by norm_num) he1
    linarith
  have hcos2 := sum_cos_div_prime_le_of_zeta_upper (z := z) (u := 2 * t)
    (B := 5 * Real.log (|t| + Real.exp 1)) hz (hzeta_hi.trans hB_le)
  rw [Real.log_mul (by norm_num) hL_pos.ne'] at hcos2
  linarith

private theorem sum_cos_two_mul_le_of_lt_half {M_box : ℝ} (hM1 : 1 ≤ M_box)
    (hbox : ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ M_box)
    {z : ℕ} (hz : 3 ≤ z) {t : ℝ} (ht_pos : 0 < |t|) (ht_lt : |t| < 1 / 2) :
    ∑ p ∈ Nat.primesLE z, Real.cos (2 * t * Real.log p) / (p : ℝ) ≤
      Real.log M_box - Real.log |t| +
        (Real.pi ^ 2 / 6 +
          2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
          (1 + Real.log 4)) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
  have hσ_mem : 1 + 1 / Real.log (z : ℝ) ∈ Icc (1 : ℝ) 2 :=
    ⟨le_add_of_nonneg_right (by positivity),
     by
      have h1 : 1 / Real.log (z : ℝ) ≤ 1 := div_le_one_of_le₀ hlogz1 hlogz_pos.le
      linarith⟩
  have h2t_mem : 2 * t ∈ Icc (-1 : ℝ) 1 := by
    refine abs_le.mp ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hs1 : (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have him := congrArg Complex.im hcon
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
    exact ht_pos.ne' (by simp [show t = 0 by linarith])
  have hfac := RHTower.zetaEntire_eq hs1
  have hsub_norm : 2 * |t| ≤
      ‖(((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) - 1‖ := by
    have hle := Complex.abs_im_le_norm
      ((((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) - 1)
    have him : ((((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) - 1).im =
        2 * t := by
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.one_im, sub_zero]
    rwa [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hle
  have hent := hbox (1 + 1 / Real.log (z : ℝ)) hσ_mem (2 * t) h2t_mem
  rw [hfac, norm_mul] at hent
  have hzeta_lo :
      ‖riemannZeta (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ≤
        M_box / |t| := by
    rw [le_div_iff₀ ht_pos]
    have hmul := (mul_le_mul_of_nonneg_right hsub_norm (norm_nonneg _)).trans hent
    nlinarith [norm_nonneg
      (riemannZeta (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))]
  have hcos2 := sum_cos_div_prime_le_of_zeta_upper (z := z) (u := 2 * t)
    (B := M_box / |t|) hz hzeta_lo
  rw [Real.log_div (by linarith) ht_pos.ne'] at hcos2
  linarith

/-- **Pointwise subset Euler-product bound across all frequencies `ξ ≠ 0` and all subsets
`S ⊆ Nat.primesLE z`.** -/
private theorem exists_eulerProductSq_one_subset_le :
    ∃ C_sub : ℝ, 0 < C_sub ∧ ∀ z : ℕ, 3 ≤ z → ∀ S : Finset ℕ, S ⊆ Nat.primesLE z →
      ∀ ξ : ℝ, ξ ≠ 0 →
        eulerProductSq 1 (2 * Real.pi * ξ) S ≤
          C_sub * ((Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 +
            (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ) *
            (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
  obtain ⟨C₁, hC₁0, hcos1⟩ := exists_neg_sum_cos_div_primesLE_le
  obtain ⟨M_box, hM1, hbox⟩ := exists_upper_bound_zetaEntire_box
  let C_pass : ℝ := Real.pi ^ 2 / 6 +
    2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
    (1 + Real.log 4)
  let C_exp : ℝ := Real.pi ^ 2 / 6 + 17 / 24 * |RHTower.Sieve.mertensSecondUpperConst| +
    C₁ + 1 / 3 * C_pass + Real.log 5 + Real.log M_box + 22
  refine ⟨Real.exp C_exp, Real.exp_pos _, fun z hz S hS ξ hξ0 => ?_⟩
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz1 : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
  have ht_ne : 2 * Real.pi * ξ ≠ 0 := mul_ne_zero (by positivity) hξ0
  have ht_pos : 0 < |2 * Real.pi * ξ| := abs_pos.mpr ht_ne
  have hL1 : 1 ≤ Real.log (|2 * Real.pi * ξ| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |2 * Real.pi * ξ| + Real.exp 1 by linarith [abs_nonneg (2 * Real.pi * ξ)])
    rwa [Real.log_exp] at h
  have hL_pos : 0 < Real.log (|2 * Real.pi * ξ| + Real.exp 1) := by linarith
  have hsq_S : ∑ p ∈ S, 1 / (p : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => by positivity).trans
      (RHTower.Sieve.sum_inv_sq_primesLE_le_pi z)
  have hmert := RHTower.Sieve.mertensS_le (by omega : 2 ≤ z)
  unfold RHTower.Sieve.mertensS RHTower.Sieve.logLog at hmert
  have hmert_abs : 17 / 24 * (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) ≤
      17 / 24 * Real.log (Real.log (z : ℝ)) +
        17 / 24 * |RHTower.Sieve.mertensSecondUpperConst| := by
    linarith [hmert, le_abs_self RHTower.Sieve.mertensSecondUpperConst]
  have hlogz_rpow : Real.exp (17 / 24 * Real.log (Real.log (z : ℝ))) =
      (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hlogz_pos]
  have hM_log_nn : 0 ≤ Real.log M_box := Real.log_nonneg hM1
  have hlog5_nn : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  by_cases ht_half : 1 / 2 ≤ |2 * Real.pi * ξ|
  · have hcos2 := sum_cos_two_mul_le_of_half_le hz ht_half
    have hlogL_nn : 0 ≤ Real.log (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) := Real.log_nonneg hL1
    have hsum_bound : (∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
        ∑ p ∈ S, (-2 * Real.cos (2 * Real.pi * ξ * Real.log p) / (p : ℝ)) ≤
        C_exp + 12 * Real.log (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) +
          17 / 24 * Real.log (Real.log (z : ℝ)) := by
      have hsub := sum_subset_neg_two_cos_div_prime_le hS (2 * Real.pi * ξ)
      rw [show 2 * (2 * Real.pi * ξ) = 2 * (2 * Real.pi * ξ) from rfl] at hsub
      have hc1 := hcos1 z (2 * Real.pi * ξ)
      dsimp [C_exp, C_pass] at hcos2 ⊢
      linarith
    have hind_nn : 0 ≤ (Ioo (-1 : ℝ) 1).indicator (fun y : ℝ => |y| ^ (-(1 / 3 : ℝ))) ξ :=
      indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) ξ
    calc eulerProductSq 1 (2 * Real.pi * ξ) S
        ≤ Real.exp ((∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
            ∑ p ∈ S, (-2 * Real.cos (2 * Real.pi * ξ * Real.log p) / (p : ℝ))) :=
          eulerProductSq_one_le_exp (2 * Real.pi * ξ) S
      _ ≤ Real.exp (C_exp + 12 * Real.log (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) +
            17 / 24 * Real.log (Real.log (z : ℝ))) := Real.exp_le_exp.mpr hsum_bound
      _ = Real.exp C_exp * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ (12 : ℕ) *
            (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
          rw [Real.exp_add, Real.exp_add, hlogz_rpow,
            show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hL_pos]
      _ ≤ Real.exp C_exp * ((Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 +
            (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ) *
            (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
            (Real.exp_pos C_exp).le) (Real.rpow_nonneg hlogz_pos.le _)
  · have ht_lt : |2 * Real.pi * ξ| < 1 / 2 := not_le.mp ht_half
    have hcos2 := sum_cos_two_mul_le_of_lt_half hM1 hbox hz ht_pos ht_lt
    have hL_le2 : Real.log (|2 * Real.pi * ξ| + Real.exp 1) ≤ Real.exp 2 := by
      have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have he2 : (4 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      have h := Real.log_le_log (by positivity)
        (show |2 * Real.pi * ξ| + Real.exp 1 ≤ Real.exp 2 by linarith)
      rw [Real.log_exp] at h
      linarith
    have hlogL_le2 : Real.log (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ≤ 2 := by
      simpa [Real.log_exp] using Real.log_le_log hL_pos hL_le2
    have hsum_bound : (∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
        ∑ p ∈ S, (-2 * Real.cos (2 * Real.pi * ξ * Real.log p) / (p : ℝ)) ≤
        C_exp + (-(1 / 3 : ℝ) * Real.log |2 * Real.pi * ξ|) +
          17 / 24 * Real.log (Real.log (z : ℝ)) := by
      have hsub := sum_subset_neg_two_cos_div_prime_le hS (2 * Real.pi * ξ)
      have hc1 := hcos1 z (2 * Real.pi * ξ)
      dsimp [C_exp, C_pass] at hcos2 ⊢
      linarith
    have hξ_mem : ξ ∈ Ioo (-1 : ℝ) 1 := by
      have habs_t : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
        rw [abs_mul, abs_of_pos (by positivity)]
      have hpi : 3 < Real.pi := Real.pi_gt_three
      exact abs_lt.mp (by nlinarith)
    have ht_rpow_le : Real.exp (-(1 / 3 : ℝ) * Real.log |2 * Real.pi * ξ|) ≤
        (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ := by
      rw [mul_comm, ← Real.rpow_def_of_pos ht_pos, indicator_of_mem hξ_mem,
        abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        Real.mul_rpow (by positivity) (abs_nonneg ξ)]
      have h2pi_le1 : (2 * Real.pi) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
        linarith [Real.pi_gt_three]
      calc (2 * Real.pi) ^ (-(1 / 3 : ℝ)) * |ξ| ^ (-(1 / 3 : ℝ))
          ≤ 1 * |ξ| ^ (-(1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right h2pi_le1 (Real.rpow_nonneg (abs_nonneg ξ) _)
        _ = |ξ| ^ (-(1 / 3 : ℝ)) := one_mul _
    have hL12_nn : 0 ≤ (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 :=
      pow_nonneg hL_pos.le 12
    calc eulerProductSq 1 (2 * Real.pi * ξ) S
        ≤ Real.exp ((∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
            ∑ p ∈ S, (-2 * Real.cos (2 * Real.pi * ξ * Real.log p) / (p : ℝ))) :=
          eulerProductSq_one_le_exp (2 * Real.pi * ξ) S
      _ ≤ Real.exp (C_exp + (-(1 / 3 : ℝ) * Real.log |2 * Real.pi * ξ|) +
            17 / 24 * Real.log (Real.log (z : ℝ))) := Real.exp_le_exp.mpr hsum_bound
      _ = Real.exp C_exp * Real.exp (-(1 / 3 : ℝ) * Real.log |2 * Real.pi * ξ|) *
            (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
          rw [Real.exp_add, Real.exp_add, hlogz_rpow]
      _ ≤ Real.exp C_exp * ((Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 +
            (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ) *
            (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos C_exp).le)
            (Real.rpow_nonneg hlogz_pos.le _)

/-- **Unconditional sub-linear `O_r((log z)^{17/24})` ceiling across all `2^{π(z)}` prime subsets
at half damping (`ε = 1/2`).**
For every modulus `r > 1`, there is an explicit constant `C > 0` such that for all `z ≥ 3` and all
subsets `S ⊆ Nat.primesLE z`,
`hypercubeDilationDirichletForm (1/2) (∏ p ∈ S, p) r hr ≤ C · (log z)^{17/24}`. -/
theorem hypercubeDilationDirichletForm_half_subset_le_rpow_log {r : ℕ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 3 ≤ z → ∀ S : Finset ℕ, S ⊆ Nat.primesLE z →
      hypercubeDilationDirichletForm (1 / 2) (∏ p ∈ S, p) r hr ≤
        C * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
  obtain ⟨C_sub, hC_sub, hsub⟩ := exists_eulerProductSq_one_subset_le
  have hint_log := integrable_stepSpectralWeight_mul_log_pow hr 12
  have hint_zero := integrable_stepSpectralWeight_mul_nearZero_rpow hr
  let Φ : ℝ → ℝ := fun ξ => stepSpectralWeight hr ξ *
    ((Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 +
      (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ)
  have hΦ_int : Integrable Φ volume := by
    refine (hint_log.add hint_zero).congr (Eventually.of_forall fun ξ => ?_)
    simp only [Φ, Pi.add_apply]
    ring
  have hΦ_nn : 0 ≤ ∫ ξ, Φ ξ := by
    refine integral_nonneg fun ξ => mul_nonneg (stepSpectralWeight_nonneg hr ξ) ?_
    have h1 : 0 ≤ (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 := by
      refine pow_nonneg (Real.log_nonneg ?_) 12
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.add_one_le_exp (1 : ℝ)]
      linarith [abs_nonneg (2 * Real.pi * ξ)]
    have h2 : 0 ≤ (Ioo (-1 : ℝ) 1).indicator (fun y : ℝ => |y| ^ (-(1 / 3 : ℝ))) ξ :=
      indicator_nonneg (fun y _ => Real.rpow_nonneg (abs_nonneg y) _) ξ
    linarith
  refine ⟨C_sub * (∫ ξ, Φ ξ) + 1, by positivity, fun z hz S hS => ?_⟩
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primesLE.mp (hS hp)).2
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz_pos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by linarith : (1 : ℝ) < z)
  have hrpow_nn : 0 ≤ (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := Real.rpow_nonneg hlogz_pos.le _
  have hae_ne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [Filter.eventually_iff, mem_ae_iff]; simp
  have hae_le : ∀ᵐ ξ : ℝ ∂volume,
      stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) S ≤
        (C_sub * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ)) * Φ ξ := by
    filter_upwards [hae_ne] with ξ hξ0
    calc stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) S
        ≤ stepSpectralWeight hr ξ *
            (C_sub * ((Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 +
              (Ioo (-1 : ℝ) 1).indicator (fun y => |y| ^ (-(1 / 3 : ℝ))) ξ) *
              (Real.log (z : ℝ)) ^ (17 / 24 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hsub z hz S hS ξ hξ0) (stepSpectralWeight_nonneg hr ξ)
      _ = (C_sub * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ)) * Φ ξ := by dsimp [Φ]; ring
  have hint_prod : Integrable
      (fun ξ : ℝ => stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) S) volume := by
    have hmeas : AEStronglyMeasurable
        (fun ξ : ℝ => stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) S) volume :=
      (integrable_stepSpectralWeight hr).aestronglyMeasurable.mul
        ((continuous_eulerProductSq 1 S).comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable
    refine (hΦ_int.const_mul (C_sub * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ))).mono' hmeas ?_
    filter_upwards [hae_le] with ξ hle
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stepSpectralWeight_nonneg hr ξ)
      (eulerProductSq_nonneg 1 (2 * Real.pi * ξ) S))]
    exact hle
  rw [hypercubeDilationDirichletForm_eq_integral hr (1 / 2) hSp,
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  calc ∫ ξ, stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) S
      ≤ ∫ ξ, (C_sub * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ)) * Φ ξ :=
        integral_mono_ae hint_prod (hΦ_int.const_mul _) hae_le
    _ = C_sub * (∫ ξ, Φ ξ) * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) := by
        rw [integral_const_mul]; ring
    _ ≤ (C_sub * (∫ ξ, Φ ξ) + 1) * (Real.log (z : ℝ)) ^ (17 / 24 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hrpow_nn

end GaloisForLFunctions.SignedSuccessorArithmetic
