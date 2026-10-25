import GaloisForLFunctions.SignedSuccessorArithmetic.TheSignedPrimeDivisorEndpointAtHalfDamping
import GaloisForLFunctions.RHTower.PMRamanujanBandMellin
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowDyadic
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound

/-!
# The hypercube Dirichlet form is uniformly bounded at half damping (`ε = 1/2`, `σ = 1`)

This module settles the open endpoint of the prime-divisor Möbius hypercube Dirichlet form

  `Q_ε(P) = ∑_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{-1/2-ε} Φ_r(d₁ / d₂)`,

proving that for every Ramanujan modulus `r > 1`, `Q_{1/2}(P)` is **uniformly bounded across all
squarefree integers `P : ℕ`** (`hypercubeDilationDirichletForm_half_bounded`), with no smoothness
cutoff and no restriction to primorials. Together with `TheHypercubeDirichletFormIsUnbounded`
(`-1/2 ≤ ε < 1/2`), `TheHalfDampingBorderlineSplitsBySign` (divergence of the `+1` parity twin at
`ε = 1/2`), and `BezoutCouplingAndCrossDepthCancellation` (`ε > 1/2`), this completes the
unconditional phase diagram of `Q_ε(P)` across all `ε ≥ -1/2`.

## Proof architecture

1. **Pointwise `O_r((1 + |ξ|)^{-4/3})` decay of `stepSpectralWeight` (`§1`):**
   * The half-density pullback of `pmRamanujanStepSource r` equals the reflected half-density
     pullback of `pmRamanujanPrimitiveSource r`, whose Mellin transform on `Re s = 1/2` is
     `(ζ(s) / s) · pmRamanujanMellinSymbol r s` (`hasMellin_pmRamanujanPrimitiveSource`).
   * Combining real-valued conjugate symmetry (`W_r(-ξ) = W_r(ξ)`), essential boundedness near the
     origin (`stepSpectralWeight_ae_le`), and the convexity bound
     `‖ζ(1/2 + it)‖ ≤ C · t^{1/3}` (`exists_norm_riemannZeta_le_convexity` at `η = 1/6`) yields
     `stepSpectralWeight hr ξ ≤ C_W(r) · (1 + |ξ|)^{-4/3}` almost everywhere on `ℝ`.
2. **Pole-free subset log-Euler-product bound (`§2`):**
   * For `|t| < 1/2` and primes `p ≤ e^{1/|t|}`, `|t log p| ≤ 1 < π/2` forces `cos(t log p) ≥ 0`
     and `-2 cos(t log p) / p ≤ 0`. On the remaining window `e^{1/|t|} < p ≤ w`, comparing
     `s_w = 1 + 1/log w + iu` against `s_{w₀} = 1 + 1/log w₀ + iu` (`w₀ = ⌊e^{1/|t|}⌋₊`,
     `u ∈ {t, 2t}`) via `zetaEntire(s) = (s - 1) ζ(s)` cancels `log(1/|u|)` identically.
   * Consequently, for every `w ≥ 3`, every `S' ⊆ Nat.primesLE w`, and **every** `t : ℝ` (including
     `t = 0`), `∑_{p ∈ S'} (-2 cos(t log p) / p) ≤ C₀ + 12 log log(|t| + e) + (17/24) log log w`.
3. **Translation-invariant shell `L²` decay and exponential integrability (`§3–§4`):**
   * Partitioning any finite prime set `S` into double-exponential shells
     `S_j = {p ∈ S : ⌊e^{e^j}⌋₊ < p ≤ ⌊e^{e^{j+1}}⌋₊}` (`j ≥ 1`) and majorizing `1_{[a-1, a+1]}` by
     `2 (1 + cos(t - a))` on `[a - π, a + π]` produces a third-order `O(|ω|^{-3})`
     Fejér-cosine kernel. Summing unit logarithmic prime windows via `sum_inv_dyadic_window_le` and
     `abs_sum_inv_bigPrimeSet_sub_le` gives `∫_{a-1}^{a+1} (shellTrig S_j t)² dt ≤ C_{L2} e^{-j}`
     uniformly in `a ∈ ℝ` and `S`.
   * Splitting `S` at `j₀ = ⌊(6/5) n⌋₊` gives headroom `(1 - (17/24)(6/5)) n = (3/20) n` against
     the tail `L²` norm `O(e^{-j₀/2})`, yielding super-level decay `O(e^{-(6/5) n})` (`6/5 > 1`),
     uniform unit-interval integrability of `exp(desingLogProd S t)`, and summability against
     `(1 + |ξ|)^{-4/3} (log(|2πξ| + e))^{12} ≪ (1 + |ξ|)^{-7/6}` over `ℝ`.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Set Filter Topology
open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators FourierTransform ArithmeticFunction.Moebius

/-! ## §1. Pointwise `O_r((1 + |ξ|)^{-4/3})` bound on `stepSpectralWeight` -/

private theorem pmRamanujanPrimitive_re_ofReal (r N : ℕ) :
    ((pmRamanujanPrimitive r N).re : ℂ) = pmRamanujanPrimitive r N := by
  apply Complex.ext
  · simp
  · simp [pmRamanujanPrimitive_im]

private theorem sqrt_exp_eq_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have h : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]

private theorem halfDensityPullback_stepSource_eq_primitiveSource_neg (r : ℕ) (x : ℝ) :
    halfDensityPullback (pmRamanujanStepSource r) x =
      halfDensityPullback (pmRamanujanPrimitiveSource r) (-x) := by
  unfold halfDensityPullback pmRamanujanStepSource pmRamanujanPrimitiveSource stepFun
  rw [pmRamanujanPrimitive_re_ofReal,
    show 1 / Real.exp (-x) = Real.exp x by rw [one_div, Real.exp_neg, inv_inv],
    sqrt_exp_eq_half, sqrt_exp_eq_half]
  have hexp : ((Real.exp (x / 2) : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ)⁻¹ =
      ((Real.exp (-x / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 2
    ring
  calc ((Real.exp (x / 2) : ℝ) : ℂ) *
        (pmRamanujanPrimitive r ⌊Real.exp x⌋₊ * ((Real.exp x : ℝ) : ℂ)⁻¹)
      = (((Real.exp (x / 2) : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ)⁻¹) *
          pmRamanujanPrimitive r ⌊Real.exp x⌋₊ := by ring
    _ = ((Real.exp (-x / 2) : ℝ) : ℂ) * pmRamanujanPrimitive r ⌊Real.exp x⌋₊ := by rw [hexp]

private theorem halfDensityPullback_stepSource_conj (r : ℕ) (x : ℝ) :
    starRingEnd ℂ (halfDensityPullback (pmRamanujanStepSource r) x) =
      halfDensityPullback (pmRamanujanStepSource r) x := by
  unfold halfDensityPullback pmRamanujanStepSource stepFun
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]

private theorem fourier_halfDensityPullback_stepSource_neg (r : ℕ) (ξ : ℝ) :
    𝓕 (halfDensityPullback (pmRamanujanStepSource r)) (-ξ) =
      starRingEnd ℂ (𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul,
    halfDensityPullback_stepSource_conj]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem fourier_halfDensityPullback_stepSource_eq_mellin {r : ℕ} (hr : 1 < r) (ξ : ℝ) :
    𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ =
      riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) /
        ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
        pmRamanujanMellinSymbol r ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  have hflip : 𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ =
      𝓕 (halfDensityPullback (pmRamanujanPrimitiveSource r)) (-ξ) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [halfDensityPullback_stepSource_eq_primitiveSource_neg, neg_neg]
    congr 2
    ring
  rw [hflip, fourier_halfDensityPullback]
  have hs_eq : (1 / 2 - 2 * ↑Real.pi * ↑(-ξ) * Complex.I : ℂ) =
      (1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hs_eq]
  have hs0 : (0 : ℝ) < ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I).re := by
    simp
  have hs1 : ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I).re < 1 := by
    simp; norm_num
  exact (hasMellin_pmRamanujanPrimitiveSource hr hs0 hs1).2

private theorem norm_pmRamanujanMellinSymbol_half_le (r : ℕ) (t : ℝ) :
    ‖pmRamanujanMellinSymbol r ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∑ x ∈ r.divisorsAntidiagonal,
        ‖(ArithmeticFunction.moebius x.2 : ℂ)‖ * (x.1 : ℝ) ^ (1 / 2 : ℝ) := by
  unfold pmRamanujanMellinSymbol
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hd : 0 < x.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hd]
  have hre : (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re = 1 / 2 := by simp; norm_num
  rw [hre]

private theorem exists_norm_fourier_stepSource_le_inv_rpow {r : ℕ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, 2 ≤ |ξ| →
      ‖𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ‖ ≤
        C * (1 + |ξ|) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨C_conv, hC_conv, hconv⟩ :=
    exists_norm_riemannZeta_le_convexity (η := 1 / 6) (by norm_num) (by norm_num)
  let M_sym : ℝ := ∑ x ∈ r.divisorsAntidiagonal,
    ‖(ArithmeticFunction.moebius x.2 : ℂ)‖ * (x.1 : ℝ) ^ (1 / 2 : ℝ)
  have hM_nn : 0 ≤ M_sym := Finset.sum_nonneg fun x _ => by positivity
  refine ⟨4 * C_conv * (2 * Real.pi) ^ (1 / 3 : ℝ) * (M_sym + 1), by positivity, fun ξ hξ2 => ?_⟩
  have hnorm_abs : ‖𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ‖ =
      ‖𝓕 (halfDensityPullback (pmRamanujanStepSource r)) |ξ|‖ := by
    rcases le_total 0 ξ with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_nonpos h0, fourier_halfDensityPullback_stepSource_neg, RCLike.norm_conj]
  rw [hnorm_abs, fourier_halfDensityPullback_stepSource_eq_mellin hr |ξ|]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have ht8 : 8 ≤ 2 * Real.pi * |ξ| := by nlinarith
  have ht_pos : 0 < 2 * Real.pi * |ξ| := by positivity
  have h1ξ_pos : 0 < 1 + |ξ| := by positivity
  have hzeta := hconv (1 / 2) (2 * Real.pi * |ξ|) (by norm_num) (by norm_num) ht8
  rw [show (1 + 1 / 6 - 1 / 2) / 2 = (1 / 3 : ℝ) by norm_num,
    show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num] at hzeta
  have hs_norm : (1 / 4 : ℝ) * (1 + |ξ|) ≤
      ‖(1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I‖ := by
    have hre := Complex.abs_re_le_norm ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)
    have him := Complex.abs_im_le_norm ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)
    have hre_eq : ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by
      simp [Complex.add_re, Complex.mul_re]
    have him_eq : ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I).im =
        2 * Real.pi * |ξ| := by
      simp [Complex.add_im, Complex.mul_im]
    rw [hre_eq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hre
    rw [him_eq, abs_of_pos ht_pos] at him
    nlinarith
  have hsym := norm_pmRamanujanMellinSymbol_half_le r (2 * Real.pi * |ξ|)
  have hsym' : ‖pmRamanujanMellinSymbol r
      ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)‖ ≤ M_sym + 1 :=
    hsym.trans (by dsimp [M_sym]; linarith)
  have ht_rpow : (2 * Real.pi * |ξ|) ^ (1 / 3 : ℝ) ≤
      (2 * Real.pi) ^ (1 / 3 : ℝ) * (1 + |ξ|) ^ (1 / 3 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (abs_nonneg ξ)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg ξ) (by linarith) (by norm_num)) (by positivity)
  rw [norm_mul, norm_div]
  have hquot : ‖riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)‖ /
      ‖(1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I‖ ≤
      4 * C_conv * (2 * Real.pi) ^ (1 / 3 : ℝ) * (1 + |ξ|) ^ (-(2 / 3 : ℝ)) := by
    have hs_pos : 0 < ‖(1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I‖ := by linarith
    rw [div_le_iff₀ hs_pos]
    have hrpow_id : (1 + |ξ|) ^ (-(2 / 3 : ℝ)) * (1 + |ξ|) = (1 + |ξ|) ^ (1 / 3 : ℝ) := by
      calc (1 + |ξ|) ^ (-(2 / 3 : ℝ)) * (1 + |ξ|)
          = (1 + |ξ|) ^ (-(2 / 3 : ℝ)) * (1 + |ξ|) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (1 + |ξ|) ^ (-(2 / 3 : ℝ) + 1) := (Real.rpow_add h1ξ_pos _ _).symm
        _ = (1 + |ξ|) ^ (1 / 3 : ℝ) := by norm_num
    calc ‖riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)‖
        ≤ C_conv * (2 * Real.pi * |ξ|) ^ (1 / 3 : ℝ) := hzeta
      _ ≤ C_conv * ((2 * Real.pi) ^ (1 / 3 : ℝ) * (1 + |ξ|) ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left ht_rpow hC_conv.le
      _ = 4 * C_conv * (2 * Real.pi) ^ (1 / 3 : ℝ) * (1 + |ξ|) ^ (-(2 / 3 : ℝ)) *
            ((1 / 4 : ℝ) * (1 + |ξ|)) := by
          rw [← hrpow_id]; ring
      _ ≤ 4 * C_conv * (2 * Real.pi) ^ (1 / 3 : ℝ) * (1 + |ξ|) ^ (-(2 / 3 : ℝ)) *
            ‖(1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I‖ :=
          mul_le_mul_of_nonneg_left hs_norm (by positivity)
  calc ‖riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)‖ /
        ‖(1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I‖ *
        ‖pmRamanujanMellinSymbol r ((1 / 2 : ℂ) + ((2 * Real.pi * |ξ| : ℝ) : ℂ) * Complex.I)‖
      ≤ (4 * C_conv * (2 * Real.pi) ^ (1 / 3 : ℝ) * (1 + |ξ|) ^ (-(2 / 3 : ℝ))) * (M_sym + 1) :=
        mul_le_mul hquot hsym' (norm_nonneg _) (by positivity)
    _ = 4 * C_conv * (2 * Real.pi) ^ (1 / 3 : ℝ) * (M_sym + 1) *
          (1 + |ξ|) ^ (-(2 / 3 : ℝ)) := by ring

/-- **Pointwise `O_r((1 + |ξ|)^{-4/3})` bound on `stepSpectralWeight` almost everywhere.** -/
theorem stepSpectralWeight_ae_le_inv_rpow {r : ℕ} (hr : 1 < r) :
    ∃ C_W : ℝ, 0 < C_W ∧ ∀ᵐ ξ : ℝ ∂volume,
      stepSpectralWeight hr ξ ≤ C_W * (1 + |ξ|) ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨C₁, hC₁, hhi⟩ := exists_norm_fourier_stepSource_le_inv_rpow hr
  have hint_pull : Integrable (halfDensityPullback (pmRamanujanStepSource r)) := by
    have hae_ne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [Filter.eventually_iff, mem_ae_iff]; simp
    have hg_int : Integrable ((Ioi (0 : ℝ)).indicator
        (fun x : ℝ => pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * x))) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr
        ((integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0).const_mul _)
    have hmeas : Measurable (halfDensityPullback (pmRamanujanStepSource r)) :=
      (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp Real.measurable_exp)).mul
        ((measurable_stepFun _).comp Real.measurable_exp)
    refine hg_int.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hae_ne] with x hx0
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      have hb : ∀ N : ℕ, |(pmRamanujanPrimitive r N).re| ≤ pmRamanujanPrimitiveBound r :=
        fun N => (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr N)
      unfold halfDensityPullback pmRamanujanStepSource
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        sqrt_exp_eq_half]
      calc Real.exp (x / 2) * ‖stepFun (fun N => (pmRamanujanPrimitive r N).re) (Real.exp x)‖
          ≤ Real.exp (x / 2) * (pmRamanujanPrimitiveBound r * (Real.exp x)⁻¹) :=
            mul_le_mul_of_nonneg_left (norm_stepFun_le hb (Real.exp_pos x)) (Real.exp_pos _).le
        _ = pmRamanujanPrimitiveBound r * Real.exp (-(1 / 2) * x) := by
            rw [← Real.exp_neg, mul_left_comm (Real.exp (x / 2)), ← Real.exp_add]
            congr 1; congr 1; ring
    · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
      have hexp : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hneg
      have h0 : halfDensityPullback (pmRamanujanStepSource r) x = 0 := by
        simp [halfDensityPullback, pmRamanujanStepSource, stepFun,
          Nat.floor_eq_zero.mpr hexp, pmRamanujanPrimitive]
      rw [h0, norm_zero, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
  have hU : (halfLineExpUnitary (stepHalfLine hr) : ℝ → ℂ) =ᵐ[volume]
      halfDensityPullback (pmRamanujanStepSource r) :=
    halfLineExpUnitary_ae_halfDensityPullback (stepHalfLine_ae_eq hr)
  have hF := coeFn_fourierTransform_eq_fourierIntegral (halfLineExpUnitary (stepHalfLine hr))
    (hint_pull.congr hU.symm)
  change ((halfLineMellinUnitary (stepHalfLine hr) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
    _ at hF
  let C_W : ℝ := max (36 * pmRamanujanPrimitiveBound r ^ 2 + 1) (C₁ ^ 2)
  refine ⟨C_W, by positivity, ?_⟩
  filter_upwards [stepSpectralWeight_ae_le hr, hF] with ξ hlow hξ
  have h1ξ_pos : 0 < 1 + |ξ| := by positivity
  by_cases h2 : 2 ≤ |ξ|
  · unfold stepSpectralWeight
    rw [hξ, Real.fourier_congr_ae hU ξ]
    have hpt := hhi ξ h2
    have hsq : ((1 + |ξ|) ^ (-(2 / 3 : ℝ))) ^ 2 = (1 + |ξ|) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h1ξ_pos.le]
      norm_num
    calc ‖𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ‖ ^ 2
        ≤ (C₁ * (1 + |ξ|) ^ (-(2 / 3 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpt 2
      _ = C₁ ^ 2 * (1 + |ξ|) ^ (-(4 / 3 : ℝ)) := by rw [mul_pow, hsq]
      _ ≤ C_W * (1 + |ξ|) ^ (-(4 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hlt2 : 1 + |ξ| ≤ 3 := by linarith [not_le.mp h2]
    have hrpow_lo : (1 / 9 : ℝ) ≤ (1 + |ξ|) ^ (-(4 / 3 : ℝ)) := by
      calc (1 / 9 : ℝ) = (3 : ℝ) ^ (-2 : ℝ) := by norm_num
        _ ≤ (3 : ℝ) ^ (-(4 / 3 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ (1 + |ξ|) ^ (-(4 / 3 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos h1ξ_pos hlt2 (by norm_num)
    have hC_lo : 36 * pmRamanujanPrimitiveBound r ^ 2 ≤ C_W :=
      (by linarith : 36 * pmRamanujanPrimitiveBound r ^ 2 ≤
        36 * pmRamanujanPrimitiveBound r ^ 2 + 1).trans (le_max_left _ _)
    calc stepSpectralWeight hr ξ
        ≤ 4 * pmRamanujanPrimitiveBound r ^ 2 := hlow
      _ = (36 * pmRamanujanPrimitiveBound r ^ 2) * (1 / 9 : ℝ) := by ring
      _ ≤ C_W * (1 + |ξ|) ^ (-(4 / 3 : ℝ)) :=
          mul_le_mul hC_lo hrpow_lo (by norm_num) (by positivity)

/-! ## §2. Pole-free subset log-product bound across all `w ≥ 3` and `t : ℝ` -/

private theorem primesLE_subset_primesLE {a b : ℕ} (hab : a ≤ b) :
    Nat.primesLE a ⊆ Nat.primesLE b := by
  intro p hp
  obtain ⟨hpa, hp'⟩ := Nat.mem_primesLE.mp hp
  exact Nat.mem_primesLE.mpr ⟨hpa.trans hab, hp'⟩

private theorem exists_zetaEntire_pole_box_bounds :
    ∃ c_box M_box : ℝ, 0 < c_box ∧ 1 ≤ M_box ∧
      ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (-1 : ℝ) 1,
        c_box ≤ ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ∧
          ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ M_box := by
  have hmap : Continuous (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  let B_box : Set ℂ :=
    (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) '' (Icc (1 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1)
  have hB_compact : IsCompact B_box := (isCompact_Icc.prod isCompact_Icc).image hmap
  have hB_ne_zero : ∀ s ∈ B_box, RHTower.zetaEntire s ≠ 0 := by
    rintro s ⟨⟨σ, u⟩, ⟨hσ, _⟩, rfl⟩
    refine RHTower.Sieve.zetaEntire_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    exact hσ.1
  have hcont_inv : ContinuousOn (fun s : ℂ => (RHTower.zetaEntire s)⁻¹) B_box :=
    RHTower.differentiable_zetaEntire.continuous.continuousOn.inv₀ hB_ne_zero
  obtain ⟨M_inv, hM_inv⟩ := hB_compact.exists_bound_of_continuousOn hcont_inv
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn
    (RHTower.differentiable_zetaEntire.continuous.continuousOn (s := Metric.closedBall (0 : ℂ) 4))
  let R_inv : ℝ := max 1 M_inv
  have hR_pos : 0 < R_inv := lt_of_lt_of_le zero_lt_one (le_max_left 1 M_inv)
  refine ⟨R_inv⁻¹, max 1 K₀, inv_pos.mpr hR_pos, le_max_left _ _, fun σ hσ u hu => ?_⟩
  have hsB : ((σ : ℂ) + (u : ℂ) * Complex.I) ∈ B_box := ⟨(σ, u), ⟨hσ, hu⟩, rfl⟩
  have hpos_norm : 0 < ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (hB_ne_zero _ hsB)
  have hinv_le : ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖⁻¹ ≤ R_inv := by
    rw [← norm_inv]
    exact (hM_inv _ hsB).trans (le_max_right 1 M_inv)
  refine ⟨(inv_le_comm₀ hR_pos hpos_norm).mpr hinv_le, ?_⟩
  have hmem : ((σ : ℂ) + (u : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖((σ : ℂ) + (u : ℂ) * Complex.I)‖
        ≤ ‖(σ : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |σ| + |u| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 + 1 := by
          have h1s : |σ| ≤ 2 := by rw [abs_of_nonneg (by linarith [hσ.1])]; exact hσ.2
          have h2u : |u| ≤ 1 := abs_le.mpr hu
          linarith
      _ ≤ 4 := by norm_num
  exact (hK₀ _ hmem).trans (le_max_right _ _)

private theorem sum_cos_primesLE_pole_sandwich {c_box M_box : ℝ} (hc0 : 0 < c_box) (hM1 : 1 ≤ M_box)
    (hbox : ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (-1 : ℝ) 1,
      c_box ≤ ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ∧
        ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ M_box)
    {y : ℕ} (hy : 3 ≤ y) {u : ℝ} (hu0 : 0 < |u|) (hu1 : |u| ≤ 1)
    (hyu : 1 / Real.log (y : ℝ) ≤ 2 * |u|) :
    Real.log (c_box / 3) - Real.log |u| -
        (Real.pi ^ 2 / 6 +
          2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
          (1 + Real.log 4)) ≤
      ∑ p ∈ Nat.primesLE y, Real.cos (u * Real.log p) / (p : ℝ) ∧
    ∑ p ∈ Nat.primesLE y, Real.cos (u * Real.log p) / (p : ℝ) ≤
      Real.log M_box - Real.log |u| +
        (Real.pi ^ 2 / 6 +
          2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
          (1 + Real.log 4)) := by
  have hy3 : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy1 : (1 : ℝ) ≤ Real.log (y : ℝ) := by
    have hexp : Real.exp 1 ≤ (y : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hlogy_pos : 0 < Real.log (y : ℝ) := by linarith
  have hσ_mem : 1 + 1 / Real.log (y : ℝ) ∈ Icc (1 : ℝ) 2 :=
    ⟨le_add_of_nonneg_right (by positivity),
     by
      have h1 : 1 / Real.log (y : ℝ) ≤ 1 := div_le_one_of_le₀ hlogy1 hlogy_pos.le
      linarith⟩
  have hu_mem : u ∈ Icc (-1 : ℝ) 1 := abs_le.mp hu1
  have hs1 : (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have him := congrArg Complex.im hcon
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
    exact hu0.ne' (by simp [him])
  have hfac := RHTower.zetaEntire_eq hs1
  have hnorm_lo : |u| ≤ ‖(((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1‖ := by
    have hle := Complex.abs_im_le_norm
      ((((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1)
    have him : ((((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1).im = u := by
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.one_im, sub_zero]
    rwa [him] at hle
  have hnorm_hi :
      ‖(((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1‖ ≤ 3 * |u| := by
    have hrw : (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1 =
        (((1 / Real.log (y : ℝ) : ℝ)) : ℂ) + (u : ℂ) * Complex.I := by
      push_cast; ring
    rw [hrw]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hent_lo, hent_hi⟩ := hbox (1 + 1 / Real.log (y : ℝ)) hσ_mem u hu_mem
  rw [hfac, norm_mul] at hent_lo hent_hi
  have hζ_hi :
      ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        M_box / |u| := by
    rw [le_div_iff₀ hu0]
    calc ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ * |u|
        = |u| * ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ :=
          mul_comm _ _
      _ ≤ ‖(((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1‖ *
            ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right hnorm_lo (norm_nonneg _)
      _ ≤ M_box := hent_hi
  have hζ_lo :
      c_box / (3 * |u|) ≤
        ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ := by
    rw [div_le_iff₀ (by positivity)]
    calc c_box
        ≤ ‖(((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1‖ *
            ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ := hent_lo
      _ ≤ 3 * |u| *
            ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right hnorm_hi (norm_nonneg _)
      _ = ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ *
            (3 * |u|) := mul_comm _ _
  constructor
  · have hσ1 : (1 : ℝ) < 1 + 1 / Real.log (y : ℝ) := by
      have : (0 : ℝ) < 1 / Real.log (y : ℝ) := by positivity
      linarith
    have hlog_lo : Real.log (c_box / 3) - Real.log |u| ≤
        Real.log ‖riemannZeta (((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ := by
      have h := Real.log_le_log (by positivity) hζ_lo
      have hdiv : c_box / (3 * |u|) = (c_box / 3) / |u| := by ring
      rwa [hdiv, Real.log_div (by positivity) hu0.ne'] at h
    have htsum := RHTower.Sieve.le_tsum_re_prime_cpow_of_log_le hσ1 hlog_lo
    have hcos := RHTower.Sieve.sum_cos_div_prime_ge_of_le hy htsum
    linarith
  · have hcos := sum_cos_div_prime_le_of_zeta_upper (z := y) (u := u) (B := M_box / |u|) hy hζ_hi
    rw [Real.log_div (by linarith) hu0.ne'] at hcos
    linarith

/-- **Pole-free subset log-Euler-product bound across all `w ≥ 3` and all `t : ℝ`.** -/
theorem exists_subset_neg_two_cos_le_pole_free :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ w : ℕ, 3 ≤ w → ∀ S' : Finset ℕ, S' ⊆ Nat.primesLE w → ∀ t : ℝ,
      ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
        C₀ + 12 * Real.log (Real.log (|t| + Real.exp 1)) +
          17 / 24 * Real.log (Real.log (w : ℝ)) := by
  obtain ⟨C₁, hC₁0, hcos1⟩ := exists_neg_sum_cos_div_primesLE_le
  obtain ⟨c_box, M_box, hc0, hM1, hbox⟩ := exists_zetaEntire_pole_box_bounds
  let C_pass : ℝ := Real.pi ^ 2 / 6 +
    2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
    (1 + Real.log 4)
  let C_win : ℝ := |Real.log M_box - Real.log (c_box / 3)| + 2 * C_pass
  let C₀ : ℝ := 17 / 24 * |RHTower.Sieve.mertensSecondUpperConst| +
    C₁ + C_pass + Real.log 5 + 2 * C_win + 1
  have hC_pass_nn : 0 ≤ C_pass := by
    dsimp [C_pass]
    have hm := RHTower.Sieve.mertensFirstConst_nonneg
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hC_win_nn : 0 ≤ C_win := by dsimp [C_win]; positivity
  have hlog5_nn : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  refine ⟨C₀, by dsimp [C₀]; positivity, fun w hw S' hS' t => ?_⟩
  have hw3 : (3 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hlogw1 : (1 : ℝ) ≤ Real.log (w : ℝ) := by
    have hexp : Real.exp 1 ≤ (w : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hlogw_pos : 0 < Real.log (w : ℝ) := by linarith
  have hloglogw_nn : 0 ≤ Real.log (Real.log (w : ℝ)) := Real.log_nonneg hlogw1
  have hL1 : 1 ≤ Real.log (|t| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
    rwa [Real.log_exp] at h
  have hL_pos : 0 < Real.log (|t| + Real.exp 1) := by linarith
  have hlogL_nn : 0 ≤ Real.log (Real.log (|t| + Real.exp 1)) := Real.log_nonneg hL1
  have hmert := RHTower.Sieve.mertensS_le (by omega : 2 ≤ w)
  unfold RHTower.Sieve.mertensS RHTower.Sieve.logLog at hmert
  have hmert_abs : 17 / 24 * (∑ p ∈ Nat.primesLE w, 1 / (p : ℝ)) ≤
      17 / 24 * Real.log (Real.log (w : ℝ)) +
        17 / 24 * |RHTower.Sieve.mertensSecondUpperConst| := by
    linarith [hmert, le_abs_self RHTower.Sieve.mertensSecondUpperConst]
  by_cases ht_half : 1 / 2 ≤ |t|
  · have hσ_mem : 1 + 1 / Real.log (w : ℝ) ∈ Icc (1 : ℝ) 2 :=
      ⟨le_add_of_nonneg_right (by positivity),
       by
        have h1 : 1 / Real.log (w : ℝ) ≤ 1 := div_le_one_of_le₀ hlogw1 hlogw_pos.le
        linarith⟩
    have hre : (((1 + 1 / Real.log (w : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re =
        1 + 1 / Real.log (w : ℝ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    have him : (((1 + 1 / Real.log (w : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).im =
        2 * t := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    have him_abs :
        |(((1 + 1 / Real.log (w : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).im| = 2 * |t| := by
      rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hzeta_hi := RHTower.Sieve.norm_riemannZeta_ge_one_log_le
      (w := ((1 + 1 / Real.log (w : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
      (by rw [hre]; exact hσ_mem.1) (by rw [hre]; exact hσ_mem.2) (by rw [him_abs]; linarith)
    rw [him_abs] at hzeta_hi
    have hB_le : 3 + Real.log (4 + 2 * |t|) ≤ 5 * Real.log (|t| + Real.exp 1) := by
      have harg : 4 + 2 * |t| ≤ 2 * (|t| + Real.exp 1) := by
        linarith [Real.exp_one_gt_d9]
      have hlog_arg : Real.log (4 + 2 * |t|) ≤ Real.log 2 + Real.log (|t| + Real.exp 1) :=
        (Real.log_le_log (by positivity) harg).trans_eq
          (Real.log_mul (by norm_num) (by linarith [Real.exp_pos 1]))
      have hlog2 : Real.log 2 ≤ 1 := by
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h := Real.log_le_log (by norm_num) he1
        rwa [Real.log_exp] at h
      linarith
    have hcos2 := sum_cos_div_prime_le_of_zeta_upper (z := w) (u := 2 * t)
      (B := 5 * Real.log (|t| + Real.exp 1)) hw (hzeta_hi.trans hB_le)
    rw [Real.log_mul (by norm_num) hL_pos.ne'] at hcos2
    have hcos2' : ∑ p ∈ Nat.primesLE w, Real.cos (2 * t * Real.log p) / (p : ℝ) ≤
        Real.log 5 + Real.log (Real.log (|t| + Real.exp 1)) + C_pass := by
      dsimp [C_pass]; linarith [hcos2]
    have hmaj : ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
        17 / 24 * (∑ p ∈ Nat.primesLE w, 1 / (p : ℝ)) -
          (∑ p ∈ Nat.primesLE w, Real.cos (t * Real.log p) / (p : ℝ)) +
          1 / 3 * (∑ p ∈ Nat.primesLE w, Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
      calc ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ))
          ≤ ∑ p ∈ S', (17 / 24 - Real.cos (t * Real.log p) +
              1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
            Finset.sum_le_sum fun p _ =>
              div_le_div_of_nonneg_right (two_squares_cos_majorant (t * Real.log p)).2
                (Nat.cast_nonneg p)
        _ ≤ ∑ p ∈ Nat.primesLE w, (17 / 24 - Real.cos (t * Real.log p) +
              1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hS' fun p _ _ =>
              div_nonneg (two_squares_cos_majorant (t * Real.log p)).1 (Nat.cast_nonneg p)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring]; ring
    have hc1 := hcos1 w t
    dsimp [C₀]
    linarith [hmaj, hmert_abs, hc1, hcos2']
  · have ht_lt : |t| < 1 / 2 := not_le.mp ht_half
    by_cases htw : |t| * Real.log (w : ℝ) ≤ 1
    · have hnonpos : ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤ 0 := by
        refine Finset.sum_nonpos fun p hp => ?_
        obtain ⟨hpw, hp'⟩ := Nat.mem_primesLE.mp (hS' hp)
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
        have hlogp_le : Real.log (p : ℝ) ≤ Real.log (w : ℝ) :=
          Real.log_le_log hp_pos (by exact_mod_cast hpw)
        have habs_arg : |t * Real.log p| ≤ Real.pi / 2 := by
          rw [abs_mul, abs_of_nonneg hlogp_nn]
          calc |t| * Real.log (p : ℝ) ≤ |t| * Real.log (w : ℝ) :=
                mul_le_mul_of_nonneg_left hlogp_le (abs_nonneg t)
            _ ≤ 1 := htw
            _ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
        have hcos_nn : 0 ≤ Real.cos (t * Real.log p) :=
          Real.cos_nonneg_of_mem_Icc (abs_le.mp habs_arg)
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hp_pos.le
      have hC0_nn : 0 ≤ C₀ := by dsimp [C₀]; positivity
      linarith
    · have htw_gt : 1 < |t| * Real.log (w : ℝ) := not_le.mp htw
      have ht_pos : 0 < |t| := by
        by_contra hle
        have ht0 : |t| = 0 := le_antisymm (not_lt.mp hle) (abs_nonneg t)
        rw [ht0, zero_mul] at htw_gt
        linarith
      let w₀ : ℕ := ⌊Real.exp (1 / |t|)⌋₊
      have h_inv_gt2 : 2 < 1 / |t| := by
        rw [lt_div_iff₀ ht_pos]; linarith
      have hexp_gt7 : 7 < Real.exp (1 / |t|) := by
        have he2 : (7 : ℝ) < Real.exp 2 := by
          have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith
        exact he2.trans (Real.exp_lt_exp.mpr h_inv_gt2)
      have hw₀_ge7 : 7 ≤ w₀ := Nat.le_floor hexp_gt7.le
      have hw₀_ge3 : 3 ≤ w₀ := by omega
      have hw₀_le_w : w₀ ≤ w := by
        have hlt : 1 / |t| < Real.log (w : ℝ) := (div_lt_iff₀ ht_pos).mpr (by linarith)
        have hexp_lt_w : Real.exp (1 / |t|) < (w : ℝ) := by
          simpa [Real.exp_log (by positivity : (0 : ℝ) < w)] using Real.exp_lt_exp.mpr hlt
        exact_mod_cast (Nat.floor_le (Real.exp_pos _).le).trans hexp_lt_w.le
      have hw₀_log_inv : 1 / Real.log (w₀ : ℝ) ≤ 2 * |t| := by
        have hlt_succ : Real.exp (1 / |t|) < (w₀ : ℝ) + 1 := Nat.lt_floor_add_one _
        have hsucc_le_sq : (w₀ : ℝ) + 1 ≤ (w₀ : ℝ) ^ 2 := by
          have hw₀R : (7 : ℝ) ≤ w₀ := by exact_mod_cast hw₀_ge7
          nlinarith
        have hlog_sq : 1 / |t| < 2 * Real.log (w₀ : ℝ) := by
          have h := Real.log_lt_log (Real.exp_pos _) (hlt_succ.trans_le hsucc_le_sq)
          rwa [Real.log_exp, Real.log_pow, Nat.cast_ofNat] at h
        have hlogw₀_pos : 0 < Real.log (w₀ : ℝ) := by linarith [div_pos one_pos ht_pos]
        rw [div_le_iff₀ hlogw₀_pos]
        have hmul := (div_lt_iff₀ ht_pos).mp hlog_sq
        linarith
      have hsplit_S' : ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) =
          (∑ p ∈ S' \ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ))) +
            ∑ p ∈ S' ∩ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S' (Nat.primesLE w₀)),
          Finset.sdiff_union_inter]
      have hhead_nonpos :
          ∑ p ∈ S' ∩ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤ 0 := by
        refine Finset.sum_nonpos fun p hp => ?_
        obtain ⟨hpw₀, hp'⟩ := Nat.mem_primesLE.mp (Finset.mem_inter.mp hp).2
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
        have hlogp_le : Real.log (p : ℝ) ≤ 1 / |t| := by
          have hp_le_exp : (p : ℝ) ≤ Real.exp (1 / |t|) :=
            (show (p : ℝ) ≤ w₀ by exact_mod_cast hpw₀).trans (Nat.floor_le (Real.exp_pos _).le)
          simpa [Real.log_exp] using Real.log_le_log hp_pos hp_le_exp
        have habs_arg : |t * Real.log p| ≤ Real.pi / 2 := by
          rw [abs_mul, abs_of_nonneg hlogp_nn]
          calc |t| * Real.log (p : ℝ) ≤ |t| * (1 / |t|) :=
                mul_le_mul_of_nonneg_left hlogp_le ht_pos.le
            _ = 1 := mul_one_div_cancel ht_pos.ne'
            _ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
        have hcos_nn : 0 ≤ Real.cos (t * Real.log p) :=
          Real.cos_nonneg_of_mem_Icc (abs_le.mp habs_arg)
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hp_pos.le
      have hsdiff_sub : S' \ Nat.primesLE w₀ ⊆ Nat.primesLE w \ Nat.primesLE w₀ :=
        Finset.sdiff_subset_sdiff hS' Subset.rfl
      have htail_maj : ∑ p ∈ S' \ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
          17 / 24 * (∑ p ∈ Nat.primesLE w, 1 / (p : ℝ)) -
            (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, Real.cos (t * Real.log p) / (p : ℝ)) +
            1 / 3 * (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
              Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
        have h1 : ∑ p ∈ S' \ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
            ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
              (17 / 24 - Real.cos (t * Real.log p) +
                1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) := by
          calc ∑ p ∈ S' \ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ))
              ≤ ∑ p ∈ S' \ Nat.primesLE w₀,
                  (17 / 24 - Real.cos (t * Real.log p) +
                    1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
                Finset.sum_le_sum fun p _ =>
                  div_le_div_of_nonneg_right (two_squares_cos_majorant (t * Real.log p)).2
                    (Nat.cast_nonneg p)
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsdiff_sub fun p _ _ =>
                  div_nonneg (two_squares_cos_majorant (t * Real.log p)).1 (Nat.cast_nonneg p)
        have h2 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
            (17 / 24 - Real.cos (t * Real.log p) +
              1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) =
            17 / 24 * (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, 1 / (p : ℝ)) -
              (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, Real.cos (t * Real.log p) / (p : ℝ)) +
              1 / 3 * (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
                Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring]; ring
        have h3 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, 1 / (p : ℝ) ≤
            ∑ p ∈ Nat.primesLE w, 1 / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => 1 / (p : ℝ))
            Finset.sdiff_subset fun _ _ _ => by positivity
        linarith
      have hw_log_inv : 1 / Real.log (w : ℝ) ≤ 2 * |t| :=
        (div_le_div_of_nonneg_left zero_le_one
          (Real.log_pos (by exact_mod_cast (by omega : 1 < w₀)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < w₀))
            (by exact_mod_cast hw₀_le_w))).trans hw₀_log_inv
      have hsand_w_1 := sum_cos_primesLE_pole_sandwich hc0 hM1 hbox hw ht_pos
        (by linarith) hw_log_inv
      have hsand_w₀_1 := sum_cos_primesLE_pole_sandwich hc0 hM1 hbox hw₀_ge3 ht_pos
        (by linarith) hw₀_log_inv
      have h2t_pos : 0 < |2 * t| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; positivity
      have h2t_le1 : |2 * t| ≤ 1 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      have hw_log_inv2 : 1 / Real.log (w : ℝ) ≤ 2 * |2 * t| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      have hw₀_log_inv2 : 1 / Real.log (w₀ : ℝ) ≤ 2 * |2 * t| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      have hsand_w_2 := sum_cos_primesLE_pole_sandwich hc0 hM1 hbox hw h2t_pos h2t_le1 hw_log_inv2
      have hsand_w₀_2 := sum_cos_primesLE_pole_sandwich hc0 hM1 hbox hw₀_ge3 h2t_pos h2t_le1
        hw₀_log_inv2
      have hsdiff_eq1 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
          Real.cos (t * Real.log p) / (p : ℝ) =
          (∑ p ∈ Nat.primesLE w, Real.cos (t * Real.log p) / (p : ℝ)) -
            ∑ p ∈ Nat.primesLE w₀, Real.cos (t * Real.log p) / (p : ℝ) :=
        Finset.sum_sdiff_eq_sub (primesLE_subset_primesLE hw₀_le_w)
      have hsdiff_eq2 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
          Real.cos (2 * t * Real.log p) / (p : ℝ) =
          (∑ p ∈ Nat.primesLE w, Real.cos (2 * t * Real.log p) / (p : ℝ)) -
            ∑ p ∈ Nat.primesLE w₀, Real.cos (2 * t * Real.log p) / (p : ℝ) :=
        Finset.sum_sdiff_eq_sub (primesLE_subset_primesLE hw₀_le_w)
      have hwin1 : -(∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
          Real.cos (t * Real.log p) / (p : ℝ)) ≤ C_win := by
        rw [hsdiff_eq1]
        dsimp [C_win, C_pass] at hsand_w_1 hsand_w₀_1 ⊢
        linarith [neg_le_abs (Real.log M_box - Real.log (c_box / 3)),
          le_abs_self (Real.log M_box - Real.log (c_box / 3))]
      have hwin2 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
          Real.cos (2 * t * Real.log p) / (p : ℝ) ≤ C_win := by
        rw [hsdiff_eq2]
        dsimp [C_win, C_pass] at hsand_w_2 hsand_w₀_2 ⊢
        linarith [neg_le_abs (Real.log M_box - Real.log (c_box / 3)),
          le_abs_self (Real.log M_box - Real.log (c_box / 3))]
      rw [hsplit_S']
      dsimp [C₀]
      linarith

/-! ## §3. Double-exponential prime shells and translation-invariant unit-interval `L²` decay -/

/-- Double-exponential prime-shell cutoff `⌊exp(exp j)⌋₊`. -/
noncomputable def shellCut (j : ℕ) : ℕ :=
  ⌊Real.exp (Real.exp (j : ℝ))⌋₊

/-- The `j`-th double-exponential shell of a finite prime set `S`. -/
noncomputable def primeShell (S : Finset ℕ) (j : ℕ) : Finset ℕ :=
  S.filter fun p => shellCut j < p ∧ p ≤ shellCut (j + 1)

/-- Shell cosine polynomial `∑_{p ∈ A} cos(t log p) / p`. -/
noncomputable def shellTrig (A : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ A, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)

private theorem shellCut_mono {i j : ℕ} (hij : i ≤ j) : shellCut i ≤ shellCut j :=
  Nat.floor_mono (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by exact_mod_cast hij)))

private theorem seven_le_shellCut {j : ℕ} (hj : 1 ≤ j) : 7 ≤ shellCut j := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have h2_le : (2 : ℝ) ≤ Real.exp (j : ℝ) := by
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith
      _ ≤ Real.exp (j : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast hj)
  exact Nat.le_floor (he2.trans (Real.exp_le_exp.mpr h2_le))

private theorem log_shell_prime_bounds {S : Finset ℕ} {j p : ℕ} (hp : p ∈ primeShell S j) :
    Real.exp (j : ℝ) < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ Real.exp ((j : ℝ) + 1) := by
  have hmem := (Finset.mem_filter.mp hp).2
  have hexp_lt : Real.exp (Real.exp (j : ℝ)) < (p : ℝ) := by
    by_contra hle
    exact not_le_of_gt hmem.1 (Nat.le_floor (not_lt.mp hle))
  have hp_pos : (0 : ℝ) < p := lt_trans (Real.exp_pos _) hexp_lt
  have hp_le : (p : ℝ) ≤ Real.exp (Real.exp ((j : ℝ) + 1)) := by
    calc (p : ℝ) ≤ (shellCut (j + 1) : ℝ) := by exact_mod_cast hmem.2
      _ ≤ Real.exp (Real.exp ((j + 1 : ℕ) : ℝ)) := Nat.floor_le (Real.exp_pos _).le
      _ = Real.exp (Real.exp ((j : ℝ) + 1)) := by push_cast; rfl
  exact ⟨by simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp_lt,
    by simpa [Real.log_exp] using Real.log_le_log hp_pos hp_le⟩

/-- Shifted Fejér-cosine kernel `∫_{-π}^π (1 + cos u) cos((a + u) ω) du`. -/
noncomputable def fejerCosKernel (a ω : ℝ) : ℝ :=
  ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * Real.cos ((a + u) * ω)

private theorem fejerCosKernel_neg (a ω : ℝ) :
    fejerCosKernel a (-ω) = fejerCosKernel a ω := by
  unfold fejerCosKernel
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show (a + u) * (-ω) = -((a + u) * ω) by ring, Real.cos_neg]

private theorem abs_fejerCosKernel_le_eight (a ω : ℝ) : |fejerCosKernel a ω| ≤ 8 := by
  unfold fejerCosKernel
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hint1 : IntervalIntegrable (fun u : ℝ => (1 + Real.cos u) * Real.cos ((a + u) * ω))
      volume (-Real.pi) Real.pi :=
    (by fun_prop : Continuous fun u : ℝ =>
      (1 + Real.cos u) * Real.cos ((a + u) * ω)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u : ℝ => 1 + Real.cos u) volume (-Real.pi) Real.pi :=
    (by fun_prop : Continuous fun u : ℝ => 1 + Real.cos u).intervalIntegrable _ _
  have hprim : ∀ u : ℝ, HasDerivAt (fun x : ℝ => x + Real.sin x) (1 + Real.cos u) u :=
    fun u => (hasDerivAt_id u).add (Real.hasDerivAt_sin u)
  have heval : ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) = 2 * Real.pi := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hprim u) hint2]
    simp [Real.sin_pi]
    ring
  calc |∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * Real.cos ((a + u) * ω)|
      ≤ ∫ u in (-Real.pi)..Real.pi, ‖(1 + Real.cos u) * Real.cos ((a + u) * ω)‖ := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) := by
        refine intervalIntegral.integral_mono_on hle hint1.norm hint2 fun u _ => ?_
        have h1 : 0 ≤ 1 + Real.cos u := by linarith [Real.neg_one_le_cos u]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
        exact mul_le_of_le_one_right h1 (Real.abs_cos_le_one _)
    _ = 2 * Real.pi := heval
    _ ≤ 8 := by linarith [Real.pi_lt_four]

private theorem abs_fejerCosKernel_le_inv_cube (a : ℝ) {ω : ℝ} (hω : 2 ≤ |ω|) :
    |fejerCosKernel a ω| ≤ 3 / |ω| ^ 3 := by
  have hω0 : ω ≠ 0 := by intro h; rw [h, abs_zero] at hω; norm_num at hω
  have hωp1 : ω + 1 ≠ 0 := by
    intro h; have : ω = -1 := by linarith
    rw [this, abs_neg, abs_one] at hω; norm_num at hω
  have hωm1 : ω - 1 ≠ 0 := by
    intro h; have : ω = 1 := by linarith
    rw [this, abs_one] at hω; norm_num at hω
  let F : ℝ → ℝ := fun u =>
    Real.sin (a * ω + ω * u) / ω +
      Real.sin (a * ω + (ω + 1) * u) / (2 * (ω + 1)) +
      Real.sin (a * ω + (ω - 1) * u) / (2 * (ω - 1))
  have hderiv : ∀ u : ℝ,
      HasDerivAt F ((1 + Real.cos u) * Real.cos ((a + u) * ω)) u := by
    intro u
    have hd1 : HasDerivAt (fun x : ℝ => Real.sin (a * ω + ω * x) / ω)
        (Real.cos (a * ω + ω * u)) u := by
      have h := (Real.hasDerivAt_sin (a * ω + ω * u)).comp u
        (((hasDerivAt_id u).const_mul ω).const_add (a * ω))
      exact (h.div_const ω).congr_deriv (by field_simp [hω0])
    have hd2 : HasDerivAt (fun x : ℝ => Real.sin (a * ω + (ω + 1) * x) / (2 * (ω + 1)))
        (Real.cos (a * ω + (ω + 1) * u) / 2) u := by
      have h := (Real.hasDerivAt_sin (a * ω + (ω + 1) * u)).comp u
        (((hasDerivAt_id u).const_mul (ω + 1)).const_add (a * ω))
      exact (h.div_const (2 * (ω + 1))).congr_deriv (by field_simp [hωp1])
    have hd3 : HasDerivAt (fun x : ℝ => Real.sin (a * ω + (ω - 1) * x) / (2 * (ω - 1)))
        (Real.cos (a * ω + (ω - 1) * u) / 2) u := by
      have h := (Real.hasDerivAt_sin (a * ω + (ω - 1) * u)).comp u
        (((hasDerivAt_id u).const_mul (ω - 1)).const_add (a * ω))
      exact (h.div_const (2 * (ω - 1))).congr_deriv (by field_simp [hωm1])
    refine ((hd1.add hd2).add hd3).congr_deriv ?_
    have htrig : Real.cos (a * ω + (ω + 1) * u) + Real.cos (a * ω + (ω - 1) * u) =
        2 * Real.cos u * Real.cos (a * ω + ω * u) := by
      rw [show a * ω + (ω + 1) * u = (a * ω + ω * u) + u by ring,
        show a * ω + (ω - 1) * u = (a * ω + ω * u) - u by ring,
        Real.cos_add, Real.cos_sub]
      ring
    rw [show (a + u) * ω = a * ω + ω * u by ring]
    linarith
  have hint : IntervalIntegrable (fun u : ℝ => (1 + Real.cos u) * Real.cos ((a + u) * ω))
      volume (-Real.pi) Real.pi :=
    (by fun_prop : Continuous fun u : ℝ =>
      (1 + Real.cos u) * Real.cos ((a + u) * ω)).intervalIntegrable _ _
  have hval : fejerCosKernel a ω = F Real.pi - F (-Real.pi) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint
  have hsin_pi1 : Real.sin (a * ω + (ω + 1) * Real.pi) = -Real.sin (a * ω + ω * Real.pi) := by
    rw [show a * ω + (ω + 1) * Real.pi = (a * ω + ω * Real.pi) + Real.pi by ring, Real.sin_add_pi]
  have hsin_pi2 : Real.sin (a * ω + (ω - 1) * Real.pi) = -Real.sin (a * ω + ω * Real.pi) := by
    rw [show a * ω + (ω - 1) * Real.pi = (a * ω + ω * Real.pi) - Real.pi by ring, Real.sin_sub_pi]
  have hsin_npi1 : Real.sin (a * ω + (ω + 1) * (-Real.pi)) =
      -Real.sin (a * ω + ω * (-Real.pi)) := by
    rw [show a * ω + (ω + 1) * (-Real.pi) = (a * ω + ω * (-Real.pi)) - Real.pi by ring,
      Real.sin_sub_pi]
  have hsin_npi2 : Real.sin (a * ω + (ω - 1) * (-Real.pi)) =
      -Real.sin (a * ω + ω * (-Real.pi)) := by
    rw [show a * ω + (ω - 1) * (-Real.pi) = (a * ω + ω * (-Real.pi)) + Real.pi by ring,
      Real.sin_add_pi]
  have hsimpl : F Real.pi - F (-Real.pi) =
      -(Real.sin (a * ω + ω * Real.pi) - Real.sin (a * ω + ω * (-Real.pi))) /
        (ω * (ω ^ 2 - 1)) := by
    dsimp [F]
    rw [hsin_pi1, hsin_pi2, hsin_npi1, hsin_npi2]
    have hωsq : ω ^ 2 - 1 ≠ 0 := by
      have : ω ^ 2 - 1 = (ω + 1) * (ω - 1) := by ring
      rw [this]; exact mul_ne_zero hωp1 hωm1
    field_simp [hω0, hωp1, hωm1, hωsq]
    ring
  rw [hval, hsimpl, abs_div, abs_neg]
  have hnum : |Real.sin (a * ω + ω * Real.pi) - Real.sin (a * ω + ω * (-Real.pi))| ≤ 2 := by
    calc |Real.sin (a * ω + ω * Real.pi) - Real.sin (a * ω + ω * (-Real.pi))|
        ≤ |Real.sin (a * ω + ω * Real.pi)| + |Real.sin (a * ω + ω * (-Real.pi))| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  have hω_sq4 : 4 ≤ |ω| ^ 2 := by nlinarith
  have hden : (3 / 4 : ℝ) * |ω| ^ 3 ≤ |ω * (ω ^ 2 - 1)| := by
    rw [abs_mul, ← sq_abs, abs_of_pos (by nlinarith : 0 < |ω| ^ 2 - 1)]
    have h1 : (3 / 4 : ℝ) * |ω| ^ 2 ≤ |ω| ^ 2 - 1 := by nlinarith
    calc (3 / 4 : ℝ) * |ω| ^ 3 = |ω| * ((3 / 4 : ℝ) * |ω| ^ 2) := by ring
      _ ≤ |ω| * (|ω| ^ 2 - 1) := mul_le_mul_of_nonneg_left h1 (abs_nonneg ω)
  have hden_pos : 0 < |ω * (ω ^ 2 - 1)| := lt_of_lt_of_le (by positivity) hden
  rw [div_le_div_iff₀ hden_pos (by positivity)]
  calc |Real.sin (a * ω + ω * Real.pi) - Real.sin (a * ω + ω * (-Real.pi))| * |ω| ^ 3
      ≤ 2 * |ω| ^ 3 := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ 3 * ((3 / 4 : ℝ) * |ω| ^ 3) := by nlinarith [pow_nonneg (abs_nonneg ω) 3]
    _ ≤ 3 * |ω * (ω ^ 2 - 1)| := mul_le_mul_of_nonneg_left hden (by norm_num)

private theorem sum_inv_primeShell_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {j : ℕ} (hj : 1 ≤ j) :
    ∑ q ∈ primeShell S j, 1 / (q : ℝ) ≤
      2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) := by
  have ha2 : 2 ≤ shellCut j := le_trans (by norm_num) (seven_le_shellCut hj)
  have hab : shellCut j ≤ shellCut (j + 1) := shellCut_mono (Nat.le_succ j)
  have hsub : primeShell S j ⊆ RHTower.Sieve.bigPrimeSet (shellCut j) (shellCut (j + 1)) := by
    intro q hq
    obtain ⟨hqS, hgt, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, hS q hqS⟩
  have hbig := (abs_le.mp (RHTower.Sieve.abs_sum_inv_bigPrimeSet_sub_le ha2 hab)).2
  have hlog_hi : RHTower.Sieve.logLog (shellCut (j + 1)) ≤ (j : ℝ) + 1 := by
    unfold RHTower.Sieve.logLog
    have hle_exp : (shellCut (j + 1) : ℝ) ≤ Real.exp (Real.exp ((j : ℝ) + 1)) := by
      unfold shellCut
      simpa [Nat.cast_add, Nat.cast_one] using
        (Nat.floor_le (Real.exp_pos (Real.exp ((j + 1 : ℕ) : ℝ))).le)
    have hpos1 : (0 : ℝ) < shellCut (j + 1) := by exact_mod_cast (by omega : 0 < shellCut (j + 1))
    have hlog1 : Real.log (shellCut (j + 1) : ℝ) ≤ Real.exp ((j : ℝ) + 1) := by
      simpa [Real.log_exp] using Real.log_le_log hpos1 hle_exp
    have hpos_log1 : 0 < Real.log (shellCut (j + 1) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < shellCut (j + 1)))
    simpa [Real.log_exp] using Real.log_le_log hpos_log1 hlog1
  have hlog_lo : (j : ℝ) - 1 ≤ RHTower.Sieve.logLog (shellCut j) := by
    unfold RHTower.Sieve.logLog
    have hgt : Real.exp (Real.exp (j : ℝ)) / 2 ≤ (shellCut j : ℝ) := by
      have hlt := Nat.lt_floor_add_one (Real.exp (Real.exp (j : ℝ)))
      change Real.exp (Real.exp (j : ℝ)) < (shellCut j : ℝ) + 1 at hlt
      have h7 : (7 : ℝ) ≤ shellCut j := by exact_mod_cast seven_le_shellCut hj
      linarith
    have hlog_ge : Real.exp (j : ℝ) - Real.log 2 ≤ Real.log (shellCut j : ℝ) := by
      have h := Real.log_le_log (by positivity) hgt
      rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h
    have hlog2 : Real.log 2 ≤ 1 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      simpa [Real.log_exp] using Real.log_le_log (by norm_num) he1
    have hhalf_exp : Real.exp ((j : ℝ) - 1) ≤ Real.exp (j : ℝ) - Real.log 2 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hprod : Real.exp (j : ℝ) = Real.exp 1 * Real.exp ((j : ℝ) - 1) := by
        rw [← Real.exp_add]; congr 1; ring
      have hle_half : 2 * Real.exp ((j : ℝ) - 1) ≤ Real.exp (j : ℝ) := by
        rw [hprod]; exact mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have hexp_ge1 : (1 : ℝ) ≤ Real.exp ((j : ℝ) - 1) :=
        Real.one_le_exp (by linarith)
      linarith
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) (hhalf_exp.trans hlog_ge)
  have hC_nn : 0 ≤ 2 * RHTower.Sieve.mertensFirstConst + 1 / 2 := by
    linarith [RHTower.Sieve.mertensFirstConst_nonneg]
  have hlog_ge1 : ∀ k : ℕ, 1 ≤ k → 1 ≤ Real.log (shellCut k : ℝ) := fun k hk => by
    have hk7 : (3 : ℝ) ≤ shellCut k := by
      have := seven_le_shellCut hk; exact_mod_cast (by omega : 3 ≤ shellCut k)
    have hexp : Real.exp 1 ≤ (shellCut k : ℝ) := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have herr1 : (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log (shellCut (j + 1) : ℝ) ≤
      2 * RHTower.Sieve.mertensFirstConst + 1 / 2 :=
    div_le_self hC_nn (hlog_ge1 (j + 1) (by omega))
  have herr2 : (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) / Real.log (shellCut j : ℝ) ≤
      2 * RHTower.Sieve.mertensFirstConst + 1 / 2 :=
    div_le_self hC_nn (hlog_ge1 j hj)
  have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => 1 / (q : ℝ)) hsub
    fun _ _ _ => by positivity
  linarith

private theorem sum_inv_unit_log_block_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {j q : ℕ} (hj : 1 ≤ j) (hq : q ∈ primeShell S j) (m : ℕ) :
    ∑ p ∈ (primeShell S j).filter
        (fun p => q < p ∧ (m : ℝ) ≤ Real.log (p : ℝ) - Real.log (q : ℝ) ∧
          Real.log (p : ℝ) - Real.log (q : ℝ) < (m : ℝ) + 1), 1 / (p : ℝ) ≤
      4 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) *
        Real.exp (-(j : ℝ)) := by
  have hq8 : 8 ≤ q := by
    have h7 := seven_le_shellCut hj
    have hgt := (Finset.mem_filter.mp hq).2.1
    omega
  have hlogq : Real.exp (j : ℝ) < Real.log (q : ℝ) := (log_shell_prime_bounds hq).1
  let y : ℕ := ⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊ - 1
  have hexp_mq_ge8 : 8 ≤ Real.exp (m : ℝ) * (q : ℝ) := by
    have hm1 : (1 : ℝ) ≤ Real.exp (m : ℝ) := Real.one_le_exp (Nat.cast_nonneg m)
    have hq8R : (8 : ℝ) ≤ q := by exact_mod_cast hq8
    nlinarith
  have hfl_ge8 : 8 ≤ ⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊ := Nat.le_floor hexp_mq_ge8
  have hy_ge7 : 7 ≤ y := by dsimp [y]; omega
  have hy2 : 2 ≤ y := by omega
  have h2y2 : 2 ≤ 2 * y := by omega
  have hy_eq : (⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊ : ℝ) = (y : ℝ) + 1 := by
    dsimp [y]
    rw [Nat.cast_sub (by omega : 1 ≤ ⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊), Nat.cast_one]
    ring
  have hsub : (primeShell S j).filter
      (fun p => q < p ∧ (m : ℝ) ≤ Real.log (p : ℝ) - Real.log (q : ℝ) ∧
        Real.log (p : ℝ) - Real.log (q : ℝ) < (m : ℝ) + 1) ⊆
      RHTower.Sieve.bigPrimeSet y (2 * y) ∪ RHTower.Sieve.bigPrimeSet (2 * y) (2 * (2 * y)) := by
    intro p hp
    obtain ⟨hp_sh, _, hlo_log, hhi_log⟩ := Finset.mem_filter.mp hp
    have hp_prime : p.Prime := hS p (Finset.mem_filter.mp hp_sh).1
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hp_ge_emq : Real.exp (m : ℝ) * (q : ℝ) ≤ (p : ℝ) := by
      have h := Real.exp_le_exp.mpr (show (m : ℝ) + Real.log (q : ℝ) ≤ Real.log (p : ℝ) by linarith)
      rwa [Real.exp_add, Real.exp_log hq_pos, Real.exp_log hp_pos] at h
    have hy_lt_p : y < p := by
      have hfl_le : ⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊ ≤ p := Nat.floor_le_of_le hp_ge_emq
      dsimp [y]; omega
    have hp_lt_4y : p ≤ 2 * (2 * y) := by
      have hp_lt_em1 : (p : ℝ) < Real.exp ((m : ℝ) + 1) * (q : ℝ) := by
        have h := Real.exp_lt_exp.mpr
          (show Real.log (p : ℝ) < ((m : ℝ) + 1) + Real.log (q : ℝ) by linarith)
        rwa [Real.exp_add, Real.exp_log hp_pos, Real.exp_log hq_pos] at h
      have he1_lt3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have hem1 : Real.exp ((m : ℝ) + 1) * (q : ℝ) < 3 * (Real.exp (m : ℝ) * (q : ℝ)) := by
        rw [Real.exp_add, mul_comm (Real.exp (m : ℝ)) (Real.exp 1), mul_assoc]
        exact mul_lt_mul_of_pos_right he1_lt3 (by positivity)
      have hfl_lt : Real.exp (m : ℝ) * (q : ℝ) < (y : ℝ) + 2 := by
        have h1 := Nat.lt_floor_add_one (Real.exp (m : ℝ) * (q : ℝ))
        linarith
      have hy7R : (7 : ℝ) ≤ y := by exact_mod_cast hy_ge7
      have hp_lt_R : (p : ℝ) < ((2 * (2 * y) : ℕ) : ℝ) := by
        push_cast; nlinarith
      exact Nat.le_of_lt (by exact_mod_cast hp_lt_R)
    by_cases hp2y : p ≤ 2 * y
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp2y⟩, hp_prime⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp_lt_4y⟩, hp_prime⟩)
  have hlogy_lo : (1 / 2 : ℝ) * Real.exp (j : ℝ) ≤ Real.log (y : ℝ) := by
    have hy_ge_half : Real.exp (m : ℝ) * (q : ℝ) / 2 ≤ (y : ℝ) := by
      have h1 := Nat.lt_floor_add_one (Real.exp (m : ℝ) * (q : ℝ))
      have hy7R : (7 : ℝ) ≤ y := by exact_mod_cast hy_ge7
      linarith
    have hq_half : (q : ℝ) / 2 ≤ Real.exp (m : ℝ) * (q : ℝ) / 2 := by
      have hm1 : (1 : ℝ) ≤ Real.exp (m : ℝ) := Real.one_le_exp (Nat.cast_nonneg m)
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hlog_ge : Real.log (q : ℝ) - Real.log 2 ≤ Real.log (y : ℝ) := by
      have h := Real.log_le_log (half_pos hq_pos) (hq_half.trans hy_ge_half)
      rwa [Real.log_div hq_pos.ne' (by norm_num)] at h
    have hlog2 : Real.log 2 ≤ 1 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      simpa [Real.log_exp] using Real.log_le_log (by norm_num) he1
    have hej2 : 2 < Real.exp (j : ℝ) := by
      have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      exact (by linarith : (2 : ℝ) < Real.exp 1).trans_le
        (Real.exp_le_exp.mpr (by exact_mod_cast hj))
    linarith
  have hC_dyad_nn : 0 ≤ Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2) := by
    have := RHTower.Sieve.mertensFirstConst_nonneg
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hw1 := RHTower.Sieve.sum_inv_dyadic_window_le hy2
  have hw2 := RHTower.Sieve.sum_inv_dyadic_window_le h2y2
  have hlog_mono : Real.log (y : ℝ) ≤ Real.log ((2 * y : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast (by omega : y ≤ 2 * y))
  have hlogy_pos : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (by positivity) hlogy_lo
  have hw2' : ∑ p ∈ RHTower.Sieve.bigPrimeSet (2 * y) (2 * (2 * y)), 1 / (p : ℝ) ≤
      (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log (y : ℝ) :=
    hw2.trans (div_le_div_of_nonneg_left hC_dyad_nn hlogy_pos hlog_mono)
  calc ∑ p ∈ (primeShell S j).filter
        (fun p => q < p ∧ (m : ℝ) ≤ Real.log (p : ℝ) - Real.log (q : ℝ) ∧
          Real.log (p : ℝ) - Real.log (q : ℝ) < (m : ℝ) + 1), 1 / (p : ℝ)
      ≤ ∑ p ∈ RHTower.Sieve.bigPrimeSet y (2 * y) ∪
          RHTower.Sieve.bigPrimeSet (2 * y) (2 * (2 * y)), 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => 1 / (p : ℝ)) hsub
          fun _ _ _ => by positivity
    _ ≤ (∑ p ∈ RHTower.Sieve.bigPrimeSet y (2 * y), 1 / (p : ℝ)) +
          ∑ p ∈ RHTower.Sieve.bigPrimeSet (2 * y) (2 * (2 * y)), 1 / (p : ℝ) := by
        rw [← Finset.sum_union_inter]
        linarith [show 0 ≤ ∑ p ∈ RHTower.Sieve.bigPrimeSet y (2 * y) ∩
          RHTower.Sieve.bigPrimeSet (2 * y) (2 * (2 * y)), 1 / (p : ℝ) from
          Finset.sum_nonneg fun _ _ => by positivity]
    _ ≤ 2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log (y : ℝ) := by
        rw [mul_div_assoc]; linarith
    _ ≤ 2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) /
          ((1 / 2 : ℝ) * Real.exp (j : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlogy_lo
    _ = 4 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) *
          Real.exp (-(j : ℝ)) := by
        rw [Real.exp_neg]; field_simp; ring

private noncomputable def fejerBlockWeight (m : ℕ) : ℝ :=
  if m < 2 then 8 else 3 / (m : ℝ) ^ 3

private theorem fejerBlockWeight_nonneg (m : ℕ) : 0 ≤ fejerBlockWeight m := by
  unfold fejerBlockWeight
  split_ifs <;> positivity

private theorem sum_fejerBlockWeight_le (M : ℕ) :
    ∑ m ∈ Finset.range M, fejerBlockWeight m ≤ 19 := by
  suffices h : ∑ m ∈ Finset.range M, fejerBlockWeight m ≤ 19 - 3 / max (M : ℝ) 1 by
    have hpos : 0 ≤ 3 / max (M : ℝ) 1 := div_nonneg (by norm_num) (le_max_of_le_right zero_le_one)
    linarith
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    rcases M with _ | _ | k
    · simp [fejerBlockWeight]; norm_num
    · simp [fejerBlockWeight]; norm_num
    · have hM2 : ¬ (k + 2 < 2) := by omega
      have hmax1 : max ((k + 2 : ℕ) : ℝ) 1 = ((k + 2 : ℕ) : ℝ) :=
        max_eq_left (by exact_mod_cast (by omega : 1 ≤ k + 2))
      have hmax2 : max ((k + 2 + 1 : ℕ) : ℝ) 1 = ((k + 2 + 1 : ℕ) : ℝ) :=
        max_eq_left (by exact_mod_cast (by omega : 1 ≤ k + 2 + 1))
      have hfw : fejerBlockWeight (k + 2) = 3 / ((k + 2 : ℕ) : ℝ) ^ 3 := by
        simp [fejerBlockWeight, hM2]
      rw [hmax1] at ih
      rw [hmax2, hfw]
      let m : ℝ := ((k + 2 : ℕ) : ℝ)
      have hm2 : 2 ≤ m := by
        dsimp [m]
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        push_cast; linarith
      have hm_pos : 0 < m := by linarith
      have hm1_pos : 0 < m + 1 := by linarith
      have hstep : 3 / m ^ 3 ≤ 3 / m - 3 / (m + 1) := by
        have hdiff : 3 / m - 3 / (m + 1) = 3 / (m * (m + 1)) := by field_simp; ring
        rw [hdiff]
        refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
        calc m * (m + 1) ≤ m * (m * m) := mul_le_mul_of_nonneg_left (by nlinarith) hm_pos.le
          _ = m ^ 3 := by ring
      have hm_succ : (((k + 2 + 1 : ℕ) : ℝ)) = m + 1 := by dsimp [m]; push_cast; ring
      rw [hm_succ]
      linarith

/-- **Translation-invariant unit-interval `L²` decay of double-exponential prime shells.** -/
theorem exists_unit_L2_primeShell_le :
    ∃ C_L2 : ℝ, 0 < C_L2 ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      ∀ j : ℕ, 1 ≤ j → ∀ a : ℝ,
        ∫ t in Icc (a - 1) (a + 1), (shellTrig (primeShell S j) t) ^ 2 ≤
          C_L2 * Real.exp (-(j : ℝ)) := by
  let C_dyad : ℝ := Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)
  let C_sh : ℝ := 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)
  let C_L2 : ℝ := C_sh ^ 2 + 8 * C_sh + 152 * C_sh * C_dyad + 1
  have hC_dyad_nn : 0 ≤ C_dyad := by
    dsimp [C_dyad]
    linarith [RHTower.Sieve.mertensFirstConst_nonneg, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hC_sh_nn : 0 ≤ C_sh := by
    dsimp [C_sh]; linarith [RHTower.Sieve.mertensFirstConst_nonneg]
  refine ⟨C_L2, by dsimp [C_L2]; positivity, fun S hS j hj a => ?_⟩
  let A := primeShell S j
  have hdom_int : ∫ t in Icc (a - 1) (a + 1), (shellTrig A t) ^ 2 ≤
      2 * ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 := by
    have hsub_pi : Icc (a - 1) (a + 1) ⊆ Icc (a - Real.pi) (a + Real.pi) :=
      Icc_subset_Icc (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
    have hint_big : IntegrableOn
        (fun t : ℝ => 2 * ((1 + Real.cos (t - a)) * (shellTrig A t) ^ 2))
        (Icc (a - Real.pi) (a + Real.pi)) := by
      refine (Continuous.continuousOn ?_).integrableOn_Icc
      unfold shellTrig
      fun_prop
    have hint_small : IntegrableOn (fun t : ℝ => (shellTrig A t) ^ 2) (Icc (a - 1) (a + 1)) := by
      refine (Continuous.continuousOn ?_).integrableOn_Icc
      unfold shellTrig
      fun_prop
    have hstep1 : ∫ t in Icc (a - 1) (a + 1), (shellTrig A t) ^ 2 ≤
        ∫ t in Icc (a - 1) (a + 1),
          2 * ((1 + Real.cos (t - a)) * (shellTrig A t) ^ 2) := by
      refine setIntegral_mono_on hint_small (hint_big.mono_set hsub_pi) measurableSet_Icc
        fun t ht => ?_
      have habs : |t - a| ≤ Real.pi / 2 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1, Real.pi_gt_three], by linarith [ht.2, Real.pi_gt_three]⟩
      have hc_nn : 0 ≤ Real.cos (t - a) := Real.cos_nonneg_of_mem_Icc (abs_le.mp habs)
      nlinarith [sq_nonneg (shellTrig A t)]
    have hstep2 : ∫ t in Icc (a - 1) (a + 1),
          2 * ((1 + Real.cos (t - a)) * (shellTrig A t) ^ 2) ≤
        ∫ t in Icc (a - Real.pi) (a + Real.pi),
          2 * ((1 + Real.cos (t - a)) * (shellTrig A t) ^ 2) := by
      refine setIntegral_mono_set hint_big
        (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t ht => hsub_pi ht)
      exact mul_nonneg (by norm_num)
        (mul_nonneg (by linarith [Real.neg_one_le_cos (t - a)]) (sq_nonneg _))
    have hshift : ∫ t in Icc (a - Real.pi) (a + Real.pi),
          2 * ((1 + Real.cos (t - a)) * (shellTrig A t) ^ 2) =
        2 * ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 := by
      have hle_pi : a - Real.pi ≤ a + Real.pi := by linarith [Real.pi_pos]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hle_pi, intervalIntegral.integral_const_mul]
      congr 1
      have hcomp := intervalIntegral.integral_comp_add_right
        (fun u : ℝ => (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2) (-a)
          (a := a - Real.pi) (b := a + Real.pi)
      rw [show a - Real.pi + -a = -Real.pi by ring,
        show a + Real.pi + -a = Real.pi by ring] at hcomp
      rw [← hcomp]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [show t + -a = t - a by ring, show a + (t - a) = t by ring]
    exact (hstep1.trans hstep2).trans_eq hshift
  have hexact : ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 =
      ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) *
        (1 / 2 * fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ)) +
          1 / 2 * fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))) := by
    have hpt : ∀ u : ℝ, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 =
        ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) *
          (1 / 2 * ((1 + Real.cos u) *
              Real.cos ((a + u) * (Real.log (p : ℝ) - Real.log (q : ℝ)))) +
            1 / 2 * ((1 + Real.cos u) *
              Real.cos ((a + u) * (Real.log (p : ℝ) + Real.log (q : ℝ))))) := by
      intro u
      have hsq : (shellTrig A (a + u)) ^ 2 =
          ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) *
            (Real.cos ((a + u) * Real.log (p : ℝ)) * Real.cos ((a + u) * Real.log (q : ℝ))) := by
        unfold shellTrig
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
      rw [hsq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hprod_cos : Real.cos ((a + u) * Real.log (p : ℝ)) *
          Real.cos ((a + u) * Real.log (q : ℝ)) =
          1 / 2 * Real.cos ((a + u) * (Real.log (p : ℝ) - Real.log (q : ℝ))) +
            1 / 2 * Real.cos ((a + u) * (Real.log (p : ℝ) + Real.log (q : ℝ))) := by
        rw [show (a + u) * (Real.log (p : ℝ) - Real.log (q : ℝ)) =
          (a + u) * Real.log (p : ℝ) - (a + u) * Real.log (q : ℝ) by ring,
          show (a + u) * (Real.log (p : ℝ) + Real.log (q : ℝ)) =
            (a + u) * Real.log (p : ℝ) + (a + u) * Real.log (q : ℝ) by ring,
          Real.cos_sub, Real.cos_add]
        ring
      rw [hprod_cos]; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun p _ => ?_
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have hi1 : IntervalIntegrable
            (fun u : ℝ => 1 / 2 * ((1 + Real.cos u) *
              Real.cos ((a + u) * (Real.log (p : ℝ) - Real.log (q : ℝ)))))
            volume (-Real.pi) Real.pi :=
          (by fun_prop : Continuous _).intervalIntegrable _ _
        have hi2 : IntervalIntegrable
            (fun u : ℝ => 1 / 2 * ((1 + Real.cos u) *
              Real.cos ((a + u) * (Real.log (p : ℝ) + Real.log (q : ℝ)))))
            volume (-Real.pi) Real.pi :=
          (by fun_prop : Continuous _).intervalIntegrable _ _
        rw [intervalIntegral.integral_add hi1 hi2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rfl
      · intro p _
        exact (by fun_prop : Continuous _).intervalIntegrable _ _
    · intro q _
      exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsh_sum : ∑ q ∈ A, 1 / (q : ℝ) ≤ C_sh := sum_inv_primeShell_le hS hj
  have hsh_nn : 0 ≤ ∑ q ∈ A, 1 / (q : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  -- Sum-frequency contribution `≤ C_sh^2 * exp(-j)`
  have hsum_freq : ∑ q ∈ A, ∑ p ∈ A,
      (1 / ((q : ℝ) * (p : ℝ))) *
        |fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))| ≤
      C_sh ^ 2 * Real.exp (-(j : ℝ)) := by
    have hpt_sum : ∀ q ∈ A, ∀ p ∈ A,
        |fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))| ≤ Real.exp (-(j : ℝ)) := by
      intro q hq p hp
      have hlogq := (log_shell_prime_bounds hq).1
      have hlogp := (log_shell_prime_bounds hp).1
      have hej2 : (2 : ℝ) ≤ Real.exp (j : ℝ) := by
        calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          _ ≤ Real.exp (j : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast hj)
      have hω2 : 2 ≤ |Real.log (p : ℝ) + Real.log (q : ℝ)| := by
        rw [abs_of_pos (by linarith)]
        linarith
      have h2ej : 2 * Real.exp (j : ℝ) ≤ |Real.log (p : ℝ) + Real.log (q : ℝ)| := by
        rw [abs_of_pos (by linarith)]
        linarith
      calc |fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))|
          ≤ 3 / |Real.log (p : ℝ) + Real.log (q : ℝ)| ^ 3 :=
            abs_fejerCosKernel_le_inv_cube a hω2
        _ ≤ 3 / (2 * Real.exp (j : ℝ)) ^ 3 :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (pow_le_pow_left₀ (by positivity) h2ej 3)
        _ = (3 / 8 : ℝ) * Real.exp (-3 * (j : ℝ)) := by
            rw [mul_pow, ← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * (j : ℝ) = 3 * (j : ℝ) by norm_num,
              show -3 * (j : ℝ) = -(3 * (j : ℝ)) by ring, Real.exp_neg]
            ring
        _ ≤ 1 * Real.exp (-(j : ℝ)) := by
            refine mul_le_mul (by norm_num) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le zero_le_one
            have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
            linarith
        _ = Real.exp (-(j : ℝ)) := one_mul _
    calc ∑ q ∈ A, ∑ p ∈ A,
          (1 / ((q : ℝ) * (p : ℝ))) *
            |fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))|
        ≤ ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) * Real.exp (-(j : ℝ)) :=
          Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (hpt_sum q hq p hp) (by positivity)
      _ = ((∑ q ∈ A, 1 / (q : ℝ)) ^ 2) * Real.exp (-(j : ℝ)) := by
          simp_rw [← Finset.sum_mul]
          congr 1
          rw [sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
      _ ≤ C_sh ^ 2 * Real.exp (-(j : ℝ)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsh_nn hsh_sum 2) (Real.exp_pos _).le
  -- Off-diagonal upper-triangular sum for fixed `q ∈ A`
  have hinner_diff : ∀ q ∈ A,
      ∑ p ∈ A.filter (q < ·),
        |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ) ≤
        76 * C_dyad * Real.exp (-(j : ℝ)) := by
    intro q hq
    let M : ℕ := ⌈Real.exp ((j : ℝ) + 1)⌉₊ + 1
    have hlogq_pos : 0 < Real.log (q : ℝ) :=
      lt_trans (Real.exp_pos _) (log_shell_prime_bounds hq).1
    have hmaps : ∀ p ∈ A.filter (q < ·),
        ⌊Real.log (p : ℝ) - Real.log (q : ℝ)⌋₊ ∈ Finset.range M := by
      intro p hp
      obtain ⟨hpA, _⟩ := Finset.mem_filter.mp hp
      have hlogp_hi := (log_shell_prime_bounds hpA).2
      have hdiff_le : Real.log (p : ℝ) - Real.log (q : ℝ) ≤ Real.exp ((j : ℝ) + 1) := by linarith
      have hfl_le : ⌊Real.log (p : ℝ) - Real.log (q : ℝ)⌋₊ ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ :=
        Nat.floor_le_of_le (hdiff_le.trans (Nat.le_ceil _))
      exact Finset.mem_range.mpr (by dsimp [M]; omega)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hblock : ∀ m ∈ Finset.range M,
        ∑ p ∈ (A.filter (q < ·)).filter
            (fun p : ℕ => ⌊Real.log (p : ℝ) - Real.log (q : ℝ)⌋₊ = m),
          |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ) ≤
          fejerBlockWeight m * (4 * C_dyad * Real.exp (-(j : ℝ))) := by
      intro m _
      let B := A.filter fun p => q < p ∧ (m : ℝ) ≤ Real.log (p : ℝ) - Real.log (q : ℝ) ∧
        Real.log (p : ℝ) - Real.log (q : ℝ) < (m : ℝ) + 1
      have hsub_B : (A.filter (q < ·)).filter
          (fun p : ℕ => ⌊Real.log (p : ℝ) - Real.log (q : ℝ)⌋₊ = m) ⊆ B := by
        intro p hp
        obtain ⟨hp1, hfl⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpA, hqp⟩ := Finset.mem_filter.mp hp1
        have hq_pos : (0 : ℝ) < q := by
          have hmem := (Finset.mem_filter.mp hq).2.1
          have := seven_le_shellCut hj
          exact_mod_cast (by omega : 0 < q)
        have hdiff_nn : 0 ≤ Real.log (p : ℝ) - Real.log (q : ℝ) :=
          sub_nonneg.mpr (Real.log_le_log hq_pos (by exact_mod_cast hqp.le))
        have hlo : (m : ℝ) ≤ Real.log (p : ℝ) - Real.log (q : ℝ) := by
          rw [← hfl]; exact Nat.floor_le hdiff_nn
        have hhi : Real.log (p : ℝ) - Real.log (q : ℝ) < (m : ℝ) + 1 := by
          rw [← hfl]; exact Nat.lt_floor_add_one _
        exact Finset.mem_filter.mpr ⟨hpA, hqp, hlo, hhi⟩
      have hker_le : ∀ p ∈ B,
          |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| ≤ fejerBlockWeight m := by
        intro p hp
        obtain ⟨_, _, hlo, _⟩ := Finset.mem_filter.mp hp
        unfold fejerBlockWeight
        split_ifs with hm2
        · exact abs_fejerCosKernel_le_eight a _
        · have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast (not_lt.mp hm2)
          have hω2 : 2 ≤ |Real.log (p : ℝ) - Real.log (q : ℝ)| := by
            rw [abs_of_nonneg (by linarith)]
            linarith
          have hm_le_abs : (m : ℝ) ≤ |Real.log (p : ℝ) - Real.log (q : ℝ)| := by
            rw [abs_of_nonneg (by linarith)]
            exact hlo
          exact (abs_fejerCosKernel_le_inv_cube a hω2).trans
            (div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (pow_le_pow_left₀ (by positivity) hm_le_abs 3))
      calc ∑ p ∈ (A.filter (q < ·)).filter
            (fun p : ℕ => ⌊Real.log (p : ℝ) - Real.log (q : ℝ)⌋₊ = m),
          |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ)
          ≤ ∑ p ∈ B, |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun p : ℕ => |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ))
              hsub_B fun _ _ _ => by positivity
        _ ≤ ∑ p ∈ B, fejerBlockWeight m * (1 / (p : ℝ)) :=
            Finset.sum_le_sum fun p hp => by
              rw [div_eq_mul_one_div]
              exact mul_le_mul_of_nonneg_right (hker_le p hp) (by positivity)
        _ = fejerBlockWeight m * ∑ p ∈ B, 1 / (p : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ fejerBlockWeight m * (4 * C_dyad * Real.exp (-(j : ℝ))) :=
            mul_le_mul_of_nonneg_left (sum_inv_unit_log_block_le hS hj hq m)
              (fejerBlockWeight_nonneg m)
    calc ∑ m ∈ Finset.range M,
          ∑ p ∈ (A.filter (q < ·)).filter
              (fun p : ℕ => ⌊Real.log (p : ℝ) - Real.log (q : ℝ)⌋₊ = m),
            |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ)
        ≤ ∑ m ∈ Finset.range M, fejerBlockWeight m * (4 * C_dyad * Real.exp (-(j : ℝ))) :=
          Finset.sum_le_sum hblock
      _ = (∑ m ∈ Finset.range M, fejerBlockWeight m) * (4 * C_dyad * Real.exp (-(j : ℝ))) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ 19 * (4 * C_dyad * Real.exp (-(j : ℝ))) :=
          mul_le_mul_of_nonneg_right (sum_fejerBlockWeight_le M) (by positivity)
      _ = 76 * C_dyad * Real.exp (-(j : ℝ)) := by ring
  -- Difference-frequency contribution `≤ (8 * C_sh + 152 * C_sh * C_dyad) * exp(-j)`
  have hdiff_freq : ∑ q ∈ A, ∑ p ∈ A,
      (1 / ((q : ℝ) * (p : ℝ))) *
        |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| ≤
      (8 * C_sh + 152 * C_sh * C_dyad) * Real.exp (-(j : ℝ)) := by
    let g : ℕ → ℕ → ℝ := fun q p =>
      (1 / ((q : ℝ) * (p : ℝ))) * |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))|
    have hg_nn : ∀ q p, 0 ≤ g q p := fun q p => by dsimp [g]; positivity
    have hg_symm : ∀ q p, g q p = g p q := fun q p => by
      dsimp [g]
      rw [mul_comm (q : ℝ) (p : ℝ),
        show Real.log (p : ℝ) - Real.log (q : ℝ) = -(Real.log (q : ℝ) - Real.log (p : ℝ)) by ring,
        fejerCosKernel_neg]
    have htri_pt : ∀ q ∈ A, ∀ p ∈ A,
        g q p ≤ (if p = q then g q q else 0) + (if q < p then g q p else 0) +
          (if p < q then g p q else 0) := by
      intro q _ p _
      rcases lt_trichotomy q p with hlt | rfl | hgt
      · have hne : p ≠ q := hlt.ne'
        have hnlt : ¬ p < q := not_lt.mpr hlt.le
        simp [hne, hlt, hnlt]
      · simp
      · have hne : p ≠ q := hgt.ne
        have hnlt : ¬ q < p := not_lt.mpr hgt.le
        simp [hne, hgt, hnlt, hg_symm q p]
    have hdiag_le : ∑ q ∈ A, g q q ≤ 8 * C_sh * Real.exp (-(j : ℝ)) := by
      have hq_inv_le : ∀ q ∈ A, 1 / (q : ℝ) ≤ Real.exp (-(j : ℝ)) := by
        intro q hq
        have hlogq := (log_shell_prime_bounds hq).1
        have hj_lt_ej : (j : ℝ) < Real.exp (j : ℝ) := by
          linarith [Real.add_one_le_exp (j : ℝ)]
        have hq_pos : (0 : ℝ) < q := by
          have := (Finset.mem_filter.mp hq).2.1
          exact_mod_cast (by omega : 0 < q)
        have hej_le_q : Real.exp (j : ℝ) ≤ (q : ℝ) := by
          simpa [Real.exp_log hq_pos] using Real.exp_le_exp.mpr (hj_lt_ej.trans hlogq).le
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (Real.exp_pos _) hej_le_q
      calc ∑ q ∈ A, g q q
          ≤ ∑ q ∈ A, (8 * Real.exp (-(j : ℝ))) * (1 / (q : ℝ)) :=
            Finset.sum_le_sum fun q hq => by
              dsimp [g]
              have hk8 := abs_fejerCosKernel_le_eight a (Real.log (q : ℝ) - Real.log (q : ℝ))
              have hqi := hq_inv_le q hq
              have hrew : (1 / ((q : ℝ) * (q : ℝ))) *
                  |fejerCosKernel a (Real.log (q : ℝ) - Real.log (q : ℝ))| =
                  (|fejerCosKernel a (Real.log (q : ℝ) - Real.log (q : ℝ))| * (1 / (q : ℝ))) *
                    (1 / (q : ℝ)) := by ring
              rw [hrew]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul hk8 hqi (by positivity) (by norm_num)
        _ = (8 * Real.exp (-(j : ℝ))) * ∑ q ∈ A, 1 / (q : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (8 * Real.exp (-(j : ℝ))) * C_sh :=
            mul_le_mul_of_nonneg_left hsh_sum (by positivity)
        _ = 8 * C_sh * Real.exp (-(j : ℝ)) := by ring
    have hoff_le : ∑ q ∈ A, ∑ p ∈ A, (if q < p then g q p else 0) ≤
        76 * C_sh * C_dyad * Real.exp (-(j : ℝ)) := by
      have hrew : ∀ q ∈ A, ∑ p ∈ A, (if q < p then g q p else 0) =
          (1 / (q : ℝ)) * ∑ p ∈ A.filter (q < ·),
            |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ) := by
        intro q _
        rw [← Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        dsimp [g]; ring
      calc ∑ q ∈ A, ∑ p ∈ A, (if q < p then g q p else 0)
          = ∑ q ∈ A, (1 / (q : ℝ)) * ∑ p ∈ A.filter (q < ·),
              |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ) :=
            Finset.sum_congr rfl hrew
        _ ≤ ∑ q ∈ A, (1 / (q : ℝ)) * (76 * C_dyad * Real.exp (-(j : ℝ))) :=
            Finset.sum_le_sum fun q hq =>
              mul_le_mul_of_nonneg_left (hinner_diff q hq) (by positivity)
        _ = (∑ q ∈ A, 1 / (q : ℝ)) * (76 * C_dyad * Real.exp (-(j : ℝ))) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ C_sh * (76 * C_dyad * Real.exp (-(j : ℝ))) :=
            mul_le_mul_of_nonneg_right hsh_sum (by positivity)
        _ = 76 * C_sh * C_dyad * Real.exp (-(j : ℝ)) := by ring
    calc ∑ q ∈ A, ∑ p ∈ A, g q p
        ≤ ∑ q ∈ A, ∑ p ∈ A,
            ((if p = q then g q q else 0) + (if q < p then g q p else 0) +
              (if p < q then g p q else 0)) :=
          Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun p hp => htri_pt q hq p hp
      _ = (∑ q ∈ A, ∑ p ∈ A, if p = q then g q q else 0) +
            (∑ q ∈ A, ∑ p ∈ A, if q < p then g q p else 0) +
            (∑ p ∈ A, ∑ q ∈ A, if p < q then g p q else 0) := by
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.sum_comm (s := A) (t := A) (f := fun q p => if p < q then g p q else 0)]
      _ = (∑ q ∈ A, g q q) + 2 * (∑ q ∈ A, ∑ p ∈ A, if q < p then g q p else 0) := by
          have hdiag_eq : (∑ q ∈ A, ∑ p ∈ A, if p = q then g q q else 0) = ∑ q ∈ A, g q q :=
            Finset.sum_congr rfl fun q hq => by simp [hq]
          rw [hdiag_eq]; ring
      _ ≤ 8 * C_sh * Real.exp (-(j : ℝ)) +
            2 * (76 * C_sh * C_dyad * Real.exp (-(j : ℝ))) := by linarith
      _ = (8 * C_sh + 152 * C_sh * C_dyad) * Real.exp (-(j : ℝ)) := by ring
  -- Combine `hdom_int`, `hexact`, `hdiff_freq`, and `hsum_freq`
  have hint_le : ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 ≤
      1 / 2 * ((8 * C_sh + 152 * C_sh * C_dyad) * Real.exp (-(j : ℝ))) +
        1 / 2 * (C_sh ^ 2 * Real.exp (-(j : ℝ))) := by
    rw [hexact]
    calc ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) *
          (1 / 2 * fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ)) +
            1 / 2 * fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ)))
        ≤ ∑ q ∈ A, ∑ p ∈ A,
            (1 / 2 * ((1 / ((q : ℝ) * (p : ℝ))) *
                |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))|) +
              1 / 2 * ((1 / ((q : ℝ) * (p : ℝ))) *
                |fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))|)) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => by
            have hqp : 0 ≤ 1 / ((q : ℝ) * (p : ℝ)) := by positivity
            have h1 := le_abs_self (fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ)))
            have h2 := le_abs_self (fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ)))
            nlinarith
      _ = 1 / 2 * (∑ q ∈ A, ∑ p ∈ A,
            (1 / ((q : ℝ) * (p : ℝ))) *
              |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))|) +
          1 / 2 * (∑ q ∈ A, ∑ p ∈ A,
            (1 / ((q : ℝ) * (p : ℝ))) *
              |fejerCosKernel a (Real.log (p : ℝ) + Real.log (q : ℝ))|) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ 1 / 2 * ((8 * C_sh + 152 * C_sh * C_dyad) * Real.exp (-(j : ℝ))) +
            1 / 2 * (C_sh ^ 2 * Real.exp (-(j : ℝ))) := by linarith
  have hexp_pos : 0 < Real.exp (-(j : ℝ)) := Real.exp_pos _
  dsimp [C_L2]
  nlinarith


/-! ## §4. Tail `L²` summation, exponential integrability, and uniform boundedness of `Q_{1/2}(P)` -/

/-- Desingularized logarithmic Euler product, obtained by subtracting the outer `12 log log(|t| + e)`
growth envelope from the prime cosine sum. -/
noncomputable def desingLogProd (S : Finset ℕ) (t : ℝ) : ℝ :=
  (∑ p ∈ S, (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ))) -
    12 * Real.log (Real.log (|t| + Real.exp 1))

private theorem continuous_desingLogProd (S : Finset ℕ) : Continuous (desingLogProd S) := by
  unfold desingLogProd
  refine (continuous_finsetSum S fun p _ => ?_).sub (continuous_const.mul ?_)
  · exact ((continuous_const.mul (Real.continuous_cos.comp
      (continuous_id.mul continuous_const))).div_const _)
  · have hc1 : Continuous fun t : ℝ => |t| + Real.exp 1 := continuous_abs.add continuous_const
    have hc2 : Continuous fun t : ℝ => Real.log (|t| + Real.exp 1) :=
      hc1.log fun t => by positivity
    refine hc2.log fun t => ?_
    have h1 : 1 ≤ Real.log (|t| + Real.exp 1) := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
      rwa [Real.log_exp] at h
    linarith

private theorem desingLogProd_le_card {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (t : ℝ) :
    desingLogProd S t ≤ (S.card : ℝ) := by
  unfold desingLogProd
  have hL1 : 1 ≤ Real.log (|t| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
    rwa [Real.log_exp] at h
  have hlogL_nn : 0 ≤ Real.log (Real.log (|t| + Real.exp 1)) := Real.log_nonneg hL1
  have hsum : ∑ p ∈ S, (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) ≤ (S.card : ℝ) := by
    calc ∑ p ∈ S, (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ))
        ≤ ∑ _p ∈ S, (1 : ℝ) := Finset.sum_le_sum fun p hp => by
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
            have hc := Real.neg_one_le_cos (t * Real.log (p : ℝ))
            rw [div_le_one (by positivity)]
            linarith
      _ = (S.card : ℝ) := by simp
  linarith

private theorem eulerProductSq_one_le_desingLogProd {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (t : ℝ) :
    eulerProductSq 1 t S ≤
      Real.exp (Real.pi ^ 2 / 6) * (Real.log (|t| + Real.exp 1)) ^ 12 *
        Real.exp (desingLogProd S t) := by
  let Z : ℕ := S.sup id
  have hsub_Z : S ⊆ Nat.primesLE Z := fun p hp =>
    Nat.mem_primesLE.mpr ⟨Finset.le_sup (f := id) hp, hS p hp⟩
  have hsq_le : ∑ p ∈ S, 1 / (p : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub_Z fun _ _ _ => by positivity).trans
      (RHTower.Sieve.sum_inv_sq_primesLE_le_pi Z)
  have hL1 : 1 ≤ Real.log (|t| + Real.exp 1) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| + Real.exp 1 by linarith [abs_nonneg t])
    rwa [Real.log_exp] at h
  have hL_pos : 0 < Real.log (|t| + Real.exp 1) := by linarith
  have hdecomp : (∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
      ∑ p ∈ S, (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) ≤
      Real.pi ^ 2 / 6 + 12 * Real.log (Real.log (|t| + Real.exp 1)) + desingLogProd S t := by
    unfold desingLogProd
    linarith
  calc eulerProductSq 1 t S
      ≤ Real.exp ((∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
          ∑ p ∈ S, (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ))) :=
        eulerProductSq_one_le_exp t S
    _ ≤ Real.exp (Real.pi ^ 2 / 6 + 12 * Real.log (Real.log (|t| + Real.exp 1)) +
          desingLogProd S t) := Real.exp_le_exp.mpr hdecomp
    _ = Real.exp (Real.pi ^ 2 / 6) * (Real.log (|t| + Real.exp 1)) ^ (12 : ℕ) *
          Real.exp (desingLogProd S t) := by
        rw [Real.exp_add, Real.exp_add,
          show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hL_pos]

private theorem j_le_shellCut (j : ℕ) : j ≤ shellCut j := by
  unfold shellCut
  have h1 : (j : ℝ) ≤ Real.exp (j : ℝ) := by linarith [Real.add_one_le_exp (j : ℝ)]
  have h2 : Real.exp (j : ℝ) ≤ Real.exp (Real.exp (j : ℝ)) := by
    linarith [Real.add_one_le_exp (Real.exp (j : ℝ))]
  exact Nat.le_floor (h1.trans h2)

private theorem sum_shell_window_eq (S : Finset ℕ) (t : ℝ) (j₀ k : ℕ) :
    ∑ p ∈ S.filter (fun p => shellCut j₀ < p ∧ p ≤ shellCut (j₀ + k)),
        (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) =
      -2 * ∑ j ∈ Finset.Ico j₀ (j₀ + k), shellTrig (primeShell S j) t := by
  induction k with
  | zero =>
    rw [Nat.add_zero, Finset.Ico_self, Finset.sum_empty, mul_zero]
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hp
    omega
  | succ k ih =>
    let W₁ := S.filter fun p => shellCut j₀ < p ∧ p ≤ shellCut (j₀ + (k + 1))
    change ∑ p ∈ W₁, (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) = _
    rw [← Finset.sum_filter_add_sum_filter_not W₁ (fun p => p ≤ shellCut (j₀ + k))]
    have hleft : W₁.filter (fun p => p ≤ shellCut (j₀ + k)) =
        S.filter (fun p => shellCut j₀ < p ∧ p ≤ shellCut (j₀ + k)) := by
      ext p
      simp only [W₁, Finset.mem_filter]
      have hmono := shellCut_mono (show j₀ + k ≤ j₀ + (k + 1) by omega)
      exact ⟨fun ⟨⟨hpS, hgt, _⟩, hle⟩ => ⟨hpS, hgt, hle⟩,
        fun ⟨hpS, hgt, hle⟩ => ⟨⟨hpS, hgt, hle.trans hmono⟩, hle⟩⟩
    have hright : W₁.filter (fun p => ¬ p ≤ shellCut (j₀ + k)) = primeShell S (j₀ + k) := by
      ext p
      simp only [W₁, primeShell, Finset.mem_filter]
      have hmono := shellCut_mono (Nat.le_add_right j₀ k)
      have heq : j₀ + (k + 1) = j₀ + k + 1 := by omega
      rw [heq]
      exact ⟨fun ⟨⟨hpS, _, hle⟩, hnle⟩ => ⟨hpS, not_le.mp hnle, hle⟩,
        fun ⟨hpS, hgt, hle⟩ => ⟨⟨hpS, lt_of_le_of_lt hmono hgt, hle⟩, not_le.mpr hgt⟩⟩
    rw [hleft, hright, ih, show j₀ + (k + 1) = (j₀ + k) + 1 by omega,
      Finset.sum_Ico_succ_top (Nat.le_add_right j₀ k), mul_add]
    congr 1
    unfold shellTrig
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring

private theorem desingLogProd_le_head_add_tail {C₀ : ℝ}
    (hpole : ∀ w : ℕ, 3 ≤ w → ∀ S' : Finset ℕ, S' ⊆ Nat.primesLE w → ∀ t : ℝ,
      ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
        C₀ + 12 * Real.log (Real.log (|t| + Real.exp 1)) +
          17 / 24 * Real.log (Real.log (w : ℝ)))
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) (t : ℝ) :
    desingLogProd S t ≤ C₀ + 17 / 24 * (j₀ : ℝ) +
      2 * ∑ j ∈ Finset.Ico j₀ (j₀ + (S.sup id + 1)), |shellTrig (primeShell S j) t| := by
  let k : ℕ := S.sup id + 1
  have hsplit := (Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ shellCut j₀)
    (fun p => -2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ))).symm
  have hhead_sub : S.filter (fun p => p ≤ shellCut j₀) ⊆ Nat.primesLE (shellCut j₀) := by
    intro p hp
    obtain ⟨hpS, hle⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle, hS p hpS⟩
  have hw3 : 3 ≤ shellCut j₀ := le_trans (by norm_num) (seven_le_shellCut hj₀)
  have hloglog_le : Real.log (Real.log (shellCut j₀ : ℝ)) ≤ (j₀ : ℝ) := by
    have hle_exp : (shellCut j₀ : ℝ) ≤ Real.exp (Real.exp (j₀ : ℝ)) :=
      Nat.floor_le (Real.exp_pos _).le
    have hpos1 : (0 : ℝ) < shellCut j₀ := by exact_mod_cast (by omega : 0 < shellCut j₀)
    have hlog1 : Real.log (shellCut j₀ : ℝ) ≤ Real.exp (j₀ : ℝ) := by
      simpa [Real.log_exp] using Real.log_le_log hpos1 hle_exp
    have hpos_log1 : 0 < Real.log (shellCut j₀ : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < shellCut j₀))
    simpa [Real.log_exp] using Real.log_le_log hpos_log1 hlog1
  have hhead_bound := hpole (shellCut j₀) hw3 _ hhead_sub t
  have htail_set : S.filter (fun p => ¬ p ≤ shellCut j₀) =
      S.filter (fun p => shellCut j₀ < p ∧ p ≤ shellCut (j₀ + k)) := by
    ext p
    simp only [Finset.mem_filter]
    refine ⟨fun ⟨hpS, hnle⟩ => ⟨hpS, not_le.mp hnle, ?_⟩, fun ⟨hpS, hgt, _⟩ => ⟨hpS, not_le.mpr hgt⟩⟩
    have hp_sup : p ≤ S.sup id := Finset.le_sup (f := id) hpS
    have hp_jk : p ≤ j₀ + k := by dsimp [k]; omega
    exact hp_jk.trans (j_le_shellCut (j₀ + k))
  have htail_eq : ∑ p ∈ S.filter (fun p => ¬ p ≤ shellCut j₀),
      (-2 * Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)) =
      -2 * ∑ j ∈ Finset.Ico j₀ (j₀ + k), shellTrig (primeShell S j) t := by
    rw [htail_set, sum_shell_window_eq]
  have htail_abs : -2 * ∑ j ∈ Finset.Ico j₀ (j₀ + k), shellTrig (primeShell S j) t ≤
      2 * ∑ j ∈ Finset.Ico j₀ (j₀ + k), |shellTrig (primeShell S j) t| := by
    rw [show -2 * ∑ j ∈ Finset.Ico j₀ (j₀ + k), shellTrig (primeShell S j) t =
      2 * ∑ j ∈ Finset.Ico j₀ (j₀ + k), -shellTrig (primeShell S j) t by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun j _ => neg_le_abs _) (by norm_num)
  unfold desingLogProd
  rw [hsplit, htail_eq]
  linarith

private theorem sum_exp_neg_half_Ico_le (j₀ k : ℕ) :
    ∑ j ∈ Finset.Ico j₀ (j₀ + k), Real.exp (-(j : ℝ) / 2) ≤
      3 * Real.exp (-(j₀ : ℝ) / 2) := by
  have hr_le : Real.exp (-1 / 2) ≤ 2 / 3 := by
    have h1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg]
    exact (inv_anti₀ (by norm_num) h1).trans_eq (by norm_num)
  have hgeom : ∀ m : ℕ, ∑ n ∈ Finset.range m, (Real.exp (-1 / 2)) ^ n ≤
      3 - 3 * (Real.exp (-1 / 2)) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hp_nn : 0 ≤ (Real.exp (-1 / 2)) ^ m := pow_nonneg (Real.exp_pos _).le m
      have hmul : 3 * ((Real.exp (-1 / 2)) ^ m * Real.exp (-1 / 2)) ≤
          2 * (Real.exp (-1 / 2)) ^ m := by
        calc 3 * ((Real.exp (-1 / 2)) ^ m * Real.exp (-1 / 2))
            = (Real.exp (-1 / 2)) ^ m * (3 * Real.exp (-1 / 2)) := by ring
          _ ≤ (Real.exp (-1 / 2)) ^ m * (3 * (2 / 3)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr_le (by norm_num)) hp_nn
          _ = 2 * (Real.exp (-1 / 2)) ^ m := by ring
      calc ∑ n ∈ Finset.range (m + 1), (Real.exp (-1 / 2)) ^ n
          = (∑ n ∈ Finset.range m, (Real.exp (-1 / 2)) ^ n) + (Real.exp (-1 / 2)) ^ m :=
            Finset.sum_range_succ _ m
        _ ≤ (3 - 3 * (Real.exp (-1 / 2)) ^ m) + (Real.exp (-1 / 2)) ^ m := add_le_add_left ih _
        _ = 3 - 2 * (Real.exp (-1 / 2)) ^ m := by ring
        _ ≤ 3 - 3 * ((Real.exp (-1 / 2)) ^ m * Real.exp (-1 / 2)) := sub_le_sub_left hmul 3
        _ = 3 - 3 * (Real.exp (-1 / 2)) ^ (m + 1) := by rw [pow_succ]
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hfactor : ∑ m ∈ Finset.range k, Real.exp (-(((j₀ + m : ℕ) : ℝ)) / 2) =
      Real.exp (-(j₀ : ℝ) / 2) * ∑ m ∈ Finset.range k, (Real.exp (-1 / 2)) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, mul_comm (3 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hp_nn : 0 ≤ 3 * (Real.exp (-1 / 2)) ^ k :=
    mul_nonneg (by norm_num) (pow_nonneg (Real.exp_pos _).le k)
  exact (hgeom k).trans (sub_le_self 3 hp_nn)

private theorem integral_tail_sq_unit_le {C_L2 : ℝ} (hC_L2 : 0 < C_L2)
    (hL2 : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ j : ℕ, 1 ≤ j → ∀ a : ℝ,
      ∫ t in Icc (a - 1) (a + 1), (shellTrig (primeShell S j) t) ^ 2 ≤
        C_L2 * Real.exp (-(j : ℝ)))
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) (k : ℕ) (a : ℝ) :
    ∫ t in Icc (a - 1) (a + 1),
        (∑ j ∈ Finset.Ico j₀ (j₀ + k), |shellTrig (primeShell S j) t|) ^ 2 ≤
      9 * C_L2 * Real.exp (-(j₀ : ℝ)) := by
  let I := Finset.Ico j₀ (j₀ + k)
  have hcs_pt : ∀ t : ℝ,
      (∑ j ∈ I, |shellTrig (primeShell S j) t|) ^ 2 ≤
        (∑ j ∈ I, Real.exp (-(j : ℝ) / 2)) *
          ∑ j ∈ I, Real.exp ((j : ℝ) / 2) * (shellTrig (primeShell S j) t) ^ 2 := by
    intro t
    have h := Finset.sum_mul_sq_le_sq_mul_sq I
      (fun j : ℕ => Real.exp (-(j : ℝ) / 4))
      (fun j : ℕ => Real.exp ((j : ℝ) / 4) * |shellTrig (primeShell S j) t|)
    have e1 : ∀ j : ℕ, Real.exp (-(j : ℝ) / 4) *
        (Real.exp ((j : ℝ) / 4) * |shellTrig (primeShell S j) t|) =
        |shellTrig (primeShell S j) t| := fun j => by
      rw [← mul_assoc, ← Real.exp_add, show -(j : ℝ) / 4 + (j : ℝ) / 4 = 0 by ring,
        Real.exp_zero, one_mul]
    have e2 : ∀ j : ℕ, (Real.exp (-(j : ℝ) / 4)) ^ 2 = Real.exp (-(j : ℝ) / 2) := fun j => by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have e3 : ∀ j : ℕ, (Real.exp ((j : ℝ) / 4) * |shellTrig (primeShell S j) t|) ^ 2 =
        Real.exp ((j : ℝ) / 2) * (shellTrig (primeShell S j) t) ^ 2 := fun j => by
      rw [mul_pow, sq_abs, sq (Real.exp ((j : ℝ) / 4)), ← Real.exp_add]; congr 2; ring
    simp only [e1, e2, e3] at h
    exact h
  have hint_lhs : IntegrableOn
      (fun t : ℝ => (∑ j ∈ I, |shellTrig (primeShell S j) t|) ^ 2) (Icc (a - 1) (a + 1)) := by
    refine (Continuous.continuousOn ?_).integrableOn_Icc
    unfold shellTrig
    fun_prop
  have hint_term : ∀ j ∈ I, IntegrableOn
      (fun t : ℝ => Real.exp ((j : ℝ) / 2) * (shellTrig (primeShell S j) t) ^ 2)
      (Icc (a - 1) (a + 1)) := fun j _ => by
    refine (Continuous.continuousOn ?_).integrableOn_Icc
    unfold shellTrig
    fun_prop
  have hint_sum : IntegrableOn
      (fun t : ℝ => ∑ j ∈ I, Real.exp ((j : ℝ) / 2) * (shellTrig (primeShell S j) t) ^ 2)
      (Icc (a - 1) (a + 1)) := by
    refine (Continuous.continuousOn ?_).integrableOn_Icc
    unfold shellTrig
    fun_prop
  have hw_sum := sum_exp_neg_half_Ico_le j₀ k
  have hw_nn : 0 ≤ ∑ j ∈ I, Real.exp (-(j : ℝ) / 2) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc ∫ t in Icc (a - 1) (a + 1), (∑ j ∈ I, |shellTrig (primeShell S j) t|) ^ 2
      ≤ ∫ t in Icc (a - 1) (a + 1),
          (∑ j ∈ I, Real.exp (-(j : ℝ) / 2)) *
            ∑ j ∈ I, Real.exp ((j : ℝ) / 2) * (shellTrig (primeShell S j) t) ^ 2 :=
        setIntegral_mono_on hint_lhs (hint_sum.const_mul _) measurableSet_Icc fun t _ => hcs_pt t
    _ = (∑ j ∈ I, Real.exp (-(j : ℝ) / 2)) *
          ∑ j ∈ I, Real.exp ((j : ℝ) / 2) *
            ∫ t in Icc (a - 1) (a + 1), (shellTrig (primeShell S j) t) ^ 2 := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum I hint_term]
        congr 1
        exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _
    _ ≤ (3 * Real.exp (-(j₀ : ℝ) / 2)) *
          ∑ j ∈ I, Real.exp ((j : ℝ) / 2) * (C_L2 * Real.exp (-(j : ℝ))) := by
        refine mul_le_mul hw_sum (Finset.sum_le_sum fun j hjI => ?_)
          (Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le
            (integral_nonneg fun _ => sq_nonneg _)) (by positivity)
        have hj1 : 1 ≤ j := hj₀.trans (Finset.mem_Ico.mp hjI).1
        exact mul_le_mul_of_nonneg_left (hL2 S hS j hj1 a) (Real.exp_pos _).le
    _ = 3 * C_L2 * Real.exp (-(j₀ : ℝ) / 2) * ∑ j ∈ I, Real.exp (-(j : ℝ) / 2) := by
        have hterm : ∑ j ∈ I, Real.exp ((j : ℝ) / 2) * (C_L2 * Real.exp (-(j : ℝ))) =
            C_L2 * ∑ j ∈ I, Real.exp (-(j : ℝ) / 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_left_comm, ← Real.exp_add, show (j : ℝ) / 2 + -(j : ℝ) = -(j : ℝ) / 2 by ring]
        rw [hterm]; ring
    _ ≤ 3 * C_L2 * Real.exp (-(j₀ : ℝ) / 2) * (3 * Real.exp (-(j₀ : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hw_sum (by positivity)
    _ = 9 * C_L2 * Real.exp (-(j₀ : ℝ)) := by
        have hexp_sq : Real.exp (-(j₀ : ℝ) / 2) * Real.exp (-(j₀ : ℝ) / 2) =
            Real.exp (-(j₀ : ℝ)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc 3 * C_L2 * Real.exp (-(j₀ : ℝ) / 2) * (3 * Real.exp (-(j₀ : ℝ) / 2))
            = 9 * C_L2 * (Real.exp (-(j₀ : ℝ) / 2) * Real.exp (-(j₀ : ℝ) / 2)) := by ring
          _ = 9 * C_L2 * Real.exp (-(j₀ : ℝ)) := by rw [hexp_sq]

private theorem integral_const_Icc_unit (a c : ℝ) :
    ∫ _t in Icc (a - 1) (a + 1), c = 2 * c := by
  have hle : a - 1 ≤ a + 1 := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem exists_setIntegral_superlevel_desingLogProd_le :
    ∃ C_meas : ℝ, 0 < C_meas ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ a : ℝ, ∀ n : ℕ,
      ∫ t in Icc (a - 1) (a + 1),
          {t : ℝ | (n : ℝ) ≤ desingLogProd S t}.indicator (fun _ => (1 : ℝ)) t ≤
        C_meas * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) := by
  obtain ⟨C₀, hC₀, hpole⟩ := exists_subset_neg_two_cos_le_pole_free
  obtain ⟨C_L2, hC_L2, hL2⟩ := exists_unit_L2_primeShell_le
  let N₀ : ℕ := ⌈20 * (C₀ + 1)⌉₊ + 20
  let C_meas : ℝ := max (2 * Real.exp ((6 / 5 : ℝ) * (N₀ : ℝ))) (27 * C_L2) + 1
  refine ⟨C_meas, by dsimp [C_meas]; positivity, fun S hS a n => ?_⟩
  let E : Set ℝ := {t : ℝ | (n : ℝ) ≤ desingLogProd S t}
  have hE_meas : MeasurableSet E :=
    isClosed_le continuous_const (continuous_desingLogProd S) |>.measurableSet
  have hint_1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (a - 1) (a + 1)) :=
    integrableOn_const (hs := by simp)
  have hint_E : IntegrableOn (E.indicator (fun _ => (1 : ℝ))) (Icc (a - 1) (a + 1)) := by
    refine hint_1.mono' (measurable_const.indicator hE_meas).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ E
    · rw [indicator_of_mem ht]; norm_num
    · rw [indicator_of_notMem ht]; norm_num
  by_cases hn : n < N₀
  · have hn_le : (n : ℝ) ≤ N₀ := by exact_mod_cast hn.le
    have h1_le_exp : (1 : ℝ) ≤ Real.exp ((6 / 5 : ℝ) * (N₀ : ℝ)) *
        Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hC_lo : 2 * Real.exp ((6 / 5 : ℝ) * (N₀ : ℝ)) ≤ C_meas :=
      (le_max_left _ _).trans (by dsimp [C_meas]; linarith)
    calc ∫ t in Icc (a - 1) (a + 1), E.indicator (fun _ => (1 : ℝ)) t
        ≤ ∫ _t in Icc (a - 1) (a + 1), (1 : ℝ) := by
          refine setIntegral_mono_on hint_E hint_1 measurableSet_Icc fun t _ => ?_
          by_cases ht : t ∈ E
          · rw [indicator_of_mem ht]
          · rw [indicator_of_notMem ht]; norm_num
      _ = 2 := by rw [integral_const_Icc_unit]; ring
      _ ≤ 2 * (Real.exp ((6 / 5 : ℝ) * (N₀ : ℝ)) * Real.exp (-(6 / 5 : ℝ) * (n : ℝ))) := by
          nlinarith
      _ = (2 * Real.exp ((6 / 5 : ℝ) * (N₀ : ℝ))) * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) := by ring
      _ ≤ C_meas * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hC_lo (Real.exp_pos _).le
  · have hn_ge : N₀ ≤ n := not_lt.mp hn
    have hn20 : (20 : ℝ) * (C₀ + 1) + 20 ≤ (n : ℝ) := by
      have hceil : 20 * (C₀ + 1) ≤ (⌈20 * (C₀ + 1)⌉₊ : ℝ) := Nat.le_ceil _
      have hnR : ((⌈20 * (C₀ + 1)⌉₊ + 20 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      push_cast at hnR
      linarith
    let j₀ : ℕ := ⌊(6 / 5 : ℝ) * (n : ℝ)⌋₊
    have hj₀_ge1 : 1 ≤ j₀ := by
      refine Nat.le_floor ?_
      linarith
    have hj₀_le : (j₀ : ℝ) ≤ (6 / 5 : ℝ) * (n : ℝ) := Nat.floor_le (by positivity)
    have hj₀_gt : (6 / 5 : ℝ) * (n : ℝ) - 1 < (j₀ : ℝ) := by
      have h := Nat.lt_floor_add_one ((6 / 5 : ℝ) * (n : ℝ))
      change (6 / 5 : ℝ) * (n : ℝ) < (j₀ : ℝ) + 1 at h
      linarith
    let k : ℕ := S.sup id + 1
    let tailSum : ℝ → ℝ := fun t =>
      ∑ j ∈ Finset.Ico j₀ (j₀ + k), |shellTrig (primeShell S j) t|
    have hint_tail : IntegrableOn (fun t : ℝ => (tailSum t) ^ 2) (Icc (a - 1) (a + 1)) := by
      refine (Continuous.continuousOn ?_).integrableOn_Icc
      dsimp [tailSum]; unfold shellTrig; fun_prop
    have hpt_ind : ∀ t ∈ Icc (a - 1) (a + 1),
        E.indicator (fun _ => (1 : ℝ)) t ≤ (tailSum t) ^ 2 := by
      intro t _
      by_cases htE : t ∈ E
      · rw [indicator_of_mem htE]
        have hn_le_des : (n : ℝ) ≤ desingLogProd S t := htE
        have hdes_le := desingLogProd_le_head_add_tail hpole hS hj₀_ge1 t
        have h1_le_tail : 1 ≤ tailSum t := by
          dsimp [tailSum, k] at hdes_le ⊢
          linarith
        nlinarith
      · rw [indicator_of_notMem htE]
        exact sq_nonneg _
    have hexp_j₀ : Real.exp (-(j₀ : ℝ)) ≤ 3 * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) := by
      have he1_le3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp (-(j₀ : ℝ))
          ≤ Real.exp (1 + -(6 / 5 : ℝ) * (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp 1 * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) := Real.exp_add _ _
        _ ≤ 3 * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) :=
            mul_le_mul_of_nonneg_right he1_le3 (Real.exp_pos _).le
    have hC_lo : 27 * C_L2 ≤ C_meas :=
      (le_max_right _ _).trans (by dsimp [C_meas]; linarith)
    calc ∫ t in Icc (a - 1) (a + 1), E.indicator (fun _ => (1 : ℝ)) t
        ≤ ∫ t in Icc (a - 1) (a + 1), (tailSum t) ^ 2 :=
          setIntegral_mono_on hint_E hint_tail measurableSet_Icc hpt_ind
      _ ≤ 9 * C_L2 * Real.exp (-(j₀ : ℝ)) :=
          integral_tail_sq_unit_le hC_L2 hL2 hS hj₀_ge1 k a
      _ ≤ 9 * C_L2 * (3 * Real.exp (-(6 / 5 : ℝ) * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp_j₀ (by positivity)
      _ = (27 * C_L2) * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) := by ring
      _ ≤ C_meas * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hC_lo (Real.exp_pos _).le

private theorem sum_exp_neg_fifth_le (K : ℕ) :
    ∑ n ∈ Finset.range K, Real.exp (-(1 / 5 : ℝ) * (n : ℝ)) ≤ 6 := by
  have hr_le : Real.exp (-1 / 5) ≤ 5 / 6 := by
    have h1 : (6 / 5 : ℝ) ≤ Real.exp (1 / 5) := by linarith [Real.add_one_le_exp (1 / 5 : ℝ)]
    rw [show (-1 / 5 : ℝ) = -(1 / 5 : ℝ) by ring, Real.exp_neg]
    exact (inv_anti₀ (by norm_num) h1).trans_eq (by norm_num)
  have hgeom : ∀ m : ℕ, ∑ n ∈ Finset.range m, (Real.exp (-1 / 5)) ^ n ≤
      6 - 6 * (Real.exp (-1 / 5)) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hp_nn : 0 ≤ (Real.exp (-1 / 5)) ^ m := pow_nonneg (Real.exp_pos _).le m
      have hmul : 6 * ((Real.exp (-1 / 5)) ^ m * Real.exp (-1 / 5)) ≤
          5 * (Real.exp (-1 / 5)) ^ m := by
        calc 6 * ((Real.exp (-1 / 5)) ^ m * Real.exp (-1 / 5))
            = (Real.exp (-1 / 5)) ^ m * (6 * Real.exp (-1 / 5)) := by ring
          _ ≤ (Real.exp (-1 / 5)) ^ m * (6 * (5 / 6)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr_le (by norm_num)) hp_nn
          _ = 5 * (Real.exp (-1 / 5)) ^ m := by ring
      calc ∑ n ∈ Finset.range (m + 1), (Real.exp (-1 / 5)) ^ n
          = (∑ n ∈ Finset.range m, (Real.exp (-1 / 5)) ^ n) + (Real.exp (-1 / 5)) ^ m :=
            Finset.sum_range_succ _ m
        _ ≤ (6 - 6 * (Real.exp (-1 / 5)) ^ m) + (Real.exp (-1 / 5)) ^ m := add_le_add_left ih _
        _ = 6 - 5 * (Real.exp (-1 / 5)) ^ m := by ring
        _ ≤ 6 - 6 * ((Real.exp (-1 / 5)) ^ m * Real.exp (-1 / 5)) := sub_le_sub_left hmul 6
        _ = 6 - 6 * (Real.exp (-1 / 5)) ^ (m + 1) := by rw [pow_succ]
  have hrew : ∑ n ∈ Finset.range K, Real.exp (-(1 / 5 : ℝ) * (n : ℝ)) =
      ∑ n ∈ Finset.range K, (Real.exp (-1 / 5)) ^ n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1; ring
  rw [hrew]
  have hp_nn : 0 ≤ 6 * (Real.exp (-1 / 5)) ^ K :=
    mul_nonneg (by norm_num) (pow_nonneg (Real.exp_pos _).le K)
  exact (hgeom K).trans (sub_le_self 6 hp_nn)

/-- **Uniform exponential integrability of `desingLogProd S` on every unit-radius interval.** -/
theorem exists_integral_exp_desingLogProd_unit_le :
    ∃ C_exp_int : ℝ, 0 < C_exp_int ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ a : ℝ,
      ∫ t in Icc (a - 1) (a + 1), Real.exp (desingLogProd S t) ≤ C_exp_int := by
  obtain ⟨C_meas, hC_meas, hmeas⟩ := exists_setIntegral_superlevel_desingLogProd_le
  let C_exp_int : ℝ := 2 * Real.exp 1 + 6 * Real.exp 1 * C_meas + 1
  refine ⟨C_exp_int, by dsimp [C_exp_int]; positivity, fun S hS a => ?_⟩
  let K : ℕ := S.card + 1
  let E : ℕ → Set ℝ := fun n => {t : ℝ | (n : ℝ) ≤ desingLogProd S t}
  have hE_meas : ∀ n : ℕ, MeasurableSet (E n) := fun n =>
    isClosed_le continuous_const (continuous_desingLogProd S) |>.measurableSet
  have hint_1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (a - 1) (a + 1)) :=
    integrableOn_const (hs := by simp)
  have hint_e1 : IntegrableOn (fun _ : ℝ => Real.exp 1) (Icc (a - 1) (a + 1)) :=
    integrableOn_const (hs := by simp)
  have hint_En : ∀ n : ℕ,
      IntegrableOn ((E n).indicator (fun _ => (1 : ℝ))) (Icc (a - 1) (a + 1)) := fun n => by
    refine hint_1.mono' (measurable_const.indicator (hE_meas n)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ E n
    · rw [indicator_of_mem ht]; norm_num
    · rw [indicator_of_notMem ht]; norm_num
  have hint_lhs : IntegrableOn (fun t : ℝ => Real.exp (desingLogProd S t))
      (Icc (a - 1) (a + 1)) :=
    (Real.continuous_exp.comp (continuous_desingLogProd S)).continuousOn.integrableOn_Icc
  have hint_sum : IntegrableOn
      (fun t : ℝ => ∑ n ∈ Finset.range K,
        Real.exp ((n : ℝ) + 1) * (E n).indicator (fun _ => (1 : ℝ)) t)
      (Icc (a - 1) (a + 1)) :=
    integrable_finsetSum _ fun n _ => (hint_En n).const_mul _
  have hpt : ∀ t ∈ Icc (a - 1) (a + 1),
      Real.exp (desingLogProd S t) ≤ Real.exp 1 +
        ∑ n ∈ Finset.range K,
          Real.exp ((n : ℝ) + 1) * (E n).indicator (fun _ => (1 : ℝ)) t := by
    intro t _
    have hsum_nn : 0 ≤ ∑ n ∈ Finset.range K,
        Real.exp ((n : ℝ) + 1) * (E n).indicator (fun _ => (1 : ℝ)) t :=
      Finset.sum_nonneg fun n _ => mul_nonneg (Real.exp_pos _).le
        (indicator_nonneg (fun _ _ => zero_le_one) t)
    by_cases hy1 : desingLogProd S t < 1
    · have hexp_le : Real.exp (desingLogProd S t) ≤ Real.exp 1 := Real.exp_le_exp.mpr hy1.le
      linarith
    · have hy_ge1 : 1 ≤ desingLogProd S t := not_lt.mp hy1
      let n₀ : ℕ := ⌊desingLogProd S t⌋₊
      have hn₀_le : (n₀ : ℝ) ≤ desingLogProd S t := Nat.floor_le (by linarith)
      have hn₀_gt : desingLogProd S t < (n₀ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hn₀_mem : n₀ ∈ Finset.range K := by
        have hcard := desingLogProd_le_card hS t
        have hn₀_card : n₀ ≤ S.card := Nat.floor_le_of_le hcard
        exact Finset.mem_range.mpr (by dsimp [K]; omega)
      have ht_En₀ : t ∈ E n₀ := hn₀_le
      have hsingle : Real.exp ((n₀ : ℝ) + 1) ≤
          ∑ n ∈ Finset.range K,
            Real.exp ((n : ℝ) + 1) * (E n).indicator (fun _ => (1 : ℝ)) t := by
        have hterm : Real.exp ((n₀ : ℝ) + 1) =
            Real.exp ((n₀ : ℝ) + 1) * (E n₀).indicator (fun _ => (1 : ℝ)) t := by
          rw [indicator_of_mem ht_En₀, mul_one]
        rw [hterm]
        exact Finset.single_le_sum
          (f := fun n : ℕ => Real.exp ((n : ℝ) + 1) * (E n).indicator (fun _ => (1 : ℝ)) t)
          (fun n _ => mul_nonneg (Real.exp_pos _).le
            (indicator_nonneg (fun _ _ => zero_le_one) t)) hn₀_mem
      have hexp_le : Real.exp (desingLogProd S t) ≤ Real.exp ((n₀ : ℝ) + 1) :=
        Real.exp_le_exp.mpr hn₀_gt.le
      have he1_pos : 0 < Real.exp 1 := Real.exp_pos 1
      linarith
  calc ∫ t in Icc (a - 1) (a + 1), Real.exp (desingLogProd S t)
      ≤ ∫ t in Icc (a - 1) (a + 1),
          (Real.exp 1 + ∑ n ∈ Finset.range K,
            Real.exp ((n : ℝ) + 1) * (E n).indicator (fun _ => (1 : ℝ)) t) :=
        setIntegral_mono_on hint_lhs (hint_e1.add hint_sum) measurableSet_Icc hpt
    _ = 2 * Real.exp 1 + ∑ n ∈ Finset.range K,
          Real.exp ((n : ℝ) + 1) *
            ∫ t in Icc (a - 1) (a + 1), (E n).indicator (fun _ => (1 : ℝ)) t := by
        rw [MeasureTheory.integral_add hint_e1 hint_sum,
          integral_const_Icc_unit,
          MeasureTheory.integral_finsetSum _ (fun n _ => (hint_En n).const_mul _)]
        congr 1
        exact Finset.sum_congr rfl fun n _ => MeasureTheory.integral_const_mul _ _
    _ ≤ 2 * Real.exp 1 + ∑ n ∈ Finset.range K,
          Real.exp ((n : ℝ) + 1) * (C_meas * Real.exp (-(6 / 5 : ℝ) * (n : ℝ))) := by
        have hsum_le : ∑ n ∈ Finset.range K,
            Real.exp ((n : ℝ) + 1) *
              ∫ t in Icc (a - 1) (a + 1), (E n).indicator (fun _ => (1 : ℝ)) t ≤
            ∑ n ∈ Finset.range K,
              Real.exp ((n : ℝ) + 1) * (C_meas * Real.exp (-(6 / 5 : ℝ) * (n : ℝ))) :=
          Finset.sum_le_sum fun n _ =>
            mul_le_mul_of_nonneg_left (hmeas S hS a n) (Real.exp_pos _).le
        linarith
    _ = 2 * Real.exp 1 + Real.exp 1 * C_meas *
          ∑ n ∈ Finset.range K, Real.exp (-(1 / 5 : ℝ) * (n : ℝ)) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have hexp_eq : Real.exp ((n : ℝ) + 1) * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)) =
            Real.exp 1 * Real.exp (-(1 / 5 : ℝ) * (n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        calc Real.exp ((n : ℝ) + 1) * (C_meas * Real.exp (-(6 / 5 : ℝ) * (n : ℝ)))
            = C_meas * (Real.exp ((n : ℝ) + 1) * Real.exp (-(6 / 5 : ℝ) * (n : ℝ))) := by ring
          _ = C_meas * (Real.exp 1 * Real.exp (-(1 / 5 : ℝ) * (n : ℝ))) := by rw [hexp_eq]
          _ = Real.exp 1 * C_meas * Real.exp (-(1 / 5 : ℝ) * (n : ℝ)) := by ring
    _ ≤ 2 * Real.exp 1 + Real.exp 1 * C_meas * 6 := by
        have h5 := mul_le_mul_of_nonneg_left (sum_exp_neg_fifth_le K)
          (mul_pos (Real.exp_pos 1) hC_meas).le
        linarith
    _ ≤ C_exp_int := by dsimp [C_exp_int]; linarith

private theorem intervalIntegral_exp_desingLogProd_quarter_le {C_exp_int : ℝ}
    (hunit : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ a : ℝ,
      ∫ t in Icc (a - 1) (a + 1), Real.exp (desingLogProd S t) ≤ C_exp_int)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (c : ℝ) :
    ∫ ξ in c..(c + 1 / 4), Real.exp (desingLogProd S (2 * Real.pi * ξ)) ≤
      C_exp_int / (2 * Real.pi) := by
  have hpi_pos : 0 < 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_comp_mul_left
    (f := fun t : ℝ => Real.exp (desingLogProd S t)) hpi_pos.ne',
    smul_eq_mul, inv_mul_le_iff₀ hpi_pos, mul_div_cancel₀ _ hpi_pos.ne']
  have hle : 2 * Real.pi * c ≤ 2 * Real.pi * (c + 1 / 4) := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  let a : ℝ := 2 * Real.pi * c + 1
  have hsub : Icc (2 * Real.pi * c) (2 * Real.pi * (c + 1 / 4)) ⊆ Icc (a - 1) (a + 1) := by
    refine Icc_subset_Icc (by dsimp [a]; linarith) ?_
    dsimp [a]
    linarith [Real.pi_lt_four]
  have hint_big : IntegrableOn (fun t : ℝ => Real.exp (desingLogProd S t))
      (Icc (a - 1) (a + 1)) :=
    (Real.continuous_exp.comp (continuous_desingLogProd S)).continuousOn.integrableOn_Icc
  exact (setIntegral_mono_set hint_big
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (Eventually.of_forall fun _ ht => hsub ht)).trans (hunit S hS a)

private theorem setIntegral_exp_desingLogProd_two_pi_unit_le {C_exp_int : ℝ} (hC : 0 < C_exp_int)
    (hunit : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ a : ℝ,
      ∫ t in Icc (a - 1) (a + 1), Real.exp (desingLogProd S t) ≤ C_exp_int)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (b : ℝ) :
    ∫ ξ in Icc b (b + 1), Real.exp (desingLogProd S (2 * Real.pi * ξ)) ≤ C_exp_int := by
  let f : ℝ → ℝ := fun ξ => Real.exp (desingLogProd S (2 * Real.pi * ξ))
  have hf_cont : Continuous f :=
    Real.continuous_exp.comp ((continuous_desingLogProd S).comp (continuous_const.mul continuous_id))
  have hle : b ≤ b + 1 := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hf_ii : ∀ x y : ℝ, IntervalIntegrable f volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf_ii b (b + 1 / 4)) (hf_ii (b + 1 / 4) (b + 1 / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf_ii (b + 1 / 2) (b + 3 / 4)) (hf_ii (b + 3 / 4) (b + 1))
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hf_ii b (b + 1 / 2)) (hf_ii (b + 1 / 2) (b + 1))
  have q0 := intervalIntegral_exp_desingLogProd_quarter_le hunit hS b
  have q1 := intervalIntegral_exp_desingLogProd_quarter_le hunit hS (b + 1 / 4)
  have q2 := intervalIntegral_exp_desingLogProd_quarter_le hunit hS (b + 1 / 2)
  have q3 := intervalIntegral_exp_desingLogProd_quarter_le hunit hS (b + 3 / 4)
  rw [show b + 1 / 4 + 1 / 4 = b + 1 / 2 by ring] at q1
  rw [show b + 1 / 2 + 1 / 4 = b + 3 / 4 by ring] at q2
  rw [show b + 3 / 4 + 1 / 4 = b + 1 by ring] at q3
  change ∫ ξ in b..(b + 1), f ξ ≤ C_exp_int
  have hsum4 : ∫ ξ in b..(b + 1), f ξ ≤ 4 * (C_exp_int / (2 * Real.pi)) := by
    linarith [h1, h2, h3, q0, q1, q2, q3]
  have h4_le : 4 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  calc ∫ ξ in b..(b + 1), f ξ
      ≤ (4 / (2 * Real.pi)) * C_exp_int := hsum4.trans_eq (by ring)
    _ ≤ 1 * C_exp_int := mul_le_mul_of_nonneg_right h4_le hC.le
    _ = C_exp_int := one_mul _

private theorem rpow_neg_four_thirds_mul_log_pow_twelve_le (ξ : ℝ) :
    (1 + |ξ|) ^ (-(4 / 3 : ℝ)) * (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 ≤
      8 * (72 : ℝ) ^ 12 * (1 + |ξ|) ^ (-(7 / 6 : ℝ)) := by
  let u : ℝ := |2 * Real.pi * ξ| + Real.exp 1
  have hu_pos : 0 < u := by dsimp [u]; positivity
  have hL1 : 1 ≤ Real.log u := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ u by dsimp [u]; linarith [abs_nonneg (2 * Real.pi * ξ)])
    rwa [Real.log_exp] at h
  have hlog_le : Real.log u ≤ 72 * u ^ (1 / 72 : ℝ) := by
    have hr := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu_pos (1 / 72 : ℝ))
    rw [Real.log_rpow hu_pos] at hr
    linarith
  have hpow12 : (Real.log u) ^ 12 ≤ (72 : ℝ) ^ 12 * u ^ (1 / 6 : ℝ) := by
    calc (Real.log u) ^ 12
        ≤ (72 * u ^ (1 / 72 : ℝ)) ^ 12 := pow_le_pow_left₀ (by linarith) hlog_le 12
      _ = (72 : ℝ) ^ 12 * (u ^ (1 / 72 : ℝ)) ^ (12 : ℕ) := mul_pow _ _ 12
      _ = (72 : ℝ) ^ 12 * u ^ (1 / 6 : ℝ) := by
          congr 1
          rw [← Real.rpow_natCast _ 12, ← Real.rpow_mul hu_pos.le]
          norm_num
  have hu_le : u ≤ 8 * (1 + |ξ|) := by
    dsimp [u]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hpi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have he1 : Real.exp 1 ≤ 8 := by linarith [Real.exp_one_lt_d9]
    nlinarith [abs_nonneg ξ]
  have hu_rpow : u ^ (1 / 6 : ℝ) ≤ 8 * (1 + |ξ|) ^ (1 / 6 : ℝ) := by
    calc u ^ (1 / 6 : ℝ)
        ≤ (8 * (1 + |ξ|)) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow hu_pos.le hu_le (by norm_num)
      _ = (8 : ℝ) ^ (1 / 6 : ℝ) * (1 + |ξ|) ^ (1 / 6 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 8 * (1 + |ξ|) ^ (1 / 6 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (8 : ℝ) ^ (1 / 6 : ℝ) ≤ (8 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 8 := Real.rpow_one 8
  have h1ξ_pos : 0 < 1 + |ξ| := by positivity
  calc (1 + |ξ|) ^ (-(4 / 3 : ℝ)) * (Real.log u) ^ 12
      ≤ (1 + |ξ|) ^ (-(4 / 3 : ℝ)) * ((72 : ℝ) ^ 12 * (8 * (1 + |ξ|) ^ (1 / 6 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (hpow12.trans (mul_le_mul_of_nonneg_left hu_rpow (by positivity))) (by positivity)
    _ = 8 * (72 : ℝ) ^ 12 * ((1 + |ξ|) ^ (-(4 / 3 : ℝ)) * (1 + |ξ|) ^ (1 / 6 : ℝ)) := by ring
    _ = 8 * (72 : ℝ) ^ 12 * (1 + |ξ|) ^ (-(7 / 6 : ℝ)) := by
        congr 1
        rw [← Real.rpow_add h1ξ_pos]
        norm_num

private theorem sum_range_succ_rpow_neg_seven_sixths_le (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ)) ≤ 7 := by
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (-(7 / 6 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have himg : ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ)) =
      ∑ n ∈ (Finset.range N).image Nat.succ, (n : ℝ) ^ (-(7 / 6 : ℝ)) :=
    (Finset.sum_image (f := fun n : ℕ => (n : ℝ) ^ (-(7 / 6 : ℝ)))
      fun _ _ _ _ h => Nat.succ.inj h).symm
  rw [himg]
  calc ∑ n ∈ (Finset.range N).image Nat.succ, (n : ℝ) ^ (-(7 / 6 : ℝ))
      ≤ ∑' n : ℕ, (n : ℝ) ^ (-(7 / 6 : ℝ)) :=
        hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
    _ ≤ 1 + 1 / ((7 / 6 : ℝ) - 1) := RHTower.Sieve.tsum_nat_rpow_neg_le (by norm_num)
    _ = 7 := by norm_num

private theorem eulerProductSq_one_le_four_pow {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (t : ℝ) :
    eulerProductSq 1 t S ≤ (4 : ℝ) ^ S.card := by
  unfold eulerProductSq
  calc ∏ p ∈ S, eulerFactorSq 1 t p
      ≤ ∏ _p ∈ S, (4 : ℝ) := Finset.prod_le_prod
          (fun p _ => eulerFactorSq_nonneg 1 t p)
          (fun p hp => by
            unfold eulerFactorSq
            have hp_nn : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) (-1 : ℝ)
            have hp_inv : (p : ℝ) ^ (-1 : ℝ) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (hS p hp).one_lt.le) (by norm_num)
            have hcos_le : -(p : ℝ) ^ (-1 : ℝ) ≤
                (p : ℝ) ^ (-1 : ℝ) * Real.cos (t * Real.log (p : ℝ)) := by
              have hmul : 0 ≤ (p : ℝ) ^ (-1 : ℝ) * (1 + Real.cos (t * Real.log (p : ℝ))) :=
                mul_nonneg hp_nn (by linarith [Real.neg_one_le_cos (t * Real.log (p : ℝ))])
              linarith
            have hsq_le : ((p : ℝ) ^ (-1 : ℝ)) ^ 2 ≤ 1 := by nlinarith
            linarith)
    _ = (4 : ℝ) ^ S.card := by simp

/-- **Unconditional uniform boundedness of the prime-divisor Möbius hypercube Dirichlet form at half
damping (`ε = 1/2`, `σ = 1`).**
For every Ramanujan modulus `r > 1`, there exists an explicit finite bound `B > 0` depending only on
`r` such that `hypercubeDilationDirichletForm (1 / 2) P r hr ≤ B` for **every** squarefree integer
`P : ℕ`. -/
theorem hypercubeDilationDirichletForm_half_bounded {r : ℕ} (hr : 1 < r) :
    ∃ B : ℝ, ∀ P : ℕ, Squarefree P → hypercubeDilationDirichletForm (1 / 2) P r hr ≤ B := by
  obtain ⟨C_W, hC_W, hae_W⟩ := stepSpectralWeight_ae_le_inv_rpow hr
  obtain ⟨C_exp_int, hC_exp_int, hunit⟩ := exists_integral_exp_desingLogProd_unit_le
  let K_pref : ℝ := C_W * Real.exp (Real.pi ^ 2 / 6) * (8 * (72 : ℝ) ^ 12)
  let B : ℝ := 14 * K_pref * C_exp_int
  have hK_pos : 0 < K_pref := by dsimp [K_pref]; positivity
  refine ⟨B, fun P hP => ?_⟩
  let S : Finset ℕ := P.primeFactors
  have hS : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hP_prod : ∏ p ∈ S, p = P := Nat.prod_primeFactors_of_squarefree hP
  rw [← hP_prod, hypercubeDilationDirichletForm_eq_integral hr (1 / 2) hS,
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  let g : ℝ → ℝ := fun ξ => stepSpectralWeight hr ξ * eulerProductSq 1 (2 * Real.pi * ξ) S
  have hg_nn : ∀ ξ : ℝ, 0 ≤ g ξ := fun ξ =>
    mul_nonneg (stepSpectralWeight_nonneg hr ξ) (eulerProductSq_nonneg 1 (2 * Real.pi * ξ) S)
  have hg_int : Integrable g volume := by
    have hmeas : AEStronglyMeasurable g volume :=
      (integrable_stepSpectralWeight hr).aestronglyMeasurable.mul
        ((continuous_eulerProductSq 1 S).comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable
    refine ((integrable_stepSpectralWeight hr).mul_const ((4 : ℝ) ^ S.card)).mono' hmeas
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn ξ)]
    exact mul_le_mul_of_nonneg_left (eulerProductSq_one_le_four_pow hS _)
      (stepSpectralWeight_nonneg hr ξ)
  let hmaj : ℝ → ℝ := fun ξ =>
    K_pref * (1 + |ξ|) ^ (-(7 / 6 : ℝ)) * Real.exp (desingLogProd S (2 * Real.pi * ξ))
  have hmaj_cont : Continuous hmaj := by
    dsimp [hmaj]
    refine ((continuous_const.mul ?_).mul
      (Real.continuous_exp.comp
        ((continuous_desingLogProd S).comp (continuous_const.mul continuous_id))))
    exact (continuous_const.add continuous_abs).rpow_const fun ξ => Or.inl (by dsimp; positivity)
  have hae_g_le : ∀ᵐ ξ : ℝ ∂volume, g ξ ≤ hmaj ξ := by
    filter_upwards [hae_W] with ξ hW
    have heul := eulerProductSq_one_le_desingLogProd hS (2 * Real.pi * ξ)
    have hrlog := rpow_neg_four_thirds_mul_log_pow_twelve_le ξ
    calc g ξ
        ≤ (C_W * (1 + |ξ|) ^ (-(4 / 3 : ℝ))) *
            (Real.exp (Real.pi ^ 2 / 6) *
              (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12 *
              Real.exp (desingLogProd S (2 * Real.pi * ξ))) :=
          mul_le_mul hW heul (eulerProductSq_nonneg _ _ _) (by positivity)
      _ = C_W * Real.exp (Real.pi ^ 2 / 6) *
            ((1 + |ξ|) ^ (-(4 / 3 : ℝ)) *
              (Real.log (|2 * Real.pi * ξ| + Real.exp 1)) ^ 12) *
            Real.exp (desingLogProd S (2 * Real.pi * ξ)) := by ring
      _ ≤ C_W * Real.exp (Real.pi ^ 2 / 6) *
            (8 * (72 : ℝ) ^ 12 * (1 + |ξ|) ^ (-(7 / 6 : ℝ))) *
            Real.exp (desingLogProd S (2 * Real.pi * ξ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrlog (by positivity)) (Real.exp_pos _).le
      _ = hmaj ξ := by dsimp [hmaj, K_pref]; ring
  -- Bound on each unit block `[k, k + 1]` and `[-(k + 1), -k]`
  have hunit_pos_block : ∀ k : ℕ,
      ∫ ξ in (k : ℝ)..((k : ℝ) + 1), hmaj ξ ≤
        K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ)) * C_exp_int := by
    intro k
    have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hpt : ∀ ξ ∈ Icc (k : ℝ) ((k : ℝ) + 1),
        hmaj ξ ≤ (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) *
          Real.exp (desingLogProd S (2 * Real.pi * ξ)) := by
      intro ξ hξ
      dsimp [hmaj]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK_pos.le) (Real.exp_pos _).le
      have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 1 + |ξ| := by
        rw [abs_of_nonneg (by linarith [hξ.1])]
        push_cast; linarith [hξ.1]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by norm_num)
    have hint_exp : IntegrableOn (fun ξ : ℝ => Real.exp (desingLogProd S (2 * Real.pi * ξ)))
        (Icc (k : ℝ) ((k : ℝ) + 1)) :=
      (Real.continuous_exp.comp
        ((continuous_desingLogProd S).comp
          (continuous_const.mul continuous_id))).continuousOn.integrableOn_Icc
    calc ∫ ξ in Icc (k : ℝ) ((k : ℝ) + 1), hmaj ξ
        ≤ ∫ ξ in Icc (k : ℝ) ((k : ℝ) + 1),
            (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) *
              Real.exp (desingLogProd S (2 * Real.pi * ξ)) :=
          setIntegral_mono_on hmaj_cont.continuousOn.integrableOn_Icc (hint_exp.const_mul _)
            measurableSet_Icc hpt
      _ = (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) *
            ∫ ξ in Icc (k : ℝ) ((k : ℝ) + 1), Real.exp (desingLogProd S (2 * Real.pi * ξ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) * C_exp_int :=
          mul_le_mul_of_nonneg_left
            (setIntegral_exp_desingLogProd_two_pi_unit_le hC_exp_int hunit hS (k : ℝ))
            (by positivity)
  have hunit_neg_block : ∀ k : ℕ,
      ∫ ξ in (-((k : ℝ) + 1))..(-(k : ℝ)), hmaj ξ ≤
        K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ)) * C_exp_int := by
    intro k
    have hle : -((k : ℝ) + 1) ≤ -(k : ℝ) := by linarith
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hpt : ∀ ξ ∈ Icc (-((k : ℝ) + 1)) (-(k : ℝ)),
        hmaj ξ ≤ (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) *
          Real.exp (desingLogProd S (2 * Real.pi * ξ)) := by
      intro ξ hξ
      dsimp [hmaj]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK_pos.le) (Real.exp_pos _).le
      have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ 1 + |ξ| := by
        rw [abs_of_nonpos (by linarith [hξ.2])]
        push_cast; linarith [hξ.2]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by norm_num)
    have hint_exp : IntegrableOn (fun ξ : ℝ => Real.exp (desingLogProd S (2 * Real.pi * ξ)))
        (Icc (-((k : ℝ) + 1)) (-(k : ℝ))) :=
      (Real.continuous_exp.comp
        ((continuous_desingLogProd S).comp
          (continuous_const.mul continuous_id))).continuousOn.integrableOn_Icc
    have hb_eq : -((k : ℝ) + 1) + 1 = -(k : ℝ) := by ring
    calc ∫ ξ in Icc (-((k : ℝ) + 1)) (-(k : ℝ)), hmaj ξ
        ≤ ∫ ξ in Icc (-((k : ℝ) + 1)) (-(k : ℝ)),
            (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) *
              Real.exp (desingLogProd S (2 * Real.pi * ξ)) :=
          setIntegral_mono_on hmaj_cont.continuousOn.integrableOn_Icc (hint_exp.const_mul _)
            measurableSet_Icc hpt
      _ = (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) *
            ∫ ξ in Icc (-((k : ℝ) + 1)) (-((k : ℝ) + 1) + 1),
              Real.exp (desingLogProd S (2 * Real.pi * ξ)) := by
          rw [hb_eq, MeasureTheory.integral_const_mul]
      _ ≤ (K_pref * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ))) * C_exp_int :=
          mul_le_mul_of_nonneg_left
            (setIntegral_exp_desingLogProd_two_pi_unit_le hC_exp_int hunit hS (-((k : ℝ) + 1)))
            (by positivity)
  -- Sum over `[-N, N]` by induction on `N`
  have htrunc_maj : ∀ N : ℕ, ∫ ξ in (-(N : ℝ))..(N : ℝ), hmaj ξ ≤ B := by
    have hind : ∀ N : ℕ, ∫ ξ in (-(N : ℝ))..(N : ℝ), hmaj ξ ≤
        2 * K_pref * C_exp_int * ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ)) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have hmaj_ii : ∀ x y : ℝ, IntervalIntegrable hmaj volume x y :=
          fun x y => hmaj_cont.intervalIntegrable x y
        have h1 := intervalIntegral.integral_add_adjacent_intervals
          (hmaj_ii (-(((N + 1 : ℕ) : ℝ))) (-(N : ℝ)))
          (hmaj_ii (-(N : ℝ)) (N : ℝ))
        have h2 := intervalIntegral.integral_add_adjacent_intervals
          (hmaj_ii (-(((N + 1 : ℕ) : ℝ))) (N : ℝ))
          (hmaj_ii (N : ℝ) ((N + 1 : ℕ) : ℝ))
        have hneg := hunit_neg_block N
        have hpos := hunit_pos_block N
        rw [show -((N : ℝ) + 1) = -(((N + 1 : ℕ) : ℝ)) by push_cast; ring] at hneg
        rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring] at hpos
        rw [Finset.sum_range_succ, mul_add]
        linarith
    intro N
    calc ∫ ξ in (-(N : ℝ))..(N : ℝ), hmaj ξ
        ≤ 2 * K_pref * C_exp_int *
            ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-(7 / 6 : ℝ)) := hind N
      _ ≤ 2 * K_pref * C_exp_int * 7 :=
          mul_le_mul_of_nonneg_left (sum_range_succ_rpow_neg_seven_sixths_le N) (by positivity)
      _ = B := by dsimp [B]; ring
  have htrunc_g : ∀ N : ℕ, ∫ ξ, (Icc (-(N : ℝ)) (N : ℝ)).indicator g ξ ≤ B := by
    intro N
    have hleN : -(N : ℝ) ≤ (N : ℝ) := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    rw [integral_indicator measurableSet_Icc]
    calc ∫ ξ in Icc (-(N : ℝ)) (N : ℝ), g ξ
        ≤ ∫ ξ in Icc (-(N : ℝ)) (N : ℝ), hmaj ξ :=
          integral_mono_ae hg_int.integrableOn hmaj_cont.continuousOn.integrableOn_Icc
            (ae_restrict_of_ae hae_g_le)
      _ = ∫ ξ in (-(N : ℝ))..(N : ℝ), hmaj ξ := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hleN]
      _ ≤ B := htrunc_maj N
  -- Pass `N → ∞` by dominated convergence
  have htend : Tendsto (fun N : ℕ => ∫ ξ, (Icc (-(N : ℝ)) (N : ℝ)).indicator g ξ)
      atTop (𝓝 (∫ ξ, g ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence g
      (Eventually.of_forall fun N => hg_int.aestronglyMeasurable.indicator measurableSet_Icc)
      (Eventually.of_forall fun N => Eventually.of_forall fun ξ => ?_)
      hg_int
      (Eventually.of_forall fun ξ => ?_)
    · rw [Real.norm_eq_abs]
      by_cases hmem : ξ ∈ Icc (-(N : ℝ)) (N : ℝ)
      · rw [indicator_of_mem hmem, abs_of_nonneg (hg_nn ξ)]
      · rw [indicator_of_notMem hmem, abs_zero]
        exact hg_nn ξ
    · refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨⌈|ξ|⌉₊, fun N hN => ?_⟩
      have hξN : |ξ| ≤ (N : ℝ) := (Nat.le_ceil |ξ|).trans (by exact_mod_cast hN)
      have hmemN : ξ ∈ Icc (-(N : ℝ)) (N : ℝ) := abs_le.mp hξN
      rw [indicator_of_mem hmemN]
  exact le_of_tendsto' htend htrunc_g

end GaloisForLFunctions.SignedSuccessorArithmetic
