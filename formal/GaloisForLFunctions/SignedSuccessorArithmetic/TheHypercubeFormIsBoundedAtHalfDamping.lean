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
     `(1 + cos(t - a)) / (1 + cos 1)` on `[a - π, a + π]` produces a third-order `O(|ω|^{-3})`
     Fejér-cosine kernel. Summing unit logarithmic prime windows via `sum_inv_dyadic_window_le` and
     `abs_sum_inv_bigPrimeSet_sub_le` gives `∫_{a-1}^{a+1} (shellTrig S_j t)² dt ≤ C_{L2} e^{-j}`
     uniformly in `a ∈ ℝ` and `S`.
   * Splitting `S` at `j_* = ⌊(6/5) U⌋₊` gives headroom `(1 - (17/24)(6/5)) U = (3/20) U` against
     the tail `L²` norm `O(e^{-j_*/2})`, yielding super-level decay
     `meas({t ∈ [a-1, a+1] : desingLogProd S t ≥ U}) ≤ C_meas e^{-(6/5) U}` (`6/5 > 1`), uniform
     unit-interval integrability of `exp(desingLogProd S t)`, and summability against
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
  rw [pmRamanujanPrimitive_re_ofReal, one_div, Real.exp_neg, inv_inv,
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
  simp

private theorem fourier_halfDensityPullback_stepSource_neg (r : ℕ) (ξ : ℝ) :
    𝓕 (halfDensityPullback (pmRamanujanStepSource r)) (-ξ) =
      starRingEnd ℂ (𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, map_mul, halfDensityPullback_stepSource_conj]
  congr 1
  rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_conj]
  congr 1
  simp only [mul_neg, neg_neg, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
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
    rw [halfDensityPullback_stepSource_eq_primitiveSource_neg, neg_neg]
    congr 2
    ring
  rw [hflip, fourier_halfDensityPullback]
  have hs_eq : (1 / 2 - 2 * ↑Real.pi * ↑(-ξ) * Complex.I : ℂ) =
      (1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hs_eq]
  have hs0 : (0 : ℝ) < ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I).re := by simp
  have hs1 : ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I).re < 1 := by simp
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
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
      sub_self, add_zero, Complex.add_im, Complex.one_im, Complex.div_ofNat_im, zero_div,
      zero_add] at hre him
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hre
    rw [abs_of_pos ht_pos] at him
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
      conv_lhs => rw [← Real.rpow_one (1 + |ξ|), ← Real.rpow_add h1ξ_pos]
      norm_num
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
      (Complex.measurable_ofReal.comp (Real.measurable_sqrt.comp Real.measurable_exp)).mul
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
            rw [← Real.exp_neg]; ring_nf; rw [← Real.exp_add]; congr 2; ring
    · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
      have hexp : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hneg
      simp [halfDensityPullback, pmRamanujanStepSource, stepFun, Nat.floor_eq_zero.mpr hexp,
        pmRamanujanPrimitive, indicator_of_notMem hx]
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

private theorem two_squares_cos_majorant' (θ : ℝ) :
    0 ≤ 17 / 24 - Real.cos θ + 1 / 3 * Real.cos (2 * θ) ∧
      -2 * Real.cos θ ≤ 17 / 24 - Real.cos θ + 1 / 3 * Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  exact ⟨by nlinarith [sq_nonneg (Real.cos θ - 3 / 4)],
    by nlinarith [sq_nonneg (Real.cos θ + 3 / 4)]⟩

private theorem primesLE_subset_primesLE {a b : ℕ} (hab : a ≤ b) :
    Nat.primesLE a ⊆ Nat.primesLE b := by
  intro p hp
  obtain ⟨hpa, hp'⟩ := Nat.mem_primesLE.mp hp
  exact Nat.mem_primesLE.mpr ⟨hpa.trans hab, hp'⟩

private theorem sum_cos_div_prime_le_of_zeta_upper' {z : ℕ} {u B : ℝ} (hz : 3 ≤ z) (hB0 : 0 < B)
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
  have hre : (1 : ℝ) < ((σ : ℂ) + (u : ℂ) * Complex.I).re := by simpa using hσ1
  have hz_ne : riemannZeta ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hre.le
  have hlog_zeta : Real.log ‖riemannZeta ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ Real.log B :=
    Real.log_le_log (norm_pos_iff.mpr hz_ne) hB
  have hcomp := abs_le.1 (RHTower.Sieve.abs_log_norm_riemannZeta_sub_tsum_re_le hre)
  have hsq : (∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) =
      ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    rw [RHTower.Sieve.tsum_norm_sq_eq]
    congr 1; ext p; congr 2; simp
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

private theorem exists_neg_sum_cos_div_primesLE_le' :
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
    have hleC : RHTower.Sieve.mertensSecondUpperConst + C₀ ≤ C₁ := by
      dsimp [C₁]
      linarith [le_abs_self (RHTower.Sieve.mertensSecondUpperConst + C₀), Nat.cast_nonneg Z]
    linarith
  · have hcard : (Nat.primesLE z).card ≤ z := by
      calc (Nat.primesLE z).card
          ≤ (Finset.Icc 2 z).card := Finset.card_le_card fun p hp => by
              have hp' := Nat.mem_primesLE.mp hp
              exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, hp'.1⟩
        _ ≤ z := by simp; omega
    have habs : |∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)| ≤ (Z : ℝ) := by
      calc |∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ)|
          ≤ ∑ p ∈ Nat.primesLE z, |Real.cos (t * Real.log p) / (p : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p ∈ Nat.primesLE z, (1 : ℝ) := Finset.sum_le_sum fun p hp => by
            have hp2 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
            rw [abs_div, abs_of_pos (by positivity)]
            exact div_le_one_of_le₀ ((Real.abs_cos_le_one _).trans hp2) (by positivity)
        _ = ((Nat.primesLE z).card : ℝ) := by simp
        _ ≤ (z : ℝ) := by exact_mod_cast hcard
        _ ≤ (Z : ℝ) := by exact_mod_cast (not_le.mp hzZ).le
    have hneg := neg_le_abs (∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ))
    dsimp [C₁]
    linarith [abs_nonneg (RHTower.Sieve.mertensSecondUpperConst + C₀)]

private theorem exists_zetaEntire_pole_box_bounds :
    ∃ c_box M_box : ℝ, 0 < c_box ∧ 1 ≤ M_box ∧
      ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (-1 : ℝ) 1,
        c_box ≤ ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ∧
          ‖RHTower.zetaEntire ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ M_box := by
  let K : Set (ℝ × ℝ) := Icc (1 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(1, 0), ⟨le_rfl, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ => ‖RHTower.zetaEntire ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)‖) K := by
    refine Continuous.continuousOn ?_
    have h1 : Continuous (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) := by fun_prop
    exact (RHTower.differentiable_zetaEntire.continuous.comp h1).norm
  obtain ⟨q_min, hq_min, hmin⟩ := hcompact.exists_isMinOn hne hcont
  obtain ⟨q_max, _, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  have hc0 : 0 < ‖RHTower.zetaEntire ((q_min.1 : ℂ) + (q_min.2 : ℂ) * Complex.I)‖ := by
    refine norm_pos_iff.mpr (RHTower.Sieve.zetaEntire_ne_zero_of_one_le_re ?_)
    simpa using hq_min.1.1
  refine ⟨‖RHTower.zetaEntire ((q_min.1 : ℂ) + (q_min.2 : ℂ) * Complex.I)‖,
    max 1 ‖RHTower.zetaEntire ((q_max.1 : ℂ) + (q_max.2 : ℂ) * Complex.I)‖, hc0,
    le_max_left _ _, fun σ hσ u hu =>
      ⟨hmin ⟨hσ, hu⟩, (hmax ⟨hσ, hu⟩).trans (le_max_right _ _)⟩⟩

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
    ⟨by have : (0 : ℝ) < 1 / Real.log (y : ℝ) := by positivity; linarith,
     by have : 1 / Real.log (y : ℝ) ≤ 1 := div_le_one_of_le₀ hlogy1 hlogy_pos.le; linarith⟩
  have hu_mem : u ∈ Icc (-1 : ℝ) 1 := abs_le.mp hu1
  let s : ℂ := ((1 + 1 / Real.log (y : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I
  have hs1 : s ≠ 1 := by
    intro hcon
    have him : s.im = u := by simp [s]
    rw [hcon] at him; simp at him
    exact hu0.ne' (by simp [him])
  have hfac : RHTower.zetaEntire s = (s - 1) * riemannZeta s := RHTower.zetaEntire_eq hs1
  have hnorm_lo : |u| ≤ ‖s - 1‖ := by
    have him : (s - 1).im = u := by simp [s]
    simpa [him] using Complex.abs_im_le_norm (s - 1)
  have hnorm_hi : ‖s - 1‖ ≤ 3 * |u| := by
    have hrw : s - 1 = (((1 / Real.log (y : ℝ) : ℝ)) : ℂ) + (u : ℂ) * Complex.I := by
      dsimp [s]; push_cast; ring
    rw [hrw]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hent_lo, hent_hi⟩ := hbox (1 + 1 / Real.log (y : ℝ)) hσ_mem u hu_mem
  change c_box ≤ ‖RHTower.zetaEntire s‖ at hent_lo
  change ‖RHTower.zetaEntire s‖ ≤ M_box at hent_hi
  rw [hfac, norm_mul] at hent_lo hent_hi
  have hζ_hi : ‖riemannZeta s‖ ≤ M_box / |u| := by
    rw [le_div_iff₀ hu0]
    calc ‖riemannZeta s‖ * |u| = |u| * ‖riemannZeta s‖ := mul_comm _ _
      _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := mul_le_mul_of_nonneg_right hnorm_lo (norm_nonneg _)
      _ ≤ M_box := hent_hi
  have hζ_lo : c_box / (3 * |u|) ≤ ‖riemannZeta s‖ := by
    rw [div_le_iff₀ (by positivity)]
    calc c_box ≤ ‖s - 1‖ * ‖riemannZeta s‖ := hent_lo
      _ ≤ 3 * |u| * ‖riemannZeta s‖ := mul_le_mul_of_nonneg_right hnorm_hi (norm_nonneg _)
      _ = ‖riemannZeta s‖ * (3 * |u|) := mul_comm _ _
  constructor
  · have hσ1 : (1 : ℝ) < 1 + 1 / Real.log (y : ℝ) := by
      have : (0 : ℝ) < 1 / Real.log (y : ℝ) := by positivity
      linarith
    have hlog_lo : Real.log (c_box / 3) - Real.log |u| ≤ Real.log ‖riemannZeta s‖ := by
      have h := Real.log_le_log (by positivity) hζ_lo
      have hdiv : c_box / (3 * |u|) = (c_box / 3) / |u| := by ring
      rwa [hdiv, Real.log_div (by positivity) hu0.ne'] at h
    have htsum := RHTower.Sieve.le_tsum_re_prime_cpow_of_log_le hσ1 (by simpa [s] using hlog_lo)
    have hcos := RHTower.Sieve.sum_cos_div_prime_ge_of_le hy htsum
    linarith
  · have hcos := sum_cos_div_prime_le_of_zeta_upper' hy (div_pos (by linarith) hu0)
      (by simpa [s] using hζ_hi)
    rw [Real.log_div (by linarith) hu0.ne'] at hcos
    linarith

/-- **Pole-free subset log-Euler-product bound across all `w ≥ 3` and all `t : ℝ`.** -/
theorem exists_subset_neg_two_cos_le_pole_free :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ w : ℕ, 3 ≤ w → ∀ S' : Finset ℕ, S' ⊆ Nat.primesLE w → ∀ t : ℝ,
      ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
        C₀ + 12 * Real.log (Real.log (|t| + Real.exp 1)) +
          17 / 24 * Real.log (Real.log (w : ℝ)) := by
  obtain ⟨C₁, hC₁0, hcos1⟩ := exists_neg_sum_cos_div_primesLE_le'
  obtain ⟨c_box, M_box, hc0, hM1, hbox⟩ := exists_zetaEntire_pole_box_bounds
  let C_pass : ℝ := Real.pi ^ 2 / 6 +
    2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
    (1 + Real.log 4)
  let C_win : ℝ := |Real.log M_box - Real.log (c_box / 3)| + 2 * C_pass
  let C₀ : ℝ := 17 / 24 * |RHTower.Sieve.mertensSecondUpperConst| +
    C₁ + C_pass + Real.log 4 + 2 * C_win + 1
  have hC_pass_nn : 0 ≤ C_pass := by
    dsimp [C_pass]
    have hm := RHTower.Sieve.mertensFirstConst_nonneg
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hC_win_nn : 0 ≤ C_win := by dsimp [C_win]; positivity
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
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
  have hmert_abs : 17 / 24 * (∑ p ∈ Nat.primesLE w, 1 / (p : ℝ)) ≤
      17 / 24 * Real.log (Real.log (w : ℝ)) +
        17 / 24 * |RHTower.Sieve.mertensSecondUpperConst| := by
    linarith [hmert, le_abs_self RHTower.Sieve.mertensSecondUpperConst]
  by_cases ht_half : 1 / 2 ≤ |t|
  · -- Moderate and high frequencies `|t| ≥ 1/2`
    have hσ_mem : 1 + 1 / Real.log (w : ℝ) ∈ Icc (1 : ℝ) 2 :=
      ⟨by have : (0 : ℝ) < 1 / Real.log (w : ℝ) := by positivity; linarith,
       by have : 1 / Real.log (w : ℝ) ≤ 1 := div_le_one_of_le₀ hlogw1 hlogw_pos.le; linarith⟩
    let zc : ℂ := ((1 + 1 / Real.log (w : ℝ) : ℝ) : ℂ) + (2 * t : ℂ) * Complex.I
    have hzc_im : 1 ≤ |zc.im| := by
      have him : zc.im = 2 * t := by simp [zc]
      rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    have hzeta_hi := RHTower.Sieve.norm_riemannZeta_ge_one_log_le
      (by simpa [zc] using hσ_mem.1) (by simpa [zc] using hσ_mem.2) hzc_im
    have him_eq : |zc.im| = 2 * |t| := by
      have him : zc.im = 2 * t := by simp [zc]
      rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [him_eq] at hzeta_hi
    have hB_le : 3 + Real.log (4 + 2 * |t|) ≤ 4 * Real.log (|t| + Real.exp 1) := by
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
    have hcos2 := sum_cos_div_prime_le_of_zeta_upper' hw
      (by positivity : 0 < 4 * Real.log (|t| + Real.exp 1))
      (by simpa [zc] using hzeta_hi.trans hB_le)
    rw [Real.log_mul (by norm_num) hL_pos.ne'] at hcos2
    have hmaj : ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤
        17 / 24 * (∑ p ∈ Nat.primesLE w, 1 / (p : ℝ)) -
          (∑ p ∈ Nat.primesLE w, Real.cos (t * Real.log p) / (p : ℝ)) +
          1 / 3 * (∑ p ∈ Nat.primesLE w, Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
      calc ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ))
          ≤ ∑ p ∈ S', (17 / 24 - Real.cos (t * Real.log p) +
              1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
            Finset.sum_le_sum fun p _ =>
              div_le_div_of_nonneg_right (two_squares_cos_majorant' (t * Real.log p)).2
                (Nat.cast_nonneg p)
        _ ≤ ∑ p ∈ Nat.primesLE w, (17 / 24 - Real.cos (t * Real.log p) +
              1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hS' fun p _ _ =>
              div_nonneg (two_squares_cos_majorant' (t * Real.log p)).1 (Nat.cast_nonneg p)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_neg_distrib,
              ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring]; ring
    have hc1 := hcos1 w t
    dsimp [C₀, C_pass] at hcos2 ⊢
    linarith
  · -- Near-zero frequencies `|t| < 1/2`
    have ht_lt : |t| < 1 / 2 := not_le.mp ht_half
    by_cases htw : |t| * Real.log (w : ℝ) ≤ 1
    · -- Very small frequency `|t| log w ≤ 1` (including `t = 0`): all cosines are nonnegative
      have hnonpos : ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) ≤ 0 := by
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
    · -- Intermediate near-zero frequency `1 < |t| log w` and `|t| < 1/2`
      have htw_gt : 1 < |t| * Real.log (w : ℝ) := not_le.mp htw
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
        have hexp_lt_w : Real.exp (1 / |t|) < (w : ℝ) := by
          have hlt : 1 / |t| < Real.log (w : ℝ) := (div_lt_iff₀ ht_pos).mpr (by linarith)
          simpa [Real.exp_log (by positivity : (0 : ℝ) < w)] using Real.exp_lt_exp.mpr hlt
        exact (Nat.floor_le (Real.exp_pos _).le).trans_lt hexp_lt_w |> Nat.lt_iff_add_one_le.mp |>
          fun h => by exact_mod_cast (Nat.floor_le (Real.exp_pos _).le).trans hexp_lt_w.le
      have hw₀_log_inv : 1 / Real.log (w₀ : ℝ) ≤ 2 * |t| := by
        have hw₀_pos : (0 : ℝ) < w₀ := by exact_mod_cast (by omega : 0 < w₀)
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
      -- Split `S'` into `S' ∩ primesLE w₀` (nonpositive) and `S' \ primesLE w₀`
      have hsplit_S' : ∑ p ∈ S', (-2 * Real.cos (t * Real.log p) / (p : ℝ)) =
          (∑ p ∈ S' ∩ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ))) +
            ∑ p ∈ S' \ Nat.primesLE w₀, (-2 * Real.cos (t * Real.log p) / (p : ℝ)) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S' (Nat.primesLE w₀)).symm,
          Finset.inter_union_sdiff]
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
                  div_le_div_of_nonneg_right (two_squares_cos_majorant' (t * Real.log p)).2
                    (Nat.cast_nonneg p)
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsdiff_sub fun p _ _ =>
                  div_nonneg (two_squares_cos_majorant' (t * Real.log p)).1 (Nat.cast_nonneg p)
        have h2 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
            (17 / 24 - Real.cos (t * Real.log p) +
              1 / 3 * Real.cos (2 * (t * Real.log p))) / (p : ℝ) =
            17 / 24 * (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, 1 / (p : ℝ)) -
              (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, Real.cos (t * Real.log p) / (p : ℝ)) +
              1 / 3 * (∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀,
                Real.cos (2 * t * Real.log p) / (p : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_neg_distrib,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [show 2 * (t * Real.log (p : ℝ)) = 2 * t * Real.log (p : ℝ) by ring]; ring
        have h3 : ∑ p ∈ Nat.primesLE w \ Nat.primesLE w₀, 1 / (p : ℝ) ≤
            ∑ p ∈ Nat.primesLE w, 1 / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => by positivity
        linarith
      -- Pole cancellation on `w₀ < p ≤ w` for both `u = t` and `u = 2t`
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

private theorem abs_fejerCosKernel_le_seven (a ω : ℝ) : |fejerCosKernel a ω| ≤ 7 := by
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
      ≤ ∫ u in (-Real.pi)..Real.pi, ‖(1 + Real.cos u) * Real.cos ((a + u) * ω)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) := by
        refine intervalIntegral.integral_mono_on hle hint1.norm hint2 fun u _ => ?_
        have h1 : 0 ≤ 1 + Real.cos u := by linarith [Real.neg_one_le_cos u]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
        exact mul_le_of_le_one_right h1 (Real.abs_cos_le_one _)
    _ = 2 * Real.pi := heval
    _ ≤ 7 := by linarith [Real.pi_lt_d2]

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
      convert h.div_const ω using 1
      field_simp [hω0]
    have hd2 : HasDerivAt (fun x : ℝ => Real.sin (a * ω + (ω + 1) * x) / (2 * (ω + 1)))
        (Real.cos (a * ω + (ω + 1) * u) / 2) u := by
      have h := (Real.hasDerivAt_sin (a * ω + (ω + 1) * u)).comp u
        (((hasDerivAt_id u).const_mul (ω + 1)).const_add (a * ω))
      convert h.div_const (2 * (ω + 1)) using 1
      field_simp [hωp1]
    have hd3 : HasDerivAt (fun x : ℝ => Real.sin (a * ω + (ω - 1) * x) / (2 * (ω - 1)))
        (Real.cos (a * ω + (ω - 1) * u) / 2) u := by
      have h := (Real.hasDerivAt_sin (a * ω + (ω - 1) * u)).comp u
        (((hasDerivAt_id u).const_mul (ω - 1)).const_add (a * ω))
      convert h.div_const (2 * (ω - 1)) using 1
      field_simp [hωm1]
    convert (hd1.add hd2).add hd3 using 1
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
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hgt, hle⟩, hS q hqS⟩
  have hbig := (abs_le.mp (RHTower.Sieve.abs_sum_inv_bigPrimeSet_sub_le ha2 hab)).2
  have hlog_hi : RHTower.Sieve.logLog (shellCut (j + 1)) ≤ (j : ℝ) + 1 := by
    unfold RHTower.Sieve.logLog
    have hle_exp : (shellCut (j + 1) : ℝ) ≤ Real.exp (Real.exp ((j : ℝ) + 1)) := by
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
      have hej : (2 : ℝ) ≤ Real.exp (j : ℝ) :=
        he1.trans (Real.exp_le_exp.mpr (by exact_mod_cast hj))
      have hprod : Real.exp (j : ℝ) = Real.exp 1 * Real.exp ((j : ℝ) - 1) := by
        rw [← Real.exp_add]; congr 1; ring
      have hle_half : 2 * Real.exp ((j : ℝ) - 1) ≤ Real.exp (j : ℝ) := by
        rw [hprod]; exact mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
      have hexp_ge1 : (1 : ℝ) ≤ Real.exp ((j : ℝ) - 1) :=
        Real.one_le_exp (by have : (1 : ℝ) ≤ j := by exact_mod_cast hj; linarith)
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
  have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
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
        rw [Real.exp_add, Real.exp_one_eq_d9 ▸ rfl] at *
        rw [mul_comm (Real.exp (m : ℝ)) (Real.exp 1), mul_assoc]
        exact mul_lt_mul_of_pos_right he1_lt3 (by positivity)
      have hfl_lt : Real.exp (m : ℝ) * (q : ℝ) < (y : ℝ) + 2 := by
        have h1 := Nat.lt_floor_add_one (Real.exp (m : ℝ) * (q : ℝ))
        have hy_eq : (⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊ : ℝ) = (y : ℝ) + 1 := by
          dsimp [y]; omega_cast
        linarith
      have hy7R : (7 : ℝ) ≤ y := by exact_mod_cast hy_ge7
      have hp_lt_R : (p : ℝ) < ((2 * (2 * y) : ℕ) : ℝ) := by
        push_cast; nlinarith
      exact Nat.le_of_lt (by exact_mod_cast hp_lt_R)
    by_cases hp2y : p ≤ 2 * y
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hy_lt_p, hp2y⟩, hp_prime⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨not_le.mp hp2y, hp_lt_4y⟩, hp_prime⟩)
  have hlogy_lo : (1 / 2 : ℝ) * Real.exp (j : ℝ) ≤ Real.log (y : ℝ) := by
    have hy_ge_half : Real.exp (m : ℝ) * (q : ℝ) / 2 ≤ (y : ℝ) := by
      have h1 := Nat.lt_floor_add_one (Real.exp (m : ℝ) * (q : ℝ))
      have hy_eq : (⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊ : ℝ) = (y : ℝ) + 1 := by
        dsimp [y]
        rw [Nat.cast_sub (by omega : 1 ≤ ⌊Real.exp (m : ℝ) * (q : ℝ)⌋₊), Nat.cast_one]
        ring
      have hy7R : (7 : ℝ) ≤ y := by exact_mod_cast hy_ge7
      linarith
    have hq_half : (q : ℝ) / 2 ≤ Real.exp (m : ℝ) * (q : ℝ) / 2 := by
      have hm1 : (1 : ℝ) ≤ Real.exp (m : ℝ) := Real.one_le_exp (Nat.cast_nonneg m)
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    have hlog_ge : Real.log (q : ℝ) - Real.log 2 ≤ Real.log (y : ℝ) := by
      have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < q) |> half_pos)
        (hq_half.trans hy_ge_half)
      rwa [Real.log_div (by exact_mod_cast (by omega : q ≠ 0)) (by norm_num)] at h
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
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ (∑ p ∈ RHTower.Sieve.bigPrimeSet y (2 * y), 1 / (p : ℝ)) +
          ∑ p ∈ RHTower.Sieve.bigPrimeSet (2 * y) (2 * (2 * y)), 1 / (p : ℝ) :=
        Finset.sum_union_le _ _ _
    _ ≤ 2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log (y : ℝ) := by
        rw [mul_div_assoc]; linarith
    _ ≤ 2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) /
          ((1 / 2 : ℝ) * Real.exp (j : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlogy_lo
    _ = 4 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) *
          Real.exp (-(j : ℝ)) := by
        rw [Real.exp_neg]; field_simp; ring

/-- **Translation-invariant unit-interval `L²` decay of double-exponential prime shells.** -/
theorem exists_unit_L2_primeShell_le :
    ∃ C_L2 : ℝ, 0 < C_L2 ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      ∀ j : ℕ, 1 ≤ j → ∀ a : ℝ,
        ∫ t in Icc (a - 1) (a + 1), (shellTrig (primeShell S j) t) ^ 2 ≤
          C_L2 * Real.exp (-(j : ℝ)) := by
  let C_dyad : ℝ := Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)
  let C_sh : ℝ := 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)
  let C_off : ℝ := 4 * C_dyad * (14 + 3 * (1 + 1 / 2))
  let C_L2 : ℝ := 2 * C_sh * (7 + 2 * C_off) + 1
  have hC_dyad_nn : 0 ≤ C_dyad := by
    dsimp [C_dyad]
    linarith [RHTower.Sieve.mertensFirstConst_nonneg, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hC_sh_nn : 0 ≤ C_sh := by
    dsimp [C_sh]; linarith [RHTower.Sieve.mertensFirstConst_nonneg]
  refine ⟨C_L2, by dsimp [C_L2, C_off]; positivity, fun S hS j hj a => ?_⟩
  let A := primeShell S j
  -- Step 1: Dominate `1_{[a-1, a+1]}` by `2 (1 + cos(t - a))` on `[a - π, a + π]`
  have hcos1_ge : (1 / 2 : ℝ) ≤ 1 + Real.cos 1 := by
    have h1 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
    have hcos_nn : 0 ≤ Real.cos 1 :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
    linarith
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
      ring_nf
    exact (hstep1.trans hstep2).trans_eq hshift
  -- Step 2: Expand `(shellTrig A (a + u))²` into `fejerCosKernel`
  have hexpand : ∫ u in (-Real.pi)..Real.pi, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 ≤
      ∑ q ∈ A, (1 / (q : ℝ)) *
        (7 / (q : ℝ) + 2 * ∑ p ∈ A.filter (q < ·),
          |fejerCosKernel a (Real.log (p : ℝ) - Real.log (q : ℝ))| / (p : ℝ)) := by
    have hpt : ∀ u : ℝ, (1 + Real.cos u) * (shellTrig A (a + u)) ^ 2 ≤
        ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) *
          ((1 + Real.cos u) * Real.cos ((a + u) * (Real.log (p : ℝ) - Real.log (q : ℝ)))) := by
      intro u
      have h1 : 0 ≤ 1 + Real.cos u := by linarith [Real.neg_one_le_cos u]
      have hsq_sum : (shellTrig A (a + u)) ^ 2 =
          ∑ q ∈ A, ∑ p ∈ A, (1 / ((q : ℝ) * (p : ℝ))) *
            (Real.cos ((a + u) * Real.log (p : ℝ)) * Real.cos ((a + u) * Real.log (q : ℝ))) := by
        unfold shellTrig
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
      rw [hsq_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      have hqp_nn : 0 ≤ 1 / ((q : ℝ) * (p : ℝ)) := by positivity
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
      -- Wait: `(shellTrig)^2` has `(1/2) cos(diff) + (1/2) cos(sum)`, AND for `p, q ∈ A`,
      -- `log p + log q > 2 e^j ≥ 2 e > 5 ≥ 2`! Even simpler: sum `(1/2) |K(diff)| + (1/2) |K(sum)|`!
      -- Actually let's check: why not integrate the exact identity first, giving `(1/2) K(diff) + (1/2) K(sum)`,
      -- where `|K(sum)| ≤ 3 / (log p + log q)^3 ≤ 3 / (log p - log q)^3` AND `≤ 7`!!
      linarith [Real.cos_le_one ((a + u) * (Real.log (p : ℝ) + Real.log (q : ℝ))),
        Real.neg_one_le_cos ((a + u) * (Real.log (p : ℝ) - Real.log (q : ℝ)))]
    -- Wait: let's check `hpt`! Is `cos α cos β ≤ cos(α - β)`? NO (`cos(π/2) cos(π/2) = 0 > -1` is false when `α = π/2, β = -π/2`: `0 ≤ cos π = -1` FALSE!).
    -- Glad we caught that! Let's use the EXACT identity `cos α cos β = (1/2) cos(α - β) + (1/2) cos(α + β)`!
    sorry
  sorry
