import GaloisForLFunctions.SignedSuccessorArithmetic.TheForwardDilatedHypercubeForm
import GaloisForLFunctions.RHTower.PMRamanujanBandMellin
import GaloisForLFunctions.ArithmeticProduction.PrefixCancellationAmplifiesTheZeroFloor
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity

/-!
# Zero-damping hypercube head collapse, Euler-2 moment majorants, and compact bridges

In `TheSizeTruncatedHypercubeFormIsTheReceiver` and `TheForwardDilatedHypercubeForm`, receiver
admission and forward-dilated `L²(1, D)` criteria were formulated across strictly positive dampings
`ε > 0` (`σ = 1/2 + ε`), where the pronic head `1 ≤ n ≤ D` carries the zero-free strip information
and the exterior ray `(1, ∞)` is summed by `ζ(1 + ε)`.

This module analyses `sizeHypercubeForm` and `forwardDilatedPrimitive` **directly on the critical
line `ε = 0` (`σ = 1/2`)** at prime core `r = 2`, together with the sharp sawtooth defect:

1. **Deterministic head collapse at `ε = 0, r = 2` (`naturalDilationPrimitive_zero_two_eq`,
   `pronicNorm_naturalDilationPrimitive_zero_two_sq_eq`,
   `sizeHypercubeForm_zero_two_eq_one_sub_inv_add_tail`):**
   Because `C_2(m) = 2 ⌊m / 2⌋ - m` and `∑_{d ≤ D} μ(d) ⌊m / d⌋ = 1_{m ≥ 1}` for `0 ≤ m ≤ D`, the
   zero-damping primitive satisfies `Ψ_{0, D, 2}(1) = -1` and `Ψ_{0, D, 2}(n) = +1` for every
   `2 ≤ n ≤ D`. Its pronic head energy telescopes identically to `1 - 1 / (D + 1)`, eliminating the
   `s = 1` pole drift `D m(D)²` present in `mollifierDefect` and concentrating all `D → ∞` growth in
   the trans-cutoff pronic tail `n > D`.

2. **Euler-2 critical-line minorant and unweighted `[1, T]` moment majorant
   (`four_div_twentyFive_le_normSq_pmRamanujanMellinSymbol_two`,
   `integral_normSq_zeta_moebius_le_sizeHypercubeForm_zero`):**
   On `Re s = 1/2`, `‖2^{1 - s} - 1‖ ≥ √2 - 1 > 2/5`, giving `‖2^{1/2 - it} - 1‖² ≥ 4/25` for all
   `t ∈ ℝ`. Combining `sizeHypercubeForm_eq_integral` at `ε = 0` with the Mellin formula for
   `stepSpectralWeight` yields, for every `T ≥ 1` and `D : ℕ`,
   `∫_1^T ‖ζ(½ + it) M_D(½ + it)‖² dt ≤ (25 π / 2) (1/4 + T²) · sizeHypercubeForm_{r=2}(0, D)`
   with no additive `+ 2(T - 1)` term.

3. **Zero-damping compact `L²(1, D)` reduction, finite-cutoff periodicity, sawtooth far-tail bound,
   and direct `K = 3` producer bridges:**
   * `forwardDilatedPrimitive r ε D (x + r) = forwardDilatedPrimitive r ε D x` for all `x ≥ 0`.
   * At `ε = 0, r = 2`, `∫_1^∞ G_{0, D}(x)² dx / x² ≤ (1 + log D)²` for all `D ≥ 1`, bounding
     `sizeHypercubeForm_{r=2}(0, D)` by `∫_1^D (∑_{d ≤ D} (μ(d)/d) (⌊d/u⌋ mod 2))² du + (1 + log D)²`.
   * For the sharp Möbius sawtooth `F_X(x) = 1_{x ≥ 1} + ∑_{d ≤ X} μ(d) {x / d}`, the far tail
     satisfies `∫_{X²}^∞ F_X(x)² dx / x² ≤ 4` for all `X ≥ 1`.
   * Sparse `D^{2β + η}` bounds (`∃ᶠ D in atTop`) on `sizeHypercubeForm_{r=2}(0, D)`, on the
     compact alternating `L²(1, D)` integral at `ε = 0`, or on `mollifierDefect(Icc 1 D, μ)`
     directly yield the `route-wd` §1 long-mollifier bound with fixed `K = 3` (via
     `T_D = D^{1 / max(1, ⌈θ₀⌉₊)}`) and force `zetaZeroWidth ≤ β`.
-/

noncomputable section

open Complex MeasureTheory Set Finset Filter Topology
open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth)
open scoped BigOperators FourierTransform Interval ArithmeticFunction.Moebius

namespace GaloisForLFunctions.SignedSuccessorArithmetic

/-! ## §1. Deterministic head collapse of `sizeHypercubeForm` at `ε = 0, r = 2` -/

/-- Exact Möbius floor identity below the cutoff: for `m ≤ D`,
`∑_{1 ≤ d ≤ D} μ(d) ⌊m / d⌋ = 1` if `1 ≤ m` and `0` if `m = 0`. -/
theorem sum_Icc_moebiusReal_floor_eq {D m : ℕ} (hmD : m ≤ D) :
    ∑ d ∈ Finset.Icc 1 D, moebiusReal d * ((m / d : ℕ) : ℝ) = if m = 0 then 0 else 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp
  · rw [if_neg hm_pos.ne']
    have hsub : ∑ d ∈ Finset.Icc 1 D, moebiusReal d * ((m / d : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 m, moebiusReal d * ((m / d : ℕ) : ℝ) := by
      symm
      refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hmD) fun d hd hdm => ?_
      have hgt : m < d := by
        simp only [Finset.mem_Icc, not_and, not_le] at hd hdm
        exact hdm hd.1
      rw [Nat.div_eq_of_lt hgt]
      simp
    have hcoeff : ∀ d : ℕ, moebiusReal d = ArithmeticProduction.sharpCoeff d := fun _ => rfl
    simp_rw [hsub, hcoeff]
    rw [ArithmeticProduction.sum_mul_nat_div ArithmeticProduction.sharpCoeff le_rfl]
    simp_rw [ArithmeticProduction.sum_divisors_sharpCoeff]
    have hmem1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm_pos⟩
    rw [Finset.sum_ite_eq' (Finset.Icc 1 m) 1 (fun _ => (1 : ℝ)), if_pos hmem1]

/-- **Deterministic evaluation of the zero-damping natural primitive at `r = 2`.**
For `1 ≤ n ≤ D`, `naturalDilationPrimitive 0 D 2 n` equals `-1` at `n = 1` and `+1` for all
`2 ≤ n ≤ D`. -/
theorem naturalDilationPrimitive_zero_two_eq {D n : ℕ} (hn1 : 1 ≤ n) (hnD : n ≤ D) :
    naturalDilationPrimitive 0 D 2 n = if n = 1 then -1 else 1 := by
  unfold naturalDilationPrimitive signedDilationPrimitive
  have hterm : ∀ d ∈ Finset.Icc 1 D,
      moebiusReal d * (d : ℝ) ^ (-0 : ℝ) * (pmRamanujanPrimitive 2 (n / d)).re =
        2 * (moebiusReal d * (((n / 2) / d : ℕ) : ℝ)) -
          moebiusReal d * ((n / d : ℕ) : ℝ) := by
    intro d _
    rw [neg_zero, Real.rpow_zero, mul_one, pmRamanujanPrimitive_two_re]
    have hdiv : (n / d) / 2 = (n / 2) / d := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    have hmod : 2 * (((n / 2) / d : ℕ) : ℝ) + (((n / d) % 2 : ℕ) : ℝ) = ((n / d : ℕ) : ℝ) := by
      rw [← hdiv]
      exact_mod_cast Nat.div_add_mod (n / d) 2
    have hmod' : -(((n / d) % 2 : ℕ) : ℝ) =
        2 * (((n / 2) / d : ℕ) : ℝ) - ((n / d : ℕ) : ℝ) := by linarith
    rw [hmod']
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_Icc_moebiusReal_floor_eq ((Nat.div_le_self n 2).trans hnD),
    sum_Icc_moebiusReal_floor_eq hnD, if_neg (by omega : n ≠ 0)]
  rcases eq_or_ne n 1 with rfl | hn_ne1
  · simp
  · have h2 : n / 2 ≠ 0 := by omega
    rw [if_neg hn_ne1, if_neg h2]
    norm_num

/-- **Exact telescoping of the zero-damping pronic head energy at `r = 2`.**
For every `D : ℕ`, the receiver head `‖Ψ_{0, D, 2}‖_D²` equals `1 - 1 / (D + 1)` identically. -/
theorem pronicNorm_naturalDilationPrimitive_zero_two_sq_eq (D : ℕ) :
    TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive 0 D 2) D ^ 2 =
      1 - 1 / ((D : ℝ) + 1) := by
  rw [TransHorizonIncidenceMechanics.pronicNorm,
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => by positivity)]
  have hsq : ∑ n ∈ Finset.Icc 1 D,
      naturalDilationPrimitive 0 D 2 n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ n ∈ Finset.Icc 1 D, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnD⟩ := Finset.mem_Icc.mp hn
    rw [naturalDilationPrimitive_zero_two_eq hn1 hnD]
    split_ifs <;> norm_num
  rw [hsq]
  clear hsq
  induction D with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos k), ih]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℝ) + 1 + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hk1, hk2]
    ring

/-- **Exact pole-free decomposition of `sizeHypercubeForm` at `ε = 0, r = 2`.** -/
theorem sizeHypercubeForm_zero_two_eq_one_sub_inv_add_tail (D : ℕ) :
    sizeHypercubeForm Nat.one_lt_two 0 D =
      1 - 1 / ((D : ℝ) + 1) +
        ∑' m : ℕ, naturalDilationPrimitive 0 D 2 (m + D + 1) ^ 2 /
          ((((m + D : ℕ) : ℝ) + 1) * (((m + D : ℕ) : ℝ) + 2)) := by
  rw [sizeHypercubeForm_eq_head_add_tail Nat.one_lt_two 0 D,
    pronicNorm_naturalDilationPrimitive_zero_two_sq_eq]

/-! ## §2. Euler-2 critical-line minorant and unweighted `[1, T]` moment majorant -/

/-- Explicit evaluation of `pmRamanujanMellinSymbol` at `r = 2`: `2^{1 - s} - 1`. -/
theorem pmRamanujanMellinSymbol_two_eq (s : ℂ) :
    pmRamanujanMellinSymbol 2 s = (2 : ℂ) ^ (1 - s) - 1 := by
  unfold pmRamanujanMellinSymbol
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius b : ℂ) * (a : ℂ) ^ (1 - s)),
    Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2),
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  simp
  ring

/-- **Pointwise lower bound for the Euler-2 Mellin symbol on the critical line.**
For every `t ∈ ℝ`, `‖2^{1/2 - it} - 1‖² ≥ 4 / 25`. -/
theorem four_div_twentyFive_le_normSq_pmRamanujanMellinSymbol_two (t : ℝ) :
    (4 / 25 : ℝ) ≤ ‖pmRamanujanMellinSymbol 2 ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  rw [pmRamanujanMellinSymbol_two_eq]
  set z : ℂ := (2 : ℂ) ^ (1 - ((1 / 2 : ℂ) + (t : ℂ) * I))
  have hz_norm : ‖z‖ = Real.sqrt 2 := by
    dsimp [z]
    rw [Complex.cpow_def_of_ne_zero two_ne_zero, Complex.norm_exp]
    have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_log zero_le_two]
    rw [hlog]
    have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have h2 : (((t : ℝ) : ℂ) * I).re = 0 := by simp
    have hre : (((Real.log 2 : ℝ) : ℂ) * (1 - ((1 / 2 : ℂ) + (t : ℂ) * I))).re =
        Real.log 2 * (1 / 2) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re, Complex.one_re, Complex.add_re, h1, h2, add_zero]
      ring
    rw [hre, ← Real.rpow_def_of_pos two_pos, ← Real.sqrt_eq_rpow]
  have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hrev : 2 / 5 ≤ ‖z - (1 : ℂ)‖ := by
    have : ‖z‖ ≤ ‖z - (1 : ℂ)‖ + 1 := by
      calc ‖z‖ = ‖(z - 1) + 1‖ := by ring_nf
        _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖z - (1 : ℂ)‖ + 1 := by rw [norm_one]
    rw [hz_norm] at this
    linarith
  calc (4 / 25 : ℝ) = (2 / 5 : ℝ) ^ 2 := by norm_num
    _ ≤ ‖z - (1 : ℂ)‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hrev 2

private theorem sqrt_exp_eq_half_local (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have h : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]

private theorem pmRamanujanPrimitive_re_ofReal_local (r N : ℕ) :
    ((pmRamanujanPrimitive r N).re : ℂ) = pmRamanujanPrimitive r N := by
  apply Complex.ext
  · simp
  · simp [pmRamanujanPrimitive_im]

/-- **Almost-everywhere Mellin evaluation of `stepSpectralWeight`.** -/
theorem stepSpectralWeight_eq_ae_mellin_normSq {r : ℕ} (hr : 1 < r) :
    stepSpectralWeight hr =ᵐ[volume] fun ξ : ℝ =>
      ‖riemannZeta ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) /
        ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
        pmRamanujanMellinSymbol r ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2 := by
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
        sqrt_exp_eq_half_local]
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
  filter_upwards [hF] with ξ hξ
  unfold stepSpectralWeight
  rw [hξ, Real.fourier_congr_ae hU ξ]
  congr 1
  have hflip : 𝓕 (halfDensityPullback (pmRamanujanStepSource r)) ξ =
      𝓕 (halfDensityPullback (pmRamanujanPrimitiveSource r)) (-ξ) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    have hstep_neg : halfDensityPullback (pmRamanujanStepSource r) (-u) =
        halfDensityPullback (pmRamanujanPrimitiveSource r) u := by
      unfold halfDensityPullback pmRamanujanStepSource pmRamanujanPrimitiveSource stepFun
      rw [pmRamanujanPrimitive_re_ofReal_local,
        show 1 / Real.exp u = Real.exp (-u) by rw [one_div, Real.exp_neg],
        sqrt_exp_eq_half_local, sqrt_exp_eq_half_local]
      have hexp : ((Real.exp (-u / 2) : ℝ) : ℂ) * ((Real.exp (-u) : ℝ) : ℂ)⁻¹ =
          ((Real.exp (u / 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Real.exp_neg, inv_inv, ← Real.exp_add]
        congr 2; ring
      calc ((Real.exp (-u / 2) : ℝ) : ℂ) *
            (pmRamanujanPrimitive r ⌊Real.exp (-u)⌋₊ * ((Real.exp (-u) : ℝ) : ℂ)⁻¹)
          = (((Real.exp (-u / 2) : ℝ) : ℂ) * ((Real.exp (-u) : ℝ) : ℂ)⁻¹) *
              pmRamanujanPrimitive r ⌊Real.exp (-u)⌋₊ := by ring
        _ = ((Real.exp (u / 2) : ℝ) : ℂ) * pmRamanujanPrimitive r ⌊Real.exp (-u)⌋₊ := by rw [hexp]
    rw [hstep_neg]
    congr 2
    ring
  rw [hflip, fourier_halfDensityPullback]
  have hs_eq : (1 / 2 - 2 * ↑Real.pi * ↑(-ξ) * I : ℂ) =
      (1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hs_eq]
  have hs_re : ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I).re = 1 / 2 := by
    have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have h2 : (((2 * Real.pi * ξ : ℝ) : ℂ) * I).re = 0 := by simp
    rw [Complex.add_re, h1, h2, add_zero]
  exact congrArg norm (hasMellin_pmRamanujanPrimitiveSource hr
    (by rw [hs_re]; norm_num) (by rw [hs_re]; norm_num)).2

/-- `moebiusPolySq (1/2) t D` coincides identically with the critical-line squared norm of `M_D`. -/
theorem moebiusPolySq_half_eq_normSq_edPoly (t : ℝ) (D : ℕ) :
    moebiusPolySq (1 / 2) t D =
      ‖RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  set P : ℂ := RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hterm : ∀ d ∈ Finset.Icc 1 D,
      NearLineLogMean.moebiusMollifierCoeff d *
        (d : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log d) : ℝ) : ℂ) -
        ((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sin (t * Real.log d) : ℝ) : ℂ) * I := by
    intro d hd
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hd_ne : (d : ℂ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hd_ne, ← Complex.ofReal_natCast d, ← Complex.ofReal_log hd_pos.le]
    have hexp_arg : (↑(Real.log (d : ℝ)) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) : ℂ) =
        ((-(1 / 2 : ℝ) * Real.log d : ℝ) : ℂ) + ((-(t * Real.log d) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hexp_arg, Complex.exp_add, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp]
    have hrpow_eq : Real.exp (-(1 / 2 : ℝ) * Real.log d) = (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hd_pos]; ring_nf
    rw [hrpow_eq, NearLineLogMean.moebiusMollifierCoeff]
    have hμ : ((ArithmeticFunction.moebius d : ℤ) : ℂ) = ((moebiusReal d : ℝ) : ℂ) := by
      simp [moebiusReal]
    rw [hμ]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hP : P = ((∑ d ∈ Finset.Icc 1 D,
        moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log d) : ℝ) : ℂ) -
      ((∑ d ∈ Finset.Icc 1 D,
        moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sin (t * Real.log d) : ℝ) : ℂ) * I := by
    dsimp [P, RHTower.edPoly]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
    push_cast
    rfl
  rw [Complex.sq_norm, Complex.normSq_apply, hP]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero,
    Complex.sub_im, Complex.mul_im, add_zero, zero_sub]
  unfold moebiusPolySq
  ring

/-- **Direct unweighted `[1, T]` moment majorant via `sizeHypercubeForm` at `ε = 0, r = 2`.**
For every `T ≥ 1` and `D : ℕ`,
`∫_1^T ‖ζ(½ + it) M_D(½ + it)‖² dt ≤ (25 π / 2) (1/4 + T²) · sizeHypercubeForm_{r=2}(0, D)`. -/
theorem integral_normSq_zeta_moebius_le_sizeHypercubeForm_zero {T : ℝ} (hT : 1 ≤ T) (D : ℕ) :
    (∫ t in (1 : ℝ)..T,
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (25 * Real.pi / 2) * (1 / 4 + T ^ 2) * sizeHypercubeForm Nat.one_lt_two 0 D := by
  have hπ_pos : 0 < 2 * Real.pi := by positivity
  set g : ℝ → ℝ := fun t =>
    (4 / 25 : ℝ) *
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2)
  set F : ℝ → ℝ := fun ξ =>
    stepSpectralWeight Nat.one_lt_two ξ * moebiusPolySq (1 / 2) (2 * Real.pi * ξ) D
  have hF_int : Integrable F := by
    refine (integrable_stepSpectralWeight Nat.one_lt_two).mul_bdd
      (by unfold moebiusPolySq; fun_prop :
        Continuous fun ξ => moebiusPolySq (1 / 2) (2 * Real.pi * ξ) D).aestronglyMeasurable
      (c := (∑ d ∈ Finset.Icc 1 D, (d : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (moebiusPolySq_nonneg _ _ _)]
    exact moebiusPolySq_le _ _ _
  have hg_cont : Continuous g := by
    dsimp [g]
    have hc1 : Continuous fun t : ℝ =>
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      have heq : (fun t : ℝ =>
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
          fun t : ℝ => ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint t) *
            MultiscaleMollifiedZetaField.moebiusPoly D
              (MultiscaleMollifiedZetaField.linePoint t)‖ ^ 2 := by
        ext t
        rw [NearLineLogMean.edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
        unfold MultiscaleMollifiedZetaField.linePoint
        norm_num
      rw [heq]
      have hcζ : Continuous fun u : ℝ => riemannZeta (MultiscaleMollifiedZetaField.linePoint u) :=
        continuous_iff_continuousAt.mpr fun u =>
          (differentiableAt_riemannZeta
            (MultiscaleMollifiedZetaField.linePoint_ne_one u)).continuousAt.comp
            MultiscaleMollifiedZetaField.continuous_linePoint.continuousAt
      exact (hcζ.mul ((MultiscaleMollifiedZetaField.differentiable_moebiusPoly D).continuous.comp
        MultiscaleMollifiedZetaField.continuous_linePoint)).norm.pow 2
    exact ((continuous_const.mul hc1).div (by fun_prop) (fun t => by positivity))
  have hae_le : (fun ξ : ℝ => g (2 * Real.pi * ξ)) ≤ᵐ[volume] F := by
    filter_upwards [stepSpectralWeight_eq_ae_mellin_normSq Nat.one_lt_two] with ξ hξ
    dsimp [F, g]
    rw [hξ, moebiusPolySq_half_eq_normSq_edPoly (2 * Real.pi * ξ) D]
    set t : ℝ := 2 * Real.pi * ξ
    have hcast : ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I) = (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
      norm_num
    rw [hcast]
    have hrhs : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        pmRamanujanMellinSymbol 2 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 =
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          ‖pmRamanujanMellinSymbol 2 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      rw [norm_mul, norm_div, mul_pow, div_pow]
    rw [hrhs]
    have hden_eq : ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [hden_eq]
    have heul := four_div_twentyFive_le_normSq_pmRamanujanMellinSymbol_two t
    have hcast2 : pmRamanujanMellinSymbol 2 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
        pmRamanujanMellinSymbol 2 ((1 / 2 : ℂ) + (t : ℂ) * I) := by norm_num
    rw [hcast2]
    set Z2 : ℝ := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
    set M2 : ℝ := ‖RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
    have hprod_norm : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 = Z2 * M2 := by
      rw [norm_mul, mul_pow]
    rw [hprod_norm]
    have hden_pos : 0 < 1 / 4 + t ^ 2 := by positivity
    calc (4 / 25 : ℝ) * (Z2 * M2) / (1 / 4 + t ^ 2)
        = (Z2 / (1 / 4 + t ^ 2) * (4 / 25)) * M2 := by ring
      _ ≤ (Z2 / (1 / 4 + t ^ 2) *
            ‖pmRamanujanMellinSymbol 2 ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) * M2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left heul (div_nonneg (sq_nonneg _) hden_pos.le))
            (sq_nonneg _)
  have hg_comp_int : Integrable (fun ξ : ℝ => g (2 * Real.pi * ξ)) := by
    refine hF_int.mono' (hg_cont.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    filter_upwards [hae_le] with ξ hle
    have hnn : 0 ≤ g (2 * Real.pi * ξ) := by dsimp [g]; positivity
    rw [Real.norm_of_nonneg hnn]
    exact hle
  have hg_int : Integrable g := by
    have h := (integrable_comp_mul_left_iff g hπ_pos.ne').mp hg_comp_int
    exact h
  have hint_R : (1 / (2 * Real.pi)) * (∫ t : ℝ, g t) ≤ sizeHypercubeForm Nat.one_lt_two 0 D := by
    rw [sizeHypercubeForm_eq_integral Nat.one_lt_two 0 D, add_zero]
    have hchg := Measure.integral_comp_mul_left g (2 * Real.pi)
    rw [abs_of_pos (inv_pos.mpr hπ_pos), smul_eq_mul] at hchg
    rw [one_div, ← hchg]
    exact integral_mono_ae hg_comp_int hF_int hae_le
  have hsub_int : (∫ t in (1 : ℝ)..T, g t) ≤ ∫ t : ℝ, g t := by
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_le_integral hg_int (Eventually.of_forall fun t => by dsimp [g]; positivity)
  set Z_M : ℝ → ℝ := fun t =>
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
  have hZM_cont : Continuous Z_M := by
    dsimp [Z_M]
    have heq : (fun t : ℝ =>
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        fun t : ℝ => ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint t) *
          MultiscaleMollifiedZetaField.moebiusPoly D
            (MultiscaleMollifiedZetaField.linePoint t)‖ ^ 2 := by
      ext t
      rw [NearLineLogMean.edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
      unfold MultiscaleMollifiedZetaField.linePoint
      norm_num
    rw [heq]
    have hcζ : Continuous fun u : ℝ => riemannZeta (MultiscaleMollifiedZetaField.linePoint u) :=
      continuous_iff_continuousAt.mpr fun u =>
        (differentiableAt_riemannZeta
          (MultiscaleMollifiedZetaField.linePoint_ne_one u)).continuousAt.comp
          MultiscaleMollifiedZetaField.continuous_linePoint.continuousAt
    exact (hcζ.mul ((MultiscaleMollifiedZetaField.differentiable_moebiusPoly D).continuous.comp
      MultiscaleMollifiedZetaField.continuous_linePoint)).norm.pow 2
  have hpt_T : ∀ t ∈ Set.Icc (1 : ℝ) T, Z_M t ≤ (25 / 4) * (1 / 4 + T ^ 2) * g t := by
    intro t ht
    dsimp [g, Z_M]
    have ht_sq : 1 / 4 + t ^ 2 ≤ 1 / 4 + T ^ 2 := by
      have : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) ht.2 2
      linarith
    have hden_pos : 0 < 1 / 4 + t ^ 2 := by positivity
    have hZM_nn : 0 ≤ Z_M t := sq_nonneg _
    change Z_M t ≤ (25 / 4) * (1 / 4 + T ^ 2) * ((4 / 25) * Z_M t / (1 / 4 + t ^ 2))
    calc Z_M t = (25 / 4) * (1 / 4 + t ^ 2) * ((4 / 25) * Z_M t / (1 / 4 + t ^ 2)) := by
          field_simp [hden_pos.ne']
      _ ≤ (25 / 4) * (1 / 4 + T ^ 2) * ((4 / 25) * Z_M t / (1 / 4 + t ^ 2)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ht_sq (by norm_num)) (by positivity)
  have hmono_T : (∫ t in (1 : ℝ)..T, Z_M t) ≤
      ∫ t in (1 : ℝ)..T, (25 / 4) * (1 / 4 + T ^ 2) * g t :=
    intervalIntegral.integral_mono_on hT (hZM_cont.intervalIntegrable _ _)
      ((hg_cont.const_mul _).intervalIntegrable _ _) hpt_T
  rw [intervalIntegral.integral_const_mul] at hmono_T
  have hscale : (∫ t : ℝ, g t) ≤ 2 * Real.pi * sizeHypercubeForm Nat.one_lt_two 0 D := by
    have := mul_le_mul_of_nonneg_left hint_R hπ_pos.le
    rwa [← mul_assoc, mul_one_div_cancel hπ_pos.ne', one_mul] at this
  calc (∫ t in (1 : ℝ)..T, Z_M t)
      ≤ (25 / 4) * (1 / 4 + T ^ 2) * (∫ t in (1 : ℝ)..T, g t) := hmono_T
    _ ≤ (25 / 4) * (1 / 4 + T ^ 2) * (∫ t : ℝ, g t) :=
        mul_le_mul_of_nonneg_left hsub_int (by positivity)
    _ ≤ (25 / 4) * (1 / 4 + T ^ 2) * (2 * Real.pi * sizeHypercubeForm Nat.one_lt_two 0 D) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (25 * Real.pi / 2) * (1 / 4 + T ^ 2) * sizeHypercubeForm Nat.one_lt_two 0 D := by ring

/-! ## §3. Finite-cutoff periodicity, zero-damping `L²(1, D)` bound, and sawtooth far tail -/

/-- **Exact `r`-periodicity of `forwardDilatedPrimitive` on `[0, ∞)`.** -/
theorem forwardDilatedPrimitive_add_natCast {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    forwardDilatedPrimitive r ε D (x + r) = forwardDilatedPrimitive r ε D x := by
  unfold forwardDilatedPrimitive
  refine Finset.sum_congr rfl fun d _ => ?_
  have hfl : ⌊(d : ℝ) * (x + r)⌋₊ = ⌊(d : ℝ) * x⌋₊ + d * r := by
    rw [show (d : ℝ) * (x + r) = (d : ℝ) * x + ((d * r : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg d) hx) (d * r)]
  rw [hfl, pmRamanujanPrimitive_re_add_mul_self hr]

/-- Elementary harmonic bound `∑_{1 ≤ d ≤ D} 1 / d ≤ 1 + log D` for `D ≥ 1`. -/
theorem sum_Icc_inv_le_one_add_log {D : ℕ} (hD : 1 ≤ D) :
    ∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ)) ≤ 1 + Real.log D := by
  induction D, hD using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hstep : 1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hk1_pos hk_pos)
      rw [inv_div, Real.log_div hk1_pos.ne' hk_pos.ne'] at hlog
      have hsub : 1 - (k : ℝ) / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) := by
        field_simp [hk1_pos.ne']; ring
      linarith
    push_cast
    linarith

/-- Pointwise harmonic bound `|forwardDilatedPrimitive 2 0 D x| ≤ 1 + log D` for `D ≥ 1`. -/
theorem abs_forwardDilatedPrimitive_two_zero_le {D : ℕ} (hD : 1 ≤ D) (x : ℝ) :
    |forwardDilatedPrimitive 2 0 D x| ≤ 1 + Real.log D := by
  rw [forwardDilatedPrimitive_two_eq, abs_neg]
  calc |∑ d ∈ Finset.Icc 1 D,
          moebiusReal d * (d : ℝ) ^ (-1 - (0 : ℝ)) * ((⌊(d : ℝ) * x⌋₊ % 2 : ℕ) : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 D,
          |moebiusReal d * (d : ℝ) ^ (-1 - (0 : ℝ)) * ((⌊(d : ℝ) * x⌋₊ % 2 : ℕ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hμ : |moebiusReal d| ≤ 1 := by
          unfold moebiusReal
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        have hmod : ((⌊(d : ℝ) * x⌋₊ % 2 : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt _ two_pos)
        rw [sub_zero, Real.rpow_neg_one, abs_mul, abs_mul,
          abs_of_pos (inv_pos.mpr hd_pos),
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (⌊(d : ℝ) * x⌋₊ % 2)), one_div]
        calc |moebiusReal d| * (d : ℝ)⁻¹ * ((⌊(d : ℝ) * x⌋₊ % 2 : ℕ) : ℝ)
            ≤ 1 * (d : ℝ)⁻¹ * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_right hμ (inv_nonneg.mpr hd_pos.le))
                hmod (Nat.cast_nonneg _) (by positivity)
          _ = (d : ℝ)⁻¹ := by ring
    _ ≤ 1 + Real.log D := sum_Icc_inv_le_one_add_log hD

/-- **Zero-damping exterior ray bound at `r = 2`.**
For every `D ≥ 1`, `∫_1^∞ G_{0, D}(x)² dx / x² ≤ (1 + log D)²`. -/
theorem integral_Ioi_one_forwardDilatedPrimitive_two_zero_le {D : ℕ} (hD : 1 ≤ D) :
    (∫ x in Set.Ioi (1 : ℝ), forwardDilatedPrimitive 2 0 D x ^ 2 / x ^ 2) ≤
      (1 + Real.log D) ^ 2 := by
  set C : ℝ := 1 + Real.log D
  have hint1 : IntegrableOn (fun x : ℝ => forwardDilatedPrimitive 2 0 D x ^ 2 / x ^ 2)
      (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_forwardDilatedPrimitive_sq Nat.one_lt_two 0 D).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)
  have hint2 : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (zero_lt_one : (0 : ℝ) < 1)).const_mul (C ^ 2)
  have hle : (∫ x in Set.Ioi (1 : ℝ), forwardDilatedPrimitive 2 0 D x ^ 2 / x ^ 2) ≤
      ∫ x in Set.Ioi (1 : ℝ), C ^ 2 * x ^ (-2 : ℝ) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_forwardDilatedPrimitive_two_zero_le hD x) 2
  refine hle.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (zero_lt_one : (0 : ℝ) < 1)]
  norm_num

/-- **Zero-damping compact `L²(1, D)` majorant for `sizeHypercubeForm` at `r = 2`.** -/
theorem sizeHypercubeForm_two_zero_le_alternating_Ioo_add_log {D : ℕ} (hD : 1 ≤ D) :
    sizeHypercubeForm Nat.one_lt_two 0 D ≤
      (∫ u in Set.Ioo (1 : ℝ) D,
        (∑ d ∈ Finset.Icc 1 D,
          moebiusReal d / (d : ℝ) * ((⌊(d : ℝ) / u⌋₊ % 2 : ℕ) : ℝ)) ^ 2) +
        (1 + Real.log D) ^ 2 := by
  rw [sizeHypercubeForm_eq_Ioo_zero_one_add_Ioi_one Nat.one_lt_two 0 D,
    integral_Ioo_zero_one_forwardDilatedPrimitive_eq 2 0 D]
  refine add_le_add ?_ (integral_Ioi_one_forwardDilatedPrimitive_two_zero_le hD)
  refine le_of_eq (setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_)
  rw [forwardDilatedPrimitive_two_eq, neg_sq]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sub_zero, Real.rpow_neg_one, div_eq_mul_inv, div_eq_mul_inv]

/-- **Unconditional `≤ 4` far-tail bound for the sharp Möbius sawtooth defect.**
For every `X ≥ 1`, `∫_{x > X²} F_X(x)² dx / x² ≤ 4`. -/
theorem integral_Ioi_sq_sawtoothDefect_sharpCoeff_le_four {X : ℕ} (hX : 1 ≤ X) :
    (∫ x in Set.Ioi ((X : ℝ) ^ 2),
      ArithmeticProduction.sawtoothDefect (Finset.Icc 1 X) ArithmeticProduction.sharpCoeff x ^ 2 /
        x ^ 2) ≤ 4 := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX2_pos : 0 < (X : ℝ) ^ 2 := by positivity
  have hpt : ∀ x : ℝ,
      |ArithmeticProduction.sawtoothDefect (Finset.Icc 1 X) ArithmeticProduction.sharpCoeff x| ≤
        2 * (X : ℝ) := by
    intro x
    unfold ArithmeticProduction.sawtoothDefect
    have h1 : |if 1 ≤ x then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    have h2 : |∑ n ∈ Finset.Icc 1 X, ArithmeticProduction.sharpCoeff n * Int.fract (x / n)| ≤ X := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Finset.Icc 1 X, |ArithmeticProduction.sharpCoeff n * Int.fract (x / n)|
          ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (x / (n : ℝ)))]
            have hμ : |ArithmeticProduction.sharpCoeff n| ≤ 1 := by
              unfold ArithmeticProduction.sharpCoeff
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
            nlinarith [Int.fract_lt_one (x / (n : ℝ)), abs_nonneg (ArithmeticProduction.sharpCoeff n)]
        _ = (X : ℝ) := by simp
    have htri := abs_add_le (if 1 ≤ x then (1 : ℝ) else 0)
      (∑ n ∈ Finset.Icc 1 X, ArithmeticProduction.sharpCoeff n * Int.fract (x / n))
    linarith
  have hmeasF : Measurable
      (ArithmeticProduction.sawtoothDefect (Finset.Icc 1 X) ArithmeticProduction.sharpCoeff) := by
    unfold ArithmeticProduction.sawtoothDefect
    refine (Measurable.ite measurableSet_Ici measurable_const measurable_const).add ?_
    refine Finset.measurable_sum _ fun n _ => Measurable.const_mul ?_ _
    exact measurable_fract.comp (measurable_id.div_const _)
  have hint_dom : IntegrableOn (fun x : ℝ => (2 * (X : ℝ)) ^ 2 * x ^ (-2 : ℝ))
      (Set.Ioi ((X : ℝ) ^ 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hX2_pos).const_mul _
  have hintF : IntegrableOn (fun x : ℝ =>
      ArithmeticProduction.sawtoothDefect (Finset.Icc 1 X) ArithmeticProduction.sharpCoeff x ^ 2 /
        x ^ 2) (Set.Ioi ((X : ℝ) ^ 2)) := by
    refine hint_dom.mono' ((hmeasF.pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hX2_pos (Set.mem_Ioi.mp hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hpt x) 2
  have hle : (∫ x in Set.Ioi ((X : ℝ) ^ 2),
      ArithmeticProduction.sawtoothDefect (Finset.Icc 1 X) ArithmeticProduction.sharpCoeff x ^ 2 /
        x ^ 2) ≤ ∫ x in Set.Ioi ((X : ℝ) ^ 2), (2 * (X : ℝ)) ^ 2 * x ^ (-2 : ℝ) := by
    refine setIntegral_mono_on hintF hint_dom measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans hX2_pos (Set.mem_Ioi.mp hx)
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hpt x) 2
  refine hle.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hX2_pos]
  have hpow : ((X : ℝ) ^ 2) ^ ((-2 : ℝ) + 1) = ((X : ℝ) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow]
  field_simp [hX2_pos.ne']
  ring

/-! ## §4. Direct `K = 3` producer bridges to `route-wd` §1 and `zetaZeroWidth` -/

/-- General scale-lifting helper: if `∫_1^T ‖ζ M_D‖² dt ≤ A · T² · Φ(D) + B · T` for `T ≥ 1`, then
any sparse bound `Φ(D) ≤ C_η D^{2β + η}` (`∃ᶠ D in atTop`) directly produces the cofinal
`route-wd` §1 moment bound with exponent `3 + 2 β θ`. -/
private theorem cofinal_moebius_moment_of_discrete_majorant {Φ : ℕ → ℝ} {A B β : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hmaj : ∀ (T : ℝ) (D : ℕ), 1 ≤ T → 1 ≤ D →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        A * T ^ 2 * Φ D + B * T)
    (hsparse : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ D : ℕ in atTop, Φ D ≤ C * (D : ℝ) ^ (2 * β + η)) :
    ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C' * T ^ (3 + 2 * β * θ) := by
  intro θ₀ hθ₀
  set m : ℕ := max 1 ⌈θ₀⌉₊
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm_ge : θ₀ ≤ (m : ℝ) := (Nat.le_ceil θ₀).trans (by exact_mod_cast le_max_right 1 ⌈θ₀⌉₊)
  obtain ⟨C, hC0, hfreqD⟩ := hsparse (1 / (m : ℝ)) (by positivity)
  refine ⟨(m : ℝ), hm_ge, A * C + B, by positivity, ?_⟩
  rw [Filter.frequently_atTop] at hfreqD ⊢
  intro T_min
  set D_min : ℕ := ⌈(max 1 T_min) ^ (m : ℝ)⌉₊ + 1
  obtain ⟨D, hD_ge, hΦD⟩ := hfreqD D_min
  have hD1 : 1 ≤ D := by omega
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast hD1
  have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  set T : ℝ := (D : ℝ) ^ (1 / (m : ℝ))
  have hT1 : 1 ≤ T := Real.one_le_rpow hD1R (by positivity)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTm_eq : T ^ (m : ℝ) = (D : ℝ) := by
    dsimp [T]
    rw [← Real.rpow_mul hD_pos.le, one_div_mul_cancel hm_pos.ne', Real.rpow_one]
  have hfl_eq : ⌊T ^ (m : ℝ)⌋₊ = D := by
    rw [hTm_eq, Nat.floor_natCast]
  have hT_ge_min : T_min ≤ T := by
    have hmax_pos : 0 < max 1 T_min := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hle_D : (max 1 T_min) ^ (m : ℝ) ≤ (D : ℝ) := by
      calc (max 1 T_min) ^ (m : ℝ) ≤ (⌈(max 1 T_min) ^ (m : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (D_min : ℝ) := by dsimp [D_min]; exact_mod_cast (Nat.le_succ _)
        _ ≤ (D : ℝ) := by exact_mod_cast hD_ge
    calc T_min ≤ max 1 T_min := le_max_right _ _
      _ = ((max 1 T_min) ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
          rw [← Real.rpow_mul hmax_pos.le, mul_one_div_cancel hm_pos.ne', Real.rpow_one]
      _ ≤ (D : ℝ) ^ (1 / (m : ℝ)) := Real.rpow_le_rpow (by positivity) hle_D (by positivity)
  refine ⟨T, hT_ge_min, ?_⟩
  rw [hfl_eq]
  have h1 := hmaj T D hT1 hD1
  have hDrpow : (D : ℝ) ^ (2 * β + 1 / (m : ℝ)) = T ^ (2 * β * (m : ℝ) + 1) := by
    rw [← hTm_eq, ← Real.rpow_mul hT0.le]
    congr 1
    field_simp [hm_pos.ne']
  have hT_le : T ≤ T ^ (3 + 2 * β * (m : ℝ)) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ (3 + 2 * β * (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
  calc (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ A * T ^ 2 * Φ D + B * T := h1
    _ ≤ A * T ^ 2 * (C * (D : ℝ) ^ (2 * β + 1 / (m : ℝ))) +
          B * T ^ (3 + 2 * β * (m : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hΦD (by positivity))
          (mul_le_mul_of_nonneg_left hT_le hB)
    _ = A * C * (T ^ (2 : ℝ) * T ^ (2 * β * (m : ℝ) + 1)) +
          B * T ^ (3 + 2 * β * (m : ℝ)) := by
        rw [hDrpow, Real.rpow_two]
        ring
    _ = (A * C + B) * T ^ (3 + 2 * β * (m : ℝ)) := by
        rw [← Real.rpow_add hT0]
        have hexp : (2 : ℝ) + (2 * β * (m : ℝ) + 1) = 3 + 2 * β * (m : ℝ) := by ring
        rw [hexp]
        ring

/-- **Direct `K = 3` producer bridge from `sizeHypercubeForm` at `ε = 0, r = 2` to `route-wd` §1.**
Sparse subpolynomial growth of `sizeHypercubeForm Nat.one_lt_two 0 D` directly yields the
`route-wd` §1 bound with fixed `K = 3` (without routing through zeros of `ζ`). -/
theorem cofinal_moebius_mollifier_of_frequently_sizeHypercubeForm_zero_subpolynomial
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ D : ℕ in atTop, sizeHypercubeForm Nat.one_lt_two 0 D ≤ C * (D : ℝ) ^ η) :
    ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C' * T ^ (3 : ℝ) := by
  have hmaj : ∀ (T : ℝ) (D : ℕ), 1 ≤ T → 1 ≤ D →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (125 * Real.pi / 8) * T ^ 2 * sizeHypercubeForm Nat.one_lt_two 0 D + 0 * T := by
    intro T D hT _
    refine (integral_normSq_zeta_moebius_le_sizeHypercubeForm_zero hT D).trans ?_
    have hnn := sizeHypercubeForm_nonneg Nat.one_lt_two 0 D
    have hπ := Real.pi_pos
    have h1 : 1 / 4 + T ^ 2 ≤ (5 / 4) * T ^ 2 := by nlinarith
    calc (25 * Real.pi / 2) * (1 / 4 + T ^ 2) * sizeHypercubeForm Nat.one_lt_two 0 D
        ≤ (25 * Real.pi / 2) * ((5 / 4) * T ^ 2) * sizeHypercubeForm Nat.one_lt_two 0 D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hnn
      _ = (125 * Real.pi / 8) * T ^ 2 * sizeHypercubeForm Nat.one_lt_two 0 D + 0 * T := by ring
  have hres := cofinal_moebius_moment_of_discrete_majorant
    (A := 125 * Real.pi / 8) (B := 0) (β := 0) (by positivity) le_rfl le_rfl hmaj
    (by simpa using h)
  simpa using hres

/-- **Zero-width bound from sparse `D^{2β + η}` control of `sizeHypercubeForm` at `ε = 0, r = 2`.** -/
theorem zetaZeroWidth_le_of_frequently_sizeHypercubeForm_zero_le {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ D : ℕ in atTop, sizeHypercubeForm Nat.one_lt_two 0 D ≤ C * (D : ℝ) ^ (2 * β + η)) :
    zetaZeroWidth ≤ β := by
  have hmaj : ∀ (T : ℝ) (D : ℕ), 1 ≤ T → 1 ≤ D →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (125 * Real.pi / 8) * T ^ 2 * sizeHypercubeForm Nat.one_lt_two 0 D + 0 * T := by
    intro T D hT _
    refine (integral_normSq_zeta_moebius_le_sizeHypercubeForm_zero hT D).trans ?_
    have hnn := sizeHypercubeForm_nonneg Nat.one_lt_two 0 D
    have hπ := Real.pi_pos
    have h1 : 1 / 4 + T ^ 2 ≤ (5 / 4) * T ^ 2 := by nlinarith
    calc (25 * Real.pi / 2) * (1 / 4 + T ^ 2) * sizeHypercubeForm Nat.one_lt_two 0 D
        ≤ (25 * Real.pi / 2) * ((5 / 4) * T ^ 2) * sizeHypercubeForm Nat.one_lt_two 0 D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hnn
      _ = (125 * Real.pi / 8) * T ^ 2 * sizeHypercubeForm Nat.one_lt_two 0 D + 0 * T := by ring
  exact NearLineLogMean.zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope hβ (by norm_num)
    (cofinal_moebius_moment_of_discrete_majorant (by positivity) le_rfl hβ hmaj h)

/-- **Direct `K = 3` producer bridge from the zero-damping compact `L²(1, D)` alternating Möbius
integral to `route-wd` §1.** -/
theorem cofinal_moebius_mollifier_of_frequently_alternating_moebius_zero_Ioo
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ D : ℕ in atTop,
        (∫ u in Set.Ioo (1 : ℝ) D,
          (∑ d ∈ Finset.Icc 1 D,
            moebiusReal d / (d : ℝ) * ((⌊(d : ℝ) / u⌋₊ % 2 : ℕ) : ℝ)) ^ 2) ≤
          C * (D : ℝ) ^ η) :
    ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C' * T ^ (3 : ℝ) := by
  refine cofinal_moebius_mollifier_of_frequently_sizeHypercubeForm_zero_subpolynomial fun η hη => ?_
  obtain ⟨C, hC0, hfreq⟩ := h η hη
  have hlog_sub : ∀ᶠ D : ℕ in atTop, 1 ≤ D ∧ (1 + Real.log D) ^ 2 ≤ (D : ℝ) ^ η := by
    refine (eventually_ge_atTop 1).and ?_
    have hev_pow : ∀ᶠ D : ℕ in atTop, max 2 (8 / η) ≤ (D : ℝ) ^ (η / 4) :=
      ((tendsto_rpow_atTop (by positivity : 0 < η / 4)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop (max 2 (8 / η))
    filter_upwards [eventually_ge_atTop 1, hev_pow] with D hD1 hD_pow
    have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have hD_pos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD1R
    set u : ℝ := (D : ℝ) ^ (η / 4)
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hD_pos _
    have hu2 : 2 ≤ u := (le_max_left 2 (8 / η)).trans hD_pow
    have hu8 : 8 / η ≤ u := (le_max_right 2 (8 / η)).trans hD_pow
    have hlog_u : Real.log u ≤ u := by
      have hexp := Real.add_one_le_exp (Real.log u)
      rw [Real.exp_log hu_pos] at hexp
      linarith
    have hlog_D : (η / 4) * Real.log D ≤ u := by
      have hlr : Real.log u = (η / 4) * Real.log D := Real.log_rpow hD_pos (η / 4)
      linarith
    have hηu : 8 ≤ u * η := (div_le_iff₀ hη).mp hu8
    have hlog_le : Real.log D ≤ u ^ 2 / 2 := by
      have hmul : η * Real.log D ≤ η * (u ^ 2 / 2) := by
        calc η * Real.log D = 4 * ((η / 4) * Real.log D) := by ring
          _ ≤ 4 * u := by linarith
          _ = (8 * u) / 2 := by ring
          _ ≤ ((u * η) * u) / 2 := by nlinarith
          _ = η * (u ^ 2 / 2) := by ring
      exact le_of_mul_le_mul_left hmul hη
    have hsum_le : 1 + Real.log D ≤ u ^ 2 := by nlinarith
    have hu_sq : u ^ 2 = (D : ℝ) ^ (η / 2) := by
      dsimp [u]
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hD_pos.le]
      congr 1; push_cast; ring
    have hnn : 0 ≤ 1 + Real.log D := add_nonneg zero_le_one (Real.log_nonneg hD1R)
    calc (1 + Real.log D) ^ 2 ≤ (u ^ 2) ^ 2 := pow_le_pow_left₀ hnn hsum_le 2
      _ = ((D : ℝ) ^ (η / 2)) ^ 2 := by rw [hu_sq]
      _ = (D : ℝ) ^ η := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hD_pos.le]
          congr 1; push_cast; ring
  refine ⟨C + 1, by positivity, ?_⟩
  refine (hfreq.and_eventually hlog_sub).mono fun D ⟨hIoo, hD1, hlogD⟩ => ?_
  calc sizeHypercubeForm Nat.one_lt_two 0 D
      ≤ (∫ u in Set.Ioo (1 : ℝ) D,
          (∑ d ∈ Finset.Icc 1 D,
            moebiusReal d / (d : ℝ) * ((⌊(d : ℝ) / u⌋₊ % 2 : ℕ) : ℝ)) ^ 2) +
          (1 + Real.log D) ^ 2 := sizeHypercubeForm_two_zero_le_alternating_Ioo_add_log hD1
    _ ≤ C * (D : ℝ) ^ η + (D : ℝ) ^ η := add_le_add hIoo hlogD
    _ = (C + 1) * (D : ℝ) ^ η := by ring

/-- **Direct `K = 3` producer bridge from `mollifierDefect(Icc 1 D, sharpCoeff)` to `route-wd` §1.** -/
theorem cofinal_moebius_mollifier_of_frequently_sharpDefect_subpolynomial
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ D : ℕ in atTop,
        ArithmeticProduction.mollifierDefect (Finset.Icc 1 D) ArithmeticProduction.sharpCoeff ≤
          C * (D : ℝ) ^ η) :
    ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∃ᶠ T : ℝ in atTop,
        (∫ t in (1 : ℝ)..T,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
              (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
          C' * T ^ (3 : ℝ) := by
  have hmaj : ∀ (T : ℝ) (D : ℕ), 1 ≤ T → 1 ≤ D →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        5 * Real.pi * T ^ 2 *
          ArithmeticProduction.mollifierDefect (Finset.Icc 1 D) ArithmeticProduction.sharpCoeff +
          2 * T := by
    intro T D hT _
    have hS : ∀ d ∈ Finset.Icc 1 D, 1 ≤ d := fun d hd => (Finset.mem_Icc.mp hd).1
    have hplanch := ArithmeticProduction.integral_normSq_zeta_realDirichletPoly_le_of_mollifierDefect
      hS ArithmeticProduction.sharpCoeff hT
    have heq_int : (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly NearLineLogMean.moebiusMollifierCoeff (Finset.Icc 1 D)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        ∫ t in (1 : ℝ)..T,
          ‖riemannZeta (1 / 2 + t * I) *
            RHTower.realDirichletPoly (Finset.Icc 1 D) ArithmeticProduction.sharpCoeff
              (1 / 2 + t * I)‖ ^ 2 := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hs : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = (1 / 2 + t * I) := by norm_num
      rw [hs]
      congr 2
    rw [heq_int]
    refine hplanch.trans ?_
    have hdef_nn : 0 ≤
        ArithmeticProduction.mollifierDefect (Finset.Icc 1 D) ArithmeticProduction.sharpCoeff := by
      unfold ArithmeticProduction.mollifierDefect
      exact integral_nonneg fun _ => sq_nonneg _
    have hT2 : 1 ≤ T ^ 2 := by nlinarith [hT]
    have hsub : 1 / 4 + T ^ 2 ≤ (5 / 4) * T ^ 2 := by linarith
    have h1 : 4 * Real.pi * (1 / 4 + T ^ 2) ≤ 5 * Real.pi * T ^ 2 := by
      calc 4 * Real.pi * (1 / 4 + T ^ 2)
          ≤ 4 * Real.pi * ((5 / 4) * T ^ 2) :=
            mul_le_mul_of_nonneg_left hsub (by positivity)
        _ = 5 * Real.pi * T ^ 2 := by ring
    have h2 : 4 * Real.pi * (1 / 4 + T ^ 2) *
        ArithmeticProduction.mollifierDefect (Finset.Icc 1 D) ArithmeticProduction.sharpCoeff ≤
        5 * Real.pi * T ^ 2 *
          ArithmeticProduction.mollifierDefect (Finset.Icc 1 D) ArithmeticProduction.sharpCoeff :=
      mul_le_mul_of_nonneg_right h1 hdef_nn
    linarith
  have hres := cofinal_moebius_moment_of_discrete_majorant
    (A := 5 * Real.pi) (B := 2) (β := 0) (by positivity) (by norm_num) le_rfl hmaj
    (by simpa using h)
  simpa using hres

end GaloisForLFunctions.SignedSuccessorArithmetic
