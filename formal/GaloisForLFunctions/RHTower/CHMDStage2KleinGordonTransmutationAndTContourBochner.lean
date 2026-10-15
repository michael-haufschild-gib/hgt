import GaloisForLFunctions.RHTower.CHMDStage1MultiplicativeResolventAndClampedBeam
import GaloisForLFunctions.RHTower.EvenSectorTwistedArcNull

/-!
# CHMD Stage 2: Klein–Gordon Mass-`1/2` Wave Pair, Exact Pole Cancellation, and T-Contour Bochner Positivity

This module formalizes **Stage 2** of the Causal Hyperbolic–Modular Duality (CHMD) route:

1. **The Klein–Gordon Mass-`1/2` Wave Pair `(V / 2, ∂_x V)` and Universal Pole Cancellation**:
   For any `V ∈ C³_c(ℝ)`, define the mass-`1/2` Klein–Gordon wave pair
   `kgHalfWave V = (1/2) V` and `kgDerivWave V = deriv V`.
   * **Spectral Dispersion Identity (`norm_sq_paperFT_kgHalfWave_add_kgDerivWave`)**:
     For all `r ∈ ℝ`,
     `‖paperFT (kgHalfWave V) r‖² + ‖paperFT (kgDerivWave V) r‖² = (1/4 + r²) ‖paperFT V r‖²`.
   * **Universal Pole Cancellation (`weilPoleTerm_kgHalfWave_add_kgDerivWave_eq_zero`)**:
     Without requiring parity or reality of `V`, the pole terms at `z = ±i/2` of `kgHalfWave V`
     and `kgDerivWave V` have opposite signs (`+1/4` and `-1/4`) and cancel identically:
     `weilPoleTerm (weilTest (kgHalfWave V) (kgHalfWave V)) +
       weilPoleTerm (weilTest (kgDerivWave V) (kgDerivWave V)) = 0`.
   * **Exact Resolvent-to-`L²` Transmutation (`bochnerResolventEnergy_kgHalfWave_add_kgDerivWave_eq`)**:
     Combining `bochnerResolventEnergy` across the Klein–Gordon pair cancels the singular resolvent
     kernel `1 / (1/4 + r²)` against the dispersion factor `1/4 + r²`, yielding the pure spectral
     `L²` mass `(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT V r‖ ^ 2`.

2. **Klein–Gordon Dispersion Lift `kgLift` and Unconditional T-Contour Bochner Positivity**:
   We define `kgLift T ρ = T (sqrtPrincipal (ρ² - 1/4))`, which maps `|ρ| ≥ 1/2` to the real
   frequency line `z = √(ρ² - 1/4) ∈ ℝ`, maps `|ρ| ≤ 1/2` to the imaginary critical segment
   `z = i √(1/4 - ρ²) ∈ i[-1/2, 1/2]`, and places the Weil pole node `z = ±i/2` at the exact origin
   `ρ = 0` (`kgLift_zero_eq_I_div_two`). We prove unconditional nonnegativity on `ρ ∈ ℝ` for:
   * all Gaussian-damped translation multipliers (`re_kgLift_gaussDamped_pairExp_nonneg`), and
   * the spectral square `specSq (paperFT g)` of any continuous compactly supported even real test
     `g : ℝ → ℝ` under both `kgLift` and `rhoLift` (`re_kgLift_specSq_paperFT_ofReal_even_nonneg`,
     `re_rhoLift_specSq_paperFT_ofReal_even_nonneg`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.CHMDStage2

open EvenSector OddSector WeilOneSided WeilPoleWeight WeilSpectral GaloisForLFunctions.HTGeometry

/-! ## Section 1: The Klein–Gordon Mass-`1/2` Wave Pair `(V / 2, ∂_x V)` -/

/-- The mass-`1/2` scalar component `(1/2) V(x)` of the Klein–Gordon wave pair. -/
def kgHalfWave (V : ℝ → ℂ) (x : ℝ) : ℂ := (1 / 2 : ℂ) * V x

/-- The derivative component `∂_x V(x)` of the Klein–Gordon wave pair. -/
def kgDerivWave (V : ℝ → ℂ) (x : ℝ) : ℂ := deriv V x

theorem contDiff_kgHalfWave {n : WithTop ℕ∞} {V : ℝ → ℂ} (hV : ContDiff ℝ n V) :
    ContDiff ℝ n (kgHalfWave V) :=
  contDiff_const.mul hV

theorem contDiff_kgDerivWave {V : ℝ → ℂ} (hV : ContDiff ℝ 3 V) :
    ContDiff ℝ 2 (kgDerivWave V) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) V from hV)).2.2

theorem hasCompactSupport_kgHalfWave {V : ℝ → ℂ} (hVc : HasCompactSupport V) :
    HasCompactSupport (kgHalfWave V) :=
  hVc.mul_left

theorem hasCompactSupport_kgDerivWave {V : ℝ → ℂ} (hVc : HasCompactSupport V) :
    HasCompactSupport (kgDerivWave V) :=
  hVc.deriv

theorem kgHalfWave_even {V : ℝ → ℂ} (hVe : ∀ x, V (-x) = V x) (x : ℝ) :
    kgHalfWave V (-x) = kgHalfWave V x := by
  unfold kgHalfWave
  rw [hVe]

theorem kgDerivWave_odd {V : ℝ → ℂ} (hVe : ∀ x, V (-x) = V x) (x : ℝ) :
    kgDerivWave V (-x) = -kgDerivWave V x := by
  have h : (fun y => V (-y)) = V := funext hVe
  have h1 := deriv_comp_neg V (-x)
  rw [h, neg_neg] at h1
  exact h1

/-- Fourier transform of `kgHalfWave V`: `paperFT (kgHalfWave V) z = (1/2) * paperFT V z`. -/
theorem paperFT_kgHalfWave (V : ℝ → ℂ) (z : ℂ) :
    paperFT (kgHalfWave V) z = (1 / 2 : ℂ) * paperFT V z := by
  unfold paperFT kgHalfWave
  have heq : (fun u : ℝ => (1 / 2 : ℂ) * V u * cexp (I * z * u)) =
      fun u : ℝ => (1 / 2 : ℂ) * (V u * cexp (I * z * u)) := by
    funext u; ring
  rw [heq, integral_const_mul]

/-- Fourier transform of `kgDerivWave V`: `paperFT (kgDerivWave V) z = -(I * z) * paperFT V z`. -/
theorem paperFT_kgDerivWave {V : ℝ → ℂ} (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V)
    (z : ℂ) :
    paperFT (kgDerivWave V) z = -(I * z) * paperFT V z :=
  paperFT_deriv_of_compact hV hVc z

/-- **Klein–Gordon Mass-`1/2` Spectral Dispersion Identity**:
For every `V ∈ C¹_c(ℝ)` and `r ∈ ℝ`,
`‖paperFT (kgHalfWave V) r‖² + ‖paperFT (kgDerivWave V) r‖² = (1/4 + r²) ‖paperFT V r‖²`. -/
theorem norm_sq_paperFT_kgHalfWave_add_kgDerivWave {V : ℝ → ℂ} (hV : ContDiff ℝ 1 V)
    (hVc : HasCompactSupport V) (r : ℝ) :
    ‖paperFT (kgHalfWave V) r‖ ^ 2 + ‖paperFT (kgDerivWave V) r‖ ^ 2 =
      (1 / 4 + r ^ 2) * ‖paperFT V r‖ ^ 2 := by
  rw [paperFT_kgHalfWave, paperFT_kgDerivWave hV hVc]
  rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  ring

/-- **Universal Klein–Gordon Pole Cancellation (`P(V/2) + P(∂_x V) = 0`)**:
For every `V ∈ C²_c(ℝ)`, the Weil pole terms of `kgHalfWave V` and `kgDerivWave V` cancel
identically (`+1/4` against `-1/4`). -/
theorem weilPoleTerm_kgHalfWave_add_kgDerivWave_eq_zero {V : ℝ → ℂ} (hV : ContDiff ℝ 2 V)
    (hVc : HasCompactSupport V) :
    weilPoleTerm (EF.weilTest (kgHalfWave V) (kgHalfWave V)) +
      weilPoleTerm (EF.weilTest (kgDerivWave V) (kgDerivWave V)) = 0 := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hd_cont : Continuous (kgDerivWave V) := hV1.continuous_deriv le_rfl
  have hh_cont : Continuous (kgHalfWave V) := (contDiff_kgHalfWave hV).continuous
  rw [weilPoleTerm_weilTest_eq hh_cont (hasCompactSupport_kgHalfWave hVc),
    weilPoleTerm_weilTest_eq hd_cont (hasCompactSupport_kgDerivWave hVc),
    paperFT_kgHalfWave, paperFT_kgHalfWave,
    paperFT_kgDerivWave hV1 hVc (I / 2), paperFT_kgDerivWave hV1 hVc (-I / 2)]
  have hI1 : -(I * (I / 2 : ℂ)) = (1 / 2 : ℂ) := by
    calc -(I * (I / 2 : ℂ)) = -(I * I) / 2 := by ring
      _ = (1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
  have hI2 : -(I * (-I / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    calc -(I * (-I / 2 : ℂ)) = (I * I) / 2 := by ring
      _ = -(1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
  rw [hI1, hI2]
  simp only [map_mul, map_neg, map_div₀, map_one, map_ofNat]
  ring

/-- For every `f : WeilTestFn`, `r ↦ ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))` is integrable on `ℝ`. -/
theorem integrable_normSq_paperFT_div (f : WeilTestFn) :
    Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hPn : ∀ r : ℝ, ‖paperFT (EF.weilTest f.1 f.1) r‖ = ‖paperFT f.1 r‖ ^ 2 := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2,
      Complex.conj_ofReal, Complex.mul_conj, Complex.norm_real, Real.norm_eq_abs,
      Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  have hFsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 :=
    (EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hkd hkc)).norm.congr
      (ae_of_all _ hPn)
  have hdiv : Continuous fun r : ℝ => 1 / (1 / 4 + r ^ 2) :=
    continuous_const.div (by fun_prop) fun r => by positivity
  refine (hFsq.const_mul 4).mono' (hFsq.aestronglyMeasurable.mul hdiv.aestronglyMeasurable)
    (ae_of_all _ fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : 1 / (1 / 4 + r ^ 2) ≤ (4 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg r]
  nlinarith [sq_nonneg ‖paperFT f.1 r‖]

/-- **Exact Resolvent-to-`L²` Transmutation for the Klein–Gordon Wave Pair**:
For every `V ∈ C³_c(ℝ)`, the sum of the Bochner resolvent energies of `kgHalfWave V` and
`kgDerivWave V` equals the pure spectral `L²` energy `(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT V r‖ ^ 2`. -/
theorem bochnerResolventEnergy_kgHalfWave_add_kgDerivWave_eq {V : ℝ → ℂ} (hV : ContDiff ℝ 3 V)
    (hVc : HasCompactSupport V) :
    bochnerResolventEnergy (EF.weilTest (kgHalfWave V) (kgHalfWave V)) +
      bochnerResolventEnergy (EF.weilTest (kgDerivWave V) (kgDerivWave V)) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT V r‖ ^ 2 := by
  have hV2 : ContDiff ℝ 2 V := hV.of_le (by norm_num)
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  let F1 : WeilTestFn := ⟨kgHalfWave V, contDiff_kgHalfWave hV2, hasCompactSupport_kgHalfWave hVc⟩
  let F2 : WeilTestFn := ⟨kgDerivWave V, contDiff_kgDerivWave hV, hasCompactSupport_kgDerivWave hVc⟩
  have hres1 : bochnerResolventEnergy (EF.weilTest (kgHalfWave V) (kgHalfWave V)) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT (kgHalfWave V) r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) :=
    bochnerResolventEnergy_weilTest_eq F1
  have hres2 : bochnerResolventEnergy (EF.weilTest (kgDerivWave V) (kgDerivWave V)) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT (kgDerivWave V) r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) :=
    bochnerResolventEnergy_weilTest_eq F2
  have hI1 : Integrable fun r : ℝ => ‖paperFT (kgHalfWave V) r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) :=
    integrable_normSq_paperFT_div F1
  have hI2 : Integrable fun r : ℝ => ‖paperFT (kgDerivWave V) r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) :=
    integrable_normSq_paperFT_div F2
  rw [hres1, hres2, ← mul_add, ← integral_add hI1 hI2]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  dsimp only
  rw [← add_mul, norm_sq_paperFT_kgHalfWave_add_kgDerivWave hV1 hVc r]
  have hpos : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Section 2: Klein–Gordon Mass-`1/2` Dispersion Lift `kgLift` and T-Contour Bochner Positivity -/

/-- The Klein–Gordon mass-`1/2` lift `kgLift T ρ = T (sqrtPrincipal (ρ² - 1/4))`, mapping `ρ ∈ ℝ`
onto the T-contour `ℝ ∪ i[-1/2, 1/2]` with the pole nodes `±i/2` at `ρ = 0`. -/
def kgLift (T : ℂ → ℂ) (ρ : ℂ) : ℂ := T (sqrtPrincipal (ρ ^ 2 - 1 / 4))

theorem kgLift_neg (T : ℂ → ℂ) (ρ : ℂ) : kgLift T (-ρ) = kgLift T ρ := by
  unfold kgLift; rw [neg_sq]

/-- For `1 / 4 ≤ ρ²`, `kgLift T ρ = T (√(ρ² - 1/4))` on the real frequency axis. -/
theorem kgLift_of_one_fourth_le_sq (T : ℂ → ℂ) {ρ : ℝ} (hρ : 1 / 4 ≤ ρ ^ 2) :
    kgLift T ρ = T ((Real.sqrt (ρ ^ 2 - 1 / 4) : ℝ) : ℂ) := by
  unfold kgLift
  rw [show (ρ : ℂ) ^ 2 - 1 / 4 = ((ρ ^ 2 - 1 / 4 : ℝ) : ℂ) by push_cast; ring,
    sqrtPrincipal_ofReal_of_nonneg (by linarith)]

/-- For `ρ² ≤ 1 / 4` and even `T`, `kgLift T ρ = T (i √(1/4 - ρ²))` on the imaginary critical
segment `i[-1/2, 1/2]`. -/
theorem kgLift_of_sq_le_one_fourth {T : ℂ → ℂ} (heven : ∀ z, T (-z) = T z) {ρ : ℝ}
    (hρ : ρ ^ 2 ≤ 1 / 4) :
    kgLift T ρ = T (I * ((Real.sqrt (1 / 4 - ρ ^ 2) : ℝ) : ℂ)) := by
  unfold kgLift
  have hsq : sqrtPrincipal ((ρ : ℂ) ^ 2 - 1 / 4) ^ 2 =
      (I * ((Real.sqrt (1 / 4 - ρ ^ 2) : ℝ) : ℂ)) ^ 2 := by
    rw [sqrtPrincipal_sq, mul_pow, Complex.I_sq,
      ← Complex.ofReal_pow (Real.sqrt (1 / 4 - ρ ^ 2)) 2,
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ ^ 2)]
    push_cast; ring
  rcases sqrtPrincipal_eq_or_neg hsq with h1 | h1
  · rw [h1]
  · rw [h1, heven]

/-- At `ρ = 0`, `kgLift T 0 = T (I / 2)` for every even `T`: the Weil pole sits at the origin of
the Klein–Gordon `ρ`-line. -/
theorem kgLift_zero_eq_I_div_two {T : ℂ → ℂ} (heven : ∀ z, T (-z) = T z) :
    kgLift T 0 = T (I / 2) := by
  have h := kgLift_of_sq_le_one_fourth heven (ρ := 0) (by norm_num)
  rw [Complex.ofReal_zero] at h
  rw [h]
  congr 1
  have hsqrt : Real.sqrt (1 / 4 - (0 : ℝ) ^ 2) = 1 / 2 := by
    rw [show (1 / 4 - (0 : ℝ) ^ 2 : ℝ) = (1 / 2) ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  push_cast
  ring

/-- **Unconditional Klein–Gordon T-Contour Nonnegativity of Translation Multipliers**:
For any finite family of shifts `x_k` with nonnegative weights `c_k ≥ 0`, the Gaussian-damped
translation pair multiplier has nonnegative `kgLift` across the entire real `ρ`-line. -/
theorem re_kgLift_gaussDamped_pairExp_nonneg {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ) (ε ρ : ℝ) :
    0 ≤ (kgLift (gaussDamped (translatePairExp s c x) ε) ρ).re := by
  rcases le_or_gt (1 / 4) (ρ ^ 2) with hρ | hρ
  · rw [kgLift_of_one_fourth_le_sq _ hρ]
    unfold gaussDamped
    rw [translatePairExp_ofReal, cexp_neg_mul_sq_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · rw [kgLift_of_sq_le_one_fourth
      (fun z => by unfold gaussDamped; rw [translatePairExp_neg, neg_sq]) hρ.le]
    set y := Real.sqrt (1 / 4 - ρ ^ 2)
    unfold gaussDamped translatePairExp
    rw [translateExpSum_I_mul, translateExpSum_I_mul,
      show -(ε : ℂ) * (I * (y : ℂ)) ^ 2 = ((ε * y ^ 2 : ℝ) : ℂ) by
        rw [mul_pow, Complex.I_sq]; push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h1 : 0 ≤ ∑ k ∈ s, c k * Real.exp (-(y * x k)) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk) (Real.exp_pos _).le
    have h2 : 0 ≤ ∑ k ∈ s, c k * Real.exp (-(y * -x k)) :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk) (Real.exp_pos _).le
    positivity

/-- For any real test `g : ℝ → ℝ`, `paperFT g (I * y)` is the real Laplace transform
`∫ u, g u * exp(-y * u)`. -/
theorem paperFT_ofReal_I_mul (g : ℝ → ℝ) (y : ℝ) :
    paperFT (fun u => (g u : ℂ)) (I * (y : ℂ)) =
      ((∫ u : ℝ, g u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  have he : I * (I * (y : ℂ)) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
    calc I * (I * (y : ℂ)) * (u : ℂ) = (I * I) * (y : ℂ) * (u : ℂ) := by ring
      _ = ((-(y * u) : ℝ) : ℂ) := by rw [Complex.I_mul_I]; push_cast; ring
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- For an even real test `g : ℝ → ℝ`, `specSq (paperFT g)` on the imaginary axis `z = i y` is the
nonnegative real square `(∫ u, g u * exp(-y * u)) ^ 2`. -/
theorem specSq_paperFT_ofReal_even_I_mul {g : ℝ → ℝ} (hge : ∀ u, g (-u) = g u) (y : ℝ) :
    specSq (paperFT fun u => (g u : ℂ)) (I * (y : ℂ)) =
      (((∫ u : ℝ, g u * Real.exp (-(y * u))) ^ 2 : ℝ) : ℂ) := by
  have hGe : ∀ z, paperFT (fun u => (g u : ℂ)) (-z) = paperFT (fun u => (g u : ℂ)) z :=
    paperFT_neg_of_even fun u => by simp only [hge]
  unfold specSq
  have hconj : conj (I * (y : ℂ)) = -(I * (y : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [hconj, hGe, paperFT_ofReal_I_mul, Complex.conj_ofReal, ← Complex.ofReal_mul, sq]

/-- **Unconditional T-Contour Positivity of `kgLift (specSq (paperFT g))` for Even Real Tests**:
For every even real function `g : ℝ → ℝ`, `0 ≤ (kgLift (specSq (paperFT g)) ρ).re` for all `ρ ∈ ℝ`. -/
theorem re_kgLift_specSq_paperFT_ofReal_even_nonneg {g : ℝ → ℝ} (hge : ∀ u, g (-u) = g u)
    (ρ : ℝ) :
    0 ≤ (kgLift (specSq (paperFT fun u => (g u : ℂ))) ρ).re := by
  have hGe : ∀ z, paperFT (fun u => (g u : ℂ)) (-z) = paperFT (fun u => (g u : ℂ)) z :=
    paperFT_neg_of_even fun u => by simp only [hge]
  have hSe : ∀ z, specSq (paperFT fun u => (g u : ℂ)) (-z) =
      specSq (paperFT fun u => (g u : ℂ)) z := by
    intro z; unfold specSq; rw [map_neg, hGe, hGe]
  rcases le_or_gt (1 / 4) (ρ ^ 2) with hρ | hρ
  · rw [kgLift_of_one_fourth_le_sq _ hρ, specSq_ofReal_eq, Complex.ofReal_re]
    positivity
  · rw [kgLift_of_sq_le_one_fourth hSe hρ.le, specSq_paperFT_ofReal_even_I_mul hge,
      Complex.ofReal_re]
    positivity

/-- **Unconditional T-Contour Positivity of `rhoLift (specSq (paperFT g))` for Even Real Tests**:
For every even real function `g : ℝ → ℝ`, `0 ≤ (rhoLift (specSq (paperFT g)) ρ).re` for all `ρ ∈ ℝ`. -/
theorem re_rhoLift_specSq_paperFT_ofReal_even_nonneg {g : ℝ → ℝ} (hge : ∀ u, g (-u) = g u)
    (ρ : ℝ) :
    0 ≤ (rhoLift (specSq (paperFT fun u => (g u : ℂ))) ρ).re := by
  have hGe : ∀ z, paperFT (fun u => (g u : ℂ)) (-z) = paperFT (fun u => (g u : ℂ)) z :=
    paperFT_neg_of_even fun u => by simp only [hge]
  have hSe : ∀ z, specSq (paperFT fun u => (g u : ℂ)) (-z) =
      specSq (paperFT fun u => (g u : ℂ)) z := by
    intro z; unfold specSq; rw [map_neg, hGe, hGe]
  rcases le_or_gt 2 (ρ ^ 2) with hρ | hρ
  · unfold rhoLift
    rw [show (ρ : ℂ) ^ 2 - 2 = ((ρ ^ 2 - 2 : ℝ) : ℂ) by push_cast; ring,
      sqrtPrincipal_ofReal_of_nonneg (by linarith), specSq_ofReal_eq, Complex.ofReal_re]
    positivity
  · rw [rhoLift_of_sq_le_two hSe hρ.le, specSq_paperFT_ofReal_even_I_mul hge, Complex.ofReal_re]
    positivity

end RHTower.CHMDStage2

end
