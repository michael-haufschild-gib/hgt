import GaloisForLFunctions.RHTower.CHMDStage3TwistedArcGroundStateAndSechAnnihilation
import GaloisForLFunctions.RHTower.CHMDStage1MultiplicativeResolventAndClampedBeam
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.EvenSectorCriticalZeroCarrier
import GaloisForLFunctions.RHTower.PolarConeArchimedeanCriterion

/-!
# CHMD Stage 4: Elliptic–Hyperbolic Closure and Single-Function Sech-Measure Rigidity

This module completes the four-stage **Causal Hyperbolic–Modular Duality (CHMD)** architecture by
combining Stages 1–3 with the Gaussian-smoothed sech-weight multiplier limit
(`EvenSectorFullPositivity`), the critical-zero carrier theorem (`EvenSectorCriticalZeroCarrier`),
and the prime-free polar cone criterion (`PolarConeArchimedeanCriterion`):

1. **Unconditional 1D Sech-Kernel Limit Formula for the Full Weil Functional
   (`tendsto_integral_sechKernel_gaussDamped_eq_re_weilFullFunctional`,
   `tendsto_integral_sechKernel_gaussDamped_vonMangoldt`)**:
   Without assuming `RiemannHypothesis` or any spectral measure, for every real compactly supported
   `C²` test function `f : ℝ → ℝ` and every weight `lam` with
   `|lam n| ≤ C_g √n (1 + log n)` (in particular unconditionally for `lam = Λ`),
   `(weilFullFunctional lam (EF.weilTest f f)).re` is the exact `k → ∞` limit of the 1D
   sech-convolution integrals
   `∫ t : ℝ, sechKernel (gaussDamped (paperFT f) (1 / (k + 1))) t * cosineShiftFn lam sechHalf t`.

2. **Single-Function Sech-Measure / Bochner Rigidity
   (`evenWeilDensity_specSq_nonneg_of_sechHalf_measure`,
   `weilPositiveFull_of_sechHalf_measure`,
   `riemannHypothesis_and_eq_vonMangoldt_of_sechHalf_measure`)**:
   Whereas `exists_cosineShift_measure` constructed a measure `ν_Φ` for every even strip function `Φ`
   assuming `WeilPositiveEvenAt 1 lam`, we prove the converse **single-function collapse**:
   if the **single 1D function** `cosineShiftFn lam sechHalf : ℝ → ℝ` is the characteristic function
   of a finite positive measure `ν` on `ℝ` (equivalently, is positive definite on `ℝ`), then:
   * `ν{ρ : ℝ | ρ² ≤ 2} = 0` (`measure_sq_le_two_eq_zero`, driven by the Stage 3 twisted-arc
     annihilation identity);
   * `ν{ρ : ℝ | 2 < ρ² ∧ Ξ(√(ρ² - 2)) ≠ 0} = 0` (`measure_xiC_ne_zero_eq_zero`);
   * `0 ≤ evenWeilDensity lam (specSq Ψ)` for every `Ψ` with `Multiplier (sechWeight Ψ)`;
   * `WeilPositiveFull lam` holds on **all** compactly supported `C²` test functions (both even and
     odd);
   * `RiemannHypothesis` holds and `lam n = Λ(n)` for all `n ≥ 2`.

3. **Unconditional Elliptic–Hyperbolic Decomposition of the Sech-Toeplitz Quadratic Form
   (`sum_sum_cosineShiftFn_eq_add_evenWeilDensity_unconditional`,
   `sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq`)**:
   Without assuming `WeilPositiveEvenAt 1 lam`, every finite Toeplitz quadratic form of
   `cosineShiftFn lam Φ` decomposes unconditionally as the sum of the even cosine-wave packet energy
   and the even sine-wave packet energy:
   `∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) =`
   `  evenWeilDensity lam (specSq (cosComb t c Φ)) + evenWeilDensity lam (specSq (sinComb t c Φ))`.

4. **Master CHMD Four-Stage Equivalence (`chmd_four_stage_master_equivalence`)**:
   Unifies the unconditional criteria across all four CHMD stages into a single theorem package.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate Nat

noncomputable section

namespace RHTower.CHMDStage4

open WeilOneSided WeilSpectral RHTower.EvenSector RHTower.WeilPolarMajorant
open RHTower.CHMDStage1 RHTower.CHMDStage2 RHTower.CHMDStage3
open GaloisForLFunctions.HTGeometry

/-! ## 1. Unconditional 1D Sech-Kernel Limit Formula for the Full Weil Functional -/

/-- **Unconditional Gaussian-Smoothed Sech-Kernel Identity.**
For every real compactly supported `C²` test function `f : ℝ → ℝ` and every `ε > 0`, the smoothed
even Weil density `evenWeilDensity lam (specSq (gaussDamped (paperFT f) ε))` equals the 1D integral
of `sechKernel (gaussDamped (paperFT f) ε)` against `cosineShiftFn lam sechHalf`, unconditionally
(without any measure hypothesis). -/
theorem evenWeilDensity_gaussDamped_eq_integral_sechKernel_unconditional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    evenWeilDensity lam (specSq (gaussDamped (paperFT fun u => (f u : ℂ)) ε)) =
      ∫ t : ℝ, sechKernel (gaussDamped (paperFT fun u => (f u : ℂ)) ε) t *
        cosineShiftFn lam sechHalf t :=
  evenWeilDensity_specSq_eq_integral_sechKernel_unconditional hg
    (multiplier_sechWeight_gaussDamped hf hfc hε)

/-- **Unconditional 1D Sech-Kernel Limit Formula for `weilFullFunctional`.**
For any real compactly supported `C²` test function `f : ℝ → ℝ` and any weight `lam` satisfying
`|lam n| ≤ C_g √n (1 + log n)`, the full Weil functional `Re W_lam(f ⋆ f̃)` is the `k → ∞` limit of
the 1D integral of `sechKernel (gaussDamped (paperFT f) (1 / (k + 1)))` against the single 1D
function `cosineShiftFn lam sechHalf`. -/
theorem tendsto_integral_sechKernel_gaussDamped_eq_re_weilFullFunctional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun k : ℕ =>
      ∫ t : ℝ, sechKernel (gaussDamped (paperFT fun u => (f u : ℂ)) (1 / ((k : ℝ) + 1))) t *
        cosineShiftFn lam sechHalf t)
      atTop (𝓝 (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) := by
  rw [re_weilFullFunctional_ofReal_eq_evenWeilDensity lam hf hfc]
  refine (tendsto_evenWeilDensity_gaussDamped hg hf hfc).congr fun k => ?_
  exact evenWeilDensity_gaussDamped_eq_integral_sechKernel_unconditional hg hf hfc (by positivity)

/-- **Unconditional 1D Sech-Kernel Limit Formula for `Λ`.**
For `lam = Λ` and every real compactly supported `C²` test function `f : ℝ → ℝ`, `Re W_Λ(f ⋆ f̃)` is
unconditionally the `k → ∞` limit of the 1D integral against `cosineShiftFn Λ sechHalf`. -/
theorem tendsto_integral_sechKernel_gaussDamped_vonMangoldt {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun k : ℕ =>
      ∫ t : ℝ, sechKernel (gaussDamped (paperFT fun u => (f u : ℂ)) (1 / ((k : ℝ) + 1))) t *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t)
      atTop (𝓝 (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) :=
  tendsto_integral_sechKernel_gaussDamped_eq_re_weilFullFunctional
    abs_vonMangoldt_le_sqrt_mul_one_add_log hf hfc

/-! ## 2. Single-Function Sech-Measure / Bochner Rigidity -/

/-- **Single-Function Sech-Measure Positivity on Multipliers.**
If `cosineShiftFn lam sechHalf` is the characteristic function of a finite positive measure `ν` on
`ℝ`, then `0 ≤ evenWeilDensity lam (specSq Ψ)` for every `Ψ` such that `sechWeight Ψ` is a
multiplier. Crucially, this requires **only** the measure `ν` for the single template `sechHalf`,
because the twisted-arc annihilation theorem `measure_sq_le_two_eq_zero` already forces
`ν{ρ : ℝ | ρ² ≤ 2} = 0` from `hν` alone. -/
theorem evenWeilDensity_specSq_nonneg_of_sechHalf_measure {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ))
    {Ψ : ℂ → ℂ} (hT : Multiplier (sechWeight Ψ)) :
    0 ≤ evenWeilDensity lam (specSq Ψ) := by
  have hA := measure_sq_le_two_eq_zero hg hν
  rw [evenWeilDensity_specSq_eq_integral_sechHalf hg hν hT]
  refine integral_nonneg_of_ae ?_
  have hc : ∀ᵐ ρ ∂ν, ρ ∉ {ρ : ℝ | ρ ^ 2 ≤ 2} := measure_eq_zero_iff_ae_notMem.mp hA
  filter_upwards [hc] with ρ hρ
  simp only [not_le] at hρ
  exact re_rhoLift_sechWeight_nonneg Ψ hρ.le

/-- If `cosineShiftFn lam sechHalf` is the characteristic function of a finite positive measure `ν`
on `ℝ`, then `0 ≤ Re W_lam(f ⋆ f̃)` for every real compactly supported `C²` test function `f`. -/
theorem re_weilFullFunctional_nonneg_of_sechHalf_measure {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  rw [re_weilFullFunctional_ofReal_eq_evenWeilDensity lam hf hfc]
  refine ge_of_tendsto (tendsto_evenWeilDensity_gaussDamped hg hf hfc)
    (Eventually.of_forall fun k => ?_)
  exact evenWeilDensity_specSq_nonneg_of_sechHalf_measure hg hν
    (multiplier_sechWeight_gaussDamped hf hfc (by positivity))

/-- **Single-Function Sech-Measure Full Positivity.**
If `cosineShiftFn lam sechHalf` is the characteristic function of a finite positive measure `ν` on
`ℝ`, then `WeilPositiveFull lam` holds on **all** compactly supported `C²` test functions (both even
and odd). -/
theorem weilPositiveFull_of_sechHalf_measure {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ)) :
    WeilPositiveFull lam :=
  weilPositiveFull_of_real fun _ hf hfc =>
    re_weilFullFunctional_nonneg_of_sechHalf_measure hg hν hf hfc

/-- **Single-Function Sech-Measure Rigidity (`RiemannHypothesis` and `lam = Λ`).**
If a sequence `lam` with `|lam n| ≤ C_g √n (1 + log n)` makes the single 1D function
`cosineShiftFn lam sechHalf` the characteristic function of a finite positive measure `ν` on `ℝ`,
then `RiemannHypothesis` holds, `lam n = Λ(n)` for all `n ≥ 2`, `ν{ρ² ≤ 2} = 0`, and `ν` is
carried purely by the critical zeros of `Ξ`. -/
theorem riemannHypothesis_and_eq_vonMangoldt_of_sechHalf_measure {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ)) :
    RiemannHypothesis ∧
      (∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      ν {ρ : ℝ | ρ ^ 2 ≤ 2} = 0 ∧
      ν {ρ : ℝ | 2 < ρ ^ 2 ∧ RHTower.XiC (Real.sqrt (ρ ^ 2 - 2)) ≠ 0} = 0 :=
  ⟨(weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
      (weilPositiveFull_of_sechHalf_measure hg hν)).1,
    (weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
      (weilPositiveFull_of_sechHalf_measure hg hν)).2,
    measure_sq_le_two_eq_zero hg hν,
    measure_xiC_ne_zero_eq_zero hg hν⟩

/-- **Single-Function Bochner Rigidity for `cosineShiftFn lam sechHalf`.**
If `cosineShiftFn lam sechHalf` is positive definite on `ℝ` (with real or complex coefficients),
then `RiemannHypothesis` holds and `lam n = Λ(n)` for all `n ≥ 2`. -/
theorem riemannHypothesis_and_eq_vonMangoldt_of_positiveDefinite_sechHalf {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpd : ∀ (N : ℕ) (t c : Fin N → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j * cosineShiftFn lam sechHalf (t j - t i)) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨ν, hfin, hν⟩ := exists_charFun_eq_of_positiveDefinite
    (positiveDefiniteOnReal_of_real (cosineShiftFn_neg lam sechHalf) hpd)
    (Complex.continuous_ofReal.comp (continuous_cosineShiftFn hg evenStrip_sechHalf))
  have h := riemannHypothesis_and_eq_vonMangoldt_of_sechHalf_measure hg hν
  exact ⟨h.1, h.2.1⟩

/-! ## 3. Unconditional Elliptic–Hyperbolic Decomposition of the Sech-Toeplitz Form -/

/-- **Unconditional Elliptic–Hyperbolic Decomposition of the Cosine-Shift Toeplitz Form.**
For any `lam` satisfying `|lam n| ≤ C_g √n (1 + log n)` and any even strip function `Φ`
(without assuming `WeilPositiveEvenAt 1 lam` or `RiemannHypothesis`), every finite Toeplitz
quadratic form of `cosineShiftFn lam Φ` equals the sum of the even Weil densities of the spectral
squares of `cosComb t c Φ` and `sinComb t c Φ`. -/
theorem sum_sum_cosineShiftFn_eq_add_evenWeilDensity_unconditional {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {N : ℕ} (t c : Fin N → ℝ) :
    ∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) =
      evenWeilDensity lam (specSq (cosComb t c Φ)) +
        evenWeilDensity lam (specSq (sinComb t c Φ)) := by
  have hgood : ∀ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
      GoodDensity (rhoCosShift (t p.2 - t p.1) Φ) := fun p _ => goodDensity_cosShift _ hΦ
  have hlin := evenWeilDensity_sum hg ((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ)
    (fun p => c p.1 * c p.2) hgood
  have hsum : ∑ i, ∑ j, c i * c j * cosineShiftFn lam Φ (t j - t i) =
      ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
        c p.1 * c p.2 * evenWeilDensity lam (rhoCosShift (t p.2 - t p.1) Φ) := by
    rw [Finset.sum_product]; rfl
  have hA := evenStrip_cosComb t c hΦ
  have hB := evenStrip_sinComb t c hΦ
  have hcongr : evenWeilDensity lam (fun z => ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ
      Finset.univ, ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) Φ z) =
      evenWeilDensity lam (fun z => specSq (cosComb t c Φ) z + specSq (sinComb t c Φ) z) := by
    have hI1 : |(I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    have hI2 : |(-I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    refine evenWeilDensity_congr ?_ ?_ fun r => ?_
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ hI1).symm
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ hI2).symm
    · exact (specSq_cosComb_add_specSq_sinComb t c Φ
        (abs_im_lt_sqrt_two (by simp; norm_num))).symm
  rw [hsum, ← hlin, hcongr,
    evenWeilDensity_add hg (goodDensity_specSq hA) (goodDensity_specSq hB)]

/-- **Unconditional Decomposition of the Sech-Toeplitz Form for `Λ`.**
For `lam = Λ` and `Φ = sechHalf`, the Toeplitz quadratic form decomposes unconditionally into the
even Weil densities of `cosComb t c sechHalf` and `sinComb t c sechHalf`. -/
theorem sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq {N : ℕ} (t c : Fin N → ℝ) :
    ∑ i, ∑ j, c i * c j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i) =
      evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (specSq (cosComb t c sechHalf)) +
        evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (specSq (sinComb t c sechHalf)) :=
  sum_sum_cosineShiftFn_eq_add_evenWeilDensity_unconditional
    abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf t c

/-! ## 4. Exact Single-Function CHMD Characterizations of the Riemann Hypothesis -/

/-- **Single-Function Sech-Toeplitz Criterion for the Riemann Hypothesis.**
`RiemannHypothesis` holds if and only if the single 1D function
`cosineShiftFn Λ sechHalf : ℝ → ℝ` has nonnegative finite Toeplitz quadratic forms on `ℝ`. -/
theorem riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (t c : Fin N → ℝ),
        0 ≤ ∑ i, ∑ j, c i * c j *
          cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf (t j - t i) := by
  constructor
  · intro hRH N t c
    have hEven : WeilPositiveEvenAt 1 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
      weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩
    exact sum_sum_cosineShiftFn_nonneg hEven abs_vonMangoldt_le_sqrt_mul_one_add_log
      evenStrip_sechHalf t c
  · intro hpd
    exact (riemannHypothesis_and_eq_vonMangoldt_of_positiveDefinite_sechHalf
      abs_vonMangoldt_le_sqrt_mul_one_add_log hpd).1

/-- **Single-Function Bochner Criterion for the Riemann Hypothesis.**
`RiemannHypothesis` holds if and only if `cosineShiftFn Λ sechHalf` is positive definite on `ℝ`. -/
theorem riemannHypothesis_iff_positiveDefiniteOnReal_cosineShiftFn_sechHalf :
    RiemannHypothesis ↔
      PositiveDefiniteOnReal
        (fun y => (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y : ℂ)) := by
  constructor
  · intro hRH
    exact positiveDefiniteOnReal_of_real
      (cosineShiftFn_neg (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf)
      (riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg.mp hRH)
  · intro hpd
    obtain ⟨ν, hfin, hν⟩ := exists_charFun_eq_of_positiveDefinite hpd
      (Complex.continuous_ofReal.comp
        (continuous_cosineShiftFn abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf))
    exact (riemannHypothesis_and_eq_vonMangoldt_of_sechHalf_measure
      abs_vonMangoldt_le_sqrt_mul_one_add_log hν).1

/-- **Single-Function Sech-Measure Criterion for the Riemann Hypothesis.**
`RiemannHypothesis` holds if and only if `cosineShiftFn Λ sechHalf` is the characteristic function
of a finite positive measure `ν` on `ℝ`. -/
theorem riemannHypothesis_iff_exists_sechHalf_measure_vonMangoldt :
    RiemannHypothesis ↔
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
        ∀ y, charFun ν y =
          (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y : ℂ) := by
  constructor
  · intro hRH
    have hEven : WeilPositiveEvenAt 1 (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
      weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩
    exact exists_cosineShift_measure hEven abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf
  · rintro ⟨ν, hfin, hν⟩
    exact (riemannHypothesis_and_eq_vonMangoldt_of_sechHalf_measure
      abs_vonMangoldt_le_sqrt_mul_one_add_log hν).1

/-- **Elliptic–Hyperbolic Wave-Packet Criterion for the Riemann Hypothesis.**
`RiemannHypothesis` holds if and only if for every finite wave packet `(t, c)` on `ℝ`, the sum of
the cosine-packet and sine-packet even Weil energies on `sechHalf` is nonnegative. -/
theorem riemannHypothesis_iff_forall_cosComb_sinComb_sechHalf_nonneg :
    RiemannHypothesis ↔
      ∀ (N : ℕ) (t c : Fin N → ℝ),
        0 ≤ evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (specSq (cosComb t c sechHalf)) +
            evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (specSq (sinComb t c sechHalf)) := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  exact forall_congr' fun N => forall_congr' fun t => forall_congr' fun c => by
    rw [sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq]

/-- **Master Four-Stage CHMD Equivalence Package.**
Unifies the equivalent formulations of `RiemannHypothesis` established across Stages 1–4 of the
Causal Hyperbolic–Modular Duality route:
1. Stage 1: Pole-free even positivity `WeilPositiveEvenPolar Λ`
   (`riemannHypothesis_iff_weilPositiveEvenPolar_vonMangoldt`);
2. Stage 1 / Polar Cone: Prime-free, pole-free archimedean nonnegativity
   `ArchimedeanNonnegOnPolarNonnegCone`
   (`riemannHypothesis_iff_archimedeanNonnegOnPolarNonnegCone`);
3. Stage 3 / Even Cone: Prime-blind positivity `PrimeBlindPositiveEvenAt 1`
   (`riemannHypothesis_iff_primeBlindPositiveEvenAt`);
4. Stage 4: Single-function Bochner positivity of `cosineShiftFn Λ sechHalf` on `ℝ`
   (`riemannHypothesis_iff_positiveDefiniteOnReal_cosineShiftFn_sechHalf`);
5. Stage 4: Existence of a single finite measure `ν` on `ℝ` with characteristic function
   `cosineShiftFn Λ sechHalf` (`riemannHypothesis_iff_exists_sechHalf_measure_vonMangoldt`);
6. Stage 4: Nonnegativity of the elliptic–hyperbolic `cosComb`/`sinComb` wave-packet energy on
   `sechHalf` (`riemannHypothesis_iff_forall_cosComb_sinComb_sechHalf_nonneg`). -/
theorem chmd_four_stage_master_equivalence :
    (RiemannHypothesis ↔
      WeilPositiveEvenPolar (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) ∧
    (RiemannHypothesis ↔ ArchimedeanNonnegOnPolarNonnegCone) ∧
    (RiemannHypothesis ↔ PrimeBlindPositiveEvenAt 1) ∧
    (RiemannHypothesis ↔
      PositiveDefiniteOnReal
        (fun y => (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y : ℂ))) ∧
    (RiemannHypothesis ↔
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
        ∀ y, charFun ν y =
          (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y : ℂ)) ∧
    (RiemannHypothesis ↔
      ∀ (N : ℕ) (t c : Fin N → ℝ),
        0 ≤ evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (specSq (cosComb t c sechHalf)) +
            evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
              (specSq (sinComb t c sechHalf))) :=
  ⟨riemannHypothesis_iff_weilPositiveEvenPolar_vonMangoldt,
    riemannHypothesis_iff_archimedeanNonnegOnPolarNonnegCone,
    riemannHypothesis_iff_primeBlindPositiveEvenAt,
    riemannHypothesis_iff_positiveDefiniteOnReal_cosineShiftFn_sechHalf,
    riemannHypothesis_iff_exists_sechHalf_measure_vonMangoldt,
    riemannHypothesis_iff_forall_cosComb_sinComb_sechHalf_nonneg⟩

end RHTower.CHMDStage4

end
