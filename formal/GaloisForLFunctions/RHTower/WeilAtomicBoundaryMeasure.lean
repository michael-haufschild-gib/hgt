import GaloisForLFunctions.RHTower.WeilAtomicExplicitFormula
import GaloisForLFunctions.RHTower.WeilFullConeBoundaryMeasure
import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare

/-!
# The boundary measure of an atomic Weil function

If the Weil function of a full-cone Weil-positive `lam` is, on `Re s > 1`, the positive atomic
Herglotz series `Σ_i c_i (1/(s − ½ − iτ_i) + 1/(s − ½ + iτ_i))`, then its boundary measure is the
atomic measure

`μ_lam = Σ_i c_i (δ_{τ_i} + δ_{−τ_i})`  (`boundaryMeasure_eq_atomicMeasure`).

**Proof.**  For a test `f`, the explicit formula applied to the translates of `f ⋆ f̃`
(`hasSum_spectralKernel_atomic`) shows that `|f̂|² Σ_i c_i (δ_{τ_i} + δ_{−τ_i})` has the spectral
kernel of `f` as characteristic function, so it is the Bochner measure of `f`, which is
`|f̂|² μ_lam` (`WeilSpectral.eq_withDensity_boundaryMeasure`).  On the shells where the mollifier
transforms are bounded below the densities can be divided out (`eq_of_forall_withDensity_mollC`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open Zeta23 Zeta23.WeilEF

noncomputable section

namespace RHTower.WeilAtomic

open WeilSpectral WeilLineIntegral

/-! ## Measures determined by their mollified versions -/

/-- Two measures with the same `|ρ̂_j|²`-weighted versions for every mollifier coincide. -/
theorem eq_of_forall_withDensity_mollC {μ₁ μ₂ : Measure ℝ}
    (h : ∀ j : ℕ, μ₁.withDensity (fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) =
      μ₂.withDensity (fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞))) : μ₁ = μ₂ := by
  have hpiece : ∀ (μ : Measure ℝ) (j : ℕ), μ.restrict (shell j) =
      ((μ.withDensity fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)).restrict
        (shell j)).withDensity fun r => (invDensity j r : ℝ≥0∞) := by
    intro μ j
    have hmχ := measurable_specDensity (WeilHerglotz.integrable_mollC j)
    have hmi := measurable_invDensity j
    have hone : (fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) *
        (fun r => (invDensity j r : ℝ≥0∞)) =ᵐ[μ.restrict (shell j)] 1 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_shell j)]
      refine Eventually.of_forall fun r hr => ?_
      have hpos := specDensity_mollC_pos j hr
      simp only [Pi.mul_apply, Pi.one_apply, invDensity]
      rw [← ENNReal.coe_mul, mul_inv_cancel₀ hpos.ne', ENNReal.coe_one]
    rw [restrict_withDensity (measurableSet_shell j), ← withDensity_mul _ hmχ.coe_nnreal_ennreal
      hmi.coe_nnreal_ennreal, withDensity_congr_ae hone, withDensity_one]
  rw [← Measure.restrict_univ (μ := μ₁), ← Measure.restrict_univ (μ := μ₂), ← iUnion_shell,
    Measure.restrict_iUnion shell_pairwise_disjoint measurableSet_shell,
    Measure.restrict_iUnion shell_pairwise_disjoint measurableSet_shell]
  congr 1
  funext j
  rw [hpiece μ₁ j, hpiece μ₂ j, h j]

/-! ## The explicit formula on translated autocorrelations -/

theorem contDiff_transl {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (y : ℝ) : ContDiff ℝ 2 (transl y k) :=
  hk.comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_transl {k : ℝ → ℂ} (hkc : HasCompactSupport k) (y : ℝ) :
    HasCompactSupport (transl y k) :=
  hkc.comp_homeomorph (Homeomorph.subRight y)

/-- Translating multiplies the transform by `e^{(s − ½) y}`, bounded on the strip. -/
theorem norm_Hfn_transl_weilTest_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (y : ℝ) : ∃ D : ℝ, ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖Hfn (transl y (EF.weilTest f f)) (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2 := by
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le hf hfc
  refine ⟨Real.exp (3 / 2 * |y|) * D, fun σ t h1 h2 => ?_⟩
  have hfac : Hfn (transl y (EF.weilTest f f)) (σ + t * I) =
      cexp (((σ : ℂ) + t * I - 1 / 2) * y) * Hfn (EF.weilTest f f) (σ + t * I) := by
    unfold Hfn
    rw [paperFT_transl]
    congr 2
    field_simp
  rw [hfac, norm_mul, Complex.norm_exp, mul_div_assoc]
  refine mul_le_mul ?_ (hD σ t h1 h2) (norm_nonneg _) (Real.exp_pos _).le
  rw [Real.exp_le_exp]
  have hre : (((σ : ℂ) + t * I - 1 / 2) * y).re = (σ - 1 / 2) * y := by simp
  rw [hre]
  calc (σ - 1 / 2) * y ≤ |σ - 1 / 2| * |y| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ 3 / 2 * |y| := by
        gcongr
        rw [abs_le]
        constructor <;> linarith

/-- **The explicit formula for the spectral kernel of an atomic Weil function.** -/
theorem hasSum_spectralKernel_atomic {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {ι : Type*} [Countable ι] {c τ : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hΦ : ∀ s : ℂ, 1 < s.re →
      HasSum (fun i => (c i : ℂ) * gPair (1 / 2 + τ i * I) s) (WeilHerglotz.weilFunction lam s))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (y : ℝ) :
    HasSum (fun i => (c i : ℂ) *
        (cexp (y * τ i * I) * ((‖paperFT f (τ i)‖ ^ 2 : ℝ) : ℂ) +
          cexp (y * (-τ i) * I) * ((‖paperFT f (-τ i)‖ ^ 2 : ℝ) : ℂ)))
      (spectralKernel lam f y) := by
  obtain ⟨D, hD⟩ := norm_Hfn_transl_weilTest_le hf hfc y
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have h := hasSum_weilFullFunctional_atomic hsl hc hΦ (contDiff_transl hkd y)
    (hasCompactSupport_transl hkc y) hD
  refine h.congr_fun fun i => ?_
  have hneg := paperFT_weilTest_self_ofReal hf.continuous hfc (-τ i)
  rw [Complex.ofReal_neg] at hneg
  rw [paperFT_transl, paperFT_transl, paperFT_weilTest_self_ofReal hf.continuous hfc, hneg]
  congr 2
  · congr 1; ring
  · congr 1; ring

/-! ## The atomic measure -/

/-- The atomic measure `Σ_i c_i (δ_{τ_i} + δ_{−τ_i})`. -/
def atomicMeasure {ι : Type*} (c τ : ι → ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (c i) • (Measure.dirac (τ i) + Measure.dirac (-τ i))

theorem lintegral_atomicMeasure {ι : Type*} (c τ : ι → ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂atomicMeasure c τ = ∑' i, ENNReal.ofReal (c i) * (g (τ i) + g (-τ i)) := by
  rw [atomicMeasure, lintegral_sum_measure]
  refine tsum_congr fun i => ?_
  rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac, smul_eq_mul]

theorem coe_specDensity (f : ℝ → ℂ) (r : ℝ) :
    ((specDensity f r : ℝ≥0) : ℝ) = ‖paperFT f r‖ ^ 2 := by
  simp [specDensity]

/-- One atom of the weighted atomic measure. -/
theorem integral_atom {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) {d : ℝ → ℝ≥0} (hd : Measurable d)
    (e : ℝ → ℂ) :
    ∫ x, e x ∂((ENNReal.ofReal c • (Measure.dirac a + Measure.dirac b)).withDensity
        fun x => (d x : ℝ≥0∞)) = (c : ℂ) * (((d a : ℝ) : ℂ) * e a + ((d b : ℝ) : ℂ) * e b) := by
  rw [integral_withDensity_eq_integral_smul hd, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal hc]
  simp only [NNReal.smul_def, Complex.real_smul]

/-- **The boundary measure of an atomic Weil function is the atomic measure.** -/
theorem boundaryMeasure_eq_atomicMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ι : Type*} [Countable ι] {c τ : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hΦ : ∀ s : ℂ, 1 < s.re →
      HasSum (fun i => (c i : ℂ) * gPair (1 / 2 + τ i * I) s) (WeilHerglotz.weilFunction lam s)) :
    boundaryMeasure hW = atomicMeasure c τ := by
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
    fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  refine eq_of_forall_withDensity_mollC fun j => ?_
  set f := WeilHerglotz.mollC j with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_mollC j
  have hfc : HasCompactSupport f := WeilHerglotz.hasCompactSupport_mollC j
  have hmd : Measurable (specDensity f) :=
    measurable_specDensity (hf.continuous.integrable_of_hasCompactSupport hfc)
  set ν : Measure ℝ := (atomicMeasure c τ).withDensity fun r => (specDensity f r : ℝ≥0∞) with hν
  -- the atomic Bochner measure is finite
  have hreal := Complex.hasSum_re (weilFullFunctional_weilTest_eq_atomic hsl hc hΦ hf hfc)
  simp only [Complex.ofReal_re] at hreal
  have hnn : ∀ i, 0 ≤ c i * (‖paperFT f (τ i)‖ ^ 2 + ‖paperFT f (-τ i)‖ ^ 2) :=
    fun i => mul_nonneg (hc i) (by positivity)
  have hatom : ∀ i, ENNReal.ofReal (c i) * ((specDensity f (τ i) : ℝ≥0∞) +
      (specDensity f (-τ i) : ℝ≥0∞)) =
      ENNReal.ofReal (c i * (‖paperFT f (τ i)‖ ^ 2 + ‖paperFT f (-τ i)‖ ^ 2)) := by
    intro i
    rw [ENNReal.ofReal_mul (hc i), ENNReal.ofReal_add (by positivity) (by positivity),
      show (-(τ i : ℂ)) = ((-τ i : ℝ) : ℂ) by push_cast; ring,
      ← coe_specDensity, ← coe_specDensity, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_atomicMeasure]
    simp_rw [hatom]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hreal.summable]
    exact ENNReal.ofReal_lt_top
  -- its characteristic function is the spectral kernel
  have hchar : ∀ y, charFun ν y = spectralKernel lam f y := by
    intro y
    have hint : Integrable (fun x : ℝ => cexp (y * x * I)) ν :=
      Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
        rw [show (y : ℂ) * x * I = ((y * x : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I])
    rw [charFun_apply_real]
    have hsplit : ν = Measure.sum fun i => (ENNReal.ofReal (c i) •
        (Measure.dirac (τ i) + Measure.dirac (-τ i))).withDensity
          fun r => (specDensity f r : ℝ≥0∞) := by
      rw [hν, atomicMeasure, withDensity_sum]
    rw [hsplit] at hint ⊢
    rw [integral_sum_measure hint]
    rw [← (hasSum_spectralKernel_atomic hsl hc hΦ hf hfc y).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [integral_atom (hc i) _ _ hmd, coe_specDensity, coe_specDensity]
    push_cast
    ring_nf
  exact (eq_withDensity_boundaryMeasure hW hf hfc hchar).symm

end RHTower.WeilAtomic
