import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaStripUniformBound
import GaloisForLFunctions.HTGeometry.CompactTestTransform
import GaloisForLFunctions.HTGeometry.StripContourShift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The pairing of the strip solution with a test transform does not depend on the height

Multiplying the holomorphic strip solution by the entire Fourier extension of a compactly supported
test function produces a holomorphic function which decays quadratically along every horizontal
line of a closed substrip and is uniformly bounded across it.  Cauchy's theorem for rectangles then
moves the line of integration freely inside `0 < Im z < 1`.
-/

open Set Complex MeasureTheory Filter

open scoped ContDiff

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- The paired integrand: the rescaled test transform times the strip solution. -/
def pairedIntegrand (ψ : ℝ → ℂ) (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) (z : ℂ) : X :=
  testTransformTwoPi ψ z • stripSolution E T c z

/-- Heights between two interior heights are interior. -/
theorem mem_imStrip_of_mem_uIcc {σ σ' : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z.im ∈ uIcc σ σ') : z ∈ imStrip 0 1 := by
  rw [Set.uIcc, Set.mem_Icc] at hz
  constructor
  · exact lt_of_lt_of_le (lt_min hσ.1 hσ'.1) hz.1
  · exact lt_of_le_of_lt hz.2 (max_lt hσ.2 hσ'.2)

omit [Nontrivial X] in
/-- The paired integrand is holomorphic across a closed substrip. -/
theorem differentiableAt_pairedIntegrand {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {E : ℂ → ℂ} (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (T : X →L[ℂ] X) (c : X) {σ σ' : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z.im ∈ uIcc σ σ') :
    DifferentiableAt ℂ (pairedIntegrand ψ E T c) z := by
  have hmem : z ∈ imStrip 0 1 := mem_imStrip_of_mem_uIcc hσ hσ' hz
  have hf : DifferentiableAt ℂ (stripSolution E T c) z :=
    (differentiableOn_stripSolution hEd T c).differentiableAt
      ((isOpen_imStrip 0 1).mem_nhds hmem)
  exact (differentiable_testTransformTwoPi hψc hψs z).smul hf

/-- The paired integrand decays quadratically in the real part, uniformly across the substrip. -/
theorem exists_bound_pairedIntegrand {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z) (c : X) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z.im ∈ uIcc σ σ' →
      ‖pairedIntegrand ψ E T c z‖ ≤ A / (1 + z.re ^ (2 : ℕ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_testTransformTwoPi_decay hψ hψs σ σ'
  obtain ⟨D, hD0, hD⟩ := exists_bound_norm_stripSolution hT hE c
    (σ₀ := σ ⊓ σ') (σ₁ := σ ⊔ σ') (lt_min hσ.1 hσ'.1) inf_le_sup (max_lt hσ.2 hσ'.2)
  refine ⟨C * D, by positivity, fun z hz => ?_⟩
  have hzIcc : z.im ∈ Icc (σ ⊓ σ') (σ ⊔ σ') := hz
  have hre : z.re ^ (2 : ℕ) ≤ ‖z‖ ^ (2 : ℕ) := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    calc z.re ^ (2 : ℕ) = |z.re| ^ (2 : ℕ) := (sq_abs _).symm
      _ ≤ ‖z‖ ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ‖pairedIntegrand ψ E T c z‖
      = ‖testTransformTwoPi ψ z‖ * ‖stripSolution E T c z‖ := by
        rw [pairedIntegrand, norm_smul]
    _ ≤ (C / (1 + ‖z‖ ^ (2 : ℕ))) * D :=
        mul_le_mul (hC z hz) (hD z hzIcc) (norm_nonneg _) (by positivity)
    _ = (C * D) / (1 + ‖z‖ ^ (2 : ℕ)) := by ring
    _ ≤ (C * D) / (1 + z.re ^ (2 : ℕ)) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        linarith

omit [Nontrivial X] in
/-- On a horizontal line the paired integrand is continuous. -/
theorem continuous_pairedIntegrand_line {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {E : ℂ → ℂ} (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (T : X →L[ℂ] X) (c : X) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun x : ℝ => pairedIntegrand ψ E T c ((x : ℂ) + (σ : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hline : ContinuousAt (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I)) x := by fun_prop
  have hmem : ((x : ℂ) + (σ : ℂ) * Complex.I).im ∈ uIcc σ σ := by
    simp
  have hdiff : DifferentiableAt ℂ (pairedIntegrand ψ E T c)
      ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    differentiableAt_pairedIntegrand hψc hψs hEd T c hσ hσ hmem
  have hcomp : ContinuousAt ((pairedIntegrand ψ E T c)
      ∘ (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I))) x :=
    ContinuousAt.comp hdiff.continuousAt hline
  exact hcomp

/-- The paired integrand is integrable on every interior horizontal line. -/
theorem integrable_pairedIntegrand_line {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z) (c : X) {σ : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun x : ℝ => pairedIntegrand ψ E T c ((x : ℂ) + (σ : ℂ) * Complex.I)) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_pairedIntegrand hψ hψs hT hE c hσ hσ
  have hint : Integrable (fun x : ℝ => A / (1 + x ^ (2 : ℕ))) := by
    have := integrable_inv_one_add_sq.const_mul A
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [div_eq_mul_inv]
  refine Integrable.mono' hint
    ((continuous_pairedIntegrand_line hψ.continuous hψs hEd T c hσ).aestronglyMeasurable) ?_
  filter_upwards with x
  have hmem : ((x : ℂ) + (σ : ℂ) * Complex.I).im ∈ uIcc σ σ := by simp
  have hre : ((x : ℂ) + (σ : ℂ) * Complex.I).re = x := by simp
  have := hA _ hmem
  rwa [hre] at this

/-- **The pairing is independent of the height.**  Cauchy's theorem on rectangles moves the line of
integration anywhere inside the strip. -/
theorem pairedIntegrand_line_shift {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ (2 : ℕ) = gammaRatio z) (c : X) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) :
    (∫ x : ℝ, pairedIntegrand ψ E T c ((x : ℂ) + (σ : ℂ) * Complex.I))
      = ∫ x : ℝ, pairedIntegrand ψ E T c ((x : ℂ) + (σ' : ℂ) * Complex.I) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_pairedIntegrand hψ hψs hT hE c hσ hσ'
  refine integral_line_shift
    (fun z hz => differentiableAt_pairedIntegrand hψ.continuous hψs hEd T c hσ hσ' hz)
    (integrable_pairedIntegrand_line hψ hψs hT hEd hE c hσ)
    (integrable_pairedIntegrand_line hψ hψs hT hEd hE c hσ') ?_
  have hbound : ∀ R : ℝ,
      ‖∫ y in σ..σ', pairedIntegrand ψ E T c ((R : ℂ) + (y : ℂ) * Complex.I)‖
        + ‖∫ y in σ..σ', pairedIntegrand ψ E T c (-(R : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 2 * (A / (1 + R ^ (2 : ℕ)) * |σ' - σ|) := by
    intro R
    have hpos : ∀ (w : ℂ) (y : ℝ), y ∈ Set.uIoc σ σ' → w.re ^ (2 : ℕ) = R ^ (2 : ℕ) →
        w.im = y → ‖pairedIntegrand ψ E T c w‖ ≤ A / (1 + R ^ (2 : ℕ)) := by
      intro w y hy hwre hwim
      have hyIcc : y ∈ uIcc σ σ' := Set.Ioc_subset_Icc_self hy
      have := hA w (by rw [hwim]; exact hyIcc)
      rwa [hwre] at this
    have h1 : ‖∫ y in σ..σ', pairedIntegrand ψ E T c ((R : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ A / (1 + R ^ (2 : ℕ)) * |σ' - σ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
      refine hpos _ y hy ?_ ?_ <;> simp
    have h2 : ‖∫ y in σ..σ', pairedIntegrand ψ E T c (-(R : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ A / (1 + R ^ (2 : ℕ)) * |σ' - σ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
      refine hpos _ y hy ?_ ?_ <;> simp
    linarith
  refine squeeze_zero (fun R => by positivity) hbound ?_
  have hquad : Tendsto (fun R : ℝ => 1 + R ^ (2 : ℕ)) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have hdiv : Tendsto (fun R : ℝ => A / (1 + R ^ (2 : ℕ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hquad
  have := (hdiv.mul_const |σ' - σ|).const_mul (2 : ℝ)
  simpa using this

end

end GaloisForLFunctions.RHTower
