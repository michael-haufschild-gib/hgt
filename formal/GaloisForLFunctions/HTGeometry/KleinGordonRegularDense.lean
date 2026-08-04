import GaloisForLFunctions.HTGeometry.KleinGordonSmoothingData

/-!
# The regularity hypotheses are not restrictive

Every strong statement of this development asks the Cauchy data to lie in the range of `⟨D⟩⁻¹` or
`⟨D⟩⁻²`. That is a genuine restriction — `⟨D⟩⁻¹` is not surjective — but it is not a small one: the
range is **dense**.

The reason is the one that runs through the whole file: `⟨D⟩⁻¹` is a Fourier multiplier with a real,
nowhere vanishing symbol. Nowhere vanishing makes it injective; real makes it self-adjoint; and an
injective self-adjoint operator on a Hilbert space has dense range, because a vector orthogonal to the
range is annihilated by the operator.

So the strong solutions of statements 68 and 106 are constructed on a dense set of Cauchy data, and
the continuous dependence of statement 111 extends them by continuity as far as any solution concept
allows.
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

section Injective

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] [SecondCountableTopology 𝕜]
variable {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A multiplication operator with a nowhere vanishing symbol is injective.** -/
theorem lpBoundedMulCLM_injective {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hne : ∀ x, φ x ≠ 0) :
    Function.Injective (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC) := by
  intro f g hfg
  have hae : ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f : Lp 𝕜 p μ) : α → 𝕜)
      =ᵐ[μ] ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC g : Lp 𝕜 p μ) : α → 𝕜) := by
    rw [hfg]
  refine Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC g, hae] with x h1 h2 h3
  rw [h1, h2] at h3
  exact mul_left_cancel₀ (hne x) h3

end Injective

end MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Density from injectivity and self-adjointness -/

/-- A continuous linear map on a Hilbert space whose range has trivial orthogonal complement has
dense range. -/
theorem denseRange_of_inner_eq_zero
    {T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    (h : ∀ g : Lp ℂ 2 (volume : Measure E),
      (∀ f : Lp ℂ 2 (volume : Measure E), inner ℂ (T f) g = (0 : ℂ)) → g = 0) :
    DenseRange T := by
  set K : Submodule ℂ (Lp ℂ 2 (volume : Measure E)) :=
    LinearMap.range (T : Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E)) with hK
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    refine h g fun f => ?_
    exact (Submodule.mem_orthogonal K g).mp hg (T f) ⟨f, rfl⟩
  have hclos := Submodule.orthogonal_orthogonal_eq_closure K
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  have hdense : Dense (K : Set (Lp ℂ 2 (volume : Measure E))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos.symm
  have hset : (K : Set (Lp ℂ 2 (volume : Measure E)))
      = Set.range (T : Lp ℂ 2 (volume : Measure E) → Lp ℂ 2 (volume : Measure E)) := by
    ext y
    simp [hK, LinearMap.mem_range, Set.mem_range]
  rw [hset] at hdense
  exact hdense

/-! ## The inverse frequency is injective with dense range -/

theorem fourierL2_injective : Function.Injective (fourierL2 E) :=
  (Lp.fourierTransformₗᵢ E ℂ).injective

theorem fourierL2inv_injective : Function.Injective (fourierL2inv E) :=
  (Lp.fourierTransformₗᵢ E ℂ).symm.injective

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgFreqInv_ne_zero (ξ : E) : kgFreqInv ξ ≠ 0 := by
  rw [kgFreqInv, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
  exact (kgFreq_pos ξ).ne'

/-- **`⟨D⟩⁻¹` is injective.** Its symbol vanishes nowhere. -/
theorem kgFreqInvOp_injective : Function.Injective (kgFreqInvOp (E := E)) := by
  intro f g hfg
  rw [kgFreqInvOp_eq, fourierMulCLM_apply, fourierMulCLM_apply] at hfg
  have h1 := fourierL2inv_injective hfg
  have h2 := lpBoundedMulCLM_injective (p := 2) (μ := (volume : Measure E))
    (measurable_kgFreqInv (E := E)) zero_le_one norm_kgFreqInv_le kgFreqInv_ne_zero h1
  exact fourierL2_injective h2

/-- **`⟨D⟩⁻¹` has dense range.** A vector orthogonal to the range is annihilated by the operator,
because the operator is self-adjoint; and the kernel is trivial. -/
theorem denseRange_kgFreqInvOp : DenseRange (kgFreqInvOp (E := E)) := by
  refine denseRange_of_inner_eq_zero fun g hg => ?_
  have hmove : ∀ f : Lp ℂ 2 (volume : Measure E),
      inner ℂ f (kgFreqInvOp (E := E) g) = (0 : ℂ) := by
    intro f
    rw [← inner_kgFreqInvOp]
    exact hg f
  have hself := hmove (kgFreqInvOp (E := E) g)
  have hzero : kgFreqInvOp (E := E) g = 0 := inner_self_eq_zero.mp hself
  have := kgFreqInvOp_injective (E := E) (a₁ := g) (a₂ := 0)
  refine this ?_
  rw [hzero, map_zero]

/-- **The doubly regular vectors are dense**, so the strong Cauchy data of statement 68 are dense. -/
theorem denseRange_kgFreqInvOp_two :
    DenseRange fun x : Lp ℂ 2 (volume : Measure E) => kgFreqInvOp (kgFreqInvOp x) :=
  denseRange_kgFreqInvOp.comp denseRange_kgFreqInvOp (kgFreqInvOp (E := E)).continuous

end GaloisForLFunctions.HTGeometry
