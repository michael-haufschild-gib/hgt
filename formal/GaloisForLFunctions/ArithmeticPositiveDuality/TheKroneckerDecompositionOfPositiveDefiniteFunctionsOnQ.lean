import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesAKroneckerNullDilationSpectrum

/-!
# The Kronecker decomposition of positive-definite functions on `ℚ_{>0}`

Every positive-definite `f` on `ℚ_{>0}` splits uniquely as `f = f_arch + f_null`:

* `f_arch(u) = ∫ u^{ix} dν(x)` for a finite measure `ν` on `ℝ`, a continuous function of `log u`;
* `f_null` is positive definite with spectral measure giving the Kronecker line mass zero.

(`kronecker_decomposition`, `kronecker_decomposition_unique`). The measure `ν` is the pull-back of
the spectral measure of `f` along the Kronecker line `x ↦ z_x`, and `f_null` is the restriction of
the spectral measure off the line. The archimedean part is the largest archimedean minorant: if
`g(u) = G(log u)` (`G` continuous) and `f − g` are positive definite, then `f_arch − g` is
positive definite (`archimedean_le_archPart`).

So the dilation side of Weil positivity (archimedean, P24) and the dilation spectra forced by
arithmetic successors (Kronecker-null, P25) are the two components of one canonical splitting.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The archimedean measure of a finite measure on the prime torus: its pull-back along the
Kronecker line. -/
def archMeasure (μ : Measure PrimeTorus) : Measure ℝ := μ.comap archPoint

/-- The Kronecker-null part of a measure on the prime torus. -/
def nullMeasure (μ : Measure PrimeTorus) : Measure PrimeTorus := μ.restrict (range archPoint)ᶜ

instance (μ : Measure PrimeTorus) [IsFiniteMeasure μ] : IsFiniteMeasure (archMeasure μ) :=
  ⟨by rw [archMeasure, measurableEmbedding_archPoint.comap_apply, Set.image_univ];
      exact measure_lt_top _ _⟩

instance (μ : Measure PrimeTorus) [IsFiniteMeasure μ] : IsFiniteMeasure (nullMeasure μ) := by
  unfold nullMeasure; infer_instance

theorem map_archMeasure (μ : Measure PrimeTorus) :
    (archMeasure μ).map archPoint = μ.restrict (range archPoint) :=
  measurableEmbedding_archPoint.map_comap μ

theorem nullMeasure_range (μ : Measure PrimeTorus) : nullMeasure μ (range archPoint) = 0 := by
  rw [nullMeasure, Measure.restrict_apply measurableEmbedding_archPoint.measurableSet_range,
    Set.inter_compl_self, measure_empty]

/-- The integral of a character splits along the Kronecker line. -/
theorem integral_ratChar_split (μ : Measure PrimeTorus) [IsFiniteMeasure μ] (u : posUnits) :
    ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ =
      ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂(archMeasure μ) +
        ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂(nullMeasure μ) := by
  have hm := measurableEmbedding_archPoint.measurableSet_range
  rw [← integral_add_compl hm (integrable_ratChar μ _), nullMeasure]
  congr 1
  rw [← map_archMeasure, measurableEmbedding_archPoint.integral_map]
  exact integral_congr_ae (Eventually.of_forall fun t => ratChar_archPoint u t)

/-- **The Kronecker decomposition.** A positive-definite function on `ℚ_{>0}` is the sum of an
archimedean function `∫ u^{ix} dν(x)` and a positive-definite function whose spectral measure
gives the Kronecker line mass zero. -/
theorem kronecker_decomposition {f : posUnits → ℂ} (hf : IsPosDefOnGroup f) :
    ∃ (ν : Measure ℝ) (σ : Measure PrimeTorus), IsFiniteMeasure ν ∧ IsFiniteMeasure σ ∧
      σ (range archPoint) = 0 ∧ ∀ u : posUnits,
        f u = ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂ν +
          ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂σ := by
  obtain ⟨μ, hμ, hfμ⟩ := exists_measure_ratChar hf
  exact ⟨archMeasure μ, nullMeasure μ, inferInstance, inferInstance, nullMeasure_range μ,
    fun u => by rw [hfμ u, integral_ratChar_split]⟩

/-- **Uniqueness.** The archimedean measure and the Kronecker-null spectral measure of the
decomposition are unique. -/
theorem kronecker_decomposition_unique {ν ν' : Measure ℝ} {σ σ' : Measure PrimeTorus}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsFiniteMeasure σ] [IsFiniteMeasure σ']
    (hσ : σ (range archPoint) = 0) (hσ' : σ' (range archPoint) = 0)
    (h : ∀ u : posUnits, ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂ν +
        ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂σ =
      ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂ν' + ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂σ') :
    ν = ν' ∧ σ = σ' := by
  -- both sides are the integrals of `ν ∘ z⁻¹ + σ`
  have hrep : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (τ : Measure PrimeTorus) [IsFiniteMeasure τ]
      (u : posUnits), ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂ρ +
        ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂τ = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂(ρ.map archPoint + τ) := by
    intro ρ _ τ _ u
    rw [integral_add_measure (integrable_ratChar _ _) (integrable_ratChar _ _),
      integral_map continuous_archPoint.aemeasurable (continuous_ratChar _).aestronglyMeasurable]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => (ratChar_archPoint u t).symm)
  have heq : ν.map archPoint + σ = ν'.map archPoint + σ' :=
    finiteMeasure_ext_of_ratChar fun u => by rw [← hrep, ← hrep, h u]
  have hm := measurableEmbedding_archPoint.measurableSet_range
  -- restrict to the line and off it
  have hline : ∀ (ρ : Measure ℝ) (τ : Measure PrimeTorus), τ (range archPoint) = 0 →
      (ρ.map archPoint + τ).restrict (range archPoint) = ρ.map archPoint := by
    intro ρ τ hτ
    rw [Measure.restrict_add, Measure.restrict_eq_zero.mpr hτ, add_zero]
    exact Measure.restrict_eq_self_of_ae_mem (ae_map_mem_range archPoint hm ρ)
  have hoff : ∀ (ρ : Measure ℝ) (τ : Measure PrimeTorus), τ (range archPoint) = 0 →
      (ρ.map archPoint + τ).restrict (range archPoint)ᶜ = τ := by
    intro ρ τ hτ
    rw [Measure.restrict_add]
    have h1 : (ρ.map archPoint).restrict (range archPoint)ᶜ = 0 := by
      rw [Measure.restrict_eq_zero, Measure.map_apply continuous_archPoint.measurable hm.compl]
      simp
    rw [h1, zero_add]
    exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp hτ)
  have hν : ν.map archPoint = ν'.map archPoint := by
    rw [← hline ν σ hσ, ← hline ν' σ' hσ', heq]
  refine ⟨?_, by rw [← hoff ν σ hσ, ← hoff ν' σ' hσ', heq]⟩
  have := congrArg (fun m : Measure PrimeTorus => m.comap archPoint) hν
  simpa [measurableEmbedding_archPoint.comap_map] using this

theorem archMeasure_add (μ μ' : Measure PrimeTorus) :
    archMeasure (μ + μ') = archMeasure μ + archMeasure μ' := by
  ext s hs
  simp only [archMeasure, Measure.add_apply,
    measurableEmbedding_archPoint.comap_apply]

theorem archMeasure_map (ρ : Measure ℝ) : archMeasure (ρ.map archPoint) = ρ :=
  measurableEmbedding_archPoint.comap_map ρ

/-- **The archimedean part is the largest archimedean minorant.** If `g(u) = G(log u)` with `G`
continuous, and `g` and `f − g` are positive definite, then `f_arch − g = ∫ u^{ix} dρ(x)` for a
finite positive measure `ρ`: the archimedean part of `f` dominates `g`. -/
theorem archimedean_le_archPart {f g : posUnits → ℂ} (hg : IsPosDefOnGroup g)
    {G : ℝ → ℂ} (hG : Continuous G) (hgG : ∀ u : posUnits, g u = G (Real.log ((u : ℚˣ) : ℚ)))
    (hfg : IsPosDefOnGroup fun u => f u - g u) {μ : Measure PrimeTorus} [IsFiniteMeasure μ]
    (hμ : ∀ u : posUnits, f u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ) :
    ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ ∀ u : posUnits,
      ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂(archMeasure μ) - g u =
        ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂ρ := by
  obtain ⟨μg, hμg, hgμ⟩ := exists_measure_ratChar hg
  obtain ⟨μh, hμh, hhμ⟩ := exists_measure_ratChar hfg
  obtain ⟨νg, hνg, hμgν⟩ := spectralMeasure_eq_map_archPoint hg hG hgG hgμ
  have hsum : μ = μg + μh := finiteMeasure_ext_of_ratChar fun u => by
    rw [integral_add_measure (integrable_ratChar _ _) (integrable_ratChar _ _), ← hμ u, ← hgμ u,
      ← hhμ u]
    ring
  have hg' : ∀ u : posUnits, g u = ∫ t, cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) ∂νg := by
    intro u
    rw [hgμ u, hμgν, integral_map continuous_archPoint.aemeasurable
      (continuous_ratChar _).aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun t => ratChar_archPoint u t)
  have hint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (u : posUnits),
      Integrable (fun t : ℝ => cexp (Real.log ((u : ℚˣ) : ℚ) * t * I)) ρ := by
    intro ρ _ u
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    rw [show (Real.log ((u : ℚˣ) : ℚ) : ℂ) * t * I = ((Real.log ((u : ℚˣ) : ℚ) * t : ℝ) : ℂ) * I
      by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  refine ⟨archMeasure μh, inferInstance, fun u => ?_⟩
  rw [hsum, archMeasure_add, hμgν, archMeasure_map, integral_add_measure (hint _ u) (hint _ u),
    hg' u]
  ring

end GaloisForLFunctions.ArithmeticPositiveDuality
