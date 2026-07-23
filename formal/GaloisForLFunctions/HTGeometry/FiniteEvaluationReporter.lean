import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.FiniteReporterConditionalInformation

/-!
# Finite evaluation packets as concrete Hilbert reporters

The evaluation-Hilbert and finite-reporter interfaces use the same column vectors but previously
did not identify them.  This module supplies the missing connector.  Literal point sampling is a
linear reporter into a finite Euclidean space, its reporter Gram is exactly the existing finite
evaluation Gram, and an unisolvent evaluation packet therefore gives a faithful, full-rank
reporter with positive sequential information.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module
open GaloisForLFunctions.HTGeometry

/-- Literal evaluation on a finite packet, regarded as a Hilbert-valued linear reporter. -/
def finiteEvaluationReporter
    {α : Type*} {d : ℕ} (points : Fin d → α) :
    (α → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun g := WithLp.toLp 2 fun i => g (points i)
  map_add' g h := by
    apply WithLp.ofLp_injective 2
    funext i
    rfl
  map_smul' a g := by
    apply WithLp.ofLp_injective 2
    funext i
    rfl

@[simp] theorem finiteEvaluationReporter_apply
    {α : Type*} {d : ℕ} (points : Fin d → α) (g : α → ℂ) :
    finiteEvaluationReporter points g =
      WithLp.toLp 2 (fun i => g (points i)) := rfl

/-- Coefficient reporting through point evaluation is the literal packet of sampled linear
combinations. -/
theorem finiteDerivativeReporterMap_finiteEvaluationReporter_apply
    {d : ℕ} (f : ℂ → ℂ) (points : Fin d → ℂ) (c : Fin d → ℂ) :
    finiteDerivativeReporterMap d f (finiteEvaluationReporter points) c =
      WithLp.toLp 2 (fun row =>
        ∑ j, c j * iteratedDeriv (j : ℕ) f (points row)) := by
  apply WithLp.ofLp_injective 2
  funext row
  simp [finiteDerivativeReporterMap_apply, Finset.sum_apply, Pi.smul_apply]

/-- The reporter Gram of a point-sampled derivative packet is exactly its evaluation Gram. -/
theorem finiteDerivativeReporterGram_finiteEvaluationReporter
    {d : ℕ} (f : ℂ → ℂ) (points : Fin d → ℂ) :
    finiteDerivativeReporterGram d f (finiteEvaluationReporter points) =
      finiteEvaluationGram (fun j : Fin d => iteratedDeriv (j : ℕ) f) points := rfl

/-- Any nonsingular `d`-jet reporter needs at least `d` Hilbert output dimensions. -/
theorem finrank_ge_of_finiteDerivativeReporterGram_det_ne_zero
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [FiniteDimensional ℂ Y]
    (d : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (hdet : (finiteDerivativeReporterGram d f report).det ≠ 0) :
    d ≤ finrank ℂ Y := by
  have hli : LinearIndependent ℂ
      (fun i : Fin d => report (iteratedDeriv (i : ℕ) f)) := by
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mp hdet
  simpa using hli.fintype_card_le_finrank

/-- **Unisolvent evaluation reporter.**  A linearly independent initial derivative block admits
pairwise distinct sampling points whose literal evaluation reporter simultaneously supports exact
dual coefficient recovery, a positive-definite reporter Gram, injective coefficient readout, zero
blind kernel, full visible rank, and positive information at every admitted derivative order. -/
theorem exists_injective_finiteEvaluationReporterHilbertReconstruction_of_linearIndependent
    {d : ℕ} (f : ℂ → ℂ)
    (hf : LinearIndependent ℂ (fun j : Fin d => iteratedDeriv (j : ℕ) f)) :
    ∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ (q r : Fin d), ∑ i, dual q i * iteratedDeriv (r : ℕ) f (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (r : ℕ) f (points i)) = a q) ∧
      (finiteDerivativeReporterGram d f
        (finiteEvaluationReporter points)).PosDef ∧
      0 < (finiteDerivativeReporterGram d f
        (finiteEvaluationReporter points)).det ∧
      Function.Injective
        (finiteDerivativeReporterMap d f (finiteEvaluationReporter points)) ∧
      LinearMap.ker
        (finiteDerivativeReporterMap d f (finiteEvaluationReporter points)) = ⊥ ∧
      finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap d f (finiteEvaluationReporter points))) = d ∧
      ∀ k : ℕ, k < d →
        0 < finiteDerivativeReporterConditionalInformation k f
          (finiteEvaluationReporter points) := by
  obtain ⟨points, dual, hinj, hdelta, hrecovery, hgram, _hdet⟩ :=
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (fun j : Fin d => iteratedDeriv (j : ℕ) f) hf
  have hreportGram :
      (finiteDerivativeReporterGram d f
        (finiteEvaluationReporter points)).PosDef := by
    simpa only [finiteDerivativeReporterGram_finiteEvaluationReporter] using hgram
  have hreportDetPos :
      0 < (finiteDerivativeReporterGram d f
        (finiteEvaluationReporter points)).det :=
    hreportGram.det_pos
  have hreportDet :
      (finiteDerivativeReporterGram d f
        (finiteEvaluationReporter points)).det ≠ 0 :=
    hreportDetPos.ne'
  have hreportInjective : Function.Injective
      (finiteDerivativeReporterMap d f (finiteEvaluationReporter points)) :=
    (finiteDerivativeReporterGram_det_ne_zero_iff_injective
      d f (finiteEvaluationReporter points)).mp hreportDet
  have hker : LinearMap.ker
      (finiteDerivativeReporterMap d f (finiteEvaluationReporter points)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hreportInjective
  have hrank : finrank ℂ (LinearMap.range
      (finiteDerivativeReporterMap d f (finiteEvaluationReporter points))) = d := by
    simpa using LinearMap.finrank_range_of_inj hreportInjective
  have hinfo : ∀ k : ℕ, k < d →
      0 < finiteDerivativeReporterConditionalInformation k f
        (finiteEvaluationReporter points) :=
    (finiteDerivativeReporterGram_det_ne_zero_iff_forall_conditionalInformation_pos
      d f (finiteEvaluationReporter points)).mp hreportDet
  exact ⟨points, dual, hinj, hdelta, hrecovery, hreportGram, hreportDetPos,
    hreportInjective, hker, hrank, hinfo⟩

end

end HTGeometry
