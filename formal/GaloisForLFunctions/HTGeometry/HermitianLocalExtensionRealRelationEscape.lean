import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionRelationEscape
import GaloisForLFunctions.HTGeometry.ComplexPermutedSpectralEscape
import GaloisForLFunctions.HTGeometry.LinearSpectralRelationOrbitPolynomial

/-!
# One local extension erases every nonzero balanced **real** spectral relation

`HermitianLocalExtensionRelationEscape` proves this for balanced *integer* characters.  The
real-relation rigidity behind metric recurrence exponents needs the same statement for real
coefficients, and the analytic core it rests on —
`exists_hermitianLocalExtension_action_ne_target` and
`selectedLayerAnalyticRelation_constant_of_preconnected` — is **already stated for arbitrary complex
coefficients**.  Only the wrappers were integer-typed, so this file is the real-coefficient wrapper.

## Main result

* `exists_hermitianLocalExtension_realRootPacket_orbit_ne_zero` — a real root packet of the extended
  system at which *every* relabeling of the relation is nonzero, i.e. the labeling-orbit obstruction
  of the relation does not vanish there.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **One local extension erases a nonzero balanced real spectral relation.**  The resulting
Hermitian matrix has a simple real characteristic-root packet whose labeling-orbit obstruction is
nonzero. -/
theorem exists_hermitianLocalExtension_realRootPacket_orbit_ne_zero
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ)
    (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected)
    (c : α × ρ → ℝ)
    (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0) :
    ∃ p : (ρ → ℝ) × Matrix ρ ρ ℝ,
      ∃ extendedEnergy : α × ρ → ℝ,
        Function.Injective extendedEnergy ∧
        (∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix
                (fun a => (energy a : ℂ))
                (realLocalExtensionParameter p).1
                transition
                (realLocalExtensionParameter p).2,
              (extendedEnergy i : ℂ)) = 0) ∧
        linearRelationOrbitValue c extendedEnergy ≠ 0 := by
  classical
  set cC : α × ρ → ℂ := fun i => ((c i : ℝ) : ℂ) with hcC
  have hbalancedC : ∑ i, cC i = 0 := by
    rw [hcC]
    have : ∑ i, ((c i : ℝ) : ℂ) = ((∑ i, c i : ℝ) : ℂ) := by push_cast; ring
    rw [this, hbalanced]
    simp
  have hcCne : cC ≠ 0 := by
    intro h
    refine hc (funext fun i => ?_)
    have := congrFun h i
    simp only [hcC, Pi.zero_apply] at this
    exact_mod_cast this
  let complexShift₀ : ρ → ℂ := fun r => (shift₀ r : ℂ)
  let center : (ρ → ℝ) × Matrix ρ ρ ℝ := (shift₀, 0)
  let C : LocalExtensionEigenbranchChart
      (fun a => (energy a : ℂ)) complexShift₀ transition :=
    Classical.choice
      (exists_localExtensionEigenbranchChart
        (fun a => (energy a : ℂ)) complexShift₀ transition hsimple)
  have hcenterComplex :
      realLocalExtensionParameter center = (complexShift₀, 0) := by
    simp [center, complexShift₀]
  have hparameterContinuous :
      ContinuousAt
        (realLocalExtensionParameter :
          ((ρ → ℝ) × Matrix ρ ρ ℝ) → (ρ → ℂ) × Matrix ρ ρ ℂ) center :=
    (realLocalExtensionParameter_analyticAt center).continuousAt
  have hpreimageNhd :
      {p | realLocalExtensionParameter p ∈ C.U} ∈ 𝓝 center := by
    apply hparameterContinuous
    rw [hcenterComplex]
    exact C.isOpen_U.mem_nhds C.center_mem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpreimageNhd
  let V : Set ((ρ → ℝ) × Matrix ρ ρ ℝ) := Metric.ball center ε
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hVconnected : IsPreconnected V := Metric.isPreconnected_ball
  have hVcenter : center ∈ V := by simpa [V] using hε
  have hVU : ∀ p ∈ V, realLocalExtensionParameter p ∈ C.U := fun p hp => hball hp
  let branchR : α × ρ → ((ρ → ℝ) × Matrix ρ ρ ℝ) → ℂ :=
    fun i p => C.branch i (realLocalExtensionParameter p)
  have hbranchR : ∀ i, AnalyticOnNhd ℝ (branchR i) V := by
    intro i p hp
    apply ((C.analyticOn_branch i (realLocalExtensionParameter p)
      (hVU p hp)).restrictScalars).comp
    exact realLocalExtensionParameter_analyticAt p
  have hlabel :
      ∀ σ : Equiv.Perm (α × ρ),
        ∃ p ∈ V, permutedComplexRelation cC branchR σ p ≠ 0 := by
    intro σ
    by_contra hnone
    push Not at hnone
    have hfixed :
        ∀ p ∈ V,
          ∑ i, permutedComplexCoefficient cC σ i *
            C.branch i (realLocalExtensionParameter p) = 0 := by
      intro p hp
      rw [sum_permutedComplexCoefficient_eq_relation]
      exact hnone p hp
    have hconstant :
        ∀ x y, permutedComplexCoefficient cC σ x = permutedComplexCoefficient cC σ y :=
      selectedLayerAnalyticRelation_constant_of_preconnected
        energy hmax transition (permutedComplexCoefficient cC σ)
        (fun r s hrs =>
          C.realSelectedLayerWitness energy shift₀ transition hsimple
            V hVopen (by simpa [center] using hVcenter) hVU
            (permutedComplexCoefficient cC σ) hfixed hrs)
        hlift
    exact (permutedComplexCoefficient_not_constant hbalancedC hcCne σ) hconstant
  obtain ⟨p, hpV, hpAll⟩ :=
    exists_all_permutedComplexRelation_ne_zero_real cC branchR V hVopen hVconnected
      ⟨center, hVcenter⟩ hbranchR hlabel
  have hpU : realLocalExtensionParameter p ∈ C.U := hVU p hpV
  let complexEnergy : α × ρ → ℂ := fun i => C.branch i (realLocalExtensionParameter p)
  have hroot :
      ∀ i,
        matrixCharpolyRelation
          (localExtensionMatrix
              (fun a => (energy a : ℂ))
              (realLocalExtensionParameter p).1
              transition
              (realLocalExtensionParameter p).2,
            complexEnergy i) = 0 :=
    C.root (realLocalExtensionParameter p) hpU
  have hmatrixHermitian :
      (localExtensionMatrix
        (fun a => (energy a : ℂ))
        (realLocalExtensionParameter p).1
        transition
        (realLocalExtensionParameter p).2).IsHermitian :=
    localExtensionMatrix_realParameter_isHermitian energy transition htransition p
  have him : ∀ i, (complexEnergy i).im = 0 := fun i =>
    matrixCharpolyRelation_im_eq_zero_of_isHermitian _ hmatrixHermitian _ (hroot i)
  let extendedEnergy : α × ρ → ℝ := fun i => (complexEnergy i).re
  have hcomplexEnergy : ∀ i, complexEnergy i = (extendedEnergy i : ℂ) := by
    intro i
    apply Complex.ext
    · rfl
    · simpa [extendedEnergy] using him i
  have hextendedInjective : Function.Injective extendedEnergy := by
    intro i j hij
    apply (C.simple (realLocalExtensionParameter p) hpU)
    change complexEnergy i = complexEnergy j
    rw [hcomplexEnergy i, hcomplexEnergy j, hij]
  have hrealLabel :
      ∀ σ : Equiv.Perm (α × ρ), ∑ i, c i * extendedEnergy (σ i) ≠ 0 := by
    intro σ hzero
    have hcomplexZero : permutedComplexRelation cC branchR σ p = 0 := by
      unfold permutedComplexRelation
      change (∑ i, cC i * complexEnergy (σ i)) = 0
      simp_rw [hcomplexEnergy, hcC]
      exact_mod_cast hzero
    exact hpAll σ hcomplexZero
  refine ⟨p, extendedEnergy, hextendedInjective, ?_, ?_⟩
  · intro i
    rw [← hcomplexEnergy i]
    exact hroot i
  · exact (linearRelationOrbitValue_ne_zero_iff c extendedEnergy).mpr hrealLabel

end

end GaloisForLFunctions.HTGeometry
