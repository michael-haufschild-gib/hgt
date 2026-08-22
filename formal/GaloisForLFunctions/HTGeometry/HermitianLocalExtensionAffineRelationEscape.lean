import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionRealRelationEscape
import GaloisForLFunctions.HTGeometry.AffineSpectralRelationOrbitPolynomial

/-!
# One local extension erases every nonzero balanced **affine** real spectral relation

`HermitianLocalExtensionRealRelationEscape` produces a spectrum on which no relabelling of a
homogeneous relation vanishes.  Nondegeneracy of a spectral map rules out relations that are merely
*constant*, so the same statement is needed with an arbitrary prescribed value.  The corpus's
constant-action rigidity `hermitianLocalExtension_constantAction_coefficients_constant` already
carries the target, so only the finite simultaneous escape has to be retargeted.

## Main results

* `exists_all_permutedComplexRelation_ne_target_real` — simultaneous escape from a prescribed value.
* `exists_hermitianLocalExtension_realRootPacket_affineOrbit_ne_zero` — a real root packet of the
  extended system on which every relabelling of the relation misses the target.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Simultaneous escape from a prescribed value.**  If every labeling of the relation somewhere
misses the target on one connected analytic chart, a single point of that chart misses it for all
labelings at once. -/
theorem exists_all_permutedComplexRelation_ne_target_real
    {I P : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : I → ℂ) (branch : I → P → ℂ) (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℝ (branch i) U) (target : ℂ)
    (hlabel : ∀ σ : Equiv.Perm I, ∃ p ∈ U, permutedComplexRelation c branch σ p ≠ target) :
    ∃ p ∈ U, ∀ σ : Equiv.Perm I, permutedComplexRelation c branch σ p ≠ target := by
  obtain ⟨p, hpU, hp⟩ :=
    exists_forall_neZero_of_finite_analyticOnNhd_real_local
      (fun σ q => permutedComplexRelation c branch σ q - target) U hUopen hUconnected hUnonempty
      (fun σ q hq =>
        ((permutedComplexRelation_analyticOnNhd_real c branch U hbranch σ) q hq).sub
          analyticAt_const)
      (fun σ => by
        obtain ⟨q, hqU, hq⟩ := hlabel σ
        exact ⟨q, hqU, sub_ne_zero.mpr hq⟩)
  exact ⟨p, hpU, fun σ => sub_ne_zero.mp (hp σ)⟩

/-- **One local extension erases a nonzero balanced affine real spectral relation.**  The resulting
Hermitian matrix has a simple real characteristic-root packet on which every relabelling of the
relation misses the prescribed value. -/
theorem exists_hermitianLocalExtension_realRootPacket_affineOrbit_ne_zero
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
    (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0) (target : ℝ) :
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
        ∀ σ : Equiv.Perm (α × ρ), ∑ i, c i * extendedEnergy (σ i) ≠ target := by
  classical
  set cC : α × ρ → ℂ := fun i => ((c i : ℝ) : ℂ) with hcC
  set targetC : ℂ := ((target : ℝ) : ℂ) with htargetC
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
        ∃ p ∈ V, permutedComplexRelation cC branchR σ p ≠ targetC := by
    intro σ
    by_contra hnone
    push Not at hnone
    have haction :
        ∀ p ∈ V,
          ∑ i, permutedComplexCoefficient cC σ i *
            C.branch i (realLocalExtensionParameter p) = targetC := by
      intro p hp
      rw [sum_permutedComplexCoefficient_eq_relation]
      exact hnone p hp
    have hconstant :
        ∀ x y, permutedComplexCoefficient cC σ x = permutedComplexCoefficient cC σ y :=
      hermitianLocalExtension_constantAction_coefficients_constant
        energy hmax shift₀ transition hsimple hlift C V hVopen
        (by simpa [center] using hVcenter) hVU
        (permutedComplexCoefficient cC σ) targetC haction
    exact (permutedComplexCoefficient_not_constant hbalancedC hcCne σ) hconstant
  obtain ⟨p, hpV, hpAll⟩ :=
    exists_all_permutedComplexRelation_ne_target_real cC branchR V hVopen hVconnected
      ⟨center, hVcenter⟩ hbranchR targetC hlabel
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
  refine ⟨p, extendedEnergy, hextendedInjective, ?_, ?_⟩
  · intro i
    rw [← hcomplexEnergy i]
    exact hroot i
  · intro σ hzero
    have hcomplexZero : permutedComplexRelation cC branchR σ p = targetC := by
      unfold permutedComplexRelation
      change (∑ i, cC i * complexEnergy (σ i)) = targetC
      simp_rw [hcomplexEnergy, hcC, htargetC]
      exact_mod_cast hzero
    exact hpAll σ hcomplexZero

end

end GaloisForLFunctions.HTGeometry
