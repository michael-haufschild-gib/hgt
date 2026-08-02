import GaloisForLFunctions.HTGeometry.CrossLayerLiftParityRigidity
import GaloisForLFunctions.HTGeometry.LocalExtensionSliceProjectiveGenericity

/-!
# Parity-complete physical local rank extension

The relation-erasure engine previously accepted either a spare local label
or an externally supplied proof that the interaction lift is connected.
Connected nonbipartite transition support now supplies that proof uniformly
for every finite attached factor of dimension at least two.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set Topology MeasureTheory

/-- **Dimension-uniform physical rank extension.** A connected,
nonbipartite Hermitian transition channel extends every maximally
projective finite real spectrum across every finite local factor with at
least two labels.  One physical Hermitian extension erases all nontrace
balanced integer spectral relations simultaneously. -/
theorem
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket_of_goodSupport
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
    (hcard : 2 ≤ Fintype.card ρ)
    (hconnected :
      (transitionSupportGraph transition).Preconnected)
    (hnonbipartite :
      ¬ (transitionSupportGraph transition).IsBipartite) :
    ∃ p : (ρ → ℝ) × Matrix ρ ρ ℝ,
      ∃ extendedEnergy : α × ρ → ℝ,
        MaximallyProjectiveEnergy extendedEnergy ∧
        Function.Injective extendedEnergy ∧
        ∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix
                (fun a => (energy a : ℂ))
                (realLocalExtensionParameter p).1
                transition
                (realLocalExtensionParameter p).2,
              (extendedEnergy i : ℂ)) = 0 := by
  exact
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket
      energy hmax shift₀ transition htransition hsimple
      (crossLayerLiftGraph_preconnected_of_two_le_card
        (transitionSupportGraph transition)
        hcard hconnected hnonbipartite)

/-- For one fixed connected nonbipartite Hermitian attachment channel,
maximal projective rank is dense, residual, and full measure in its entire
real onsite-plus-edge extension slice. -/
theorem
    hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_goodSupport
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
    (hcard : 2 ≤ Fintype.card ρ)
    (hconnected :
      (transitionSupportGraph transition).Preconnected)
    (hnonbipartite :
      ¬ (transitionSupportGraph transition).IsBipartite) :
    ∃ p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ,
      MaximallyProjectiveEnergy
          (hermitianLocalExtensionSliceMatrix_isHermitian
            (α := α) (ρ := ρ)
            energy transition htransition p₀).eigenvalues ∧
        Dense
          (hermitianLocalExtensionSliceMaximalSet
            (α := α) (ρ := ρ)
            energy transition htransition) ∧
        hermitianLocalExtensionSliceMaximalSet
            (α := α) (ρ := ρ)
            energy transition htransition ∈
          residual
            (Fin (localExtensionSliceParameterCount ρ) → ℝ) ∧
        volume
          (hermitianLocalExtensionSliceMaximalSet
            (α := α) (ρ := ρ)
            energy transition htransition)ᶜ = 0 := by
  obtain ⟨p, extendedEnergy,
      hextendedMax, _hextendedInjective, hroot⟩ :=
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket_of_goodSupport
      energy hmax shift₀ transition htransition hsimple
      hcard hconnected hnonbipartite
  let p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ :=
    localExtensionSliceCoordinates p
  have hrootSlice :
      ∀ i,
        matrixCharpolyRelation
          (hermitianLocalExtensionSliceMatrix
              energy transition p₀,
            (extendedEnergy i : ℂ)) = 0 := by
    intro i
    simpa [hermitianLocalExtensionSliceMatrix, p₀] using hroot i
  have hsliceMax :
      MaximallyProjectiveEnergy
        (hermitianLocalExtensionSliceMatrix_isHermitian
          energy transition htransition p₀).eigenvalues :=
    maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket
      (hermitianLocalExtensionSliceMatrix
        energy transition p₀)
      (hermitianLocalExtensionSliceMatrix_isHermitian
        energy transition htransition p₀)
      extendedEnergy hextendedMax hrootSlice
  have hbase :
      (hermitianLocalExtensionSliceBase (α := α) (ρ := ρ)
        energy transition).IsHermitian :=
    hermitianLocalExtensionSliceBase_isHermitian
      (α := α) (ρ := ρ)
      energy transition htransition
  have hgenerator :
      ∀ i,
        (hermitianLocalExtensionSliceGenerator (α := α) (ρ := ρ)
          energy transition i).IsHermitian :=
    hermitianLocalExtensionSliceGenerator_isHermitian
      (α := α) (ρ := ρ)
      energy transition htransition
  let haffine :=
    realAffineMatrix_isHermitian
      (hermitianLocalExtensionSliceBase energy transition)
      (hermitianLocalExtensionSliceGenerator
        energy transition)
      hbase hgenerator p₀
  have hsliceAffine :
      hermitianLocalExtensionSliceMatrix
          energy transition p₀ =
        realAffineMatrix
          (hermitianLocalExtensionSliceBase
            energy transition)
          (hermitianLocalExtensionSliceGenerator
            energy transition)
          p₀ :=
    hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix
      energy transition p₀
  have heigenAffine :
      (hermitianLocalExtensionSliceMatrix_isHermitian
        energy transition htransition p₀).eigenvalues =
          haffine.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (hermitianLocalExtensionSliceMatrix_isHermitian
          energy transition htransition p₀)
        haffine).2
    exact congrArg Matrix.charpoly hsliceAffine
  have haffineMax :
      MaximallyProjectiveEnergy haffine.eigenvalues := by
    rw [← heigenAffine]
    exact hsliceMax
  have hgeneric :=
    realAffineHermitianMaximalSet_dense_residual_fullMeasure
      (hermitianLocalExtensionSliceBase energy transition)
      (hermitianLocalExtensionSliceGenerator
        energy transition)
      hbase hgenerator p₀ haffineMax
  refine ⟨p₀, hsliceMax, ?_⟩
  rw [hermitianLocalExtensionSliceMaximalSet_eq_realAffine
    energy transition htransition]
  exact hgeneric

/-- A finite Hermitian observable family with connected, nonbipartite
combined support admits one real linear combination and one physical
nearest-factor coupling whose spectrum has maximal projective rank, for
every attached local dimension at least two. -/
theorem
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket_of_goodFamily
    {α ρ η : Type*} [Fintype α] [Fintype ρ] [Fintype η]
    [DecidableEq α] [DecidableEq ρ] [DecidableEq η]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hcard : 2 ≤ Fintype.card ρ)
    (hconnected :
      (transitionFamilySupportGraph transition).Preconnected)
    (hnonbipartite :
      ¬ (transitionFamilySupportGraph transition).IsBipartite) :
    ∃ observableCoefficient : η → ℝ,
      ∃ p : (ρ → ℝ) × Matrix ρ ρ ℝ,
        ∃ extendedEnergy : α × ρ → ℝ,
          MaximallyProjectiveEnergy extendedEnergy ∧
          Function.Injective extendedEnergy ∧
          ∀ i,
            matrixCharpolyRelation
              (localExtensionMatrix
                  (fun a => (energy a : ℂ))
                  (realLocalExtensionParameter p).1
                  (realMatrixFamilyCombination
                    transition observableCoefficient)
                  (realLocalExtensionParameter p).2,
                (extendedEnergy i : ℂ)) = 0 := by
  exact
    exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket_of_family
      energy hmax shift₀ transition htransition hsimple
      (crossLayerLiftGraph_preconnected_of_two_le_card
        (transitionFamilySupportGraph transition)
        hcard hconnected hnonbipartite)

/-- **Parity-complete full-slice genericity.** Under connected,
nonbipartite observable support, maximal projective spectral rank is
realized and is dense, residual, and full measure in the entire physical
onsite-plus-edge extension slice, uniformly for every finite local
dimension at least two. -/
theorem
    hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_goodFamily
    {α ρ η : Type*} [Fintype α] [Fintype ρ] [Fintype η]
    [DecidableEq α] [DecidableEq ρ] [DecidableEq η]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy
          (fun a => (energy a : ℂ))
          (fun r => (shift₀ r : ℂ))))
    (hcard : 2 ≤ Fintype.card ρ)
    (hconnected :
      (transitionFamilySupportGraph transition).Preconnected)
    (hnonbipartite :
      ¬ (transitionFamilySupportGraph transition).IsBipartite) :
    ∃ observableCoefficient : η → ℝ,
      let combinedTransition :=
        realMatrixFamilyCombination
          transition observableCoefficient
      let hcombined :
          combinedTransition.IsHermitian :=
        realMatrixFamilyCombination_isHermitian
          transition htransition observableCoefficient
      ∃ p₀ : Fin (localExtensionSliceParameterCount ρ) → ℝ,
        MaximallyProjectiveEnergy
            (hermitianLocalExtensionSliceMatrix_isHermitian
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined p₀).eigenvalues ∧
          Dense
            (hermitianLocalExtensionSliceMaximalSet
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined) ∧
          hermitianLocalExtensionSliceMaximalSet
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined ∈
            residual
              (Fin (localExtensionSliceParameterCount ρ) → ℝ) ∧
          volume
            (hermitianLocalExtensionSliceMaximalSet
              (α := α) (ρ := ρ)
              energy combinedTransition hcombined)ᶜ = 0 := by
  exact
    hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_family
      energy hmax shift₀ transition htransition hsimple
      (crossLayerLiftGraph_preconnected_of_two_le_card
        (transitionFamilySupportGraph transition)
        hcard hconnected hnonbipartite)

end

end GaloisForLFunctions.HTGeometry
