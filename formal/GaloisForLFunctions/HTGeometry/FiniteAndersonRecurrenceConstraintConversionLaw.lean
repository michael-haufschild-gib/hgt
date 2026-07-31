import GaloisForLFunctions.HTGeometry.FiniteAndersonProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import GaloisForLFunctions.HTGeometry.UniversalInteractionRecurrenceConversionLaw
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Local Anderson conversion of recurrence constraints into time

For every fixed finite Hermitian hopping graph, every reference onsite
potential, and every positive onsite-control budget, a nearby real onsite
potential has maximal projective spectral rank. The local perturbation
therefore converts the complete reference recurrence-relation rank into
temporal dimension, erases every post-perturbation balanced relation, and
attains every positive full-support replica collision floor.

This is a local-Hamiltonian realization of the universal constraint
conversion law. Hopping amplitudes and graph are held fixed; only diagonal
onsite controls change.
-/

open Set Topology MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Changing only the onsite potential changes the finite Anderson
Hamiltonian by exactly the sup distance of the controls in operator norm. -/
theorem norm_finiteAndersonHamiltonian_sub_eq_onsiteDist
    {d : ℕ}
    (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (onsite₀ onsite₁ : Fin (d + 1) → ℝ) :
    ‖finiteAndersonHamiltonian T onsite₁ -
        finiteAndersonHamiltonian T onsite₀‖ =
      dist onsite₁ onsite₀ := by
  rw [dist_eq_norm]
  simp only [finiteAndersonHamiltonian, add_sub_add_left_eq_sub,
    Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  change ‖fun i => (onsite₁ i : ℂ) - (onsite₀ i : ℂ)‖ =
    ‖fun i => onsite₁ i - onsite₀ i‖
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [show ‖(onsite₁ i : ℂ) - (onsite₀ i : ℂ)‖ =
        ‖onsite₁ i - onsite₀ i‖ by
      calc
        ‖(onsite₁ i : ℂ) - (onsite₀ i : ℂ)‖ =
            ‖((onsite₁ i - onsite₀ i : ℝ) : ℂ)‖ := by
              congr 1
              norm_cast
        _ = ‖onsite₁ i - onsite₀ i‖ := Complex.norm_real _]
    exact norm_le_pi_norm (fun i => onsite₁ i - onsite₀ i) i
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [show ‖onsite₁ i - onsite₀ i‖ =
        ‖(onsite₁ i : ℂ) - (onsite₀ i : ℂ)‖ by
      symm
      calc
        ‖(onsite₁ i : ℂ) - (onsite₀ i : ℂ)‖ =
            ‖((onsite₁ i - onsite₀ i : ℝ) : ℂ)‖ := by
              congr 1
              norm_cast
        _ = ‖onsite₁ i - onsite₀ i‖ := Complex.norm_real _]
    exact norm_le_pi_norm
      (fun i => (onsite₁ i : ℂ) - (onsite₀ i : ℂ)) i

/-- Fixed-time operator-norm stability for arbitrary onsite controls of
one fixed finite hopping Hamiltonian. -/
theorem finiteAnderson_heisenbergEvolution_norm_sub_le_onsiteDist
    {d : ℕ}
    (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hT : T.IsHermitian)
    (onsite₀ onsite₁ : Fin (d + 1) → ℝ)
    (O : EuclideanSpace ℂ (Fin (d + 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (d + 1)))
    (t : ℝ) :
    ‖NormedSpace.exp (t • ((-Complex.I) •
          (Matrix.toEuclideanCLM
            (n := Fin (d + 1)) (𝕜 := ℂ))
            (finiteAndersonHamiltonian T onsite₁))) * O *
          star (NormedSpace.exp (t • ((-Complex.I) •
            (Matrix.toEuclideanCLM
              (n := Fin (d + 1)) (𝕜 := ℂ))
              (finiteAndersonHamiltonian T onsite₁)))) -
        NormedSpace.exp (t • ((-Complex.I) •
          (Matrix.toEuclideanCLM
            (n := Fin (d + 1)) (𝕜 := ℂ))
            (finiteAndersonHamiltonian T onsite₀))) * O *
          star (NormedSpace.exp (t • ((-Complex.I) •
            (Matrix.toEuclideanCLM
              (n := Fin (d + 1)) (𝕜 := ℂ))
              (finiteAndersonHamiltonian T onsite₀))))‖
      ≤ 2 * |t| * dist onsite₁ onsite₀ * ‖O‖ := by
  have hH₁ : IsSelfAdjoint
      ((Matrix.toEuclideanCLM
        (n := Fin (d + 1)) (𝕜 := ℂ))
        (finiteAndersonHamiltonian T onsite₁)) := by
    change star
        ((Matrix.toEuclideanCLM
          (n := Fin (d + 1)) (𝕜 := ℂ))
          (finiteAndersonHamiltonian T onsite₁)) =
      (Matrix.toEuclideanCLM
        (n := Fin (d + 1)) (𝕜 := ℂ))
        (finiteAndersonHamiltonian T onsite₁)
    rw [← map_star]
    congr 1
    exact finiteAndersonHamiltonian_isHermitian T hT onsite₁
  have hH₀ : IsSelfAdjoint
      ((Matrix.toEuclideanCLM
        (n := Fin (d + 1)) (𝕜 := ℂ))
        (finiteAndersonHamiltonian T onsite₀)) := by
    change star
        ((Matrix.toEuclideanCLM
          (n := Fin (d + 1)) (𝕜 := ℂ))
          (finiteAndersonHamiltonian T onsite₀)) =
      (Matrix.toEuclideanCLM
        (n := Fin (d + 1)) (𝕜 := ℂ))
        (finiteAndersonHamiltonian T onsite₀)
    rw [← map_star]
    congr 1
    exact finiteAndersonHamiltonian_isHermitian T hT onsite₀
  have hdist :
      ‖(Matrix.toEuclideanCLM
            (n := Fin (d + 1)) (𝕜 := ℂ))
            (finiteAndersonHamiltonian T onsite₁) -
          (Matrix.toEuclideanCLM
            (n := Fin (d + 1)) (𝕜 := ℂ))
            (finiteAndersonHamiltonian T onsite₀)‖ =
        dist onsite₁ onsite₀ := by
    rw [← map_sub, Matrix.l2_opNorm_toEuclideanCLM]
    exact norm_finiteAndersonHamiltonian_sub_eq_onsiteDist
      T onsite₀ onsite₁
  have hbound :=
    selfAdjoint_heisenbergEvolution_norm_sub_le
      ((Matrix.toEuclideanCLM
        (n := Fin (d + 1)) (𝕜 := ℂ))
        (finiteAndersonHamiltonian T onsite₁))
      ((Matrix.toEuclideanCLM
        (n := Fin (d + 1)) (𝕜 := ℂ))
        (finiteAndersonHamiltonian T onsite₀))
      O hH₁ hH₀ t
  rw [hdist] at hbound
  exact hbound

/-- **Local Anderson recurrence-constraint conversion.** Around every
onsite potential of every fixed finite Hermitian hopping Hamiltonian lies a
potential that converts the complete initial recurrence-relation rank into
temporal dimension. Such converting potentials are in fact dense, residual,
and full measure by the imported genericity theorem. -/
theorem exists_finiteAnderson_onsite_fullConstraintConversion
    {d : ℕ}
    (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hT : T.IsHermitian)
    (onsite₀ : Fin (d + 1) → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ onsite₁ : Fin (d + 1) → ℝ,
      dist onsite₁ onsite₀ < ε ∧
      MaximallyProjectiveEnergy
        (finiteAndersonHamiltonian_isHermitian
          T hT onsite₁).eigenvalues ∧
      phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues) -
          phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₀).eigenvalues) =
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (finiteAndersonHamiltonian_isHermitian
              T hT onsite₀).eigenvalues) ∧
      Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (finiteAndersonHamiltonian_isHermitian
              T hT onsite₁).eigenvalues) = 0 ∧
      (∀ (O : EuclideanSpace ℂ (Fin (d + 1)) →L[ℂ]
            EuclideanSpace ℂ (Fin (d + 1)))
          (t : ℝ),
        ‖NormedSpace.exp (t • ((-Complex.I) •
              (Matrix.toEuclideanCLM
                (n := Fin (d + 1)) (𝕜 := ℂ))
                (finiteAndersonHamiltonian T onsite₁))) * O *
              star (NormedSpace.exp (t • ((-Complex.I) •
                (Matrix.toEuclideanCLM
                  (n := Fin (d + 1)) (𝕜 := ℂ))
                  (finiteAndersonHamiltonian T onsite₁)))) -
            NormedSpace.exp (t • ((-Complex.I) •
              (Matrix.toEuclideanCLM
                (n := Fin (d + 1)) (𝕜 := ℂ))
                (finiteAndersonHamiltonian T onsite₀))) * O *
              star (NormedSpace.exp (t • ((-Complex.I) •
                (Matrix.toEuclideanCLM
                  (n := Fin (d + 1)) (𝕜 := ℂ))
                  (finiteAndersonHamiltonian T onsite₀))))‖
          ≤ 2 * |t| * ε * ‖O‖) ∧
      (∀ (weight : Fin (d + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues r =
            fidelityReplicaPermutationFloor weight r) := by
  have hdense :=
    (finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure
      T hT).1
  have hopen : IsOpen (Metric.ball onsite₀ ε) :=
    Metric.isOpen_ball
  have hnonempty : (Metric.ball onsite₀ ε).Nonempty := by
    exact ⟨onsite₀, by simpa using hε⟩
  obtain ⟨onsite₁, hmax, hclose⟩ :=
    hdense.exists_mem_open hopen hnonempty
  have hconversion :=
    projectiveTemporalRank_gain_eq_relationRank_of_maximallyProjective
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₀).eigenvalues
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₁).eigenvalues
      hmax
  have hphase₀ :=
    relationPhaseEnsemble_temporalDimension_eq_projectiveRank
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₀).eigenvalues
  have hphase₁ :=
    relationPhaseEnsemble_temporalDimension_eq_projectiveRank
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₁).eigenvalues
  have hphaseConversion :
      phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues) -
          phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₀).eigenvalues) =
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (finiteAndersonHamiltonian_isHermitian
              T hT onsite₀).eigenvalues) := by
    rw [hphase₁, hphase₀]
    exact hconversion
  have hzero :=
    projectiveRelationRank_eq_zero_of_maximallyProjective
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₁).eigenvalues hmax
  have hfinite :
      ∀ (O : EuclideanSpace ℂ (Fin (d + 1)) →L[ℂ]
            EuclideanSpace ℂ (Fin (d + 1)))
          (t : ℝ),
        ‖NormedSpace.exp (t • ((-Complex.I) •
              (Matrix.toEuclideanCLM
                (n := Fin (d + 1)) (𝕜 := ℂ))
                (finiteAndersonHamiltonian T onsite₁))) * O *
              star (NormedSpace.exp (t • ((-Complex.I) •
                (Matrix.toEuclideanCLM
                  (n := Fin (d + 1)) (𝕜 := ℂ))
                  (finiteAndersonHamiltonian T onsite₁)))) -
            NormedSpace.exp (t • ((-Complex.I) •
              (Matrix.toEuclideanCLM
                (n := Fin (d + 1)) (𝕜 := ℂ))
                (finiteAndersonHamiltonian T onsite₀))) * O *
              star (NormedSpace.exp (t • ((-Complex.I) •
                (Matrix.toEuclideanCLM
                  (n := Fin (d + 1)) (𝕜 := ℂ))
                  (finiteAndersonHamiltonian T onsite₀))))‖
          ≤ 2 * |t| * ε * ‖O‖ := by
    intro O t
    calc
      _ ≤ 2 * |t| * dist onsite₁ onsite₀ * ‖O‖ :=
        finiteAnderson_heisenbergEvolution_norm_sub_le_onsiteDist
          T hT onsite₀ onsite₁ O t
      _ ≤ 2 * |t| * ε * ‖O‖ := by
        gcongr
        exact hclose.le
  have hcollision :
      ∀ (weight : Fin (d + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues r =
            fidelityReplicaPermutationFloor weight r := by
    intro weight hweight
    exact
      (all_fidelityReplicaCollisionMass_eq_floor_iff
        hweight
        (finiteAndersonHamiltonian_isHermitian
          T hT onsite₁).eigenvalues).2 hmax
  refine
    ⟨onsite₁, ?_, hmax, hphaseConversion, hzero, hfinite, hcollision⟩
  simpa [Metric.mem_ball] using hclose

end

end GaloisForLFunctions.HTGeometry
