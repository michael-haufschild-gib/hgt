import GaloisForLFunctions.HTGeometry.CountableProjectiveFutureUniversalityLaw
import GaloisForLFunctions.HTGeometry.CountableRecurrenceSingularityLaw
import GaloisForLFunctions.HTGeometry.FiniteAndersonRecurrenceConstraintConversionLaw

/-!
# Finite-horizon no-go for the completed recurrent future

No bounded observation horizon can certify the completed projective future of
a countably infinite pure-point Hamiltonian.  Given any horizon and any
positive experimental tolerance, one trace-class diagonal perturbation is
uniformly invisible to every normalized Heisenberg probe on every finite
spectral window throughout that horizon.  Nevertheless, the same
perturbation makes every forward projective orbit dense in the full product
torus, removes every nonzero exact global return, and realizes every finite
temporal rank.

The observable estimate is independent of the chosen window dimension.  The
perturbation is self-adjoint, preserves the maximal domain of an arbitrary
possibly unbounded diagonal Hamiltonian, and can be made smaller than the
explicit operator-norm budget selected from the horizon and tolerance.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open NormedSpace
open Topology

/-- **Finite-horizon global-recurrence no-go.**  Every finite-time family of
finite-window normalized operator probes is compatible, within every
positive tolerance, with maximal infinite projective future complexity. -/
theorem exists_finiteHorizonIndistinguishable_fullProjectiveFuture
    {I : Type*} [Countable I] [Infinite I]
    (energy : I → ℝ) (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      ‖realSummableDiagonalOperator w hw‖ <
        ε / (2 * (T + 1)) ∧
      IsSelfAdjoint (realSummableDiagonalOperator w hw) ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      IsSelfAdjoint
        (RHTower.maximalRealDiagonal (fun i => energy i + w i)) ∧
      FinitelySupportedMaximallyProjectiveEnergy
        (fun i => energy i + w i) ∧
      (∀ n : ℕ, ∃ e : Fin (n + 1) ↪ I,
        projectiveTemporalRank
          ((fun i => energy i + w i) ∘ e) = n) ∧
      (∀ anchor : I, ∀ τ : ℝ,
        closure
            (screwPhase
              (anchoredProjectiveGap
                (fun i => energy i + w i) anchor) '' Set.Ici τ) =
          Set.univ) ∧
      (∀ anchor : I, ∀ t : ℝ,
        screwPhase
            (anchoredProjectiveGap
              (fun i => energy i + w i) anchor) t = 0 →
          t = 0) ∧
      ∀ {J : Type*} [Fintype J] [DecidableEq J]
          (e : J ↪ I)
          (O : RHTower.FiniteIndexClockSpace J →L[ℂ]
            RHTower.FiniteIndexClockSpace J)
          (t : ℝ),
        ‖O‖ ≤ 1 → |t| ≤ T →
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                ((fun i => energy i + w i) ∘ e))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  ((fun i => energy i + w i) ∘ e)))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian (energy ∘ e))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (energy ∘ e))))‖ < ε := by
  let δ : ℝ := ε / (2 * (T + 1))
  have hT1 : 0 < T + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨w, hw, hpoint, hnorm, hself, htrace,
      hdomain, hHamiltonian, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  refine ⟨w, hw, hnorm, hself, htrace, hdomain, hHamiltonian, hmax,
    hmax.unboundedFiniteWindowTemporalRank, ?_, ?_, ?_⟩
  · intro anchor τ
    exact
      closure_screwPhase_anchoredProjectiveGap_image_Ici_eq_univ
        (fun i => energy i + w i) anchor hmax τ
  · intro anchor t
    exact hmax.no_nonzeroExactProjectiveReturn anchor t
  · intro J _ _ e O t hO ht
    let before : J → ℝ := energy ∘ e
    let after : J → ℝ := (fun i => energy i + w i) ∘ e
    have hwindowNorm :
        ‖RHTower.finiteIndexDiagonalHamiltonian after -
            RHTower.finiteIndexDiagonalHamiltonian before‖ ≤ δ := by
      apply finiteIndexDiagonalHamiltonian_norm_sub_le
        after before δ hδ.le
      intro j
      simpa [after, before, Function.comp_apply] using
        (hpoint (e j)).le
    have hduhamel :
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian after)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian after))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian before)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian before)))‖
          ≤ 2 * |t| * δ * ‖O‖ := by
      calc
        _ ≤ 2 * |t| *
            ‖RHTower.finiteIndexDiagonalHamiltonian after -
              RHTower.finiteIndexDiagonalHamiltonian before‖ * ‖O‖ :=
          selfAdjoint_heisenbergEvolution_norm_sub_le
            (RHTower.finiteIndexDiagonalHamiltonian after)
            (RHTower.finiteIndexDiagonalHamiltonian before) O
            (finiteIndexDiagonalHamiltonian_isSelfAdjoint after)
            (finiteIndexDiagonalHamiltonian_isSelfAdjoint before) t
        _ ≤ 2 * |t| * δ * ‖O‖ := by gcongr
    change _ < ε
    calc
      _ ≤ 2 * |t| * δ * ‖O‖ := hduhamel
      _ ≤ 2 * T * δ * 1 := by gcongr
      _ < ε := by
        dsimp [δ]
        field_simp
        nlinarith

/-- **Local finite-horizon recurrence no-go.**  For every fixed finite
Hermitian hopping matrix, arbitrarily small onsite-potential changes are
uniformly invisible to every normalized Heisenberg probe throughout a fixed
finite horizon, while producing maximal projective recurrence complexity and
all replica collision floors. -/
theorem exists_finiteAnderson_finiteHorizonIndistinguishable_fullConstraintConversion
    {d : ℕ}
    (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hT : T.IsHermitian)
    (onsite₀ : Fin (d + 1) → ℝ)
    (H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η) :
    ∃ onsite₁ : Fin (d + 1) → ℝ,
      dist onsite₁ onsite₀ < η / (2 * (H + 1)) ∧
      MaximallyProjectiveEnergy
        (finiteAndersonHamiltonian_isHermitian T hT onsite₁).eigenvalues ∧
      (∀ (O : EuclideanSpace ℂ (Fin (d + 1)) →L[ℂ]
            EuclideanSpace ℂ (Fin (d + 1)))
          (t : ℝ),
        ‖O‖ ≤ 1 → |t| ≤ H →
        ‖exp (t • ((-Complex.I) •
              (Matrix.toEuclideanCLM
                (n := Fin (d + 1)) (𝕜 := ℂ))
                (finiteAndersonHamiltonian T onsite₁))) * O *
              star (exp (t • ((-Complex.I) •
                (Matrix.toEuclideanCLM
                  (n := Fin (d + 1)) (𝕜 := ℂ))
                  (finiteAndersonHamiltonian T onsite₁)))) -
            exp (t • ((-Complex.I) •
              (Matrix.toEuclideanCLM
                (n := Fin (d + 1)) (𝕜 := ℂ))
                (finiteAndersonHamiltonian T onsite₀))) * O *
              star (exp (t • ((-Complex.I) •
                (Matrix.toEuclideanCLM
                  (n := Fin (d + 1)) (𝕜 := ℂ))
                  (finiteAndersonHamiltonian T onsite₀))))‖ < η) ∧
      ∀ (weight : Fin (d + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues r =
            fidelityReplicaPermutationFloor weight r := by
  let δ : ℝ := η / (2 * (H + 1))
  have hH1 : 0 < H + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨onsite₁, hclose, hmax, hconversion, hrank,
      hfinite, hcollision⟩ :=
    exists_finiteAnderson_onsite_fullConstraintConversion
      T hT onsite₀ δ hδ
  refine ⟨onsite₁, hclose, hmax, ?_, hcollision⟩
  intro O t hO ht
  calc
    _ ≤ 2 * |t| * δ * ‖O‖ := hfinite O t
    _ ≤ 2 * H * δ * 1 := by gcongr
    _ < η := by
      dsimp [δ]
      field_simp
      nlinarith

end

end GaloisForLFunctions.HTGeometry
