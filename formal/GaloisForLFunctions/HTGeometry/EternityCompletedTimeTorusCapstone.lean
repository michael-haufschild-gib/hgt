import GaloisForLFunctions.HTGeometry.EternityReturnExponentCapstone
import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus

/-!
# The completed time of a prescribed neighbour is a torus of the prescribed dimension

The completed projective time of a finite spectrum — the closure of its relative phase orbit — is a
compact connected subgroup of the phase torus, isomorphic as a topological group to a torus of
dimension the rational rank of the gap packet.  Combined with the commuting perturbation of
prescribed temporal dimension, every Hamiltonian neighbourhood contains completed times that are
tori of every dimension `1, …, D-1`, all inside a uniform bounded-horizon tube.

The same presentation gives the two-sided return-volume law of the neighbour: its pulled-back
anchored return target has Haar volume between two explicit multiples of `ε` to the prescribed
dimension.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- The projective frequencies of a finite spectrum are its anchored gaps. -/
theorem range_projectiveFrequency_eq (E : Fin (n + 1) → ℝ) :
    Set.range (projectiveFrequency E 0) = Set.range (fun j : Fin n => E j.succ - E 0) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero i.2
    refine ⟨j, ?_⟩
    show E j.succ - E 0 = projectiveFrequency E 0 i
    rw [projectiveFrequency, hj]
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.succ, Fin.succ_ne_zero j⟩, rfl⟩

/-- The projective frequency packet has the temporal dimension of the spectrum. -/
theorem finrank_span_projectiveFrequency_eq (E : Fin (n + 1) → ℝ) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (projectiveFrequency E 0)))
      = rationalCoordinateRank (fun j : Fin n => E j.succ - E 0) := by
  rw [range_projectiveFrequency_eq, rationalCoordinateRank]

/-- **Corollary 2, group form: every Hamiltonian neighbourhood contains completed times of every
dimension.**  For every prescribed temporal dimension `k` and every uniform bounded-horizon tube, a
commuting simple-spectrum Hermitian neighbour has completed projective time a compact connected
subgroup of the phase torus, presented isomorphically by a `k`-dimensional torus. -/
theorem exists_isHermitian_commuting_completedTimeTorus_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ)
      (M : {i : Fin (n + 1) // i ≠ 0} → Fin k → ℤ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        rationalCoordinateRank (fun j : Fin n => E' j.succ - E' 0) = k ∧
        closure (Set.range (finiteClockPhasePoint (projectiveFrequency E' 0)))
            = ((torusIntegerAddHom M).range :
              Set (UnitAddTorus {i : Fin (n + 1) // i ≠ 0})) ∧
          IsCompact (closure (Set.range (finiteClockPhasePoint (projectiveFrequency E' 0)))) ∧
          IsConnected (closure (Set.range (finiteClockPhasePoint (projectiveFrequency E' 0)))) ∧
          Function.Injective (torusIntegerHom M) := by
  obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_gapRank_uniform_horizon hk hkn A hA hT hη
  obtain ⟨k', M, hclosure, hcompact, hconn, hMinj, hk'⟩ :=
    exists_completedTime_representation (projectiveFrequency E' 0)
  have hkk : k' = k := by
    rw [hk', finrank_span_projectiveFrequency_eq, hrank]
  subst hkk
  exact ⟨B, E', M, hherm, hcomm, hinj, hclose, hrank, hclosure, hcompact, hconn, hMinj⟩

/-- **Corollary 3 `(4)`: the two-sided return-volume law of a prescribed neighbour.**  The
pulled-back anchored return target of the neighbour's presenting torus has Haar volume between two
explicit positive multiples of `ε` to the prescribed dimension, for all small tolerances. -/
theorem exists_isHermitian_commuting_returnVolume_sandwich_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ) (gamma : Fin k → ℝ)
      (M : Fin n → Fin k → ℤ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        (∀ i : Fin n, E' i.succ - E' 0 = ∑ j, (M i j : ℝ) * gamma j) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          (2 / torusRowBound M) ^ k * ε ^ k ≤
              ((finiteTorusHaarProbabilityMeasure (Fin k) : Measure (UnitAddTorus (Fin k)))
                (integerReturnPreimage M ε)).toReal ∧
            ((finiteTorusHaarProbabilityMeasure (Fin k) : Measure (UnitAddTorus (Fin k)))
                (integerReturnPreimage M ε)).toReal ≤ (4 : ℝ) ^ k * ε ^ k) ∧
        Tendsto (fun ε : ℝ => Real.log
            ((finiteTorusHaarProbabilityMeasure (Fin k) : Measure (UnitAddTorus (Fin k)))
              (integerReturnPreimage M ε)).toReal / Real.log ε)
          (𝓝[>] 0) (𝓝 (k : ℝ)) := by
  obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_gapRank_uniform_horizon hk hkn A hA hT hη
  obtain ⟨k', gamma, M, Aint, -, -, -, hM, hAM, hk'⟩ :=
    exists_frequency_integer_basis (fun i : Fin n => E' i.succ - E' 0)
  have hkk : k' = k := hk'.trans hrank
  subst hkk
  have hspan := span_rows_eq_top_of_leftInverse M Aint hAM
  obtain ⟨σ, hσ⟩ := exists_selectedSquare_det_ne_zero M hspan
  refine ⟨B, E', gamma, M, hherm, hcomm, hinj, hclose, hM, ?_, ?_⟩
  · simpa using integerReturnPreimage_measure_sandwich M σ hσ
  · simpa using tendsto_log_integerReturnPreimage_div_log_of_span M hspan

/-- **Corollary 2 as worded**: the neighbour's completed time *is* a `k`-torus.  The phase-orbit
closure is not merely the range of an integer presentation; because that presentation is injective
and the presenting torus is compact, the closure is homeomorphic to the `k`-torus and isomorphic to
it as a topological group. -/
theorem exists_isHermitian_commuting_completedTimeTorus_equiv_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ)
      (M : {i : Fin (n + 1) // i ≠ 0} → Fin k → ℤ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        rationalCoordinateRank (fun j : Fin n => E' j.succ - E' 0) = k ∧
        Nonempty (UnitAddTorus (Fin k) ≃ₜ
          (closure (Set.range (finiteClockPhasePoint (projectiveFrequency E' 0))))) ∧
        Nonempty (UnitAddTorus (Fin k) ≃+ (torusIntegerAddHom M).range) := by
  obtain ⟨B, E', M, hherm, hcomm, hinj, hclose, hrank, hclosure, -, -, hMinj⟩ :=
    exists_isHermitian_commuting_completedTimeTorus_uniform_horizon hk hkn A hA hT hη
  exact ⟨B, E', M, hherm, hcomm, hinj, hclose, hrank,
    nonempty_homeomorph_of_eq_torusIntegerAddHom_range hclosure hMinj,
    ⟨torusIntegerAddEquivRange hMinj⟩⟩

end

end GaloisForLFunctions.HTGeometry
