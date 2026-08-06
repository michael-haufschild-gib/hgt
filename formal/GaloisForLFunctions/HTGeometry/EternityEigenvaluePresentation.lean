import GaloisForLFunctions.HTGeometry.EternityCompletedTimeTorusCapstone

/-!
# The temporal dimension read off the eigenvalues themselves

A commuting perturbation is built from a prescribed spectrum, so its temporal dimension is stated
in terms of that spectrum.  The card states it in terms of the eigenvalues of the perturbed matrix.
The two agree: a unitary conjugation of a real diagonal matrix has exactly the diagonal entries as
its spectrum, so the eigenvalue function and the prescribed spectrum have the same value set, hence
the same gap module and the same rank; and a prescribed simple spectrum makes the eigenvalue
function itself injective.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- **The eigenvalue value set of a spectral presentation.**  Conjugating a real diagonal matrix by
a unitary leaves the spectrum, hence the set of eigenvalues, equal to the diagonal entries. -/
theorem range_eigenvalues_of_presentation {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hB : B.IsHermitian) {V : Matrix.unitaryGroup (Fin (n + 1)) ℂ} {E : Fin (n + 1) → ℝ}
    (hpres : B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) V)
      (Matrix.diagonal (RCLike.ofReal ∘ E))) :
    Set.range hB.eigenvalues = Set.range E := by
  have h1 : spectrum ℝ B = Set.range hB.eigenvalues :=
    Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues (𝕜 := ℂ) hB
  have h2C : spectrum ℂ B
      = spectrum ℂ (Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ E)) := by
    rw [hpres]
    exact AlgEquiv.spectrum_eq
      (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) V) _
  have h3 : spectrum ℝ B = Set.range E := by
    ext r
    rw [← spectrum.algebraMap_mem_iff ℂ, h2C, spectrum_diagonal]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hcast : ((E i : ℝ) : ℂ) = ((r : ℝ) : ℂ) := hi
      exact_mod_cast hcast
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  rw [← h1, h3]

/-- A presented simple spectrum makes the eigenvalue function injective. -/
theorem injective_eigenvalues_of_presentation {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hB : B.IsHermitian) {V : Matrix.unitaryGroup (Fin (n + 1)) ℂ} {E : Fin (n + 1) → ℝ}
    (hpres : B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) V)
      (Matrix.diagonal (RCLike.ofReal ∘ E))) (hinj : Function.Injective E) :
    Function.Injective hB.eigenvalues := by
  classical
  have hrange : Set.range hB.eigenvalues = Set.range E :=
    range_eigenvalues_of_presentation hB hpres
  have himage : (Finset.univ.image hB.eigenvalues) = (Finset.univ.image E) := by
    ext x
    have hx : x ∈ Set.range hB.eigenvalues ↔ x ∈ Set.range E := by rw [hrange]
    simpa [Finset.mem_image, Set.mem_range] using hx
  have hcard : (Finset.univ.image hB.eigenvalues).card
      = (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [himage, Finset.card_image_of_injective _ hinj]
  have hinjOn : Set.InjOn hB.eigenvalues (Finset.univ : Finset (Fin (n + 1))) :=
    Finset.card_image_iff.mp hcard
  intro i j hij
  exact hinjOn (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij

/-- The gap module, hence the temporal dimension, depends only on the value set of the
spectrum. -/
theorem rationalCoordinateRank_gaps_congr {E F : Fin (n + 1) → ℝ}
    (hEF : Set.range E = Set.range F) :
    rationalCoordinateRank (fun j : Fin n => E j.succ - E 0)
      = rationalCoordinateRank (fun j : Fin n => F j.succ - F 0) := by
  have hset : {g : ℝ | ∃ i j : Fin (n + 1), g = E i - E j}
      = {g : ℝ | ∃ i j : Fin (n + 1), g = F i - F j} := by
    ext g
    constructor
    · rintro ⟨i, j, rfl⟩
      obtain ⟨i', hi'⟩ : E i ∈ Set.range F := by rw [← hEF]; exact ⟨i, rfl⟩
      obtain ⟨j', hj'⟩ : E j ∈ Set.range F := by rw [← hEF]; exact ⟨j, rfl⟩
      exact ⟨i', j', by rw [hi', hj']⟩
    · rintro ⟨i, j, rfl⟩
      obtain ⟨i', hi'⟩ : F i ∈ Set.range E := by rw [hEF]; exact ⟨i, rfl⟩
      obtain ⟨j', hj'⟩ : F j ∈ Set.range E := by rw [hEF]; exact ⟨j, rfl⟩
      exact ⟨i', j', by rw [hi', hj']⟩
  rw [← finrank_span_gapSet_eq_rationalCoordinateRank E,
    ← finrank_span_gapSet_eq_rationalCoordinateRank F, hset]

/-- **Theorem B in the card's own form.**  Every Hermitian matrix has, in every operator-norm
neighbourhood, a commuting Hermitian neighbour whose *own* eigenvalues are simple and whose
temporal dimension, computed from those eigenvalues, is exactly the prescribed value. -/
theorem exists_isHermitian_commuting_close_eigenvalueGapRank {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
      B * A = A * B ∧ ‖B - A‖ < ε ∧ Function.Injective hB.eigenvalues ∧
        rationalCoordinateRank
            (fun j : Fin n => hB.eigenvalues j.succ - hB.eigenvalues 0) = k := by
  obtain ⟨B, E', hherm, hcomm, hinj, hnorm, hconj, hrank⟩ :=
    exists_isHermitian_commuting_close_gapRank hk hkn A hA hε
  refine ⟨B, hherm, hcomm, hnorm, injective_eigenvalues_of_presentation hherm hconj hinj, ?_⟩
  rw [rationalCoordinateRank_gaps_congr (range_eigenvalues_of_presentation hherm hconj)]
  exact hrank

/-- **Theorem B with a horizon, on the eigenvalues themselves.** -/
theorem exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
      B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
        rationalCoordinateRank
            (fun j : Fin n => hB.eigenvalues j.succ - hB.eigenvalues 0) = k ∧
        ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η := by
  obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_gapRank_uniform_horizon hk hkn A hA hT hη
  refine ⟨B, hherm, hcomm, injective_eigenvalues_of_presentation hherm hconj hinj, ?_, hclose⟩
  rw [rationalCoordinateRank_gaps_congr (range_eigenvalues_of_presentation hherm hconj)]
  exact hrank

/-- **Corollary 1 on the eigenvalues themselves.**  From three levels onward every Hermitian matrix
has, inside every uniform bounded-horizon tube, a commuting neighbour whose own spectrum is simple
and returns exactly, and one whose own spectrum is simple and never returns exactly. -/
theorem exists_isHermitian_commuting_eigenvaluePeriodic_and_aperiodic_uniform_horizon
    (hn : 2 ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    (∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
        B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
          HasPositiveProjectiveReturn hB.eigenvalues ∧
          ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
      ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian),
        B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
          ¬ HasPositiveProjectiveReturn hB.eigenvalues ∧
          ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η := by
  have hnpos : 0 < n := by omega
  constructor
  · obtain ⟨B, hB, hcomm, hinj, hrank, hclose⟩ :=
      exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon (k := 1) one_pos (by omega)
        A hA hT hη
    exact ⟨B, hB, hcomm, hinj,
      (hasPositiveProjectiveReturn_iff_gapRank_eq_one hnpos hinj).mpr hrank, hclose⟩
  · obtain ⟨B, hB, hcomm, hinj, hrank, hclose⟩ :=
      exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon (k := 2) two_pos hn
        A hA hT hη
    refine ⟨B, hB, hcomm, hinj, ?_, hclose⟩
    intro hret
    have h1 := (hasPositiveProjectiveReturn_iff_gapRank_eq_one hnpos hinj).mp hret
    rw [hrank] at h1
    omega

/-- **Corollary 3 on the eigenvalues themselves.**  The neighbour's own spectral gaps are presented
by an integer character matrix over a `k`-dimensional frequency basis, and the pulled-back anchored
return target on that presenting torus has logarithmic Haar exponent exactly `k`. -/
theorem exists_isHermitian_commuting_eigenvalueReturnExponent_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian) (gamma : Fin k → ℝ)
      (M : Fin n → Fin k → ℤ),
      B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        (∀ i : Fin n, hB.eigenvalues i.succ - hB.eigenvalues 0
          = ∑ j, (M i j : ℝ) * gamma j) ∧
        Filter.Tendsto (fun ε : ℝ => Real.log
            ((finiteTorusHaarProbabilityMeasure (Fin k) :
              MeasureTheory.Measure (UnitAddTorus (Fin k)))
              (integerReturnPreimage M ε)).toReal / Real.log ε)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (k : ℝ)) := by
  obtain ⟨B, hB, hcomm, hinj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon hk hkn A hA hT hη
  obtain ⟨k', gamma, M, Aint, -, -, -, hM, hAM, hk'⟩ :=
    exists_frequency_integer_basis (fun i : Fin n => hB.eigenvalues i.succ - hB.eigenvalues 0)
  have hkk : k' = k := hk'.trans hrank
  subst hkk
  refine ⟨B, hB, gamma, M, hcomm, hinj, hclose, hM, ?_⟩
  have hspan := span_rows_eq_top_of_leftInverse M Aint hAM
  simpa using tendsto_log_integerReturnPreimage_div_log_of_span M hspan

/-- **Corollary 2, group form, on the eigenvalues themselves.**  The neighbour's completed
projective time — built from its own spectral gaps — is a compact connected subgroup of the phase
torus, presented isomorphically by a `k`-dimensional torus. -/
theorem exists_isHermitian_commuting_eigenvalueCompletedTimeTorus_uniform_horizon {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian)
      (M : {i : Fin (n + 1) // i ≠ 0} → Fin k → ℤ),
      B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        closure (Set.range (finiteClockPhasePoint (projectiveFrequency hB.eigenvalues 0)))
            = ((torusIntegerAddHom M).range :
              Set (UnitAddTorus {i : Fin (n + 1) // i ≠ 0})) ∧
          IsCompact (closure
            (Set.range (finiteClockPhasePoint (projectiveFrequency hB.eigenvalues 0)))) ∧
          IsConnected (closure
            (Set.range (finiteClockPhasePoint (projectiveFrequency hB.eigenvalues 0)))) ∧
          Function.Injective (torusIntegerHom M) := by
  obtain ⟨B, hB, hcomm, hinj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_eigenvalueGapRank_uniform_horizon hk hkn A hA hT hη
  obtain ⟨k', M, hclosure, hcompact, hconn, hMinj, hk'⟩ :=
    exists_completedTime_representation (projectiveFrequency hB.eigenvalues 0)
  have hkk : k' = k := by
    rw [hk', finrank_span_projectiveFrequency_eq, hrank]
  subst hkk
  exact ⟨B, hB, M, hcomm, hinj, hclose, hclosure, hcompact, hconn, hMinj⟩


/-- **Corollary 2 as worded, on the eigenvalues themselves**: the neighbour's completed projective
time is a `k`-torus, homeomorphically and as a topological group. -/
theorem exists_isHermitian_commuting_eigenvalueCompletedTimeTorus_equiv_uniform_horizon {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : B.IsHermitian)
      (M : {i : Fin (n + 1) // i ≠ 0} → Fin k → ℤ),
      B * A = A * B ∧ Function.Injective hB.eigenvalues ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        Nonempty (UnitAddTorus (Fin k) ≃ₜ
          (closure (Set.range (finiteClockPhasePoint (projectiveFrequency hB.eigenvalues 0))))) ∧
        Nonempty (UnitAddTorus (Fin k) ≃+ (torusIntegerAddHom M).range) := by
  obtain ⟨B, hB, M, hcomm, hinj, hclose, hclosure, -, -, hMinj⟩ :=
    exists_isHermitian_commuting_eigenvalueCompletedTimeTorus_uniform_horizon hk hkn A hA hT hη
  exact ⟨B, hB, M, hcomm, hinj, hclose,
    nonempty_homeomorph_of_eq_torusIntegerAddHom_range hclosure hMinj,
    ⟨torusIntegerAddEquivRange hMinj⟩⟩

end

end GaloisForLFunctions.HTGeometry
