import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.EternityHorizonCapstone

/-!
# Every recurrence dimension inside every Hamiltonian neighbourhood

The completed observed orbit of a Hamiltonian presented as a unitary conjugation of a diagonal
spectrum has Minkowski dimension the rational rank of the gaps its reporter family resolves.
Reading the dimension off the presentation rather than off a chosen eigenbasis is what makes it
computable for a perturbation constructed from a prescribed spectrum.

With the reporter family that resolves every gap — the all-ones matrix conjugated into the
eigenbasis — the visible gap module is the full gap module, whose rank is the temporal dimension.
Hence every Hamiltonian neighbourhood contains completed orbits of every dimension `1, …, D-1`,
and no exact recurrence dimension is open.
-/

open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ}

/-! ### The observed orbit of a presented Hamiltonian -/

/-- The gap frequency of an entry coordinate, read off a presented spectrum. -/
def presentedGapFrequency (N : ℕ) (E : d → ℝ) : (Fin N × d × d) → ℝ :=
  fun p => E p.2.2 - E p.2.1

/-- The reporter weight of an entry coordinate, read off a presenting unitary. -/
def presentedReporterWeight (lam : Fin N → ℝ) (B : Fin N → Matrix d d ℂ) (V : Matrix d d ℂ) :
    (Fin N × d × d) → ℂ :=
  fun p => (Real.sqrt (lam p.1) : ℂ) * (star V * B p.1 * V) p.2.1 p.2.2

/-- **The observed orbit of a presented Hamiltonian is a weighted phase curve.** -/
theorem observedOrbit_eq_orbitAssembly_presented (lam : Fin N → ℝ) (B : Fin N → Matrix d d ℂ)
    {V : Matrix d d ℂ} (hV : V ∈ unitary (Matrix d d ℂ)) (E : d → ℝ) {H : Matrix d d ℂ}
    (hHV : H = V * Matrix.diagonal (fun i => (E i : ℂ)) * star V) (t : ℝ) :
    observedOrbit lam B H t
      = orbitAssembly V (weightedPhaseCurve (presentedGapFrequency N E)
          (presentedReporterWeight lam B V) t) := by
  refine congrArg (EuclideanSpace.equiv (Fin N × d × d) ℂ).symm ?_
  funext p
  obtain ⟨a, i, j⟩ := p
  have hmid : Matrix.of (fun i j =>
        weightedPhaseCurve (presentedGapFrequency N E) (presentedReporterWeight lam B V) t
          (a, i, j))
      = (Real.sqrt (lam a) : ℂ) •
        (Matrix.diagonal (fun i => Complex.exp (-(Complex.I * (t * E i))))
          * (star V * B a * V)
          * star (Matrix.diagonal (fun i => Complex.exp (-(Complex.I * (t * E i)))))) :=
    of_weightedPhaseCurve_eq_smul _ _ E _ _ t (fun i j => (a, i, j))
      (fun i j => rfl) (fun i j => rfl)
  have hrep := evolved_reporter_conj hV E hHV (B a) t
  show (Real.sqrt (lam a) : ℂ) *
      (unitaryEvolution H t * B a * star (unitaryEvolution H t)) i j
    = (V * Matrix.of (fun i j =>
        weightedPhaseCurve (presentedGapFrequency N E) (presentedReporterWeight lam B V) t
          (a, i, j)) * star V) i j
  rw [hmid, hrep, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

/-- The gaps a reporter family resolves in a presenting basis. -/
def presentedVisibleGapSet (B : Fin N → Matrix d d ℂ) (V : Matrix d d ℂ) (E : d → ℝ) : Set ℝ :=
  {g | ∃ a : Fin N, ∃ i j : d, (star V * B a * V) i j ≠ 0 ∧ g = E i - E j}

/-- **The completed observed orbit of a presented Hamiltonian has the dimension of its visible gap
module.** -/
theorem exists_hasBoxDim_closure_range_observedOrbit_presented (lam : Fin N → ℝ)
    (hlam : ∀ a, 0 < lam a) (B : Fin N → Matrix d d ℂ) {V : Matrix d d ℂ}
    (hV : V ∈ unitary (Matrix d d ℂ)) (E : d → ℝ) {H : Matrix d d ℂ}
    (hHV : H = V * Matrix.diagonal (fun i => (E i : ℂ)) * star V) :
    ∃ k : ℕ, (k : ℝ) = (Module.finrank ℚ (Submodule.span ℚ (presentedVisibleGapSet B V E)) : ℝ) ∧
      HasBoxDim (closure (Set.range (observedOrbit lam B H))) (k : ℝ) := by
  have hbi : IsBiLipschitz
      (orbitAssembly (N := N) V : ((Fin N × d × d) → ℂ) → EuclideanSpace ℂ (Fin N × d × d)) :=
    isBiLipschitz_orbitAssembly hV
  obtain ⟨k, hk, hdim⟩ := exists_hasBoxDim_closure_range_image_weightedPhaseCurve
    (presentedGapFrequency N E) (presentedReporterWeight lam B V) hbi
  have horbit : observedOrbit lam B H
      = (orbitAssembly V) ∘
        weightedPhaseCurve (presentedGapFrequency N E) (presentedReporterWeight lam B V) := by
    funext t
    exact observedOrbit_eq_orbitAssembly_presented lam B hV E hHV t
  have hsupport : presentedGapFrequency N E '' {p | presentedReporterWeight lam B V p ≠ 0}
      = (fun x => -x) '' presentedVisibleGapSet B V E := by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨a, i, j⟩ := p
      refine ⟨E i - E j, ⟨a, i, j, ?_, rfl⟩, ?_⟩
      · intro hzero
        exact hp (by rw [presentedReporterWeight, hzero, mul_zero])
      · rw [presentedGapFrequency]
        ring
    · rintro ⟨g', ⟨a, i, j, hne, rfl⟩, rfl⟩
      refine ⟨(a, i, j), ?_, ?_⟩
      · have hsq : (Real.sqrt (lam a) : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact Real.sqrt_ne_zero'.mpr (hlam a)
        exact mul_ne_zero hsq hne
      · rw [presentedGapFrequency]
        ring
  refine ⟨k, ?_, ?_⟩
  · rw [hk, hsupport, span_rat_image_neg]
  · rw [horbit]
    exact hdim

/-! ### The reporter family that resolves every gap -/

/-- The reporter family that resolves every gap: the all-ones matrix in the presenting basis. -/
def completeReporter (V : Matrix d d ℂ) : Fin 1 → Matrix d d ℂ :=
  fun _ => V * (Matrix.of fun _ _ => (1 : ℂ)) * star V

theorem star_mul_completeReporter_mul {V : Matrix d d ℂ} (hV : V ∈ unitary (Matrix d d ℂ))
    (a : Fin 1) : star V * completeReporter V a * V = Matrix.of fun _ _ => (1 : ℂ) := by
  have hstar : star V * V = 1 := (Unitary.mem_iff.mp hV).1
  rw [completeReporter]
  calc star V * (V * (Matrix.of fun _ _ => (1 : ℂ)) * star V) * V
      = (star V * V) * (Matrix.of fun _ _ => (1 : ℂ)) * (star V * V) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of fun _ _ => (1 : ℂ) := by rw [hstar, Matrix.one_mul, Matrix.mul_one]

/-- With the complete reporter family every gap is visible. -/
theorem presentedVisibleGapSet_completeReporter {V : Matrix d d ℂ}
    (hV : V ∈ unitary (Matrix d d ℂ)) (E : d → ℝ) :
    presentedVisibleGapSet (completeReporter V) V E = {g : ℝ | ∃ i j : d, g = E i - E j} := by
  ext g
  constructor
  · rintro ⟨a, i, j, -, rfl⟩
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    refine ⟨0, i, j, ?_, rfl⟩
    rw [star_mul_completeReporter_mul hV]
    exact one_ne_zero

/-! ### The gap module of a finite spectrum -/

/-- The full gap module is spanned by the anchored gaps. -/
theorem span_gapSet_eq_span_anchored {n : ℕ} (E : Fin (n + 1) → ℝ) :
    Submodule.span ℚ {g : ℝ | ∃ i j : Fin (n + 1), g = E i - E j}
      = Submodule.span ℚ (Set.range fun j : Fin n => E j.succ - E 0) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, j, rfl⟩
    have hmem : ∀ i : Fin (n + 1), E i - E 0 ∈
        Submodule.span ℚ (Set.range fun j : Fin n => E j.succ - E 0) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro m
        exact Submodule.subset_span ⟨m, rfl⟩
    have hsub : E i - E j = (E i - E 0) - (E j - E 0) := by ring
    rw [hsub]
    exact Submodule.sub_mem _ (hmem i) (hmem j)
  · rintro _ ⟨m, rfl⟩
    exact Submodule.subset_span ⟨m.succ, 0, rfl⟩

/-- **The gap module has the temporal dimension of the spectrum.** -/
theorem finrank_span_gapSet_eq_rationalCoordinateRank {n : ℕ} (E : Fin (n + 1) → ℝ) :
    Module.finrank ℚ (Submodule.span ℚ {g : ℝ | ∃ i j : Fin (n + 1), g = E i - E j})
      = rationalCoordinateRank (fun j : Fin n => E j.succ - E 0) := by
  rw [span_gapSet_eq_span_anchored, rationalCoordinateRank]

/-! ### Every dimension in every neighbourhood -/

variable {n : ℕ}

/-- **Corollary 2: every Hamiltonian neighbourhood contains every recurrence dimension.**  For every
prescribed dimension `k` and every uniform bounded-horizon tube, a commuting simple-spectrum
Hermitian neighbour has completed observed orbit of Minkowski dimension exactly `k`, read through
the reporter family that resolves every gap of the unperturbed eigenbasis. -/
theorem exists_isHermitian_commuting_orbitDimension_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      B.IsHermitian ∧ B * A = A * B ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        HasBoxDim (closure (Set.range (observedOrbit (fun _ : Fin 1 => (1 : ℝ))
          (completeReporter (hA.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) B)))
          (k : ℝ) := by
  obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_gapRank_uniform_horizon hk hkn A hA hT hη
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    (hA.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hVdef
  have hV : V ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := hA.eigenvectorUnitary.2
  have hHV : B = V * Matrix.diagonal (fun i => (E' i : ℂ)) * star V := hconj
  obtain ⟨m, hm, hdim⟩ := exists_hasBoxDim_closure_range_observedOrbit_presented
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ => one_pos) (completeReporter V) hV E' hHV
  refine ⟨B, hherm, hcomm, hclose, ?_⟩
  have hvis : presentedVisibleGapSet (completeReporter V) V E'
      = {g : ℝ | ∃ i j : Fin (n + 1), g = E' i - E' j} :=
    presentedVisibleGapSet_completeReporter hV E'
  rw [hvis, finrank_span_gapSet_eq_rationalCoordinateRank, hrank] at hm
  have hmk : m = k := by exact_mod_cast hm
  rw [← hmk]
  exact hdim

/-- **No exact recurrence dimension is open.**  From three levels onward every Hamiltonian has, in
every uniform bounded-horizon tube, commuting neighbours whose completed observed orbits have
different dimensions; so no dimension is locally constant in the Hamiltonian. -/
theorem exists_isHermitian_commuting_orbitDimension_distinct (hn : 2 ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ} (hT : 0 < T)
    (hη : 0 < η) :
    ∃ B₁ B₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      B₁.IsHermitian ∧ B₂.IsHermitian ∧ B₁ * A = A * B₁ ∧ B₂ * A = A * B₂ ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B₁ t - unitaryEvolution A t‖ < η) ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B₂ t - unitaryEvolution A t‖ < η) ∧
        HasBoxDim (closure (Set.range (observedOrbit (fun _ : Fin 1 => (1 : ℝ))
          (completeReporter (hA.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) B₁)))
          (1 : ℝ) ∧
        HasBoxDim (closure (Set.range (observedOrbit (fun _ : Fin 1 => (1 : ℝ))
          (completeReporter (hA.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) B₂)))
          (2 : ℝ) := by
  obtain ⟨B₁, hherm₁, hcomm₁, hclose₁, hdim₁⟩ :=
    exists_isHermitian_commuting_orbitDimension_uniform_horizon (k := 1) one_pos (by omega) A hA
      hT hη
  obtain ⟨B₂, hherm₂, hcomm₂, hclose₂, hdim₂⟩ :=
    exists_isHermitian_commuting_orbitDimension_uniform_horizon (k := 2) two_pos hn A hA hT hη
  exact ⟨B₁, B₂, hherm₁, hherm₂, hcomm₁, hcomm₂, hclose₁, hclose₂, by simpa using hdim₁,
    by simpa using hdim₂⟩

end

end GaloisForLFunctions.HTGeometry
