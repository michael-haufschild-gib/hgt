import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic
import GaloisForLFunctions.HTGeometry.AutonomousWordComplexityConeLaw
import GaloisForLFunctions.HTGeometry.StarProjectionPeriodicComplexityLaw

/-!
# Fixed-resolution packing by exactly periodic projector clocks

In dimension `d`, the diagonal Boolean projections form a family of size
`2^d`.  At half-period, their projector clocks are diagonal sign matrices.
Distinct sign matrices have operator-norm distance exactly `2`.

Consequently the half-period carrier of static projector Hamiltonians has
external covering number at least `2^d` at every radius below `1`.  This
removes the depth-dependent resolution loss of the two-level construction:
an exponentially large finite dictionary is defeated at one fixed physical
resolution while every selected trajectory still returns exactly after one
unit of time.
-/

open Set Topology Complex
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

abbrev FiniteComplexMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Coordinate projection selected by a Boolean string. -/
noncomputable def booleanDiagonalProjection {d : ℕ}
    (b : Fin d → Bool) : FiniteComplexMatrix d :=
  Matrix.diagonal fun i ↦ if b i then 1 else 0

theorem booleanDiagonalProjection_isStarProjection {d : ℕ}
    (b : Fin d → Bool) :
    IsStarProjection (booleanDiagonalProjection b) := by
  rw [isStarProjection_iff']
  constructor
  · rw [booleanDiagonalProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    cases b i <;> simp
  · rw [booleanDiagonalProjection, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases hi : b i = true <;> simp [hi]

theorem booleanDiagonalProjection_injective {d : ℕ} :
    Function.Injective
      (booleanDiagonalProjection : (Fin d → Bool) → FiniteComplexMatrix d) := by
  intro b c hbc
  funext i
  have hii := congrFun (congrFun hbc i) i
  cases hbi : b i <;> cases hci : c i <;>
    simp [booleanDiagonalProjection, hbi, hci] at hii ⊢

/-- Direct diagonal-sign description of the half-period endpoints. -/
noncomputable def booleanReflectionEndpoint {d : ℕ}
    (b : Fin d → Bool) : FiniteComplexMatrix d :=
  Matrix.diagonal fun i ↦ if b i then -1 else 1

theorem booleanReflectionEndpoint_injective {d : ℕ} :
    Function.Injective
      (booleanReflectionEndpoint : (Fin d → Bool) → FiniteComplexMatrix d) := by
  intro b c hbc
  funext i
  have hii := congrFun (congrFun hbc i) i
  cases hbi : b i <;> cases hci : c i
  · rfl
  · norm_num [booleanReflectionEndpoint, hbi, hci] at hii
  · norm_num [booleanReflectionEndpoint, hbi, hci] at hii
  · rfl

theorem coe_toCircle_half :
    ((AddCircle.toCircle
      (((1 / 2 : ℝ) : AddCircle (1 : ℝ))) : Circle) : ℂ) = -1 := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  convert Complex.exp_pi_mul_I
  field_simp

theorem starProjectionPhaseOrbit_booleanDiagonalProjection_half
    {d : ℕ} (b : Fin d → Bool) :
    starProjectionPhaseOrbit (booleanDiagonalProjection b)
        (((1 / 2 : ℝ) : AddCircle (1 : ℝ))) =
      booleanReflectionEndpoint b := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [starProjectionPhaseOrbit, coe_toCircle_half]
    cases hbi : b i <;>
      simp [idempotentPhase,
        booleanDiagonalProjection, booleanReflectionEndpoint,
        hbi]
  · simp [starProjectionPhaseOrbit, idempotentPhase,
      booleanDiagonalProjection, booleanReflectionEndpoint, hij]

private theorem booleanReflectionCoordinateDifference_norm
    {b c : Bool} (hbc : b ≠ c) :
    ‖((if b then (-1 : ℂ) else 1) -
      (if c then (-1 : ℂ) else 1))‖ = 2 := by
  cases b <;> cases c
  · simp at hbc
  · norm_num [Complex.norm_def, Complex.normSq_ofReal]
  · norm_num [Complex.norm_def, Complex.normSq_ofReal]
  · simp at hbc

/-- Distinct Boolean projector clocks are exactly distance two apart at
half-period in operator norm. -/
theorem dist_booleanReflectionEndpoint_eq_two {d : ℕ}
    {b c : Fin d → Bool} (hbc : b ≠ c) :
    dist (booleanReflectionEndpoint b)
      (booleanReflectionEndpoint c) = 2 := by
  rw [dist_eq_norm]
  have hdiag :
      booleanReflectionEndpoint b - booleanReflectionEndpoint c =
        Matrix.diagonal (fun i ↦
          (if b i then (-1 : ℂ) else 1) -
          (if c i then (-1 : ℂ) else 1)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [booleanReflectionEndpoint]
    · simp [booleanReflectionEndpoint, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    cases hbi : b i <;> cases hci : c i <;>
      norm_num [Complex.norm_def, Complex.normSq_ofReal]
  · have hpoint : ∃ i, b i ≠ c i := by
      by_contra h
      push Not at h
      exact hbc (funext h)
    obtain ⟨i, hi⟩ := hpoint
    have hle := norm_le_pi_norm
      (fun i ↦
        (if b i then (-1 : ℂ) else 1) -
        (if c i then (-1 : ℂ) else 1)) i
    rw [booleanReflectionCoordinateDifference_norm hi] at hle
    exact hle

/-- The complete Boolean half-period family. -/
noncomputable def booleanReflectionCarrier (d : ℕ) :
    Set (FiniteComplexMatrix d) :=
  Set.range
    (booleanReflectionEndpoint :
      (Fin d → Bool) → FiniteComplexMatrix d)

/-- The Boolean half-period family is `1`-separated. -/
theorem booleanReflectionCarrier_isSeparated (d : ℕ) :
    Metric.IsSeparated (1 : ℝ≥0)
      (booleanReflectionCarrier d) := by
  rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ hne
  have hbc : b ≠ c := by
    intro h
    apply hne
    exact congrArg booleanReflectionEndpoint h
  rw [edist_dist, dist_booleanReflectionEndpoint_eq_two hbc]
  norm_num

/-- The Boolean carrier contains at least `2^d` distinct endpoints. -/
theorem two_pow_le_encard_booleanReflectionCarrier (d : ℕ) :
    (2 ^ d : ℕ) ≤ (booleanReflectionCarrier d).encard := by
  have hinj :
      Function.Injective
        (booleanReflectionEndpoint :
          (Fin d → Bool) → FiniteComplexMatrix d) :=
    booleanReflectionEndpoint_injective
  simpa [booleanReflectionCarrier, ENat.card_eq_coe_fintype_card,
    Fintype.card_pi_const] using hinj.encard_range

/-- Fixed-radius metric entropy of the half-period projector family is at
least `2^d`. -/
theorem two_pow_le_externalCoveringNumber_booleanReflectionCarrier
    (d : ℕ) :
    (2 ^ d : ℕ) ≤
      Metric.externalCoveringNumber (1 / 2 : ℝ≥0)
        (booleanReflectionCarrier d) := by
  calc
    (2 ^ d : ℕ) ≤ (booleanReflectionCarrier d).encard :=
      two_pow_le_encard_booleanReflectionCarrier d
    _ ≤ Metric.packingNumber (1 : ℝ≥0)
        (booleanReflectionCarrier d) :=
      (booleanReflectionCarrier_isSeparated d).encard_le_packingNumber
        (by rfl)
    _ = Metric.packingNumber
        (2 * (1 / 2 : ℝ≥0)) (booleanReflectionCarrier d) := by norm_num
    _ ≤ Metric.externalCoveringNumber (1 / 2 : ℝ≥0)
        (booleanReflectionCarrier d) :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber _ _

/-- Every Boolean reflection endpoint belongs to the half-period carrier of
star-projection clocks. -/
theorem booleanReflectionCarrier_subset_starProjectionPhaseCarrier
    (d : ℕ) :
    booleanReflectionCarrier d ⊆
      starProjectionPhaseCarrier (FiniteComplexMatrix d)
        (((1 / 2 : ℝ) : AddCircle (1 : ℝ))) := by
  rintro _ ⟨b, rfl⟩
  refine ⟨⟨booleanDiagonalProjection b,
    booleanDiagonalProjection_isStarProjection b⟩, ?_⟩
  exact starProjectionPhaseOrbit_booleanDiagonalProjection_half b

/-- Fixed-radius metric entropy of all projector-clock orientations is at
least `2^d`. -/
theorem two_pow_le_externalCoveringNumber_starProjectionPhaseCarrier
    (d : ℕ) :
    (2 ^ d : ℕ) ≤
      Metric.externalCoveringNumber (1 / 2 : ℝ≥0)
        (starProjectionPhaseCarrier (FiniteComplexMatrix d)
          (((1 / 2 : ℝ) : AddCircle (1 : ℝ)))) := by
  exact
    (two_pow_le_externalCoveringNumber_booleanReflectionCarrier d).trans
      (Metric.externalCoveringNumber_mono_set
        (booleanReflectionCarrier_subset_starProjectionPhaseCarrier d))

/-- **Fixed-resolution exponential complexity with exact recurrence.**
Whenever a finite endpoint dictionary has fewer than `2^d` elements and
contains the identity, one diagonal Boolean projection selects a static
Hamiltonian `H = -2πP` whose evolution is exactly one-periodic and whose
cycle contains an endpoint more than `1/2` away from the whole dictionary.
After every real start, identity-near, dictionary-hard, and identity-near
epochs occur in strict order, with each leg at most one period.

The robustness radius is the same `1/2` in every dimension and for every
dictionary satisfying the cardinal inequality. -/
theorem booleanProjectorClock_fixedResolution_easyHard_alternate
    {d : ℕ} {C : Set (FiniteComplexMatrix d)}
    (hone : (1 : FiniteComplexMatrix d) ∈ C)
    (hCard : C.encard < (2 ^ d : ℕ)) :
    ∃ b : Fin d → Bool,
      IsStarProjection (booleanDiagonalProjection b) ∧
      (∀ t : AddCircle (1 : ℝ),
        starProjectionPhaseOrbit (booleanDiagonalProjection b) t ∈
          unitary (FiniteComplexMatrix d)) ∧
      (∀ t : ℝ,
        starProjectionPhaseOrbit (booleanDiagonalProjection b)
            ((t + 1 : ℝ) : AddCircle (1 : ℝ)) =
          starProjectionPhaseOrbit (booleanDiagonalProjection b)
            (t : AddCircle (1 : ℝ))) ∧
      ∀ a : ℝ,
        ∃ tEasy ∈ Set.Icc a (a + 1),
        ∃ tHard ∈ Set.Ioc tEasy (tEasy + 1),
        ∃ tEasy' ∈ Set.Ioc tHard (tHard + 1),
          starProjectionPhaseOrbit (booleanDiagonalProjection b)
              (tEasy : AddCircle (1 : ℝ)) ∈
            interior (metricClosedBallTarget (1 / 2 : ℝ≥0) C) ∧
          (∀ c ∈ C,
            (1 / 2 : ℝ) <
              dist
                (starProjectionPhaseOrbit (booleanDiagonalProjection b)
                  (tHard : AddCircle (1 : ℝ))) c) ∧
          starProjectionPhaseOrbit (booleanDiagonalProjection b)
              (tEasy' : AddCircle (1 : ℝ)) ∈
            interior (metricClosedBallTarget (1 / 2 : ℝ≥0) C) := by
  have hEntropy :
      C.encard <
        Metric.externalCoveringNumber (1 / 2 : ℝ≥0)
          (booleanReflectionCarrier d) :=
    hCard.trans_le
      (two_pow_le_externalCoveringNumber_booleanReflectionCarrier d)
  have hcover :
      ∀ x ∈ booleanReflectionCarrier d,
        ∃ b : Fin d → Bool, ∃ z : AddCircle (1 : ℝ),
          starProjectionPhaseOrbit (booleanDiagonalProjection b) z = x := by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, ((1 / 2 : ℝ) : AddCircle (1 : ℝ)),
      starProjectionPhaseOrbit_booleanDiagonalProjection_half b⟩
  obtain ⟨b, hb⟩ :=
    unitPeriodicFamily_coveringEntropy_easyHard_alternate
      (embed := fun b : Fin d → Bool ↦
        starProjectionPhaseOrbit (booleanDiagonalProjection b))
      hcover (1 : FiniteComplexMatrix d) hone
      (fun b ↦ starProjectionPhaseOrbit_zero
        (booleanDiagonalProjection b))
      (1 / 2 : ℝ≥0) (by norm_num) hEntropy
  have hp : IsStarProjection (booleanDiagonalProjection b) :=
    booleanDiagonalProjection_isStarProjection b
  exact ⟨b, hp,
    fun t ↦ starProjectionPhaseOrbit_mem_unitary hp t,
    fun t ↦ unitPeriodicFamily_period_one
      (fun b : Fin d → Bool ↦
        starProjectionPhaseOrbit (booleanDiagonalProjection b)) b t,
    hb⟩

/-- Matrix endpoints of all words of length at most `s`. -/
def finiteDimensionalBoundedCircuitEndpointSet
    {d : ℕ} {gate : Type*}
    (generator : gate → unitary (FiniteComplexMatrix d))
    (s : ℕ) : Set (FiniteComplexMatrix d) :=
  (fun w : List gate ↦
    ((circuitWordValue generator w :
      unitary (FiniteComplexMatrix d)) : FiniteComplexMatrix d)) ''
      {w | w.length ≤ s}

theorem finiteDimensionalBoundedCircuitEndpointSet_finite
    {d : ℕ} {gate : Type*} [Finite gate]
    (generator : gate → unitary (FiniteComplexMatrix d)) (s : ℕ) :
    (finiteDimensionalBoundedCircuitEndpointSet generator s).Finite := by
  exact (List.finite_length_le gate s).image _

theorem one_mem_finiteDimensionalBoundedCircuitEndpointSet
    {d : ℕ} {gate : Type*}
    (generator : gate → unitary (FiniteComplexMatrix d)) (s : ℕ) :
    (1 : FiniteComplexMatrix d) ∈
      finiteDimensionalBoundedCircuitEndpointSet generator s := by
  refine ⟨[], by simp, ?_⟩
  simp [circuitWordValue]

/-- A word of length at most `s` embeds into the disjoint union of all
fixed-length word types up to `s`. -/
def boundedWordEmbedding {gate : Type*} (s : ℕ) :
    {w : List gate // w.length ≤ s} ↪
      Σ k : Fin (s + 1), List.Vector gate k.1 where
  toFun w :=
    ⟨⟨w.1.length, Nat.lt_succ_iff.mpr w.2⟩, ⟨w.1, rfl⟩⟩
  inj' w v h := by
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) h

/-- Exact geometric-sum upper bound for the number of distinct circuit
endpoints of depth at most `s`. -/
theorem encard_finiteDimensionalBoundedCircuitEndpointSet_le
    {d : ℕ} {gate : Type*} [Fintype gate]
    (generator : gate → unitary (FiniteComplexMatrix d)) (s : ℕ) :
    (finiteDimensionalBoundedCircuitEndpointSet generator s).encard ≤
      (∑ k : Fin (s + 1), Fintype.card gate ^ k.1 : ℕ) := by
  let W : Set (List gate) := {w | w.length ≤ s}
  let endpoint : List gate → FiniteComplexMatrix d := fun w ↦
    ((circuitWordValue generator w :
      unitary (FiniteComplexMatrix d)) : FiniteComplexMatrix d)
  calc
    (finiteDimensionalBoundedCircuitEndpointSet generator s).encard =
        (endpoint '' W).encard := by rfl
    _ ≤ W.encard := Set.encard_image_le endpoint W
    _ = ENat.card {w : List gate // w.length ≤ s} := rfl
    _ ≤ ENat.card
        (Σ k : Fin (s + 1), List.Vector gate k.1) :=
      ENat.card_le_card_of_injective
        (boundedWordEmbedding (gate := gate) s).injective
    _ = (∑ k : Fin (s + 1), Fintype.card gate ^ k.1 : ℕ) := by
      rw [ENat.card_eq_coe_fintype_card]
      norm_cast
      simp only [Fintype.card_sigma, card_vector]

/-- **Fixed-resolution, exponentially deep circuit hardness on an exact
one-period clock.** Let `d` be Hilbert-space dimension and let the finite gate
alphabet contain `g` gates.  If the total number

`1 + g + ... + g^s`

of words through depth `s` is smaller than `2^d`, then one diagonal,
time-independent Hamiltonian `H = -2πP` has all of the following
simultaneously:

* exact period one;
* a self-adjoint static generator and exact Schrödinger exponential;
* after every starting time, a strict easy--hard--easy sequence with every
  leg at most one period;
* operator-norm separation greater than `1/2` from every circuit word of
  depth at most `s` at the hard epoch.

Thus fixed-resolution circuit hardness can be exponential in `d` while the
recurrence period stays exactly one. -/
theorem diagonalProjectorClock_fixedResolution_circuitHard
    {d : ℕ} {gate : Type*} [Fintype gate]
    (generator : gate → unitary (FiniteComplexMatrix d)) (s : ℕ)
    (hWords :
      (∑ k : Fin (s + 1), Fintype.card gate ^ k.1 : ℕ) <
        2 ^ d) :
    ∃ b : Fin d → Bool,
      IsSelfAdjoint
        (starProjectionHamiltonian (booleanDiagonalProjection b)) ∧
      (∀ t : ℝ,
        starProjectionPhaseOrbit (booleanDiagonalProjection b)
            (t : AddCircle (1 : ℝ)) =
          NormedSpace.exp (((-(t : ℂ)) * Complex.I) •
            starProjectionHamiltonian (booleanDiagonalProjection b))) ∧
      (∀ t : ℝ,
        starProjectionPhaseOrbit (booleanDiagonalProjection b)
            ((t + 1 : ℝ) : AddCircle (1 : ℝ)) =
          starProjectionPhaseOrbit (booleanDiagonalProjection b)
            (t : AddCircle (1 : ℝ))) ∧
      ∀ a : ℝ,
        ∃ tEasy ∈ Set.Icc a (a + 1),
        ∃ tHard ∈ Set.Ioc tEasy (tEasy + 1),
        ∃ tEasy' ∈ Set.Ioc tHard (tHard + 1),
          starProjectionPhaseOrbit (booleanDiagonalProjection b)
              (tEasy : AddCircle (1 : ℝ)) ∈
            interior (metricClosedBallTarget (1 / 2 : ℝ≥0)
              (finiteDimensionalBoundedCircuitEndpointSet generator s)) ∧
          CircuitWordSeparated generator (1 / 2 : ℝ) s
            ⟨starProjectionPhaseOrbit (booleanDiagonalProjection b)
                (tHard : AddCircle (1 : ℝ)),
              starProjectionPhaseOrbit_mem_unitary
                (booleanDiagonalProjection_isStarProjection b) _⟩ ∧
          starProjectionPhaseOrbit (booleanDiagonalProjection b)
              (tEasy' : AddCircle (1 : ℝ)) ∈
            interior (metricClosedBallTarget (1 / 2 : ℝ≥0)
              (finiteDimensionalBoundedCircuitEndpointSet generator s)) := by
  let C :=
    finiteDimensionalBoundedCircuitEndpointSet generator s
  have hWordsENat :
      ((∑ k : Fin (s + 1), Fintype.card gate ^ k.1 : ℕ) : ℕ∞) <
        ((2 ^ d : ℕ) : ℕ∞) := by
    exact_mod_cast hWords
  have hCard : C.encard < (2 ^ d : ℕ) :=
    (encard_finiteDimensionalBoundedCircuitEndpointSet_le
      generator s).trans_lt hWordsENat
  obtain ⟨b, hp, _hunitary, hperiod, hb⟩ :=
    booleanProjectorClock_fixedResolution_easyHard_alternate
      (C := C)
      (one_mem_finiteDimensionalBoundedCircuitEndpointSet generator s)
      hCard
  refine ⟨b, starProjectionHamiltonian_isSelfAdjoint hp,
    fun t ↦ starProjectionPhaseOrbit_eq_staticEvolution
      hp.isIdempotentElem t,
    hperiod, fun a ↦ ?_⟩
  obtain ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
      hEasy, hHard, hEasy'⟩ := hb a
  refine ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
    hEasy, ?_, hEasy'⟩
  intro w hw
  have hwC :
      ((circuitWordValue generator w :
        unitary (FiniteComplexMatrix d)) : FiniteComplexMatrix d) ∈ C :=
    ⟨w, hw, rfl⟩
  have hsep := hHard _ hwC
  simpa only [Subtype.dist_eq, dist_comm] using hsep

end GaloisForLFunctions.HTGeometry
