import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic
import GaloisForLFunctions.HTGeometry.AutonomousWordComplexityConeLaw
import GaloisForLFunctions.HTGeometry.StarProjectionPeriodicComplexityLaw

/-!
# Concrete two-level projector clocks defeat every finite dictionary

The rank-one projections

`P_t = (1 + t²)⁻¹ [[1,t],[t,t²]]`

form an injective real family of star projections on a two-level Hilbert
space.  At every nontrivial clock phase their unitary endpoints remain an
infinite family.  Therefore every finite circuit dictionary misses one such
endpoint by a positive distance.  The corresponding static one-frequency
clock repeats exactly every unit period and reproduces that hard endpoint in
every period.
-/

open Set Topology Complex
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

abbrev FinTwoComplexMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- An explicit real line of rank-one projections in two complex dimensions. -/
noncomputable def finTwoRankOneProjection (t : ℝ) : FinTwoComplexMatrix :=
  !![((1 / (1 + t ^ 2) : ℝ) : ℂ), ((t / (1 + t ^ 2) : ℝ) : ℂ);
     ((t / (1 + t ^ 2) : ℝ) : ℂ), ((t ^ 2 / (1 + t ^ 2) : ℝ) : ℂ)]

private theorem finTwoRankOneProjection_den_ne (t : ℝ) :
    1 + t ^ 2 ≠ 0 := by
  positivity

/-- Every member of the explicit family is a star projection. -/
theorem finTwoRankOneProjection_isStarProjection (t : ℝ) :
    IsStarProjection (finTwoRankOneProjection t) := by
  rw [isStarProjection_iff']
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finTwoRankOneProjection, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [finTwoRankOneProjection_den_ne t]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finTwoRankOneProjection, Matrix.star_apply]

/-- The projection remembers the real parameter: the ratio of entries
`P₀₁/P₀₀` is exactly `t`. -/
theorem finTwoRankOneProjection_injective :
    Function.Injective finTwoRankOneProjection := by
  intro s t h
  have hratio := congrArg
    (fun M : FinTwoComplexMatrix ↦ M 0 1 / M 0 0) h
  have hsden : (1 + (s : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast finTwoRankOneProjection_den_ne s
  have htden : (1 + (t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast finTwoRankOneProjection_den_ne t
  have hst : (s : ℂ) = (t : ℂ) := by
    simpa [finTwoRankOneProjection, hsden, htden] using hratio
  exact_mod_cast hst

/-- At every nontrivial clock phase, the two-level star-projection carrier is
infinite. -/
theorem finTwo_starProjectionPhaseCarrier_infinite
    (θ : AddCircle (1 : ℝ)) (hθ : AddCircle.toCircle θ ≠ 1) :
    (starProjectionPhaseCarrier FinTwoComplexMatrix θ).Infinite := by
  let f : ℝ → FinTwoComplexMatrix := fun t ↦
    starProjectionPhaseOrbit (finTwoRankOneProjection t) θ
  have hphase : (AddCircle.toCircle θ : ℂ) ≠ 1 := by
    intro h
    exact hθ (Subtype.ext h)
  have hf : Function.Injective f := by
    intro s t hst
    apply finTwoRankOneProjection_injective
    exact idempotentPhase_injective_of_ne_one hphase hst
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro x ⟨t, rfl⟩
  exact ⟨⟨finTwoRankOneProjection t,
    finTwoRankOneProjection_isStarProjection t⟩, rfl⟩

/-- The half-period phase is nontrivial. -/
theorem toCircle_half_ne_one :
    AddCircle.toCircle (((1 / 2 : ℝ) : AddCircle (1 : ℝ))) ≠ 1 := by
  intro h
  have hcirc : (((1 / 2 : ℝ) : AddCircle (1 : ℝ))) = 0 :=
    (AddCircle.injective_toCircle one_ne_zero) (by simpa using h)
  have hhalf : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ))
      (by norm_num)).mp hcirc
  norm_num at hhalf

/-- **Unconditional two-level recurrence/complexity separation.** For every
finite endpoint dictionary containing the identity, there is a positive
resolution and a rank-one projector whose unitary one-frequency evolution is
exactly one-periodic yet alternates identity-near, dictionary-hard,
identity-near after every real start.  Each leg is at most one period.

There is no entropy, randomness, genericity, Diophantine, or spectral-rank
premise. -/
theorem finTwoProjectorClock_finiteDictionary_easyHard_alternate
    {C : Set FinTwoComplexMatrix} (hC : C.Finite)
    (hone : (1 : FinTwoComplexMatrix) ∈ C) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∃ p : {p : FinTwoComplexMatrix // IsStarProjection p},
        (∀ s : AddCircle (1 : ℝ),
          starProjectionPhaseOrbit p.1 s ∈ unitary FinTwoComplexMatrix) ∧
        ∀ a : ℝ,
          ∃ tEasy ∈ Set.Icc a (a + 1),
          ∃ tHard ∈ Set.Ioc tEasy (tEasy + 1),
          ∃ tEasy' ∈ Set.Ioc tHard (tHard + 1),
            starProjectionPhaseOrbit p.1
                (tEasy : AddCircle (1 : ℝ)) ∈
              interior (metricClosedBallTarget ε C) ∧
            (∀ c ∈ C,
              (ε : ℝ) < dist
                (starProjectionPhaseOrbit p.1
                  (tHard : AddCircle (1 : ℝ))) c) ∧
            starProjectionPhaseOrbit p.1
                (tEasy' : AddCircle (1 : ℝ)) ∈
              interior (metricClosedBallTarget ε C) := by
  let θ : AddCircle (1 : ℝ) := ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
  have hA : (starProjectionPhaseCarrier FinTwoComplexMatrix θ).Infinite :=
    finTwo_starProjectionPhaseCarrier_infinite θ toCircle_half_ne_one
  have hcover : ∀ x ∈ starProjectionPhaseCarrier FinTwoComplexMatrix θ,
      ∃ p : {p : FinTwoComplexMatrix // IsStarProjection p},
        ∃ z : AddCircle (1 : ℝ), starProjectionPhaseOrbit p.1 z = x := by
    intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact ⟨p, θ, rfl⟩
  obtain ⟨ε, hε, p, hp⟩ :=
    unitPeriodicFamily_infiniteCarrier_finiteDictionary_alternate
      (embed := fun p : {p : FinTwoComplexMatrix // IsStarProjection p} ↦
        starProjectionPhaseOrbit p.1)
      hcover hA hC (1 : FinTwoComplexMatrix) hone
      (fun p ↦ starProjectionPhaseOrbit_zero p.1)
  exact ⟨ε, hε, p,
    fun s ↦ starProjectionPhaseOrbit_mem_unitary p.2 s, hp⟩

/-- Matrix endpoints of all gate words of length at most `s`. -/
def finTwoBoundedCircuitEndpointSet
    {gate : Type*} (generator : gate → unitary FinTwoComplexMatrix)
    (s : ℕ) : Set FinTwoComplexMatrix :=
  (fun w : List gate ↦
    ((circuitWordValue generator w : unitary FinTwoComplexMatrix) :
      FinTwoComplexMatrix)) '' {w | w.length ≤ s}

theorem finTwoBoundedCircuitEndpointSet_finite
    {gate : Type*} [Finite gate]
    (generator : gate → unitary FinTwoComplexMatrix) (s : ℕ) :
    (finTwoBoundedCircuitEndpointSet generator s).Finite := by
  exact (List.finite_length_le gate s).image _

theorem one_mem_finTwoBoundedCircuitEndpointSet
    {gate : Type*} (generator : gate → unitary FinTwoComplexMatrix)
    (s : ℕ) :
    (1 : FinTwoComplexMatrix) ∈
      finTwoBoundedCircuitEndpointSet generator s := by
  refine ⟨[], by simp, ?_⟩
  simp [circuitWordValue]

/-- **Arbitrary-depth periodic circuit hardness.** For every finite gate
alphabet and every requested depth `s`, an explicit two-level projector clock
can be chosen whose exactly one-periodic unitary motion contains an endpoint
separated from every circuit of depth at most `s` by one positive resolution.
That hard endpoint occurs between two identity-near epochs after every start,
with each leg at most one period.

The resolution and selected projection may depend on `s`; no claim of a
uniform positive resolution as `s → ∞` is made. -/
theorem finTwoProjectorClock_arbitraryDepth_easyHard_alternate
    {gate : Type*} [Fintype gate]
    (generator : gate → unitary FinTwoComplexMatrix) (s : ℕ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∃ p : {p : FinTwoComplexMatrix // IsStarProjection p},
        ∀ a : ℝ,
          ∃ tEasy ∈ Set.Icc a (a + 1),
          ∃ tHard ∈ Set.Ioc tEasy (tEasy + 1),
          ∃ tEasy' ∈ Set.Ioc tHard (tHard + 1),
            starProjectionPhaseOrbit p.1
                (tEasy : AddCircle (1 : ℝ)) ∈
              interior (metricClosedBallTarget ε
                (finTwoBoundedCircuitEndpointSet generator s)) ∧
            CircuitWordSeparated generator (ε : ℝ) s
              ⟨starProjectionPhaseOrbit p.1
                  (tHard : AddCircle (1 : ℝ)),
                starProjectionPhaseOrbit_mem_unitary p.2 _⟩ ∧
            starProjectionPhaseOrbit p.1
                (tEasy' : AddCircle (1 : ℝ)) ∈
              interior (metricClosedBallTarget ε
                (finTwoBoundedCircuitEndpointSet generator s)) := by
  let C := finTwoBoundedCircuitEndpointSet generator s
  have hC : C.Finite :=
    finTwoBoundedCircuitEndpointSet_finite generator s
  have hone : (1 : FinTwoComplexMatrix) ∈ C :=
    one_mem_finTwoBoundedCircuitEndpointSet generator s
  obtain ⟨ε, hε, p, _hpunitary, hp⟩ :=
    finTwoProjectorClock_finiteDictionary_easyHard_alternate hC hone
  refine ⟨ε, hε, p, fun a ↦ ?_⟩
  obtain ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
      hEasy, hHard, hEasy'⟩ := hp a
  refine ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy',
    hEasy, ?_, hEasy'⟩
  intro w hw
  have hwC :
      ((circuitWordValue generator w : unitary FinTwoComplexMatrix) :
        FinTwoComplexMatrix) ∈ C := ⟨w, hw, rfl⟩
  have hsep := hHard _ hwC
  simpa only [Subtype.dist_eq, dist_comm] using hsep

end GaloisForLFunctions.HTGeometry
