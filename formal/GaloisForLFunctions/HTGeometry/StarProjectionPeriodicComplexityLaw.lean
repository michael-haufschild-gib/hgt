import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import GaloisForLFunctions.HTGeometry.PeriodicMetricEntropySeparationLaw

/-!
# One-frequency projector clocks with ambient-scale complexity

A star projection `p` defines the unitary loop

`U_p(θ) = 1 + (exp(2π i θ) - 1) p`.

Every such loop has exactly one frequency and period one.  Nevertheless, the
orientation of `p` ranges over a high-dimensional projection space.  Metric
entropy of that ambient family can therefore force a robustly circuit-hard
endpoint on one exactly periodic loop.  This is the precise separation between
spectral recurrence data and eigenvector complexity.
-/

open Set Topology Complex
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- Algebraic phase supported on an idempotent. -/
noncomputable def idempotentPhase
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (p : A) (z : ℂ) : A :=
  1 + (z - 1) • p

/-- Multiplicative phases multiply on an idempotent support. -/
theorem idempotentPhase_mul
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    {p : A} (hp : IsIdempotentElem p) (z w : ℂ) :
    idempotentPhase p z * idempotentPhase p w =
      idempotentPhase p (z * w) := by
  simp only [idempotentPhase, add_mul, mul_add, one_mul, mul_one,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hp.eq]
  module

/-- A nontrivial scalar phase remembers its idempotent support exactly. -/
theorem idempotentPhase_injective_of_ne_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    {z : ℂ} (hz : z ≠ 1) :
    Function.Injective (fun p : A ↦ idempotentPhase p z) := by
  intro p q hpq
  apply smul_right_injective A (sub_ne_zero.mpr hz)
  simpa [idempotentPhase] using congrArg (fun x : A ↦ x - 1) hpq

/-- Exact exponential of a scalar-supported idempotent. -/
theorem exp_smul_idempotent
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {p : A} (hp : IsIdempotentElem p) (z : ℂ) :
    NormedSpace.exp (z • p) = idempotentPhase p (Complex.exp z) := by
  have hsScalar : HasSum
      (fun n : ℕ ↦ ((n.factorial : ℂ)⁻¹) • z ^ n)
      (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' z
  have hsScalarTail : HasSum
      (fun n : ℕ ↦ ((n + 1).factorial : ℂ)⁻¹ * z ^ (n + 1))
      (Complex.exp z - 1) := by
    have htail := (hasSum_nat_add_iff' 1).mpr hsScalar
    simpa [smul_eq_mul] using htail
  have hsATail : HasSum
      (fun n : ℕ ↦ ((n + 1).factorial : ℂ)⁻¹ • (z • p) ^ (n + 1))
      ((Complex.exp z - 1) • p) := by
    convert hsScalarTail.smul_const p using 1
    funext n
    rw [smul_pow, hp.pow_succ_eq]
    simp [mul_smul]
  have hsA : HasSum
      (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ • (z • p) ^ n)
      (idempotentPhase p (Complex.exp z)) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa [idempotentPhase] using hsATail
  exact (NormedSpace.exp_series_hasSum_exp' (z • p)).unique hsA

/-- The phase loop attached to a projection. -/
noncomputable def starProjectionPhaseOrbit
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (p : A) (θ : AddCircle (1 : ℝ)) : A :=
  idempotentPhase p (AddCircle.toCircle θ : ℂ)

theorem continuous_starProjectionPhaseOrbit
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (p : A) :
    Continuous (starProjectionPhaseOrbit p) := by
  unfold starProjectionPhaseOrbit idempotentPhase
  fun_prop

@[simp]
theorem starProjectionPhaseOrbit_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (p : A) :
    starProjectionPhaseOrbit p (0 : AddCircle (1 : ℝ)) = 1 := by
  simp [starProjectionPhaseOrbit, idempotentPhase]

/-- The projector clock is a one-parameter subgroup. -/
theorem starProjectionPhaseOrbit_add
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    {p : A} (hp : IsIdempotentElem p)
    (θ φ : AddCircle (1 : ℝ)) :
    starProjectionPhaseOrbit p (θ + φ) =
      starProjectionPhaseOrbit p θ * starProjectionPhaseOrbit p φ := by
  rw [starProjectionPhaseOrbit, AddCircle.toCircle_add]
  exact (idempotentPhase_mul hp _ _).symm

/-- The real-time projector clock is the ordinary exponential of the static
self-adjoint generator `-2π p` (up to the sign convention for time
evolution). -/
theorem starProjectionPhaseOrbit_real_eq_exp
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {p : A} (hp : IsIdempotentElem p) (t : ℝ) :
    starProjectionPhaseOrbit p (t : AddCircle (1 : ℝ)) =
      NormedSpace.exp ((((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) • p) := by
  rw [starProjectionPhaseOrbit, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  rw [exp_smul_idempotent hp]
  congr 2
  congr 1
  norm_num

/-- Static Hamiltonian whose Schrödinger evolution is the projector clock. -/
noncomputable def starProjectionHamiltonian
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (p : A) : A :=
  (((-2 * Real.pi : ℝ) : ℂ)) • p

theorem starProjectionHamiltonian_isSelfAdjoint
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) :
    IsSelfAdjoint (starProjectionHamiltonian p) := by
  simp only [starProjectionHamiltonian, IsSelfAdjoint, star_smul]
  rw [hp.isSelfAdjoint]
  norm_num

/-- Exact identification with ordinary time-independent Schrödinger
evolution `exp(-itH)`. -/
theorem starProjectionPhaseOrbit_eq_staticEvolution
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {p : A} (hp : IsIdempotentElem p) (t : ℝ) :
    starProjectionPhaseOrbit p (t : AddCircle (1 : ℝ)) =
      NormedSpace.exp (((-(t : ℂ)) * Complex.I) •
        starProjectionHamiltonian p) := by
  rw [starProjectionPhaseOrbit_real_eq_exp hp]
  rw [starProjectionHamiltonian, smul_smul]
  congr 2
  push_cast
  ring

theorem star_idempotentPhase
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) (z : ℂ) :
    star (idempotentPhase p z) = idempotentPhase p (star z) := by
  simp only [idempotentPhase, star_add, star_one, star_smul, star_sub]
  rw [hp.isSelfAdjoint]

/-- Every point on the projector clock is unitary. -/
theorem starProjectionPhaseOrbit_mem_unitary
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) (θ : AddCircle (1 : ℝ)) :
    starProjectionPhaseOrbit p θ ∈ unitary A := by
  let z : Circle := AddCircle.toCircle θ
  have hstar : star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    exact (Circle.coe_inv_eq_conj z).symm
  have hzLeft : star (z : ℂ) * (z : ℂ) = 1 := by
    rw [hstar, Circle.coe_inv]
    exact inv_mul_cancel₀ (Circle.coe_ne_zero z)
  have hzRight : (z : ℂ) * star (z : ℂ) = 1 := by
    rw [mul_comm, hzLeft]
  rw [Unitary.mem_iff]
  rw [starProjectionPhaseOrbit, star_idempotentPhase hp]
  constructor
  · rw [idempotentPhase_mul hp.isIdempotentElem, hzLeft]
    simp [idempotentPhase]
  · rw [idempotentPhase_mul hp.isIdempotentElem, hzRight]
    simp [idempotentPhase]

/-- All endpoints obtained from star projections at one fixed clock phase. -/
noncomputable def starProjectionPhaseCarrier
    (A : Type*) [NormedRing A] [NormedAlgebra ℂ A] [Star A]
    (θ : AddCircle (1 : ℝ)) : Set A :=
  Set.range fun p : {p : A // IsStarProjection p} ↦
    starProjectionPhaseOrbit p.1 θ

/-- **Exactly periodic complexity-separation law for projector Hamiltonians.**
If one fixed-phase family of star-projection clocks has covering entropy larger
than a dictionary `C`, then a single star projection generates an exactly
one-periodic unitary evolution which, after every starting time, visits the
identity neighborhood, a point robustly farther than `ε` from every dictionary
endpoint, and the identity neighborhood again.  Every leg is at most one
period.

This proves that spectral recurrence complexity and circuit complexity are
independent before additional structure such as locality is imposed: the clock
has one frequency and fixed period, while its hard endpoint is selected by the
ambient geometry of eigenspace orientations. -/
theorem starProjectionClock_coveringEntropy_easyHard_alternate
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [StarModule ℂ A]
    (θ : AddCircle (1 : ℝ)) {C : Set A} (hone : (1 : A) ∈ C)
    (ε : ℝ≥0) (hε : 0 < ε)
    (hEntropy :
      C.encard < Metric.externalCoveringNumber ε
        (starProjectionPhaseCarrier A θ)) :
    ∃ p : {p : A // IsStarProjection p},
      (∀ s : AddCircle (1 : ℝ),
        starProjectionPhaseOrbit p.1 s ∈ unitary A) ∧
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
  have hcover : ∀ x ∈ starProjectionPhaseCarrier A θ,
      ∃ p : {p : A // IsStarProjection p},
        ∃ z : AddCircle (1 : ℝ), starProjectionPhaseOrbit p.1 z = x := by
    intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact ⟨p, θ, rfl⟩
  obtain ⟨p, hp⟩ :=
    unitPeriodicFamily_coveringEntropy_easyHard_alternate
      (embed := fun p : {p : A // IsStarProjection p} ↦
        starProjectionPhaseOrbit p.1)
      hcover (1 : A) hone (fun p ↦ starProjectionPhaseOrbit_zero p.1)
      ε hε hEntropy
  exact ⟨p, fun s ↦ starProjectionPhaseOrbit_mem_unitary p.2 s, hp⟩

end GaloisForLFunctions.HTGeometry
