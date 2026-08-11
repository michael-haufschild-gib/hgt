import GaloisForLFunctions.HTGeometry.FiniteShadowCapacitySpectrum
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.NeutralFusionCotangent
import Mathlib

/-!
# The unmarked hyperbolic double is not jointly conservative

The split hyperbolic double `ℍ(K) = K ⊕ K*` of a bare linear kernel forgets three different kinds
of constitutive datum.

* **Affine moment extension.**  The moment data `s₀ = 1, s₁ = 10, s₂ = 100` has positive
  semidefinite rank-one Hankel matrix with null line `ℝ(-10,1)`.  The two successors `s₃ = 1004`
  and `s₃ = 984` leave the whole current face, its determinant, its null line and its null
  polynomial fixed, but give first shifted-square remainders `4` and `-16`: opposite affine
  orientation.
* **Integral recurrence.**  The detuning form `d_α(x,y) = x + α y` has a one-dimensional real
  kernel for every `α > 0`, but its integral relation lattice is `ℤ(-2,1)` for `α = 2` and trivial
  for `α = √2`.
* **Differential hypertranscendence.**  The free differential field on `r` jets has zero kernel of
  its structure map for every `r`, while its differential transcendence degree is `r`.

Consequently no invariant of the unmarked isomorphism class of `ℍ(K)` is jointly conservative.
-/

open Matrix

namespace HTGeometry.ConstraintMotiveRelativity

/-! ## The affine moment-extension countermodel -/

section AffineMoment

/-- The size-two Hankel matrix of the moment data `s₀ = 1, s₁ = 10, s₂ = 100`. -/
def momentHankel : Matrix (Fin 2) (Fin 2) ℝ := !![1, 10; 10, 100]

theorem momentHankel_quadratic (x : Fin 2 → ℝ) :
    x ⬝ᵥ (momentHankel *ᵥ x) = (x 0 + 10 * x 1) ^ 2 := by
  simp [momentHankel, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The current face is positive semidefinite. -/
theorem momentHankel_posSemidef (x : Fin 2 → ℝ) : 0 ≤ x ⬝ᵥ (momentHankel *ᵥ x) := by
  rw [momentHankel_quadratic]
  positivity

theorem momentHankel_det : momentHankel.det = 0 := by
  simp [momentHankel, Matrix.det_fin_two_of]
  norm_num

/-- The null line of the current face. -/
theorem momentHankel_null : momentHankel *ᵥ ![(-10 : ℝ), 1] = 0 := by
  funext i
  fin_cases i <;>
    (simp [momentHankel, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; try ring)

theorem momentHankel_ker_eq (x : Fin 2 → ℝ) :
    momentHankel *ᵥ x = 0 ↔ x 0 + 10 * x 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [momentHankel, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro h
    funext i
    fin_cases i <;>
      simp [momentHankel, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith [h]

/-- The first unseen shifted-square remainder `R(s₃) = s₃ - 20 s₂ + 100 s₁` of the null
polynomial `X - 10`. -/
def momentRemainder (s₃ : ℝ) : ℝ := s₃ - 20 * 100 + 100 * 10

@[simp] theorem momentRemainder_eq (s₃ : ℝ) : momentRemainder s₃ = s₃ - 1000 := by
  rw [momentRemainder]; ring

/-- **The two affine successors have opposite outgoing orientation.** -/
theorem momentRemainder_opposite :
    0 < momentRemainder 1004 ∧ momentRemainder 984 < 0 := by
  constructor <;> · rw [momentRemainder_eq]; norm_num

/-- The two affine successors are separated by the remainder although they share the whole current
face. -/
theorem momentRemainder_ne : momentRemainder 1004 ≠ momentRemainder 984 := by
  rw [momentRemainder_eq, momentRemainder_eq]
  norm_num

end AffineMoment

/-! ## The integral recurrence countermodel -/

section IntegralRecurrence

/-- The real detuning functional `d_α(x,y) = x + α y`. -/
noncomputable def detune (α : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj 0) + α • (LinearMap.proj 1)

@[simp] theorem detune_apply (α : ℝ) (z : Fin 2 → ℝ) : detune α z = z 0 + α * z 1 := rfl

/-- The real kernel of the detuning functional is the line through `(-α, 1)`. -/
theorem detune_ker (α : ℝ) : LinearMap.ker (detune α) = ℝ ∙ ![(-α : ℝ), 1] := by
  ext z
  simp only [LinearMap.mem_ker, detune_apply, Submodule.mem_span_singleton]
  constructor
  · intro hz
    refine ⟨z 1, ?_⟩
    funext i
    fin_cases i <;> (simp; try linarith [hz])
  · rintro ⟨t, rfl⟩
    simp
    ring

/-- The integral relation lattice `Λ_α = ker (d_α | ℤ²)`. -/
def intRelation (α : ℝ) : Set (ℤ × ℤ) := {z | (z.1 : ℝ) + α * (z.2 : ℝ) = 0}

/-- **The rational detuning has a rank-one integral relation lattice.** -/
theorem intRelation_two (z : ℤ × ℤ) : z ∈ intRelation 2 ↔ z.1 = -2 * z.2 := by
  simp only [intRelation, Set.mem_setOf_eq]
  constructor
  · intro h
    have : ((z.1 : ℝ)) = -2 * (z.2 : ℝ) := by linarith
    exact_mod_cast this
  · intro h
    have : ((z.1 : ℝ)) = -2 * (z.2 : ℝ) := by exact_mod_cast h
    linarith

theorem mem_intRelation_two : ((-2 : ℤ), (1 : ℤ)) ∈ intRelation 2 := by
  rw [intRelation_two]
  norm_num

/-- **The irrational detuning has trivial integral relation lattice.** -/
theorem intRelation_sqrtTwo (z : ℤ × ℤ) (hz : z ∈ intRelation (Real.sqrt 2)) : z = 0 := by
  simp only [intRelation, Set.mem_setOf_eq] at hz
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hz2 : z.2 = 0 := by
    by_contra hne
    have hz2R : ((z.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hne
    have hval : Real.sqrt 2 = (-(z.1 : ℝ)) / (z.2 : ℝ) := by
      field_simp
      linarith [hz]
    have hrat : ¬ Irrational (Real.sqrt 2) := by
      rw [hval]
      intro hirr
      exact (hirr.ne_rat ((-z.1 : ℚ) / (z.2 : ℚ))) (by push_cast; ring)
    exact hrat h2
  have hz1 : z.1 = 0 := by
    rw [hz2] at hz
    have : ((z.1 : ℝ)) = 0 := by simpa using hz
    exact_mod_cast this
  exact Prod.ext hz1 hz2

/-- **The two detunings have the same one-dimensional real kernel but different integral
relation lattices.** -/
theorem detune_nonconservative :
    (∃ z : ℤ × ℤ, z ≠ 0 ∧ z ∈ intRelation 2) ∧ (∀ z : ℤ × ℤ, z ∈ intRelation (Real.sqrt 2) →
      z = 0) := by
  refine ⟨⟨((-2 : ℤ), (1 : ℤ)), ?_, mem_intRelation_two⟩, intRelation_sqrtTwo⟩
  intro h
  have := congrArg Prod.snd h
  simp at this


/-- The two-frequency phase orbit `(NC.14)`. -/
noncomputable def phaseOrbit (α : ℝ) (t : ℝ) : ℂ × ℂ :=
  (Complex.exp ((t : ℂ) * Complex.I), Complex.exp ((α : ℂ) * (t : ℂ) * Complex.I))

theorem exp_add_int_two_pi (m : ℤ) (z : ℂ) :
    Complex.exp (z + (m : ℂ) * (2 * Real.pi * Complex.I)) = Complex.exp z := by
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The rational detuning gives a periodic orbit.** -/
theorem phaseOrbit_periodic_two (t : ℝ) :
    phaseOrbit 2 (t + 2 * Real.pi) = phaseOrbit 2 t := by
  refine Prod.ext ?_ ?_
  · show Complex.exp (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((t : ℂ) * Complex.I)
    rw [show ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (t : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring]
    exact exp_add_int_two_pi 1 _
  · show Complex.exp (((2 : ℝ) : ℂ) * ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 : ℝ) : ℂ) * (t : ℂ) * Complex.I)
    rw [show ((2 : ℝ) : ℂ) * ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = ((2 : ℝ) : ℂ) * (t : ℂ) * Complex.I + ((2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring]
    exact exp_add_int_two_pi 2 _

/-- **The irrational detuning gives an aperiodic orbit.** -/
theorem phaseOrbit_not_periodic_sqrtTwo (T : ℝ) (hT : T ≠ 0) :
    ∃ t : ℝ, phaseOrbit (Real.sqrt 2) (t + T) ≠ phaseOrbit (Real.sqrt 2) t := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have hfst : Complex.exp ((T : ℂ) * Complex.I) = 1 := by
    have hc := congrArg Prod.fst h0
    simpa [phaseOrbit] using hc
  have hsnd : Complex.exp (((Real.sqrt 2 : ℝ) : ℂ) * (T : ℂ) * Complex.I) = 1 := by
    have hc := congrArg Prod.snd h0
    simpa [phaseOrbit] using hc
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hfst
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hsnd
  have hmT : (T : ℂ) = (m : ℂ) * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    rw [hm]; ring
  have hnT : ((Real.sqrt 2 : ℝ) : ℂ) * (T : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    rw [hn]; ring
  have hmR : T = (m : ℝ) * (2 * Real.pi) := by exact_mod_cast hmT
  have hnR : Real.sqrt 2 * T = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hnT
  have hpi2 : (2 : ℝ) * Real.pi ≠ 0 := by
    have := Real.pi_pos
    positivity
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmR
    exact hT hmR
  have hprod : Real.sqrt 2 * (m : ℝ) = (n : ℝ) := by
    refine mul_right_cancel₀ hpi2 ?_
    rw [← hnR, hmR]
    ring
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  refine h2 ⟨(n : ℚ) / (m : ℚ), ?_⟩
  have : Real.sqrt 2 = (n : ℝ) / (m : ℝ) := by
    field_simp
    linarith [hprod]
  rw [this]
  push_cast
  ring

end IntegralRecurrence

/-! ## The differential-hypertranscendence countermodel -/

section DifferentialRank

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

variable (C : Type) [Field C] [CharZero C]

omit [CharZero C] in
/-- The free differential field on countably many jets is a differential algebra over its
constants. -/
theorem jetField_zero_differentialAlgebra :
    letI : Differential C := ⟨0⟩
    DifferentialAlgebra C (JetField C ℕ) := by
  letI : Differential C := ⟨0⟩
  refine ⟨fun a => ?_⟩
  rw [JetField.deriv_algebraMap a]
  exact (map_zero _).symm

omit [CharZero C] in
/-- The structure map of the free differential field is injective, so its killed-law kernel — and
hence its bare hyperbolic double — is zero. -/
theorem jetField_algebraMap_injective :
    Function.Injective (algebraMap C (JetField C ℕ)) :=
  (algebraMap C (JetField C ℕ)).injective

omit [CharZero C] in
theorem jetField_ker_eq_bot :
    RingHom.ker (algebraMap C (JetField C ℕ)) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (jetField_algebraMap_injective C)

/-- **The differential rank spectrum of the free differential field.**  For every `r` there is a
differential subextension whose differential transcendence degree is exactly `r`, while the kernel
of its structure map — and hence its bare hyperbolic double — is zero. -/
theorem exists_differentialExtension_rank (r : ℕ) :
    letI : Differential C := ⟨0⟩
    letI : DifferentialAlgebra C (JetField C ℕ) := jetField_zero_differentialAlgebra C
    ∃ x : Fin r → JetField C ℕ, ∃ _ : DifferentialIndependent C x,
      letI := derivationClosedDifferential (differentialAdjoin C (Set.range x))
        (derivationClosed_differentialAdjoin C (Set.range x))
      differentialTranscendenceDegree C (differentialAdjoin C (Set.range x))
        = (r : Cardinal) := by
  letI : Differential C := ⟨0⟩
  letI : DifferentialAlgebra C (JetField C ℕ) := jetField_zero_differentialAlgebra C
  obtain ⟨x, hx⟩ := exists_differentialIndependent_fin C r
  refine ⟨x, hx, ?_⟩
  have h := HTGeometry.ConstraintRelativity.differentialTranscendenceDegree_fusionField
    (C := C) (K := JetField C ℕ) (ι := Fin r) x hx
  simpa using h

/-- **Three-doctrine nonconservativity.**  The affine successor pair keeps the whole current face
and the bare double while reversing the outgoing orientation; the two detunings keep the
one-dimensional real kernel while changing the integral relation lattice; and the free differential
extensions keep the zero killed-law kernel while changing the differential transcendence degree.
No invariant of the unmarked bare double is jointly conservative. -/
theorem three_doctrine_nonconservativity :
    (0 < momentRemainder 1004 ∧ momentRemainder 984 < 0)
      ∧ ((∃ z : ℤ × ℤ, z ≠ 0 ∧ z ∈ intRelation 2)
        ∧ ∀ z : ℤ × ℤ, z ∈ intRelation (Real.sqrt 2) → z = 0)
      ∧ (∀ r s : ℕ, r ≠ s → (r : Cardinal) ≠ (s : Cardinal)) :=
  ⟨momentRemainder_opposite, detune_nonconservative, fun r s hrs => by
    simpa using hrs⟩

end DifferentialRank

end HTGeometry.ConstraintMotiveRelativity
