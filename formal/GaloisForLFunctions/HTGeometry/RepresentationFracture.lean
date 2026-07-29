import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic

/-!
# Representation fracture at an involution

This file proves the exact obstruction behind the proposed weak-to-spacetime event transition.
For a complex matrix involution `A`, the matrix

`P = (1 - A) / 2`

is a projection. Its trace is its rank, so

`trace A = n - 2 * rank P`.

Thus the trace of an involution on a fixed finite-dimensional carrier belongs to a finite set.
Continuity over a preconnected parameter space makes that trace constant. Applied to a continuous
family of finite-dimensional representations, the character at any order-two element cannot
change. In particular, a character value `2` cannot continuously become `10` while exact
representation multiplication and the fixed carrier both survive.

No unitarity, diagonalization choice, field equation, or physical interpretation is assumed.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Projection onto the `-1` eigenspace associated with a complex matrix involution. -/
def involutionProjection (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (1 - A)

/-- The half-difference from the identity is idempotent whenever `A² = 1`. -/
theorem involutionProjection_isIdempotent
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    IsIdempotentElem (involutionProjection A) := by
  rw [IsIdempotentElem]
  simp only [involutionProjection, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ = (4 : ℂ)⁻¹ by norm_num]
  have hsq : (1 - A) * (1 - A) = (2 : ℂ) • (1 - A) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hA]
    module
  rw [hsq, smul_smul]
  norm_num

/-- The trace of the involution projection is exactly the dimension of its range. -/
theorem involutionProjection_trace_eq_finrank
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    Matrix.trace (involutionProjection A) =
      (Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') : ℂ) := by
  have hP : IsIdempotentElem (involutionProjection A).toLin' := by
    rw [IsIdempotentElem]
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' (involutionProjection_isIdempotent A hA).eq
  have hproj : LinearMap.IsProj (LinearMap.range (involutionProjection A).toLin')
      (involutionProjection A).toLin' :=
    LinearMap.IsIdempotentElem.isProj_range _ hP
  simpa using hproj.trace

/-- Character formula for an involution: dimension minus twice the `-1` multiplicity. -/
theorem involution_trace_eq_card_sub_two_mul_finrank
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    Matrix.trace A =
      (Fintype.card n : ℂ) -
        2 * (Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') : ℂ) := by
  have htrace := involutionProjection_trace_eq_finrank A hA
  rw [involutionProjection, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one] at htrace
  change (2 : ℂ)⁻¹ • ((Fintype.card n : ℂ) - Matrix.trace A) =
    (Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin') : ℂ) at htrace
  simp only [smul_eq_mul] at htrace
  linear_combination -2 * htrace

/-- Finite set containing every possible character value of an involution on an `n`-carrier. -/
def involutionTraceSpectrum : Set ℂ :=
  Set.range fun k : Fin (Fintype.card n + 1) =>
    (Fintype.card n : ℂ) - 2 * (k : ℕ)

/-- Every complex matrix involution has trace in the finite involution spectrum. -/
theorem involution_trace_mem_spectrum
    (A : Matrix n n ℂ) (hA : A * A = 1) :
    Matrix.trace A ∈ involutionTraceSpectrum (n := n) := by
  let r := Module.finrank ℂ (LinearMap.range (involutionProjection A).toLin')
  have hr_le : r ≤ Fintype.card n := by
    simpa only [r, Module.finrank_pi] using
      Submodule.finrank_le (LinearMap.range (involutionProjection A).toLin')
  refine ⟨⟨r, Nat.lt_succ_iff.mpr hr_le⟩, ?_⟩
  exact (involution_trace_eq_card_sub_two_mul_finrank A hA).symm

omit [DecidableEq n] in
/-- Matrix trace is continuous under entrywise matrix topology. -/
theorem continuous_matrix_trace {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n ℂ} (hA : Continuous A) :
    Continuous fun x => Matrix.trace (A x) := by
  rw [show (fun x => Matrix.trace (A x)) =
    (fun x => ∑ i, A x i i) by rfl]
  exact continuous_finsetSum Finset.univ
    (fun i _ => hA.matrix_elem i i)

/--
The trace of a continuous family of involutions on a fixed finite complex carrier is constant over
every preconnected parameter space.
-/
theorem continuous_involution_trace_constant
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (A : X → Matrix n n ℂ) (hA : Continuous A)
    (hinvolution : ∀ x, A x * A x = 1) (x y : X) :
    Matrix.trace (A x) = Matrix.trace (A y) := by
  let traceLift : X → involutionTraceSpectrum (n := n) :=
    fun z => ⟨Matrix.trace (A z), involution_trace_mem_spectrum (A z) (hinvolution z)⟩
  have htraceLift : Continuous traceLift :=
    (continuous_matrix_trace hA).subtype_mk _
  letI : Finite (involutionTraceSpectrum (n := n)) :=
    Set.Finite.to_subtype (Set.finite_range _)
  have hlift : traceLift x = traceLift y :=
    TotallyDisconnectedSpace.eq_of_continuous traceLift htraceLift x y
  exact congrArg Subtype.val hlift

/--
Representation-fracture theorem: in a continuous family of representations on one fixed
finite-dimensional complex carrier, the character of an order-two element is constant.
-/
theorem continuous_representation_character_constant_at_involution
    {X G : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Monoid G]
    (ρ : X → G →* Matrix n n ℂ) (z : G) (hz : z * z = 1)
    (hρ : Continuous fun x => ρ x z) (x y : X) :
    Matrix.trace (ρ x z) = Matrix.trace (ρ y z) := by
  apply continuous_involution_trace_constant (fun w => ρ w z) hρ
  intro w
  rw [← map_mul, hz, map_one]

/--
Exact endpoint obstruction used by the weak-to-spacetime carrier audit: character `2` cannot
continuously become character `10` while the carrier and representation law remain fixed.
-/
theorem no_continuous_representation_family_trace_two_to_ten
    {X G : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Monoid G]
    (ρ : X → G →* Matrix n n ℂ) (z : G) (hz : z * z = 1)
    (hρ : Continuous fun x => ρ x z) (x y : X)
    (hx : Matrix.trace (ρ x z) = 2)
    (hy : Matrix.trace (ρ y z) = 10) :
    False := by
  have hxy :=
    continuous_representation_character_constant_at_involution ρ z hz hρ x y
  rw [hx, hy] at hxy
  norm_num at hxy

end GaloisForLFunctions.HTGeometry
