import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimitiveCompletedInteraction
import GaloisForLFunctions.RHTower.DirichletLZeroCount
import GaloisForLFunctions.HTGeometry.ReflectionAntiDifferential

/-!
# Global meromorphic matrix landing of the primitive Euler--Wick interaction

The safe-half-plane replica matrix is upgraded to an element of the genuine meromorphic function
field on the whole complex plane.  Its ordered channels are `Xi * C` and `Xi * C⁻¹`, where `C` is
the primitive completed modulo-twelve interaction.  Both `Xi` and `C` enter as actual entire germs;
their nonzeroness in the function field is certified at `s = 2`.

The determinant identity is therefore global in the function field, including through pointwise
zeros of `C`: it is exactly `Xi²`, not a pointwise identity with a totalized inverse.  Critical-line
reflection fixes `Xi` and multiplies the two ordered channels by the primitive root number and its
inverse.  Thus analytic continuation and ordered phase retention are no longer open EWQ steps.
What remains is dimension-preserving descent of this matrix action to the original Xi divisor
module; determinant scalarization still erases the interaction.
-/

open Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open Bottcher

local instance ewqGlobalMeroDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Actual Xi as an entire element of the global analytic ring. -/
def ewqXiGlobalAnalytic : analyticSubring (Set.univ : Set ℂ) :=
  ⟨Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) _root_.RHTower.xi,
    ⟨_root_.RHTower.xi, _root_.RHTower.xi_analyticOnNhd_univ, rfl⟩⟩

/-- Primitive EWQ interaction as an entire element of the global analytic ring. -/
def ewqPrimitiveInteractionGlobalAnalytic : analyticSubring (Set.univ : Set ℂ) :=
  ⟨Germ.coeRingHom (𝓟 (Set.univ : Set ℂ))
      eulerWickQuadraticPrimitiveCompletedInteraction,
    ⟨eulerWickQuadraticPrimitiveCompletedInteraction,
      eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.differentiableOn.analyticOnNhd
        isOpen_univ,
      rfl⟩⟩

@[simp] theorem ewqXiGlobalAnalytic_coe :
    (ewqXiGlobalAnalytic : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) _root_.RHTower.xi := rfl

@[simp] theorem ewqPrimitiveInteractionGlobalAnalytic_coe :
    (ewqPrimitiveInteractionGlobalAnalytic : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ))
        eulerWickQuadraticPrimitiveCompletedInteraction := rfl

theorem quadraticCharacterTwelve_ne_one : quadraticCharacterTwelve ≠ 1 := by
  intro h
  have hp := quadraticCharacterTwelve_isPrimitive
  rw [DirichletCharacter.isPrimitive_def, h,
    DirichletCharacter.conductor_one] at hp
  norm_num at hp

theorem eulerWickQuadraticPrimitiveCompletedInteraction_two_ne_zero :
    eulerWickQuadraticPrimitiveCompletedInteraction 2 ≠ 0 := by
  rw [eulerWickQuadraticPrimitiveCompletedInteraction, _root_.RHTower.dirichletXi]
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
    (_root_.RHTower.completedLFunction_two_ne_zero 11
      ⟨quadraticCharacterTwelve, quadraticCharacterTwelve_ne_one⟩)

theorem ewqXiGlobalAnalytic_ne_zero : ewqXiGlobalAnalytic ≠ 0 := by
  intro h
  have hgerm :
      (Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) _root_.RHTower.xi :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = 0 := congrArg Subtype.val h
  have hev : ∀ᶠ z : ℂ in 𝓟 (Set.univ : Set ℂ),
      _root_.RHTower.xi z = (0 : ℂ → ℂ) z :=
    Filter.Germ.coe_eq.mp (by simpa using hgerm)
  exact _root_.RHTower.xi_two_ne_zero
    (eventually_principal.mp hev 2 (Set.mem_univ 2))

theorem ewqPrimitiveInteractionGlobalAnalytic_ne_zero :
    ewqPrimitiveInteractionGlobalAnalytic ≠ 0 := by
  intro h
  have hgerm :
      (Germ.coeRingHom (𝓟 (Set.univ : Set ℂ))
        eulerWickQuadraticPrimitiveCompletedInteraction :
          Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = 0 := congrArg Subtype.val h
  have hev : ∀ᶠ z : ℂ in 𝓟 (Set.univ : Set ℂ),
      eulerWickQuadraticPrimitiveCompletedInteraction z = (0 : ℂ → ℂ) z :=
    Filter.Germ.coe_eq.mp (by simpa using hgerm)
  exact eulerWickQuadraticPrimitiveCompletedInteraction_two_ne_zero
    (eventually_principal.mp hev 2 (Set.mem_univ 2))

/-- Xi in the genuine global meromorphic function field. -/
def ewqXiGlobalMero : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ) ewqXiGlobalAnalytic

/-- Primitive completed joint interaction in the genuine global meromorphic function field. -/
def ewqPrimitiveInteractionGlobalMero : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    ewqPrimitiveInteractionGlobalAnalytic

theorem ewqXiGlobalMero_ne_zero : ewqXiGlobalMero ≠ 0 := by
  simpa only [ewqXiGlobalMero, map_zero] using
    (IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)).ne
      ewqXiGlobalAnalytic_ne_zero

theorem ewqPrimitiveInteractionGlobalMero_ne_zero :
    ewqPrimitiveInteractionGlobalMero ≠ 0 := by
  simpa only [ewqPrimitiveInteractionGlobalMero, map_zero] using
    (IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)).ne
      ewqPrimitiveInteractionGlobalAnalytic_ne_zero

/-- Constant root number in the global meromorphic field. -/
def ewqRootNumberGlobalMero : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (constToAnalytic Set.univ quadraticCharacterTwelve.rootNumber)

theorem ewqRootNumberGlobalMero_ne_zero : ewqRootNumberGlobalMero ≠ 0 := by
  have hroot := _root_.RHTower.rootNumber_ne_zero quadraticCharacterTwelve_isPrimitive
  have hconst : constToAnalytic (Set.univ : Set ℂ)
      quadraticCharacterTwelve.rootNumber ≠ 0 := by
    intro h
    apply hroot
    simpa using congrArg Subtype.val h
  simpa only [ewqRootNumberGlobalMero, map_zero] using
    (IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)).ne hconst

/-- Critical-line reflection fixes the global Xi element. -/
theorem complexReflectionAnalyticEquiv_one_ewqXiGlobalAnalytic :
    complexReflectionAnalyticEquiv 1 ewqXiGlobalAnalytic = ewqXiGlobalAnalytic := by
  have hmaps : ∀ z ∈ (Set.univ : Set ℂ), complexReflection 1 z ∈ Set.univ :=
    fun z _ => Set.mem_univ z
  have hcomp : (ewqXiGlobalAnalytic : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto
      (complexReflection 1) (tendsto_principal_principal.mpr hmaps) =
        (ewqXiGlobalAnalytic : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := by
    rw [ewqXiGlobalAnalytic_coe]
    change (↑_root_.RHTower.xi : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto
        (complexReflection 1) (tendsto_principal_principal.mpr hmaps) =
      (↑_root_.RHTower.xi : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    rw [Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr fun z _ => by
      simpa [complexReflection] using _root_.RHTower.xi_one_sub z
  simpa only [complexReflectionAnalyticEquiv] using
    (precompAnalyticEquiv_apply_of_invariant
      (analyticOnNhd_complexReflection 1 Set.univ)
      (analyticOnNhd_complexReflection 1 Set.univ)
      hmaps hmaps
      (complexReflection_comp_self 1 Set.univ)
      (complexReflection_comp_self 1 Set.univ) hcomp)

/-- Critical-line reflection retains the primitive interaction with its root-number phase. -/
theorem complexReflectionAnalyticEquiv_one_ewqPrimitiveInteractionGlobalAnalytic :
    complexReflectionAnalyticEquiv 1 ewqPrimitiveInteractionGlobalAnalytic =
      constToAnalytic Set.univ quadraticCharacterTwelve.rootNumber *
        ewqPrimitiveInteractionGlobalAnalytic := by
  have hmaps : ∀ z ∈ (Set.univ : Set ℂ), complexReflection 1 z ∈ Set.univ :=
    fun z _ => Set.mem_univ z
  have hcomp :
      (ewqPrimitiveInteractionGlobalAnalytic : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto
          (complexReflection 1) (tendsto_principal_principal.mpr hmaps) =
        (quadraticCharacterTwelve.rootNumber : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) *
          (ewqPrimitiveInteractionGlobalAnalytic : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := by
    rw [ewqPrimitiveInteractionGlobalAnalytic_coe]
    change (↑eulerWickQuadraticPrimitiveCompletedInteraction :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto
          (complexReflection 1) (tendsto_principal_principal.mpr hmaps) =
      (↑(fun _ : ℂ => quadraticCharacterTwelve.rootNumber) :
          Germ (𝓟 (Set.univ : Set ℂ)) ℂ) *
        (↑eulerWickQuadraticPrimitiveCompletedInteraction :
          Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    rw [Germ.coe_compTendsto, ← Germ.coe_mul, Germ.coe_eq]
    exact eventually_principal.mpr fun z _ => by
      simpa [complexReflection] using
        eulerWickQuadraticPrimitiveCompletedInteraction_one_sub z
  apply Subtype.ext
  have hconst :
      (constToAnalytic Set.univ quadraticCharacterTwelve.rootNumber :
          Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
        (quadraticCharacterTwelve.rootNumber : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := rfl
  rw [MulMemClass.coe_mul, hconst]
  simpa only [complexReflectionAnalyticEquiv] using
    (precompAnalyticEquiv_apply_of_scale
      (analyticOnNhd_complexReflection 1 Set.univ)
      (analyticOnNhd_complexReflection 1 Set.univ)
      hmaps hmaps
      (complexReflection_comp_self 1 Set.univ)
      (complexReflection_comp_self 1 Set.univ) hcomp)

theorem complexReflectionMeroEquiv_one_ewqXiGlobalMero :
    complexReflectionMeroEquiv 1 ewqXiGlobalMero = ewqXiGlobalMero := by
  rw [ewqXiGlobalMero, complexReflectionMeroEquiv_algebraMap,
    complexReflectionAnalyticEquiv_one_ewqXiGlobalAnalytic]

theorem complexReflectionMeroEquiv_one_ewqPrimitiveInteractionGlobalMero :
    complexReflectionMeroEquiv 1 ewqPrimitiveInteractionGlobalMero =
      ewqRootNumberGlobalMero * ewqPrimitiveInteractionGlobalMero := by
  rw [ewqPrimitiveInteractionGlobalMero, complexReflectionMeroEquiv_algebraMap,
    complexReflectionAnalyticEquiv_one_ewqPrimitiveInteractionGlobalAnalytic, map_mul]
  rfl

/-- Ordered global meromorphic Pauli eigenchannels. -/
def eulerWickReplicaGlobalCompletedEigenMatrix :
    Matrix (Fin 2) (Fin 2) (meroField (Set.univ : Set ℂ)) :=
  Matrix.diagonal ![
    ewqXiGlobalMero * ewqPrimitiveInteractionGlobalMero,
    ewqXiGlobalMero * ewqPrimitiveInteractionGlobalMero⁻¹]

theorem eulerWickReplicaGlobalCompletedEigenMatrix_apply_zero_zero :
    eulerWickReplicaGlobalCompletedEigenMatrix 0 0 =
      ewqXiGlobalMero * ewqPrimitiveInteractionGlobalMero := by
  simp [eulerWickReplicaGlobalCompletedEigenMatrix]

theorem eulerWickReplicaGlobalCompletedEigenMatrix_apply_one_one :
    eulerWickReplicaGlobalCompletedEigenMatrix 1 1 =
      ewqXiGlobalMero * ewqPrimitiveInteractionGlobalMero⁻¹ := by
  simp [eulerWickReplicaGlobalCompletedEigenMatrix]

/-- Reflection retains the ordered positive Pauli channel with the primitive root-number phase. -/
theorem complexReflectionMeroEquiv_one_globalEigenMatrix_zero_zero :
    complexReflectionMeroEquiv 1
        (eulerWickReplicaGlobalCompletedEigenMatrix 0 0) =
      ewqRootNumberGlobalMero *
        eulerWickReplicaGlobalCompletedEigenMatrix 0 0 := by
  rw [eulerWickReplicaGlobalCompletedEigenMatrix_apply_zero_zero, map_mul,
    complexReflectionMeroEquiv_one_ewqXiGlobalMero,
    complexReflectionMeroEquiv_one_ewqPrimitiveInteractionGlobalMero]
  ring

/-- Reflection retains the opposite Pauli channel with the inverse root-number phase. -/
theorem complexReflectionMeroEquiv_one_globalEigenMatrix_one_one :
    complexReflectionMeroEquiv 1
        (eulerWickReplicaGlobalCompletedEigenMatrix 1 1) =
      ewqRootNumberGlobalMero⁻¹ *
        eulerWickReplicaGlobalCompletedEigenMatrix 1 1 := by
  rw [eulerWickReplicaGlobalCompletedEigenMatrix_apply_one_one, map_mul, map_inv₀,
    complexReflectionMeroEquiv_one_ewqXiGlobalMero,
    complexReflectionMeroEquiv_one_ewqPrimitiveInteractionGlobalMero]
  field_simp [ewqRootNumberGlobalMero_ne_zero,
    ewqPrimitiveInteractionGlobalMero_ne_zero]

/-- Exact determinant identity in the global meromorphic field. -/
theorem det_eulerWickReplicaGlobalCompletedEigenMatrix :
    eulerWickReplicaGlobalCompletedEigenMatrix.det = ewqXiGlobalMero ^ (2 : ℕ) := by
  rw [eulerWickReplicaGlobalCompletedEigenMatrix, Matrix.det_diagonal,
    Fin.prod_univ_two]
  calc
    (ewqXiGlobalMero * ewqPrimitiveInteractionGlobalMero) *
        (ewqXiGlobalMero * ewqPrimitiveInteractionGlobalMero⁻¹) =
        ewqXiGlobalMero ^ (2 : ℕ) *
          (ewqPrimitiveInteractionGlobalMero * ewqPrimitiveInteractionGlobalMero⁻¹) := by ring
    _ = ewqXiGlobalMero ^ (2 : ℕ) := by
      rw [mul_inv_cancel₀ ewqPrimitiveInteractionGlobalMero_ne_zero, mul_one]

end GaloisForLFunctions.RHTower
