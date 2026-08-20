import GaloisForLFunctions.HTGeometry.HLSKinematics
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Algebraic boson--fermion Fock space for HLS systems

`HLSAlgebraicFock B F` is the algebraic Fock space
`SymmetricAlgebra ℂ B ⊗ ExteriorAlgebra ℂ F`.  It supplies exact Bose/Fermi
statistics and fermion parity before any Hilbert completion, topology, or
unbounded-operator analysis is introduced.

This is an algebraic precursor to, not a replacement for, physical Fock space.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Algebraic boson--fermion Fock space: symmetric bosonic creation tensored with exterior
fermionic creation. -/
abbrev HLSAlgebraicFock (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] :=
  SymmetricAlgebra ℂ B ⊗[ℂ] ExteriorAlgebra ℂ F

/-- Bosonic one-particle creation in the algebraic Fock space. -/
def hlsBosonCreate (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (b : B) : HLSAlgebraicFock B F :=
  SymmetricAlgebra.ι ℂ B b ⊗ₜ[ℂ] (1 : ExteriorAlgebra ℂ F)

/-- Fermionic one-particle creation in the algebraic Fock space. -/
def hlsFermionCreate (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (f : F) : HLSAlgebraicFock B F :=
  (1 : SymmetricAlgebra ℂ B) ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ f

/-- Parity of the exterior factor, induced by negating every fermionic one-particle vector. -/
def hlsExteriorParity (F : Type v) [AddCommGroup F] [Module ℂ F] :
    ExteriorAlgebra ℂ F →ₐ[ℂ] ExteriorAlgebra ℂ F :=
  ExteriorAlgebra.map (-LinearMap.id)

/-- Fermion parity on the full algebraic Fock space: identity on the symmetric bosonic factor
and exterior parity on the fermionic factor. -/
def hlsFockParity (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] : HLSAlgebraicFock B F →ₗ[ℂ] HLSAlgebraicFock B F :=
  TensorProduct.map LinearMap.id (hlsExteriorParity F).toLinearMap

/-- Fermion parity negates every one-fermion creation operator. -/
theorem hlsExteriorParity_apply_ι (F : Type v) [AddCommGroup F] [Module ℂ F] (f : F) :
    hlsExteriorParity F (ExteriorAlgebra.ι ℂ f) = -ExteriorAlgebra.ι ℂ f := by
  simp [hlsExteriorParity]

/-- Fermion parity is an involution. -/
theorem hlsExteriorParity_squared (F : Type v) [AddCommGroup F] [Module ℂ F] :
    (hlsExteriorParity F).comp (hlsExteriorParity F) =
      AlgHom.id ℂ (ExteriorAlgebra ℂ F) := by
  simp only [hlsExteriorParity, ExteriorAlgebra.map_comp_map]
  simp

/-- Full algebraic Fock parity is an involution. -/
theorem hlsFockParity_squared (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] :
    (hlsFockParity B F).comp (hlsFockParity B F) = LinearMap.id := by
  ext b f
  change TensorProduct.map LinearMap.id (hlsExteriorParity F).toLinearMap
    (TensorProduct.map LinearMap.id (hlsExteriorParity F).toLinearMap (b ⊗ₜ[ℂ] f)) = b ⊗ₜ[ℂ] f
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  change b ⊗ₜ[ℂ] hlsExteriorParity F (hlsExteriorParity F f) = b ⊗ₜ[ℂ] f
  have h := congrArg (fun q : ExteriorAlgebra ℂ F →ₐ[ℂ] ExteriorAlgebra ℂ F => q f)
    (hlsExteriorParity_squared F)
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using congrArg (TensorProduct.tmul ℂ b) h

/-- Fermion parity is a genuine algebraic Fock-space linear equivalence, equal to its own inverse. -/
def hlsFockParityEquiv (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] : HLSAlgebraicFock B F ≃ₗ[ℂ] HLSAlgebraicFock B F :=
  { hlsFockParity B F with
    invFun := hlsFockParity B F
    left_inv := by
      intro x
      exact LinearMap.congr_fun (hlsFockParity_squared B F) x
    right_inv := by
      intro x
      exact LinearMap.congr_fun (hlsFockParity_squared B F) x }

/-- Algebraic Fock parity remains involutive when used as a linear equivalence. -/
theorem hlsFockParityEquiv_apply_twice (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (x : HLSAlgebraicFock B F) :
    hlsFockParityEquiv B F (hlsFockParityEquiv B F x) = x :=
  LinearMap.congr_fun (hlsFockParity_squared B F) x

/-- Bosonic creation operators commute. -/
theorem hlsBosonCreate_commute (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (b c : B) :
    hlsBosonCreate B F b * hlsBosonCreate B F c =
      hlsBosonCreate B F c * hlsBosonCreate B F b := by
  simp only [hlsBosonCreate, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm]

/-- Full Fock parity fixes bosonic creation. -/
theorem hlsFockParity_apply_bosonCreate (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (b : B) :
    hlsFockParity B F (hlsBosonCreate B F b) = hlsBosonCreate B F b := by
  simp [hlsFockParity, hlsBosonCreate, hlsExteriorParity]

/-- Fermionic creation squares to zero. -/
theorem hlsFermionCreate_sq_zero (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (f : F) :
    hlsFermionCreate B F f * hlsFermionCreate B F f = 0 := by
  simp [hlsFermionCreate]

/-- Fermionic creation operators anticommute. -/
theorem hlsFermionCreate_anticommute (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (f g : F) :
    hlsFermionCreate B F f * hlsFermionCreate B F g +
      hlsFermionCreate B F g * hlsFermionCreate B F f = 0 := by
  simp only [hlsFermionCreate, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.tmul_add]
  simp [ExteriorAlgebra.ι_add_mul_swap]

/-- Full Fock parity negates fermionic creation. -/
theorem hlsFockParity_apply_fermionCreate (B : Type u) (F : Type v) [AddCommGroup B]
    [Module ℂ B] [AddCommGroup F] [Module ℂ F] (f : F) :
    hlsFockParity B F (hlsFermionCreate B F f) = -hlsFermionCreate B F f := by
  simp [hlsFockParity, hlsFermionCreate, hlsExteriorParity_apply_ι]
  rw [TensorProduct.tmul_neg]

/-- Bosonic and fermionic creation commute in the ordinary tensor-product algebra. -/
theorem hlsBosonCreate_commutes_fermionCreate (B : Type u) (F : Type v) [AddCommGroup B]
    [Module ℂ B] [AddCommGroup F] [Module ℂ F] (b : B) (f : F) :
    hlsBosonCreate B F b * hlsFermionCreate B F f =
      hlsFermionCreate B F f * hlsBosonCreate B F b := by
  simp [hlsBosonCreate, hlsFermionCreate]

end GaloisForLFunctions.HTGeometry
