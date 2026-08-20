import GaloisForLFunctions.HTGeometry.HLSKinematics
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

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

/-- Bosonic creation operators commute. -/
theorem hlsBosonCreate_commute (B : Type u) (F : Type v) [AddCommGroup B] [Module ℂ B]
    [AddCommGroup F] [Module ℂ F] (b c : B) :
    hlsBosonCreate B F b * hlsBosonCreate B F c =
      hlsBosonCreate B F c * hlsBosonCreate B F b := by
  simp only [hlsBosonCreate, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm]

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

/-- Bosonic and fermionic creation commute in the ordinary tensor-product algebra. -/
theorem hlsBosonCreate_commutes_fermionCreate (B : Type u) (F : Type v) [AddCommGroup B]
    [Module ℂ B] [AddCommGroup F] [Module ℂ F] (b : B) (f : F) :
    hlsBosonCreate B F b * hlsFermionCreate B F f =
      hlsFermionCreate B F f * hlsBosonCreate B F b := by
  simp [hlsBosonCreate, hlsFermionCreate]

end GaloisForLFunctions.HTGeometry
