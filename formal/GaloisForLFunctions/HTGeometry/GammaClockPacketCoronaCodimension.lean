import GaloisForLFunctions.HTGeometry.GammaClockCoronaConormal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Gamma-clock packet corona codimension

One Gamma clock has exactly one conormal line after quotienting by finite observation windows.
A finite packet of independent prime-normal directions therefore has one corona conormal line per
direction.  This file proves the exact packet statement: the kernel rank of the componentwise
Gamma constraint is the packet cardinality.

This identifies support cardinality with an intrinsic finite-blind normal codimension.  It is
independent of any divisor and applies before analytic completion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K]

/-- Componentwise Gamma-corona constraint on a packet of normal directions. -/
def packetStreamCoronaConstraint (S : Type*) :
    (S → StreamCorona K) →ₗ[K] (S → StreamCorona K) where
  toFun x s := streamCoronaConstraint K (x s)
  map_add' x y := by
    funext s
    exact map_add (streamCoronaConstraint K) (x s) (y s)
  map_smul' a x := by
    funext s
    exact map_smul (streamCoronaConstraint K) a (x s)

/-- One constant-stream corona conormal in every packet coordinate. -/
def packetCoronaConormal (S : Type*) :
    (S → K) →ₗ[K] (S → StreamCorona K) where
  toFun a s :=
    a s •
      (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K)
  map_add' a b := by
    funext s
    simp only [Pi.add_apply, add_smul]
  map_smul' c a := by
    funext s
    change
      (c * a s) •
          (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) =
        c •
          (a s •
            (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K))
    exact mul_smul c (a s) _

/-- Independent packet amplitudes give independent corona conormals. -/
theorem packetCoronaConormal_injective (S : Type*) :
    Function.Injective (packetCoronaConormal K S) := by
  intro a b hab
  funext s
  have hs := congrFun hab s
  change
    a s • (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) =
      b s • (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) at hs
  have hzero :
      (a s - b s) •
          (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) = 0 := by
    rw [sub_smul, hs, sub_self]
  have hscalar : a s - b s = 0 := by
    rcases (smul_eq_zero.mp hzero) with h | h
    · exact h
    · exact False.elim ((coronaClass_const_ne_zero K) h)
  exact sub_eq_zero.mp hscalar

/-- The packet Gamma-corona kernel is exactly the packet of constant-stream conormal lines. -/
theorem range_packetCoronaConormal_eq_ker_packetStreamCoronaConstraint
    (S : Type*) :
    LinearMap.range (packetCoronaConormal K S) =
      LinearMap.ker (packetStreamCoronaConstraint K S) := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    funext s
    change
      streamCoronaConstraint K
          (a s •
            (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K)) = 0
    rw [map_smul]
    have hconst :
        (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) ∈
          LinearMap.ker (streamCoronaConstraint K) := by
      rw [ker_streamCoronaConstraint K]
      exact Submodule.mem_span_singleton_self _
    rw [LinearMap.mem_ker.mp hconst, smul_zero]
  · intro x hx
    have hxzero :
        packetStreamCoronaConstraint K S x = 0 :=
      LinearMap.mem_ker.mp hx
    have hcomponent :
        ∀ s : S, x s ∈ LinearMap.ker (streamCoronaConstraint K) := by
      intro s
      rw [LinearMap.mem_ker]
      exact congrFun hxzero s
    have hspan :
        ∀ s : S,
          x s ∈
            K ∙
              (Submodule.Quotient.mk (fun _ ↦ (1 : K)) : StreamCorona K) := by
      intro s
      simpa only [ker_streamCoronaConstraint K] using hcomponent s
    choose a ha using fun s ↦ Submodule.mem_span_singleton.mp (hspan s)
    refine ⟨a, ?_⟩
    funext s
    exact ha s

/-- **Gamma packet-corona codimension law.**  The finite-blind conormal rank of a finite packet is
exactly its number of normal directions. -/
theorem finrank_ker_packetStreamCoronaConstraint
    (S : Type*) [Fintype S] :
    Module.finrank K (LinearMap.ker (packetStreamCoronaConstraint K S)) =
      Fintype.card S := by
  rw [← range_packetCoronaConormal_eq_ker_packetStreamCoronaConstraint K S]
  have hfinrank :=
    (LinearEquiv.ofInjective
      (packetCoronaConormal K S)
      (packetCoronaConormal_injective K S)).finrank_eq
  simpa only [Module.finrank_pi] using hfinrank.symm

/-- On an `N`-direction packet, Gamma corona conormal rank is exactly `N`. -/
theorem finrank_ker_finPacketStreamCoronaConstraint (N : ℕ) :
    Module.finrank K
        (LinearMap.ker (packetStreamCoronaConstraint K (Fin N))) = N := by
  rw [finrank_ker_packetStreamCoronaConstraint K (Fin N), Fintype.card_fin]

end

end GaloisForLFunctions.HTGeometry
