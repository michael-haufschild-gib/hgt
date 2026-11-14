import GaloisForLFunctions.RepresentationLifting.AcyclicNormalForm
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.CharP.Two

/-!
# Trace on acyclic square-zero modules

A linear section supplies a contracting operator `s` with `ds + sd = 1`.
For every endomorphism `T` commuting with `d`, cyclicity of trace gives
`tr T = 2 tr(sdT)`. Thus these endomorphisms are traceless in characteristic two.
This is the basis-independent form of the free dual-number trace mechanism.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Exactness of a square-zero operator over a field gives a contracting operator. -/
theorem acyclic_squareZero_contracting (d : Module.End k V)
    (hexact : LinearMap.range d = LinearMap.ker d) :
    ∃ s : Module.End k V, d * s + s * d = 1 := by
  obtain ⟨e, he⟩ := acyclic_squareZero_normalForm d hexact
  let s : Module.End k V := e.symm.toLinearMap.comp
    (((LinearMap.snd k (LinearMap.ker d) (LinearMap.ker d)).prod 0).comp e.toLinearMap)
  have hs (v : V) : e (s v) = ((e v).2, 0) := by simp [s]
  refine ⟨s, ?_⟩
  ext v
  apply e.injective
  change e (d (s v) + s (d v)) = e v
  rw [map_add, he, hs, hs, he]
  simp

/-- One contraction gives the doubled trace formula for the entire centralizer of `d`. -/
theorem acyclic_squareZero_trace_formula [FiniteDimensional k V]
    (d : Module.End k V) (hexact : LinearMap.range d = LinearMap.ker d) :
    ∃ s : Module.End k V, d * s + s * d = 1 ∧
      ∀ T : Module.End k V, T * d = d * T →
        LinearMap.trace k V T = 2 * LinearMap.trace k V (s * d * T) := by
  obtain ⟨s, hs⟩ := acyclic_squareZero_contracting d hexact
  refine ⟨s, hs, ?_⟩
  intro T hcomm
  calc
    LinearMap.trace k V T = LinearMap.trace k V ((d * s + s * d) * T) := by rw [hs, one_mul]
    _ = LinearMap.trace k V (d * s * T) + LinearMap.trace k V (s * d * T) := by
      rw [add_mul, map_add]
    _ = 2 * LinearMap.trace k V (s * d * T) := by
      rw [mul_assoc d s T, LinearMap.trace_mul_comm, mul_assoc s T d, hcomm,
        ← mul_assoc, two_mul]

/-- The centralizer of an acyclic square-zero operator is traceless in characteristic two. -/
theorem acyclic_squareZero_trace_zero [FiniteDimensional k V] [CharP k 2]
    (d T : Module.End k V) (hexact : LinearMap.range d = LinearMap.ker d)
    (hcomm : T * d = d * T) : LinearMap.trace k V T = 0 := by
  obtain ⟨s, _, hs⟩ := acyclic_squareZero_trace_formula d hexact
  rw [hs T hcomm, two_mul, CharTwo.add_self_eq_zero]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.acyclic_squareZero_contracting
#print axioms GaloisForLFunctions.RepresentationLifting.acyclic_squareZero_trace_formula
#print axioms GaloisForLFunctions.RepresentationLifting.acyclic_squareZero_trace_zero
