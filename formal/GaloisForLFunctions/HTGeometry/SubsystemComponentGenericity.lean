import GaloisForLFunctions.HTGeometry.SubsystemComponentDecomposition
import GaloisForLFunctions.HTGeometry.BlockSumSpectralGenericity

/-!
# Generic transversality of the component spectra of a subsystem

Equation `(5)` computes the temporal rank read by a vertex subset once the
spectra of the connected components of the induced graph are mutually
projectively independent.  That hypothesis is a genericity condition on the
ambient interaction parameters: it holds at every parameter of the
block-diagonal projective generic set of the component families.

This file names that set, extracts the transversality hypothesis from it, and
records its one-witness genericity.
-/

open scoped Matrix BigOperators
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Component families of a vertex subset, as polynomial matrix families in the
ambient interaction parameters. -/
def componentPolynomialFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    ∀ c : {P : Finset V // P ∈ componentPackets G S},
      Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1)
        (MvPolynomial (Fin (interactionCoordinateCount A G)) ℂ) :=
  fun c => realAffineMatrixPolynomial 0 (restrictedGeneratorFin A G c.1)

theorem componentPolynomialFamily_eval (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V)
    (c : {P : Finset V // P ∈ componentPackets G S})
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    (componentPolynomialFamily A G S c).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))) =
      subsystemBlock A G c.1 p :=
  eval_realAffineMatrixPolynomial 0 (restrictedGeneratorFin A G c.1) p

theorem componentPolynomialFamily_isHermitian (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V)
    (c : {P : Finset V // P ∈ componentPackets G S})
    (p : Fin (interactionCoordinateCount A G) → ℝ) :
    ((componentPolynomialFamily A G S c).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p t : ℂ)))).IsHermitian := by
  rw [componentPolynomialFamily_eval]
  exact subsystemBlock_isHermitian A G c.1 p

/-- Parameters at which the component spectra of a vertex subset are mutually
projectively independent. -/
def subsystemComponentGenericSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    Set (Fin (interactionCoordinateCount A G) → ℝ) :=
  polynomialMatrixProjectiveGenericSet
    (Matrix.blockDiagonal' (componentPolynomialFamily A G S))

/-- **The generic set delivers the hypothesis of equation `(5)`.** -/
theorem componentProjectivelyIndependent_of_mem_subsystemComponentGenericSet
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p : Fin (interactionCoordinateCount A G) → ℝ)
    (hp : p ∈ subsystemComponentGenericSet A G S) :
    ComponentProjectivelyIndependent
      (fun c : {P : Finset V // P ∈ componentPackets G S} =>
        (subsystemBlock_isHermitian A G c.1 p).eigenvalues) := by
  have hbase := componentProjectivelyIndependent_of_mem_blockDiagonalGenericSet
    (componentPolynomialFamily A G S) p
    (componentPolynomialFamily_isHermitian A G S · p) hp
  have hfun :
      (fun c : {P : Finset V // P ∈ componentPackets G S} =>
        (componentPolynomialFamily_isHermitian A G S c p).eigenvalues) =
      fun c : {P : Finset V // P ∈ componentPackets G S} =>
        (subsystemBlock_isHermitian A G c.1 p).eigenvalues := by
    funext c
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (componentPolynomialFamily_isHermitian A G S c p)
      (subsystemBlock_isHermitian A G c.1 p)).2
    rw [componentPolynomialFamily_eval]
  rwa [hfun] at hbase

/-- **One witness makes component transversality generic.**  If some parameter
carries a maximally projective concatenated root packet for the component
blocks of a vertex subset, then the parameters with mutually projectively
independent component spectra are dense, residual and of full Lebesgue
measure. -/
theorem subsystemComponentGenericSet_dense_residual_fullMeasure
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (p₀ : Fin (interactionCoordinateCount A G) → ℝ)
    (e : ∀ c : {P : Finset V // P ∈ componentPackets G S},
      LocalConfiguration A c.1 → ℝ)
    (hroot : ∀ c i, matrixCharpolyRelation
      (subsystemBlock A G c.1 p₀, (e c i : ℂ)) = 0)
    (hmax : MaximallyProjectiveEnergy
      (fun x : Σ c : {P : Finset V // P ∈ componentPackets G S},
          LocalConfiguration A c.1 => e x.1 x.2)) :
    Dense (subsystemComponentGenericSet A G S) ∧
      subsystemComponentGenericSet A G S ∈
        residual (Fin (interactionCoordinateCount A G) → ℝ) ∧
      volume (subsystemComponentGenericSet A G S)ᶜ = 0 := by
  refine blockDiagonalProjectiveGenericSet_dense_residual_fullMeasure
    (componentPolynomialFamily A G S) p₀ e hmax ?_
  intro c i
  rw [componentPolynomialFamily_eval]
  exact hroot c i

end

end GaloisForLFunctions.HTGeometry
