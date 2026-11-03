import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PrimeLewisBoundaryFunctional

/-!
# Corrected prime Hecke transport on the retained boundary carrier

Restoration with its retained coordinate intertwines every corrected prime source
operator with the actual Hecke action and its boundary eigenvalue.
-/

set_option autoImplicit false
noncomputable section
open Complex Set
open GaloisForLFunctions RenormalizedIntersectionTheory MayerScatteringCore

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


private theorem lewisHeckeOperator_reconstruct (p : ℕ) (s : ℂ) (g : ℝ → ℂ) (c : ℂ) (a : ℝ) :
    lewisHeckeOperator p s (mayerBoundaryReconstruct s g c) a =
      lewisHeckeOperator p s g a -
        c * lewisHeckeOperator p s (fun x : ℝ => 1 + (x : ℂ) ^ (-(2 * s))) a -
        (g 1 / (2 * s - 1)) * lewisHeckeOperator p s (scatteringPowers (2 * s)) a := by
  simp only [lewisHeckeOperator, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro M hM
  rw [mayerBoundaryReconstruct]
  ring

/-- Every corrected prime correspondence is actual source transport with the
retained boundary coordinate scaled by its arithmetic eigenvalue. -/
theorem mayerCorrectedHeckeOperator_reconstruct {p : ℕ} [Fact p.Prime] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) {g : ℝ → ℂ}
    (hg : g ∈ mayerCompletedLewisCarrier s) (c : ℂ) :
    mayerCorrectedHeckeOperator p s (mayerBoundaryReconstruct s g c) =
      mayerBoundaryReconstruct s (lewisHeckeOperator p s g)
        ((1 + (p : ℂ) ^ (1 - 2 * s)) * c) := by
  have hv := mayerCompletedLewisCarrier_boundary_relation hg
  funext a
  rw [mayerCorrectedHeckeOperator, mayerCoreZetaCoordinate_reconstruct hs hs1 g c hv,
    mayerCoreScatteringCoordinate_reconstruct hs hs1 g c hv,
    lewisHeckeOperator_reconstruct]
  conv_rhs => rw [mayerBoundaryReconstruct, mayerCompletedLewisCarrier_prime_at_one hg]
  ring

/-- Retained-boundary restoration intertwines every corrected prime operator
with the actual source correspondence on the full carrier. -/
theorem mayerBoundaryRestore_correctedHeckeOperator {p : ℕ} [Fact p.Prime] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) {f : ℝ → ℂ}
    (hf : f ∈ mayerBoundaryCoreCarrier s) :
    mayerBoundaryRestore s (mayerCorrectedHeckeOperator p s f) =
        lewisHeckeOperator p s (mayerBoundaryRestore s f) ∧
      mayerCoreZetaCoordinate s (mayerCorrectedHeckeOperator p s f) =
        (1 + (p : ℂ) ^ (1 - 2 * s)) * mayerCoreZetaCoordinate s f := by
  have hg : mayerBoundaryRestore s f ∈ mayerCompletedLewisCarrier s := hf
  have hp : p.Prime := Fact.out
  have hT := mayerCompletedLewisCarrier_heckeOperator hp.pos hg
  have hv := mayerCompletedLewisCarrier_boundary_relation hT
  have he := mayerCorrectedHeckeOperator_reconstruct (p := p) hs hs1 hg (mayerCoreZetaCoordinate s f)
  rw [mayerBoundaryReconstruct_restore hs1 f] at he
  constructor
  · rw [he]
    exact mayerBoundaryRestore_reconstruct hs hs1 _ _ hv
  · rw [he]
    exact mayerCoreZetaCoordinate_reconstruct hs hs1 _ _ hv

/-- The explicit physical boundary extension is invariant under every corrected
prime source correspondence. -/
theorem mayerBoundaryCoreCarrier_correctedHeckeOperator {p : ℕ} [Fact p.Prime] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) {f : ℝ → ℂ}
    (hf : f ∈ mayerBoundaryCoreCarrier s) :
    mayerCorrectedHeckeOperator p s f ∈ mayerBoundaryCoreCarrier s := by
  change mayerBoundaryRestore s (mayerCorrectedHeckeOperator p s f) ∈ mayerCompletedLewisCarrier s
  rw [(mayerBoundaryRestore_correctedHeckeOperator hs hs1 hf).1]
  exact mayerCompletedLewisCarrier_heckeOperator (Fact.out : p.Prime).pos hf

#print axioms mayerCorrectedHeckeOperator_reconstruct
#print axioms mayerBoundaryRestore_correctedHeckeOperator
#print axioms mayerBoundaryCoreCarrier_correctedHeckeOperator

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
