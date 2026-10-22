/-
Copyright (c) 2026 Michael L. Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael L. Walker
-/
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSupportPrunedSelfAdjointSeamCarrier
import GaloisForLFunctions.RHTower.DirichletHilbertRiggingBarrier

/-!
# Evaluation-rigging fracture for the Suzuki seam carrier

The support-pruned `ell²` carrier has the correct self-adjoint prime adjacency, but scalar physical
evaluation has unit-modulus response on every valuation basis vector. On any infinite injective
vertex family, no bounded Hilbert functional can have those responses.

This theorem does not reject the carrier. It forces the rigged realization
`ell¹ ⊂ ell² ⊂ ell∞`: physical evaluation is bounded on the `ell¹` source state, while the
middle `ell²` space retains self-adjoint Gamma/prime energy.
-/

open Complex Set
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- **No bounded physical phase evaluation on an infinite Suzuki `ell²` seam family.**

The phase may be the literal `exp (-i ξ x(q_n))`, but the theorem only needs its exact
unit-modulus property. -/
theorem no_bounded_suzukiSeamHilbert_phaseEvaluation
    (q : ℕ → SuzukiSeamVertex) (hq : Function.Injective q)
    (phase : ℕ → ℂ) (hphase : ∀ n, ‖phase n‖ = 1) :
    ¬ ∃ E : SuzukiSeamHilbert →L[ℂ] ℂ,
      ∀ n, E (lp.single 2 (q n) (1 : ℂ)) = phase n := by
  let u : ℕ → SuzukiSeamHilbert := fun n =>
    (starRingEnd ℂ) (phase n) • lp.single 2 (q n) (1 : ℂ)
  have hphase_mul (n : ℕ) :
      phase n * (starRingEnd ℂ) (phase n) = 1 := by
    rw [Complex.mul_conj', hphase n]
    norm_num
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      dsimp [u]
      rw [inner_smul_left, inner_smul_right, lp.inner_single_left]
      simp [lp.single_apply, hphase_mul]
    · have hqij : q i ≠ q j := fun h => hij (hq h)
      dsimp [u]
      rw [inner_smul_left, inner_smul_right, lp.inner_single_left]
      simp [lp.single_apply, hqij, hij]
  have hB : HasBesselBound u 1 := by
    intro s x
    simpa using hu.sum_inner_products_le x (s := s)
  rintro ⟨E, hE⟩
  apply no_bessel_family_with_unit_response u 1 hB
  refine ⟨ContinuousLinearMap.adjoint E 1, ?_⟩
  intro n
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [u, hE n, hphase_mul]

end GaloisForLFunctions.RHTower
