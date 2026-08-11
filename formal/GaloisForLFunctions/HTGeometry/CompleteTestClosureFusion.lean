import Mathlib

/-!
# Complete test-closure fusion

This module certifies the basis-independent finite core of
`complete-atomic-fourier-hankel-order-and-inertia-fusion-law.md`.

A finite family of source-atom quadratic responses is fused after an invertible change of complete
test coordinates.  The fused response reconstructs every atom response, reflects atomwise
nonnegativity, preserves every compensation-feasibility set, and preserves existence of a strict
negative witness.  The final matrix lemmas certify the corresponding positive-semidefinite
congruence law and its Vandermonde specialization.

Fourier and Hankel packets enter the paper theorem because their full finite evaluation transforms
are Vandermonde isomorphisms.  The present theorem deliberately takes the resulting equivalence as
its coordinate-free input, so the response space `V` can itself be a matrix-channel space.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {X V : Type*}

/-- Sum of all source-atom responses on one complete test packet. -/
def completeAtomicResponse [Fintype X] (Q : X → V → ℝ) (z : X → V) : ℝ :=
  ∑ x, Q x (z x)

/-- Every source atom has nonnegative response on every local test. -/
def AtomwiseResponseNonnegative (Q : X → V → ℝ) : Prop :=
  ∀ x v, 0 ≤ Q x v

/-- The unfused complete packet has nonnegative total response. -/
def CompleteResponseNonnegative [Fintype X] (Q : X → V → ℝ) : Prop :=
  ∀ z, 0 ≤ completeAtomicResponse Q z

/-- An invertible test transformation has nonnegative fused response on every packet. -/
def TransformedCompleteResponseNonnegative [Fintype X]
    (Q : X → V → ℝ) (T : (X → V) ≃ (X → V)) : Prop :=
  ∀ z, 0 ≤ completeAtomicResponse Q (T z)

/-- A packet supported at one atom reads exactly that atom's response. -/
theorem completeAtomicResponse_single [Fintype X] [DecidableEq X] [Zero V]
    (Q : X → V → ℝ) (hzero : ∀ x, Q x 0 = 0) (x : X) (v : V) :
    completeAtomicResponse Q (Pi.single x v) = Q x v := by
  classical
  simp only [completeAtomicResponse]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy]
    exact hzero y
  · simp

/-- Complete unfused packets reflect the full finite atomwise positive order. -/
theorem atomwiseResponseNonnegative_iff_completeResponseNonnegative
    [Fintype X] [DecidableEq X] [Zero V]
    (Q : X → V → ℝ) (hzero : ∀ x, Q x 0 = 0) :
    AtomwiseResponseNonnegative Q ↔ CompleteResponseNonnegative Q := by
  constructor
  · intro h z
    exact Finset.sum_nonneg fun x _ => h x (z x)
  · intro h x v
    have hv := h (Pi.single x v)
    rw [completeAtomicResponse_single Q hzero x v] at hv
    exact hv

/-- **Complete test fusion reflects source order.**  Any invertible change of complete test
coordinates has nonnegative fused response exactly when every source atom is nonnegative. -/
theorem transformedCompleteResponseNonnegative_iff_atomwise
    [Fintype X] [DecidableEq X] [Zero V]
    (Q : X → V → ℝ) (hzero : ∀ x, Q x 0 = 0)
    (T : (X → V) ≃ (X → V)) :
    TransformedCompleteResponseNonnegative Q T ↔ AtomwiseResponseNonnegative Q := by
  rw [atomwiseResponseNonnegative_iff_completeResponseNonnegative Q hzero]
  constructor
  · intro h z
    simpa using h (T.symm z)
  · intro h z
    exact h (T z)

/-- Two complete invertible test calculi have exactly the same positive cone. -/
theorem transformedCompleteResponseNonnegative_iff_transformed
    [Fintype X] [DecidableEq X] [Zero V]
    (Q : X → V → ℝ) (hzero : ∀ x, Q x 0 = 0)
    (T U : (X → V) ≃ (X → V)) :
    TransformedCompleteResponseNonnegative Q T ↔
      TransformedCompleteResponseNonnegative Q U := by
  rw [transformedCompleteResponseNonnegative_iff_atomwise Q hzero T,
    transformedCompleteResponseNonnegative_iff_atomwise Q hzero U]

/-- **Joint reconstruction.** Equality of one complete fused response for all packets reconstructs
every source-atom quadratic response. -/
theorem completeTransformedResponse_reconstructs_atoms
    [Fintype X] [DecidableEq X] [Zero V]
    (Q P : X → V → ℝ) (hQzero : ∀ x, Q x 0 = 0) (hPzero : ∀ x, P x 0 = 0)
    (T : (X → V) ≃ (X → V))
    (hresponse : ∀ z, completeAtomicResponse Q (T z) = completeAtomicResponse P (T z)) :
    Q = P := by
  funext x v
  have h := hresponse (T.symm (Pi.single x v))
  rw [T.apply_symm_apply, completeAtomicResponse_single Q hQzero x v,
    completeAtomicResponse_single P hPzero x v] at h
  exact h

/-- A complete invertible test basis preserves the existence of a strict negative witness.  Thus a
negative atom direction cannot disappear through complete Fourier/Hankel fusion. -/
theorem transformedCompleteResponse_negativeWitness_iff
    [Fintype X] [DecidableEq X] [Zero V]
    (Q : X → V → ℝ) (hzero : ∀ x, Q x 0 = 0)
    (T : (X → V) ≃ (X → V)) :
    (∃ z, completeAtomicResponse Q (T z) < 0) ↔ ∃ x v, Q x v < 0 := by
  constructor
  · rintro ⟨z, hz⟩
    by_contra h
    push Not at h
    exact (not_lt_of_ge (Finset.sum_nonneg fun x _ => h x ((T z) x))) hz
  · rintro ⟨x, v, hv⟩
    refine ⟨T.symm (Pi.single x v), ?_⟩
    rw [T.apply_symm_apply, completeAtomicResponse_single Q hzero x v]
    exact hv

/-- **Compensation-gauge conservation.** For every coefficient `c`, atomwise feasibility of the
compensated source response is equivalent to feasibility after any complete invertible test fusion.
Hence all complete test bases have exactly the same feasible coefficient set and the same sharp
admission gauge. -/
theorem completeTestCompensationFeasible_conserved
    [Fintype X] [DecidableEq X] [Zero V]
    (W H : X → V → ℝ) (hWzero : ∀ x, W x 0 = 0) (hHzero : ∀ x, H x 0 = 0)
    (T : (X → V) ≃ (X → V)) (c : ℝ) :
    (∀ x v, 0 ≤ c * W x v - H x v) ↔
      ∀ z, 0 ≤ completeAtomicResponse (fun x v => c * W x v - H x v) (T z) := by
  symm
  apply transformedCompleteResponseNonnegative_iff_atomwise
  intro x
  simp [hWzero x, hHzero x]

/-- The pointwise feasible set is identical in two complete test gauges. -/
theorem completeTestCompensationFeasible_iff_two_transforms
    [Fintype X] [DecidableEq X] [Zero V]
    (W H : X → V → ℝ) (hWzero : ∀ x, W x 0 = 0) (hHzero : ∀ x, H x 0 = 0)
    (T U : (X → V) ≃ (X → V)) (c : ℝ) :
    (∀ z, 0 ≤ completeAtomicResponse (fun x v => c * W x v - H x v) (T z)) ↔
      ∀ z, 0 ≤ completeAtomicResponse (fun x v => c * W x v - H x v) (U z) := by
  rw [← completeTestCompensationFeasible_conserved W H hWzero hHzero T c,
    ← completeTestCompensationFeasible_conserved W H hWzero hHzero U c]

section MatrixCongruence

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Invertible real congruence preserves and reflects positive semidefiniteness. -/
theorem posSemidef_invertibleCongruence_iff (U H : Matrix n n ℝ) (hU : IsUnit U) :
    (U.conjTranspose * H * U).PosSemidef ↔ H.PosSemidef := by
  simpa only [Matrix.star_eq_conjTranspose] using
    Matrix.IsUnit.posSemidef_star_left_conjugate_iff (x := H) hU

/-- Pairwise-distinct real nodes make the full Vandermonde test matrix invertible. -/
theorem completeTest_vandermonde_isUnit {N : ℕ} (node : Fin N → ℝ)
    (hnode : Function.Injective node) :
    IsUnit (Matrix.vandermonde node) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hnode)

/-- **Full finite Hankel test closure.** Congruence by a Vandermonde evaluation matrix reflects the
entire positive-semidefinite cone, not merely one direction of block-Hankel positivity. -/
theorem vandermonde_posSemidef_congruence_iff {N : ℕ} (node : Fin N → ℝ)
    (hnode : Function.Injective node) (H : Matrix (Fin N) (Fin N) ℝ) :
    ((Matrix.vandermonde node).conjTranspose * H * Matrix.vandermonde node).PosSemidef ↔
      H.PosSemidef :=
  posSemidef_invertibleCongruence_iff _ _ (completeTest_vandermonde_isUnit node hnode)

end MatrixCongruence

/-- Closed finite capstone: complete fusion reconstructs atom responses, reflects positive order,
conserves every compensation-feasibility set, and preserves strict negative witnesses. -/
theorem completeTestClosureFusion_capstone :
    (∀ (X V : Type*) [Fintype X] [DecidableEq X] [Zero V]
      (Q : X → V → ℝ) (T : (X → V) ≃ (X → V)),
      (∀ x, Q x 0 = 0) →
        (TransformedCompleteResponseNonnegative Q T ↔ AtomwiseResponseNonnegative Q)) ∧
    (∀ (X V : Type*) [Fintype X] [DecidableEq X] [Zero V]
      (Q P : X → V → ℝ) (T : (X → V) ≃ (X → V)),
      (∀ x, Q x 0 = 0) → (∀ x, P x 0 = 0) →
        (∀ z, completeAtomicResponse Q (T z) = completeAtomicResponse P (T z)) → Q = P) ∧
    (∀ (X V : Type*) [Fintype X] [DecidableEq X] [Zero V]
      (Q : X → V → ℝ) (T : (X → V) ≃ (X → V)),
      (∀ x, Q x 0 = 0) →
        ((∃ z, completeAtomicResponse Q (T z) < 0) ↔ ∃ x v, Q x v < 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X V instF instD instZ Q T hzero
    exact @transformedCompleteResponseNonnegative_iff_atomwise X V instF instD instZ Q hzero T
  · intro X V instF instD instZ Q P T hQzero hPzero
    exact @completeTransformedResponse_reconstructs_atoms X V instF instD instZ
      Q P hQzero hPzero T
  · intro X V instF instD instZ Q T hzero
    exact @transformedCompleteResponse_negativeWitness_iff X V instF instD instZ Q hzero T

end GaloisForLFunctions.HTGeometry
