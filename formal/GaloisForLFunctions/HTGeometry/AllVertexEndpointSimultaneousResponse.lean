import GaloisForLFunctions.HTGeometry.AllVertexEndpointResponse
import GaloisForLFunctions.HTGeometry.PolynomialEvalSelector

/-!
# Simultaneous all-observer response under one physical layer shift

A leaf attachment must preserve transition channels at every old observer
site at once.  Pointwise response escape is insufficient: choosing a layer
shift for one observer could put another observer at a pole or a response
zero.

This file clears every finite response packet into one polynomial.  One
nonnegative integer layer shift then avoids every product-spectrum collision
and keeps every prescribed two-step observer response nonzero
simultaneously.  The result is uniform over arbitrary unselected transition
matrix entries.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Clearing the common denominator of a finite simple-pole packet is an
exact pointwise identity at every pole-free evaluation point. -/
theorem distinctNodePacketNumerator_eval_eq_packet_mul_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z c : ι → ℂ) (w : ℂ)
    (havoid : ∀ i, w ≠ z i) :
    (distinctNodePacketNumerator z c).eval w =
      (∑ i, c i / (z i - w)) * ∏ i, (z i - w) := by
  rw [distinctNodePacketNumerator]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : z i - w ≠ 0 :=
    sub_ne_zero.mpr (havoid i).symm
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => z j - w) (Finset.mem_univ i)]
  field_simp

private theorem C_sub_X_ne_zero (z : ℂ) :
    Polynomial.C z - Polynomial.X ≠ 0 := by
  intro hzero
  apply Polynomial.X_sub_C_ne_zero z
  calc
    Polynomial.X - Polynomial.C z =
        -(Polynomial.C z - Polynomial.X) := by ring
    _ = 0 := by rw [hzero]; simp

/-- **Simultaneous all-observer layer-shift law.** Given finitely many
two-step channels, each consisting of one nonzero attachment transition
followed by one nonzero observer transition, one nonnegative integer layer
shift simultaneously:

* avoids every pole of every response packet; and
* makes every full response packet nonzero.

No genericity assumption is placed on any unselected matrix entry. -/
theorem
    exists_natCast_all_twoStepEndpointPacketResponses_ne_zero
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (attachment observer : J → Matrix I I ℂ)
    (a g b : J → I)
    (hag : ∀ q, a q ≠ g q)
    (hgb : ∀ q, g q ≠ b q)
    (hattachment : ∀ q, attachment q (a q) (g q) ≠ 0)
    (hobserver : ∀ q, observer q (g q) (b q) ≠ 0) :
    ∃ n : ℕ,
      (n : ℂ) ∉
          twoLayerForbiddenShift (fun i => (energy i : ℂ)) ∧
      (∀ q j,
        (n : ℂ) ≠
          twoStepEndpointPacketPole energy (a q) (b q) j) ∧
      ∀ q,
        twoStepEndpointPacketResponse energy
          (attachment q) (observer q) (a q) (b q) n ≠ 0 := by
  let numerator : J → ℂ[X] := fun q =>
    distinctNodePacketNumerator
      (twoStepEndpointPacketPole energy (a q) (b q))
      (twoStepEndpointPacketCoefficient
        (attachment q) (observer q) (a q) (b q))
  let denominator : J → ℂ[X] := fun q =>
    ∏ j : Sum I I,
      (Polynomial.C
        (twoStepEndpointPacketPole energy (a q) (b q) j) -
          Polynomial.X)
  let globalDenominator : ℂ[X] :=
    ∏ p : I × I,
      (Polynomial.C ((energy p.2 - energy p.1 : ℝ) : ℂ) -
        Polynomial.X)
  let Q : ℂ[X] :=
    globalDenominator * ∏ q, numerator q * denominator q
  have hnumerator : ∀ q, numerator q ≠ 0 := by
    intro q
    exact twoStepEndpointPacketNumerator_ne_zero
      energy hmax (attachment q) (observer q)
      (hag q) (hgb q) (hattachment q) (hobserver q)
  have hdenominator : ∀ q, denominator q ≠ 0 := by
    intro q
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact C_sub_X_ne_zero _
  have hglobalDenominator : globalDenominator ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact C_sub_X_ne_zero _
  have hQ : Q ≠ 0 := by
    apply mul_ne_zero hglobalDenominator
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact mul_ne_zero (hnumerator q) (hdenominator q)
  obtain ⟨n, _hnmem, hnQ⟩ :=
    GaloisForLFunctions.exists_mem_eval_ne_zero
      (b := fun n : ℕ => (n : ℂ))
      Nat.cast_injective hQ Set.infinite_univ
  have hglobalAndBlocks :
      globalDenominator.eval (n : ℂ) *
          (∏ q,
            (numerator q * denominator q).eval (n : ℂ)) ≠ 0 := by
    simpa only [Q, eval_mul, eval_prod] using hnQ
  have hglobalEval :
      globalDenominator.eval (n : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp hglobalAndBlocks).1
  have hblock :
      ∀ q, (numerator q * denominator q).eval (n : ℂ) ≠ 0 := by
    have hprod :
        (∏ q, (numerator q * denominator q).eval (n : ℂ)) ≠ 0 := by
      exact (mul_ne_zero_iff.mp hglobalAndBlocks).2
    intro q
    exact Finset.prod_ne_zero_iff.mp hprod q (Finset.mem_univ q)
  have hglobalAvoid :
      (n : ℂ) ∉
        twoLayerForbiddenShift (fun i => (energy i : ℂ)) := by
    rintro ⟨p, hp⟩
    apply hglobalEval
    change
      (∏ p : I × I,
        (Polynomial.C ((energy p.2 - energy p.1 : ℝ) : ℂ) -
          Polynomial.X)).eval (n : ℂ) = 0
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    simp only [eval_sub, eval_C, eval_X]
    rw [← hp]
    push_cast
    ring
  have havoid :
      ∀ q j,
        (n : ℂ) ≠
          twoStepEndpointPacketPole energy (a q) (b q) j := by
    intro q j hnj
    have hfactor : (denominator q).eval (n : ℂ) ≠ 0 :=
      (mul_ne_zero_iff.mp (by
        simpa only [eval_mul] using hblock q)).2
    apply hfactor
    change
      (∏ j : Sum I I,
        (Polynomial.C
          (twoStepEndpointPacketPole energy (a q) (b q) j) -
            Polynomial.X)).eval (n : ℂ) = 0
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hnj]
  refine ⟨n, hglobalAvoid, havoid, ?_⟩
  intro q hresponse
  have hnum : (numerator q).eval (n : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp (by
      simpa only [eval_mul] using hblock q)).1
  apply hnum
  change
    (distinctNodePacketNumerator
      (twoStepEndpointPacketPole energy (a q) (b q))
      (twoStepEndpointPacketCoefficient
        (attachment q) (observer q) (a q) (b q))).eval
        (n : ℂ) = 0
  rw [distinctNodePacketNumerator_eval_eq_packet_mul_prod]
  · rw [show
      (∑ j,
        twoStepEndpointPacketCoefficient
            (attachment q) (observer q) (a q) (b q) j /
          (twoStepEndpointPacketPole energy (a q) (b q) j - n)) =
        twoStepEndpointPacketResponse energy
          (attachment q) (observer q) (a q) (b q) n by rfl,
      hresponse, zero_mul]
  · exact havoid q

end

end GaloisForLFunctions.HTGeometry
