import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity

/-!
# Literal adjacent admission history budget

Route U needs an all-degree object: a cofinal selection of degrees leaves open a sparse
escape.  This file aggregates the existing *literal* adjacent completed-arithmetic source
law over every finite consecutive degree interval.  It also separates a strictly positive
cross-degree reserve from logarithmic admission velocity.  Thus a future source lower bound
must control this history budget, not merely a cofinal set of degreewise charges.

No source lower bound, limiting rate, or Riemann-hypothesis conclusion is asserted here.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- Kinetic plus cross-degree cost paid by the two literal adjacent source actions. -/
def routeUAdjacentEffectivityCost (w : ℝ) (n : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionNorm (w ^ 2) n *
        xiShiftedCanonicalAdmissionNorm (w ^ 2) (n - 1) *
        (xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) (n - 1) -
          xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) n) ^ 2 +
      2 * (xiShiftedNondegenerateSourceEffectivityWeight n +
          xiShiftedNondegenerateSourceEffectivityWeight (n - 1)) *
        xiShiftedCanonicalAdmissionNorm (w ^ 2) n *
        xiShiftedCanonicalAdmissionNorm (w ^ 2) (n - 1)

/-- Literal completed arithmetic source supply on the shared degree edge. -/
def routeUAdjacentLiteralSourceSupply (w : ℝ) (n : ℕ) : ℝ :=
  xiShiftedNondegenerateSourceEffectivityWeight n *
        xiShiftedCanonicalAdmissionNorm (w ^ 2) (n - 1) *
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource w n
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) (n + 1)) +
      xiShiftedNondegenerateSourceEffectivityWeight (n - 1) *
        xiShiftedCanonicalAdmissionNorm (w ^ 2) n *
        xiShiftedNondegenerateNullFlagCompletedArithmeticSource w (n - 1)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) (n - 1))
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)

/-- Non-kinetic cost which persists when adjacent logarithmic velocity vanishes. -/
def routeUAdjacentCrossDegreeReserve (w : ℝ) (n : ℕ) : ℝ :=
  2 * (xiShiftedNondegenerateSourceEffectivityWeight n +
      xiShiftedNondegenerateSourceEffectivityWeight (n - 1)) *
    xiShiftedCanonicalAdmissionNorm (w ^ 2) n *
    xiShiftedCanonicalAdmissionNorm (w ^ 2) (n - 1)

/-- Two adjacent literal sources pay the complete adjacent admission cost. -/
theorem routeU_adjacentEffectivityCost_le_literalSourceSupply
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    routeUAdjacentEffectivityCost w n ≤ routeUAdjacentLiteralSourceSupply w n := by
  exact literal_adjacent_nondegenerateAdaptiveMixedSources_pay_edgeEffectivity hw hn hH

/-- Positive Hankel chambers retain the cross-degree reserve inside full edge cost. -/
theorem routeU_adjacentCrossDegreeReserve_le_effectivityCost
    {w : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    routeUAdjacentCrossDegreeReserve w n ≤ routeUAdjacentEffectivityCost w n := by
  have htop : (xiShiftedMomentHankelMatrix (w ^ 2) (n + 2)).PosDef := hH
  have hprev : (xiShiftedMomentHankelMatrix (w ^ 2) ((n - 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) htop
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm (w ^ 2) n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm htop]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef htop) (by omega)
  have hprevnorm : 0 < xiShiftedCanonicalAdmissionNorm (w ^ 2) (n - 1) := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hprev]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hprev) (by omega)
  have hvelocity : 0 ≤
      xiShiftedCanonicalAdmissionNorm (w ^ 2) n *
        xiShiftedCanonicalAdmissionNorm (w ^ 2) (n - 1) *
        (xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) (n - 1) -
          xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) n) ^ 2 := by
    positivity
  exact le_add_of_nonneg_left hvelocity

/-- Literal sources pay every finite consecutive history of adjacent admission costs. -/
theorem routeU_finset_adjacentEffectivityHistory_le_literalSourceSupply
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    (∑ n ∈ Finset.Icc 2 N, routeUAdjacentEffectivityCost w n) ≤
      ∑ n ∈ Finset.Icc 2 N, routeUAdjacentLiteralSourceSupply w n := by
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  have htop : (xiShiftedMomentHankelMatrix (w ^ 2) (N + 2)).PosDef := hH
  have hnH : (xiShiftedMomentHankelMatrix (w ^ 2) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) htop
  exact routeU_adjacentEffectivityCost_le_literalSourceSupply hw hn.1 hnH

/-- Every finite consecutive degree history retains its cross-degree reserve, paid by
literal completed arithmetic source supply. -/
theorem routeU_finset_adjacentCrossDegreeReserve_le_literalSourceSupply
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (N + 2)).PosDef) :
    (∑ n ∈ Finset.Icc 2 N, routeUAdjacentCrossDegreeReserve w n) ≤
      ∑ n ∈ Finset.Icc 2 N, routeUAdjacentLiteralSourceSupply w n := by
  calc
    (∑ n ∈ Finset.Icc 2 N, routeUAdjacentCrossDegreeReserve w n) ≤
        ∑ n ∈ Finset.Icc 2 N, routeUAdjacentEffectivityCost w n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Icc] at hn
      have htop : (xiShiftedMomentHankelMatrix (w ^ 2) (N + 2)).PosDef := hH
      have hnH : (xiShiftedMomentHankelMatrix (w ^ 2) (n + 2)).PosDef :=
        xiShiftedMomentHankel_posDef_of_le (by omega) htop
      exact routeU_adjacentCrossDegreeReserve_le_effectivityCost hn.1 hnH
    _ ≤ ∑ n ∈ Finset.Icc 2 N, routeUAdjacentLiteralSourceSupply w n :=
      routeU_finset_adjacentEffectivityHistory_le_literalSourceSupply hw hH

end

end RHTower
