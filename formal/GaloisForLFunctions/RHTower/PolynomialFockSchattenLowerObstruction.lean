import GaloisForLFunctions.RHTower.PolynomialFockAdaptedTangentPacketSynthesis
import GaloisForLFunctions.RHTower.PositiveSchattenBoundedPacketDiagonal
import GaloisForLFunctions.HTGeometry.OperatorLoewnerVectorBounds

/-!
# Schatten lower obstruction for the polynomial Fock critical-prime incidence

For `m > 4`, the critical-prime incidence operator `I = S* S` on the degree-`m` polynomial moment
Fock space is not in the Schatten class `S_q` for any `0 < q ≤ m / (m - 4)`. The proof tests `I`
against the bounded synthesis operator of the shifted adapted tangent packets: Schatten membership
would make the packet responses `Re ⟨φ_n, I φ_n⟩` `q`-summable, these responses dominate the
inner-window adapted cell masses, and those masses are not `q`-summable at or below the threshold.
The range `q < 1` is reduced to the known failure of trace-class membership.

## Main results

- `not_summable_rpow_shifted_criticalPrimeFockInnerWindowAdaptedCellMass`: for `0 < q ≤ m / (m - 4)`,
  `n ↦ M_{n+1}^q` is not summable.
- `polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_of_le_threshold`: for
  `1 ≤ q ≤ m / (m - 4)`, the incidence operator is not in `S_q`.
- `polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_of_pos_of_le_threshold`: for
  `0 < q ≤ m / (m - 4)`, the incidence operator is not in `S_q`.

## Hypotheses

All results are unconditional. They assume `4 < m` and `q ≤ m / (m - 4)`, with `0 < q` (or `1 ≤ q`
in the first Schatten statement).
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Assuming `4 < m` and `0 < q ≤ m / (m - 4)`, the shifted inner-window adapted cell masses
`n ↦ M_{n+1}^q` are not summable. -/
theorem not_summable_rpow_shifted_criticalPrimeFockInnerWindowAdaptedCellMass
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q)
    (hqThreshold : q ≤ criticalPrimeFockSchattenThreshold m) :
    ¬ Summable (fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m
        (polynomialFockInnerWindowFactor m) (n + 1) ^ q) := by
  intro hshift
  have hall : Summable (fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m
        (polynomialFockInnerWindowFactor m) n ^ q) := by
    exact (summable_nat_add_iff (f := fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m
        (polynomialFockInnerWindowFactor m) n ^ q) 1).mp hshift
  have hlt :=
    (summable_rpow_criticalPrimeFockInnerWindowAdaptedCellMass_iff hm hq).mp hall
  exact (not_lt_of_ge hqThreshold) hlt

/-- Assuming `4 < m` and `1 ≤ q ≤ m / (m - 4)`, the polynomial Fock critical-prime incidence
operator is not in the Schatten class `S_q`; the adapted packet responses would otherwise be
`q`-summable and dominate the non-summable cell masses. -/
theorem polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_of_le_threshold
    {m q : ℝ} (hm : 4 < m) (hq : 1 ≤ q)
    (hqThreshold : q ≤ criticalPrimeFockSchattenThreshold m) :
    ¬ MemSchattenClass q (polynomialCriticalPrimeSamplingIncidence m hm.le) := by
  intro hSch
  let T : MomentFock →L[ℂ] MomentFock :=
    polynomialCriticalPrimeSamplingIncidence m hm.le
  let A : MomentFock →L[ℂ] MomentFock :=
    polynomialFockAdaptedTangentPacketSynthesis m hm
  let g : ℕ → MomentFock := HTGeometry.ellTwoCoordinateBasis ℕ
  let u : ℕ → MomentFock :=
    polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le
  let mass : ℕ → ℝ := fun n =>
    criticalPrimeFockScaledAdaptedCellMass m
      (polynomialFockInnerWindowFactor m) (n + 1)
  let response : ℕ → ℝ := fun n =>
    (inner ℂ (u n) (T (u n))).re
  let a : ℝ := Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m))
  let b : ℝ := 3 ^ (m / 2 - 1)
  let K : ℝ := b / a
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hT : 0 ≤ T := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    exact polynomialCriticalPrimeSamplingIncidence_isPositive m hm.le
  change MemSchattenClass q T at hSch
  have hg : ∀ n, g n = 0 ∨ ‖g n‖ = 1 := fun n =>
    Or.inr ((HTGeometry.ellTwoCoordinateBasis ℕ).orthonormal.norm_eq_one n)
  have hgo : ∀ i j, i ≠ j → inner ℂ (g i) (g j) = 0 := fun _ _ hij =>
    (HTGeometry.ellTwoCoordinateBasis ℕ).orthonormal.inner_eq_zero hij
  have hAg : ∀ n, A (g n) = u n := by
    intro n
    change polynomialFockAdaptedTangentPacketSynthesis m hm
        (HTGeometry.ellTwoCoordinateBasis ℕ n) =
      polynomialFockShiftedAdaptedNormalizedTangentPacket m hm.le n
    exact polynomialFockAdaptedTangentPacketSynthesis_coordinateBasis hm n
  have hsumResponse : Summable fun n => response n ^ q := by
    have h := summable_rpow_bounded_packet_response_of_nonneg_of_memSchattenClass
      (A := A) hq hT hSch g hg hgo
    refine h.congr fun n => ?_
    change (inner ℂ (A (g n)) (T (A (g n)))).re ^ q = response n ^ q
    rw [hAg n]
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hK : 0 < K := div_pos hb ha
  have hcenter : ∀ n : ℕ, 1 ≤ criticalPrimeFockAdaptedCellCenter m (n + 1) := by
    intro n
    have hbase : (1 : ℝ) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hexponent : 0 ≤ 2 / m := by positivity
    exact Real.one_le_rpow hbase hexponent
  have hlow : ∀ n, a * mass n ≤ b * response n := by
    intro n
    simpa [a, b, mass, response, u, T,
      polynomialFockShiftedAdaptedNormalizedTangentPacket] using
      adaptedCell_normalizedTangentPacket_incidence_response_lower
        (m := m) hm.le (n := n + 1) (hcenter n)
  have hresponseNonneg : ∀ n, 0 ≤ response n := by
    intro n
    dsimp [response]
    rw [re_inner_comm_complex]
    exact GaloisForLFunctions.HTGeometry.re_inner_nonneg_of_nonneg hT (u n)
  have hmassLe : ∀ n, mass n ≤ K * response n := by
    intro n
    have heq : b * response n = a * (K * response n) := by
      dsimp [K]
      field_simp [ha.ne']
    by_contra hnot
    have hstrict : K * response n < mass n := lt_of_not_ge hnot
    have hmul : a * (K * response n) < a * mass n :=
      mul_lt_mul_of_pos_left hstrict ha
    linarith [hlow n]
  have hmassNonneg : ∀ n, 0 ≤ mass n := fun n =>
    criticalPrimeFockScaledAdaptedCellMass_nonneg
      (polynomialFockInnerWindowFactor_pos hm.le).le m (n + 1)
  have hdom : ∀ n, mass n ^ q ≤ K ^ q * response n ^ q := by
    intro n
    calc
      mass n ^ q ≤ (K * response n) ^ q :=
        Real.rpow_le_rpow (hmassNonneg n) (hmassLe n) hq0.le
      _ = K ^ q * response n ^ q := Real.mul_rpow hK.le (hresponseNonneg n)
  have hsumMass : Summable fun n => mass n ^ q :=
    Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (hmassNonneg n) q)
      hdom (hsumResponse.mul_left (K ^ q))
  exact not_summable_rpow_shifted_criticalPrimeFockInnerWindowAdaptedCellMass
    hm hq0 hqThreshold hsumMass

/-- Assuming `4 < m` and `0 < q ≤ m / (m - 4)`, the polynomial Fock critical-prime incidence
operator is not in `S_q`; for `q < 1` this follows from the failure of trace-class membership. -/
theorem polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_of_pos_of_le_threshold
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q)
    (hqThreshold : q ≤ criticalPrimeFockSchattenThreshold m) :
    ¬ MemSchattenClass q (polynomialCriticalPrimeSamplingIncidence m hm.le) := by
  by_cases hqOne : 1 ≤ q
  · exact polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_of_le_threshold
      hm hqOne hqThreshold
  · intro hSch
    have hSchOne := hSch.mono hq (le_of_not_ge hqOne)
    exact polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_one m hm.le hSchOne

end

end RHTower
