import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientSourceEnvelope
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant

/-!
# Chebyshev cofinal envelope for Route-P's terminal coefficient

The literal matched first moment dominates twice the ordinary Chebyshev
function.  Combined with the exact mass--centroid formula for the canonical
shift, a sharp AM--GM step exposes a `sqrt psi` source envelope.  The
unconditional prime number theorem then supplies every fixed subunit diagonal
terminal scale.

This is a cofinal source-magnitude law, not an endpoint-scale law: it does
not decide the ratio-one boundary, coefficient crossings there, or construct
the required ordered-history graph intertwiner.
-/

open scoped BigOperators Chebyshev
open Filter Topology
open ArithmeticFunction

noncomputable section

namespace RHTower

private theorem sum_range_shift_two (F : ℕ → ℝ)
    (hzero : F 0 = 0) (hone : F 1 = 0) (K : ℕ) :
    (∑ n ∈ Finset.range (K + 3), F n) =
      ∑ n ∈ Finset.range (K + 1), F (n + 2) := by
  induction K with
  | zero => simp [Finset.sum_range_succ, hzero, hone]
  | succ K ih =>
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun x : ℝ => x + F (K + 3)) ih

private theorem sum_vonMangoldt_shift_two_eq_psi (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1), ArithmeticFunction.vonMangoldt (n + 2)) =
      Chebyshev.psi ((K + 2 : ℕ) : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hIcc : Finset.Icc 0 (K + 2) = Finset.range (K + 3) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc, sum_range_shift_two]
  · rfl
  · simp

private theorem criticalMellinAtomWeight_mul_sqrt_eq_vonMangoldt
    {n : ℕ} (hn : 0 < n) :
    criticalMellinAtomWeight n * Real.sqrt (n : ℝ) = ArithmeticFunction.vonMangoldt n := by
  unfold criticalMellinAtomWeight
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hnR.le, ← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.mpr hnR]

private theorem matchedPolarCentroid_ge_two_mul_sqrt {n : ℕ} (hn : 0 < n) :
    2 * Real.sqrt (n : ℝ) ≤ ccmActualHeadMatchedPolarCentroid n := by
  have hsq := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hcent : 0 < ccmActualHeadMatchedPolarCentroid n :=
    ccmActualHeadMatchedPolarCentroid_pos n
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (criticalMellinAtomWeight n)]

/-- The literal matched first moment dominates twice the ordinary Chebyshev
mass at the identical arithmetic head. -/
theorem ccmActualHeadMatchedCentroidAggregate_one_ge_two_mul_psi (K : ℕ) :
    2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) ≤
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2) := by
  rw [← sum_vonMangoldt_shift_two_eq_psi, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn2 : 0 < n + 2 := by omega
  rw [← criticalMellinAtomWeight_mul_sqrt_eq_vonMangoldt hn2]
  calc
    2 * (criticalMellinAtomWeight (n + 2) * Real.sqrt ((n + 2 : ℕ) : ℝ)) =
        criticalMellinAtomWeight (n + 2) * (2 * Real.sqrt ((n + 2 : ℕ) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (matchedPolarCentroid_ge_two_mul_sqrt hn2)
      (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)

private theorem psi_nonneg (K : ℕ) :
    0 ≤ Chebyshev.psi ((K + 2 : ℕ) : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Exact source envelope: the negative canonical shift exceeds the square-root
of the ordinary Chebyshev mass. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredShift_le_neg_one_sub_sqrt_psi (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤
      -1 - Real.sqrt (Chebyshev.psi ((K + 2 : ℕ) : ℝ)) := by
  let m := ccmActualHeadParabolicMass K
  let s := ∑ n ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2)
  let psiK := Chebyshev.psi ((K + 2 : ℕ) : ℝ)
  have hm : 0 < m := ccmActualHeadParabolicMass_pos K
  have hs : 0 ≤ s := by
    dsimp [s]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
      (ccmActualHeadMatchedPolarCentroid_pos _).le
  have hpsi : 0 ≤ psiK := psi_nonneg K
  have hsource : 2 * psiK ≤ s :=
    ccmActualHeadMatchedCentroidAggregate_one_ge_two_mul_psi K
  have hform :
      (m / 4 + s / (2 * m)) ^ 2 - s / 2 =
        (m / 4 - s / (2 * m)) ^ 2 := by
    field_simp [hm.ne']
    ring
  have hsq : psiK ≤ (m / 4 + s / (2 * m)) ^ 2 := by
    nlinarith [sq_nonneg (m / 4 - s / (2 * m))]
  have hright : 0 ≤ m / 4 + s / (2 * m) := by positivity
  have hroot : Real.sqrt psiK ^ 2 = psiK := Real.sq_sqrt hpsi
  have henvelope : Real.sqrt psiK ≤ m / 4 + s / (2 * m) := by
    nlinarith
  rw [ccmActualHeadMatchedQuantileParabolicCenteredShift_eq_mass_centroid_decomposition]
  change -1 - m / 4 - s / (2 * m) ≤ -1 - Real.sqrt psiK
  linarith

private theorem eventually_psi_ge_subunit_scale (q : ℝ) (hq : q < 1) :
    ∀ᶠ K : ℕ in atTop,
      q * ((K + 2 : ℕ) : ℝ) ≤ Chebyshev.psi ((K + 2 : ℕ) : ℝ) := by
  have hindex : Tendsto (fun K : ℕ => ((K + 2 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have herror := tendsto_chebyshevError_div.comp hindex
  have hnear : ∀ᶠ x : ℝ in 𝓝 0, q - 1 < x :=
    eventually_gt_nhds (by linarith)
  filter_upwards [herror.eventually hnear] with K hK
  have hpos : 0 < ((K + 2 : ℕ) : ℝ) := by positivity
  unfold chebyshevError at hK
  have hmul := (lt_div_iff₀ hpos).mp hK
  linarith

/-- **Cofinal subunit terminal-scale law.** Every fixed terminal scale ratio
strictly below the physical head scale has eventually nonpositive literal
Route-P coefficient, uniformly over all integer terminal scales below it. -/
theorem speQuantileRiesz_terminalCoefficient_eventually_nonpos_below_subunit_scale
    (q : ℝ) (hq : q < 1) :
    ∀ᶠ K : ℕ in atTop, ∀ M : ℕ,
      (M : ℝ) ≤ q * ((K + 2 : ℕ) : ℝ) →
        Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ 0 := by
  filter_upwards [eventually_psi_ge_subunit_scale q hq] with K hqK M hM
  have hMpsi : (M : ℝ) ≤ Chebyshev.psi ((K + 2 : ℕ) : ℝ) :=
    hM.trans hqK
  have hroot := Real.sqrt_le_sqrt hMpsi
  have hshift := ccmActualHeadMatchedQuantileParabolicCenteredShift_le_neg_one_sub_sqrt_psi K
  linarith

/-- The strictly nonnegative local geometric correction left after comparing the
matched first moment to ordinary Chebyshev mass. -/
def ccmActualHeadMatchedCentroidChebyshevExcess (K : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (n + 2) * ccmActualHeadMatchedPolarCentroid (n + 2)) -
    2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ)

theorem ccmActualHeadMatchedCentroidChebyshevExcess_nonneg (K : ℕ) :
    0 ≤ ccmActualHeadMatchedCentroidChebyshevExcess K := by
  unfold ccmActualHeadMatchedCentroidChebyshevExcess
  linarith [ccmActualHeadMatchedCentroidAggregate_one_ge_two_mul_psi K]

/-- **Unit-scale compensated-error identity.** The sole unresolved physical
terminal coefficient is exactly a Chebyshev error, compensated by an explicit
mass mismatch square, nonnegative source-width excess, and positive mass term. -/
theorem ccmActualHeadMatchedQuantileParabolicUnitScaleCompensatedChebyshevIdentity (K : ℕ) :
    let m := ccmActualHeadParabolicMass K
    let r := Real.sqrt ((K + 2 : ℕ) : ℝ)
    let e := ccmActualHeadMatchedCentroidChebyshevExcess K
    4 * m * (-ccmActualHeadMatchedQuantileParabolicCenteredShift K - r) =
      (m - 2 * r) ^ 2 + 2 * e +
        4 * chebyshevError ((K + 2 : ℕ) : ℝ) + 4 * m := by
  dsimp
  rw [ccmActualHeadMatchedQuantileParabolicCenteredShift_eq_mass_centroid_decomposition]
  unfold ccmActualHeadMatchedCentroidChebyshevExcess chebyshevError
  have hmass : ccmActualHeadParabolicMass K ≠ 0 :=
    (ccmActualHeadParabolicMass_pos K).ne'
  have hroot : Real.sqrt ((K + 2 : ℕ) : ℝ) ^ 2 = ((K + 2 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  field_simp [hmass]
  nlinarith [hroot]

/-- **Exact unit-scale frontier.** The ratio-one Route-P coefficient is
nonpositive iff its compensated Chebyshev barrier is nonnegative.  Therefore
unit-scale control cannot be asserted from the PNT alone; it is precisely the
remaining signed arithmetic problem. -/
theorem speQuantileRiesz_terminalCoefficient_unitScale_nonpos_iff_compensatedChebyshev
    (K : ℕ) :
    Real.sqrt ((K + 2 : ℕ) : ℝ) +
        ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ 0 ↔
      0 ≤
        (ccmActualHeadParabolicMass K - 2 * Real.sqrt ((K + 2 : ℕ) : ℝ)) ^ 2 +
          2 * ccmActualHeadMatchedCentroidChebyshevExcess K +
          4 * chebyshevError ((K + 2 : ℕ) : ℝ) +
          4 * ccmActualHeadParabolicMass K := by
  rw [← ccmActualHeadMatchedQuantileParabolicUnitScaleCompensatedChebyshevIdentity]
  constructor
  · intro h
    have hmass : 0 ≤ ccmActualHeadParabolicMass K :=
      (ccmActualHeadParabolicMass_pos K).le
    have hterm : 0 ≤ -ccmActualHeadMatchedQuantileParabolicCenteredShift K -
        Real.sqrt ((K + 2 : ℕ) : ℝ) := by linarith
    positivity
  · intro h
    have hmass : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
    have hterm : 0 ≤ -ccmActualHeadMatchedQuantileParabolicCenteredShift K -
        Real.sqrt ((K + 2 : ℕ) : ℝ) := by
      nlinarith
    linarith

end RHTower
