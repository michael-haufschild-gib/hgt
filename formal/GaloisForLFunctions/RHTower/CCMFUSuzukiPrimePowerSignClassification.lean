import GaloisForLFunctions.RHTower.CCMFUSuzukiGammaBinetCofinalBridge
import GaloisForLFunctions.HTGeometry.NearDiagonalParity

noncomputable section

namespace RHTower

open MeasureTheory Set
open GaloisForLFunctions.RHTower
open scoped Interval

theorem sqrt_endpoint_data {k : ℕ} (hk : 4 ≤ k) :
    let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
    let b := Real.sqrt (k : ℝ)
    0 < a ∧ 0 < b ∧ a ≤ b ∧
      (b - a) * (b + a) = 1 ∧ 23 * b ≤ 27 * a := by
  dsimp
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have ha := Real.sqrt_pos.mpr hpredpos
  have hb := Real.sqrt_pos.mpr hkpos
  have ha2 := Real.sq_sqrt hpredpos.le
  have hb2 := Real.sq_sqrt hkpos.le
  have hpredle : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.sub_le k 1)
  have hab := Real.sqrt_le_sqrt hpredle
  have hpoly : (729 : ℝ) ≤ 200 * (k : ℝ) := by nlinarith
  have hratioSq : (23 * Real.sqrt (k : ℝ)) ^ (2 : ℕ) ≤
      (27 * Real.sqrt ((k - 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    rw [mul_pow, mul_pow, ha2, hb2, hcast]
    norm_num
    nlinarith
  have hratio : 23 * Real.sqrt (k : ℝ) ≤
      27 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
    nlinarith [sq_nonneg
      (23 * Real.sqrt (k : ℝ) + 27 * Real.sqrt ((k - 1 : ℕ) : ℝ))]
  refine ⟨ha, hb, hab, ?_, hratio⟩
  nlinarith

theorem integral_screwRegularKernel_checkpoint_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      screwRegularKernel t := by
  have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hloglt : Real.log ((k - 1 : ℕ) : ℝ) < Real.log (k : ℝ) := by
    rw [Real.strictMonoOn_log.lt_iff_lt hpredpos hkpos]
    exact_mod_cast (by omega : k - 1 < k)
  have hlog2 : Real.log 2 ≤ Real.log ((k - 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hpredpos
    · exact_mod_cast (by omega : 2 ≤ k - 1)
  apply intervalIntegral.integral_pos hloglt
  · exact continuousOn_screwRegularKernel.mono fun t ht =>
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le (hlog2.trans ht.1)
  · intro t ht
    exact (suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le
      (hlog2.trans ht.1.le)).le
  · refine ⟨Real.log (k : ℝ), ⟨hloglt.le, le_rfl⟩, ?_⟩
    exact suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le
      (hlog2.trans hloglt.le)

/-- The regular curvature carried by one source-valid checkpoint cell is at
most its explicit exponential-half cell mass. -/
theorem integral_screwRegularKernel_checkpoint_upper {k : ℕ} (hk : 3 ≤ k) :
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t) ≤
      2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) := by
  have htail := (suzukiCheckpointWeightedArchTailCell_nonneg_le hk).1
  have htail0 : 0 ≤
      ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        suzukiCheckpointArchTail t := by
    have hkR : (0 : ℝ) < (k : ℝ) := by positivity
    nlinarith
  rw [integral_screwRegularKernel_eq_expHalf_sub_archTail hk]
  have hexp := integral_exp_half_log_cell (k := k - 1) (by omega : 1 ≤ k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hexp
  rw [hexp]
  linarith

/-- A signed curvature cell is bounded above by its smooth exponential-half
budget minus the literal prime atom at its endpoint. -/
theorem suzukiCheckpointSignedCurvatureCell_le_expHalfGap
    {k : ℕ} (hk : 3 ≤ k) :
    suzukiCheckpointSignedCurvatureCell (k - 1) ≤
      2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - criticalMellinAtomWeight k := by
  unfold suzukiCheckpointSignedCurvatureCell
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  linarith [integral_screwRegularKernel_checkpoint_upper hk]

/-- **Finite-block source budget.**  Starting at any source-valid endpoint,
the literal signed curvature over that endpoint and any finite forward block
is no larger than the telescoped smooth square-root gain minus the first
prime atom.  Thus later prime atoms cannot pay an earlier prime jump; every
possible payment is already contained in the displayed regular budget. -/
theorem suzukiCheckpointSignedCurvature_forwardBlock_le
    {k m : ℕ} (hk : 3 ≤ k) :
    suzukiCheckpointSignedCurvatureCell (k - 1) +
        ∑ j ∈ Finset.range m, suzukiCheckpointSignedCurvatureCell (k + j) ≤
      2 * (Real.sqrt (k + m : ℕ) - Real.sqrt (k - 1 : ℕ)) -
        criticalMellinAtomWeight k := by
  induction m with
  | zero =>
      simpa using suzukiCheckpointSignedCurvatureCell_le_expHalfGap hk
  | succ m ih =>
      have hkm : 3 ≤ k + m + 1 := by omega
      have hcell := suzukiCheckpointSignedCurvatureCell_le_expHalfGap hkm
      have hweight : 0 ≤ criticalMellinAtomWeight (k + m + 1) := by
        exact criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
      have hnext : suzukiCheckpointSignedCurvatureCell (k + m) ≤
          2 * (Real.sqrt (k + m + 1 : ℕ) - Real.sqrt (k + m : ℕ)) := by
        simpa only [Nat.add_sub_cancel] using hcell.trans (sub_le_self _ hweight)
      rw [Finset.sum_range_succ]
      calc
        suzukiCheckpointSignedCurvatureCell (k - 1) +
            ((∑ j ∈ Finset.range m, suzukiCheckpointSignedCurvatureCell (k + j)) +
              suzukiCheckpointSignedCurvatureCell (k + m)) =
          (suzukiCheckpointSignedCurvatureCell (k - 1) +
            ∑ j ∈ Finset.range m, suzukiCheckpointSignedCurvatureCell (k + j)) +
              suzukiCheckpointSignedCurvatureCell (k + m) := by ring
        _ ≤ (2 * (Real.sqrt (k + m : ℕ) - Real.sqrt (k - 1 : ℕ)) -
              criticalMellinAtomWeight k) +
            2 * (Real.sqrt (k + m + 1 : ℕ) - Real.sqrt (k + m : ℕ)) :=
          add_le_add ih hnext
        _ = 2 * (Real.sqrt (k + (m + 1) : ℕ) - Real.sqrt (k - 1 : ℕ)) -
              criticalMellinAtomWeight k := by
          push_cast
          ring

/-- A finite forward block stays strictly negative whenever its exposed first
atom exceeds the full smooth budget available through the block endpoint. -/
theorem suzukiCheckpointSignedCurvature_forwardBlock_neg_of_atom_gt
    {k m : ℕ} (hk : 3 ≤ k)
    (hbudget : 2 * (Real.sqrt (k + m : ℕ) - Real.sqrt (k - 1 : ℕ)) <
      criticalMellinAtomWeight k) :
    suzukiCheckpointSignedCurvatureCell (k - 1) +
        ∑ j ∈ Finset.range m, suzukiCheckpointSignedCurvatureCell (k + j) < 0 := by
  have hbound := suzukiCheckpointSignedCurvature_forwardBlock_le (m := m) hk
  linarith

theorem integral_screwRegularKernel_checkpoint_lower {k : ℕ} (hk : 4 ≤ k) :
    (4 / 5 : ℝ) / Real.sqrt k ≤
      ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t := by
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  obtain ⟨ha, hb, hab, hgap, _⟩ := sqrt_endpoint_data hk
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ha2 : a ^ (2 : ℕ) = ((k - 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ (2 : ℕ) = (k : ℝ) := Real.sq_sqrt (by positivity)
  have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hgap0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hexpLower : 1 / b ≤ 2 * (b - a) := by
    rw [div_le_iff₀ hb]
    nlinarith
  have hprodSq : (b * a) ^ (2 : ℕ) = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    rw [mul_pow, hb2, ha2]
  have hpoly : (100 : ℝ) ≤ 9 * (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    rw [hcast]
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (by linarith : 0 ≤ (k : ℝ) + 3)]
  have hprod : 10 ≤ 3 * b * a := by
    have hsq : (100 : ℝ) ≤ (3 * b * a) ^ (2 : ℕ) := by
      rw [show (3 * b * a) ^ (2 : ℕ) = 9 * (b * a) ^ (2 : ℕ) by ring, hprodSq]
      simpa only [mul_assoc] using hpoly
    nlinarith [mul_nonneg hb.le ha.le]
  have hbBudget : b ≤ (3 / 10 : ℝ) * (k : ℝ) * a := by
    have hm := mul_le_mul_of_nonneg_left hprod hb.le
    nlinarith [hm, hb2]
  let T := ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
    suzukiCheckpointArchTail t
  have htail := suzukiCheckpointWeightedArchTailCell_nonneg_le (k := k) (by omega : 3 ≤ k)
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    nlinarith [htail.1]
  have hTa : (k : ℝ) * T * a ≤ 2 / 3 := by
    have hm := mul_le_mul_of_nonneg_right htail.2 ha.le
    change (k : ℝ) * T * a ≤ (2 / 3 : ℝ) * a⁻¹ * a at hm
    calc
      (k : ℝ) * T * a ≤ (2 / 3 : ℝ) * a⁻¹ * a := hm
      _ = 2 / 3 := by
        rw [show (2 / 3 : ℝ) * a⁻¹ * a = (2 / 3 : ℝ) * (a⁻¹ * a) by ring,
          inv_mul_cancel₀ ha.ne', mul_one]
  have hTb : T * b ≤ 1 / 5 := by
    have hm := mul_le_mul_of_nonneg_left hbBudget hT0
    nlinarith
  have hTUpper : T ≤ (1 / 5 : ℝ) / b := by
    rw [le_div_iff₀ hb]
    exact hTb
  rw [integral_screwRegularKernel_eq_expHalf_sub_archTail (by omega : 3 ≤ k)]
  have hexp := integral_exp_half_log_cell (k := k - 1) (by omega : 1 ≤ k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hexp
  change _ ≤ _ - T
  rw [hexp]
  change (4 / 5 : ℝ) / b ≤ 2 * (b - a) - T
  have hsplit : (4 / 5 : ℝ) / b + (1 / 5 : ℝ) / b = 1 / b := by ring
  linarith

theorem expHalf_checkpoint_scaled_le {k : ℕ} (hk : 4 ≤ k) :
    2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) * Real.sqrt k ≤ 27 / 25 := by
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  obtain ⟨ha, hb, hab, hgap, hratio⟩ := sqrt_endpoint_data hk
  have hgap0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlinear : 50 * b ≤ 27 * (b + a) := by linarith
  have hm := mul_le_mul_of_nonneg_right hlinear hgap0
  change 2 * (b - a) * b ≤ (27 / 25 : ℝ)
  nlinarith

theorem suzukiCheckpointSignedCurvatureCell_pos_of_not_primePower
    {k : ℕ} (hk : 3 ≤ k) (hnot : ¬ IsPrimePow k) :
    0 < suzukiCheckpointSignedCurvatureCell (k - 1) := by
  have hvm : ArithmeticFunction.vonMangoldt k = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot
  unfold suzukiCheckpointSignedCurvatureCell
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
  simp only [zero_div, sub_zero]
  exact integral_screwRegularKernel_checkpoint_pos hk

theorem suzukiCheckpointSignedCurvatureCell_pos_of_even_endpoint
    {k : ℕ} (hk : 4 ≤ k) (heven : Even k) :
    0 < suzukiCheckpointSignedCurvatureCell (k - 1) := by
  by_cases hvm : ArithmeticFunction.vonMangoldt k = 0
  · unfold suzukiCheckpointSignedCurvatureCell
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
    simp only [zero_div, sub_zero]
    exact integral_screwRegularKernel_checkpoint_pos (by omega)
  · obtain ⟨e, he, hpow⟩ :=
      GaloisForLFunctions.HTGeometry.exists_pow_two_of_even_of_vonMangoldt_ne_zero heven hvm
    have hvmEq : ArithmeticFunction.vonMangoldt k = Real.log 2 := by
      rw [hpow, ArithmeticFunction.vonMangoldt_apply_pow he.ne',
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hlog : Real.log 2 < (7 / 10 : ℝ) :=
      Real.log_two_lt_d9.trans (by norm_num)
    have hlower := integral_screwRegularKernel_checkpoint_lower hk
    unfold suzukiCheckpointSignedCurvatureCell
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvmEq]
    have hscaled : Real.log 2 / Real.sqrt (k : ℝ) <
        (4 / 5 : ℝ) / Real.sqrt (k : ℝ) := by
      exact (div_lt_div_iff_of_pos_right hsqrt).mpr (by linarith)
    linarith

theorem suzukiCheckpointSignedCurvatureCell_neg_of_odd_primePower_endpoint
    {k : ℕ} (hk : 4 ≤ k) (hodd : Odd k) (hpp : IsPrimePow k) :
    suzukiCheckpointSignedCurvatureCell (k - 1) < 0 := by
  obtain ⟨p, e, hp, he, hpow⟩ := (isPrimePow_nat_iff k).mp hpp
  have hpOdd : Odd p := by
    rw [← Nat.odd_pow_iff he.ne', hpow]
    exact hodd
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpOdd
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hlog : Real.log 3 ≤ Real.log (p : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hpR
    · exact_mod_cast hp3
  have hvm : ArithmeticFunction.vonMangoldt k = Real.log p := by
    rw [← hpow, ArithmeticFunction.vonMangoldt_apply_pow he.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hupper := integral_screwRegularKernel_checkpoint_upper (by omega : 3 ≤ k)
  have hscale := expHalf_checkpoint_scaled_le hk
  have hintScaled :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          screwRegularKernel t) * Real.sqrt k ≤ 27 / 25 := by
    exact (mul_le_mul_of_nonneg_right hupper hsqrt.le).trans hscale
  have hstrict :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          screwRegularKernel t) * Real.sqrt k < Real.log p := by
    have hconst : (27 / 25 : ℝ) < Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    exact hintScaled.trans_lt (hconst.trans_le hlog)
  have hdiv :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          screwRegularKernel t) < Real.log p / Real.sqrt k := by
    exact (lt_div_iff₀ hsqrt).mpr hstrict
  unfold suzukiCheckpointSignedCurvatureCell
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
  linarith

theorem suzukiCheckpointSignedCurvatureCell_neg_iff_odd_primePower_endpoint
    {k : ℕ} (hk : 4 ≤ k) :
    suzukiCheckpointSignedCurvatureCell (k - 1) < 0 ↔
      Odd k ∧ IsPrimePow k := by
  constructor
  · intro hneg
    by_contra hnot
    rw [not_and_or] at hnot
    rcases hnot with hnotOdd | hnotPP
    · have heven : Even k := Nat.not_odd_iff_even.mp hnotOdd
      linarith [suzukiCheckpointSignedCurvatureCell_pos_of_even_endpoint hk heven]
    · linarith [suzukiCheckpointSignedCurvatureCell_pos_of_not_primePower
        (by omega : 3 ≤ k) hnotPP]
  · rintro ⟨hodd, hpp⟩
    exact suzukiCheckpointSignedCurvatureCell_neg_of_odd_primePower_endpoint hk hodd hpp

theorem suzukiCheckpointSignedCurvatureCell_pos_iff_not_odd_primePower_endpoint
    {k : ℕ} (hk : 4 ≤ k) :
    0 < suzukiCheckpointSignedCurvatureCell (k - 1) ↔
      ¬(Odd k ∧ IsPrimePow k) := by
  constructor
  · intro hpos hbad
    have hneg :=
      (suzukiCheckpointSignedCurvatureCell_neg_iff_odd_primePower_endpoint hk).2 hbad
    linarith
  · intro hnot
    by_cases hodd : Odd k
    · exact suzukiCheckpointSignedCurvatureCell_pos_of_not_primePower
        (by omega : 3 ≤ k) (fun hpp => hnot ⟨hodd, hpp⟩)
    · exact suzukiCheckpointSignedCurvatureCell_pos_of_even_endpoint hk
        (Nat.not_odd_iff_even.mp hodd)

theorem ccmSuzukiPrimePolarGammaCurvatureCell_neg_iff_odd_primePower_endpoint
    {k : ℕ} (hk : 4 ≤ k) :
    ccmSuzukiPrimePolarGammaCurvatureCell (k - 1) < 0 ↔
      Odd k ∧ IsPrimePow k := by
  rw [← suzukiCheckpointSignedCurvatureCell_eq_primePolarGamma
    (N := k - 1) (by omega : 2 ≤ k - 1)]
  exact suzukiCheckpointSignedCurvatureCell_neg_iff_odd_primePower_endpoint hk

theorem suzukiCheckpointAffineSlope_strictAntiMonotone_iff_odd_primePower_endpoint
    {k : ℕ} (hk : 4 ≤ k) :
    suzukiCheckpointAffineSlope k < suzukiCheckpointAffineSlope (k - 1) ↔
      Odd k ∧ IsPrimePow k := by
  rw [← suzukiCheckpointSignedCurvatureCell_neg_iff_odd_primePower_endpoint hk]
  have hjump := suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell
    (N := k - 1) (by omega : 2 ≤ k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hjump
  constructor <;> intro h <;> linarith

end RHTower
