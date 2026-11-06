import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffZeroSum
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffTailSmallness
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffShifts

/-!
# A quadratic positive region of the calibrated Hausdorff array

For sufficiently large order and saddle width, the positive core dominates
the complete complementary sum. The finitely many smaller orders are
covered by their existing explicit shift thresholds.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open _root_.RHTower

/-- A sufficiently broad saddle makes the complete calibrated entry nonnegative. -/
theorem exists_broad_saddle_nonneg :
    ∃ P : ℕ, 4 ≤ P ∧ ∃ W : ℝ, 32 ≤ W ∧ ∀ k r : ℕ, ∀ s w T : ℝ,
      P ≤ k + 1 → W ≤ w → w ≤ s → 500 ≤ T → 0 < r →
      ((k + 1 : ℕ) : ℝ) * (primeArchEndpointHausdorffRadius * s ^ 2 - 1) = r →
      200 * ((k + 1 : ℕ) : ℝ) ≤ r →
      ((k + 1 : ℕ) : ℝ) * w ^ 2 = s ^ 2 →
      10 * ((k + 1 : ℕ) : ℝ) * primeArchEndpointHausdorffRadius * T ^ 2 = r →
      0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment k r := by
  classical
  obtain ⟨C, hC, Sn, hSn, hnegative⟩ := exists_negative_sum_bound
  obtain ⟨Sc, hSc, Wc, hWc, hcount⟩ := exists_saddle_core_card_lower
  let L : ℝ := 131072 * (8000 * C)
  let Q : ℝ := 16384 * Real.exp 1 + 8
  obtain ⟨P, hP⟩ := exists_nat_ge (max 4 (max L (8000 * Q)))
  have hP4 : 4 ≤ P := by exact_mod_cast (le_max_left _ _).trans hP
  let W : ℝ := max 32 (max Wc (max (max Sn Sc) (L + 1)))
  refine ⟨P, hP4, W, le_max_left _ _, ?_⟩
  intro k r s w T hp hw hws hT hr hbalance hpr hwidth hthermal
  have hwp : 32 ≤ w := (le_max_left _ _).trans hw
  have hwc : Wc ≤ w := (le_max_left _ _).trans ((le_max_right _ _).trans hw)
  have hwm : max (max Sn Sc) (L + 1) ≤ w :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hw)
  have hwsn : Sn ≤ w := (le_max_left _ _).trans ((le_max_left _ _).trans hwm)
  have hwsc : Sc ≤ w := (le_max_right _ _).trans ((le_max_left _ _).trans hwm)
  have hwL : L + 1 ≤ w := (le_max_right _ _).trans hwm
  have hs0 : 0 < s := by linarith only [hwp, hws]
  have hw0 : 0 < w := by linarith only [hwp]
  have hpR : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hPcast : (P : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast hp
  have hpL : L ≤ ((k + 1 : ℕ) : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hP.trans hPcast))
  have hpQ : 8000 * Q ≤ ((k + 1 : ℕ) : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hP.trans hPcast))
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hwL2 : L ≤ w ^ 2 := by nlinarith only [hwL, hL0, sq_nonneg (w - 1)]
  have hgaussian := gaussian_factor_le (by linarith only [hC] : 0 < C) hpL hwL2
  have horder := order_tail_le_inverse (k + 1) (Nat.succ_pos k)
  have horderSmall : (16384 * Real.exp 1 + 8) / ((k + 1 : ℕ) : ℝ) ≤ 1 / 8000 := by
    rw [div_le_iff₀ hpR]
    change 8000 * (16384 * Real.exp 1 + 8) ≤ ((k + 1 : ℕ) : ℝ) at hpQ
    linarith only [hpQ]
  have horder' := horder.trans horderSmall
  have hheight := height_le_order_mul_width hs0 hw0.le (Nat.succ_le_succ (Nat.zero_le k)) hwidth
  let M := realKernel primeArchEndpointHausdorffRadius (k + 1) r s
  have hM : 0 < M := realKernel_saddle_pos hs0 (Nat.succ_pos k) hr hbalance
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hwp, hws])
  let V := M * w * Real.log s
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfinite := hnegative s w T k r (hwsn.trans hws) hwp hws hT (hP4.trans hp)
    hr hbalance hpr hwidth hthermal
  have htotal := (summable_negativeAtom primeArchEndpointHausdorffRadius k r).tsum_le_of_sum_le hfinite
  have hfar := mul_le_mul_of_nonneg_left hheight
    (show 0 ≤ 4096 * Real.exp 1 * M * Real.log s * (4 : ℝ)⁻¹ ^ (k + 1) by positivity)
  have hlow := mul_le_mul_of_nonneg_left hheight
    (show 0 ≤ 2 * M * Real.log s * Real.exp (-4 * ((k + 1 : ℕ) : ℝ)) by positivity)
  have hgaussian' := mul_le_mul_of_nonneg_left hgaussian hV
  have horder'' := mul_le_mul_of_nonneg_left horder' hV
  have hnegativeSmall : (∑' q, negativeAtom primeArchEndpointHausdorffRadius k r q) ≤ V / 4000 := by
    dsimp [V, M] at hgaussian' horder'' hfar hlow ⊢
    nlinarith only [htotal, hfar, hlow, hgaussian', horder'']
  let B := xiCopiesBand (s - w / 10) (s + w / 10)
  have hBcard := hcount s w (hwsc.trans hws) hwc hws
  have hBterm : ∀ q ∈ B, M / 2 ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    have hq' := mem_xiCopiesBand.mp hq
    have hdist : |( |(q.1 : ℂ).im| - s)| ≤ w / 10 := by
      apply abs_le.mpr
      constructor <;> linarith only [hq'.1, hq'.2]
    obtain ⟨y, hy, heq⟩ := atom_eq_kernel_abs_ordinate primeArchEndpointHausdorffRadius k r q
    rw [heq]
    have h := half_saddle_le_re_kernel hs0 (Nat.succ_pos k) hr
      (by linarith only [hpr, hpR]) hbalance hwidth hwp hws hdist hy
    change M / 2 ≤ _
    nlinarith only [h]
  have hBsum := Finset.sum_le_sum hBterm
  simp only [Finset.sum_const, nsmul_eq_mul] at hBsum
  have hBcard' := mul_le_mul_of_nonneg_right hBcard (show 0 ≤ M / 2 by positivity)
  have hcore : V / 2000 ≤ ∑ q ∈ B, (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    dsimp [V]
    change w * Real.log s / 1000 * (M / 2) ≤ (B.card : ℝ) * (M / 2) at hBcard'
    nlinarith only [hBsum, hBcard']
  have hsource := core_sum_le_source_add_negative primeArchEndpointHausdorffRadius k r B
  nlinarith only [hcore, hsource, hnegativeSmall, hV]

/-- One quadratic shift bound certifies all orders of the actual calibrated Hausdorff array. -/
theorem exists_quadratic_scaledHausdorffMomentDifference_nonneg :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, C * (((k + 1 : ℕ) : ℝ) ^ 2) ≤ r →
      0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment k r := by
  classical
  obtain ⟨P, hP, W, hW, hmain⟩ := exists_broad_saddle_nonneg
  let R := primeArchEndpointHausdorffRadius
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  let H : ℕ := ∑ k ∈ Finset.range P, explicitPrimeArchHausdorffShift k
  let C : ℝ := max 200 (max (R * W ^ 2) (max (2500000 * R) (H : ℝ)))
  have hC200 : 200 ≤ C := le_max_left _ _
  have hCW : R * W ^ 2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT : 2500000 * R ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCH : (H : ℝ) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC : 0 < C := by linarith only [hC200]
  refine ⟨C, hC, ?_⟩
  intro k r hshift
  have hp1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hp0 : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hp2 : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith only [hp1, sq_nonneg (((k + 1 : ℕ) : ℝ) - 1)]
  have hp21 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := hp1.trans hp2
  have hpr : 200 * ((k + 1 : ℕ) : ℝ) ≤ r := by
    have h := mul_le_mul_of_nonneg_right hC200 (sq_nonneg ((k + 1 : ℕ) : ℝ))
    nlinarith only [h, hshift, hp2]
  have hr0 : 0 < (r : ℝ) := by linarith only [hpr, hp0]
  have hr : 0 < r := by exact_mod_cast hr0
  by_cases hp : P ≤ k + 1
  · let s := Real.sqrt ((((k + 1 : ℕ) : ℝ) + r) / (((k + 1 : ℕ) : ℝ) * R))
    let w := Real.sqrt ((((k + 1 : ℕ) : ℝ) + r) / (((k + 1 : ℕ) : ℝ) ^ 2 * R))
    let T := Real.sqrt ((r : ℝ) / (10 * ((k + 1 : ℕ) : ℝ) * R))
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hw0 : 0 < w := Real.sqrt_pos.mpr (by positivity)
    have hT0 : 0 < T := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = (((k + 1 : ℕ) : ℝ) + r) / (((k + 1 : ℕ) : ℝ) * R) :=
      Real.sq_sqrt (by positivity)
    have hw2 : w ^ 2 = (((k + 1 : ℕ) : ℝ) + r) / (((k + 1 : ℕ) : ℝ) ^ 2 * R) :=
      Real.sq_sqrt (by positivity)
    have hT2 : T ^ 2 = (r : ℝ) / (10 * ((k + 1 : ℕ) : ℝ) * R) :=
      Real.sq_sqrt (by positivity)
    have hbalance : ((k + 1 : ℕ) : ℝ) * (R * s ^ 2 - 1) = r := by
      rw [hs2]
      field_simp [hp0.ne', hR.ne']
      ring
    have hwidth : ((k + 1 : ℕ) : ℝ) * w ^ 2 = s ^ 2 := by
      rw [hs2, hw2]
      field_simp [hp0.ne', hR.ne']
    have hthermal : 10 * ((k + 1 : ℕ) : ℝ) * R * T ^ 2 = r := by
      rw [hT2]
      field_simp [hp0.ne', hR.ne']
    have hwW : W ≤ w := by
      apply (sq_le_sq₀ (by linarith only [hW]) hw0.le).mp
      rw [hw2, le_div_iff₀ (by positivity : 0 < ((k + 1 : ℕ) : ℝ) ^ 2 * R)]
      have h := mul_le_mul_of_nonneg_right hCW (sq_nonneg ((k + 1 : ℕ) : ℝ))
      nlinarith only [h, hshift, hp0]
    have hT500 : 500 ≤ T := by
      apply (sq_le_sq₀ (by norm_num) hT0.le).mp
      rw [hT2, le_div_iff₀ (by positivity : 0 < 10 * ((k + 1 : ℕ) : ℝ) * R)]
      have h₁ := mul_le_mul_of_nonneg_right hCT (sq_nonneg ((k + 1 : ℕ) : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 2500000 * R by positivity)
      nlinarith only [h₁, h₂, hshift]
    have hws := saddle_width_le_height hs0 hw0.le (Nat.succ_le_succ (Nat.zero_le k)) hwidth
    exact hmain k r s w T hp hwW hws hT500 hr hbalance hpr hwidth hthermal
  · have hkP : k < P := by omega
    have hkH : explicitPrimeArchHausdorffShift k ≤ H :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hkP)
    have hkHR : (explicitPrimeArchHausdorffShift k : ℝ) ≤ H := by exact_mod_cast hkH
    have hCr : C ≤ (r : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hp21 hC.le
      nlinarith only [h, hshift]
    have hkr : explicitPrimeArchHausdorffShift k ≤ r := by
      exact_mod_cast hkHR.trans (hCH.trans hCr)
    exact scaledHausdorffMomentDifference_nonneg_of_explicit_shift_le k r hkr

#print axioms exists_broad_saddle_nonneg
#print axioms exists_quadratic_scaledHausdorffMomentDifference_nonneg

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
