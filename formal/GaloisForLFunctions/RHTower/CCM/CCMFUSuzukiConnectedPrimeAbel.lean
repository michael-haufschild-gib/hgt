import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiConnectedSixthJet
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeAbelCompleteness

/-!
# Literal connected Suzuki prime channel in the Abel half-plane

The connected multiplier changes the actual prime Dirichlet coefficients, not merely a
model sequence. Their absolute convergence and Abel identity are proved on the safe
Euler half-plane. The completed signed source still requires the polar lane.
-/

open Complex Filter Set Topology MeasureTheory

namespace RHTower

noncomputable section

def ccmSuzukiConnectedPrimeDirichletCoeff (b ω : ℝ) (n : ℕ) : ℂ :=
  ccmGuinandWeilThirdGradePrimeDirichletCoeff b n *
    (shiftedEulerLogConnectedThirdMultiplier ω (Real.log n) : ℂ)

private theorem ccmSuzukiConnected_multiplier_le_exp
    {ω h : ℝ} (hω : 0 < ω) (hh : 0 < h) :
    shiftedEulerLogConnectedThirdMultiplier ω h ≤ Real.exp (ω * h) := by
  have hle := shiftedEulerLogConnectedThirdMultiplier_le_cosh hω hh
  have harg : 0 ≤ ω * h := (mul_pos hω hh).le
  have hexp : Real.exp (-(ω * h)) ≤ Real.exp (ω * h) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    shiftedEulerLogConnectedThirdMultiplier ω h ≤ Real.cosh (ω * h) := hle
    _ ≤ Real.exp (ω * h) := by rw [Real.cosh_eq]; linarith

theorem norm_ccmSuzukiConnectedPrimeDirichletCoeff_le_rpow
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω) (n : ℕ) :
    ‖ccmSuzukiConnectedPrimeDirichletCoeff b ω n‖ ≤
      (32 / b ^ (2 : ℕ)) * (n : ℝ) ^ ω := by
  by_cases hbn : b < Real.log n
  · have hlog : 0 < Real.log n := hb.trans hbn
    have hn1 : 1 < n :=
      Nat.one_lt_cast.mp ((Real.log_pos_iff (by positivity)).mp hlog)
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hm0 := shiftedEulerLogConnectedThirdMultiplier_nonneg hω hlog
    have hm := ccmSuzukiConnected_multiplier_le_exp hω hlog
    have hcoeff := norm_ccmGuinandWeilThirdGradePrimeDirichletCoeff_le hb n
    rw [ccmSuzukiConnectedPrimeDirichletCoeff, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hm0]
    calc
      ‖ccmGuinandWeilThirdGradePrimeDirichletCoeff b n‖ *
          shiftedEulerLogConnectedThirdMultiplier ω (Real.log n) ≤
        (32 / b ^ (2 : ℕ)) *
          shiftedEulerLogConnectedThirdMultiplier ω (Real.log n) :=
        mul_le_mul_of_nonneg_right hcoeff hm0
      _ ≤ (32 / b ^ (2 : ℕ)) * Real.exp (ω * Real.log n) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (32 / b ^ (2 : ℕ)) * (n : ℝ) ^ ω := by
        rw [Real.rpow_def_of_pos hnPos]
        congr 1
        ring
  · simp [ccmSuzukiConnectedPrimeDirichletCoeff,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff, hbn]
    positivity

theorem abscissa_ccmSuzukiConnectedPrimeDirichletCoeff_le
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω) :
    LSeries.abscissaOfAbsConv (ccmSuzukiConnectedPrimeDirichletCoeff b ω) ≤ ω + 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (x := ω)
  refine ⟨32 / b ^ (2 : ℕ), ?_⟩
  intro n _
  exact norm_ccmSuzukiConnectedPrimeDirichletCoeff_le_rpow hb hω n

theorem ccmSuzukiConnectedPrimeDirichletCoeff_sum_norm_isBigO
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ‖ccmSuzukiConnectedPrimeDirichletCoeff b ω k‖) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (ω + 1)) := by
  let C : ℝ := 32 / b ^ (2 : ℕ)
  refine Asymptotics.IsBigO.of_bound C
    (Filter.Eventually.of_forall fun n => ?_)
  by_cases hn : n = 0
  · subst n
    simp [C]
    positivity
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hcalc :
      ∑ k ∈ Finset.Icc 1 n, ‖ccmSuzukiConnectedPrimeDirichletCoeff b ω k‖ ≤
        C * (n : ℝ) ^ (ω + 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 n, C * (k : ℝ) ^ ω := by
        apply Finset.sum_le_sum
        intro k _
        exact norm_ccmSuzukiConnectedPrimeDirichletCoeff_le_rpow hb hω k
      _ ≤ ∑ _k ∈ Finset.Icc 1 n, C * (n : ℝ) ^ ω := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg k)
            (by exact_mod_cast hkn) hω.le) (by positivity)
      _ = C * (n : ℝ) ^ ω * (n : ℝ) := by
        simp [Nat.card_Icc, nsmul_eq_mul]
        ring
      _ = C * (n : ℝ) ^ (ω + 1) := by
        rw [Real.rpow_add hnPos, Real.rpow_one]
        ring
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (ω + 1))]
  exact hcalc

def ccmSuzukiConnectedPrimeRateWindow (b ω H : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.exp H⌋₊, ccmSuzukiConnectedPrimeDirichletCoeff b ω k

theorem ccmSuzukiConnectedPrimeRateWindow_eq_literalPrime
    {b H : ℝ} (hb : 0 < b) (hH : 0 < H) (ω : ℝ) :
    ccmSuzukiConnectedPrimeRateWindow b ω H =
      ((∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k *
            ccmSuzukiConnectedThirdGradeWeight ω (Real.log k)
        else 0) : ℂ) := by
  have hm : 1 ≤ ⌊Real.exp H⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_exp hH.le)
  rw [ccmSuzukiConnectedPrimeRateWindow,
    ← Finset.insert_Icc_add_one_left_eq_Icc hm,
    Finset.sum_insert (by simp)]
  have hone : ccmSuzukiConnectedPrimeDirichletCoeff b ω 1 = 0 := by
    simp [ccmSuzukiConnectedPrimeDirichletCoeff,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff,
      not_lt.mpr hb.le]
  rw [hone, zero_add]
  simp only [Nat.reduceAdd]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k
  · simp only [hbk, if_true, ccmSuzukiConnectedPrimeDirichletCoeff,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff]
    rw [ccmSuzukiConnectedThirdGradeWeight,
      ← criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale]
    push_cast
    ring
  · simp [ccmSuzukiConnectedPrimeDirichletCoeff,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff, hbk]

theorem ccmSuzukiConnectedPrimeRateWindow_eq_zero_of_le
    {b ω H : ℝ} (hHb : H ≤ b) :
    ccmSuzukiConnectedPrimeRateWindow b ω H = 0 := by
  rw [ccmSuzukiConnectedPrimeRateWindow]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    have hk1 : 1 ≤ (0 : ℕ) := (Finset.mem_Icc.mp hk).1
    omega
  rw [ccmSuzukiConnectedPrimeDirichletCoeff,
    ccmGuinandWeilThirdGradePrimeDirichletCoeff, if_neg]
  · ring
  intro hbk
  have hkfloor : k ≤ ⌊Real.exp H⌋₊ := (Finset.mem_Icc.mp hk).2
  have hkexp : (k : ℝ) ≤ Real.exp H :=
    (Nat.cast_le.mpr hkfloor).trans (Nat.floor_le (Real.exp_pos H).le)
  have hHlog : H < Real.log k := hHb.trans_lt hbk
  have hexplt : Real.exp H < (k : ℝ) := by
    calc
      Real.exp H < Real.exp (Real.log k) := Real.exp_lt_exp.mpr hHlog
      _ = (k : ℝ) := Real.exp_log (by positivity)
  exact (not_lt_of_ge hkexp) hexplt

theorem LSeries_ccmSuzukiConnectedPrimeDirichletCoeff_eq_abel
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {u : ℂ} (hu : ω + 1 < u.re) :
    LSeries (ccmSuzukiConnectedPrimeDirichletCoeff b ω) u =
      u * ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) * ccmSuzukiConnectedPrimeRateWindow b ω H := by
  have hmain := LSeries_eq_mul_integral'
    (ccmSuzukiConnectedPrimeDirichletCoeff b ω)
    (r := ω + 1) (by linarith : 0 ≤ ω + 1) hu
    (ccmSuzukiConnectedPrimeDirichletCoeff_sum_norm_isBigO hb hω)
  rw [hmain]
  congr 1
  let g : ℝ → ℂ := fun t =>
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
      ccmSuzukiConnectedPrimeDirichletCoeff b ω k) *
        (t : ℂ) ^ (-(u + 1))
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun x _ => Real.hasDerivAt_exp x |>.hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [Real.image_exp_Ioi, Real.exp_zero] at hchange
  change (∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
        ccmSuzukiConnectedPrimeDirichletCoeff b ω k) * (t : ℂ) ^ (-(u + 1))) = _
  calc
    (∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
        ccmSuzukiConnectedPrimeDirichletCoeff b ω k) * (t : ℂ) ^ (-(u + 1))) =
        ∫ H : ℝ in Set.Ioi 0, |Real.exp H| • g (Real.exp H) := hchange
    _ = ∫ H : ℝ in Set.Ioi 0,
        Complex.exp (-u * (H : ℂ)) * ccmSuzukiConnectedPrimeRateWindow b ω H := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro H hH
      dsimp only [g, ccmSuzukiConnectedPrimeRateWindow]
      rw [abs_of_pos (Real.exp_pos H), Complex.real_smul]
      rw [← mul_assoc, mul_comm (Real.exp H : ℂ), mul_assoc,
        exp_mul_cpow_neg_add_one]
      ring
    _ = ∫ H : ℝ in Set.Ioi b,
        Complex.exp (-u * (H : ℂ)) * ccmSuzukiConnectedPrimeRateWindow b ω H := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
        ← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with H
      by_cases hbH : b < H
      · have hH0 : 0 < H := hb.trans hbH
        simp [hbH, hH0]
      · by_cases hH0 : 0 < H
        · have hz := ccmSuzukiConnectedPrimeRateWindow_eq_zero_of_le
            (ω := ω) (le_of_not_gt hbH)
          simp [hbH, hH0, hz]
        · simp [hbH, hH0]

end

end RHTower
