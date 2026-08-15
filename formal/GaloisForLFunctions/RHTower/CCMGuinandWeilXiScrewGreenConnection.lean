import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCompletedConnection
import GaloisForLFunctions.RHTower.SuzukiExplicitScrewZeroSeries
import GaloisForLFunctions.RHTower.SuzukiOriginRemainderFirstJet
import GaloisForLFunctions.RHTower.SuzukiScrewDistributionalKernel

/-!
# Completed Guinand–Weil third grade as Xi-screw Green curvature

This module identifies the literal Xi zero-divisor object carried by the completed
four-unit source.  On positive time, Suzuki's screw is a smooth polar--Gamma sector
minus prime hinges.  Its canonical right slope therefore records completed-error
current, while its affine codiagonal is the Green primitive of the completed source.

Two integrations by parts give the universal finite-window law

`source(F) = -F(H) ΔΨ'₊ + F'(H) C_b(H) - ∫_[b,H] C_b(h) F''(h) dh`.

For the forced inverse-cubic aperture, this becomes an exact Xi-screw Green formula.
Consequently convergence of the completed third-grade rate is equivalent, without
any analytic assumption, to convergence of that zero-divisor Green functional.
-/

open scoped BigOperators Interval
open MeasureTheory Set Finset Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Smooth part of Suzuki's positive-time Xi screw, before subtracting prime hinges. -/
def ccmGuinandWeilXiScrewSmoothPart (h : ℝ) : ℝ :=
  4 * Real.exp (h / 2) + 4 * Real.exp (-(h / 2)) - 8 +
    screwLinearCoeff / 2 * h + screwLerchConst - screwLerchTail h

/-- Classical slope of the smooth part of Suzuki's positive-time Xi screw. -/
def ccmGuinandWeilXiScrewSmoothSlope (h : ℝ) : ℝ :=
  2 * Real.exp (h / 2) - 2 * Real.exp (-(h / 2)) +
    screwLinearCoeff / 2 - screwLerchTail₁ h

/-- Canonical right slope of the positive-time Xi screw.  The cumulative critical prime mass
includes a hinge born at the endpoint. -/
def ccmGuinandWeilXiScrewRightSlope (h : ℝ) : ℝ :=
  ccmGuinandWeilXiScrewSmoothSlope h - criticalMellinPrimeMass h

/-- Affine-normalized codiagonal of the smooth (polar--Gamma) screw sector. -/
def ccmGuinandWeilXiScrewSmoothCodiagonal (b h : ℝ) : ℝ :=
  ccmGuinandWeilXiScrewSmoothPart h - ccmGuinandWeilXiScrewSmoothPart b -
    (h - b) * ccmGuinandWeilXiScrewSmoothSlope b

/-- Affine-normalized source codiagonal of the Xi screw based at `b`. -/
def ccmGuinandWeilXiScrewCodiagonal (b h : ℝ) : ℝ :=
  suzukiPsi h - suzukiPsi b -
    (h - b) * ccmGuinandWeilXiScrewRightSlope b

theorem ccmPublishedArchimedeanDensity_sub_two_cosh_eq_neg_screwRegularKernel
    {h : ℝ} (hh : 0 < h) :
    ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2) =
      -screwRegularKernel h := by
  rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hh,
    screwRegularKernel_eq_tailForm hh]
  rw [Real.cosh_eq]
  ring

theorem criticalMellinAtomWeight_eq_screwPrimeWeight
    {k : ℕ} (hk : 0 < k) :
    criticalMellinAtomWeight k = screwPrimeWeight k := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  unfold criticalMellinAtomWeight screwPrimeWeight
  rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hk0, div_eq_mul_inv]
  ring

theorem suzukiPsi_eq_smoothPart_sub_screwPrimeSum
    {h : ℝ} (hh : 0 ≤ h) :
    suzukiPsi h =
      ccmGuinandWeilXiScrewSmoothPart h - screwPrimeSum h := by
  rw [suzukiPsi, abs_of_nonneg hh]
  unfold screwFn ccmGuinandWeilXiScrewSmoothPart
  ring

theorem hasDerivAt_ccmGuinandWeilXiScrewSmoothPart
    {h : ℝ} (hh : 0 < h) :
    HasDerivAt ccmGuinandWeilXiScrewSmoothPart
      (ccmGuinandWeilXiScrewSmoothSlope h) h := by
  have htail := hasDerivAt_screwLerchTail hh
  have hpos := (hasDerivAt_exp_half h).const_mul (4 : ℝ)
  have hneg := (hasDerivAt_exp_neg_half h).const_mul (4 : ℝ)
  have hlin : HasDerivAt (fun y : ℝ => screwLinearCoeff / 2 * y)
      (screwLinearCoeff / 2) h := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id h).const_mul (screwLinearCoeff / 2)
  have hraw := ((((hpos.fun_add hneg).sub_const 8).fun_add hlin).add_const
    screwLerchConst).fun_sub htail
  unfold ccmGuinandWeilXiScrewSmoothPart ccmGuinandWeilXiScrewSmoothSlope
  apply hraw.congr_deriv
  ring

theorem hasDerivAt_ccmGuinandWeilXiScrewSmoothSlope
    {h : ℝ} (hh : 0 < h) :
    HasDerivAt ccmGuinandWeilXiScrewSmoothSlope
      (screwRegularKernel h) h := by
  have htail := hasDerivAt_screwLerchTail₁ hh
  have hpos := (hasDerivAt_exp_half h).const_mul (2 : ℝ)
  have hneg := (hasDerivAt_exp_neg_half h).const_mul (2 : ℝ)
  have hraw := ((hpos.fun_sub hneg).add_const
    (screwLinearCoeff / 2)).fun_sub htail
  unfold ccmGuinandWeilXiScrewSmoothSlope
  apply hraw.congr_deriv
  rw [screwRegularKernel_eq_tailForm hh, screwLerchTail₂_eq hh]
  ring

theorem hasDerivAt_ccmGuinandWeilXiScrewSmoothCodiagonal
    {b h : ℝ} (hh : 0 < h) :
    HasDerivAt (ccmGuinandWeilXiScrewSmoothCodiagonal b)
      (ccmGuinandWeilXiScrewSmoothSlope h -
        ccmGuinandWeilXiScrewSmoothSlope b) h := by
  have hsmooth := hasDerivAt_ccmGuinandWeilXiScrewSmoothPart hh
  have haff : HasDerivAt
      (fun x : ℝ => (x - b) * ccmGuinandWeilXiScrewSmoothSlope b)
      (ccmGuinandWeilXiScrewSmoothSlope b) h := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id h).sub_const b).mul_const
        (ccmGuinandWeilXiScrewSmoothSlope b)
  unfold ccmGuinandWeilXiScrewSmoothCodiagonal
  exact (hsmooth.sub_const
    (ccmGuinandWeilXiScrewSmoothPart b)).fun_sub haff

theorem hasDerivAt_ccmGuinandWeilXiScrewSmoothCodiagonalSlope
    {b h : ℝ} (hh : 0 < h) :
    HasDerivAt
      (fun x => ccmGuinandWeilXiScrewSmoothSlope x -
        ccmGuinandWeilXiScrewSmoothSlope b)
      (screwRegularKernel h) h :=
  (hasDerivAt_ccmGuinandWeilXiScrewSmoothSlope hh).sub_const _

/-- Twice-integrated Green identity for the smooth polar--Gamma sector. -/
theorem ccmGuinandWeil_smoothScrewGreenIdentity
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H)
    {F F' F'' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc b H, HasDerivAt F' (F'' x) x)
    (hF''cont : ContinuousOn F'' (Set.Icc b H)) :
    -( ∫ h in b..H, F h * screwRegularKernel h) =
      -F H * (ccmGuinandWeilXiScrewSmoothSlope H -
          ccmGuinandWeilXiScrewSmoothSlope b) +
        F' H * ccmGuinandWeilXiScrewSmoothCodiagonal b H -
          ∫ h in b..H,
            ccmGuinandWeilXiScrewSmoothCodiagonal b h * F'' h := by
  let C : ℝ → ℝ := ccmGuinandWeilXiScrewSmoothCodiagonal b
  let C' : ℝ → ℝ := fun h =>
    ccmGuinandWeilXiScrewSmoothSlope h -
      ccmGuinandWeilXiScrewSmoothSlope b
  let K : ℝ → ℝ := screwRegularKernel
  have hu : Set.uIcc b H = Set.Icc b H := Set.uIcc_of_le hbH
  have hCD : ∀ x ∈ Set.uIcc b H, HasDerivAt C (C' x) x := by
    intro x hx
    rw [hu] at hx
    exact hasDerivAt_ccmGuinandWeilXiScrewSmoothCodiagonal
      (hb0.trans_le hx.1)
  have hC'D : ∀ x ∈ Set.uIcc b H, HasDerivAt C' (K x) x := by
    intro x hx
    rw [hu] at hx
    exact hasDerivAt_ccmGuinandWeilXiScrewSmoothCodiagonalSlope
      (hb0.trans_le hx.1)
  have hFI : IntervalIntegrable F' volume b H := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hu]
    exact fun x hx => ((hF' x hx).continuousAt).continuousWithinAt
  have hF''I : IntervalIntegrable F'' volume b H := by
    apply ContinuousOn.intervalIntegrable
    simpa only [hu] using hF''cont
  have hC'I : IntervalIntegrable C' volume b H := by
    refine ContinuousOn.intervalIntegrable ?_
    exact fun x hx => ((hC'D x hx).continuousAt).continuousWithinAt
  have hKI : IntervalIntegrable K volume b H := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hu]
    exact continuousOn_screwRegularKernel.mono fun x hx => hb0.trans_le hx.1
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := F) (u' := F') (v := C') (v' := K)
    (fun x hx => hF x (by simpa only [hu] using hx)) hC'D hFI hKI
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := C) (u' := C') (v := F') (v' := F'')
    hCD (fun x hx => hF' x (by simpa only [hu] using hx)) hC'I hF''I
  have hCb : C b = 0 := by simp [C, ccmGuinandWeilXiScrewSmoothCodiagonal]
  have hC'b : C' b = 0 := by simp [C']
  rw [hC'b] at hfirst
  rw [hCb] at hsecond
  dsimp only [C, C', K] at hfirst hsecond ⊢
  simp only [mul_zero, sub_zero] at hfirst hsecond
  have hcomm :
      (∫ x in b..H, F' x *
        (ccmGuinandWeilXiScrewSmoothSlope x -
          ccmGuinandWeilXiScrewSmoothSlope b)) =
      ∫ x in b..H,
        (ccmGuinandWeilXiScrewSmoothSlope x -
          ccmGuinandWeilXiScrewSmoothSlope b) * F' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hcomm] at hfirst
  linarith

/-! ## Endpoint-exact prime hinge curvature -/

/-- Prime hinges born in the half-open source window `(b,H]`. -/
def ccmGuinandWeilPrimeHingeCodiagonal (b H h : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then
      criticalMellinAtomWeight k * max 0 (h - Real.log k)
    else 0

/-- Total atomic curvature born in `(b,H]`. -/
def ccmGuinandWeilPrimeWindowMass (b H : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then criticalMellinAtomWeight k else 0

private theorem ccmGuinandWeil_integral_hinge_mul_secondDeriv
    {b a H : ℝ} (hba : b < a) (haH : a ≤ H)
    {F F' F'' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc b H, HasDerivAt F' (F'' x) x)
    (hF''cont : ContinuousOn F'' (Set.Icc b H)) :
    (∫ x in b..H, max 0 (x - a) * F'' x) =
      (H - a) * F' H - (F H - F a) := by
  have hba' : b ≤ a := hba.le
  have hF'int : IntervalIntegrable F' volume a H := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le haH]
    intro x hx
    exact ((hF' x ⟨hba'.trans hx.1, hx.2⟩).continuousAt).continuousWithinAt
  have hF''int : IntervalIntegrable F'' volume a H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le haH]
    exact hF''cont.mono (Set.Icc_subset_Icc hba' le_rfl)
  have hright := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x - a) (u' := fun _ => 1)
    (v := F') (v' := F'')
    (fun x _ => (hasDerivAt_id x).sub_const a)
    (fun x hx => hF' x (by
      rw [Set.uIcc_of_le haH] at hx
      exact ⟨hba'.trans hx.1, hx.2⟩))
    (continuous_const.intervalIntegrable a H) hF''int
  have hFTC : (∫ x in a..H, F' x) = F H - F a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hF x (by
        rw [Set.uIcc_of_le haH] at hx
        exact ⟨hba'.trans hx.1, hx.2⟩)) hF'int
  have hleftInt : IntervalIntegrable
      (fun x : ℝ => max 0 (x - a) * F'' x) volume b a := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hba']
    exact (continuous_const.max (continuous_id.sub continuous_const)).continuousOn.mul
      (hF''cont.mono (Set.Icc_subset_Icc le_rfl haH))
  have hrightInt : IntervalIntegrable
      (fun x : ℝ => max 0 (x - a) * F'' x) volume a H := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le haH]
    exact (continuous_const.max (continuous_id.sub continuous_const)).continuousOn.mul
      (hF''cont.mono (Set.Icc_subset_Icc hba' le_rfl))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hleftInt hrightInt
  have hleft : (∫ x in b..a, max 0 (x - a) * F'' x) = 0 := by
    rw [show (∫ x in b..a, max 0 (x - a) * F'' x) =
        ∫ _x in b..a, (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hba'] at hx
      change max 0 (x - a) * F'' x = 0
      rw [max_eq_left (sub_nonpos.mpr hx.2), zero_mul],
      intervalIntegral.integral_zero]
  have hrightMax :
      (∫ x in a..H, max 0 (x - a) * F'' x) =
        ∫ x in a..H, (x - a) * F'' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le haH] at hx
    change max 0 (x - a) * F'' x = (x - a) * F'' x
    rw [max_eq_right (sub_nonneg.mpr hx.1)]
  rw [hleft, zero_add, hrightMax] at hsplit
  rw [hsplit] at hright
  simp only [one_mul] at hright
  rw [hFTC] at hright
  simpa only [sub_self, zero_mul, one_mul, sub_zero] using hright

/-- A half-open finite family of prime hinges has atomic curvature exactly at its birth lags. -/
theorem ccmGuinandWeilPrimeHingeGreenIdentity
    {b H : ℝ} (_hb0 : 0 < b) (hbH : b ≤ H)
    {F F' F'' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc b H, HasDerivAt F' (F'' x) x)
    (hF''cont : ContinuousOn F'' (Set.Icc b H)) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then criticalMellinAtomWeight k * F (Real.log k) else 0) =
      F H * ccmGuinandWeilPrimeWindowMass b H -
        F' H * ccmGuinandWeilPrimeHingeCodiagonal b H H +
          ∫ h in b..H, ccmGuinandWeilPrimeHingeCodiagonal b H h * F'' h := by
  have htermInt : ∀ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊, IntervalIntegrable
      (fun h : ℝ =>
        (if b < Real.log k then
          criticalMellinAtomWeight k * max 0 (h - Real.log k)
        else 0) * F'' h) volume b H := by
    intro k hk
    by_cases hbk : b < Real.log k
    · have hcont : ContinuousOn
          (fun h : ℝ => criticalMellinAtomWeight k *
            max 0 (h - Real.log k)) (Set.Icc b H) := by
        fun_prop
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hbH]
      refine (hcont.mul hF''cont).congr ?_
      intro h _hh
      dsimp only [Pi.mul_apply]
      rw [if_pos hbk]
    · simpa only [hbk, if_false, zero_mul] using
        (continuous_const.intervalIntegrable b H : IntervalIntegrable
          (fun _ : ℝ => (0 : ℝ)) volume b H)
  unfold ccmGuinandWeilPrimeWindowMass
    ccmGuinandWeilPrimeHingeCodiagonal
  have hdistribute :
      (fun h : ℝ =>
        (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            criticalMellinAtomWeight k * max 0 (h - Real.log k)
          else 0) * F'' h) =
      (fun h : ℝ =>
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          (if b < Real.log k then
            criticalMellinAtomWeight k * max 0 (h - Real.log k)
          else 0) * F'' h) := by
    funext h
    rw [Finset.sum_mul]
  rw [hdistribute, intervalIntegral.integral_finsetSum htermInt,
    Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k
  · have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkexp : (k : ℝ) ≤ Real.exp H :=
      (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
    have hlogH : Real.log k ≤ H :=
      (Real.log_le_iff_le_exp hkpos).mpr hkexp
    have hhinge := ccmGuinandWeil_integral_hinge_mul_secondDeriv
      hbk hlogH hF hF' hF''cont
    simp only [hbk, if_true]
    rw [show
      (∫ x in b..H,
        criticalMellinAtomWeight k * max 0 (x - Real.log k) * F'' x) =
          criticalMellinAtomWeight k *
            ∫ x in b..H, max 0 (x - Real.log k) * F'' x by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      ring]
    rw [hhinge, max_eq_right (sub_nonneg.mpr hlogH)]
    ring
  · simp [hbk]

/-! ## Arithmetic hinge codiagonal equals the Xi-screw codiagonal defect -/

private theorem screwPrimeSum_eq_criticalMellinHingeSum
    {h H : ℝ} (hhH : h ≤ H) :
    screwPrimeSum h =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        criticalMellinAtomWeight k * max 0 (h - Real.log k) := by
  have hfloor : ⌊Real.exp h⌋₊ ≤ ⌊Real.exp H⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hhH)
  rw [screwPrimeSum_eq_sum_max hfloor]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := by
    have hk2 := (Finset.mem_Icc.mp hk).1
    omega
  rw [criticalMellinAtomWeight_eq_screwPrimeWeight hkpos]

theorem ccmGuinandWeilPrimeWindowMass_eq_mass_sub
    {b H : ℝ} (hbH : b ≤ H) :
    ccmGuinandWeilPrimeWindowMass b H =
      criticalMellinPrimeMass H - criticalMellinPrimeMass b := by
  rw [ccmGuinandWeilPrimeWindowMass,
    criticalMellinPrimeMass_eq_commonAtomStep (h := H) (H := H) le_rfl,
    criticalMellinPrimeMass_eq_commonAtomStep hbH,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkexp : (k : ℝ) ≤ Real.exp H :=
    (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
  have hlogH : Real.log k ≤ H :=
    (Real.log_le_iff_le_exp hkpos).mpr hkexp
  by_cases hbk : b < Real.log k
  · have hnot : ¬ Real.log k ≤ b := not_le.mpr hbk
    simp [hbk, hnot, hlogH]
  · have hle : Real.log k ≤ b := le_of_not_gt hbk
    simp [hbk, hle, hlogH]

theorem ccmGuinandWeilPrimeHingeCodiagonal_eq_screwPrimeSum
    {b H h : ℝ} (hbH : b ≤ H) (hh : h ∈ Set.Icc b H) :
    ccmGuinandWeilPrimeHingeCodiagonal b H h =
      screwPrimeSum h - screwPrimeSum b -
        (h - b) * criticalMellinPrimeMass b := by
  rw [screwPrimeSum_eq_criticalMellinHingeSum hh.2,
    screwPrimeSum_eq_criticalMellinHingeSum hbH,
    criticalMellinPrimeMass_eq_commonAtomStep hbH]
  unfold ccmGuinandWeilPrimeHingeCodiagonal
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k
  · have hnot : ¬ Real.log k ≤ b := not_le.mpr hbk
    rw [if_pos hbk, if_neg hnot]
    rw [max_eq_left (sub_nonpos.mpr hbk.le)]
    ring
  · have hle : Real.log k ≤ b := le_of_not_gt hbk
    have hleh : Real.log k ≤ h := hle.trans hh.1
    rw [if_neg hbk, if_pos hle,
      max_eq_right (sub_nonneg.mpr hleh),
      max_eq_right (sub_nonneg.mpr hle)]
    ring

theorem ccmGuinandWeilXiScrewCodiagonal_eq_smooth_sub_primeHinge
    {b H h : ℝ} (hb0 : 0 < b) (hbH : b ≤ H)
    (hh : h ∈ Set.Icc b H) :
    ccmGuinandWeilXiScrewCodiagonal b h =
      ccmGuinandWeilXiScrewSmoothCodiagonal b h -
        ccmGuinandWeilPrimeHingeCodiagonal b H h := by
  rw [ccmGuinandWeilXiScrewCodiagonal,
    suzukiPsi_eq_smoothPart_sub_screwPrimeSum
      (hb0.le.trans hh.1),
    suzukiPsi_eq_smoothPart_sub_screwPrimeSum hb0.le,
    ccmGuinandWeilXiScrewRightSlope,
    ccmGuinandWeilPrimeHingeCodiagonal_eq_screwPrimeSum hbH hh]
  unfold ccmGuinandWeilXiScrewSmoothCodiagonal
  ring

theorem ccmGuinandWeilXiScrewRightSlope_sub_eq_smooth_sub_primeWindowMass
    {b H : ℝ} (hbH : b ≤ H) :
    ccmGuinandWeilXiScrewRightSlope H -
        ccmGuinandWeilXiScrewRightSlope b =
      (ccmGuinandWeilXiScrewSmoothSlope H -
        ccmGuinandWeilXiScrewSmoothSlope b) -
          ccmGuinandWeilPrimeWindowMass b H := by
  rw [ccmGuinandWeilXiScrewRightSlope,
    ccmGuinandWeilXiScrewRightSlope,
    ccmGuinandWeilPrimeWindowMass_eq_mass_sub hbH]
  ring

/-- The Xi-screw right slope is the completed critical-Mellin error plus one explicit
archimedean correction.  Thus the C70 endpoint is literally a screw boundary current. -/
theorem ccmGuinandWeilXiScrewRightSlope_eq_completedError_add_arch
    (h : ℝ) :
    ccmGuinandWeilXiScrewRightSlope h =
      criticalMellinCompletedError h +
        screwLinearCoeff / 2 - screwLerchTail₁ h := by
  rw [ccmGuinandWeilXiScrewRightSlope,
    ccmGuinandWeilXiScrewSmoothSlope,
    criticalMellinCompletedError_eq_polar_sub_primeMass,
    Real.sinh_eq]
  ring

/-- The difference between screw boundary current and completed-error current converges to the
fixed archimedean slope constant. -/
theorem tendsto_ccmGuinandWeilXiScrewRightSlope_sub_completedError :
    Tendsto
      (fun h => ccmGuinandWeilXiScrewRightSlope h -
        criticalMellinCompletedError h)
      atTop (nhds (screwLinearCoeff / 2)) := by
  have hconst : Tendsto (fun _ : ℝ => screwLinearCoeff / 2) atTop
      (nhds (screwLinearCoeff / 2)) := tendsto_const_nhds
  have hsub := hconst.sub tendsto_screwLerchTail₁_atTop
  have hsub' : Tendsto
      (fun h : ℝ => screwLinearCoeff / 2 - screwLerchTail₁ h)
      atTop (nhds (screwLinearCoeff / 2)) := by
    simpa only [sub_zero] using hsub
  apply hsub'.congr'
  filter_upwards with h
  rw [ccmGuinandWeilXiScrewRightSlope_eq_completedError_add_arch]
  ring

/-! ## Completed source = affine-normalized Xi-screw Green curvature -/

/-- A generic positive-window reporter against the literal completed
prime--polar--Gamma source. -/
def ccmGuinandWeilCompletedSourceWindow
    (b H : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log k then
        criticalMellinAtomWeight k * F (Real.log k) else 0) +
    ∫ h in b..H,
      F h * (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2))

/-- **Windowed Xi-screw Green law.**  The literal completed source on `(b,H]`, tested by any
twice differentiable reporter, is the negative curvature of the affine-normalized Xi screw.
The right-slope convention includes a prime atom at `H` and excludes one at `b`. -/
theorem ccmGuinandWeilCompletedSourceWindow_eq_xiScrewGreen
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H)
    {F F' F'' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Set.Icc b H, HasDerivAt F' (F'' x) x)
    (hF''cont : ContinuousOn F'' (Set.Icc b H)) :
    ccmGuinandWeilCompletedSourceWindow b H F =
      -F H * (ccmGuinandWeilXiScrewRightSlope H -
          ccmGuinandWeilXiScrewRightSlope b) +
        F' H * ccmGuinandWeilXiScrewCodiagonal b H -
          ∫ h in b..H,
            ccmGuinandWeilXiScrewCodiagonal b h * F'' h := by
  have hcontinuous :
      (∫ h in b..H,
        F h * (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2))) =
        -(∫ h in b..H, F h * screwRegularKernel h) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro h hh
    rw [Set.uIcc_of_le hbH] at hh
    change F h * (ccmPublishedArchimedeanDensity h -
      2 * Real.cosh (h / 2)) = -(F h * screwRegularKernel h)
    rw [ccmPublishedArchimedeanDensity_sub_two_cosh_eq_neg_screwRegularKernel
      (hb0.trans_le hh.1)]
    ring
  have hprime := ccmGuinandWeilPrimeHingeGreenIdentity
    hb0 hbH hF hF' hF''cont
  have hsmooth := ccmGuinandWeil_smoothScrewGreenIdentity
    hb0 hbH hF hF' hF''cont
  let C : ℝ → ℝ := ccmGuinandWeilXiScrewSmoothCodiagonal b
  let P : ℝ → ℝ := ccmGuinandWeilPrimeHingeCodiagonal b H
  have hCcont : ContinuousOn C (Set.Icc b H) := by
    intro h hh
    exact ((hasDerivAt_ccmGuinandWeilXiScrewSmoothCodiagonal
      (hb0.trans_le hh.1)).continuousAt).continuousWithinAt
  have hPcont : Continuous P := by
    dsimp only [P]
    unfold ccmGuinandWeilPrimeHingeCodiagonal
    refine continuous_finsetSum _ fun k _hk => ?_
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      fun_prop
    · simp only [hbk, if_false]
      fun_prop
  have hCI : IntervalIntegrable (fun h => C h * F'' h) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hCcont.mul hF''cont
  have hPI : IntervalIntegrable (fun h => P h * F'' h) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hPcont.continuousOn.mul hF''cont
  have hbulk :
      (∫ h in b..H, ccmGuinandWeilXiScrewCodiagonal b h * F'' h) =
        (∫ h in b..H, C h * F'' h) -
          ∫ h in b..H, P h * F'' h := by
    rw [← intervalIntegral.integral_sub hCI hPI]
    apply intervalIntegral.integral_congr
    intro h hh
    rw [Set.uIcc_of_le hbH] at hh
    change ccmGuinandWeilXiScrewCodiagonal b h * F'' h =
      C h * F'' h - P h * F'' h
    rw [ccmGuinandWeilXiScrewCodiagonal_eq_smooth_sub_primeHinge
      hb0 hbH hh]
    dsimp only [C, P]
    ring
  have hcodH := ccmGuinandWeilXiScrewCodiagonal_eq_smooth_sub_primeHinge
    hb0 hbH (⟨hbH, le_rfl⟩ : H ∈ Set.Icc b H)
  have hslope :=
    ccmGuinandWeilXiScrewRightSlope_sub_eq_smooth_sub_primeWindowMass hbH
  rw [ccmGuinandWeilCompletedSourceWindow, hcontinuous, hprime, hsmooth, hbulk]
  dsimp only [C, P] at hbulk ⊢
  rw [hcodH, hslope]
  ring

/-! ## Forced inverse-cubic reporter -/

/-- Second derivative of the inverse-cubic reporter forced by the prime-entry third jet. -/
def ccmGuinandWeilThirdGradeWeightSecondDeriv (h : ℝ) : ℝ :=
  384 / h ^ 5

theorem hasDerivAt_ccmGuinandWeilThirdGradeWeightDeriv
    {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt ccmGuinandWeilThirdGradeWeightDeriv
      (ccmGuinandWeilThirdGradeWeightSecondDeriv h) h := by
  have hraw := (hasDerivAt_const (x := h) (c := (-96 : ℝ))).div
    ((hasDerivAt_id (x := h)).pow 4) (pow_ne_zero 4 hh)
  unfold ccmGuinandWeilThirdGradeWeightDeriv
    ccmGuinandWeilThirdGradeWeightSecondDeriv
  apply hraw.congr_deriv
  simp only [id_eq, Pi.pow_apply]
  field_simp [hh]
  ring

theorem continuousOn_ccmGuinandWeilThirdGradeWeightSecondDeriv
    {b H : ℝ} (hb0 : 0 < b) :
    ContinuousOn ccmGuinandWeilThirdGradeWeightSecondDeriv (Set.Icc b H) := by
  intro h hh
  unfold ccmGuinandWeilThirdGradeWeightSecondDeriv
  exact (continuousAt_const.div (continuousAt_id.pow 5)
    (pow_ne_zero 5 (ne_of_gt (hb0.trans_le hh.1)))).continuousWithinAt

theorem ccmGuinandWeilCompletedSourceWindow_thirdGrade_eq_rate
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilCompletedSourceWindow b H ccmGuinandWeilThirdGradeWeight =
      ccmGuinandWeilCompletedThirdGradeRateWindow b H := by
  have hprime :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k *
            ccmGuinandWeilThirdGradeWeight (Real.log k)
        else 0) = ccmGuinandWeilPrimeThirdGradeRateWindow b H := by
    rw [ccmGuinandWeilPrimeThirdGradeRateWindow]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · simp only [hbk, if_true]
      exact criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale k
    · simp [hbk]
  have hwcont : ContinuousOn ccmGuinandWeilThirdGradeWeight (Set.Icc b H) := by
    intro h hh
    unfold ccmGuinandWeilThirdGradeWeight
    exact (continuousAt_const.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 (ne_of_gt (hb0.trans_le hh.1)))).continuousWithinAt
  have hgcont : ContinuousOn ccmPublishedArchimedeanDensity (Set.Icc b H) := by
    intro h hh
    unfold ccmPublishedArchimedeanDensity
    have hpos : 0 < h := hb0.trans_le hh.1
    have hden : Real.exp h - Real.exp (-h) ≠ 0 := by
      have he : Real.exp (-h) < Real.exp h :=
        Real.exp_lt_exp.mpr (by linarith)
      linarith
    have hnum : ContinuousAt (fun x : ℝ => Real.exp (x / 2)) h := by
      fun_prop
    have hdencont : ContinuousAt
        (fun x : ℝ => Real.exp x - Real.exp (-x)) h := by
      fun_prop
    exact (hnum.div hdencont hden).continuousWithinAt
  have hpcont : ContinuousOn (fun h : ℝ => 2 * Real.cosh (h / 2))
      (Set.Icc b H) := by fun_prop
  have hgammaInt : IntervalIntegrable
      (fun h => ccmGuinandWeilThirdGradeWeight h *
        ccmPublishedArchimedeanDensity h) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hwcont.mul hgcont
  have hpolarInt : IntervalIntegrable
      (fun h => ccmGuinandWeilThirdGradeWeight h *
        (2 * Real.cosh (h / 2))) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hwcont.mul hpcont
  have hcontinuous :
      (∫ h in b..H, ccmGuinandWeilThirdGradeWeight h *
        (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2))) =
        ccmGuinandWeilGammaThirdGradeRateWindow b H -
          ccmGuinandWeilPolarThirdGradeRateWindow b H := by
    rw [ccmGuinandWeilGammaThirdGradeRateWindow,
      ccmGuinandWeilPolarThirdGradeRateWindow,
      ← intervalIntegral.integral_sub hgammaInt hpolarInt]
    apply intervalIntegral.integral_congr
    intro h hh
    ring
  rw [ccmGuinandWeilCompletedSourceWindow, hprime, hcontinuous,
    ccmGuinandWeilCompletedThirdGradeRateWindow]
  ring

/-- **Forced inverse-cubic Xi-screw connection.**  The CCM prime-entry third jet is exactly the
Green pairing of the affine-normalized multiplicity-exact Xi screw with inverse-cubic reporter. -/
theorem ccmGuinandWeilCompletedThirdGradeRateWindow_eq_xiScrewGreen
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilCompletedThirdGradeRateWindow b H =
      -ccmGuinandWeilThirdGradeWeight H *
          (ccmGuinandWeilXiScrewRightSlope H -
            ccmGuinandWeilXiScrewRightSlope b) +
        ccmGuinandWeilThirdGradeWeightDeriv H *
          ccmGuinandWeilXiScrewCodiagonal b H -
            ∫ h in b..H,
              ccmGuinandWeilXiScrewCodiagonal b h *
                ccmGuinandWeilThirdGradeWeightSecondDeriv h := by
  have hgreen := ccmGuinandWeilCompletedSourceWindow_eq_xiScrewGreen
    hb0 hbH
    (F := ccmGuinandWeilThirdGradeWeight)
    (F' := ccmGuinandWeilThirdGradeWeightDeriv)
    (F'' := ccmGuinandWeilThirdGradeWeightSecondDeriv)
    (fun h hh => hasDerivAt_ccmGuinandWeilThirdGradeWeight
      (ne_of_gt (hb0.trans_le hh.1)))
    (fun h hh => hasDerivAt_ccmGuinandWeilThirdGradeWeightDeriv
      (ne_of_gt (hb0.trans_le hh.1)))
    (continuousOn_ccmGuinandWeilThirdGradeWeightSecondDeriv hb0)
  rw [ccmGuinandWeilCompletedSourceWindow_thirdGrade_eq_rate hb0 hbH] at hgreen
  exact hgreen

theorem ccmGuinandWeilCompletedThirdGradeRateWindow_eq_explicitXiScrewGreen
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilCompletedThirdGradeRateWindow b H =
      -(32 / H ^ 3) *
          (ccmGuinandWeilXiScrewRightSlope H -
            ccmGuinandWeilXiScrewRightSlope b) -
        (96 / H ^ 4) * ccmGuinandWeilXiScrewCodiagonal b H -
          ∫ h in b..H,
            384 * ccmGuinandWeilXiScrewCodiagonal b h / h ^ 5 := by
  rw [ccmGuinandWeilCompletedThirdGradeRateWindow_eq_xiScrewGreen hb0 hbH]
  unfold ccmGuinandWeilThirdGradeWeight
    ccmGuinandWeilThirdGradeWeightDeriv
    ccmGuinandWeilThirdGradeWeightSecondDeriv
  have hint :
      (∫ h in b..H,
        ccmGuinandWeilXiScrewCodiagonal b h * (384 / h ^ 5)) =
      ∫ h in b..H,
        384 * ccmGuinandWeilXiScrewCodiagonal b h / h ^ 5 := by
    apply intervalIntegral.integral_congr
    intro h hh
    ring
  rw [hint]
  ring

/-! ## Cofinal Xi-screw gate -/

/-- Variable Xi-screw Green reporter selected by the CCM prime-entry third jet. -/
def ccmGuinandWeilXiScrewThirdGradeGreen (b H : ℝ) : ℝ :=
  -(32 / H ^ 3) *
      (ccmGuinandWeilXiScrewRightSlope H -
        ccmGuinandWeilXiScrewRightSlope b) -
    (96 / H ^ 4) * ccmGuinandWeilXiScrewCodiagonal b H -
      ∫ h in b..H,
        384 * ccmGuinandWeilXiScrewCodiagonal b h / h ^ 5

theorem ccmGuinandWeilCompletedThirdGradeRateWindow_eq_xiScrewThirdGradeGreen
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilCompletedThirdGradeRateWindow b H =
      ccmGuinandWeilXiScrewThirdGradeGreen b H := by
  exact ccmGuinandWeilCompletedThirdGradeRateWindow_eq_explicitXiScrewGreen
    hb0 hbH

/-- Cofinal convergence of the completed source is literally cofinal convergence of its
affine-normalized Xi-screw Green reporter. -/
theorem ccmGuinandWeilCompletedThirdGradeRateWindow_converges_iff_xiScrewGreen_converges
    {b : ℝ} (hb0 : 0 < b) :
    (∃ L : ℝ,
      Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b) atTop (nhds L)) ↔
      ∃ L : ℝ,
        Tendsto (ccmGuinandWeilXiScrewThirdGradeGreen b) atTop (nhds L) := by
  have heq : ccmGuinandWeilCompletedThirdGradeRateWindow b =ᶠ[atTop]
      ccmGuinandWeilXiScrewThirdGradeGreen b := by
    filter_upwards [eventually_ge_atTop b] with H hH
    exact ccmGuinandWeilCompletedThirdGradeRateWindow_eq_xiScrewThirdGradeGreen
      hb0 hH
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, Tendsto.congr' heq hL⟩
  · rintro ⟨L, hL⟩
    exact ⟨L, Tendsto.congr' heq.symm hL⟩

/-- **Exact obstruction transfer.**  The Xi-screw Green reporter converges exactly when C70's
completed-error endpoint/flux channel converges; Gamma and separate prime/polar growth are absent
from both sides. -/
theorem ccmGuinandWeilXiScrewThirdGradeGreen_converges_iff_errorFlux_converges
    {b : ℝ} (hb0 : 0 < b) :
    (∃ L : ℝ,
      Tendsto (ccmGuinandWeilXiScrewThirdGradeGreen b) atTop (nhds L)) ↔
      ∃ L : ℝ,
        Tendsto (ccmGuinandWeilCompletedErrorThirdGradeFlux b) atTop (nhds L) :=
  (ccmGuinandWeilCompletedThirdGradeRateWindow_converges_iff_xiScrewGreen_converges
    hb0).symm.trans
      (ccmGuinandWeilCompletedThirdGradeRateWindow_converges_iff_errorFlux_converges
        hb0)

theorem ccmGuinandWeilXiScrewCodiagonal_eq_divisor
    {b h : ℝ} (hb : 0 ≤ b) (hh : 0 ≤ h) :
    (ccmGuinandWeilXiScrewCodiagonal b h : ℂ) =
      xiScrewDivisor h - xiScrewDivisor b -
        ((h - b) * ccmGuinandWeilXiScrewRightSlope b : ℝ) := by
  rw [ccmGuinandWeilXiScrewCodiagonal]
  push_cast
  rw [ofReal_suzukiPsi_eq_xiScrewDivisor hh,
    ofReal_suzukiPsi_eq_xiScrewDivisor hb]

end

end RHTower

