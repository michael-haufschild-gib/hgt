import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryThirdJetConnection
import GaloisForLFunctions.RHTower.CCMFirstClockHalfWaveReflection
import GaloisForLFunctions.RHTower.CCMSharpRectangularSewing

/-!
# Completed third-grade Guinand--Weil connection

The prime-entry cubic jet forces one logarithmic grade: an atom at wall location `h = log k`
has rate `32 * criticalMellinAtomWeight k / h^3`.  This file applies that same forced weight to
the literal continuous polar and Gamma channels.  No damping parameter is chosen.

On every positive window `[b,H]`, finite Stieltjes integration by parts gives the exact
prime-minus-polar identity

```text
Q_pp(b,H)
 = 32 E(b)/b^3 - 32 E(H)/H^3 - integral_b^H 96 E(h)/h^4 dh,
```

where `E` is the already formalized completed critical-Mellin error.  Adding the literal Gamma
density gives the completed third-grade connection.  The Gamma tail is proved absolutely
integrable.  Therefore the cofinal obstruction is isolated in the endpoint/flux expression of
`E`; the large polar and prime rates no longer appear separately.

This is an unconditional finite-window identity and tail classification.  It proves neither the
cofinal limit nor RH.
-/

open scoped BigOperators Interval
open MeasureTheory Set Finset Filter Topology

namespace RHTower

noncomputable section

/-! ## Shifted finite Stieltjes integration by parts -/

private theorem ccmGuinandWeil_integral_step_mul_deriv
    {F F' : ℝ → ℝ} {b H y : ℝ} (hby : b < y) (hyH : y ≤ H)
    (hF : ∀ x ∈ Set.uIcc y H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume y H) (c : ℝ) :
    (∫ h in Ioc b H, (if y ≤ h then c else 0) * F' h) =
      c * (F H - F y) := by
  have hbH : b ≤ H := hby.le.trans hyH
  have hfun : (fun h : ℝ => (if y ≤ h then c else 0) * F' h) =
      (Ici y).indicator (fun h => c * F' h) := by
    funext h
    by_cases hyh : y ≤ h <;> simp [Set.indicator, hyh]
  rw [hfun]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [Set.indicator_indicator]
  have hset : Ioc b H ∩ Ici y = Icc y H := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · intro hh
      exact ⟨hh.2, hh.1.2⟩
    · intro hh
      exact ⟨⟨hby.trans_le hh.1, hh.2⟩, hh.1⟩
  rw [hset, MeasureTheory.integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hyH]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hF']

/-- Finite-atom integration by parts on a positive logarithmic window.  The lower-wall strict
inequality excludes atoms already present in the initial state. -/
theorem ccmGuinandWeilPrimeWindow_stieltjesIntegrationByParts
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) {F F' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume b H) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log k then
          criticalMellinAtomWeight k * F (Real.log k) else 0) =
      F H * (criticalMellinPrimeMass H - criticalMellinPrimeMass b) -
        ∫ h in Ioc b H,
          (criticalMellinPrimeMass h - criticalMellinPrimeMass b) * F' h := by
  let K : Finset ℕ := Finset.Icc 2 ⌊Real.exp H⌋₊
  have hH0 : 0 ≤ H := hb0.le.trans hbH
  have hbase : Integrable F' (volume.restrict (Ioc b H)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hbH).mp hF'
  have hstep : ∀ k ∈ K, Integrable
      (fun h : ℝ =>
        (if b < Real.log k then
          if Real.log k ≤ h then criticalMellinAtomWeight k else 0
        else 0) * F' h)
      (volume.restrict (Ioc b H)) := by
    intro k _hk
    by_cases hbk : b < Real.log k
    · have hi := (hbase.const_mul (criticalMellinAtomWeight k)).indicator
        (measurableSet_Ici : MeasurableSet (Ici (Real.log k)))
      apply hi.congr
      filter_upwards with h
      by_cases hkh : Real.log k ≤ h <;> simp [Set.indicator, hbk, hkh]
    · simpa [hbk] using (integrable_zero :
        Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Ioc b H)))
  have hmass :
      (∫ h in Ioc b H,
          (criticalMellinPrimeMass h - criticalMellinPrimeMass b) * F' h) =
        ∫ h in Ioc b H,
          ∑ k ∈ K,
            (if b < Real.log k then
              if Real.log k ≤ h then criticalMellinAtomWeight k else 0
            else 0) * F' h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    rw [criticalMellinPrimeMass_eq_commonAtomStep hh.2,
      criticalMellinPrimeMass_eq_commonAtomStep hbH]
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · have hnotb : ¬ Real.log k ≤ b := not_le.mpr hbk
      by_cases hkh : Real.log k ≤ h <;> simp [hbk, hnotb, hkh]
    · have hlogb : Real.log k ≤ b := le_of_not_gt hbk
      have hlogh : Real.log k ≤ h := hlogb.trans hh.1.le
      simp [hbk, hlogb, hlogh]
  have hmassEndpoint :
      criticalMellinPrimeMass H - criticalMellinPrimeMass b =
        ∑ k ∈ K, if b < Real.log k then criticalMellinAtomWeight k else 0 := by
    rw [criticalMellinPrimeMass_eq_commonAtomStep le_rfl,
      criticalMellinPrimeMass_eq_commonAtomStep hbH]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkexp : (k : ℝ) ≤ Real.exp H :=
      (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
    have hlogH : Real.log k ≤ H :=
      (Real.log_le_iff_le_exp hkpos).mpr hkexp
    by_cases hbk : b < Real.log k
    · have hnotb : ¬ Real.log k ≤ b := not_le.mpr hbk
      simp [hbk, hnotb, hlogH]
    · have hlogb : Real.log k ≤ b := le_of_not_gt hbk
      simp [hbk, hlogb, hlogH]
  rw [hmass, MeasureTheory.integral_finsetSum K hstep]
  rw [hmassEndpoint, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k
  · have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkexp : (k : ℝ) ≤ Real.exp H :=
      (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
    have hlogH : Real.log k ≤ H :=
      (Real.log_le_iff_le_exp hkpos).mpr hkexp
    have hFsub : ∀ x ∈ Set.uIcc (Real.log k) H,
        HasDerivAt F (F' x) x := by
      intro x hx
      apply hF x
      rw [Set.uIcc_of_le hlogH] at hx
      exact ⟨hbk.le.trans hx.1, hx.2⟩
    have hFsubInt : IntervalIntegrable F' volume (Real.log k) H :=
      hF'.mono_set (by
        rw [Set.uIcc_of_le hlogH, Set.uIcc_of_le hbH]
        exact Set.Icc_subset_Icc hbk.le le_rfl)
    have hatom := ccmGuinandWeil_integral_step_mul_deriv hbk hlogH
      hFsub hFsubInt (criticalMellinAtomWeight k)
    simp only [hbk, if_true]
    rw [hatom]
    ring
  · simp [hbk]

/-- Continuous polar integration by parts on the same shifted window. -/
theorem ccmGuinandWeilContinuousPolar_windowIntegrationByParts
    {b H : ℝ} (hbH : b ≤ H) {F F' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume b H) :
    (∫ h in b..H, F h * (2 * Real.cosh (h / 2))) =
      F H * (4 * Real.sinh (H / 2)) -
        F b * (4 * Real.sinh (b / 2)) -
          ∫ h in b..H, F' h * (4 * Real.sinh (h / 2)) := by
  let P : ℝ → ℝ := fun h => 4 * Real.sinh (h / 2)
  have hP : ∀ x ∈ Set.uIcc b H,
      HasDerivAt P (2 * Real.cosh (x / 2)) x := by
    intro x hx
    dsimp only [P]
    apply (((Real.hasDerivAt_sinh (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)).const_mul 4).congr_deriv
    ring
  have hP' : IntervalIntegrable
      (fun h : ℝ => 2 * Real.cosh (h / 2)) volume b H := by
    exact (by fun_prop : Continuous
      (fun h : ℝ => 2 * Real.cosh (h / 2))).intervalIntegrable b H
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := F) (v := P) (u' := F')
    (v' := fun h => 2 * Real.cosh (h / 2))
    (fun x hx => hF x (by simpa only [Set.uIcc_of_le hbH] using hx))
    hP hF' hP'
  dsimp only [P] at hibp
  linear_combination hibp

/-- Prime-minus-polar source window tested against a generic logarithmic weight. -/
def ccmGuinandWeilPrimePolarWeightedWindow (b H : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      if b < Real.log k then
        criticalMellinAtomWeight k * F (Real.log k) else 0) -
    ∫ h in b..H, F h * (2 * Real.cosh (h / 2))

/-- **Shifted completed-error law.**  Every smooth positive-window reporter replaces separate
prime and polar rates by two endpoint values and one completed-error flux. -/
theorem ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) {F F' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume b H)
    (hF'cont : ContinuousOn F' (Set.Icc b H)) :
    ccmGuinandWeilPrimePolarWeightedWindow b H F =
      F b * criticalMellinCompletedError b -
        F H * criticalMellinCompletedError H +
          ∫ h in b..H, criticalMellinCompletedError h * F' h := by
  have hprime := ccmGuinandWeilPrimeWindow_stieltjesIntegrationByParts
    hb0 hbH hF hF'
  have hpolar := ccmGuinandWeilContinuousPolar_windowIntegrationByParts hbH hF hF'
  have hFTC : (∫ h in b..H, F' h) = F H - F b := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hF x (by simpa only [Set.uIcc_of_le hbH] using hx)) hF'
  have hPint : IntervalIntegrable
      (fun h => criticalMellinPrimeMass h * F' h) volume b H := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hbH]
    have hPbase : IntegrableOn criticalMellinPrimeMass (Set.Icc b H) := by
      exact (integrableOn_criticalMellinPrimeMass_Ioc
        (a := b - 1) (b := H)).mono_set (by
          intro x hx
          exact ⟨by linarith [hx.1], hx.2⟩)
    exact (hPbase.mul_continuousOn hF'cont isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hRint : IntervalIntegrable
      (fun h => (4 * Real.sinh (h / 2)) * F' h) volume b H := by
    have hF'contU : ContinuousOn F' (Set.uIcc b H) := by
      simpa only [Set.uIcc_of_le hbH] using hF'cont
    exact ((by fun_prop : Continuous
      (fun h : ℝ => 4 * Real.sinh (h / 2))).continuousOn.intervalIntegrable).mul_continuousOn
        hF'contU
  have hsplit :
      (∫ h in b..H, criticalMellinCompletedError h * F' h) =
        (∫ h in b..H, (4 * Real.sinh (h / 2)) * F' h) -
          ∫ h in b..H, criticalMellinPrimeMass h * F' h := by
    rw [← intervalIntegral.integral_sub hRint hPint]
    apply intervalIntegral.integral_congr
    intro h hh
    change criticalMellinCompletedError h * F' h =
      4 * Real.sinh (h / 2) * F' h - criticalMellinPrimeMass h * F' h
    rw [criticalMellinCompletedError_eq_polar_sub_primeMass]
    ring
  rw [ccmGuinandWeilPrimePolarWeightedWindow, hprime, hpolar, hsplit,
    criticalMellinCompletedError_eq_polar_sub_primeMass,
    criticalMellinCompletedError_eq_polar_sub_primeMass]
  have hcommR :
      (∫ h in b..H, F' h * (4 * Real.sinh (h / 2))) =
        ∫ h in b..H, (4 * Real.sinh (h / 2)) * F' h := by
    apply intervalIntegral.integral_congr
    intro h hh
    ring
  rw [hcommR]
  have hPshift :
      (∫ h in Ioc b H,
          (criticalMellinPrimeMass h - criticalMellinPrimeMass b) * F' h) =
        (∫ h in b..H, criticalMellinPrimeMass h * F' h) -
          criticalMellinPrimeMass b * (F H - F b) := by
    rw [← intervalIntegral.integral_of_le hbH]
    calc
      (∫ h in b..H,
          (criticalMellinPrimeMass h - criticalMellinPrimeMass b) * F' h) =
        ∫ h in b..H,
          (criticalMellinPrimeMass h * F' h -
            criticalMellinPrimeMass b * F' h) := by
          apply intervalIntegral.integral_congr
          intro h hh
          ring
      _ = (∫ h in b..H, criticalMellinPrimeMass h * F' h) -
          ∫ h in b..H, criticalMellinPrimeMass b * F' h := by
        rw [intervalIntegral.integral_sub hPint
          (hF'.const_mul (criticalMellinPrimeMass b))]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, hFTC]
  rw [hPshift]
  ring

/-! ## Forced cubic logarithmic grade -/

/-- Logarithmic reporter weight forced by the prime-entry cubic jet. -/
def ccmGuinandWeilThirdGradeWeight (h : ℝ) : ℝ :=
  32 / h ^ 3

/-- Derivative of the forced cubic logarithmic weight away from the singular origin. -/
def ccmGuinandWeilThirdGradeWeightDeriv (h : ℝ) : ℝ :=
  -96 / h ^ 4

theorem hasDerivAt_ccmGuinandWeilThirdGradeWeight
    {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt ccmGuinandWeilThirdGradeWeight
      (ccmGuinandWeilThirdGradeWeightDeriv h) h := by
  have hraw := (hasDerivAt_const (x := h) (c := (32 : ℝ))).div
    ((hasDerivAt_id (x := h)).pow 3) (pow_ne_zero 3 hh)
  apply hraw.congr_deriv
  simp only [ccmGuinandWeilThirdGradeWeightDeriv, Pi.pow_apply, id_eq, zero_mul,
    zero_sub, Nat.cast_ofNat]
  field_simp [hh]
  ring

/-- The forced third-grade prime-minus-polar connection is exactly the completed-error endpoint
plus flux reporter. -/
theorem ccmGuinandWeilThirdGradePrimePolarWindow_eq_completedErrorFlux
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H ccmGuinandWeilThirdGradeWeight =
      ccmGuinandWeilThirdGradeWeight b * criticalMellinCompletedError b -
        ccmGuinandWeilThirdGradeWeight H * criticalMellinCompletedError H +
          ∫ h in b..H,
            criticalMellinCompletedError h * ccmGuinandWeilThirdGradeWeightDeriv h := by
  apply ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux hb0 hbH
  · intro x hx
    exact hasDerivAt_ccmGuinandWeilThirdGradeWeight
      (ne_of_gt (hb0.trans_le hx.1))
  · have hc : ContinuousOn ccmGuinandWeilThirdGradeWeightDeriv (Set.Icc b H) := by
      intro x hx
      unfold ccmGuinandWeilThirdGradeWeightDeriv
      exact (continuousAt_const.div (continuousAt_id.pow 4)
        (pow_ne_zero 4 (ne_of_gt (hb0.trans_le hx.1)))).continuousWithinAt
    have hcU : ContinuousOn ccmGuinandWeilThirdGradeWeightDeriv (Set.uIcc b H) := by
      simpa only [Set.uIcc_of_le hbH] using hc
    exact hcU.intervalIntegrable
  · intro x hx
    unfold ccmGuinandWeilThirdGradeWeightDeriv
    exact (continuousAt_const.div (continuousAt_id.pow 4)
      (pow_ne_zero 4 (ne_of_gt (hb0.trans_le hx.1)))).continuousWithinAt

/-- Explicit form of the completed-error flux: cubic wall normalization produces a quartic
error kernel and no other cofinal term. -/
theorem ccmGuinandWeilThirdGradePrimePolarWindow_eq_explicitCompletedErrorFlux
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H ccmGuinandWeilThirdGradeWeight =
      32 * criticalMellinCompletedError b / b ^ 3 -
        32 * criticalMellinCompletedError H / H ^ 3 -
          ∫ h in b..H,
            96 * criticalMellinCompletedError h / h ^ 4 := by
  rw [ccmGuinandWeilThirdGradePrimePolarWindow_eq_completedErrorFlux hb0 hbH]
  unfold ccmGuinandWeilThirdGradeWeight ccmGuinandWeilThirdGradeWeightDeriv
  have hint :
      (∫ h in b..H, criticalMellinCompletedError h * (-96 / h ^ 4)) =
        -(∫ h in b..H, 96 * criticalMellinCompletedError h / h ^ 4) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro h hh
    ring
  rw [hint]
  ring

/-! ## Literal completed third-grade rate -/

/-- Finite arithmetic third-grade rate after the lower wall `b`. -/
def ccmGuinandWeilPrimeThirdGradeRateWindow (b H : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log k then ccmGuinandWeilPrimeEntryThirdJetScale k else 0

/-- Continuous polar rate in the same forced logarithmic grade. -/
def ccmGuinandWeilPolarThirdGradeRateWindow (b H : ℝ) : ℝ :=
  ∫ h in b..H,
    ccmGuinandWeilThirdGradeWeight h * (2 * Real.cosh (h / 2))

/-- Literal Gamma rate in the same forced logarithmic grade. -/
def ccmGuinandWeilGammaThirdGradeRateWindow (b H : ℝ) : ℝ :=
  ∫ h in b..H,
    ccmGuinandWeilThirdGradeWeight h * ccmPublishedArchimedeanDensity h

/-- Completed prime--polar--Gamma third-grade scalar connection. -/
def ccmGuinandWeilCompletedThirdGradeRateWindow (b H : ℝ) : ℝ :=
  ccmGuinandWeilPrimeThirdGradeRateWindow b H -
    ccmGuinandWeilPolarThirdGradeRateWindow b H +
      ccmGuinandWeilGammaThirdGradeRateWindow b H

/-- Each weighted atom is definitionally the already proved prime-entry cubic scale. -/
theorem criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale
    (k : ℕ) :
    criticalMellinAtomWeight k * ccmGuinandWeilThirdGradeWeight (Real.log k) =
      ccmGuinandWeilPrimeEntryThirdJetScale k := by
  rw [ccmGuinandWeilThirdGradeWeight,
    ccmGuinandWeilPrimeEntryThirdJetScale]
  ring

/-- The generic weighted prime-minus-polar reporter is literally the finite cubic event rate
minus its continuous polar companion. -/
theorem ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar
    (b H : ℝ) :
    ccmGuinandWeilPrimePolarWeightedWindow b H ccmGuinandWeilThirdGradeWeight =
      ccmGuinandWeilPrimeThirdGradeRateWindow b H -
        ccmGuinandWeilPolarThirdGradeRateWindow b H := by
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmGuinandWeilPrimeThirdGradeRateWindow,
    ccmGuinandWeilPolarThirdGradeRateWindow]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hbk : b < Real.log k
  · simp only [hbk, if_true]
    exact criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale k
  · simp [hbk]

/-- **Completed third-grade connection law.**  After exact prime--polar cancellation, only the
completed-error endpoint/flux reporter and the literal Gamma window remain. -/
theorem ccmGuinandWeilCompletedThirdGradeRateWindow_eq_errorFlux_add_gamma
    {b H : ℝ} (hb0 : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilCompletedThirdGradeRateWindow b H =
      32 * criticalMellinCompletedError b / b ^ 3 -
        32 * criticalMellinCompletedError H / H ^ 3 -
          (∫ h in b..H, 96 * criticalMellinCompletedError h / h ^ 4) +
            ccmGuinandWeilGammaThirdGradeRateWindow b H := by
  rw [ccmGuinandWeilCompletedThirdGradeRateWindow,
    ← ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar,
    ccmGuinandWeilThirdGradePrimePolarWindow_eq_explicitCompletedErrorFlux hb0 hbH]

/-! ## Gamma tail closure -/

/-- The literal Gamma third-grade tail is absolutely integrable beyond every positive wall. -/
theorem integrableOn_ccmGuinandWeilGammaThirdGradeTail
    {b : ℝ} (hb : 0 < b) :
    IntegrableOn
      (fun h => ccmGuinandWeilThirdGradeWeight h *
        ccmPublishedArchimedeanDensity h)
      (Set.Ioi b) := by
  let d : ℝ := 1 - Real.exp (-2 * b)
  let C : ℝ := (32 / b ^ 3) / d
  have hd : 0 < d := by
    dsimp only [d]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hexp : IntegrableOn (fun h : ℝ => Real.exp (-h / 2)) (Set.Ioi b) := by
    have hscaled :=
      (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => Real.exp (-x)) b (a := (1 / 2 : ℝ)) (by norm_num)).mpr
        (integrableOn_exp_neg_Ioi ((1 / 2 : ℝ) * b))
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro h hh
    ring_nf
  have hmajor : IntegrableOn (fun h : ℝ => C * Real.exp (-h / 2)) (Set.Ioi b) :=
    hexp.const_mul C
  apply hmajor.mono'
  · apply Measurable.aestronglyMeasurable
    unfold ccmGuinandWeilThirdGradeWeight ccmPublishedArchimedeanDensity
    measurability
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 < h := hb.trans hh
    have hb3 : 0 < b ^ 3 := pow_pos hb 3
    have hh3 : 0 < h ^ 3 := pow_pos hh0 3
    have hpow : b ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hb.le hh.le 3
    have hw : 0 ≤ ccmGuinandWeilThirdGradeWeight h := by
      unfold ccmGuinandWeilThirdGradeWeight
      positivity
    have hwle : ccmGuinandWeilThirdGradeWeight h ≤ 32 / b ^ 3 := by
      unfold ccmGuinandWeilThirdGradeWeight
      exact div_le_div_of_nonneg_left (by norm_num) hb3 hpow
    have hden : d ≤ 1 - Real.exp (-2 * h) := by
      dsimp only [d]
      have hbh : b < h := hh
      have hlin : -2 * h < -2 * b :=
        mul_lt_mul_of_neg_left hbh (by norm_num)
      have he : Real.exp (-2 * h) ≤ Real.exp (-2 * b) :=
        Real.exp_le_exp.mpr hlin.le
      linarith
    have hdensity :
        ccmPublishedArchimedeanDensity h ≤ Real.exp (-h / 2) / d := by
      rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hh0]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hd hden
    have hdensity0 : 0 ≤ ccmPublishedArchimedeanDensity h := by
      rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hh0]
      exact div_nonneg (Real.exp_nonneg _) (hd.trans_le hden).le
    have hbound :
        ccmGuinandWeilThirdGradeWeight h * ccmPublishedArchimedeanDensity h ≤
          C * Real.exp (-h / 2) := by
      calc
        _ ≤ (32 / b ^ 3) * ccmPublishedArchimedeanDensity h :=
          mul_le_mul_of_nonneg_right hwle hdensity0
        _ ≤ (32 / b ^ 3) * (Real.exp (-h / 2) / d) :=
          mul_le_mul_of_nonneg_left hdensity
            (div_nonneg (by norm_num) hb3.le)
        _ = C * Real.exp (-h / 2) := by
          dsimp only [C]
          field_simp [hd.ne']
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hdensity0)]
    exact hbound

/-- Gamma contribution has a finite cofinal limit; any failure of the completed third-grade
connection must come from the completed-error endpoint/flux channel. -/
theorem tendsto_ccmGuinandWeilGammaThirdGradeRateWindow
    {b : ℝ} (hb : 0 < b) :
    Tendsto (ccmGuinandWeilGammaThirdGradeRateWindow b) atTop
      (nhds (∫ h in Set.Ioi b,
        ccmGuinandWeilThirdGradeWeight h * ccmPublishedArchimedeanDensity h)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
    (integrableOn_ccmGuinandWeilGammaThirdGradeTail hb) tendsto_id

/-! ## Exact cofinal gate -/

/-- Variable completed-error part of the third-grade connection.  The lower endpoint contribution
is deliberately omitted because it is one fixed constant. -/
def ccmGuinandWeilCompletedErrorThirdGradeFlux (b H : ℝ) : ℝ :=
  -32 * criticalMellinCompletedError H / H ^ 3 -
    ∫ h in b..H, 96 * criticalMellinCompletedError h / h ^ 4

/-- The completed connection is a fixed base value, the completed-error flux, and the convergent
Gamma window. -/
theorem ccmGuinandWeilCompletedThirdGradeRateWindow_eq_base_add_errorFlux_add_gamma
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilCompletedThirdGradeRateWindow b H =
      32 * criticalMellinCompletedError b / b ^ 3 +
        ccmGuinandWeilCompletedErrorThirdGradeFlux b H +
          ccmGuinandWeilGammaThirdGradeRateWindow b H := by
  rw [ccmGuinandWeilCompletedThirdGradeRateWindow_eq_errorFlux_add_gamma hb hbH]
  rw [ccmGuinandWeilCompletedErrorThirdGradeFlux]
  ring

/-- **Cofinal obstruction classification.**  Since the Gamma channel converges, the whole
third-grade connection has a finite cofinal limit exactly when its completed-error endpoint/flux
channel does.  This removes Gamma and separate prime/polar growth from the remaining gate. -/
theorem ccmGuinandWeilCompletedThirdGradeRateWindow_converges_iff_errorFlux_converges
    {b : ℝ} (hb : 0 < b) :
    (∃ L : ℝ, Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b) atTop (nhds L)) ↔
      ∃ L : ℝ, Tendsto (ccmGuinandWeilCompletedErrorThirdGradeFlux b) atTop (nhds L) := by
  let B : ℝ := 32 * criticalMellinCompletedError b / b ^ 3
  let G : ℝ := ∫ h in Set.Ioi b,
    ccmGuinandWeilThirdGradeWeight h * ccmPublishedArchimedeanDensity h
  have hgamma : Tendsto (ccmGuinandWeilGammaThirdGradeRateWindow b) atTop (nhds G) :=
    tendsto_ccmGuinandWeilGammaThirdGradeRateWindow hb
  have hB : Tendsto (fun _ : ℝ => B) atTop (nhds B) := tendsto_const_nhds
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - B - G, ?_⟩
    have hsub := (hL.sub hB).sub hgamma
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop b] with H hH
    rw [ccmGuinandWeilCompletedThirdGradeRateWindow_eq_base_add_errorFlux_add_gamma
      hb hH]
    dsimp only [B]
    ring
  · rintro ⟨L, hL⟩
    refine ⟨B + L + G, ?_⟩
    have hadd := (hB.add hL).add hgamma
    apply hadd.congr'
    filter_upwards [eventually_ge_atTop b] with H hH
    rw [ccmGuinandWeilCompletedThirdGradeRateWindow_eq_base_add_errorFlux_add_gamma
      hb hH]

end

end RHTower
