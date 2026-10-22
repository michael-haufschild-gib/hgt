import GaloisForLFunctions.RHTower.CCM.CCMPrimeEntryEulerCurvature
import GaloisForLFunctions.RHTower.VonMangoldtConvHarmonicSummatory

/-!
# Cubic control of the complete Euler endpoint contribution

The endpoint term in the localized Euler-curvature identity vanishes beyond
the physical entry cutoff. On the surviving layers, the limiting overlap
and the harmonic Mangoldt convolution estimate give a cubic budget in
logarithmic time. The remaining centered curvature retains the full finite
kernel, continuous background, and mixed prime work.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

def ccmPrimeEntryEulerEndpoint (T : ℝ) : ℝ :=
  ∑ R ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊),
    (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R *
      ccmPrimeEntryOverlap T (Real.log R) 0

private theorem selfConv_nonneg (R : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

theorem ccmPrimeEntryEulerEndpoint_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ccmPrimeEntryEulerEndpoint T :=
  Finset.sum_nonneg fun R _ => mul_nonneg (selfConv_nonneg R)
    (ccmPrimeEntryOverlap_nonneg hT _ _)

/-- The product-layer endpoint keeps no terms beyond the original entry cutoff. -/
theorem ccmPrimeEntryEulerEndpoint_eq_short_sum {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryEulerEndpoint T =
      ∑ R ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R *
          ccmPrimeEntryOverlap T (Real.log R) 0 := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNN : ⌊Real.exp T⌋₊ ≤ ⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊ := by
    nlinarith only [hN]
  unfold ccmPrimeEntryEulerEndpoint
  symm
  apply Finset.sum_subset
    (fun R hR => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hR).1, (Finset.mem_Icc.mp hR).2.trans hNN⟩)
  intro R hR hnot
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (Finset.mem_Icc.mp hR).1
  have hlog : T ≤ Real.log R := by
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hR).1,
      (Nat.le_floor_iff (Real.exp_pos T).le).mpr
        ((Real.log_le_iff_le_exp hRpos).mp h)⟩)
  rw [ccmPrimeEntryOverlap_eq_zero_of_left_ge hT hlog, mul_zero]

/-- Every arithmetic endpoint term has a common cubic budget, without a
zero hypothesis or a bound on the centered prime deficit. -/
theorem ccmPrimeEntryEulerEndpoint_le_cubic {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryEulerEndpoint T ≤ (T + 2) * (T ^ 2 / 2 + 30 * T + 120) := by
  let N := ⌊Real.exp T⌋₊
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hlogT : Real.log (N : ℝ) ≤ T :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans_le hNR)).mpr
      (Nat.floor_le (Real.exp_pos T).le)
  have hsum : (∑ R ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R / R) ≤
        T ^ 2 / 2 + 30 * T + 120 := by
    have h := (abs_le.mp (abs_sum_vonMangoldt_conv_div_sub_le N hN)).2
    have hs : Real.log (N : ℝ) ^ 2 ≤ T ^ 2 := by gcongr
    linarith only [h, hs, hlogT]
  have hterm (R : ℕ) (hR : R ∈ Finset.Icc 1 N) :
      ccmPrimeEntryOverlap T (Real.log R) 0 ≤ (T + 2) / R := by
    have hRpos : (0 : ℝ) < R := by exact_mod_cast (Finset.mem_Icc.mp hR).1
    have hRlog0 : 0 ≤ Real.log (R : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hR).1)
    have hRlogT : Real.log (R : ℝ) ≤ T :=
      (Real.log_le_iff_le_exp hRpos).mpr
        ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hR).2)
    calc
      _ ≤ ccmPrimeEntryOverlapLimit (Real.log R) 0 :=
        ccmPrimeEntryOverlap_le_limit (by simpa only [max_eq_left hRlog0] using hRlog0)
          hRlogT hT
      _ = (Real.log R + 2) / R := by
        rw [ccmPrimeEntryOverlapLimit, max_eq_left hRlog0, sub_zero,
          abs_of_nonneg hRlog0, Real.exp_neg, Real.exp_log hRpos]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hRlogT]) hRpos.le
  rw [ccmPrimeEntryEulerEndpoint_eq_short_sum hT]
  calc
    _ ≤ ∑ R ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R *
          ((T + 2) / R) :=
      Finset.sum_le_sum fun R hR => mul_le_mul_of_nonneg_left (hterm R hR) (selfConv_nonneg R)
    _ = (T + 2) * ∑ R ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R / R := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

def ccmPrimeDeficitCenteredEulerCurvature (T : ℝ) : ℝ :=
  Real.exp T - Real.exp (-T) - 2 * T -
    2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
      ∑ R ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊),
        ccmPrimeEntryEulerCurvature T R

theorem ccmPrimeDeficitCriticalEnergy_integral_eq_centeredEuler_add_endpoint
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      ccmPrimeDeficitCenteredEulerCurvature T + ccmPrimeEntryEulerEndpoint T := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_euler_curvature hT,
    ccmPrimeDeficitCenteredEulerCurvature, ccmPrimeEntryEulerEndpoint,
    Finset.sum_add_distrib]
  ring

/-- The complete critical energy and its centered localized curvature
differ by a nonnegative contribution with an unconditional cubic bound. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_sub_centeredEuler_bounds
    {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) -
        ccmPrimeDeficitCenteredEulerCurvature T ∧
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) -
        ccmPrimeDeficitCenteredEulerCurvature T ≤
          (T + 2) * (T ^ 2 / 2 + 30 * T + 120) := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_centeredEuler_add_endpoint hT,
    add_sub_cancel_left]
  exact ⟨ccmPrimeEntryEulerEndpoint_nonneg hT, ccmPrimeEntryEulerEndpoint_le_cubic hT⟩

end RHTower
