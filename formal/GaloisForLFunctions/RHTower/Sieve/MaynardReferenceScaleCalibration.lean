import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog
import GaloisForLFunctions.RHTower.PsiWindowUpperBound
import GaloisForLFunctions.HTGeometry.SmoothWeight

/-!
# Reference-scale calibration for Route T

Maynard calibrates the low-frequency main term with a pointwise prime theorem in intervals of
length `x^(2/3)`.  The main term is independent of the short-window resolution, so a stronger
principle is available: compare one wide reference window with the target window and subtract the
two normalized identities.  The unknown low-frequency term cancels exactly.  A sparse target
therefore forces a large error at one of the two scales; pointwise smallness of the reference error
is unnecessary.

This file proves the algebraic two-scale law and supplies an unconditional wide reference mass
from the corpus's power-log prime number theorem.  The latter is uniform for every additive width
`H` above `N * exp (-c * log(N)^(1/10))`.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction

/-- Adjacent smooth cutoffs form the positive Route-T physical window. -/
def routeTSmoothWindowWeight (N H x : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x -
    GaloisForLFunctions.HTGeometry.smoothWeight N H x

/-- Fixed positive floor of the adjacent smooth window on its central half. -/
def routeTSmoothWindowCentralMargin : ℝ :=
  min (Real.smoothTransition (1 / 2 : ℝ))
    (1 - Real.smoothTransition (1 / 2 : ℝ))

theorem routeTSmoothWindowCentralMargin_pos :
    0 < routeTSmoothWindowCentralMargin := by
  rw [routeTSmoothWindowCentralMargin, lt_min_iff]
  exact ⟨Real.smoothTransition.pos_of_pos (by norm_num),
    sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one (by norm_num))⟩

/-- The adjacent window is pointwise nonnegative. -/
theorem routeTSmoothWindowWeight_nonneg {N H x : ℝ} (hH : 0 < H) :
    0 ≤ routeTSmoothWindowWeight N H x := by
  change 0 ≤
    (1 - Real.smoothTransition (H⁻¹ * (x + -(N + H)))) -
      (1 - Real.smoothTransition (H⁻¹ * (x + -N)))
  have harg : H⁻¹ * (x + -(N + H)) ≤ H⁻¹ * (x + -N) := by
    have hInv : 0 ≤ H⁻¹ := inv_nonneg.mpr hH.le
    nlinarith
  linarith [Real.smoothTransition.monotone harg]

/-- On the central half of its support, the adjacent window has a fixed positive floor. -/
theorem routeTSmoothWindowCentralMargin_le
    {N H x : ℝ} (hH : 0 < H)
    (hxlo : N + H / 2 ≤ x) (hxhi : x ≤ N + 3 * H / 2) :
    routeTSmoothWindowCentralMargin ≤ routeTSmoothWindowWeight N H x := by
  rw [routeTSmoothWindowCentralMargin]
  by_cases hx : x ≤ N + H
  · have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 1 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hx
    rw [routeTSmoothWindowWeight, hplus,
      GaloisForLFunctions.HTGeometry.smoothWeight]
    have harg : (1 / 2 : ℝ) ≤ H⁻¹ * (x + -N) := by
      have hmul := mul_le_mul_of_nonneg_left hxlo (inv_nonneg.mpr hH.le)
      field_simp [hH.ne'] at hmul ⊢
      linarith
    have hmono := Real.smoothTransition.monotone harg
    simpa only [sub_sub_cancel] using (min_le_left
      (Real.smoothTransition (1 / 2 : ℝ))
      (1 - Real.smoothTransition (1 / 2 : ℝ))).trans hmono
  · have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 0 :=
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (le_of_not_ge hx)
    rw [routeTSmoothWindowWeight, hbase, sub_zero,
      GaloisForLFunctions.HTGeometry.smoothWeight]
    have harg : H⁻¹ * (x + -(N + H)) ≤ (1 / 2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hxhi (inv_nonneg.mpr hH.le)
      field_simp [hH.ne'] at hmul ⊢
      linarith
    have hmono := Real.smoothTransition.monotone harg
    exact (min_le_right _ _).trans (sub_le_sub_left hmono 1)

/-- The adjacent smooth von Mangoldt window is a finite sum: the weight vanishes from `N + 2H`
onwards.  No Dirichlet-series summability premise is involved. -/
theorem summable_vonMangoldt_mul_routeTSmoothWindowWeight
    {N H : ℝ} (hH : 0 < H) :
    Summable fun n : ℕ =>
      (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n := by
  refine summable_of_ne_finset_zero
    (s := Finset.range (⌈N + 2 * H⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range] at hn
  have hge : N + 2 * H ≤ (n : ℝ) := by
    have hceil : N + 2 * H ≤ (⌈N + 2 * H⌉₊ : ℝ) := Nat.le_ceil _
    have hncast : ((⌈N + 2 * H⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_not_lt hn
    push_cast at hncast
    linarith
  have hfirst : GaloisForLFunctions.HTGeometry.smoothWeight
      (N + H) H (n : ℝ) = 0 := by
    apply GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
    linarith
  have hsecond : GaloisForLFunctions.HTGeometry.smoothWeight
      N H (n : ℝ) = 0 := by
    apply GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
    linarith
  rw [routeTSmoothWindowWeight, hfirst, hsecond, sub_self, mul_zero]

/-- The prime log-mass in the central half of an adjacent window injects into its full smooth
von Mangoldt mass.  This is the exact arithmetic producer needed by the two-scale calibration. -/
theorem routeT_theta_window_mul_margin_le_smooth_vonMangoldt_mass
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    routeTSmoothWindowCentralMargin *
        (Chebyshev.theta (N + 3 * H / 2) - Chebyshev.theta (N + H / 2)) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n := by
  let a : ℝ := N + H / 2
  let b : ℝ := N + 3 * H / 2
  let P : Finset ℕ := (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime
  have ha0 : 0 ≤ a := by dsimp only [a]; linarith
  have hab : a ≤ b := by dsimp only [a, b]; linarith
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have htheta : Chebyshev.theta b - Chebyshev.theta a =
      ∑ p ∈ P, Real.log p := by
    dsimp only [P]
    simpa only [Chebyshev.theta, Nat.floor_natCast] using
      (RHTower.theta_window_eq hfloor)
  have hprimeTerm : ∀ p ∈ P,
      routeTSmoothWindowCentralMargin * Real.log p ≤
        (vonMangoldt p : ℝ) * routeTSmoothWindowWeight N H p := by
    intro p hp
    have hpdata := Finset.mem_filter.mp hp
    have hpIoc := Finset.mem_Ioc.mp hpdata.1
    have hpa : a < (p : ℝ) := (Nat.floor_lt ha0).mp hpIoc.1
    have hb0 : 0 ≤ b := ha0.trans hab
    have hpb : (p : ℝ) ≤ b :=
      (by exact_mod_cast hpIoc.2 : (p : ℝ) ≤ (⌊b⌋₊ : ℝ)).trans
        (Nat.floor_le hb0)
    have hmargin := routeTSmoothWindowCentralMargin_le hH hpa.le hpb
    rw [vonMangoldt_apply_prime hpdata.2]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hmargin
        (Real.log_nonneg (show (1 : ℝ) ≤ (p : ℝ) by
          exact_mod_cast hpdata.2.one_lt.le)))
  have hsumNonneg : ∀ n : ℕ,
      0 ≤ (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n := fun n =>
    mul_nonneg vonMangoldt_nonneg (routeTSmoothWindowWeight_nonneg hH)
  change routeTSmoothWindowCentralMargin *
      (Chebyshev.theta b - Chebyshev.theta a) ≤ _
  rw [htheta, Finset.mul_sum]
  exact (Finset.sum_le_sum hprimeTerm).trans
    ((summable_vonMangoldt_mul_routeTSmoothWindowWeight hH).sum_le_tsum P
      (fun n _ => hsumNonneg n))

/-- **Unconditional wide-window prime mass.**  Every sufficiently large additive interval
`[N+H/2, N+3H/2]` has Chebyshev mass at least `H/2` once its width exceeds the corpus's
power-log PNT error scale. -/
theorem exists_routeT_reference_theta_window_lower :
    ∃ c K N₀ : ℝ, 0 < c ∧ 0 < K ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N → 0 < H → H ≤ N →
        K * N * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) ≤ H →
        H / 2 ≤ Chebyshev.theta (N + 3 * H / 2) -
          Chebyshev.theta (N + H / 2) := by
  obtain ⟨c, C, x₀, hc, hC, hx₀, htheta⟩ := exists_chebyshev_theta_power_log
  refine ⟨c, 16 * (C + 1), x₀, hc, by positivity, hx₀, ?_⟩
  intro N H hN hH hHN hwidth
  let a : ℝ := N + H / 2
  let b : ℝ := N + 3 * H / 2
  have hN3 : 3 ≤ N := hx₀.trans hN
  have hN0 : 0 < N := by linarith
  have haN : N ≤ a := by dsimp only [a]; linarith
  have hbN : N ≤ b := by dsimp only [b]; linarith
  have hax₀ : x₀ ≤ a := hN.trans haN
  have hbx₀ : x₀ ≤ b := hN.trans hbN
  have ha0 : 0 < a := hN0.trans_le haN
  have hb0 : 0 < b := hN0.trans_le hbN
  let E : ℝ := Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10)))
  have hE0 : 0 < E := by dsimp only [E]; positivity
  have hdecay : ∀ z : ℝ, N ≤ z →
      Real.exp (-(c * Real.log z ^ ((1 : ℝ) / 10))) ≤ E := by
    intro z hNz
    have hz0 : 0 < z := hN0.trans_le hNz
    have hlog : Real.log N ≤ Real.log z := Real.log_le_log hN0 hNz
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hpow : Real.log N ^ ((1 : ℝ) / 10) ≤
        Real.log z ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hlogN0 hlog (by norm_num)
    dsimp only [E]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hEa := hdecay a haN
  have hEb := hdecay b hbN
  have hthetaa := abs_le.mp (htheta a hax₀)
  have hthetab := abs_le.mp (htheta b hbx₀)
  have hab : b - a = H := by dsimp only [a, b]; ring
  have habUpper : a + b ≤ 4 * N := by
    dsimp only [a, b]
    linarith
  have herror : C * a *
        Real.exp (-(c * Real.log a ^ ((1 : ℝ) / 10))) +
      C * b * Real.exp (-(c * Real.log b ^ ((1 : ℝ) / 10))) ≤ H / 2 := by
    have hCa : C * a * Real.exp (-(c * Real.log a ^ ((1 : ℝ) / 10))) ≤
        C * a * E := mul_le_mul_of_nonneg_left hEa (mul_nonneg hC ha0.le)
    have hCb : C * b * Real.exp (-(c * Real.log b ^ ((1 : ℝ) / 10))) ≤
        C * b * E := mul_le_mul_of_nonneg_left hEb (mul_nonneg hC hb0.le)
    have hsum : C * a * E + C * b * E ≤ 4 * C * N * E := by
      have hCE : 0 ≤ C * E := mul_nonneg hC hE0.le
      calc
        C * a * E + C * b * E = (C * E) * (a + b) := by ring
        _ ≤ (C * E) * (4 * N) := mul_le_mul_of_nonneg_left habUpper hCE
        _ = 4 * C * N * E := by ring
    have hK : 8 * C * N * E ≤ 16 * (C + 1) * N * E := by
      have hNE : 0 ≤ N * E := mul_nonneg hN0.le hE0.le
      nlinarith
    have hhalf : 4 * C * N * E ≤ H / 2 := by
      have hscaled : 8 * C * N * E ≤ H := hK.trans (by simpa only [E] using hwidth)
      linarith
    linarith
  have hlowerB : b - C * b *
      Real.exp (-(c * Real.log b ^ ((1 : ℝ) / 10))) ≤ Chebyshev.theta b := by
    linarith [hthetab.1]
  have hupperA : Chebyshev.theta a ≤ a + C * a *
      Real.exp (-(c * Real.log a ^ ((1 : ℝ) / 10))) := by
    linarith [hthetaa.2]
  change H / 2 ≤ Chebyshev.theta b - Chebyshev.theta a
  linarith

/-- **Closed wide-reference producer.**  Every sufficiently wide reference window carries a
fixed positive fraction of its width in the actual adjacent smooth von Mangoldt sum. -/
theorem exists_routeT_reference_smooth_vonMangoldt_mass_lower :
    ∃ c K N₀ : ℝ, 0 < c ∧ 0 < K ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N → 0 < H → H ≤ N →
        K * N * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) ≤ H →
        routeTSmoothWindowCentralMargin * (H / 2) ≤
          ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n := by
  obtain ⟨c, K, N₀, hc, hK, hN₀, htheta⟩ :=
    exists_routeT_reference_theta_window_lower
  refine ⟨c, K, N₀, hc, hK, hN₀, ?_⟩
  intro N H hN hH hHN hwidth
  have hN0 : 0 ≤ N := by linarith
  exact (mul_le_mul_of_nonneg_left
      (htheta N H hN hH hHN hwidth) routeTSmoothWindowCentralMargin_pos.le).trans
    (routeT_theta_window_mul_margin_le_smooth_vonMangoldt_mass hN0 hH)

/-- Subtracting reference and target decompositions cancels the unknown low-frequency main term
exactly.  This identity is the source of two-scale self-calibration. -/
theorem routeT_reference_target_main_cancellation
    {reference target main referenceError targetError referenceRemainder targetRemainder : ℝ}
    (href : reference = main + referenceError + referenceRemainder)
    (htarget : target = main + targetError + targetRemainder) :
    reference - target =
      (referenceError - targetError) + (referenceRemainder - targetRemainder) := by
  rw [href, htarget]
  ring

/-- **Two-scale self-calibration law.**  If the normalized reference mass exceeds the normalized
target mass by `gap`, and deterministic remainders spend at most half that gap, then one of the
two spectral errors has size at least `gap/4`.  No pointwise short-interval calibration theorem is
needed. -/
theorem routeT_reference_or_target_error_large
    {reference target main referenceError targetError referenceRemainder targetRemainder gap : ℝ}
    (hmass : gap ≤ reference - target)
    (href : reference = main + referenceError + referenceRemainder)
    (htarget : target = main + targetError + targetRemainder)
    (hremainder : |referenceRemainder| + |targetRemainder| ≤ gap / 2) :
    gap / 4 ≤ |referenceError| ∨ gap / 4 ≤ |targetError| := by
  have hcancel := routeT_reference_target_main_cancellation href htarget
  have htotal : gap ≤ |referenceError| + |targetError| +
      (|referenceRemainder| + |targetRemainder|) := by
    calc
      gap ≤ reference - target := hmass
      _ = (referenceError - targetError) +
          (referenceRemainder - targetRemainder) := hcancel
      _ ≤ |referenceError - targetError| +
          |referenceRemainder - targetRemainder| := by
        linarith [le_abs_self (referenceError - targetError),
          le_abs_self (referenceRemainder - targetRemainder)]
      _ ≤ (|referenceError| + |targetError|) +
          (|referenceRemainder| + |targetRemainder|) := by
        gcongr
        · exact abs_sub referenceError targetError
        · exact abs_sub referenceRemainder targetRemainder
  have herrors : gap / 2 ≤ |referenceError| + |targetError| := by
    linarith
  by_contra h
  push Not at h
  linarith

end RHTower.Sieve
