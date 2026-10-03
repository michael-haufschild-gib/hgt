import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralNegativeValues
import GaloisForLFunctions.RHTower.PrimeLagLandauCriterion
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThreeThirteenths

/-!
# The oscillation exponent of `π - li` is at least `Θ = sup Re ρ`

For every `b < Θ`, unconditionally, `π(x) - li(x) > x^b` and `π(x) - li(x) < -x^b` for arbitrarily
large `x`.  For `b ≥ ½` this is Landau's argument in the form of the two receivers
`zetaResidueUnit_ne_zero_of_primePowerCount_le` and
`zetaResidueUnit_ne_zero_of_logIntegralCompare_le`: a one-sided bound `±(π - li) ≤ x^b` clears the
half-plane `Re s > b`, so `Θ ≤ b`.  For `b < ½` Littlewood's theorem gives more.
-/

open Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- A zero-free half-plane `Re s > b` for the residue unit bounds every zero copy. -/
theorem re_le_of_zetaResidueUnit_ne_zero {b : ℝ}
    (h : ∀ s : ℂ, b < s.re → zetaResidueUnit s ≠ 0) (q : XiZeroCopy) : (q.1 : ℂ).re ≤ b := by
  by_contra hlt
  exact h _ (not_le.mp hlt) (zetaResidueUnit_eq_zero_of_xiZeroCopy q)

theorem zeroReSup_le_of_zetaResidueUnit_ne_zero {b : ℝ}
    (h : ∀ s : ℂ, b < s.re → zetaResidueUnit s ≠ 0) : zeroReSup ≤ b := by
  haveI := nonempty_xiZeroCopy
  exact zeroReSup_le (re_le_of_zetaResidueUnit_ne_zero h)

theorem sqrt_exp_le_exp_mul {b t : ℝ} (hb : 1 / 2 ≤ b) (ht : 0 ≤ t) :
    Real.exp (1 / 2 * t) ≤ Real.exp (b * t) :=
  Real.exp_le_exp.mpr (by nlinarith)

/-- **Upper receiver at exponent `b ∈ [½, 1]`.**  `π ≤ li + x^b` eventually clears `Re s > b`. -/
theorem zetaResidueUnit_ne_zero_of_primeCounting_le_logIntegral_add_rpow {b : ℝ} (hb : 1 / 2 ≤ b)
    (hb1 : b ≤ 1)
    (h : ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (∫ t in (2 : ℝ)..x, 1 / Real.log t) + x ^ b)
    {s : ℂ} (hs : b < s.re) : zetaResidueUnit s ≠ 0 := by
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp h
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set x₀ : ℝ := max x₁ 2 with hx₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₁ : ℝ := 1 + |C| / Real.log 2 + 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hM0 : 0 ≤ x₀ + 1 := by rw [hx₀]; linarith [le_max_right x₁ 2]
  refine zetaResidueUnit_ne_zero_of_primePowerCount_le (by linarith) hb1 hK₁0 hM0 ?_ hs
  intro t ht
  have hE := Real.exp_pos (b * t)
  have hhalf := sqrt_exp_le_exp_mul hb ht.le
  have hL := logIntegralCompare_nonneg ht.le
  by_cases hxt : x₀ ≤ Real.exp t
  · have hx2 : 2 ≤ Real.exp t := le_trans (le_max_right _ _) hxt
    have hpi := hx₁ (Real.exp t) (le_trans (le_max_left _ _) hxt)
    have hli := integral_inv_log_le_logIntegralCompare hx2
    rw [Real.log_exp] at hli
    have hpp := primePowerCount_le_primeCounting_add (Real.exp t)
    have hps := hC (Real.exp t)
    rw [sqrt_exp_eq_exp_half_mul] at hps
    have hrp : Real.exp t ^ b = Real.exp (b * t) := by
      rw [← Real.exp_mul]; ring_nf
    rw [hrp] at hpi
    have hps' : (Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)) / Real.log 2
        ≤ |C| / Real.log 2 * Real.exp (b * t) := by
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hl2.le
      calc Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)
          ≤ C * Real.exp (1 / 2 * t) := hps
        _ ≤ |C| * Real.exp (1 / 2 * t) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
        _ ≤ |C| * Real.exp (b * t) := mul_le_mul_of_nonneg_left hhalf (abs_nonneg _)
    have hlog := log_le_two_mul_exp_half ht
    have hexp : K₁ * Real.exp (b * t) = Real.exp (b * t)
        + |C| / Real.log 2 * Real.exp (b * t) + 2 * Real.exp (b * t) := by
      rw [hK₁]; ring
    have hx02 : 2 ≤ x₀ := le_max_right _ _
    linarith
  · have h1 := primePowerCount_le (Real.exp t)
    have h2 := Nat.floor_le (Real.exp_pos t).le
    have h3 : 0 ≤ K₁ * Real.exp (b * t) := mul_nonneg hK₁0 hE.le
    have hxt' : Real.exp t < x₀ := not_le.mp hxt
    linarith

/-- **Lower receiver at exponent `b ∈ (0, 1]`.**  `π ≥ li - x^b` eventually clears `Re s > b`. -/
theorem zetaResidueUnit_ne_zero_of_logIntegral_sub_rpow_le_primeCounting {b : ℝ} (hb : 0 < b)
    (hb1 : b ≤ 1)
    (h : ∀ᶠ x : ℝ in atTop,
      (∫ t in (2 : ℝ)..x, 1 / Real.log t) - x ^ b ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ))
    {s : ℂ} (hs : b < s.re) : zetaResidueUnit s ≠ 0 := by
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp h
  set x₀ : ℝ := max x₁ 2 with hx₀
  set L₂ : ℝ := logIntegralCompare (Real.log 2) with hL₂
  have hL₂0 : 0 ≤ L₂ := logIntegralCompare_nonneg (Real.log_pos (by norm_num)).le
  have hM0 : 0 ≤ x₀ + L₂ := by rw [hx₀]; linarith [le_max_right x₁ 2]
  refine zetaResidueUnit_ne_zero_of_logIntegralCompare_le hb hb1 zero_le_one hM0 ?_ hs
  intro t ht
  have hE := Real.exp_pos (b * t)
  have hPc := primePowerCount_nonneg (Real.exp t)
  by_cases hxt : x₀ ≤ Real.exp t
  · have hx2 : 2 ≤ Real.exp t := le_trans (le_max_right _ _) hxt
    have hpi := hx₁ (Real.exp t) (le_trans (le_max_left _ _) hxt)
    have hli := logIntegralCompare_sub_le_integral_inv_log hx2
    rw [Real.log_exp] at hli
    have hpp := primeCounting_le_primePowerCount (Real.exp t)
    have hrp : Real.exp t ^ b = Real.exp (b * t) := by
      rw [← Real.exp_mul]; ring_nf
    rw [hrp] at hpi
    have hx02 : 2 ≤ x₀ := le_max_right _ _
    linarith
  · have h1 := logIntegralCompare_le_exp ht.le
    have hxt' : Real.exp t < x₀ := not_le.mp hxt
    linarith

/-- `x^b ≤ (c/28)√x logloglog x / log x` for large `x` when `b < ½`. -/
theorem eventually_rpow_le_littlewood {b : ℝ} (hb : b < 1 / 2) :
    ∀ᶠ x : ℝ in atTop, x ^ b
      ≤ littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x := by
  have hc0 : 0 < littlewoodConst / 28 := by have := littlewoodConst_pos; positivity
  have hd : 0 < 1 / 2 - b := by linarith
  filter_upwards [(isLittleO_log_rpow_atTop hd).bound (show 0 < littlewoodConst / 28 by positivity),
    tendsto_logLogLog_atTop.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with x hx hL3 hx1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlx,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  rw [le_div_iff₀ hlx]
  have hsq : Real.sqrt x = x ^ b * x ^ (1 / 2 - b) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; ring_nf
  have hxb : 0 ≤ x ^ b := Real.rpow_nonneg hx0.le _
  calc x ^ b * Real.log x ≤ x ^ b * (littlewoodConst / 28 * x ^ (1 / 2 - b)) :=
        mul_le_mul_of_nonneg_left hx hxb
    _ = littlewoodConst / 28 * Real.sqrt x := by rw [hsq]; ring
    _ ≤ littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) :=
        le_mul_of_one_le_right (by positivity) hL3

/-- **Landau–Ingham, upper side.**  For every `b < Θ`, `π(x) > li(x) + x^b` infinitely often. -/
theorem frequently_logIntegral_add_rpow_lt_primeCounting {b : ℝ} (hb : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, (∫ t in (2 : ℝ)..x, 1 / Real.log t) + x ^ b
      < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  rcases lt_or_ge b (1 / 2) with hhalf | hhalf
  · refine (frequently_logIntegral_add_littlewood_lt_primeCounting.and_eventually
      (eventually_rpow_le_littlewood hhalf)).mono fun x ⟨h1, h2⟩ => by linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have hΘ1 : zeroReSup ≤ 1 := by
      haveI := nonempty_xiZeroCopy
      exact zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le
    have hz := fun s hs => zetaResidueUnit_ne_zero_of_primeCounting_le_logIntegral_add_rpow
      hhalf (by linarith) (hno.mono fun x hx => not_lt.mp hx) (s := s) hs
    have := zeroReSup_le_of_zetaResidueUnit_ne_zero hz
    linarith

/-- **Landau–Ingham, lower side.**  For every `b < Θ`, `π(x) < li(x) - x^b` infinitely often. -/
theorem frequently_primeCounting_lt_logIntegral_sub_rpow {b : ℝ} (hb : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ)
      < (∫ t in (2 : ℝ)..x, 1 / Real.log t) - x ^ b := by
  rcases lt_or_ge b (1 / 2) with hhalf | hhalf
  · refine (frequently_primeCounting_lt_logIntegral_sub_littlewood.and_eventually
      (eventually_rpow_le_littlewood hhalf)).mono fun x ⟨h1, h2⟩ => by linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    have hΘ1 : zeroReSup ≤ 1 := by
      haveI := nonempty_xiZeroCopy
      exact zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le
    have hz := fun s hs => zetaResidueUnit_ne_zero_of_logIntegral_sub_rpow_le_primeCounting
      (by linarith) (by linarith) (hno.mono fun x hx => not_lt.mp hx) (s := s) hs
    have := zeroReSup_le_of_zetaResidueUnit_ne_zero hz
    linarith

end

end RHTower
