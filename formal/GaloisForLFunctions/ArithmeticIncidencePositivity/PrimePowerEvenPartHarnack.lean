import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomEvenPartPotential

/-!
# Harnack across the prime-power shifts with the even part kept: the atoms of `3` and `4`

For odd `F` supported in `[−r, r]`, `½ log n < r`, the atom of `n` sees `F` on the strip
`S_n = [log n − r, r]` only through its parts even and odd about `½ log n`:
`∫ F(x) F(x + log n) dx = 2 ∫_{S_n} α² − ∫_{S_n} F²` (`integral_mul_shift_eq_two_reflectedOdd_sub`).
The sharp micro-fold (`sharpMicroFold_strip_ge`) pays the odd part with the archimedean surplus of
`S_n`, `∫∫_{S_n × S_n} k (F x − F y)² ≥ λ ∫_{S_n} α²`, `λ = 1.9 − η/p − 3η²`. Keeping the even part
(`two_mul_primePowerShift_le_stripSurplus_sub_evenPart`): if `(1 + t) 2Λ(n)/√n ≤ θ λ`, `0 ≤ t ≤ 1`,

    2 Λ(n)/√n ∫ F F(· + log n) ≤ θ · 2 stripSurplus_{S_n} − 2 (Λ(n)/√n) t ∫_{S_n} F²:

the fraction `θ` of the strip surplus pays the atom and the strip gains the potential `(Λ(n)/√n) t`.
This sharpens `two_mul_primePowerShift_le_stripSurplus` (the case `t = 0`, `θ = 1`) for every
`n ≥ 2` and every window `½ log n < r ≤ ½ log n + 1/12`.

* **`n = 3`** (`two_mul_primeThreeShift_le_stripSurplus_sub`): `Λ(3)/√3 ≤ 0.6344` and `λ ≥ 1.7`, so
  `t = 1/3`, `θ = 1`: the atom of `3` is paid by its strip and leaves the potential
  `(2/3)Λ(3)/√3 ≥ 2/5` per unit of `∫_{S_3} F²`.
* **`n = 4`** (`two_mul_primeFourShift_le_stripSurplus_sub`): `Λ(4)/√4 = ½ log 2`, so `t = 1`, the
  exact identity, costs `2 log 2 ≤ (4/5) λ`: the atom of `4` is paid by `80%` of its strip surplus and
  is a net gain, `log 2 ∫_{S_4} F²`.

The atom of `4`, like every proper prime power (`Λ(p^k)/p^{k/2} ≤ log p/p ≤ 1/e`), is too small to
cost anything on its strip once its even part is counted.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- `Λ(3)/√3 = log 3/√3 ∈ [0.634, 0.6344]`. -/
theorem vonMangoldtAtom_three_bounds :
    634 / 1000 ≤ vonMangoldtAtom 3 ∧ vonMangoldtAtom 3 ≤ 6344 / 10000 := by
  unfold vonMangoldtAtom
  rw [if_pos (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  have hs1 : (17320 / 10000 : ℝ) ≤ Real.sqrt ((3 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : Real.sqrt ((3 : ℕ) : ℝ) ≤ 17321 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have l3 := log_three_bounds
  push_cast at hs1 hs2 ⊢
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- `Λ(4)/√4 = log 2 / 2`. -/
theorem vonMangoldtAtom_four : vonMangoldtAtom 4 = Real.log 2 / 2 := by
  unfold vonMangoldtAtom
  rw [if_pos (by norm_num), show (4 : ℕ) = 2 ^ 2 by norm_num,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hs : Real.sqrt (((2 ^ 2 : ℕ) : ℝ)) = 2 := by
    rw [show (((2 ^ 2 : ℕ) : ℝ)) = (2 : ℝ) ^ 2 by push_cast; ring]
    exact Real.sqrt_sq (by norm_num)
  rw [hs]
  push_cast
  ring

section EvenPart

variable {F : ℝ → ℝ} {K r : ℝ} {n : ℕ} (hn : 2 ≤ n) (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0) (hr : Real.log n / 2 < r) (hr' : r ≤ Real.log n / 2 + 1 / 12)

include hn hF hFc hodd hFL hsupp hr hr' in
/-- **Harnack across a prime-power shift, with the even part kept.** For `n ≥ 2`, every odd `F`
supported in `[−r, r]`, `½ log n < r ≤ ½ log n + 1/12`, `θ ≥ 0`, `0 ≤ t ≤ 1` and
`(1 + t) 2Λ(n)/√n ≤ θ λ`: `2 Λ(n)/√n ∫ F F(· + log n) ≤ θ · 2 stripSurplus − 2 (Λ(n)/√n) t ∫_{S_n} F²`. -/
theorem two_mul_primePowerShift_le_stripSurplus_sub_evenPart {θ t : ℝ} (hθ0 : 0 ≤ θ) (ht1 : t ≤ 1)
    (hθ : (1 + t) * (2 * vonMangoldtAtom n) ≤ θ * (19 / 10 -
      (r - (Real.log n - r)) / 2 / (Real.log n - r) - 3 * ((r - (Real.log n - r)) / 2) ^ 2)) :
    2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
      θ * (2 * stripSurplus F (Real.log n - r) r) -
        2 * vonMangoldtAtom n * t * ∫ x in (Real.log n - r)..r, F x ^ 2 := by
  have hl2 := Real.log_two_gt_d9
  have hn2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  set L := Real.log n with hLdef
  set p := L - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hL : p + r = L := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr6 : r - p ≤ 1 / 6 := by rw [hpdef]; linarith
  have hr1 : r - p ≤ 1 := by linarith
  have hms := sharpMicroFold_strip_ge hF hFL hp0 hpr hL hr3 hr6
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hF hFL hp0 hpr.le hr1
  have hshift := integral_mul_shift_le_interp hF hFc hodd (r := r) (L := L) (by linarith)
    (by rw [← hpdef]; exact hpr.le) hsupp ht1
  rw [← hpdef] at hshift
  have hw0 := vonMangoldtAtom_nonneg n
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F L x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  -- the atom costs `(1 + t)` times the odd part and pays `t` on the strip; the micro-fold pays the cost
  have k1 := mul_le_mul_of_nonneg_left hshift hw0
  have k2 := mul_le_mul_of_nonneg_right hθ hα0
  have k4 := mul_le_mul_of_nonneg_left hms hθ0
  rw [hT] at k4
  linarith only [k1, k2, k4]

end EvenPart

/-- **The atom of `3` pays potential on its strip.** For every odd `F` supported in `[−r, r]`,
`½ log 3 < r ≤ ½ log 3 + 1/12`:
`2 Λ(3)/√3 ∫ F F(· + log 3) ≤ 2 stripSurplus F (log 3 − r) r − (2/5) ∫_{log 3 − r}^{r} F²`. -/
theorem two_mul_primeThreeShift_le_stripSurplus_sub {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hsupp : ∀ x, r < |x| → F x = 0) (hr : Real.log 3 / 2 < r) (hr' : r ≤ Real.log 3 / 2 + 1 / 12) :
    2 * (vonMangoldtAtom 3 * ∫ x, F x * F (x + Real.log 3)) ≤
      2 * stripSurplus F (Real.log 3 - r) r - 2 / 5 * ∫ x in (Real.log 3 - r)..r, F x ^ 2 := by
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_three_bounds
  have l3 := log_three_bounds
  -- the micro-fold constant on the strip of `3`: `λ ≥ 1.7`
  have hlam : (1 + 1 / 3) * (2 * vonMangoldtAtom 3) ≤ 1 * (19 / 10 -
      (r - (Real.log 3 - r)) / 2 / (Real.log 3 - r) - 3 * ((r - (Real.log 3 - r)) / 2) ^ 2) := by
    have hp : 0 < Real.log 3 - r := by linarith
    have hη0 : 0 ≤ (r - (Real.log 3 - r)) / 2 := by linarith
    have hη1 : (r - (Real.log 3 - r)) / 2 ≤ 1 / 12 := by linarith
    have hq : (r - (Real.log 3 - r)) / 2 / (Real.log 3 - r) ≤ 179 / 1000 := by
      rw [div_le_iff₀ hp]; linarith
    have hsq : 3 * ((r - (Real.log 3 - r)) / 2) ^ 2 ≤ 21 / 1000 := by nlinarith
    linarith
  have h := two_mul_primePowerShift_le_stripSurplus_sub_evenPart (n := 3) (θ := 1) (t := 1 / 3)
    (by norm_num) hF hFc hodd
    hFL hsupp (by push_cast; exact hr) (by push_cast; exact hr') (by norm_num) (by norm_num)
    (by push_cast; exact hlam)
  push_cast at h
  have hS0 : 0 ≤ ∫ x in (Real.log 3 - r)..r, F x ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  have hgain := mul_le_mul_of_nonneg_right (show 2 / 5 ≤ 2 * vonMangoldtAtom 3 * (1 / 3) by linarith) hS0
  linarith only [h, hgain]

/-- **The atom of `4` is a net gain on its strip.** For every odd `F` supported in `[−r, r]`,
`log 2 < r ≤ log 2 + 1/12`:
`2 Λ(4)/√4 ∫ F F(· + log 4) ≤ (4/5) · 2 stripSurplus F (log 4 − r) r − log 2 ∫_{log 4 − r}^{r} F²`. -/
theorem two_mul_primeFourShift_le_stripSurplus_sub {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
    (hsupp : ∀ x, r < |x| → F x = 0) (hr : Real.log 2 < r) (hr' : r ≤ Real.log 2 + 1 / 12) :
    2 * (vonMangoldtAtom 4 * ∫ x, F x * F (x + Real.log 4)) ≤
      4 / 5 * (2 * stripSurplus F (Real.log 4 - r) r) -
        Real.log 2 * ∫ x in (Real.log 4 - r)..r, F x ^ 2 := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hΛ := vonMangoldtAtom_four
  -- the micro-fold constant on the strip of `4`: `λ ≥ 1.742`, and `2 log 2 ≤ (4/5) λ`
  have hlam : (1 + 1) * (2 * vonMangoldtAtom 4) ≤ 4 / 5 * (19 / 10 -
      (r - (Real.log 4 - r)) / 2 / (Real.log 4 - r) - 3 * ((r - (Real.log 4 - r)) / 2) ^ 2) := by
    rw [hΛ, h4]
    have hp : 0 < 2 * Real.log 2 - r := by linarith
    have hη0 : 0 ≤ (r - (2 * Real.log 2 - r)) / 2 := by linarith
    have hη1 : (r - (2 * Real.log 2 - r)) / 2 ≤ 1 / 12 := by linarith
    have hq : (r - (2 * Real.log 2 - r)) / 2 / (2 * Real.log 2 - r) ≤ 137 / 1000 := by
      rw [div_le_iff₀ hp]; linarith
    have hsq : 3 * ((r - (2 * Real.log 2 - r)) / 2) ^ 2 ≤ 21 / 1000 := by nlinarith
    linarith
  have hr4 : Real.log ((4 : ℕ) : ℝ) / 2 < r := by push_cast; rw [h4]; linarith
  have hr4' : r ≤ Real.log ((4 : ℕ) : ℝ) / 2 + 1 / 12 := by push_cast; rw [h4]; linarith
  have h := two_mul_primePowerShift_le_stripSurplus_sub_evenPart (n := 4) (θ := 4 / 5) (t := 1)
    (by norm_num) hF hFc hodd
    hFL hsupp hr4 hr4' (by norm_num) le_rfl (by push_cast; exact hlam)
  push_cast at h
  rw [hΛ] at h ⊢
  linarith only [h]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
