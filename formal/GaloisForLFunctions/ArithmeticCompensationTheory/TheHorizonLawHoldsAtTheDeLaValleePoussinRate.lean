import GaloisForLFunctions.ArithmeticCompensationTheory.TheCombAtTheHorizonIsAResolvent

/-!
# The horizon law holds at the de la Vallée Poussin rate

The comb at aperture `r` has mass `S_r ∼ 2e^r`, its depths `u_p = 2r − log p` follow the horizon law
`½e^{−u/2} du`, and its energy on a fixed test is the resolvent `J(F) S_r²`. This file makes all three
quantitative, with the error of the prime number theorem, `exp(−c√r)`.

* `exists_abs_combMass_sub_le`: `|S_r − 2e^r| ≤ K e^r exp(−c√r)`. Abel summation of `p^{−1/2} log p`
  against `θ` leaves the boundary error `e^r (θ(x)/x − 1)` and the integrated error
  `∫_2^x (θ(t)/t − 1) t^{−1/2} dt`, `x = e^{2r}`, which is cut at `√x`: below the cut the trivial
  bound costs `e^{r/2}`, above it the prime number theorem gives `e^r exp(−c√r)`.
* `exists_abs_combTail_sub_le`: the depth law `sup_{u ≥ 0} |S_{r−u/2}/S_r − e^{−u/2}| ≤ K exp(−c√r)`.
* `exists_abs_combAverage_sub_horizonIntegral_le`: for every `L`-Lipschitz test `φ` bounded by `M`,
  `|S_r^{−1} Σ_p w_p φ(u_p − v) − ∫_{u>0} φ(u − v) ½e^{−u/2} du| ≤ K (L + M) exp(−c√r)`, with `c, K`
  independent of `φ` and `v`: shells of width `e^{−s}` down to depth `2s`, `s ≍ √r`.
* `exists_abs_combEnergy_div_sub_horizonEnergy_le`: for every Lipschitz compactly supported test,
  `|E_r(F)/S_r² − J(F)| ≤ K (Λ‖F‖₁ + A_F(0)) exp(−c√r)`, `Λ` the Lipschitz constant, again with
  universal `c, K`; hence `E_r(F) = 4 J(F) e^{2r} + O(e^{2r} exp(−c√r))`
  (`exists_abs_combEnergy_sub_le`).

The rate is exactly the prime-number-theorem rate: a remainder `S_r − 2e^r = O(e^{θr})` with `θ < 1`
is a statement about the zeros of `ζ` beyond the reach of these tools.
-/

open Filter Topology Finset MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The prime number theorem with the de la Vallée Poussin error -/

/-- `|θ(t)/t − 1| ≤ C exp(−c√(log t))` for `t ≥ T₀`. -/
theorem exists_abs_thetaError_le :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      |RHTower.thetaError t| ≤ C * Real.exp (-c * Real.sqrt (Real.log t)) := by
  obtain ⟨c, hc, hO⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  refine ⟨c, hc, |C|, abs_nonneg _, max T 2, le_max_right _ _, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith [le_max_right T 2]
  have h := hT t (le_trans (le_max_left _ _) ht)
  simp only [Pi.sub_apply, id, Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos ht0, abs_of_pos (Real.exp_pos _)] at h
  have he : RHTower.thetaError t = (Chebyshev.theta t - t) / t := by
    rw [RHTower.thetaError]; field_simp
  rw [he, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  calc |Chebyshev.theta t - t| ≤ C * (t * Real.exp (-c * Real.sqrt (Real.log t))) := h
    _ ≤ |C| * (t * Real.exp (-c * Real.sqrt (Real.log t))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| * Real.exp (-c * Real.sqrt (Real.log t)) * t := by ring

/-- `∫_a^b t^{−1/2} dt = 2(√b − √a)`. -/
theorem integral_rpow_neg_half {a b : ℝ} :
    ∫ t in a..b, t ^ ((1 / 2 : ℝ) - 1) = 2 * (b ^ (1 / 2 : ℝ) - a ^ (1 / 2 : ℝ)) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

/-- `(e^a)^{1/2} = e^{a/2}`. -/
theorem exp_rpow_half (a : ℝ) : Real.exp a ^ (1 / 2 : ℝ) = Real.exp (a / 2) := by
  rw [← Real.exp_mul]; ring_nf

/-- The comb mass minus `2e^r`, exactly: the bounded correction, a constant, the boundary error of
`θ` at `e^{2r}`, and half the integrated error. -/
theorem combMass_sub_eq {r : ℝ} (hr : 2 ≤ Real.exp (2 * r)) :
    combMass r - 2 * Real.exp r = combCorrectionMass r +
      ((2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log 2 -
        (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Chebyshev.theta 2 - (2 : ℝ) ^ (1 / 2 : ℝ)) +
      Real.exp r * RHTower.thetaError (Real.exp (2 * r)) +
      (1 / 2) * ∫ t in (2 : ℝ)..Real.exp (2 * r), RHTower.thetaError t * t ^ ((1 / 2 : ℝ) - 1) := by
  have hx0 := Real.exp_pos (2 * r)
  have hA : Real.exp (2 * r) ^ ((1 / 2 : ℝ) - 1) * Real.exp (2 * r) = Real.exp r := by
    rw [← Real.exp_mul, ← Real.exp_add]; ring_nf
  have hB : Real.exp (2 * r) ^ (1 / 2 : ℝ) = Real.exp r := by
    rw [exp_rpow_half]; ring_nf
  rw [combMass_eq_main_add_correction, combMainMass_eq hr, RHTower.primeRpowLogSumIoc_eq hr,
    RHTower.integral_derivRpow_mul_theta_eq (by norm_num) hr, RHTower.theta_eq_mul_thetaError hx0,
    ← mul_assoc, hA, hB]
  ring

/-- **The comb mass at the de la Vallée Poussin rate.** `|S_r − 2e^r| ≤ K e^r exp(−c√r)`. -/
theorem exists_abs_combMass_sub_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in atTop,
      |combMass r - 2 * Real.exp r| ≤ K * Real.exp r * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c, hc, C, hC0, T₀, hT₀, hθ⟩ := exists_abs_thetaError_le
  set M : ℝ := Real.log 4 + 1
  have hM0 : 0 ≤ M := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  set B : ℝ := 2 * (1 / (1 / 2) + RHTower.tiltedPrimeLogTotalConst)
  set K₁ : ℝ := |(2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log 2 -
    (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Chebyshev.theta 2 - (2 : ℝ) ^ (1 / 2 : ℝ)| + B
  have hB0 : 0 ≤ B := (combCorrectionMass_nonneg 0).trans (combCorrectionMass_le 0)
  have hK₁ : 0 ≤ K₁ := by positivity
  refine ⟨c, hc, K₁ + M + 2 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max (Real.log T₀) 0) (4 * c ^ 2))] with r hr
  have hr0 : 0 ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hrT : Real.log T₀ ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hrc : 4 * c ^ 2 ≤ r := (le_max_right _ _).trans hr
  set x := Real.exp (2 * r)
  set y := Real.exp r
  have hyT : T₀ ≤ y := by
    calc T₀ = Real.exp (Real.log T₀) := (Real.exp_log (by linarith)).symm
      _ ≤ y := Real.exp_le_exp.mpr hrT
  have hy2 : 2 ≤ y := hT₀.trans hyT
  have hyx : y ≤ x := Real.exp_le_exp.mpr (by linarith)
  have hx2 : 2 ≤ x := hy2.trans hyx
  -- `c√r ≤ r/2`, so `e^{r/2} ≤ e^r exp(−c√r)` and `1 ≤ e^r exp(−c√r)`
  have hsq : c * Real.sqrt r ≤ r / 2 := by
    have h1 : 2 * c ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by nlinarith)
    have h2 := Real.mul_self_sqrt hr0
    nlinarith [Real.sqrt_nonneg r]
  set ρ := Real.exp r * Real.exp (-c * Real.sqrt r)
  have hρ : ρ = Real.exp (r - c * Real.sqrt r) := by
    simp only [ρ, ← Real.exp_add]; ring_nf
  have hhalf : Real.exp (r / 2) ≤ ρ := by rw [hρ]; exact Real.exp_le_exp.mpr (by linarith)
  have hone : 1 ≤ ρ := by
    rw [hρ]; exact Real.one_le_exp (by linarith)
  have hdecay : ∀ t, y ≤ t → |RHTower.thetaError t| ≤ C * Real.exp (-c * Real.sqrt r) := by
    intro t ht
    refine (hθ t (hyT.trans ht)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    have hlog : r ≤ Real.log t := by
      rw [← Real.log_exp r]; exact Real.log_le_log (Real.exp_pos r) ht
    have := Real.sqrt_le_sqrt hlog
    nlinarith
  -- the integrated error, cut at `y = √x`
  set f : ℝ → ℝ := fun t => RHTower.thetaError t * t ^ ((1 / 2 : ℝ) - 1)
  have hfi : IntervalIntegrable f volume 2 x := RHTower.intervalIntegrable_thetaError_mul hx2
  have hfi1 : IntervalIntegrable f volume 2 y := RHTower.intervalIntegrable_thetaError_mul hy2
  have hfi2 : IntervalIntegrable f volume y x := hfi.mono_set (by
    rw [uIcc_of_le hyx, uIcc_of_le hx2]; exact Icc_subset_Icc hy2 le_rfl)
  have hpi : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1)) volume a b :=
    fun a b => intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hI1 : |∫ t in (2 : ℝ)..y, f t| ≤ 2 * M * Real.exp (r / 2) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hy2).trans ?_
    refine (intervalIntegral.integral_mono_on hy2 hfi1.abs ((hpi 2 y).const_mul M)
      fun t ht => ?_).trans ?_
    · have ht0 : 0 < t := by linarith [ht.1]
      simp only [f, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      exact mul_le_mul_of_nonneg_right (RHTower.abs_thetaError_le ht.1)
        (Real.rpow_pos_of_pos ht0 _).le
    · rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half, exp_rpow_half]
      have : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
      nlinarith
  have hI2 : |∫ t in y..x, f t| ≤ 2 * C * Real.exp (-c * Real.sqrt r) * Real.exp r := by
    refine (intervalIntegral.abs_integral_le_integral_abs hyx).trans ?_
    refine (intervalIntegral.integral_mono_on hyx hfi2.abs
      ((hpi y x).const_mul (C * Real.exp (-c * Real.sqrt r))) fun t ht => ?_).trans ?_
    · have ht0 : 0 < t := by linarith [ht.1]
      simp only [f, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      exact mul_le_mul_of_nonneg_right (hdecay t ht.1) (Real.rpow_pos_of_pos ht0 _).le
    · rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half, exp_rpow_half, exp_rpow_half,
        show 2 * r / 2 = r by ring]
      have h1 : 0 ≤ C * Real.exp (-c * Real.sqrt r) := by positivity
      have h2 : 0 ≤ Real.exp (r / 2) := (Real.exp_pos _).le
      nlinarith [mul_nonneg h1 h2]
  have hI : |∫ t in (2 : ℝ)..x, f t| ≤
      2 * M * Real.exp (r / 2) + 2 * C * Real.exp (-c * Real.sqrt r) * Real.exp r := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hfi1 hfi2]
    exact (abs_add_le _ _).trans (add_le_add hI1 hI2)
  -- the boundary error
  have hbd : |Real.exp r * RHTower.thetaError x| ≤ C * ρ := by
    rw [abs_mul, abs_of_pos (Real.exp_pos r)]
    have := hdecay x hyx
    calc Real.exp r * |RHTower.thetaError x| ≤ Real.exp r * (C * Real.exp (-c * Real.sqrt r)) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos r).le
      _ = C * ρ := by simp only [ρ]; ring
  have hcorr : |combCorrectionMass r| ≤ B := by
    rw [abs_of_nonneg (combCorrectionMass_nonneg r)]; exact combCorrectionMass_le r
  rw [combMass_sub_eq hx2]
  set k₀ := (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log 2 -
    (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Chebyshev.theta 2 - (2 : ℝ) ^ (1 / 2 : ℝ)
  have hsum : |combCorrectionMass r + k₀ + Real.exp r * RHTower.thetaError x +
      1 / 2 * ∫ t in (2 : ℝ)..x, f t| ≤ B + |k₀| + C * ρ + (1 / 2) * |∫ t in (2 : ℝ)..x, f t| := by
    have h3 : |1 / 2 * ∫ t in (2 : ℝ)..x, f t| = 1 / 2 * |∫ t in (2 : ℝ)..x, f t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_add_le (combCorrectionMass r + k₀ + Real.exp r * RHTower.thetaError x)
      (1 / 2 * ∫ t in (2 : ℝ)..x, f t)
    have := abs_add_le (combCorrectionMass r + k₀) (Real.exp r * RHTower.thetaError x)
    have := abs_add_le (combCorrectionMass r) k₀
    linarith
  have hρ' : Real.exp (-c * Real.sqrt r) * Real.exp r = ρ := by simp only [ρ]; ring
  calc _ ≤ B + |k₀| + C * ρ + (1 / 2) * |∫ t in (2 : ℝ)..x, f t| := hsum
    _ ≤ K₁ + C * ρ + (M * Real.exp (r / 2) + C * ρ) := by
        have := hI
        rw [mul_assoc (2 * C), hρ'] at this
        have hK : K₁ = |k₀| + B := rfl
        linarith
    _ ≤ K₁ * ρ + C * ρ + (M * ρ + C * ρ) := by
        have h1 : K₁ ≤ K₁ * ρ := le_mul_of_one_le_right hK₁ hone
        have h2 : M * Real.exp (r / 2) ≤ M * ρ := mul_le_mul_of_nonneg_left hhalf hM0
        linarith
    _ = (K₁ + M + 2 * C) * Real.exp r * Real.exp (-c * Real.sqrt r) := by
        simp only [ρ]; ring

/-! ## The depth law -/

/-- **The depth law at the de la Vallée Poussin rate.**
`sup_{u ≥ 0} |S_{r−u/2}/S_r − e^{−u/2}| ≤ K exp(−c√r)`. -/
theorem exists_abs_combTail_sub_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in atTop, ∀ u : ℝ, 0 ≤ u →
      |combTail r u - Real.exp (-u / 2)| ≤ K * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c, hc, K, hK, hev⟩ := exists_abs_combMass_sub_le
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  have hrel : ∀ y, Y ≤ y → |combMass y / Real.exp y - 2| ≤ K * Real.exp (-c * Real.sqrt y) := by
    intro y hy
    have hey := Real.exp_pos y
    rw [show combMass y / Real.exp y - 2 = (combMass y - 2 * Real.exp y) / Real.exp y by
      field_simp, abs_div, abs_of_pos hey, div_le_iff₀ hey]
    calc _ ≤ K * Real.exp y * Real.exp (-c * Real.sqrt y) := hY y hy
      _ = _ := by ring
  have hsmall : ∀ᶠ r in atTop, K * Real.exp (-(c / 2) * Real.sqrt r) ≤ 1 / 2 := by
    have h2 : Tendsto (fun r : ℝ => c / 2 * Real.sqrt r) atTop atTop :=
      Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul K
    rw [mul_zero] at h3
    have h1 : Tendsto (fun r : ℝ => K * Real.exp (-(c / 2) * Real.sqrt r)) atTop (𝓝 0) :=
      h3.congr fun r => by simp only [Function.comp_apply, neg_mul]
    exact h1.eventually (eventually_le_nhds (by norm_num))
  refine ⟨c / 2, by positivity, 2 * K + 1, by positivity, ?_⟩
  filter_upwards [hsmall, eventually_ge_atTop (max (2 * Y) (max 0 (c ^ 2)))] with r hη hr
  have hr0 : 0 ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hrY : Y ≤ r / 2 := by have := (le_max_left _ _).trans hr; linarith
  have hrc : c ^ 2 ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  set η := K * Real.exp (-(c / 2) * Real.sqrt r)
  have hη0 : 0 ≤ η := by positivity
  have hrel' : ∀ y, r / 2 ≤ y → |combMass y / Real.exp y - 2| ≤ η := by
    intro y hy
    refine (hrel y (hrY.trans hy)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK)
    have h1 : Real.sqrt r / 2 ≤ Real.sqrt (r / 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_pow, Real.sq_sqrt hr0]; linarith
    have h2 := h1.trans (Real.sqrt_le_sqrt hy)
    nlinarith
  -- `e^{−r/2} ≤ exp(−(c/2)√r)` since `c ≤ √r`
  have hexpr : Real.exp (-r / 2) ≤ Real.exp (-(c / 2) * Real.sqrt r) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : c ≤ Real.sqrt r := Real.le_sqrt_of_sq_le hrc
    have h2 := Real.mul_self_sqrt hr0
    nlinarith [Real.sqrt_nonneg r]
  have har := hrel' r (by linarith)
  have har1 : 3 / 2 ≤ combMass r / Real.exp r := by linarith [(abs_le.mp har).1]
  have hSr : 0 < combMass r := by
    have h2 : 0 < combMass r / Real.exp r := by linarith
    exact (div_pos_iff_of_pos_right (Real.exp_pos r)).mp h2
  have hnear : ∀ u, 0 ≤ u → u ≤ r → |combTail r u - Real.exp (-u / 2)| ≤ 2 * η := by
    intro u hu0 hur
    have hay := hrel' (r - u / 2) (by linarith)
    set ay := combMass (r - u / 2) / Real.exp (r - u / 2)
    set ar := combMass r / Real.exp r
    have hsplit : combTail r u = ay / ar * Real.exp (-u / 2) := by
      simp only [combTail, ay, ar]
      have he : Real.exp (r - u / 2) = Real.exp r * Real.exp (-u / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      field_simp
    rw [hsplit]
    have hexp1 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp0 := Real.exp_pos (-u / 2)
    have hdiff : |ay / ar - 1| ≤ 2 * η := by
      have har0 : (0 : ℝ) < ar := by linarith
      rw [div_sub_one har0.ne', abs_div, abs_of_pos har0, div_le_iff₀ har0]
      have h1 : |ay - ar| ≤ 2 * η := by
        calc |ay - ar| = |(ay - 2) - (ar - 2)| := by ring_nf
          _ ≤ |ay - 2| + |ar - 2| := abs_sub _ _
          _ ≤ 2 * η := by linarith
      nlinarith
    calc |ay / ar * Real.exp (-u / 2) - Real.exp (-u / 2)|
        = |ay / ar - 1| * Real.exp (-u / 2) := by
          rw [← sub_one_mul, abs_mul, abs_of_pos hexp0]
      _ ≤ 2 * η * 1 := mul_le_mul hdiff hexp1 hexp0.le (by positivity)
      _ = 2 * η := mul_one _
  have hη' : 2 * η + Real.exp (-r / 2) ≤ (2 * K + 1) * Real.exp (-(c / 2) * Real.sqrt r) := by
    simp only [η]; nlinarith
  intro u hu
  rcases le_or_gt u r with hur | hur
  · have := hnear u hu hur
    have : 0 ≤ Real.exp (-r / 2) := (Real.exp_pos _).le
    linarith
  · have hr' := (abs_le.mp (hnear r hr0 le_rfl)).2
    have hmono := combTail_anti hSr hur.le
    have hT0 := combTail_nonneg r u
    have he0 := Real.exp_pos (-u / 2)
    have heU : Real.exp (-u / 2) ≤ Real.exp (-r / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_le]
    constructor <;> linarith

/-! ## Depth statistics of Lipschitz tests -/

/-- **Depth statistics at the de la Vallée Poussin rate.** For every `L`-Lipschitz test `φ` bounded
by `M` and every translate `v`, the comb average of `φ(u_p − v)` is within `K (L + M) exp(−c√r)` of
its horizon-law integral, with `c` and `K` independent of `φ`, `L`, `M` and `v`. -/
theorem exists_abs_combAverage_sub_horizonIntegral_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in atTop, ∀ (φ : ℝ → ℝ) (L M : ℝ), (∀ t, |φ t| ≤ M) →
      (∀ x y, |φ x - φ y| ≤ L * |x - y|) → ∀ v : ℝ,
      |combDepthSum (fun u => φ (u - v)) r 0 / combMass r -
        horizonIntegral (fun u => φ (u - v))| ≤ K * (L + M) * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c₀, hc₀, K₀, hK₀, hev⟩ := exists_abs_combTail_sub_le
  refine ⟨c₀ / 4, by positivity, 2 + 11 * K₀, by positivity, ?_⟩
  filter_upwards [hev, eventually_combMass_pos, eventually_ge_atTop 0] with r hT hS hr0
    φ L M hφM hφL v
  have hL0 : 0 ≤ L := by
    have h := hφL 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hφM 0)
  have hφc : Continuous φ := by
    refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]
    exact hφL x y
  -- the mesh `h = e^{−s}` and the depth cutoff `Nh ≥ 2s`, with `s = (c₀/2)√r`
  set s := c₀ / 2 * Real.sqrt r with hsdef
  have hs0 : 0 ≤ s := by positivity
  set η := K₀ * Real.exp (-c₀ * Real.sqrt r)
  have hη : η = K₀ * Real.exp (-(2 * s)) := by simp only [η, s]; ring_nf
  have hη0 : 0 ≤ η := by positivity
  set h := Real.exp (-s)
  have hh : 0 < h := Real.exp_pos _
  set N : ℕ := ⌈2 * s * Real.exp s⌉₊
  have hN1 : 2 * s * Real.exp s ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 2 * s * Real.exp s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hNh : 2 * s ≤ N * h := by
    have hes : Real.exp s * h = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_right hN1 hh.le]
  have hcut : Real.exp (-(N * h) / 2) ≤ h := Real.exp_le_exp.mpr (by linarith)
  set g : ℝ → ℝ := fun u => φ (u - v)
  have hgc : Continuous g := hφc.comp' (continuous_sub_right _)
  have hgM : ∀ t, |g t| ≤ M := fun t => hφM _
  have hgω : ∀ x y, |x - y| ≤ h → |g x - g y| ≤ L * h := fun x y hxy =>
    (hφL _ _).trans (by
      rw [show x - v - (y - v) = x - y by ring]; exact mul_le_mul_of_nonneg_left hxy hL0)
  have hdisc := abs_combDepthSum_sub_shells_le hgM hgω hh.le r N
  have hcont := abs_horizonIntegral_sub_shells_le hgc hgM hgω hh.le N
  have hmid : |∑ k ∈ range N, g (k * h) * (combShellMass r h k / combMass r) -
      ∑ k ∈ range N, g (k * h) * expShellMass h k| ≤ 2 * N * M * η := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ range N, |g (k * h) * (combShellMass r h k / combMass r) -
        g (k * h) * expShellMass h k| ≤ M * (2 * η) := by
      intro k _
      rw [← mul_sub, abs_mul, combShellMass_div, expShellMass]
      refine mul_le_mul (hgM _) ?_ (abs_nonneg _) hM0
      have h1 := hT (k * h) (by positivity)
      have h2 := hT ((k + 1) * h) (by positivity)
      rw [show -(((k : ℝ) + 1) * h) / 2 = -((k + 1) * h) / 2 by ring] at h2
      calc |combTail r (k * h) - combTail r ((k + 1) * h) -
            (Real.exp (-(k * h) / 2) - Real.exp (-((k + 1) * h) / 2))|
          = |(combTail r (k * h) - Real.exp (-(k * h) / 2)) -
              (combTail r ((k + 1) * h) - Real.exp (-((k + 1) * h) / 2))| := by ring_nf
        _ ≤ |combTail r (k * h) - Real.exp (-(k * h) / 2)| +
              |combTail r ((k + 1) * h) - Real.exp (-((k + 1) * h) / 2)| := abs_sub _ _
        _ ≤ 2 * η := by linarith
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    nlinarith
  have htail : combTail r (N * h) ≤ Real.exp (-(N * h) / 2) + η := by
    have := hT (N * h) (by positivity)
    linarith [(abs_le.mp this).2]
  have hdisc' : |combDepthSum g r 0 / combMass r -
      ∑ k ∈ range N, g (k * h) * (combShellMass r h k / combMass r)| ≤
      L * h + M * combTail r (N * h) := by
    have heq : combDepthSum g r 0 / combMass r -
        ∑ k ∈ range N, g (k * h) * (combShellMass r h k / combMass r) =
        (combDepthSum g r 0 - ∑ k ∈ range N, g (k * h) * combShellMass r h k) / combMass r := by
      rw [sub_div, sum_div]; congr 1; exact sum_congr rfl fun k _ => by ring
    rw [heq, abs_div, abs_of_pos hS, div_le_iff₀ hS, combTail]
    calc |combDepthSum g r 0 - ∑ k ∈ range N, g (k * h) * combShellMass r h k|
        ≤ L * h * combMass r + M * combMass (r - N * h / 2) := hdisc
      _ = (L * h + M * (combMass (r - N * h / 2) / combMass r)) * combMass r := by
          field_simp
  -- the arithmetic of the three errors
  have hq : h ≤ Real.exp (-(s / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hkey : η * (1 + 2 * N) ≤ 11 * K₀ * Real.exp (-(s / 2)) := by
    have h1 : Real.exp (-(2 * s)) ≤ Real.exp (-(s / 2)) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(2 * s)) * Real.exp s = h := by
      show _ = Real.exp (-s); rw [← Real.exp_add]; ring_nf
    have h3 : s * h ≤ 2 * Real.exp (-(s / 2)) := by
      have h4 : s / 2 + 1 ≤ Real.exp (s / 2) := Real.add_one_le_exp _
      have h5 : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by rw [← Real.exp_add]; simp
      have h6 : h = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by
        show Real.exp (-s) = _; rw [← Real.exp_add]; ring_nf
      have h7 := Real.exp_pos (-(s / 2))
      rw [h6]
      nlinarith [mul_le_mul_of_nonneg_right h4 (mul_pos h7 h7).le]
    have hE := Real.exp_pos (-(2 * s))
    calc η * (1 + 2 * N) ≤ K₀ * Real.exp (-(2 * s)) * (3 + 4 * s * Real.exp s) := by
          rw [hη]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = K₀ * (3 * Real.exp (-(2 * s)) + 4 * (s * (Real.exp (-(2 * s)) * Real.exp s))) := by
          ring
      _ = K₀ * (3 * Real.exp (-(2 * s)) + 4 * (s * h)) := by rw [h2]
      _ ≤ K₀ * (3 * Real.exp (-(s / 2)) + 4 * (2 * Real.exp (-(s / 2)))) := by gcongr
      _ = 11 * K₀ * Real.exp (-(s / 2)) := by ring
  have hfinal : Real.exp (-(s / 2)) = Real.exp (-(c₀ / 4) * Real.sqrt r) := by
    simp only [s]; ring_nf
  have hMtail : M * combTail r (N * h) ≤ M * h + M * η :=
    by nlinarith [mul_le_mul_of_nonneg_left htail hM0, mul_le_mul_of_nonneg_left hcut hM0]
  have hMcut : M * Real.exp (-(N * h) / 2) ≤ M * h := mul_le_mul_of_nonneg_left hcut hM0
  calc |combDepthSum g r 0 / combMass r - horizonIntegral g|
      = |(combDepthSum g r 0 / combMass r -
            ∑ k ∈ range N, g (k * h) * (combShellMass r h k / combMass r)) +
          (∑ k ∈ range N, g (k * h) * (combShellMass r h k / combMass r) -
            ∑ k ∈ range N, g (k * h) * expShellMass h k) +
          (∑ k ∈ range N, g (k * h) * expShellMass h k - horizonIntegral g)| := by
        congr 1; ring
    _ ≤ (L * h + M * combTail r (N * h)) + 2 * N * M * η +
          (L * h + M * Real.exp (-(N * h) / 2)) := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add hdisc' hmid)) ?_)
        rw [abs_sub_comm]; exact hcont
    _ ≤ 2 * (L + M) * h + M * (η * (1 + 2 * N)) := by nlinarith
    _ ≤ 2 * (L + M) * Real.exp (-(s / 2)) + M * (11 * K₀ * Real.exp (-(s / 2))) := by
        gcongr
    _ ≤ (2 + 11 * K₀) * (L + M) * Real.exp (-(c₀ / 4) * Real.sqrt r) := by
        rw [← hfinal]
        have he := Real.exp_pos (-(s / 2))
        nlinarith [mul_nonneg (mul_nonneg hK₀ hL0) he.le]

/-! ## The resolvent law -/

/-- The autocorrelation of a `Λ`-Lipschitz compactly supported test is `Λ‖F‖₁`-Lipschitz. -/
theorem abs_autoCorr_sub_le {F : ℝ → ℝ} {Λ : ℝ} (hFc : HasCompactSupport F)
    (hΛ : ∀ a b, |F a - F b| ≤ Λ * |a - b|) (s t : ℝ) :
    |autoCorr F s - autoCorr F t| ≤ Λ * (∫ x, |F x|) * |s - t| := by
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hF : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := Λ.toNNReal) fun x y => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ0]
    exact hΛ x y
  have hint : ∀ z : ℝ, Integrable fun x => F x * F (x + z) := fun z =>
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport hFc
  unfold autoCorr
  rw [← integral_sub (hint s) (hint t)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ x, |F x * F (x + s) - F x * F (x + t)| ≤ Λ * |s - t| * |F x| := by
    intro x
    rw [← mul_sub, abs_mul, show x + s = x + s from rfl]
    have h := hΛ (x + s) (x + t)
    rw [show x + s - (x + t) = s - t by ring] at h
    calc |F x| * |F (x + s) - F (x + t)| ≤ |F x| * (Λ * |s - t|) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = Λ * |s - t| * |F x| := by ring
  calc ∫ x, |F x * F (x + s) - F x * F (x + t)| ≤ ∫ x, Λ * |s - t| * |F x| :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (hFi.abs.const_mul _) (Eventually.of_forall hpt)
    _ = Λ * (∫ x, |F x|) * |s - t| := by rw [integral_const_mul]; ring

/-- **The resolvent law at the de la Vallée Poussin rate.** For every `Λ`-Lipschitz compactly
supported test, `|E_r(F)/S_r² − J(F)| ≤ K (Λ‖F‖₁ + A_F(0)) exp(−c√r)`, with `c` and `K` independent of
the test. -/
theorem exists_abs_combEnergy_div_sub_horizonEnergy_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in atTop, ∀ (F : ℝ → ℝ) (Λ : ℝ), HasCompactSupport F →
      (∀ a b, |F a - F b| ≤ Λ * |a - b|) →
      |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 - horizonEnergy F| ≤
        K * (Λ * (∫ x, |F x|) + autoCorr F 0) * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c, hc, K, hK, hev⟩ := exists_abs_combAverage_sub_horizonIntegral_le
  refine ⟨c, hc, 2 * K, by positivity, ?_⟩
  filter_upwards [hev, eventually_combMass_pos] with r hav hS F Λ hFc hΛ
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hF : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := Λ.toNNReal) fun x y => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ0]
    exact hΛ x y
  set L := Λ * ∫ x, |F x|
  set A0 := autoCorr F 0
  have hbA : ∀ t, |autoCorr F t| ≤ A0 := fun t => abs_autoCorr_le_autoCorr_zero hF hFc t
  have hLA : ∀ x y, |autoCorr F x - autoCorr F y| ≤ L * |x - y| := abs_autoCorr_sub_le hFc hΛ
  have hcA := continuous_autoCorr hF hFc
  have hbG : ∀ t, |horizonAutoCorr F t| ≤ A0 := abs_horizonAutoCorr_le hF hFc
  have hLG : ∀ x y, |horizonAutoCorr F x - horizonAutoCorr F y| ≤ L * |x - y| := by
    intro x y
    rw [horizonAutoCorr, horizonAutoCorr,
      horizonIntegral_sub (hcA.comp' (continuous_sub_right _))
        (hcA.comp' (continuous_sub_right _)) (fun t => hbA _) (fun t => hbA _)]
    refine abs_horizonIntegral_le fun u => ?_
    refine (hLA _ _).trans (le_of_eq ?_)
    rw [show u - x - (u - y) = -(x - y) by ring, abs_neg]
  set ε := K * (L + A0) * Real.exp (-c * Real.sqrt r)
  have hin : ∀ v, |combDepthSum (fun u => autoCorr F (u - v)) r 0 / combMass r -
      horizonAutoCorr F v| ≤ ε := fun v => hav (autoCorr F) L A0 hbA hLA v
  have hout : |combDepthSum (horizonAutoCorr F) r 0 / combMass r -
      horizonIntegral (horizonAutoCorr F)| ≤ ε := by
    have h0 := hav (horizonAutoCorr F) L A0 hbG hLG 0
    simp only [sub_zero] at h0
    exact h0
  have hJ : horizonEnergy F = horizonIntegral (horizonAutoCorr F) := rfl
  have hinner : |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
      combDepthSum (horizonAutoCorr F) r 0 / combMass r| ≤ ε := by
    have hD : combDepthSum (horizonAutoCorr F) r 0 =
        ∑ q ∈ combPrimes r, combWeight q * horizonAutoCorr F (combDepth r q) := by
      simp only [combDepthSum, show r - 0 / 2 = r by ring]
    have e1 : ∑ q ∈ combPrimes r, combWeight q *
        (combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 / combMass r -
          horizonAutoCorr F (combDepth r q)) =
        (∑ q ∈ combPrimes r, combWeight q *
          combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0) / combMass r -
        ∑ q ∈ combPrimes r, combWeight q * horizonAutoCorr F (combDepth r q) := by
      rw [sum_div, ← sum_sub_distrib]
      exact sum_congr rfl fun q _ => by ring
    have heq : combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
        combDepthSum (horizonAutoCorr F) r 0 / combMass r =
        (∑ q ∈ combPrimes r, combWeight q *
          (combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 / combMass r -
            horizonAutoCorr F (combDepth r q))) / combMass r := by
      rw [e1, combEnergy_eq_depthSum, hD]
      field_simp
    rw [heq, abs_div, abs_of_pos hS, div_le_iff₀ hS]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q ∈ combPrimes r, |combWeight q *
          (combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 / combMass r -
            horizonAutoCorr F (combDepth r q))|
        ≤ ∑ q ∈ combPrimes r, combWeight q * ε := by
          refine sum_le_sum fun q _ => ?_
          rw [abs_mul, abs_of_nonneg (combWeight_nonneg q)]
          exact mul_le_mul_of_nonneg_left (hin (combDepth r q)) (combWeight_nonneg q)
      _ = ε * combMass r := by rw [← sum_mul, mul_comm]; rfl
  rw [hJ]
  calc |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
        horizonIntegral (horizonAutoCorr F)|
      ≤ |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
          combDepthSum (horizonAutoCorr F) r 0 / combMass r| +
        |combDepthSum (horizonAutoCorr F) r 0 / combMass r -
          horizonIntegral (horizonAutoCorr F)| := abs_sub_le _ _ _
    _ ≤ ε + ε := add_le_add hinner hout
    _ = 2 * K * (L + A0) * Real.exp (-c * Real.sqrt r) := by simp only [ε]; ring

/-- **The raw comb energy at the de la Vallée Poussin rate.** For every `Λ`-Lipschitz compactly
supported test, `|E_r(F) − 4 J(F) e^{2r}| ≤ K (Λ‖F‖₁ + A_F(0)) e^{2r} exp(−c√r)`. -/
theorem exists_abs_combEnergy_sub_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in atTop, ∀ (F : ℝ → ℝ) (Λ : ℝ), HasCompactSupport F →
      (∀ a b, |F a - F b| ≤ Λ * |a - b|) →
      |combEnergy F (combPrimes r) combWeight - 4 * horizonEnergy F * Real.exp (2 * r)| ≤
        K * (Λ * (∫ x, |F x|) + autoCorr F 0) * Real.exp (2 * r) * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c₁, hc₁, K₁, hK₁, h1⟩ := exists_abs_combEnergy_div_sub_horizonEnergy_le
  obtain ⟨c₂, hc₂, K₂, hK₂, h2⟩ := exists_abs_combMass_sub_le
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, 9 * K₁ + 5 * K₂, by positivity, ?_⟩
  filter_upwards [h1, h2, eventually_combMass_le, eventually_combMass_pos] with r hE hS hS3 hS0
    F Λ hFc hΛ
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hF : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := Λ.toNNReal) fun x y => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ0]
    exact hΛ x y
  set L := Λ * ∫ x, |F x|
  set A0 := autoCorr F 0
  have hL0 : 0 ≤ L := mul_nonneg hΛ0 (integral_nonneg fun _ => abs_nonneg _)
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans (abs_autoCorr_le_autoCorr_zero hF hFc 0)
  have hJ0 := horizonEnergy_nonneg hF hFc
  have hJA := horizonEnergy_le hF hFc
  set ε := Real.exp (-(min c₁ c₂) * Real.sqrt r)
  have hε0 : 0 < ε := Real.exp_pos _
  have hsr := Real.sqrt_nonneg r
  have hε₁ : Real.exp (-c₁ * Real.sqrt r) ≤ ε :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ c₂])
  have hε₂ : Real.exp (-c₂ * Real.sqrt r) ≤ ε :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right c₁ c₂])
  set S := combMass r
  set E := combEnergy F (combPrimes r) combWeight
  set J := horizonEnergy F
  set y := Real.exp r
  have hy0 : 0 < y := Real.exp_pos r
  have hy2 : Real.exp (2 * r) = y ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  -- `E = (J + D) S²` with `|D| ≤ K₁ (L + A₀) ε`
  set D := E / S ^ 2 - J
  have hD : |D| ≤ K₁ * (L + A0) * ε :=
    (hE F Λ hFc hΛ).trans (mul_le_mul_of_nonneg_left hε₁ (by positivity))
  have hED : E = (J + D) * S ^ 2 := by simp only [D]; field_simp; ring
  have hSd : |S - 2 * y| ≤ K₂ * y * ε :=
    hS.trans (mul_le_mul_of_nonneg_left hε₂ (by positivity))
  have hsplit : E - 4 * J * Real.exp (2 * r) = D * S ^ 2 + J * ((S - 2 * y) * (S + 2 * y)) := by
    rw [hED, hy2]; ring
  have hSS : S + 2 * y ≤ 5 * y := by linarith
  have hS2 : S ^ 2 ≤ 9 * y ^ 2 := by nlinarith
  have t1 : |D * S ^ 2| ≤ K₁ * (L + A0) * ε * (9 * y ^ 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg S)]
    exact mul_le_mul hD hS2 (sq_nonneg _) (by positivity)
  have t2 : |J * ((S - 2 * y) * (S + 2 * y))| ≤ A0 * (K₂ * y * ε * (5 * y)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hJ0, abs_of_pos (by linarith : 0 < S + 2 * y)]
    exact mul_le_mul hJA (mul_le_mul hSd hSS (by linarith) (by positivity)) (by positivity) hA0
  rw [hsplit, hy2]
  calc |D * S ^ 2 + J * ((S - 2 * y) * (S + 2 * y))|
      ≤ K₁ * (L + A0) * ε * (9 * y ^ 2) + A0 * (K₂ * y * ε * (5 * y)) :=
        (abs_add_le _ _).trans (add_le_add t1 t2)
    _ ≤ (9 * K₁ + 5 * K₂) * (L + A0) * y ^ 2 * ε := by
        have : 0 ≤ K₂ * L * y ^ 2 * ε := by positivity
        nlinarith

end GaloisForLFunctions.ArithmeticCompensationTheory
