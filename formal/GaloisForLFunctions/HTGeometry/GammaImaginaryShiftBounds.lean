import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The imaginary shift of the Gamma function, with explicit two-sided bounds

For `x > 0` and real `y`, Euler's limit `Γ(s) = lim nˢ n!/∏_{j≤n}(s+j)` gives the exact product

  `|Γ(x+iy)|² / Γ(x)² = ∏_{j ≥ 0} (1 + y²/(x+j)²)⁻¹`,

so `log|Γ(x+iy)| − log Γ(x) = −½ Σ_{j≥0} f(j)` with the decreasing weight
`f(u) = log(1 + y²/(x+u)²)`.  Comparing the sum with `∫₀^∞ f`, whose value is the closed form
`I(x,y) = π|y| − x log(1 + y²/x²) − 2|y| arctan(x/|y|)` (primitive
`v log(1 + y²/v²) + 2|y| arctan(v/|y|)`), gives

  `−½ (f(0) + I(x,y)) ≤ log|Γ(x+iy)| − log Γ(x) ≤ −½ I(x,y)`.

This is an explicit, uniform form of Stirling's decay `|Γ(x+iy)| ≈ Γ(x) (1+y²/x²)^{x/2} e^{−|y| arctan(|y|/x)}`
in the imaginary direction, valid for every `x > 0` and every `y`, with error at most `½ log(1+y²/x²)`.
-/

open Complex Real Filter Topology Finset

namespace HTGeometry

noncomputable section

def gammaShiftWeight (x y u : ℝ) : ℝ := Real.log (1 + y ^ 2 / (x + u) ^ 2)

theorem gammaShiftWeight_nonneg (x y u : ℝ) : 0 ≤ gammaShiftWeight x y u :=
  Real.log_nonneg (by have := div_nonneg (sq_nonneg y) (sq_nonneg (x + u)); linarith)

theorem antitoneOn_gammaShiftWeight {x : ℝ} (hx : 0 < x) (y : ℝ) :
    AntitoneOn (fun u => gammaShiftWeight x y u) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold gammaShiftWeight
  apply Real.log_le_log (by positivity)
  have hxa : 0 < x + a := by linarith
  have hxb : 0 < x + b := by linarith
  have : (x + a) ^ 2 ≤ (x + b) ^ 2 := by nlinarith
  have := div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) this
  linarith

def gammaShiftPrimitive (y v : ℝ) : ℝ :=
  v * Real.log (1 + y ^ 2 / v ^ 2) + 2 * |y| * Real.arctan (v / |y|)

theorem hasDerivAt_gammaShiftPrimitive {y v : ℝ} (hy : y ≠ 0) (hv : 0 < v) :
    HasDerivAt (gammaShiftPrimitive y) (Real.log (1 + y ^ 2 / v ^ 2)) v := by
  have hY : 0 < |y| := abs_pos.mpr hy
  have hv0 : v ≠ 0 := hv.ne'
  have h1 : HasDerivAt (fun w => 1 + y ^ 2 * (w ^ 2)⁻¹)
      (y ^ 2 * (-(↑2 * v ^ (2 - 1)) / (v ^ 2) ^ 2)) v :=
    (((hasDerivAt_pow 2 v).inv (pow_ne_zero 2 hv0)).const_mul (y ^ 2)).const_add 1
  have hpos : 0 < 1 + y ^ 2 * (v ^ 2)⁻¹ := by positivity
  have h2 := (hasDerivAt_id v).mul (h1.log hpos.ne')
  have h3 := (Real.hasDerivAt_arctan (v / |y|)).comp v ((hasDerivAt_id v).div_const |y|)
  have h4 := h3.const_mul (2 * |y|)
  have hfun : gammaShiftPrimitive y = fun w => id w * Real.log (1 + y ^ 2 * (w ^ 2)⁻¹) +
      2 * |y| * (Real.arctan ∘ fun x => id x / |y|) w := by
    funext w
    simp [gammaShiftPrimitive, div_eq_mul_inv]
  rw [hfun]
  refine (h2.add h4).congr_deriv ?_
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  simp only [id]
  rw [← div_eq_mul_inv]
  field_simp
  rw [hy2]
  ring

theorem integral_gammaShiftWeight {x y N : ℝ} (hx : 0 < x) (hy : y ≠ 0) (hN : 0 ≤ N) :
    ∫ u in (0 : ℝ)..N, gammaShiftWeight x y u =
      gammaShiftPrimitive y (x + N) - gammaShiftPrimitive y x := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) N,
      HasDerivAt (fun u => gammaShiftPrimitive y (x + u)) (gammaShiftWeight x y u) u := by
    intro u hu
    rw [Set.uIcc_of_le hN] at hu
    have hxu : 0 < x + u := by linarith [hu.1]
    exact HasDerivAt.comp_const_add x u (hasDerivAt_gammaShiftPrimitive hy hxu)
  have hint : IntervalIntegrable (fun u => gammaShiftWeight x y u) MeasureTheory.volume 0 N := by
    apply AntitoneOn.intervalIntegrable
    refine (antitoneOn_gammaShiftWeight hx y).mono ?_
    rw [Set.uIcc_of_le hN]
    exact Set.Icc_subset_Ici_self
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- The closed form of `∫₀^∞ log(1 + y²/(x+u)²) du`. -/
def gammaShiftIntegral (x y : ℝ) : ℝ := π * |y| - gammaShiftPrimitive y x

theorem tendsto_gammaShiftPrimitive (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun N : ℕ => gammaShiftPrimitive y (x + N)) atTop (𝓝 (π * |y|)) := by
  have hY : 0 < |y| := abs_pos.mpr hy
  have hv : Tendsto (fun N : ℕ => x + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  -- first term tends to zero
  have h1 : Tendsto (fun N : ℕ => (x + N) * Real.log (1 + y ^ 2 / (x + N) ^ 2)) atTop (𝓝 0) := by
    have hup : Tendsto (fun N : ℕ => y ^ 2 / (x + N)) atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop hv)
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [hv.eventually_gt_atTop 0] with N hN
      exact mul_nonneg hN.le (Real.log_nonneg (by have := div_nonneg (sq_nonneg y) (sq_nonneg (x + N)); linarith))
    · filter_upwards [hv.eventually_gt_atTop 0] with N hN
      have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + y ^ 2 / (x + N) ^ 2 by positivity)
      calc (x + N) * Real.log (1 + y ^ 2 / (x + N) ^ 2)
          ≤ (x + N) * (y ^ 2 / (x + N) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hN.le
            linarith
        _ = y ^ 2 / (x + N) := by field_simp
  have h2 : Tendsto (fun N : ℕ => 2 * |y| * Real.arctan ((x + N) / |y|)) atTop (𝓝 (π * |y|)) := by
    have harg : Tendsto (fun N : ℕ => (x + N) / |y|) atTop atTop := hv.atTop_div_const hY
    have := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg).const_mul
      (2 * |y|)
    rw [show π * |y| = 2 * |y| * (π / 2) by ring]
    exact this
  have := h1.add h2
  simpa [gammaShiftPrimitive] using this

theorem tendsto_integral_gammaShiftWeight {x y : ℝ} (hx : 0 < x) (hy : y ≠ 0) :
    Tendsto (fun N : ℕ => ∫ u in (0 : ℝ)..(N : ℝ), gammaShiftWeight x y u) atTop
      (𝓝 (gammaShiftIntegral x y)) := by
  have := (tendsto_gammaShiftPrimitive x hy).sub_const (gammaShiftPrimitive y x)
  refine this.congr fun N => ?_
  rw [integral_gammaShiftWeight hx hy (Nat.cast_nonneg N)]

/-- The Euler sequence ratio: `‖GammaSeq (x+iy) n‖ = GammaSeq x n · ∏ (x+j)/‖x+j+iy‖`. -/
theorem norm_GammaSeq_eq {x : ℝ} (hx : 0 < x) (y : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((x : ℂ) + y * I) n‖ =
      Real.GammaSeq x n * ∏ j ∈ Finset.range (n + 1), ((x + j) / ‖(x : ℂ) + y * I + j‖) := by
  unfold Complex.GammaSeq Real.GammaSeq
  rw [norm_div, norm_mul, norm_prod]
  have hcpow : ‖(n : ℂ) ^ ((x : ℂ) + y * I)‖ = (n : ℝ) ^ x := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  rw [hcpow, Complex.norm_natCast, Finset.prod_div_distrib]
  have hprodpos : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) :=
    Finset.prod_pos fun j _ => by positivity
  have hprodnorm : 0 < ∏ j ∈ Finset.range (n + 1), ‖(x : ℂ) + y * I + j‖ := by
    refine Finset.prod_pos fun j _ => norm_pos_iff.mpr ?_
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  field_simp

theorem log_norm_GammaSeq_sub {x : ℝ} (hx : 0 < x) (y : ℝ) {n : ℕ} (hn : 0 < n) :
    Real.log ‖Complex.GammaSeq ((x : ℂ) + y * I) n‖ - Real.log (Real.GammaSeq x n) =
      -(1 / 2) * ∑ j ∈ Finset.range (n + 1), gammaShiftWeight x y j := by
  have hG : 0 < Real.GammaSeq x n := by
    unfold Real.GammaSeq
    have : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) :=
      Finset.prod_pos fun j _ => by positivity
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hnorm : ∀ j : ℕ, ‖(x : ℂ) + y * I + j‖ = Real.sqrt ((x + j) ^ 2 + y ^ 2) := by
    intro j
    rw [show (x : ℂ) + y * I + j = ((x + j : ℝ) : ℂ) + y * I by push_cast; ring,
      Complex.norm_add_mul_I]
  have hr : ∀ j ∈ Finset.range (n + 1), 0 < (x + j) / ‖(x : ℂ) + y * I + j‖ := by
    intro j _
    rw [hnorm]
    have : 0 < x + (j : ℝ) := by positivity
    have : 0 < (x + j) ^ 2 + y ^ 2 := by positivity
    positivity
  rw [norm_GammaSeq_eq hx y hn, Real.log_mul hG.ne' (Finset.prod_pos hr).ne',
    Real.log_prod (fun j hj => (hr j hj).ne'), Finset.mul_sum]
  simp only [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hxj : 0 < x + (j : ℝ) := by positivity
  have hsq : 0 < (x + j) ^ 2 + y ^ 2 := by positivity
  rw [hnorm, Real.log_div hxj.ne' (Real.sqrt_pos.mpr hsq).ne', Real.log_sqrt hsq.le]
  unfold gammaShiftWeight
  have : 1 + y ^ 2 / (x + j) ^ 2 = ((x + j) ^ 2 + y ^ 2) / (x + j) ^ 2 := by
    field_simp
  rw [this, Real.log_div hsq.ne' (by positivity), Real.log_pow]
  push_cast
  ring

/-- The weights sum to `−2 (log‖Γ(x+iy)‖ − log Γ(x))`. -/
theorem hasSum_gammaShiftWeight {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasSum (fun j : ℕ => gammaShiftWeight x y j)
      (-2 * (Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ - Real.log (Real.Gamma x))) := by
  have hΓC : Complex.Gamma ((x : ℂ) + y * I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [hx])
  have hΓR : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hL := ((Complex.GammaSeq_tendsto_Gamma ((x : ℂ) + y * I)).norm.log
    (norm_ne_zero_iff.mpr hΓC)).sub ((Real.GammaSeq_tendsto_Gamma x).log hΓR.ne')
  have hS : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), gammaShiftWeight x y j) atTop
      (𝓝 (-2 * (Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ - Real.log (Real.Gamma x)))) := by
    refine (hL.const_mul (-2)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [log_norm_GammaSeq_sub hx y hn]
    ring
  exact (hasSum_iff_tendsto_nat_of_nonneg (fun j => gammaShiftWeight_nonneg x y j) _).mpr
    ((tendsto_add_atTop_iff_nat 1).mp hS)

/-- **Two-sided bounds for `|Γ(x+iy)|` in terms of `Γ(x)`.**  For `x > 0` and real `y`,
`−½(log(1+y²/x²) + I(x,y)) ≤ log|Γ(x+iy)| − log Γ(x) ≤ −½ I(x,y)` with
`I(x,y) = π|y| − x log(1+y²/x²) − 2|y| arctan(x/|y|) = ∫₀^∞ log(1 + y²/(x+u)²) du`. -/
theorem log_norm_Gamma_sub_log_Gamma_bounds {x : ℝ} (hx : 0 < x) (y : ℝ) :
    -(1 / 2) * (gammaShiftWeight x y 0 + gammaShiftIntegral x y) ≤
        Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ - Real.log (Real.Gamma x) ∧
      Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ - Real.log (Real.Gamma x) ≤
        -(1 / 2) * gammaShiftIntegral x y := by
  by_cases hy : y = 0
  · subst hy
    have h0 : gammaShiftIntegral x 0 = 0 := by simp [gammaShiftIntegral, gammaShiftPrimitive]
    have hw : gammaShiftWeight x 0 0 = 0 := by simp [gammaShiftWeight]
    have hΓ : ‖Complex.Gamma ((x : ℂ) + (0 : ℝ) * I)‖ = Real.Gamma x := by
      rw [show (x : ℂ) + ((0 : ℝ) : ℂ) * I = (x : ℂ) by simp, Complex.Gamma_ofReal,
        Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos hx).le]
    rw [h0, hw, hΓ]
    simp
  set L := Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ - Real.log (Real.Gamma x) with hLdef
  have hsum := hasSum_gammaShiftWeight hx y
  have hS := hsum.tendsto_sum_nat
  have hAnti : ∀ N : ℕ, AntitoneOn (fun u => gammaShiftWeight x y u) (Set.Icc 0 (0 + (N : ℝ))) :=
    fun N => (antitoneOn_gammaShiftWeight hx y).mono Set.Icc_subset_Ici_self
  have hlow : ∀ N : ℕ, ∫ u in (0 : ℝ)..(N : ℝ), gammaShiftWeight x y u ≤
      ∑ i ∈ Finset.range N, gammaShiftWeight x y i := by
    intro N
    have := (hAnti N).integral_le_sum
    simpa using this
  have hup : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), gammaShiftWeight x y i ≤
      gammaShiftWeight x y 0 + ∫ u in (0 : ℝ)..(N : ℝ), gammaShiftWeight x y u := by
    intro N
    have := (hAnti N).sum_le_integral
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add] at this ⊢
    push_cast at this ⊢
    linarith
  have hI := tendsto_integral_gammaShiftWeight hx hy
  constructor
  · have h1 : -2 * L ≤ gammaShiftWeight x y 0 + gammaShiftIntegral x y :=
      le_of_tendsto_of_tendsto' ((tendsto_add_atTop_iff_nat 1).mpr hS)
        (hI.const_add _) hup
    linarith
  · have h2 : gammaShiftIntegral x y ≤ -2 * L := le_of_tendsto_of_tendsto' hI hS hlow
    linarith

end

end HTGeometry
