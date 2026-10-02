import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLinearFloorCriterion
import GaloisForLFunctions.RHTower.RoutePCompletedErrorOneSidedLandau

/-!
# The nonlinear critical-mass comparison behind Route P

The literal Abel primitive is `sqrt(x)*primeMassHalf(x)-psi(x)`. Its right derivative
is the actual staircase mass divided by `2*sqrt(x)`, at every x>=1 including prime
entries. A quadratic upper barrier for this primitive forces a one-sided logarithmic
critical-mass discrepancy. The completed-error Landau theorem then forces RH.

This analytic implication does not assert that the source barrier holds. The
terminal-escape argument uses it inside a contradiction, with the complete finite
compensation retained.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

theorem routeP_primeMass_nonneg (x : ℝ) : 0 ≤ primeMassHalf x := by
  unfold primeMassHalf
  exact Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.sqrt_nonneg _)

theorem routeP_primeMass_mono : Monotone primeMassHalf := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxy)
  · intro n _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem routeP_primeMass_rightContinuous {x : ℝ} (hx : 0 ≤ x) :
    ContinuousWithinAt primeMassHalf (Ici x) x := by
  have heq : primeMassHalf =ᶠ[𝓝[≥] x] fun _ => primeMassHalf x := by
    filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with y hy
    have hy0 : 0 ≤ y := hx.trans hy.1
    have hf : ⌊y⌋₊ = ⌊x⌋₊ :=
      (Nat.floor_eq_iff hy0).mpr ⟨(Nat.floor_le hx).trans hy.1, hy.2⟩
    simp only [primeMassHalf, hf]
  exact continuousWithinAt_const.congr_of_eventuallyEq heq rfl

/-- A harmless extension below 1 makes the Abel density locally integrable on all of R. -/
def routePAbelMassDensity (x : ℝ) : ℝ := primeMassHalf x / (2 * Real.sqrt (max x 1))

theorem routePAbelMassDensity_nonneg (x : ℝ) : 0 ≤ routePAbelMassDensity x := by
  exact div_nonneg (routeP_primeMass_nonneg x) (by positivity)

theorem continuous_routePAbelWeight : Continuous (fun x : ℝ => (2 * Real.sqrt (max x 1))⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    have h : 0 < max x 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact (mul_pos (by norm_num) (Real.sqrt_pos.mpr h)).ne'

theorem intervalIntegrable_routePAbelMassDensity (a b : ℝ) :
    IntervalIntegrable routePAbelMassDensity volume a b := by
  change IntervalIntegrable (fun x => primeMassHalf x / (2 * Real.sqrt (max x 1))) volume a b
  simpa only [div_eq_mul_inv] using
    (routeP_primeMass_mono.intervalIntegrable (a := a) (b := b)).mul_continuousOn
      continuous_routePAbelWeight.continuousOn

theorem measurable_routePAbelMassDensity : Measurable routePAbelMassDensity := by
  convert! routeP_primeMass_mono.measurable.mul continuous_routePAbelWeight.measurable using 1

def routePAbelMassPrimitive (x : ℝ) : ℝ := ∫ t in (1:ℝ)..x, routePAbelMassDensity t

theorem continuous_routePAbelMassPrimitive : Continuous routePAbelMassPrimitive :=
  intervalIntegral.continuous_primitive intervalIntegrable_routePAbelMassDensity 1

theorem routePAbelMassPrimitive_rightDerivative {x : ℝ} (hx : 1 ≤ x) :
    HasDerivWithinAt routePAbelMassPrimitive
      (primeMassHalf x / (2 * Real.sqrt x)) (Ici x) x := by
  have hr : ContinuousWithinAt routePAbelMassDensity (Ici x) x := by
    convert! (routeP_primeMass_rightContinuous (zero_le_one.trans hx)).mul
      continuous_routePAbelWeight.continuousWithinAt using 1
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Ici x) (t := Ioi x) (intervalIntegrable_routePAbelMassDensity 1 x)
    measurable_routePAbelMassDensity.stronglyMeasurable.stronglyMeasurableAtFilter
    (hr.mono Ioi_subset_Ici_self)
  convert! hd using 1
  simp only [routePAbelMassDensity, max_eq_left hx]

theorem routePAbelMassPrimitive_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ routePAbelMassPrimitive x :=
  intervalIntegral.integral_nonneg hx fun t _ => routePAbelMassDensity_nonneg t

/-- Exact Abel identity, keeping the literal prime staircase. -/
theorem routePAbelMassPrimitive_eq {x : ℝ} (hx : 1 ≤ x) :
    routePAbelMassPrimitive x = Real.sqrt x * primeMassHalf x - Chebyshev.psi x := by
  let c : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt n
  have hc : c 0 = 0 := by simp [c]
  have hder (t : ℝ) (ht : 1 ≤ t) : deriv Real.sqrt t = 1 / (2 * Real.sqrt t) :=
    (Real.hasDerivAt_sqrt (ne_of_gt (zero_lt_one.trans_le ht))).deriv
  have hdiff : ∀ t ∈ Icc (1:ℝ) x, DifferentiableAt ℝ Real.sqrt t :=
    fun t ht => (Real.hasDerivAt_sqrt (ne_of_gt (zero_lt_one.trans_le ht.1))).differentiableAt
  have hint : IntegrableOn (deriv Real.sqrt) (Icc (1:ℝ) x) := by
    apply ContinuousOn.integrableOn_Icc
    have hcont : ContinuousOn (fun t : ℝ => 1 / (2 * Real.sqrt t)) (Icc 1 x) :=
      continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
        (fun t ht => (mul_pos (by norm_num)
          (Real.sqrt_pos.mpr (zero_lt_one.trans_le ht.1))).ne')
    exact hcont.congr (fun t ht => hder t ht.1)
  have hab := sum_mul_eq_sub_integral_mul₀ c hc x hdiff hint
  have hsum : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, Real.sqrt k * c k) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_sum_Icc]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n = 0
    · simp [hn, c]
    · dsimp [c]
      rw [mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn))]
  have hI : (∫ t in Ioc (1:ℝ) x, deriv Real.sqrt t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      routePAbelMassPrimitive x := by
    rw [routePAbelMassPrimitive, intervalIntegral.integral_of_le hx]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hder t ht.1.le, routePAbelMassDensity, max_eq_left ht.1.le]
    change 1 / (2 * Real.sqrt t) * primeMassHalf t = primeMassHalf t / (2 * Real.sqrt t)
    ring
  rw [hsum, hI] at hab
  change Chebyshev.psi x = Real.sqrt x * primeMassHalf x - routePAbelMassPrimitive x at hab
  linarith

/-- The actual Abel primitive has an unconditional positive linear lower scale. -/
theorem routePAbelMassPrimitive_eventually_linear_lower :
    ∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧ ∀ x : ℝ, A ≤ x → c * x ≤ routePAbelMassPrimitive x := by
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨L, hL⟩ := eventually_atTop.1 eventually_sqrt_le_primeMassHalf
  let A : ℝ := max L 1
  have hA : 1 ≤ A := le_max_right _ _
  have hdens : ∀ t : ℝ, A ≤ t → c / 2 ≤ routePAbelMassDensity t := by
    intro t ht
    have ht1 : 1 ≤ t := hA.trans ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (zero_lt_one.trans_le ht1)
    have hm := hL t ((le_max_left _ _).trans ht)
    change c * Real.sqrt t ≤ primeMassHalf t at hm
    rw [routePAbelMassDensity, max_eq_left ht1, le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨c / 4, 2 * A, by positivity, by linarith, ?_⟩
  intro x hx
  have hAx : A ≤ x := by linarith
  have hI := intervalIntegral.integral_mono_on hAx
    (continuous_const.intervalIntegrable A x) (intervalIntegrable_routePAbelMassDensity A x)
    (fun t ht => hdens t ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_routePAbelMassDensity 1 A) (intervalIntegrable_routePAbelMassDensity A x)
  change routePAbelMassPrimitive A + (∫ t in A..x, routePAbelMassDensity t) =
    routePAbelMassPrimitive x at hsplit
  have hFA := routePAbelMassPrimitive_nonneg hA
  nlinarith

/-- A quadratic upper barrier for the Abel primitive forces a logarithmic one-sided
critical-mass discrepancy. Prime jumps are handled by right derivatives at every point. -/
theorem routeP_mass_logarithmic_lower_of_quadraticAbelBound {C X b : ℝ} (hb : 0 < b)
    (hbound : ∀ x : ℝ, X ≤ x →
      routePAbelMassPrimitive x - C ≤ (primeMassHalf x + 2 * b) ^ 2 / 4) :
    ∃ A D L : ℝ, 0 < A ∧ 1 ≤ L ∧ ∀ x : ℝ, L ≤ x →
      2 * Real.sqrt x - A * Real.log x - D ≤ primeMassHalf x := by
  obtain ⟨c, T, hc, hT, hF⟩ := routePAbelMassPrimitive_eventually_linear_lower
  let L : ℝ := max (max T X) (max 1 (2 * |C| / c))
  have hLT : T ≤ L := (le_max_left T X).trans (le_max_left _ _)
  have hLX : X ≤ L := (le_max_right T X).trans (le_max_left _ _)
  have hL1 : 1 ≤ L := (le_max_left 1 _).trans (le_max_right _ _)
  have hLC : 2 * |C| / c ≤ L := (le_max_right 1 _).trans (le_max_right _ _)
  let a : ℝ := Real.sqrt (c / 2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = c / 2 := Real.sq_sqrt (by positivity)
  let Z : ℝ → ℝ := fun x => Real.sqrt (routePAbelMassPrimitive x - C)
  have hG (x : ℝ) (hx : L ≤ x) : a ^ 2 * x ≤ routePAbelMassPrimitive x - C := by
    have hCx : 2 * |C| ≤ x * c := (div_le_iff₀ hc).mp (hLC.trans hx)
    have hFx := hF x (hLT.trans hx)
    rw [ha2]
    nlinarith [le_abs_self C]
  have hGpos (x : ℝ) (hx : L ≤ x) : 0 < routePAbelMassPrimitive x - C :=
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos ha) (zero_lt_one.trans_le (hL1.trans hx))) (hG x hx)
  have hZ (x : ℝ) (hx : L ≤ x) : a * Real.sqrt x ≤ Z x := by
    have hx0 : 0 ≤ x := zero_le_one.trans (hL1.trans hx)
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt (hGpos x hx).le]
    exact hG x hx
  have hM (x : ℝ) (hx : L ≤ x) : 2 * Z x - 2 * b ≤ primeMassHalf x := by
    have hb := hbound x (hLX.trans hx)
    have hz2 : (Z x) ^ 2 = routePAbelMassPrimitive x - C := Real.sq_sqrt (hGpos x hx).le
    have hm := routeP_primeMass_nonneg x
    have hz0 : 0 ≤ Z x := Real.sqrt_nonneg _
    nlinarith
  let k : ℝ := b / (2 * a)
  have hk : 0 < k := by dsimp [k]; positivity
  let f : ℝ → ℝ := fun x => Real.sqrt x - Z x
  let f' : ℝ → ℝ := fun x => 1 / (2 * Real.sqrt x) -
    (primeMassHalf x / (2 * Real.sqrt x)) / (2 * Z x)
  have hfc : Continuous f :=
    Real.continuous_sqrt.sub (Real.continuous_sqrt.comp (continuous_routePAbelMassPrimitive.sub continuous_const))
  have hfd (x : ℝ) (hx : L ≤ x) : HasDerivWithinAt f (f' x) (Ici x) x := by
    have hx1 := hL1.trans hx
    exact (Real.hasDerivAt_sqrt (ne_of_gt (zero_lt_one.trans_le hx1))).hasDerivWithinAt.sub
      (((routePAbelMassPrimitive_rightDerivative hx1).sub_const C).sqrt (hGpos x hx).ne')
  have hrate (x : ℝ) (hx : L ≤ x) : f' x ≤ k * x⁻¹ := by
    have hx0 : 0 < x := zero_lt_one.trans_le (hL1.trans hx)
    have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hz : 0 < Z x := Real.sqrt_pos.mpr (hGpos x hx)
    have hm := hM x hx
    have hzx := hZ x hx
    have hr2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
    have hden : 2 * a * x ≤ 2 * Real.sqrt x * Z x := by nlinarith
    have heq : f' x = (2 * Z x - primeMassHalf x) / (4 * Real.sqrt x * Z x) := by
      dsimp [f']
      field_simp
      ring
    rw [heq]
    calc
      (2 * Z x - primeMassHalf x) / (4 * Real.sqrt x * Z x) ≤
          (2 * b) / (4 * Real.sqrt x * Z x) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = b / (2 * Real.sqrt x * Z x) := by field_simp; ring
      _ ≤ b / (2 * a * x) := div_le_div_of_nonneg_left hb.le (by positivity) hden
      _ = k * x⁻¹ := by dsimp [k]; field_simp
  let d : ℝ := f L - k * Real.log L
  have hfbound (x : ℝ) (hx : L ≤ x) : f x ≤ k * Real.log x + d := by
    apply image_le_of_deriv_right_le_deriv_boundary (a := L) (b := x)
      hfc.continuousOn (fun y hy => hfd y hy.1) (B' := fun y => k * y⁻¹)
    · dsimp [d]; linarith
    · intro y hy
      exact (((Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans_le (hL1.trans hy.1)))).const_mul k).add_const d).continuousAt.continuousWithinAt
    · intro y hy
      exact (((Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans_le (hL1.trans hy.1)))).const_mul k).add_const d).hasDerivWithinAt
    · intro y hy
      exact hrate y hy.1
    · exact ⟨hx, le_rfl⟩
  refine ⟨2 * k, 2 * d + 2 * b, L, by positivity, hL1, ?_⟩
  intro x hx
  have hb := hfbound x hx
  have hm := hM x hx
  dsimp [f] at hb
  linarith

/-- A quadratic Abel barrier would force RH; the source barrier is not assumed proved. -/
theorem riemannHypothesis_of_primeMass_quadraticAbelBound {C X b : ℝ} (hb : 0 < b)
    (hbound : ∀ x : ℝ, X ≤ x →
      routePAbelMassPrimitive x - C ≤ (primeMassHalf x + 2 * b) ^ 2 / 4) : RiemannHypothesis := by
  obtain ⟨A, D, L, hA, hL, hm⟩ := routeP_mass_logarithmic_lower_of_quadraticAbelBound hb hbound
  refine riemannHypothesis_of_completedError_eventually_linear_upper
    (C := A + |D|) (L := max 0 (Real.log L)) ?_
  intro t ht
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have hLt : L ≤ Real.exp t := by
    rw [← Real.exp_log (zero_lt_one.trans_le hL)]
    exact Real.exp_le_exp.mpr ((le_max_right _ _).trans ht)
  have hmass := hm (Real.exp t) hLt
  rw [Real.log_exp, ← Real.exp_half] at hmass
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass, criticalMellinPrimeMass_eq_primeMassHalf,
    Real.sinh_eq]
  have he := Real.exp_pos (-(t / 2))
  nlinarith [le_abs_self D, abs_nonneg D]

end
end RHTower
