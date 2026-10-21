import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeWindowCalculus

/-!
# Archimedean bounds for curved window gauges

Elementary two-sided bounds on the archimedean densities `ω(u) = e^{−u/2}/(1 − e^{−2u})` and
`ν(u) = e^{−2u}/(1 − e^{−2u})` on short windows, sharp to second order:

* `½ + u/4 − u²/48 − u³/32 ≤ u ω(u) ≤ ½ + u/4 − u²/48` on `(0, 1]`, from
  `ω(u) = 1/(4 sinh(u/2)) + 1/(4 cosh(u/2))` (`mul_archLevyDensity_ge_sharp`,
  `mul_archLevyDensity_le_sharp`), and the cruder `½ + u/4 − u²/16 ≤ u ω(u) ≤ ½ + u/4`;
* `ω − ν ≤ 3/4 − u/6` on `(0, 3/5]` (`archLevyDensity_sub_archDiagonalDensity_le_sharp`), hence the
  one-sided window killing `∫_0^∞ (ν − ω 1_{u ≤ a}) ≥ N(a) − (3/4) a + a²/12`;
* the window killing itself, `N(s) = −½ log(1 − e^{−2s}) ≥ −½ log(2s) + s/2 − s²/12`, from
  `1 − e^{−2s} = 2 e^{−s} sinh s` and `sinh s ≤ s e^{s²/6}` (`neg_half_log_one_sub_exp_ge_sharp`);
* past the plastic threshold the pole density exceeds `ω` by at most `6.5 (t − 0.275)` on
  `[0.275, 0.55]` (`two_mul_cosh_sub_archLevyDensity_le_linear`).

The second-order terms of the killing (`−s²/12` per side) and of the density difference (`+a²/12` per
side) cancel exactly in the window potential.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Taylor bounds of higher order -/

/-- `e^x ≤ T₅(x) + |x|⁶/617` for `|x| ≤ 1`. -/
theorem exp_le_taylor_six {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + |x| ^ 6 / 617 := by
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  have h6 : |x| ^ 6 * (7 / 4320) ≤ |x| ^ 6 / 617 := by
    have : 0 ≤ |x| ^ 6 := by positivity
    nlinarith
  linarith

/-- `e^x ≥ T₅(x) − |x|⁶/617` for `|x| ≤ 1`. -/
theorem taylor_six_le_exp {x : ℝ} (hx : |x| ≤ 1) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 - |x| ^ 6 / 617 ≤ Real.exp x := by
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).1
  have h6 : |x| ^ 6 * (7 / 4320) ≤ |x| ^ 6 / 617 := by
    have : 0 ≤ |x| ^ 6 := by positivity
    nlinarith
  linarith

/-- `e^x ≤ T₆(x) + |x|⁷/4410` for `|x| ≤ 1`. -/
theorem exp_le_taylor_seven {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 +
      |x| ^ 7 / 4410 := by
  have h := Real.exp_bound hx (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  have h7 : |x| ^ 7 * (8 / 35280) ≤ |x| ^ 7 / 4410 := by
    have : 0 ≤ |x| ^ 7 := by positivity
    nlinarith
  linarith

/-- `e^x ≥ T₆(x) − |x|⁷/4410` for `|x| ≤ 1`. -/
theorem taylor_seven_le_exp {x : ℝ} (hx : |x| ≤ 1) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 - |x| ^ 7 / 4410 ≤
      Real.exp x := by
  have h := Real.exp_bound hx (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).1
  have h7 : |x| ^ 7 * (8 / 35280) ≤ |x| ^ 7 / 4410 := by
    have : 0 ≤ |x| ^ 7 := by positivity
    nlinarith
  linarith

/-! ### The Lévy density times `u` -/

/-- `ω(t) = 1/(4 sinh(t/2)) + 1/(4 cosh(t/2))`. -/
theorem archLevyDensity_eq_inv_sinh_add_inv_cosh {t : ℝ} (ht : 0 < t) :
    archLevyDensity t = 1 / (4 * Real.sinh (t / 2)) + 1 / (4 * Real.cosh (t / 2)) := by
  set v := Real.exp (-t / 2) with hvdef
  have hv0 : 0 < v := Real.exp_pos _
  have hv1 : v < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinv : Real.exp (t / 2) = v⁻¹ := by
    rw [hvdef, ← Real.exp_neg]; ring_nf
  have e2 : Real.exp (-2 * t) = v ^ 4 := by
    rw [hvdef, ← Real.exp_nat_mul]; ring_nf
  have hs : Real.sinh (t / 2) = (1 - v ^ 2) / (2 * v) := by
    rw [Real.sinh_eq, hinv, show -(t / 2) = -t / 2 by ring, ← hvdef]
    field_simp
  have hc : Real.cosh (t / 2) = (1 + v ^ 2) / (2 * v) := by
    rw [Real.cosh_eq, hinv, show -(t / 2) = -t / 2 by ring, ← hvdef]
    field_simp
  have h1 : 1 - v ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 + v ^ 2 ≠ 0 := by positivity
  have h3 : 1 - v ^ 4 ≠ 0 := by nlinarith [pow_lt_one₀ hv0.le hv1 (show (4 : ℕ) ≠ 0 by norm_num)]
  unfold archLevyDensity
  rw [← hvdef, e2, hs, hc]
  field_simp
  ring

/-- Two-sided bounds on `[0, 1]`: `z + z³/6 ≤ sinh z`, `(1 − z²/6) sinh z ≤ z`, `1 + z²/2 ≤ cosh z`,
`(1 − z²/2) cosh z ≤ 1`. -/
theorem sinh_cosh_taylor_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    z + z ^ 3 / 6 ≤ Real.sinh z ∧ (1 - z ^ 2 / 6) * Real.sinh z ≤ z ∧
      1 + z ^ 2 / 2 ≤ Real.cosh z ∧ (1 - z ^ 2 / 2) * Real.cosh z ≤ 1 := by
  have hz : |z| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have hzn : |-z| ≤ 1 := by rwa [abs_neg]
  have hp := exp_le_taylor_six hz
  have hp' := taylor_six_le_exp hz
  have hm := exp_le_taylor_six hzn
  have hm' := taylor_six_le_exp hzn
  rw [abs_neg, abs_of_nonneg h0] at hm hm'
  rw [abs_of_nonneg h0] at hp hp'
  have h65 : z ^ 6 ≤ z ^ 5 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h54 : z ^ 5 ≤ z ^ 4 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h4 : 0 ≤ z ^ 4 := by positivity
  have h5 : 0 ≤ z ^ 5 := by positivity
  have hS1 : Real.sinh z ≤ z + z ^ 3 / 6 + z ^ 5 / 120 + z ^ 6 / 617 := by
    rw [Real.sinh_eq]; linarith
  have hC1 : Real.cosh z ≤ 1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 617 := by
    rw [Real.cosh_eq]; linarith
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  refine ⟨by rw [Real.sinh_eq]; linarith, ?_, by rw [Real.cosh_eq]; linarith, ?_⟩
  · have hA : 0 ≤ 1 - z ^ 2 / 6 := by linarith
    have := mul_le_mul_of_nonneg_left hS1 hA
    nlinarith [mul_nonneg h5 (sq_nonneg z), mul_nonneg (mul_nonneg h5 h0) (sq_nonneg z)]
  · have hA : 0 ≤ 1 - z ^ 2 / 2 := by linarith
    have := mul_le_mul_of_nonneg_left hC1 hA
    nlinarith [mul_nonneg h4 (sq_nonneg z), mul_nonneg (mul_nonneg h4 (sq_nonneg z)) (sq_nonneg z)]

/-- **Sharp upper bound** `u ω(u) ≤ ½ + u/4 − u²/48` on `(0, 1]`. -/
theorem mul_archLevyDensity_le_sharp {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    u * archLevyDensity u ≤ 1 / 2 + u / 4 - u ^ 2 / 48 := by
  set z := u / 2 with hz
  have hz0 : 0 < z := by rw [hz]; linarith
  obtain ⟨hs1, -, hc1, -⟩ := sinh_cosh_taylor_bounds hz0.le (by rw [hz]; linarith)
  have hS : 0 < Real.sinh z := by nlinarith [pow_pos hz0 3]
  have hC : 0 < Real.cosh z := Real.cosh_pos z
  rw [archLevyDensity_eq_inv_sinh_add_inv_cosh h0, ← hz]
  have e : u * (1 / (4 * Real.sinh z) + 1 / (4 * Real.cosh z)) =
      z / (2 * Real.sinh z) + z / (2 * Real.cosh z) := by
    rw [hz]; field_simp; ring
  rw [e]
  have hA : 0 ≤ 1 - z ^ 2 / 6 + z ^ 4 / 36 := by nlinarith [sq_nonneg (z ^ 2 / 6 - 1 / 2)]
  have hB : 0 ≤ 1 - z ^ 2 / 2 + z ^ 4 / 4 := by nlinarith [sq_nonneg (z ^ 2 / 2 - 1 / 2)]
  have k1 : z / (2 * Real.sinh z) ≤ (1 - z ^ 2 / 6 + z ^ 4 / 36) / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs1 hA, pow_pos hz0 7]
  have k2 : z / (2 * Real.cosh z) ≤ z / 2 * (1 - z ^ 2 / 2 + z ^ 4 / 4) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hz0.le hB), pow_pos hz0 7]
  have hpoly : (1 - z ^ 2 / 6 + z ^ 4 / 36) / 2 + z / 2 * (1 - z ^ 2 / 2 + z ^ 4 / 4) ≤
      1 / 2 + u / 4 - u ^ 2 / 48 := by
    rw [hz]
    nlinarith [pow_pos h0 3, mul_nonneg (pow_pos h0 3).le (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_nonneg (pow_pos h0 4).le (by linarith : (0 : ℝ) ≤ 1 - u)]
  linarith

/-- **Sharp lower bound** `u ω(u) ≥ ½ + u/4 − u²/48 − u³/32` on `(0, 1]`. -/
theorem mul_archLevyDensity_ge_sharp {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 ≤ u * archLevyDensity u := by
  set z := u / 2 with hz
  have hz0 : 0 < z := by rw [hz]; linarith
  obtain ⟨hs1, hs2, -, hc2⟩ := sinh_cosh_taylor_bounds hz0.le (by rw [hz]; linarith)
  have hS : 0 < Real.sinh z := by nlinarith [pow_pos hz0 3]
  have hC : 0 < Real.cosh z := Real.cosh_pos z
  rw [archLevyDensity_eq_inv_sinh_add_inv_cosh h0, ← hz]
  have e : u * (1 / (4 * Real.sinh z) + 1 / (4 * Real.cosh z)) =
      z / (2 * Real.sinh z) + z / (2 * Real.cosh z) := by
    rw [hz]; field_simp; ring
  rw [e]
  have k1 : (1 - z ^ 2 / 6) / 2 ≤ z / (2 * Real.sinh z) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have k2 : z / 2 * (1 - z ^ 2 / 2) ≤ z / (2 * Real.cosh z) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hc2 hz0.le]
  have hpoly : 1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 =
      (1 - z ^ 2 / 6) / 2 + z / 2 * (1 - z ^ 2 / 2) := by rw [hz]; ring
  linarith

/-- **Upper bound** `u ω(u) ≤ ½ + u/4` on `(0, 1]`. -/
theorem mul_archLevyDensity_le {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    u * archLevyDensity u ≤ 1 / 2 + u / 4 := by
  have := mul_archLevyDensity_le_sharp h0 h1
  nlinarith [sq_nonneg u]

/-- **Lower bound** `u ω(u) ≥ ½ + u/4 − u²/16` on `(0, 1]`. -/
theorem mul_archLevyDensity_ge {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    1 / 2 + u / 4 - u ^ 2 / 16 ≤ u * archLevyDensity u := by
  have := mul_archLevyDensity_ge_sharp h0 h1
  nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ 4 / 3 - u)]

/-! ### The density difference -/

/-- **The sharp density difference** `ω − ν ≤ 3/4 − u/6` on `(0, 3/5]`. With `z = e^{−u/2}`,
`u ≤ 1/z − z` (`sinh` dominates its argument) reduces it to `2P(z) = (z − 1)² Q(z) ≥ 0`. -/
theorem archLevyDensity_sub_archDiagonalDensity_le_sharp {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 3 / 5) :
    archLevyDensity u - archDiagonalDensity u ≤ 3 / 4 - u / 6 := by
  set z := Real.exp (-u / 2) with hz
  have hz0 : 0 < z := Real.exp_pos _
  have hz1 : z < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hzlow : 0.74 ≤ z := by
    have hT := taylor_le_exp_neg (x := 0.3) (by norm_num) (by norm_num)
    have : Real.exp (-(3 / 10)) ≤ z := Real.exp_le_exp.mpr (by linarith)
    norm_num at hT
    linarith
  have h4 : Real.exp (-2 * u) = z ^ 4 := by
    rw [hz, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hinv : Real.exp (u / 2) = z⁻¹ := by rw [hz, ← Real.exp_neg]; ring_nf
  have hsinh : u ≤ z⁻¹ - z := by
    have h := (Real.self_le_sinh_iff (x := u / 2)).mpr (by linarith)
    rw [Real.sinh_eq, hinv, show -(u / 2) = -u / 2 by ring, ← hz] at h
    linarith
  have hden : 0 < 1 - z ^ 4 := by
    have : z ^ 4 < 1 := pow_lt_one₀ hz0.le hz1 (by norm_num)
    linarith
  have hQ : 0 ≤ -2 * z ^ 4 - z ^ 3 + 2 * z ^ 2 + 5 * z - 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ z - 0.74) (by linarith : (0 : ℝ) ≤ 1 - z)]
  have hP : 6 * z ^ 2 - 6 * z ^ 5 ≤ (9 / 2 * z - 1 + z ^ 2) * (1 - z ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (z - 1)) hQ]
  unfold archLevyDensity archDiagonalDensity
  rw [h4, ← hz, div_sub_div_same, div_le_iff₀ hden]
  have hzb : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0.ne'
  have hb0 : 0 < z⁻¹ := inv_pos.mpr hz0
  -- `3/4 − u/6 ≥ 3/4 − (z⁻¹ − z)/6`
  have hstep : (3 / 4 - (z⁻¹ - z) / 6) * (1 - z ^ 4) ≤ (3 / 4 - u / 6) * (1 - z ^ 4) :=
    mul_le_mul_of_nonneg_right (by linarith) hden.le
  have hpoly : z - z ^ 4 ≤ (3 / 4 - (z⁻¹ - z) / 6) * (1 - z ^ 4) := by
    have hm : 6 * z * (z - z ^ 4) ≤ 6 * z * ((3 / 4 - (z⁻¹ - z) / 6) * (1 - z ^ 4)) := by
      have e : 6 * z * ((3 / 4 - (z⁻¹ - z) / 6) * (1 - z ^ 4)) =
          (9 / 2 * z - 1 + z ^ 2) * (1 - z ^ 4) := by
        field_simp
        ring
      rw [e]
      nlinarith
    exact le_of_mul_le_mul_left hm (by positivity)
  linarith

/-- **The sharp one-sided window killing.** For `0 < a ≤ 3/5`,
`∫_0^∞ (ν − ω 1_{u ≤ a}) ≥ N(a) − (3/4) a + a²/12`. -/
theorem integral_one_sided_window_ge_sharp {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 3 / 5) :
    IntegrableOn (fun u => if u ≤ a then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) (Ioi 0) ∧
      -(1 / 2) * Real.log (1 - Real.exp (-2 * a)) - 3 / 4 * a + a ^ 2 / 12 ≤
        ∫ u in Ioi (0 : ℝ), (if u ≤ a then archDiagonalDensity u - archLevyDensity u
          else archDiagonalDensity u) := by
  obtain ⟨hint, -⟩ := integral_one_sided_window_ge ha
  refine ⟨hint, ?_⟩
  have hunion : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hmeasD : Measurable archDiagonalDensity := by unfold archDiagonalDensity; fun_prop
  have hbd : ∀ u ∈ Ioc (0 : ℝ) a, |archDiagonalDensity u - archLevyDensity u| ≤ 3 / 4 := by
    intro u hu
    have h1 := archLevyDensity_sub_archDiagonalDensity_le hu.1
    have h2 : archDiagonalDensity u ≤ archLevyDensity u := archDiagonalDensity_le hu.1
    rw [abs_le]
    constructor <;> linarith
  have hI1 : IntegrableOn (fun u => archDiagonalDensity u - archLevyDensity u) (Ioc 0 a) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 4) (by simp)
      ((hmeasD.sub measurable_archLevyDensity).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs]; exact hbd u hu)
  rw [hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (hunion ▸ subset_union_left)) (hint.mono_set (hunion ▸ subset_union_right))]
  have e1 : (∫ u in Ioc 0 a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [if_pos hu.2]
  have e2 : (∫ u in Ioi a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioi a, archDiagonalDensity u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [if_neg (not_le.mpr hu)]
  have hlin : IntegrableOn (fun u : ℝ => -(3 / 4) + u / 6) (Ioc 0 a) :=
    (continuous_const.add (continuous_id.div_const 6)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlow : (∫ u in Ioc 0 a, (-(3 / 4) + u / 6)) ≤
      ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) :=
    setIntegral_mono_on hlin hI1 measurableSet_Ioc fun u hu => by
      have := archLevyDensity_sub_archDiagonalDensity_le_sharp hu.1 (hu.2.trans ha1)
      linarith
  have hval : (∫ u in Ioc 0 a, (-(3 / 4) + u / 6)) = -(3 / 4) * a + a ^ 2 / 12 := by
    rw [← intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_add
      (f := fun _ => -(3 / 4 : ℝ)) (g := fun x : ℝ => x / 6) intervalIntegrable_const
      ((continuous_id.div_const 6).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_div, integral_id]
    simp
    ring
  rw [e1, e2, integral_Ioi_archDiagonalDensity ha]
  linarith

/-! ### Integrals of `u ω` and `u² ω` -/

theorem measurable_mul_archLevyDensity : Measurable fun u : ℝ => u * archLevyDensity u :=
  measurable_id.mul measurable_archLevyDensity

theorem integrableOn_mul_archLevyDensity {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1) :
    IntegrableOn (fun u => u * archLevyDensity u) (Ioc c d) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    measurable_mul_archLevyDensity.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 < u := lt_of_le_of_lt hc hu.1
  have h1 := mul_archLevyDensity_le hu0 (hu.2.trans hd)
  have h2 := mul_nonneg hu0.le (archLevyDensity_pos hu0).le
  rw [Real.norm_eq_abs, abs_of_nonneg h2]
  linarith [hu.2]

/-- `∫_c^d u ω(u) du ≤ (d − c)/2 + (d² − c²)/8` for `0 ≤ c ≤ d ≤ 1`. -/
theorem integral_mul_archLevyDensity_le {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    (∫ u in Ioc c d, u * archLevyDensity u) ≤ (d - c) / 2 + (d ^ 2 - c ^ 2) / 8 := by
  have hlin : IntegrableOn (fun u : ℝ => 1 / 2 + u / 4) (Ioc c d) :=
    (continuous_const.add (continuous_id.div_const 4)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := setIntegral_mono_on (integrableOn_mul_archLevyDensity hc hd) hlin measurableSet_Ioc
    fun u hu => mul_archLevyDensity_le (lt_of_le_of_lt hc hu.1) (hu.2.trans hd)
  have hval : (∫ u in Ioc c d, (1 / 2 + u / 4)) = (d - c) / 2 + (d ^ 2 - c ^ 2) / 8 := by
    rw [← intervalIntegral.integral_of_le hcd, intervalIntegral.integral_add
      (f := fun _ => (1 / 2 : ℝ)) (g := fun x : ℝ => x / 4) intervalIntegrable_const
      ((continuous_id.div_const 4).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_div, integral_id]
    simp
    ring
  linarith

theorem integrableOn_sq_mul_archLevyDensity {a : ℝ} (ha : a ≤ 1) :
    IntegrableOn (fun u => u ^ 2 * archLevyDensity u) (Ioc 0 a) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_id.pow_const 2).mul measurable_archLevyDensity).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
  have h1 := mul_archLevyDensity_le hu.1 (hu.2.trans ha)
  have h2 := mul_nonneg hu.1.le (archLevyDensity_pos hu.1).le
  have hu1 : u ≤ 1 := hu.2.trans ha
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg u) (archLevyDensity_pos hu.1).le)]
  have : u ^ 2 * archLevyDensity u = u * (u * archLevyDensity u) := by ring
  rw [this]
  nlinarith [hu.1]

/-- `∫_0^a u² ω(u) du ≥ a²/4 + a³/12 − a⁴/64` for `0 < a ≤ 1`. -/
theorem integral_sq_mul_archLevyDensity_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ 2 / 4 + a ^ 3 / 12 - a ^ 4 / 64 ≤ ∫ u in Ioc 0 a, u ^ 2 * archLevyDensity u := by
  have hpoly : IntegrableOn (fun u : ℝ => u / 2 + u ^ 2 / 4 - u ^ 3 / 16) (Ioc 0 a) :=
    (by fun_prop : Continuous fun u : ℝ => u / 2 + u ^ 2 / 4 - u ^ 3 / 16).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have h := setIntegral_mono_on hpoly (integrableOn_sq_mul_archLevyDensity (by linarith))
    measurableSet_Ioc fun u hu => by
      have := mul_archLevyDensity_ge hu.1 (hu.2.trans ha1)
      have e : u ^ 2 * archLevyDensity u = u * (u * archLevyDensity u) := by ring
      rw [e]
      nlinarith [hu.1]
  have hval : (∫ u in Ioc 0 a, (u / 2 + u ^ 2 / 4 - u ^ 3 / 16)) =
      a ^ 2 / 4 + a ^ 3 / 12 - a ^ 4 / 64 := by
    rw [← intervalIntegral.integral_of_le ha.le]
    have i1 : IntervalIntegrable (fun u : ℝ => u / 2) volume 0 a :=
      (continuous_id.div_const 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u : ℝ => u ^ 2 / 4) volume 0 a :=
      ((continuous_pow 2).div_const 4).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u : ℝ => u ^ 3 / 16) volume 0 a :=
      ((continuous_pow 3).div_const 16).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_div, intervalIntegral.integral_div, intervalIntegral.integral_div,
      integral_id, integral_pow, integral_pow]
    norm_num
    ring
  linarith

/-! ### The window killing -/

/-- `sinh s ≤ s e^{s²/6}` for `0 ≤ s ≤ 1`. -/
theorem sinh_le_mul_exp_sq_div_six {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Real.sinh s ≤ s * Real.exp (s ^ 2 / 6) := by
  have hp := exp_le_taylor_seven (x := s) (by rw [abs_of_nonneg h0]; exact h1)
  have hm := taylor_seven_le_exp (x := -s) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at hp
  rw [abs_neg, abs_of_nonneg h0] at hm
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 6)
  have hs7 : s ^ 7 ≤ s ^ 5 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have hsinh : Real.sinh s ≤ s + s ^ 3 / 6 + s ^ 5 / 120 + s ^ 7 / 4410 := by
    rw [Real.sinh_eq]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hq h0, pow_nonneg h0 5, pow_nonneg h0 7]

/-- **The sharp window killing** `N(s) ≥ −½ log(2s) + s/2 − s²/12` for `0 < s ≤ 1`. -/
theorem neg_half_log_one_sub_exp_ge_sharp {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) :
    -(1 / 2) * Real.log (2 * s) + s / 2 - s ^ 2 / 12 ≤
      -(1 / 2) * Real.log (1 - Real.exp (-2 * s)) := by
  have hpos : 0 < 1 - Real.exp (-2 * s) := by
    have : Real.exp (-2 * s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hid : 1 - Real.exp (-2 * s) = 2 * Real.exp (-s) * Real.sinh s := by
    rw [Real.sinh_eq, mul_assoc, mul_div_assoc', mul_sub, ← Real.exp_add, ← Real.exp_add]
    norm_num
    ring_nf
  have hle : 1 - Real.exp (-2 * s) ≤ 2 * s * Real.exp (-s + s ^ 2 / 6) := by
    rw [hid, Real.exp_add]
    have := sinh_le_mul_exp_sq_div_six h0.le h1
    have he := Real.exp_pos (-s)
    nlinarith
  have hl := Real.log_le_log hpos hle
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hl
  linarith

/-! ### Past the plastic threshold -/

/-- **The negative density is linear past the plastic threshold**: for `0.275 ≤ t ≤ 0.55`,
`2cosh(t/2) − ω(t) ≤ 6.5 (t − 0.275)`. -/
theorem two_mul_cosh_sub_archLevyDensity_le_linear {t : ℝ} (h0 : 0.275 ≤ t) (h1 : t ≤ 0.55) :
    2 * Real.cosh (t / 2) - archLevyDensity t ≤ 6.5 * (t - 0.275) := by
  have ht0 : 0 < t := by linarith
  have hω := mul_archLevyDensity_ge ht0 (by linarith)
  have hp := exp_le_taylor_five (x := t / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hm := exp_le_taylor_five (x := -(t / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (by linarith : (0 : ℝ) < t / 2)] at hp
  rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < t / 2)] at hm
  have hc : 2 * Real.cosh (t / 2) ≤ 2 + t ^ 2 / 4 + t ^ 4 / 192 + t ^ 5 / 1600 := by
    rw [Real.cosh_eq]
    nlinarith
  -- multiply through by `t`
  have hkey : t * (2 + t ^ 2 / 4 + t ^ 4 / 192 + t ^ 5 / 1600) - (1 / 2 + t / 4 - t ^ 2 / 16) ≤
      t * (6.5 * (t - 0.275)) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 0.275) (by linarith : (0 : ℝ) ≤ 0.55 - t),
      pow_pos ht0 3, pow_pos ht0 4, pow_pos ht0 5, pow_pos ht0 6]
  have : t * (2 * Real.cosh (t / 2) - archLevyDensity t) ≤ t * (6.5 * (t - 0.275)) := by
    nlinarith [mul_le_mul_of_nonneg_left hc ht0.le]
  exact le_of_mul_le_mul_left this ht0

/-! ### Two logarithms -/

/-- `log(5/2) > 0.9162871`. -/
theorem log_five_halves_gt : 0.9162871 < Real.log (5 / 2) := by
  have h2 := Real.log_two_gt_d9
  have h54 : 0.22314 < Real.log (5 / 4) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := exp_le_taylor_five (x := 0.22314) (by norm_num [abs_of_pos])
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.22314)] at this
    norm_num at this ⊢
    linarith
  have e : Real.log (5 / 2) = Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e]
  linarith

/-- `log(4/3) > 0.2876`. -/
theorem log_four_thirds_gt : 0.2876 < Real.log (4 / 3) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := exp_le_taylor_five (x := 0.2876) (by norm_num [abs_of_pos])
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.2876)] at this
  norm_num at this ⊢
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
