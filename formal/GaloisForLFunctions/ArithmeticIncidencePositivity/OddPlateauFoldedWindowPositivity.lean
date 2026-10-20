import GaloisForLFunctions.ArithmeticCriticalityTheory.PoleConductanceWindowWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.ArchimedeanZTypeLaw
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper

/-!
# Odd-sector Weil positivity on `[−7/25, 7/25]`: the folded odd plateau gauge

Let `P` be an even plateau gauge, `0 ≤ P ≤ 1`, `P = 1` on `[−r, r]`, `P = 0` outside `(−R, R)`,
`2R < log 2`, and let `F` be odd and supported in `[−r, r]`. In the ground-state representation
`Q(F) = J_P(F) − ∫ F² 𝒲P` every jump of length `t` joins a pair `(x, x + t)`. For odd `F` and even `P`
the crossing pair `(−a, b)` (`a, b > 0`) carries the squared sum `(F(a) + F(b))²` at the archimedean
rate `ω(a + b)`, while the same-side pair `(a, b)` carries `(F(a) − F(b))²` at the rate `ω(|a − b|)`.
Since `ω` is decreasing,

    ω(|a − b|)(F(a) − F(b))² + ω(a + b)(F(a) + F(b))² ≥ 2ω(a + b)(F(a)² + F(b)²),

and the archimedean jump energy folds into a killing potential (`fourKilling_le_archJump`):

    J_P(F) ≥ 4 ∫_{x>0} F(x)² (Ω(x) − Ω(x + r)) dx,      Ω(y) = ∫_y^∞ ω.

In the language of conductances: the crossing conductances of the odd gauge `sign(x) P(x)` are
dominated pair by pair by the same-side ones (the archimedean Z-type law), and what remains is a
positive potential `2(Ω(|x|) − Ω(|x| + r))`, logarithmically large at the origin. The pole is not
converted into a conductance: for odd tests it costs only `2(∫ F sinh(x/2))² ≤ (R³/3) cosh²(R/2) ∫F²`.

The plateau potential has an exact closed form through the edge function
`E(u) = log(1 + e^{−u/2}) + ½ log(1 + e^{−u}) + arctan(e^{−u/2}) = Ω(u) − N(u)`
(`integral_one_sided_window_eq`): `∫_0^∞ (ν − ω 1_{u ≤ a}) = Ω(a) − E(0)`, `E(0) = ½ log 8 + π/4`, so at a
plateau point (`neg_poleFreeWeilOperator_ge_antideriv`)

    −𝒲P(x) ≥ Ω(R − x) + Ω(R + x) − log 8 − π/2 − (γ + log π).

With `½ log(4/y) + π/4 − y/4 ≤ Ω(y) ≤ ½ log(4/y) + π/4 − y/4 + y²/96 + 5y³/384` the total potential is
at least `−log 2 − ½ log((R² − x²)x²/(x + r)²) − O(r²) − (γ + log π)`, and
`(R − x) x² ≤ R²(R + x)/11` (the maximum sits at the golden point `x = R/φ`).

**Theorem** (`fullZeroForm_ge_of_odd_support_le`). Every odd `F ∈ C²_c` vanishing outside
`[−7/25, 7/25]` satisfies `Ẑ(F) ≥ (1/40) ∫ F²`. In the coordinates of the arithmetic criticality
theory this is `J_M(u) + V_μ(u) ≥ 0` for every even profile `u` with `M u` supported in
`[−7/25, 7/25]`, in every odd gauge `M`; the support reached is `2.67` times the Markov window
`21/200` and the jump density is never converted, so the plastic threshold plays no role.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Elementary hyperbolic and arctangent bounds -/

/-- `sinh z ≤ z cosh z` for `z ≥ 0` (`tanh z ≤ z`). -/
theorem sinh_le_mul_cosh {z : ℝ} (hz : 0 ≤ z) : Real.sinh z ≤ z * Real.cosh z := by
  have hmono : MonotoneOn (fun z => z * Real.cosh z - Real.sinh z) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun w hw => ?_
    rw [interior_Ici] at hw
    have hd : HasDerivAt (fun z => z * Real.cosh z - Real.sinh z) (w * Real.sinh w) w := by
      have h1 := ((hasDerivAt_id' w).mul (Real.hasDerivAt_cosh w)).sub (Real.hasDerivAt_sinh w)
      exact h1.congr_deriv (by ring)
    rw [hd.deriv]
    exact mul_nonneg (le_of_lt hw) (Real.sinh_nonneg_iff.mpr (le_of_lt hw))
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h
  linarith

/-- `z cosh z ≤ sinh z (1 + z²/3)` for `z ≥ 0` (`coth z ≤ 1/z + z/3`). -/
theorem mul_cosh_le_sinh_mul {z : ℝ} (hz : 0 ≤ z) :
    z * Real.cosh z ≤ Real.sinh z * (1 + z ^ 2 / 3) := by
  have hmono : MonotoneOn (fun z => Real.sinh z * (1 + z ^ 2 / 3) - z * Real.cosh z) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun w hw => ?_
    rw [interior_Ici] at hw
    have hd : HasDerivAt (fun z => Real.sinh z * (1 + z ^ 2 / 3) - z * Real.cosh z)
        (w / 3 * (w * Real.cosh w - Real.sinh w)) w := by
      have h2 : HasDerivAt (fun z : ℝ => 1 + z ^ 2 / 3) (2 * w / 3) w := by
        have := ((hasDerivAt_pow 2 w).div_const 3).const_add 1
        exact this.congr_deriv (by norm_num)
      have h1 := ((Real.hasDerivAt_sinh w).mul h2).sub
        ((hasDerivAt_id' w).mul (Real.hasDerivAt_cosh w))
      exact h1.congr_deriv (by ring)
    rw [hd.deriv]
    have hw' : 0 < w := hw
    exact mul_nonneg (by linarith) (by linarith [sinh_le_mul_cosh hw'.le])
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  norm_num at h
  linarith

private theorem arctan_le_self_of_nonneg' {w : ℝ} (hw : 0 ≤ w) : Real.arctan w ≤ w := by
  have h := integral_one_div_one_add_sq (a := 0) (b := w)
  rw [Real.arctan_zero, sub_zero] at h
  rw [← h]
  have hle : ∫ t in (0 : ℝ)..w, 1 / (1 + t ^ 2) ≤ ∫ _t in (0 : ℝ)..w, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on hw ?_ intervalIntegrable_const fun t _ => ?_
    · exact (continuous_const.div (continuous_const.add (continuous_pow 2))
        fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne').intervalIntegrable _ _
    · rw [div_le_one (by positivity)]; nlinarith [sq_nonneg t]
  simpa using hle

private theorem sub_cube_div_two_le_arctan' {w : ℝ} (hw : 0 ≤ w) : w - w ^ 3 / 2 ≤ Real.arctan w := by
  have hs : Real.sin (Real.arctan w) ≤ Real.arctan w := Real.sin_le (Real.arctan_nonneg.2 hw)
  rw [Real.sin_arctan] at hs
  have hsq : Real.sqrt (1 + w ^ 2) ≤ 1 + w ^ 2 / 2 :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith [sq_nonneg (w ^ 2)])
  have hpos : 0 < Real.sqrt (1 + w ^ 2) := by positivity
  have h1 : w / (1 + w ^ 2 / 2) ≤ w / Real.sqrt (1 + w ^ 2) :=
    div_le_div_of_nonneg_left hw hpos hsq
  have h2 : w - w ^ 3 / 2 ≤ w / (1 + w ^ 2 / 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hw 5]
  linarith

/-- `(1 + e^{−2z})/(1 − e^{−2z}) = cosh z / sinh z`. -/
theorem one_add_exp_div_one_sub_exp {z : ℝ} (hz : 0 < z) :
    (1 + Real.exp (-2 * z)) / (1 - Real.exp (-2 * z)) = Real.cosh z / Real.sinh z := by
  have hu : 0 < Real.exp (-z) := Real.exp_pos _
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e2 : Real.exp (-2 * z) = Real.exp (-z) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e1 : Real.exp z = (Real.exp (-z))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [Real.cosh_eq, Real.sinh_eq, e2, e1]
  have h3 : 0 < 1 - Real.exp (-z) ^ 2 := by nlinarith
  have h4 : (Real.exp (-z))⁻¹ - Real.exp (-z) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : Real.exp (-z) * (Real.exp (-z))⁻¹ = Real.exp (-z) * Real.exp (-z) := by rw [h]
    rw [mul_inv_cancel₀ hu.ne'] at this
    nlinarith
  field_simp

/-- `tanh z = (1 − e^{−2z})/(1 + e^{−2z})`. -/
theorem tanh_eq_exp {z : ℝ} :
    Real.tanh z = (1 - Real.exp (-2 * z)) / (1 + Real.exp (-2 * z)) := by
  have hu : 0 < Real.exp (-z) := Real.exp_pos _
  have e2 : Real.exp (-2 * z) = Real.exp (-z) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e1 : Real.exp z = (Real.exp (-z))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq, e2, e1]
  field_simp

/-- `arctan(e^{−2z}) + arctan(tanh z) = π/4` for `z ≥ 0`. -/
theorem arctan_exp_add_arctan_tanh {z : ℝ} (hz : 0 ≤ z) :
    Real.arctan (Real.exp (-2 * z)) + Real.arctan (Real.tanh z) = Real.pi / 4 := by
  set u := Real.exp (-2 * z) with hudef
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht : Real.tanh z = (1 - u) / (1 + u) := tanh_eq_exp
  have hprod : u * Real.tanh z < 1 := by
    rw [ht]
    rw [show u * ((1 - u) / (1 + u)) = (u - u ^ 2) / (1 + u) by field_simp]
    rw [div_lt_one (by linarith)]
    nlinarith
  rw [Real.arctan_add hprod, ht]
  have h1 : (u + (1 - u) / (1 + u)) / (1 - u * ((1 - u) / (1 + u))) = 1 := by
    have h2 : 1 - u * ((1 - u) / (1 + u)) ≠ 0 := by
      rw [show 1 - u * ((1 - u) / (1 + u)) = (1 + u ^ 2) / (1 + u) by field_simp; ring]
      positivity
    rw [div_eq_one_iff_eq h2]
    field_simp
    ring
  rw [h1, Real.arctan_one]

/-- **Lower bound for `Ω`.** `½ log(4/y) + π/4 − y/4 ≤ Ω(y)` for `y > 0`. -/
theorem archLevyAntideriv_ge {y : ℝ} (hy : 0 < y) :
    -(1 / 2) * Real.log (y / 4) + Real.pi / 4 - y / 4 ≤ archLevyAntideriv y := by
  set z := y / 4 with hzdef
  have hz : 0 < z := by positivity
  have hy2 : -y / 2 = -2 * z := by rw [hzdef]; ring
  rw [archLevyAntideriv_eq_log_div hy, hy2, one_add_exp_div_one_sub_exp hz]
  have hs : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hc : 0 < Real.cosh z := Real.cosh_pos z
  have hlog : -Real.log z ≤ Real.log (Real.cosh z / Real.sinh z) := by
    rw [← Real.log_inv]
    refine Real.log_le_log (by positivity) ?_
    rw [inv_eq_one_div, div_le_div_iff₀ hz hs]
    linarith [sinh_le_mul_cosh hz.le]
  have hat := arctan_exp_add_arctan_tanh hz.le
  have htanh : Real.tanh z ≤ z := by
    rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ hc]
    linarith [sinh_le_mul_cosh hz.le]
  have htanh0 : 0 ≤ Real.tanh z := by
    rw [Real.tanh_eq_sinh_div_cosh]; positivity
  have harc := arctan_le_self_of_nonneg' htanh0
  linarith

/-- **Upper bound for `Ω`.** `Ω(y) ≤ ½ log(4/y) + y²/96 + π/4 − y/4 + 5y³/384` for `y > 0`. -/
theorem archLevyAntideriv_le_expansion {y : ℝ} (hy : 0 < y) :
    archLevyAntideriv y ≤
      -(1 / 2) * Real.log (y / 4) + y ^ 2 / 96 + Real.pi / 4 - y / 4 + 5 / 384 * y ^ 3 := by
  set z := y / 4 with hzdef
  have hz : 0 < z := by positivity
  have hy2 : -y / 2 = -2 * z := by rw [hzdef]; ring
  rw [archLevyAntideriv_eq_log_div hy, hy2, one_add_exp_div_one_sub_exp hz]
  have hs : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hc : 0 < Real.cosh z := Real.cosh_pos z
  have h7 := mul_cosh_le_sinh_mul hz.le
  have hlog : Real.log (Real.cosh z / Real.sinh z) ≤ -Real.log z + z ^ 2 / 3 := by
    have h1 : Real.cosh z / Real.sinh z ≤ (1 + z ^ 2 / 3) / z := by
      rw [div_le_div_iff₀ hs hz]; linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) hz.ne'] at h2
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + z ^ 2 / 3 by positivity)
    linarith
  have hat := arctan_exp_add_arctan_tanh hz.le
  have htanh : Real.tanh z ≤ z := by
    rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ hc]
    linarith [sinh_le_mul_cosh hz.le]
  have htanh0 : 0 ≤ Real.tanh z := by
    rw [Real.tanh_eq_sinh_div_cosh]; positivity
  have htanh_low : z - z ^ 3 / 3 ≤ Real.tanh z := by
    rw [Real.tanh_eq_sinh_div_cosh, le_div_iff₀ hc]
    have hq : (z - z ^ 3 / 3) * (1 + z ^ 2 / 3) ≤ z := by nlinarith [pow_nonneg hz.le 5]
    nlinarith [hc]
  have harc := sub_cube_div_two_le_arctan' htanh0
  have hcube : Real.tanh z ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ htanh0 htanh 3
  have hz3 : z ^ 3 = y ^ 3 / 64 := by rw [hzdef]; ring
  have hz2 : z ^ 2 = y ^ 2 / 16 := by rw [hzdef]; ring
  nlinarith

/-! ### The exact window killing of a plateau gauge -/

/-- The edge function `E(u) = log(1 + e^{−u/2}) + ½ log(1 + e^{−u}) + arctan(e^{−u/2})`. -/
def windowEdgeFunction (u : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-u / 2)) + 1 / 2 * Real.log (1 + Real.exp (-u)) +
    Real.arctan (Real.exp (-u / 2))

theorem windowEdgeFunction_zero :
    windowEdgeFunction 0 = 3 / 2 * Real.log 2 + Real.pi / 4 := by
  unfold windowEdgeFunction
  norm_num [Real.arctan_one]
  ring

theorem continuous_windowEdgeFunction : Continuous windowEdgeFunction := by
  unfold windowEdgeFunction
  refine ((Continuous.log (by fun_prop) fun u => (by positivity : (0 : ℝ) < 1 + _).ne').add
    (continuous_const.mul (Continuous.log (by fun_prop) fun u =>
      (by positivity : (0 : ℝ) < 1 + _).ne'))).add ?_
  exact Real.continuous_arctan.comp (by fun_prop)

/-- On `(0, ∞)`, `E = Ω − N` with `N(u) = −½ log(1 − e^{−2u})`. -/
theorem windowEdgeFunction_eq {u : ℝ} (hu : 0 < u) :
    windowEdgeFunction u = archLevyAntideriv u + 1 / 2 * Real.log (1 - Real.exp (-2 * u)) := by
  set t := Real.exp (-u / 2) with htdef
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e2 : Real.exp (-u) = t ^ 2 := by rw [htdef, ← Real.exp_nat_mul]; ring_nf
  have e4 : Real.exp (-2 * u) = t ^ 4 := by rw [htdef, ← Real.exp_nat_mul]; ring_nf
  have hfac : 1 - t ^ 4 = (1 - t) * (1 + t) * (1 + t ^ 2) := by ring
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 + t := by linarith
  have h3 : 0 < 1 + t ^ 2 := by positivity
  unfold windowEdgeFunction archLevyAntideriv
  rw [← htdef, e2, e4, hfac, Real.log_mul (by positivity) h3.ne', Real.log_mul h1.ne' h2.ne']
  ring

/-- `|ν − ω| ≤ 3/4` on `(0, ∞)`. -/
theorem abs_archDiagonalDensity_sub_archLevyDensity_le {u : ℝ} (hu : 0 < u) :
    |archDiagonalDensity u - archLevyDensity u| ≤ 3 / 4 := by
  have h1 := archLevyDensity_sub_archDiagonalDensity_le hu
  have h2 := archDiagonalDensity_le hu
  rw [abs_le]; constructor <;> linarith

theorem measurable_archDiagonalDensity : Measurable archDiagonalDensity := by
  unfold archDiagonalDensity; fun_prop

/-- `∫_0^a (ν − ω) = E(a) − E(0)`. -/
theorem integral_archDiagonal_sub_archLevy {a : ℝ} (ha : 0 < a) :
    ∫ u in (0 : ℝ)..a, (archDiagonalDensity u - archLevyDensity u) =
      windowEdgeFunction a - windowEdgeFunction 0 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le
    continuous_windowEdgeFunction.continuousOn (fun u hu => ?_) ?_
  · have hu0 : 0 < u := hu.1
    have hΩ := hasDerivAt_archLevyAntideriv hu0
    have hN := hasDerivAt_half_log_one_sub_exp hu0
    have hsum := hΩ.add hN
    have hev : (fun v => archLevyAntideriv v + 1 / 2 * Real.log (1 - Real.exp (-2 * v))) =ᶠ[𝓝 u]
        windowEdgeFunction := by
      filter_upwards [Ioi_mem_nhds hu0] with v hv
      exact (windowEdgeFunction_eq hv).symm
    exact (hsum.congr_of_eventuallyEq hev.symm).congr_deriv (by ring)
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
    refine Measure.integrableOn_of_bounded (M := 3 / 4) (by simp)
      ((measurable_archDiagonalDensity.sub measurable_archLevyDensity).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs]; exact abs_archDiagonalDensity_sub_archLevyDensity_le hu.1)

/-- **The exact one-sided window killing.** `∫_0^∞ (ν − ω 1_{u ≤ a}) = Ω(a) − E(0)`. -/
theorem integral_one_sided_window_eq {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), (if u ≤ a then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) = archLevyAntideriv a - windowEdgeFunction 0 := by
  obtain ⟨hint, -⟩ := integral_one_sided_window_ge ha
  have hunion : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  rw [hunion] at hint ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right)]
  have e1 : (∫ u in Ioc 0 a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioc 0 a, (archDiagonalDensity u - archLevyDensity u) :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [if_pos hu.2]
  have e2 : (∫ u in Ioi a, (if u ≤ a then archDiagonalDensity u - archLevyDensity u
      else archDiagonalDensity u)) = ∫ u in Ioi a, archDiagonalDensity u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by rw [if_neg (not_le.mpr hu)]
  rw [e1, e2, ← intervalIntegral.integral_of_le ha.le, integral_archDiagonal_sub_archLevy ha,
    integral_Ioi_archDiagonalDensity ha, windowEdgeFunction_eq ha]
  ring

/-- **The exact potential of a plateau gauge.** At a plateau point,
`−𝒲M(x) ≥ Ω(R − x) + Ω(R + x) − 2E(0) − (γ + log π)`. -/
theorem neg_poleFreeWeilOperator_ge_antideriv {M : ℝ → ℝ} {K R : ℝ} (hMc : Continuous M)
    (hLip : ∀ a b, |M a - M b| ≤ K * |a - b|) (hle : ∀ y, M y ≤ 1)
    (hsupp : ∀ y, R ≤ |y| → M y = 0) {x : ℝ} (hR : 2 * R < Real.log 2) (hx : |x| < R)
    (hMx : M x = 1) :
    archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
        2 * archConstantReal ≤ -poleFreeWeilOperator M x := by
  have ha : 0 < R - x := by linarith [le_abs_self x]
  have hb : 0 < R + x := by linarith [neg_abs_le x]
  obtain ⟨hIa, -⟩ := integral_one_sided_window_ge ha
  obtain ⟨hIb, -⟩ := integral_one_sided_window_ge hb
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u
        else archDiagonalDensity u) +
      (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u) ≤
        profileArchTerm M x u := by
    intro u hu
    have hω := archLevyDensity_pos hu
    have h1 : M (x + u) ≤ if u ≤ R - x then 1 else 0 := by
      split_ifs with h
      · exact hle _
      · exact (hsupp _ (by rw [abs_of_pos (by linarith [le_abs_self x] : 0 < x + u)]; linarith)).le
    have h2 : M (x - u) ≤ if u ≤ R + x then 1 else 0 := by
      split_ifs with h
      · exact hle _
      · exact (hsupp _ (by rw [abs_of_neg (by linarith [neg_abs_le x] : x - u < 0)]; linarith)).le
    unfold profileArchTerm
    rw [hMx]
    have hm1 := mul_le_mul_of_nonneg_left h1 hω.le
    have hm2 := mul_le_mul_of_nonneg_left h2 hω.le
    split_ifs at hm1 hm2 ⊢ <;> nlinarith
  have hmono := setIntegral_mono_on (f := fun u =>
      (if u ≤ R - x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u) +
      (if u ≤ R + x then archDiagonalDensity u - archLevyDensity u else archDiagonalDensity u))
    (hIa.add hIb) (integrableOn_profileArchTerm hMc hLip x) measurableSet_Ioi hpt
  rw [integral_add hIa hIb, integral_one_sided_window_eq ha, integral_one_sided_window_eq hb] at hmono
  unfold poleFreeWeilOperator
  rw [profilePrimeSum_eq_zero hsupp hR hx, hMx]
  linarith

/-! ### Integrability on the positive quadrant -/

/-- A measurable function on the positive quadrant, bounded by `C` and vanishing outside the box
`(0, T₁] × (0, T₂]`, is integrable. -/
theorem integrable_quadrant_of_bound {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C T₁ T₂ : ℝ}
    (hb : ∀ t x, 0 < t → 0 < x → |f (t, x)| ≤ C)
    (hz : ∀ t x, 0 < t → 0 < x → (T₁ < t ∨ T₂ < x) → f (t, x) = 0) :
    Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict]
  have hbox : MeasurableSet (Ioc (0 : ℝ) T₁ ×ˢ Ioc (0 : ℝ) T₂) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hfin : ((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ Ioi 0)
      (Ioc (0 : ℝ) T₁ ×ˢ Ioc (0 : ℝ) T₂) < ⊤ := by
    refine lt_of_le_of_lt (Measure.restrict_apply_le _ _) ?_
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  have hg : Integrable ((Ioc (0 : ℝ) T₁ ×ˢ Ioc (0 : ℝ) T₂).indicator fun _ => C)
      (((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ Ioi 0)) :=
    (integrable_indicator_iff hbox).mpr (integrableOn_const hfin.ne)
  refine hg.mono' hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    (Eventually.of_forall fun p hp => ?_)
  obtain ⟨ht, hx⟩ := hp
  have ht0 : 0 < p.1 := ht
  have hx0 : 0 < p.2 := hx
  rw [Real.norm_eq_abs]
  by_cases hin : p ∈ Ioc (0 : ℝ) T₁ ×ˢ Ioc (0 : ℝ) T₂
  · rw [Set.indicator_of_mem hin]
    exact hb p.1 p.2 ht0 hx0
  · rw [Set.indicator_of_notMem hin]
    have hout : T₁ < p.1 ∨ T₂ < p.2 := by
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      exact hin ⟨⟨ht0, hcon.1⟩, ⟨hx0, hcon.2⟩⟩
    have := hz p.1 p.2 ht0 hx0 hout
    rw [show p = (p.1, p.2) from rfl, this, abs_zero]

/-! ### The archimedean fold of an odd test in an even gauge -/

/-- The reflected difference jump `P(x)P(t−x)(F(x) − F(t−x))²` of the crossing pair `(−x, t − x)`. -/
def crossingDiffJump (P F : ℝ → ℝ) (t x : ℝ) : ℝ := P x * P (t - x) * (F x - F (t - x)) ^ 2

theorem crossingDiffJump_comm (P F : ℝ → ℝ) (t x : ℝ) :
    crossingDiffJump P F t (t - x) = crossingDiffJump P F t x := by
  unfold crossingDiffJump
  rw [sub_sub_cancel]
  ring

theorem crossingDiffJump_add_two_mul (P F : ℝ → ℝ) (s x : ℝ) :
    crossingDiffJump P F (s + 2 * x) x = signedShiftJump P F s x := by
  unfold crossingDiffJump signedShiftJump
  rw [show s + 2 * x - x = x + s by ring]

section Fold

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc in
theorem continuous_signedShiftJump (t : ℝ) : Continuous fun x => signedShiftJump P F t x := by
  unfold signedShiftJump; fun_prop

include hPc hFc hPB in
theorem integrable_signedShiftJump (t : ℝ) : Integrable fun x => signedShiftJump P F t x := by
  refine (continuous_signedShiftJump hPc hFc t).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun x hx => ?_
  unfold signedShiftJump
  rw [hPB x (by
    by_contra h
    exact hx ⟨by linarith [neg_abs_le x, not_le.mp h], by linarith [le_abs_self x, not_le.mp h]⟩),
    zero_mul, zero_mul]

include hPe hFo in
theorem signedShiftJump_reflect (t x : ℝ) :
    signedShiftJump P F t (-x - t) = signedShiftJump P F t x := by
  unfold signedShiftJump
  rw [show -x - t + t = -x by ring, show -x - t = -(x + t) by ring, hPe, hPe, hFo, hFo]
  ring

include hPe hFo in
theorem signedShiftJump_neg (t a : ℝ) :
    signedShiftJump P F t (-a) = P a * P (t - a) * (F a + F (t - a)) ^ 2 := by
  unfold signedShiftJump
  rw [show -a + t = t - a by ring, hPe, hFo]
  ring

include hPc hFc hPe hFo hPB in
/-- **The per-shift split.** For odd `F` and even `P`, the jump profile at shift `t > 0` is twice
the same-side profile plus the crossing (reflected sum) profile. -/
theorem integral_signedShiftJump_eq_split {t : ℝ} (ht : 0 < t) :
    (∫ x, signedShiftJump P F t x) =
      2 * (∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        ∫ x in Ioo (0 : ℝ) t, P x * P (t - x) * (F x + F (t - x)) ^ 2 := by
  set g := fun x => signedShiftJump P F t x with hgdef
  have hg : Integrable g := integrable_signedShiftJump hPc hFc hPB t
  have h1 : (∫ x, g x) = (∫ x in Ioi (0 : ℝ), g x) + ∫ x in Iic (0 : ℝ), g x := by
    rw [← integral_add_compl measurableSet_Ioi hg, compl_Ioi]
  have h2 : (∫ x in Iic (0 : ℝ), g x) =
      (∫ x in Iic (-t), g x) + ∫ x in Ioc (-t) 0, g x := by
    rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hg.integrableOn
      hg.integrableOn, Iic_union_Ioc_eq_Iic (by linarith)]
  have h3 : (∫ x in Iic (-t), g x) = ∫ x in Ioi (0 : ℝ), g x := by
    have e3 := integral_comp_neg_Iic (-t) (fun y => g (y - t))
    simp only [neg_neg] at e3
    have e : (∫ x in Iic (-t), g x) = ∫ x in Iic (-t), g (-x - t) :=
      setIntegral_congr_fun measurableSet_Iic fun x _ => by
        simp only [hgdef]
        rw [signedShiftJump_reflect hPe hFo]
    rw [e, e3, setIntegral_Ioi_translate]
    simp only [add_sub_cancel_right]
  have h4 : (∫ x in Ioc (-t) 0, g x) =
      ∫ x in Ioo (0 : ℝ) t, P x * P (t - x) * (F x + F (t - x)) ^ 2 := by
    rw [← integral_indicator measurableSet_Ioc,
      ← integral_neg_eq_self (fun x => (Ioc (-t) 0).indicator g x)]
    have e : (fun x => (Ioc (-t) 0).indicator g (-x)) =
        (Ico (0 : ℝ) t).indicator fun x => P x * P (t - x) * (F x + F (t - x)) ^ 2 := by
      funext x
      by_cases hx : x ∈ Ico (0 : ℝ) t
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show -x ∈ Ioc (-t) 0 from
          ⟨by linarith [hx.2], by linarith [hx.1]⟩)]
        exact signedShiftJump_neg hPe hFo t x
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx
          ⟨by linarith [h.2], by linarith [h.1]⟩)]
    rw [e, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo]
  rw [h1, h2, h3, h4]
  ring

include hPc hFc in
/-- The crossing sum profile is the killing profile minus the reflected difference profile. -/
theorem integral_crossingSum_eq {t : ℝ} :
    (∫ x in Ioo (0 : ℝ) t, P x * P (t - x) * (F x + F (t - x)) ^ 2) =
      (∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) -
        ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := by
  have hc1 : Continuous fun x => P x * P (t - x) * F x ^ 2 := by fun_prop
  have hc2 : Continuous fun x => P x * P (t - x) * F (t - x) ^ 2 := by fun_prop
  have hc3 : Continuous fun x => crossingDiffJump P F t x := by unfold crossingDiffJump; fun_prop
  have i1 : IntegrableOn (fun x => P x * P (t - x) * F x ^ 2) (Ioo 0 t) :=
    hc1.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have i2 : IntegrableOn (fun x => P x * P (t - x) * F (t - x) ^ 2) (Ioo 0 t) :=
    hc2.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have i3 : IntegrableOn (fun x => crossingDiffJump P F t x) (Ioo 0 t) :=
    hc3.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hrefl : (∫ x in Ioo (0 : ℝ) t, P x * P (t - x) * F (t - x) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, P x * P (t - x) * F x ^ 2 := by
    have := setIntegral_Ioo_reflect_self (fun x => P (t - x) * P x * F x ^ 2) t
    simp only [sub_sub_cancel] at this
    rw [this]
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by ring
  have hpt : ∀ x, P x * P (t - x) * (F x + F (t - x)) ^ 2 =
      2 * (P x * P (t - x) * F x ^ 2) + 2 * (P x * P (t - x) * F (t - x) ^ 2) -
        crossingDiffJump P F t x := fun x => by unfold crossingDiffJump; ring
  have hA : IntegrableOn (fun x => 2 * (P x * P (t - x) * F x ^ 2) +
      2 * (P x * P (t - x) * F (t - x) ^ 2)) (Ioo 0 t) := (i1.const_mul 2).add (i2.const_mul 2)
  have hsub := integral_sub hA i3
  have hadd := integral_add (i1.const_mul 2) (i2.const_mul 2)
  simp_rw [hpt]
  rw [hsub, hadd, integral_const_mul, integral_const_mul, hrefl]
  have e4 : (∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) =
      4 * ∫ x in Ioo (0 : ℝ) t, P x * P (t - x) * F x ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by ring
  rw [e4]
  ring

include hPc hFc in
/-- **Midpoint folding of the crossing collar.** -/
theorem integral_crossingDiffJump_eq_two_mul_half {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) =
      2 * ∫ x in Ioo (0 : ℝ) (t / 2), crossingDiffJump P F t x := by
  have hc : Continuous fun x => crossingDiffJump P F t x := by unfold crossingDiffJump; fun_prop
  have hsplit : (∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) =
      (∫ x in Ioc (0 : ℝ) (t / 2), crossingDiffJump P F t x) +
        ∫ x in Ioo (t / 2) t, crossingDiffJump P F t x := by
    have hd : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioo (t / 2) t) :=
      Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
    rw [← setIntegral_union hd measurableSet_Ioo
      (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self),
      Ioc_union_Ioo_eq_Ioo (by linarith) (by linarith)]
  rw [hsplit, integral_Ioc_eq_integral_Ioo, setIntegral_Ioo_reflect_midpoint]
  simp_rw [crossingDiffJump_comm]
  ring

include hP0 in
theorem signedShiftJump_nonneg' (s x : ℝ) : 0 ≤ signedShiftJump P F s x := by
  unfold signedShiftJump
  exact mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (sq_nonneg _)

include hP0 in
theorem crossingDiffJump_nonneg (t x : ℝ) : 0 ≤ crossingDiffJump P F t x := by
  unfold crossingDiffJump
  exact mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (sq_nonneg _)

include hFL hFo in
theorem abs_le_mul_abs_of_odd (x : ℝ) : |F x| ≤ K * |x| := by
  have h0 : F 0 = 0 := by have := hFo 0; rw [neg_zero] at this; linarith
  have := hFL x 0
  rwa [h0, sub_zero, sub_zero] at this

include hP0 hP1 hFL in
theorem signedShiftJump_le (s x : ℝ) : signedShiftJump P F s x ≤ K ^ 2 * s ^ 2 := by
  unfold signedShiftJump
  have hsq : (F x - F (x + s)) ^ 2 ≤ K ^ 2 * s ^ 2 := by
    have h := hFL x (x + s)
    rw [show x - (x + s) = -s by ring, abs_neg] at h
    calc (F x - F (x + s)) ^ 2 = |F x - F (x + s)| ^ 2 := (sq_abs _).symm
      _ ≤ (K * |s|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = K ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
  calc P x * P (x + s) * (F x - F (x + s)) ^ 2 ≤ 1 * (K ^ 2 * s ^ 2) :=
        mul_le_mul (mul_le_one₀ (hP1 _) (hP0 _) (hP1 _)) hsq (sq_nonneg _) zero_le_one
    _ = _ := one_mul _

include hPB hB0 in
theorem signedShiftJump_eq_zero_of_pos {s x : ℝ} (hx : 0 < x) (h : 2 * B < s ∨ B < x) :
    signedShiftJump P F s x = 0 := by
  unfold signedShiftJump
  rcases h with h | h
  · rw [hPB (x + s) (by rw [abs_of_pos (by linarith)]; linarith), mul_zero, zero_mul]
  · rw [hPB x (by rw [abs_of_pos hx]; linarith), zero_mul, zero_mul]

include hPc hFc hP0 hP1 hFL hPB hB0 hB1 in
theorem integrable_archLevy_mul_signedShiftJump_prod :
    Integrable (Function.uncurry fun t x => archLevyDensity t * signedShiftJump P F t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : Measurable (Function.uncurry fun t x => archLevyDensity t * signedShiftJump P F t x) := by
    refine (measurable_archLevyDensity.comp measurable_fst).mul ?_
    have : Continuous (Function.uncurry fun t x => signedShiftJump P F t x) := by
      unfold signedShiftJump; fun_prop
    exact this.measurable
  refine integrable_quadrant_of_bound hmeas (C := 3 / 2 * K ^ 2) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · simp only [Function.uncurry_apply_pair]
    by_cases hts : t ≤ 2 * B
    · have hω := archLevyDensity_le_of_le_one ht (by linarith)
      have hJ := signedShiftJump_le hP0 hP1 hFL t x
      have hJ0 := signedShiftJump_nonneg' hP0 (F := F) t x
      rw [abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht).le hJ0)]
      calc archLevyDensity t * signedShiftJump P F t x ≤ 3 / 2 / t * (K ^ 2 * t ^ 2) :=
            mul_le_mul hω hJ hJ0 (by positivity)
        _ = 3 / 2 * K ^ 2 * t := by field_simp
        _ ≤ 3 / 2 * K ^ 2 * 1 := by
            have : 0 ≤ 3 / 2 * K ^ 2 := by positivity
            nlinarith
        _ = _ := mul_one _
    · rw [signedShiftJump_eq_zero_of_pos hPB hB0 hx (Or.inl (not_le.mp hts)), mul_zero, abs_zero]
      positivity
  · simp only [Function.uncurry_apply_pair]
    rw [signedShiftJump_eq_zero_of_pos hPB hB0 hx h, mul_zero]

/-- The folded crossing integrand `ω(t) 1_{0<x<t/2} D_t(x)` on `(0,∞)²`. -/
def foldedCrossingIntegrand (P F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  archLevyDensity p.1 *
    ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2}.indicator (fun q => crossingDiffJump P F q.1 q.2) p)

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
theorem foldedCrossingIntegrand_apply (t x : ℝ) :
    foldedCrossingIntegrand P F (t, x) = archLevyDensity t *
      (Ioo (0 : ℝ) (t / 2)).indicator (fun y => crossingDiffJump P F t y) x := by
  unfold foldedCrossingIntegrand
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ioo]

include hPc hFc hP0 hP1 hFL hPB hB0 hB1 in
theorem integrable_foldedCrossingIntegrand :
    Integrable (foldedCrossingIntegrand P F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.div_const 2))
  have hc : Continuous fun q : ℝ × ℝ => crossingDiffJump P F q.1 q.2 := by
    unfold crossingDiffJump; fun_prop
  have hmeas : Measurable (foldedCrossingIntegrand P F) :=
    (measurable_archLevyDensity.comp measurable_fst).mul (hc.measurable.indicator hset)
  refine integrable_quadrant_of_bound hmeas (C := 3 / 2 * K ^ 2) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · rw [foldedCrossingIntegrand_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) (t / 2)
    · rw [Set.indicator_of_mem hxt]
      have hD0 := crossingDiffJump_nonneg hP0 (F := F) t x
      by_cases hts : t ≤ 2 * B
      · have hω := archLevyDensity_le_of_le_one ht (by linarith)
        have hD : crossingDiffJump P F t x ≤ K ^ 2 * t ^ 2 := by
          unfold crossingDiffJump
          have h := hFL x (t - x)
          have habs : |x - (t - x)| ≤ t := by
            rw [abs_le]; constructor <;> linarith [hxt.1, hxt.2]
          have hK : 0 ≤ K := le_trans (abs_nonneg _) (by
            have := hFL 1 0; have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
            rw [h1, mul_one] at this; exact this)
          have h2 : |F x - F (t - x)| ≤ K * t := h.trans (mul_le_mul_of_nonneg_left habs hK)
          have hsq : (F x - F (t - x)) ^ 2 ≤ K ^ 2 * t ^ 2 := by
            calc (F x - F (t - x)) ^ 2 = |F x - F (t - x)| ^ 2 := (sq_abs _).symm
              _ ≤ (K * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
              _ = K ^ 2 * t ^ 2 := by ring
          calc P x * P (t - x) * (F x - F (t - x)) ^ 2 ≤ 1 * (K ^ 2 * t ^ 2) :=
                mul_le_mul (mul_le_one₀ (hP1 _) (hP0 _) (hP1 _)) hsq (sq_nonneg _) zero_le_one
            _ = _ := one_mul _
        rw [abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht).le hD0)]
        calc archLevyDensity t * crossingDiffJump P F t x ≤ 3 / 2 / t * (K ^ 2 * t ^ 2) :=
              mul_le_mul hω hD hD0 (by positivity)
          _ = 3 / 2 * K ^ 2 * t := by field_simp
          _ ≤ 3 / 2 * K ^ 2 * 1 := by
              have : 0 ≤ 3 / 2 * K ^ 2 := by positivity
              nlinarith
          _ = _ := mul_one _
      · have hP : P (t - x) = 0 := hPB _ (by
          rw [abs_of_pos (by linarith [hxt.2])]; linarith [hxt.2, not_le.mp hts])
        unfold crossingDiffJump
        rw [hP, mul_zero, zero_mul, mul_zero, abs_zero]
        positivity
    · rw [Set.indicator_of_notMem hxt, mul_zero, abs_zero]
      positivity
  · rw [foldedCrossingIntegrand_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) (t / 2)
    · rw [Set.indicator_of_mem hxt]
      unfold crossingDiffJump
      rcases h with h | h
      · rw [hPB (t - x) (by rw [abs_of_pos (by linarith [hxt.2])]; linarith [hxt.2]),
          mul_zero, zero_mul, mul_zero]
      · rw [hPB x (by rw [abs_of_pos hx]; linarith), zero_mul, zero_mul, mul_zero]
    · rw [Set.indicator_of_notMem hxt, mul_zero]

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- The folded crossing integrand at fixed `x > 0`, as a shift integral. -/
theorem integral_foldedCrossingIntegrand_eq {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x)) =
      ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) * signedShiftJump P F s x := by
  have h1 : (∫ t in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x)) =
      ∫ t in Ioi (2 * x), archLevyDensity t * crossingDiffJump P F t x := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    simp only [Set.indicator_apply, mem_Ioi, foldedCrossingIntegrand_apply, mem_Ioo]
    by_cases h : 2 * x < t
    · rw [if_pos (by linarith), if_pos ⟨hx, by linarith⟩, if_pos h]
    · rw [if_neg h]
      by_cases h' : 0 < t
      · rw [if_pos h', if_neg (fun hh => h (by linarith [hh.2])), mul_zero]
      · rw [if_neg h']
  rw [h1, setIntegral_Ioi_translate]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [crossingDiffJump_add_two_mul]

include hPc hFc hP0 hP1 hFL hPB hB0 hB1 in
/-- `D_arch = 2 ∫_{x>0} ∫_{s>0} ω(s + 2x) J_s(x) ds dx`. -/
theorem archCrossingDiffEnergy_eq :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
        signedShiftJump P F s x := by
  have hID := integrable_foldedCrossingIntegrand hPc hFc hP0 hP1 hPB hFL hB0 hB1
  have h1 : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
      signedShiftJump P F s x) =
      ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      (integral_foldedCrossingIntegrand_eq (mem_Ioi.mp hx)).symm
  rw [h1, ← integral_integral_swap (f := fun t x => foldedCrossingIntegrand P F (t, x)) hID,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [integral_crossingDiffJump_eq_two_mul_half hPc hFc (mem_Ioi.mp ht)]
  have : (∫ x in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x)) =
      archLevyDensity t * ∫ x in Ioo (0 : ℝ) (t / 2), crossingDiffJump P F t x := by
    simp_rw [foldedCrossingIntegrand_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [this]
  ring

include hPc hFc hP0 hP1 hFL hPB hB0 hB1 in
/-- `S_arch = ∫_{x>0} ∫_{s>0} ω(s) J_s(x) ds dx`. -/
theorem archSameEnergy_eq :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity s * signedShiftJump P F s x := by
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  rw [← integral_integral_swap (f := fun t x => archLevyDensity t * signedShiftJump P F t x) hIS]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [integral_const_mul]

include hPc hFc hP0 hP1 hFL hPB hB0 hB1 in
/-- **The archimedean Z-type law in an even gauge.** `D_arch ≤ 2 S_arch`. -/
theorem archCrossingDiff_le_two_mul_archSame :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) ≤
      2 * ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x := by
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  rw [archCrossingDiffEnergy_eq hPc hFc hP0 hP1 hPB hFL hB0 hB1,
    archSameEnergy_eq hPc hFc hP0 hP1 hPB hFL hB0 hB1]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  have hsec := hIS.prod_left_ae
  have hout := hIS.integral_prod_right
  refine integral_mono_of_nonneg ?_ hout ?_
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    exact setIntegral_nonneg measurableSet_Ioi fun s hs => mul_nonneg
      (archLevyDensity_pos (by linarith [mem_Ioi.mp hs, mem_Ioi.mp hx])).le
      (signedShiftJump_nonneg' hP0 s x)
  · filter_upwards [hsec, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    have hx0' : 0 < x := hx0
    refine integral_mono_of_nonneg ?_ hx ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => mul_nonneg
        (archLevyDensity_pos (by linarith [mem_Ioi.mp hs])).le (signedShiftJump_nonneg' hP0 s x)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := hs
      show archLevyDensity (s + 2 * x) * signedShiftJump P F s x ≤
        archLevyDensity s * signedShiftJump P F s x
      exact mul_le_mul_of_nonneg_right
        (strictAntiOn_archLevyDensity.antitoneOn hs0 (show (0 : ℝ) < s + 2 * x by linarith)
          (by linarith))
        (signedShiftJump_nonneg' hP0 s x)

/-- The killing integrand `ω(t) 4F(x)² 1_{x < t ≤ x + r}` on `(0,∞)²`. -/
def killingIntegrand (F : ℝ → ℝ) (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  archLevyDensity p.1 * ({q : ℝ × ℝ | q.2 < q.1 ∧ q.1 ≤ q.2 + r}.indicator
    (fun q => 4 * F q.2 ^ 2) p)

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
theorem killingIntegrand_apply (r t x : ℝ) :
    killingIntegrand F r (t, x) = archLevyDensity t * (Ioc x (x + r)).indicator
      (fun _ => 4 * F x ^ 2) t := by
  unfold killingIntegrand
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ioc]

include hFc hFo hFB hFL hB1 in
theorem integrable_killingIntegrand {r : ℝ} (hrB : r ≤ B) :
    Integrable (killingIntegrand F r)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : MeasurableSet {q : ℝ × ℝ | q.2 < q.1 ∧ q.1 ≤ q.2 + r} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_snd measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_snd.add_const r))
  have hmeas : Measurable (killingIntegrand F r) :=
    (measurable_archLevyDensity.comp measurable_fst).mul
      ((by fun_prop : Continuous fun q : ℝ × ℝ => 4 * F q.2 ^ 2).measurable.indicator hset)
  refine integrable_quadrant_of_bound hmeas (C := 6 * K ^ 2) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · rw [killingIntegrand_apply]
    by_cases hin : t ∈ Ioc x (x + r)
    · rw [Set.indicator_of_mem hin]
      by_cases hxB : B ≤ x
      · rw [hFB x (by rw [abs_of_pos hx]; exact hxB)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, abs_zero]
        positivity
      · have hts : t ≤ 1 := by linarith [hin.2, not_le.mp hxB]
        have hω := archLevyDensity_le_of_le_one ht hts
        have hF := abs_le_mul_abs_of_odd hFo hFL x
        have hF2 : 4 * F x ^ 2 ≤ 4 * K ^ 2 * t ^ 2 := by
          have h1 : F x ^ 2 ≤ (K * |x|) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hF 2
          have h2 : (K * |x|) ^ 2 ≤ K ^ 2 * t ^ 2 := by
            rw [mul_pow, sq_abs]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le (le_of_lt hin.1) 2)
              (sq_nonneg K)
          linarith
        have h0 : 0 ≤ 4 * F x ^ 2 := by positivity
        rw [abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht).le h0)]
        calc archLevyDensity t * (4 * F x ^ 2) ≤ 3 / 2 / t * (4 * K ^ 2 * t ^ 2) :=
              mul_le_mul hω hF2 h0 (by positivity)
          _ = 6 * K ^ 2 * t := by field_simp; ring
          _ ≤ 6 * K ^ 2 * 1 := by
              have : 0 ≤ 6 * K ^ 2 := by positivity
              nlinarith
          _ = _ := mul_one _
    · rw [Set.indicator_of_notMem hin, mul_zero, abs_zero]
      positivity
  · rw [killingIntegrand_apply]
    by_cases hin : t ∈ Ioc x (x + r)
    · rw [Set.indicator_of_mem hin]
      have hxB : B ≤ x := by
        rcases h with h | h
        · linarith [hin.2]
        · exact h.le
      rw [hFB x (by rw [abs_of_pos hx]; exact hxB)]
      simp
    · rw [Set.indicator_of_notMem hin, mul_zero]

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- The killing integrand at fixed `x > 0` integrates to `4F(x)²(Ω(x) − Ω(x + r))`. -/
theorem integral_killingIntegrand_eq {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), killingIntegrand F r (t, x)) =
      4 * F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) := by
  simp_rw [killingIntegrand_apply]
  have e : (fun t => archLevyDensity t * (Ioc x (x + r)).indicator (fun _ => 4 * F x ^ 2) t) =
      (Ioc x (x + r)).indicator fun t => 4 * F x ^ 2 * archLevyDensity t := by
    funext t
    by_cases h : t ∈ Ioc x (x + r)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [e, setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (fun t ht => mem_Ioi.mpr (lt_trans hx ht.1)), integral_const_mul,
    ← intervalIntegral.integral_of_le (by linarith), integral_archLevyDensity_Icc hx (by linarith)]

include hFc hFo hFB hFL hB1 in
/-- The folded killing density `F(x)²(Ω(x) − Ω(x + r))` is integrable on `(0, ∞)`. -/
theorem integrableOn_sq_mul_antideriv_sub {r : ℝ} (hr0 : 0 < r) (hrB : r ≤ B) :
    IntegrableOn (fun x => F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) (Ioi 0) := by
  have hKI := integrable_killingIntegrand hFc hFo hFB hFL hB1 hrB
  have h : IntegrableOn (fun x => 1 / 4 * ∫ t in Ioi (0 : ℝ), killingIntegrand F r (t, x)) (Ioi 0) :=
    (hKI.integral_prod_right).const_mul (1 / 4)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only
  rw [integral_killingIntegrand_eq hr0 (mem_Ioi.mp hx)]
  ring

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The archimedean fold of an odd test in an even plateau gauge.**
`J_P(F) ≥ 4 ∫_{x>0} F(x)² (Ω(x) − Ω(x + r))` when `P = 1` on `[−r, r] ⊇ supp F`. -/
theorem fourKilling_le_archJump {r : ℝ} (hr0 : 0 < r) (hrB : r ≤ B)
    (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r) (hPcs : HasCompactSupport P) :
    4 * ∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t := by
  -- the four profiles and their integrability
  have hI : IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile P F t) (Ioi 0) :=
    integrableOn_archLevy_mul_gaugeJumpProfile hP1 hP0 hPB hB0.le (by linarith) hFc hPc hPcs hFL
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  have hS : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x)
      (Ioi 0) :=
    hIS.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [Function.uncurry_apply_pair]
      rw [integral_const_mul])
  have hID := integrable_foldedCrossingIntegrand hPc hFc hP0 hP1 hPB hFL hB0 hB1
  have hD : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x)
      (Ioi 0) := by
    have h2 : IntegrableOn (fun t => 2 * ∫ x in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x))
        (Ioi 0) := hID.integral_prod_left.const_mul 2
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only
    simp_rw [foldedCrossingIntegrand_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self, integral_crossingDiffJump_eq_two_mul_half hPc hFc ht0]
    ring
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t =
      2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        archLevyDensity t * (∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) -
        archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := fun t ht => by
    unfold gaugeJumpProfile
    rw [integral_signedShiftJump_eq_split hPc hFc hPe hFo hPB ht, integral_crossingSum_eq hPc hFc]
    ring
  have hK : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
      4 * P x * P (t - x) * F x ^ 2) (Ioi 0) := by
    refine ((hI.sub (hS.const_mul 2)).add hD).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hsplit t ht]
    ring
  have hJ : (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) =
      2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
          4 * P x * P (t - x) * F x ^ 2) -
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := by
    have hA : IntegrableOn (fun t => 2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ),
        signedShiftJump P F t x) + archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
          4 * P x * P (t - x) * F x ^ 2) (Ioi 0) := (hS.const_mul 2).add hK
    have hS2 : IntegrableOn (fun t => 2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ),
        signedShiftJump P F t x)) (Ioi 0) := hS.const_mul 2
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hA hD,
      integral_add hS2 hK, integral_const_mul]
  have hZ := archCrossingDiff_le_two_mul_archSame hPc hFc hP0 hP1 hPB hFL hB0 hB1
  -- the killing profile dominates the folded killing integrand
  have hKI := integrable_killingIntegrand hFc hFo hFB hFL hB1 hrB
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (∫ x in Ioi (0 : ℝ), killingIntegrand F r (t, x)) ≤
      archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2 := by
    intro t ht
    have ht0 : 0 < t := ht
    have hω := (archLevyDensity_pos ht0).le
    have e1 : (fun x => killingIntegrand F r (t, x)) =
        fun x => archLevyDensity t * (Ico (t - r) t).indicator (fun x => 4 * F x ^ 2) x := by
      funext x
      rw [killingIntegrand_apply]
      congr 1
      by_cases h : t ∈ Ioc x (x + r)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ Ico (t - r) t from
          ⟨by linarith [h.2], h.1⟩)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hh => h
          ⟨hh.2, by linarith [hh.1]⟩)]
    have e2 : (archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) =
        ∫ x in Ioi (0 : ℝ), archLevyDensity t *
          (Ioo (0 : ℝ) t).indicator (fun x => 4 * P x * P (t - x) * F x ^ 2) x := by
      rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
    rw [e1, e2]
    have hc1 : Continuous fun x => 4 * F x ^ 2 := by fun_prop
    have hc2 : Continuous fun x => 4 * P x * P (t - x) * F x ^ 2 := by fun_prop
    have i1 : Integrable fun x => archLevyDensity t * (Ico (t - r) t).indicator
        (fun x => 4 * F x ^ 2) x :=
      ((hc1.integrableOn_Icc.mono_set Ico_subset_Icc_self).integrable_indicator
        measurableSet_Ico).const_mul _
    have i2 : Integrable fun x => archLevyDensity t * (Ioo (0 : ℝ) t).indicator
        (fun x => 4 * P x * P (t - x) * F x ^ 2) x :=
      ((hc2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator
        measurableSet_Ioo).const_mul _
    refine setIntegral_mono_on i1.integrableOn i2.integrableOn measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    refine mul_le_mul_of_nonneg_left ?_ hω
    by_cases h : x ∈ Ico (t - r) t
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) t from ⟨hx0, h.2⟩)]
      by_cases hF0 : F x = 0
      · rw [hF0]; simp
      · rw [hPr x (hFr x hF0), hPr (t - x) (by
          rw [abs_of_pos (by linarith [h.2])]; linarith [h.1])]
        ring_nf; exact le_rfl
    · rw [Set.indicator_of_notMem h]
      exact Set.indicator_nonneg (fun y _ => by
        have := hP0 y; have := hP0 (t - y); positivity) x
  have hK2 : (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), killingIntegrand F r (t, x)) ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2 :=
    setIntegral_mono_on hKI.integral_prod_left hK measurableSet_Ioi hpt
  have hswap : (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), killingIntegrand F r (t, x)) =
      4 * ∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) := by
    rw [integral_integral_swap (f := fun t x => killingIntegrand F r (t, x)) hKI,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [integral_killingIntegrand_eq hr0 (mem_Ioi.mp hx)]
    ring
  linarith

end Fold

/-! ### Evenness and the odd pole moment -/

/-- The pole-free Weil operator of an even gauge is even. -/
theorem poleFreeWeilOperator_neg {M : ℝ → ℝ} (hMe : ∀ y, M (-y) = M y) (x : ℝ) :
    poleFreeWeilOperator M (-x) = poleFreeWeilOperator M x := by
  unfold poleFreeWeilOperator profilePrimeSum
  have h1 : ∀ n : ℕ, M (-x + Real.log n) + M (-x - Real.log n) =
      M (x + Real.log n) + M (x - Real.log n) := fun n => by
    rw [show -x + Real.log n = -(x - Real.log n) by ring,
      show -x - Real.log n = -(x + Real.log n) by ring, hMe, hMe]
    ring
  have h2 : ∀ u, profileArchTerm M (-x) u = profileArchTerm M x u := fun u => by
    unfold profileArchTerm
    rw [show -x + u = -(x - u) by ring, show -x - u = -(x + u) by ring, hMe, hMe, hMe]
    ring
  simp_rw [h1, h2, hMe]

/-- `∫ h = 2 ∫_{x>0} h` for an even integrable `h`. -/
theorem integral_eq_two_mul_Ioi_of_even {h : ℝ → ℝ} (hh : Integrable h)
    (he : ∀ x, h (-x) = h x) : ∫ x, h x = 2 * ∫ x in Ioi (0 : ℝ), h x := by
  rw [← integral_add_compl measurableSet_Ioi hh, compl_Ioi]
  have e := integral_comp_neg_Iic (0 : ℝ) h
  simp only [neg_zero] at e
  have : (∫ x in Iic (0 : ℝ), h x) = ∫ x in Ioi (0 : ℝ), h x := by
    rw [← e]
    exact setIntegral_congr_fun measurableSet_Iic fun x _ => (he x).symm
  rw [this]
  ring

/-- **The odd pole moment on a window, sharp form.** If `F` vanishes off the set where a continuous
compactly supported `0 ≤ M ≤ 1` equals `1`, and `M = 0` outside `(−R, R)`, then
`S(F)² ≤ (R³/6) cosh²(R/2) ∫ F²`. -/
theorem sq_oddPoleMoment_le_cosh {F M : ℝ → ℝ} {R : ℝ} (hR0 : 0 ≤ R) (hF : Continuous F)
    (hFc : HasCompactSupport F) (hMc : Continuous M) (hMcs : HasCompactSupport M)
    (hnn : ∀ y, 0 ≤ M y) (hle : ∀ y, M y ≤ 1) (hsupp : ∀ y, R ≤ |y| → M y = 0)
    (hFM : ∀ x, F x ≠ 0 → M x = 1) :
    oddPoleMoment F ^ 2 ≤ R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 * ∫ x, F x ^ 2 := by
  set c := Real.cosh (R / 2) ^ 2 with hcdef
  have hGc : Continuous fun x => M x * Real.sinh (x / 2) :=
    hMc.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hS : oddPoleMoment F = ∫ x, F x * (M x * Real.sinh (x / 2)) := by
    unfold oddPoleMoment
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases h : F x = 0
    · simp only [h, zero_mul]
    · simp only [hFM x h, one_mul]
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hGcs : HasCompactSupport fun x => M x * Real.sinh (x / 2) := hMcs.mul_right
  have hG2 : Integrable fun x => (M x * Real.sinh (x / 2)) ^ 2 :=
    (hGc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hGcs)
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le hF.aestronglyMeasurable
    hGc.aestronglyMeasurable hF2 hG2
  have hpt : ∀ x, (M x * Real.sinh (x / 2)) ^ 2 ≤
      Set.indicator (Icc (-R) R) (fun x => c / 4 * x ^ 2) x := by
    intro x
    by_cases hx : |x| < R
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨(abs_le.mp hx.le).1, (abs_le.mp hx.le).2⟩)]
      have h1 : |Real.sinh (x / 2)| ≤ |x| / 2 * Real.cosh (R / 2) := by
        rw [Real.abs_sinh, abs_div, abs_two]
        have h2 := sinh_le_mul_cosh (show 0 ≤ |x| / 2 by positivity)
        have h3 : Real.cosh (|x| / 2) ≤ Real.cosh (R / 2) := by
          rw [Real.cosh_le_cosh, abs_of_nonneg (show (0 : ℝ) ≤ |x| / 2 by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ R / 2 by linarith)]
          linarith
        calc Real.sinh (|x| / 2) ≤ |x| / 2 * Real.cosh (|x| / 2) := h2
          _ ≤ |x| / 2 * Real.cosh (R / 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      have h4 : |M x * Real.sinh (x / 2)| ≤ |x| / 2 * Real.cosh (R / 2) := by
        rw [abs_mul, abs_of_nonneg (hnn x)]
        calc M x * |Real.sinh (x / 2)| ≤ 1 * (|x| / 2 * Real.cosh (R / 2)) :=
              mul_le_mul (hle x) h1 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      calc (M x * Real.sinh (x / 2)) ^ 2 = |M x * Real.sinh (x / 2)| ^ 2 := (sq_abs _).symm
        _ ≤ (|x| / 2 * Real.cosh (R / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
        _ = c / 4 * x ^ 2 := by rw [hcdef, mul_pow, div_pow, sq_abs]; ring
    · rw [hsupp x (not_lt.mp hx), zero_mul, zero_pow two_ne_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) x
  have hint : (∫ x, Set.indicator (Icc (-R) R) (fun x => c / 4 * x ^ 2) x) = c / 4 * (2 * R ^ 3 / 3) := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
      integral_pow]
    ring
  have hGb : ∫ x, (M x * Real.sinh (x / 2)) ^ 2 ≤ c / 4 * (2 * R ^ 3 / 3) := by
    rw [← hint]
    exact integral_mono hG2 ((integrable_indicator_iff measurableSet_Icc).mpr
      ((continuous_const.mul (continuous_pow 2)).integrableOn_Icc)) hpt
  rw [hS]
  calc (∫ x, F x * (M x * Real.sinh (x / 2))) ^ 2 ≤
      (∫ x, F x ^ 2) * ∫ x, (M x * Real.sinh (x / 2)) ^ 2 := hCS
    _ ≤ (∫ x, F x ^ 2) * (c / 4 * (2 * R ^ 3 / 3)) :=
        mul_le_mul_of_nonneg_left hGb (integral_nonneg fun x => sq_nonneg _)
    _ = _ := by ring

/-! ### The numerical potential on `[0, 7/25]` -/

private theorem log_pi_le_one_point_one_four_four_eight : Real.log Real.pi ≤ 11448 / 10000 := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have he := Real.exp_one_gt_d9
  have hT := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1448 / 10000 by norm_num) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hsplit : Real.exp (11448 / 10000) = Real.exp 1 * Real.exp (1448 / 10000) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.pi_lt_d6, Real.exp_pos 1, Real.exp_pos (1448 / 10000)]

/-- `exp(3.5318) ≤ 34.3`. -/
private theorem exp_three_point_five_three_one_eight_le : Real.exp (35318 / 10000) ≤ 343 / 10 := by
  have he := Real.exp_one_lt_d9
  have hT := Real.exp_bound' (show (0 : ℝ) ≤ 5318 / 10000 by norm_num)
    (show (5318 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 6 by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hsplit : Real.exp (35318 / 10000) = Real.exp 1 ^ 3 * Real.exp (5318 / 10000) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [hsplit]
  have h1 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
  have h2 := Real.exp_pos (5318 / 10000)
  have h3 : Real.exp 1 ^ 3 * Real.exp (5318 / 10000) ≤ 2.7182818286 ^ 3 * Real.exp (5318 / 10000) :=
    mul_le_mul_of_nonneg_right h1 h2.le
  nlinarith

/-- The golden-point cubic: `(R − x)(R + x)x²/(x + r)² ≤ R⁴/(11 r²)` on `[0, r]`,
`R = 561/2000`, `r = 7/25`. -/
theorem goldenCubic_le {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 7 / 25) :
    (561 / 2000 - x) * (561 / 2000 + x) * x ^ 2 / (x + 7 / 25) ^ 2 ≤
      (561 / 2000) ^ 4 / (11 * (7 / 25) ^ 2) := by
  have h1 : 11 * (561 / 2000 - x) * x ^ 2 ≤ (561 / 2000) ^ 2 * (561 / 2000 + x) := by
    have hk : 0 ≤ x + 59 / 250 * (561 / 2000) := by linarith
    nlinarith [mul_nonneg (sq_nonneg (x - 309 / 500 * (561 / 2000))) hk, hx0]
  have h2 : 7 / 25 * (561 / 2000 + x) ≤ 561 / 2000 * (x + 7 / 25) := by linarith
  have hpos : 0 < x + 7 / 25 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h3 : (0 : ℝ) ≤ (7 / 25) ^ 2 * (561 / 2000 + x) := by positivity
  have h4 : 11 * (561 / 2000 - x) * x ^ 2 * ((7 / 25) ^ 2 * (561 / 2000 + x)) ≤
      (561 / 2000) ^ 2 * (561 / 2000 + x) * ((7 / 25) ^ 2 * (561 / 2000 + x)) :=
    mul_le_mul_of_nonneg_right h1 h3
  have h5 : (7 / 25 * (561 / 2000 + x)) ^ 2 ≤ (561 / 2000 * (x + 7 / 25)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [h4, h5]

/-- **The folded odd-plateau potential on `(0, 7/25]`.** -/
theorem oddPlateau_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 7 / 25) :
    1 / 40 + 751 / 100000 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + 7 / 25)) +
      (archLevyAntideriv (561 / 2000 - x) + archLevyAntideriv (561 / 2000 + x) -
        2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have ha := archLevyAntideriv_ge (y := 561 / 2000 - x) (by linarith)
  have hb := archLevyAntideriv_ge (y := 561 / 2000 + x) (by linarith)
  have hx := archLevyAntideriv_ge hx0
  have hc := archLevyAntideriv_le_expansion (y := x + 7 / 25) (by linarith)
  have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ := log_pi_le_one_point_one_four_four_eight
  -- the logarithms combine into `log(4A)`, `A` the golden cubic
  set A := (561 / 2000 - x) * (561 / 2000 + x) * x ^ 2 / (x + 7 / 25) ^ 2 with hAdef
  have hp1 : 0 < 561 / 2000 - x := by linarith
  have hp2 : 0 < 561 / 2000 + x := by linarith
  have hp3 : 0 < x + 7 / 25 := by linarith
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hlogA : Real.log ((561 / 2000 - x) / 4) + Real.log ((561 / 2000 + x) / 4) +
      2 * Real.log (x / 4) - 2 * Real.log ((x + 7 / 25) / 4) + 6 * Real.log 2 =
        Real.log (4 * A) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [hAdef, Real.log_div hp1.ne' (by norm_num), Real.log_div hp2.ne' (by norm_num),
      Real.log_div hx0.ne' (by norm_num), Real.log_div hp3.ne' (by norm_num),
      Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hp1.ne' hp2.ne', Real.log_pow,
      Real.log_pow, h4]
    push_cast
    ring
  have hA := goldenCubic_le hx0 hxr
  rw [← hAdef] at hA
  have hlog4A : Real.log (4 * A) ≤ -(35318 / 10000) := by
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_neg]
    have he := exp_three_point_five_three_one_eight_le
    have hepos := Real.exp_pos (35318 / 10000)
    rw [le_inv_comm₀ (by positivity) hepos]
    calc Real.exp (35318 / 10000) ≤ 343 / 10 := he
      _ ≤ (4 * ((561 / 2000) ^ 4 / (11 * (7 / 25) ^ 2)))⁻¹ := by norm_num
      _ ≤ (4 * A)⁻¹ := by
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          linarith
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  have hx2 : (x + 7 / 25) ^ 2 ≤ (14 / 25) ^ 2 := pow_le_pow_left₀ hp3.le (by linarith) 2
  have hx3 : (x + 7 / 25) ^ 3 ≤ (14 / 25) ^ 3 := pow_le_pow_left₀ hp3.le (by linarith) 3
  nlinarith [hlogA, hlog4A, hx2, hx3, Real.pi_pos]

/-! ### Odd-sector positivity on `[−7/25, 7/25]` -/

/-- **Weil positivity of every odd test supported in `[−7/25, 7/25]`.** Every odd `F ∈ C²_c`
vanishing outside `[−7/25, 7/25]` satisfies `Ẑ(F) ≥ (1/40) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 7 / 25 < |x| → F x = 0) :
    1 / 40 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 7 / 25 with hrdef
  set R : ℝ := 561 / 2000 with hRdef
  set δ : ℝ := R - r with hδdef
  have hδ : 0 < δ := by rw [hδdef, hRdef, hrdef]; norm_num
  set P := plateauGauge R δ with hPdef
  have hPd : ContDiff ℝ 2 P := contDiff_plateauGauge R δ
  have hPcs : HasCompactSupport P := hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := plateauGauge_nonneg R δ
  have hP1 : ∀ y, P y ≤ 1 := plateauGauge_le_one R δ
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hPr : ∀ y, |y| ≤ r → P y = 1 := fun y hy =>
    plateauGauge_eq_one hδ (by rw [hδdef]; linarith)
  have hPe : ∀ y, P (-y) = P y := fun y => by
    simp only [hPdef, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  have hFr : ∀ x, F x ≠ 0 → |x| ≤ r := fun x hx => by
    by_contra h
    exact hx (hsupp x (not_le.mp h))
  have hFM : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => hPr x (hFr x hx)
  have hFB : ∀ x, R ≤ |x| → F x = 0 := fun x hx => hsupp x (by
    simp only [hrdef, hRdef] at hx ⊢; linarith)
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hPL : ∀ a b, |P a - P b| ≤ KM * |a - b| := fun a b => hKM b a
  have hR0 : 0 < R := by rw [hRdef]; norm_num
  have hR1 : 2 * R ≤ 1 := by rw [hRdef]; norm_num
  have hlog2 : 2 * R < Real.log 2 := by
    have := Real.log_two_gt_d9; rw [hRdef]; linarith
  -- representation, fold, potential
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_of_window (F := F) hPB hlog2
  have hfold := fourKilling_le_archJump hPd.continuous hF.continuous hPe hodd hP0 hP1 hPB hFB hFL
    hR0 hR1 (r := r) (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs
  have hZ : fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2 := by
    unfold fullZeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous hPL hdec8).neg
  set G : ℝ → ℝ := fun x => F x ^ 2 * P x * -poleFreeWeilOperator P x with hGdef
  have hGi : Integrable G :=
    (((hF.continuous.pow 2).mul hPd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  have hGe : ∀ x, G (-x) = G x := fun x => by
    simp only [hGdef, hodd, hPe, poleFreeWeilOperator_neg hPe, neg_sq]
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hF2e : ∀ x, (fun x => F x ^ 2) (-x) = F x ^ 2 := fun x => by simp only [hodd, neg_sq]
  have hGint := integral_eq_two_mul_Ioi_of_even hGi hGe
  have hF2int := integral_eq_two_mul_Ioi_of_even hF2 hF2e
  have hHi := integrableOn_sq_mul_antideriv_sub hF.continuous hodd hFB hFL hR1
    (r := r) (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num)
  -- pointwise potential on the half line
  set c₀ : ℝ := 1 / 40 + 751 / 100000 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) + G x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · simp [hGdef, h]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_ge_antideriv hPd.continuous hPL hP1 hPB hlog2 hxR
        (hFM x h)
      have hV := oddPlateau_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hGdef, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      rw [hRdef, hrdef] at *
      nlinarith [mul_le_mul_of_nonneg_left hW' hF0, mul_le_mul_of_nonneg_left hV hF0]
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + G x) (Ioi 0) := (hHi.const_mul 2).add hGi.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2 hGi.integrableOn, integral_const_mul, integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 10199 / 10000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 984 / 100000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (984 / 100000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (984 / 100000) ≤ 100989 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 984 / 100000 by norm_num)
        (show (984 / 100000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 100989 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 751 / 100000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3 : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 751 / 200000 := by
      have : R ^ 3 / 6 = (561 / 2000) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      nlinarith [hcosh]
    nlinarith [mul_le_mul_of_nonneg_right hR3 hI0]
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [hc₀] at hmono
  rw [hZ, hQ, hJ]
  linarith [hfold, hmono, hGint, hF2int, hpole]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
