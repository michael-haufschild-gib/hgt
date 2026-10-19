import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateEnergyComparison

/-!
# The pole-free variation inequality

Let `μ_a = m_a(x) sinh(x/2) dx` on `(0, ∞)`, a positive measure of mass `sinh(a/2)/2`. The source
of the two-sided representation, `4 sinh(a/2) ∫ u² dμ_a`, splits as

    4 sinh(a/2) ∫ u² dμ_a = 8 (∫ u dμ_a)² + 4 sinh(a/2) ∫ (u − ū)² dμ_a,   ū = 2 ∫ u dμ_a / sinh(a/2),

the first term being the pole term `2 (∫ m_a u e^{−x/2})²` of the explicit formula for the odd test
`m_a u`, the second the **profile variance** `V_a(u)`. Subtracting from `u` its mean `ū` times a
wide plateau `u_L` gives a test `m_a (u − ū u_L)` whose source is at most `V_a(u)`, whose
same-side and reflected energies differ from those of `u` by terms controlled through Young's
inequality by the energies of the plateau, which are `O(e^{−8L})`. Letting `L → ∞`, the Riemann
Hypothesis gives the **pole-free variation inequality**

    D(ω_a, u) ≤ 2 S(ω_a, u) + V_a(u),

sharper than `D ≤ 2S + 4 sinh(a/2) ∫ u² dμ_a` by the pole term, and invariant under `u ↦ u + c`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The profile variance -/

/-- The half-line moment `∫_{x>0} u m_a sinh(x/2)`. -/
def profileMoment (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)

/-- The profile variance `4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) − 8 (∫_{x>0} u m_a sinh(x/2))²`. -/
def profileVariance (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  4 * Real.sinh (a / 2) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
    8 * profileMoment a u ^ 2

theorem integrableOn_mul_shiftDifference_mul_sinh {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (a : ℝ) :
    IntegrableOn (fun x => u x * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) := by
  have hc : Continuous fun x => u x * shiftDifference a x * Real.sinh (x / 2) :=
    (hu.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hcs : HasCompactSupport fun x => u x * shiftDifference a x * Real.sinh (x / 2) :=
    (huc.mul_right (f' := shiftDifference a)).mul_right (f' := fun x => Real.sinh (x / 2))
  exact (hc.integrable_of_hasCompactSupport hcs).integrableOn

theorem integrableOn_sq_mul_shiftDifference_mul_sinh {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (a : ℝ) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) := by
  have hg : Continuous fun x => shiftDifference a x * Real.sinh (x / 2) :=
    (continuous_shiftDifference a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  refine (integrableOn_continuous_mul_sq hg hu huc (Ioi 0)).congr_fun (fun x _ => ?_)
    measurableSet_Ioi
  show shiftDifference a x * Real.sinh (x / 2) * u x ^ 2 = _
  ring

/-- The profile variance is `4 sinh(a/2)` times the variance of `u` against `μ_a`. -/
theorem profileVariance_eq {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    profileVariance a u = 4 * Real.sinh (a / 2) *
      ∫ x in Ioi (0 : ℝ), (u x - 2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 *
        shiftDifference a x * Real.sinh (x / 2) := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  set m := profileMoment a u with hm
  set c := 2 * m / Real.sinh (a / 2) with hc
  have h1 := integrableOn_sq_mul_shiftDifference_mul_sinh hu huc a
  have h2 := integrableOn_mul_shiftDifference_mul_sinh hu huc a
  have h3 := (integrable_shiftDifference_mul_sinh_half a).integrableOn (s := Ioi 0)
  have e : ∀ x, (u x - c) ^ 2 * shiftDifference a x * Real.sinh (x / 2) =
      u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
        2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)) +
        c ^ 2 * (shiftDifference a x * Real.sinh (x / 2)) := fun x => by ring
  have h2c : IntegrableOn (fun x => 2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)))
    (Ioi 0) := h2.const_mul _
  have h12 : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
    2 * c * (u x * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := h1.sub h2c
  have h3c : IntegrableOn (fun x => c ^ 2 * (shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) :=
    h3.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi fun x _ => e x, integral_add h12 h3c,
    integral_sub h1 h2c, integral_const_mul, integral_const_mul,
    integral_Ioi_shiftDifference_mul_sinh_half]
  unfold profileVariance
  rw [← hm]
  show 4 * Real.sinh (a / 2) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
      8 * m ^ 2 = 4 * Real.sinh (a / 2) *
      ((∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) - 2 * c * m +
        c ^ 2 * (Real.sinh (a / 2) / 2))
  rw [hc]
  field_simp
  ring

theorem profileVariance_nonneg {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) : 0 ≤ profileVariance a u := by
  rw [profileVariance_eq ha hu huc]
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hx
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (shiftDifference_nonneg_of_nonneg ha.le hx0.le))
    (Real.sinh_nonneg_iff.mpr (by positivity))

/-- The profile variance is at most the source of the two-sided representation. -/
theorem profileVariance_le_source (a : ℝ) (u : ℝ → ℝ) :
    profileVariance a u ≤
      4 * Real.sinh (a / 2) * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  unfold profileVariance
  nlinarith [sq_nonneg (profileMoment a u)]

/-! ### The source of the corrected profile -/

/-- For `L` beyond the support of `u`, the source of `u − ū u_L` is at most the profile variance. -/
theorem source_sub_plateau_le_profileVariance {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {R L : ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hRL : R ≤ L) :
    4 * Real.sinh (a / 2) *
      (∫ x in Ioi (0 : ℝ), (u x - 2 * profileMoment a u / Real.sinh (a / 2) * smoothPlateau L x) ^ 2 *
        shiftDifference a x * Real.sinh (x / 2)) ≤ profileVariance a u := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  set m := profileMoment a u with hm
  set c := 2 * m / Real.sinh (a / 2) with hc
  have h1 := integrableOn_sq_mul_shiftDifference_mul_sinh hu huc a
  have h2 := integrableOn_mul_shiftDifference_mul_sinh hu huc a
  have h3 := (integrable_shiftDifference_mul_sinh_half a).integrableOn (s := Ioi 0)
  have hpl := integrableOn_sq_mul_shiftDifference_mul_sinh (contDiff_smoothPlateau L).continuous
    (hasCompactSupport_smoothPlateau L) a
  -- `u · u_L = u` on the support of `u`
  have huL : ∀ x, u x * smoothPlateau L x = u x := by
    intro x
    by_cases hx : R < |x|
    · rw [hsupp x hx, zero_mul]
    · rw [not_lt] at hx
      rw [smoothPlateau_eq_one (hx.trans hRL), mul_one]
  have e : ∀ x, (u x - c * smoothPlateau L x) ^ 2 * shiftDifference a x * Real.sinh (x / 2) =
      u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
        2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)) +
        c ^ 2 * (smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) := fun x => by
    have := huL x
    linear_combination (-(2 * c) * shiftDifference a x * Real.sinh (x / 2)) * this
  have h2c : IntegrableOn (fun x => 2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)))
    (Ioi 0) := h2.const_mul _
  have h12 : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) -
    2 * c * (u x * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := h1.sub h2c
  have hplc : IntegrableOn (fun x => c ^ 2 *
    (smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := hpl.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi fun x _ => e x, integral_add h12 hplc,
    integral_sub h1 h2c, integral_const_mul, integral_const_mul]
  have hplle : (∫ x in Ioi (0 : ℝ), smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) ≤
      Real.sinh (a / 2) / 2 := by
    rw [← integral_Ioi_shiftDifference_mul_sinh_half a]
    refine setIntegral_mono_on hpl h3 measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have hms : 0 ≤ shiftDifference a x * Real.sinh (x / 2) :=
      mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0.le)
        (Real.sinh_nonneg_iff.mpr (by positivity))
    have hp1 : smoothPlateau L x ^ 2 ≤ 1 :=
      pow_le_one₀ (smoothPlateau_nonneg L x) (smoothPlateau_le_one L x)
    calc smoothPlateau L x ^ 2 * shiftDifference a x * Real.sinh (x / 2)
        = smoothPlateau L x ^ 2 * (shiftDifference a x * Real.sinh (x / 2)) := by ring
      _ ≤ 1 * (shiftDifference a x * Real.sinh (x / 2)) := mul_le_mul_of_nonneg_right hp1 hms
      _ = _ := one_mul _
  unfold profileVariance
  rw [← hm]
  have hc2 : 0 ≤ 4 * Real.sinh (a / 2) * c ^ 2 := by positivity
  have key : 4 * Real.sinh (a / 2) * (2 * c * m) - 4 * Real.sinh (a / 2) * (c ^ 2 * (Real.sinh (a / 2) / 2)) =
      8 * m ^ 2 := by
    rw [hc]
    field_simp
    ring
  nlinarith [mul_le_mul_of_nonneg_left hplle hc2, key]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
