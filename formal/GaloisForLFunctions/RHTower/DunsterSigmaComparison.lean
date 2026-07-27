import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import GaloisForLFunctions.RHTower.RadialPSWFExteriorPhase

/-!
# The turning parameter deforms the radial Liouville data by an exact multiplicative factor

The exterior radial prolate speed `S(σ, z) = √((z² − σ²)/(z² − 1))` is usually compared with its
free model `S(0, z) = z/√(z² − 1)` by expanding in `σ`.  That comparison degenerates as `z → 1`,
where both speeds blow up, and it forces a separate boundary-layer treatment near the turning
point.

No expansion is needed.  The two speeds differ by the **exact multiplicative factor**

`S(σ, z) = S(0, z) · √(1 − σ²/z²)`,

whose value lies in `[√(1 − σ²), 1]` for every `z > 1` — with no loss at either end of the ray,
because `σ²/z²` is *smaller* than `σ²` exactly where the speeds are large.  Integrating the
inequality gives the same two-sided multiplicative comparison for the phases,

`√(1 − σ²) · (√(z²−1) − √(a²−1)) ≤ ξ_σ(z) − ξ_σ(a) ≤ √(z²−1) − √(a²−1)`,

and feeding that into the Liouville–Green amplitude

`A_σ(x)⁴ = ξ_σ(x)² / ((x² − 1)(x² − σ²))`,     `A_0(x)⁴ = x⁻²`,

gives

`1 − σ² ≤ (A_σ(x)/A_0(x))⁴ ≤ 1/(1 − σ²)`

for every `x > 1`.  The amplitude comparison is uniform up to the turning point because `σ`
deforms the numerator `ξ_σ²` and the denominator factor `x² − σ²` in the *same* direction, so the
two deformations cancel and no boundary layer appears.

Everything here is exact: identities and two-sided bounds, no asymptotics.
-/

open Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## The exact multiplicative comparison of speeds -/

/-- **The turning parameter acts multiplicatively on the exterior speed.**  This is an identity,
not an approximation, and it holds for every real `σ`. -/
theorem radialPSWFExteriorSpeed_eq_free_mul (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    radialPSWFExteriorSpeed sigma z
      = radialPSWFExteriorSpeed 0 z * Real.sqrt (1 - sigma ^ 2 / z ^ 2) := by
  have hz0 : (0 : ℝ) < z := zero_lt_one.trans hz
  have hden : (0 : ℝ) < z ^ 2 - 1 := by nlinarith
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have harg : (0 : ℝ) ≤ z ^ 2 / (z ^ 2 - 1) := div_nonneg hz2.le hden.le
  have hfree : radialPSWFExteriorSpeed 0 z = Real.sqrt (z ^ 2 / (z ^ 2 - 1)) := by
    simp [radialPSWFExteriorSpeed]
  rw [radialPSWFExteriorSpeed, hfree, ← Real.sqrt_mul harg]
  congr 1
  field_simp

/-- The free exterior speed in closed form. -/
theorem radialPSWFExteriorSpeed_zero_eq {z : ℝ} (hz : 1 < z) :
    radialPSWFExteriorSpeed 0 z = z / Real.sqrt (z ^ 2 - 1) := by
  have hz0 : (0 : ℝ) < z := zero_lt_one.trans hz
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  rw [radialPSWFExteriorSpeed, show ((0 : ℝ)) ^ 2 = 0 by norm_num, sub_zero,
    Real.sqrt_div hz2, Real.sqrt_sq hz0.le]

theorem radialPSWFExteriorSpeed_zero_nonneg (z : ℝ) : 0 ≤ radialPSWFExteriorSpeed 0 z :=
  Real.sqrt_nonneg _

/-- The comparison factor is squeezed between `√(1 − σ²)` and `1`, uniformly on the exterior ray.
The lower bound is where the turning point would normally be lost: `σ²/z² ≤ σ²` precisely because
`z ≥ 1`. -/
theorem radialPSWFComparisonFactor_mem_Icc (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    Real.sqrt (1 - sigma ^ 2) ≤ Real.sqrt (1 - sigma ^ 2 / z ^ 2)
      ∧ Real.sqrt (1 - sigma ^ 2 / z ^ 2) ≤ 1 := by
  have hz2 : (1 : ℝ) < z ^ 2 := by nlinarith
  have hz2pos : (0 : ℝ) < z ^ 2 := by linarith
  have hsigma0 : (0 : ℝ) ≤ sigma ^ 2 := sq_nonneg sigma
  have hle : sigma ^ 2 / z ^ 2 ≤ sigma ^ 2 := by
    rw [div_le_iff₀ hz2pos]
    nlinarith
  have hnn : (0 : ℝ) ≤ sigma ^ 2 / z ^ 2 := div_nonneg hsigma0 hz2pos.le
  refine ⟨Real.sqrt_le_sqrt (by linarith), ?_⟩
  have hone : Real.sqrt (1 - sigma ^ 2 / z ^ 2) ≤ Real.sqrt 1 :=
    Real.sqrt_le_sqrt (by linarith)
  simpa using hone

/-- **Exact two-sided comparison of speeds.**  The perturbed exterior speed is trapped between a
fixed multiple of the free speed and the free speed itself, with a ratio independent of `z`. -/
theorem radialPSWFExteriorSpeed_two_sided (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    Real.sqrt (1 - sigma ^ 2) * radialPSWFExteriorSpeed 0 z ≤ radialPSWFExteriorSpeed sigma z
      ∧ radialPSWFExteriorSpeed sigma z ≤ radialPSWFExteriorSpeed 0 z := by
  obtain ⟨hlow, hhigh⟩ := radialPSWFComparisonFactor_mem_Icc sigma hz
  have hfree := radialPSWFExteriorSpeed_zero_nonneg z
  rw [radialPSWFExteriorSpeed_eq_free_mul sigma hz]
  constructor
  · rw [mul_comm (Real.sqrt (1 - sigma ^ 2))]
    exact mul_le_mul_of_nonneg_left hlow hfree
  · calc
      radialPSWFExteriorSpeed 0 z * Real.sqrt (1 - sigma ^ 2 / z ^ 2)
          ≤ radialPSWFExteriorSpeed 0 z * 1 := mul_le_mul_of_nonneg_left hhigh hfree
      _ = radialPSWFExteriorSpeed 0 z := mul_one _

/-! ## Transfer to the phase -/

theorem continuousOn_radialPSWFExteriorSpeed_Icc (sigma : ℝ) {a z : ℝ} (ha : 1 < a) :
    ContinuousOn (radialPSWFExteriorSpeed sigma) (Icc a z) := fun _ hx =>
  (continuousAt_radialPSWFExteriorSpeed sigma (ha.trans_le hx.1)).continuousWithinAt

theorem intervalIntegrable_radialPSWFExteriorSpeed
    (sigma : ℝ) {a z : ℝ} (ha : 1 < a) (haz : a ≤ z) :
    IntervalIntegrable (radialPSWFExteriorSpeed sigma) volume a z := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le haz]
  exact continuousOn_radialPSWFExteriorSpeed_Icc sigma ha

/-- The phase increment is the integral of the speed. -/
theorem radialPSWFExteriorPhase_sub_eq_integral
    (sigma : ℝ) {a z : ℝ} (ha : 1 < a) (hz : 1 < z) :
    radialPSWFExteriorPhase sigma z - radialPSWFExteriorPhase sigma a
      = ∫ u in a..z, radialPSWFExteriorSpeed sigma u :=
  intervalIntegral.integral_interval_sub_left
    (continuousOn_radialPSWFExteriorSpeed_uIcc sigma hz).intervalIntegrable
    (continuousOn_radialPSWFExteriorSpeed_uIcc sigma ha).intervalIntegrable

/-- The free phase profile `ρ(x) = √(x² − 1)` has the free exterior speed as its derivative. -/
theorem hasDerivAt_radialPSWFFreeProfile {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1)) (radialPSWFExteriorSpeed 0 x) x := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hpos : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hne : x ^ 2 - 1 ≠ 0 := ne_of_gt hpos
  have hbase : HasDerivAt (fun u : ℝ => u ^ 2 - 1) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).sub_const 1)
  have hd := hbase.sqrt hne
  have hsq : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  convert hd using 1
  rw [radialPSWFExteriorSpeed_zero_eq hx]
  field_simp

/-- **The free phase increment in closed form:** `ξ₀(z) − ξ₀(a) = √(z²−1) − √(a²−1)`. -/
theorem radialPSWFExteriorPhase_zero_sub_eq {a z : ℝ} (ha : 1 < a) (haz : a ≤ z) :
    radialPSWFExteriorPhase 0 z - radialPSWFExteriorPhase 0 a
      = Real.sqrt (z ^ 2 - 1) - Real.sqrt (a ^ 2 - 1) := by
  have hz : 1 < z := ha.trans_le haz
  rw [radialPSWFExteriorPhase_sub_eq_integral 0 ha hz]
  have hderiv : ∀ x ∈ uIcc a z,
      HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1)) (radialPSWFExteriorSpeed 0 x) x := by
    intro x hx
    rw [uIcc_of_le haz] at hx
    exact hasDerivAt_radialPSWFFreeProfile (ha.trans_le hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_radialPSWFExteriorSpeed 0 ha haz)]

/-- **Exact two-sided comparison of phase increments.**  Uniform in `a` and `z`: the ratio of the
perturbed increment to the free increment lies in `[√(1 − σ²), 1]` no matter how close `a` is to
the turning point. -/
theorem radialPSWFExteriorPhase_sub_two_sided
    (sigma : ℝ) {a z : ℝ} (ha : 1 < a) (haz : a ≤ z) :
    Real.sqrt (1 - sigma ^ 2) * (Real.sqrt (z ^ 2 - 1) - Real.sqrt (a ^ 2 - 1))
        ≤ radialPSWFExteriorPhase sigma z - radialPSWFExteriorPhase sigma a
      ∧ radialPSWFExteriorPhase sigma z - radialPSWFExteriorPhase sigma a
        ≤ Real.sqrt (z ^ 2 - 1) - Real.sqrt (a ^ 2 - 1) := by
  have hz : 1 < z := ha.trans_le haz
  have hfreeInt : ∫ u in a..z, radialPSWFExteriorSpeed 0 u
      = Real.sqrt (z ^ 2 - 1) - Real.sqrt (a ^ 2 - 1) := by
    rw [← radialPSWFExteriorPhase_sub_eq_integral 0 ha hz]
    exact radialPSWFExteriorPhase_zero_sub_eq ha haz
  have hintS : IntervalIntegrable (radialPSWFExteriorSpeed sigma) volume a z :=
    intervalIntegrable_radialPSWFExteriorSpeed sigma ha haz
  have hint0 : IntervalIntegrable (radialPSWFExteriorSpeed 0) volume a z :=
    intervalIntegrable_radialPSWFExteriorSpeed 0 ha haz
  rw [radialPSWFExteriorPhase_sub_eq_integral sigma ha hz]
  constructor
  · have hmono : ∫ u in a..z, Real.sqrt (1 - sigma ^ 2) * radialPSWFExteriorSpeed 0 u
        ≤ ∫ u in a..z, radialPSWFExteriorSpeed sigma u := by
      refine intervalIntegral.integral_mono_on haz (hint0.const_mul _) hintS ?_
      intro x hx
      exact (radialPSWFExteriorSpeed_two_sided sigma (ha.trans_le hx.1)).1
    rwa [intervalIntegral.integral_const_mul, hfreeInt] at hmono
  · have hmono : ∫ u in a..z, radialPSWFExteriorSpeed sigma u
        ≤ ∫ u in a..z, radialPSWFExteriorSpeed 0 u := by
      refine intervalIntegral.integral_mono_on haz hintS hint0 ?_
      intro x hx
      exact (radialPSWFExteriorSpeed_two_sided sigma (ha.trans_le hx.1)).2
    rwa [hfreeInt] at hmono

/-! ## The phase anchored at the turning point

The corpus phase is normalized at `z = 2`; the Liouville–Green amplitude needs the phase measured
from the turning point `z = 1`, where the speed is singular and the naive integral is improper.

The substitution `t = √(u² − 1)` removes the singularity exactly.  Since

`√((u² − σ²)/(u² − 1)) = (u/√(u² − 1)) · √(1 − σ²/u²)`  and  `dt = (u/√(u² − 1)) du`,

the anchored phase is the integral of the **bounded** density `√(1 − σ²/(1 + t²))` over `[0, ρ(z)]`
with `ρ(z) = √(z² − 1)`.  The whole turning-point singularity is the free one, carried by the change
of variable; the turning parameter survives only as a density with values in `[√(1 − σ²), 1]`.
-/

/-- The radial Liouville phase anchored at the turning point, written in arclength coordinates.
Nonsingular by construction. -/
def radialPSWFTurningPhase (sigma z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.sqrt (z ^ 2 - 1), Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2))

theorem continuous_radialPSWFTurningDensity (sigma : ℝ) :
    Continuous fun t : ℝ => Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2)) := by
  have hden : Continuous fun t : ℝ => (1 : ℝ) + t ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  have hne : ∀ t : ℝ, (1 : ℝ) + t ^ 2 ≠ 0 := fun t => by positivity
  exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_const.div hden hne))

/-- The arclength density is squeezed between `√(1 − σ²)` and `1` at every point. -/
theorem radialPSWFTurningDensity_mem_Icc (sigma t : ℝ) :
    Real.sqrt (1 - sigma ^ 2) ≤ Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2))
      ∧ Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2)) ≤ 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hone : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hsig : (0 : ℝ) ≤ sigma ^ 2 := sq_nonneg sigma
  have hle : sigma ^ 2 / (1 + t ^ 2) ≤ sigma ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have hnn : (0 : ℝ) ≤ sigma ^ 2 / (1 + t ^ 2) := div_nonneg hsig hpos.le
  refine ⟨Real.sqrt_le_sqrt (by linarith), ?_⟩
  have hub : Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2)) ≤ Real.sqrt 1 :=
    Real.sqrt_le_sqrt (by linarith)
  simpa using hub

theorem radialPSWFTurningPhase_zero (z : ℝ) :
    radialPSWFTurningPhase 0 z = Real.sqrt (z ^ 2 - 1) := by
  simp [radialPSWFTurningPhase]

/-- **The anchored phase obeys the exact two-sided multiplicative comparison**, on the whole closed
ray including the turning point itself. -/
theorem radialPSWFTurningPhase_mem_Icc (sigma z : ℝ) :
    Real.sqrt (1 - sigma ^ 2) * Real.sqrt (z ^ 2 - 1) ≤ radialPSWFTurningPhase sigma z
      ∧ radialPSWFTurningPhase sigma z ≤ Real.sqrt (z ^ 2 - 1) := by
  have hL : (0 : ℝ) ≤ Real.sqrt (z ^ 2 - 1) := Real.sqrt_nonneg _
  have hcont : IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2)))
      volume 0 (Real.sqrt (z ^ 2 - 1)) :=
    (continuous_radialPSWFTurningDensity sigma).intervalIntegrable _ _
  constructor
  · have hm := intervalIntegral.integral_mono_on hL
      (intervalIntegrable_const (c := Real.sqrt (1 - sigma ^ 2))) hcont
      (fun t _ => (radialPSWFTurningDensity_mem_Icc sigma t).1)
    simpa [radialPSWFTurningPhase, mul_comm] using hm
  · have hm := intervalIntegral.integral_mono_on hL hcont
      (intervalIntegrable_const (c := (1 : ℝ)))
      (fun t _ => (radialPSWFTurningDensity_mem_Icc sigma t).2)
    simpa [radialPSWFTurningPhase] using hm

/-- **The anchored phase differs from the corpus exterior phase by an additive constant.**  Proved
by the exact change of variable `t = √(u² − 1)`, which is regular on every `[a, z] ⊂ (1, ∞)`. -/
theorem radialPSWFTurningPhase_sub_eq (sigma : ℝ) {a z : ℝ} (ha : 1 < a) (haz : a ≤ z) :
    radialPSWFTurningPhase sigma z - radialPSWFTurningPhase sigma a
      = radialPSWFExteriorPhase sigma z - radialPSWFExteriorPhase sigma a := by
  have hz : 1 < z := ha.trans_le haz
  rw [radialPSWFExteriorPhase_sub_eq_integral sigma ha hz]
  have hderiv : ∀ u ∈ uIcc a z,
      HasDerivAt (fun v : ℝ => Real.sqrt (v ^ 2 - 1)) (radialPSWFExteriorSpeed 0 u) u := by
    intro u hu
    rw [uIcc_of_le haz] at hu
    exact hasDerivAt_radialPSWFFreeProfile (ha.trans_le hu.1)
  have hcont' : ContinuousOn (radialPSWFExteriorSpeed 0) (uIcc a z) := by
    rw [uIcc_of_le haz]
    exact continuousOn_radialPSWFExteriorSpeed_Icc 0 ha
  have hsub := intervalIntegral.integral_comp_mul_deriv hderiv hcont'
    (continuous_radialPSWFTurningDensity sigma)
  have hsplit : radialPSWFTurningPhase sigma z - radialPSWFTurningPhase sigma a
      = ∫ t in Real.sqrt (a ^ 2 - 1)..Real.sqrt (z ^ 2 - 1),
          Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2)) :=
    intervalIntegral.integral_interval_sub_left
      ((continuous_radialPSWFTurningDensity sigma).intervalIntegrable _ _)
      ((continuous_radialPSWFTurningDensity sigma).intervalIntegrable _ _)
  rw [hsplit, ← hsub]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  rw [uIcc_of_le haz] at hu
  have hu1 : 1 < u := ha.trans_le hu.1
  have hpos : (0 : ℝ) ≤ u ^ 2 - 1 := by nlinarith
  simp only [Function.comp_apply]
  rw [Real.sq_sqrt hpos, show (1 : ℝ) + (u ^ 2 - 1) = u ^ 2 by ring, mul_comm,
    ← radialPSWFExteriorSpeed_eq_free_mul sigma hu1]

/-- The squared anchored phase, in the form the Liouville–Green amplitude consumes. -/
theorem radialPSWFTurningPhase_sq_mem_Icc {sigma : ℝ} (hsigma : sigma ^ 2 ≤ 1) {z : ℝ}
    (hz : 1 ≤ z) :
    (1 - sigma ^ 2) * (z ^ 2 - 1) ≤ radialPSWFTurningPhase sigma z ^ 2
      ∧ radialPSWFTurningPhase sigma z ^ 2 ≤ z ^ 2 - 1 := by
  have hz1 : (0 : ℝ) ≤ z ^ 2 - 1 := by nlinarith
  have he : (0 : ℝ) ≤ 1 - sigma ^ 2 := by linarith
  obtain ⟨hlow, hhigh⟩ := radialPSWFTurningPhase_mem_Icc sigma z
  have hnn : (0 : ℝ) ≤ Real.sqrt (1 - sigma ^ 2) * Real.sqrt (z ^ 2 - 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hphase : (0 : ℝ) ≤ radialPSWFTurningPhase sigma z := hnn.trans hlow
  constructor
  · have hsq : (Real.sqrt (1 - sigma ^ 2) * Real.sqrt (z ^ 2 - 1)) ^ 2
        = (1 - sigma ^ 2) * (z ^ 2 - 1) := by
      rw [mul_pow, Real.sq_sqrt he, Real.sq_sqrt hz1]
    rw [← hsq]
    exact pow_le_pow_left₀ hnn hlow 2
  · have hsq : (Real.sqrt (z ^ 2 - 1)) ^ 2 = z ^ 2 - 1 := Real.sq_sqrt hz1
    rw [← hsq]
    exact pow_le_pow_left₀ hphase hhigh 2

/-! ## Transfer to the Liouville–Green amplitude -/

/-- The fourth power of the exterior Liouville–Green amplitude, as a function of the phase value
`xi` reached at `x`.  At `σ = 0` and `xi = √(x²−1)` this is `x⁻²`. -/
def radialPSWFAmplitudePow4 (sigma xi x : ℝ) : ℝ :=
  xi ^ 2 / ((x ^ 2 - 1) * (x ^ 2 - sigma ^ 2))

theorem radialPSWFAmplitudePow4_zero {x : ℝ} (hx : 1 < x) :
    radialPSWFAmplitudePow4 0 (Real.sqrt (x ^ 2 - 1)) x = (x ^ 2)⁻¹ := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hpos : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  rw [radialPSWFAmplitudePow4, Real.sq_sqrt hpos.le,
    show ((0 : ℝ)) ^ 2 = 0 by norm_num, sub_zero]
  field_simp

/-- **Exact two-sided comparison of amplitudes.**  Whenever the phase obeys the multiplicative
bound of `radialPSWFExteriorPhase_sub_two_sided` — i.e. `ξ_σ(x)² ∈ [(1−σ²)(x²−1), x²−1]` — the
fourth power of the amplitude ratio is trapped in `[1 − σ², 1/(1 − σ²)]`.

The bound holds for every `x > 1`, arbitrarily close to the turning point.  This is the point the
transfer turns on: the `σ`-deformation of the numerator `ξ_σ²` and of the denominator factor
`x² − σ²` push the ratio in opposite directions and cancel, so the singularities at `x = 1` never
enter. -/
theorem radialPSWFAmplitudePow4_ratio_mem_Icc
    {sigma x xi : ℝ} (hsigma1 : sigma ^ 2 < 1) (hx : 1 < x)
    (hlow : (1 - sigma ^ 2) * (x ^ 2 - 1) ≤ xi ^ 2) (hhigh : xi ^ 2 ≤ x ^ 2 - 1) :
    1 - sigma ^ 2 ≤ radialPSWFAmplitudePow4 sigma xi x / radialPSWFAmplitudePow4 0
        (Real.sqrt (x ^ 2 - 1)) x
      ∧ radialPSWFAmplitudePow4 sigma xi x / radialPSWFAmplitudePow4 0
        (Real.sqrt (x ^ 2 - 1)) x ≤ (1 - sigma ^ 2)⁻¹ := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hx2 : (1 : ℝ) < x ^ 2 := by nlinarith
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by linarith
  have hsig0 : (0 : ℝ) ≤ sigma ^ 2 := sq_nonneg sigma
  have hxe : (0 : ℝ) < x ^ 2 - sigma ^ 2 := by linarith
  have hden : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - sigma ^ 2) := mul_pos h1 hxe
  have he : (0 : ℝ) < 1 - sigma ^ 2 := by linarith
  have hratio : radialPSWFAmplitudePow4 sigma xi x
      / radialPSWFAmplitudePow4 0 (Real.sqrt (x ^ 2 - 1)) x
      = x ^ 2 * xi ^ 2 / ((x ^ 2 - 1) * (x ^ 2 - sigma ^ 2)) := by
    rw [radialPSWFAmplitudePow4_zero hx, radialPSWFAmplitudePow4]
    field_simp
  rw [hratio]
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [hlow, h1, hxe, hsig0]
  · rw [div_le_iff₀ hden, inv_eq_one_div, one_div, ← div_eq_inv_mul, le_div_iff₀ he]
    nlinarith [hhigh, h1, hxe, hsig0, hx2]

/-- **The transfer, with no hypothesis on the phase.**  For the actual anchored Liouville phase the
fourth power of the amplitude ratio is trapped in `[1 − σ², 1/(1 − σ²)]` at every point of the
exterior ray.  At `σ = 0` both bounds are `1`, as they must be. -/
theorem radialPSWFAmplitudePow4_turning_ratio_mem_Icc
    {sigma x : ℝ} (hsigma : sigma ^ 2 < 1) (hx : 1 < x) :
    1 - sigma ^ 2 ≤ radialPSWFAmplitudePow4 sigma (radialPSWFTurningPhase sigma x) x
        / radialPSWFAmplitudePow4 0 (Real.sqrt (x ^ 2 - 1)) x
      ∧ radialPSWFAmplitudePow4 sigma (radialPSWFTurningPhase sigma x) x
        / radialPSWFAmplitudePow4 0 (Real.sqrt (x ^ 2 - 1)) x ≤ (1 - sigma ^ 2)⁻¹ := by
  obtain ⟨hlow, hhigh⟩ := radialPSWFTurningPhase_sq_mem_Icc hsigma.le hx.le
  exact radialPSWFAmplitudePow4_ratio_mem_Icc hsigma hx hlow hhigh


end

end RHTower
