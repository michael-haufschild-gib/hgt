import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenRadialHierarchy
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenRobinSteinWard

/-!
# Source-specific curvature gap for the theta Born--Witten clock

The observable that turns the first Morse state into the theta source does more than preserve
strict log-concavity.  After writing its positive readout weight as `q`, the exact log-density
curvature is

`4 * q + 6 + 6 / q + 9 / q ^ (2 : ℕ)`.

This profile is uniformly at least `19`.  For the dominant first theta atom this improves the
generic scale floor `4 * pi`; for the supersymmetric partner it improves `2 * pi` to `19 / 2`.
The radial hierarchy inherits the same improvement together with its exact centrifugal term.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Algebraic core of the source-specific curvature gap. -/
lemma nineteen_mul_sq_le_thetaBornCurvatureNumerator
    {q : ℝ} (hq : 0 < q) :
    19 * q ^ (2 : ℕ) ≤ 4 * q ^ (3 : ℕ) + 6 * q ^ (2 : ℕ) + 6 * q + 9 := by
  have hq0 : 0 ≤ q := hq.le
  have hq3 : 0 ≤ q ^ (3 : ℕ) := pow_nonneg hq0 3
  by_cases hq1 : q ≤ 1
  · have hq2_le_q : q ^ (2 : ℕ) ≤ q := by nlinarith [sq_nonneg (q - 1)]
    nlinarith
  · have hq1lt : 1 < q := lt_of_not_ge hq1
    by_cases hq2 : q ≤ 2
    · let z : ℝ := q - 3 / 2
      have hzLower : -(1 / 2 : ℝ) < z := by dsimp [z]; linarith
      have hzUpper : z ≤ 1 / 2 := by dsimp [z]; linarith
      have hpoly :
          4 * q ^ (3 : ℕ) - 13 * q ^ (2 : ℕ) + 6 * q + 9 =
            4 * z ^ (3 : ℕ) + 5 * z ^ (2 : ℕ) - 6 * z + 9 / 4 := by
        dsimp [z]
        ring
      by_cases hz : z ≤ 0
      · have hzSq : z ^ (2 : ℕ) ≤ 1 / 4 := by nlinarith [sq_nonneg (z + 1 / 2)]
        have hfactor : 4 * z ^ (2 : ℕ) - 1 ≤ 0 := by nlinarith
        have hcubic : 0 ≤ z * (4 * z ^ (2 : ℕ) - 1) :=
          mul_nonneg_of_nonpos_of_nonpos hz hfactor
        have hpos : 0 ≤ 4 * z ^ (3 : ℕ) + 5 * z ^ (2 : ℕ) - 6 * z + 9 / 4 := by
          nlinarith [sq_nonneg z]
        nlinarith [hpoly]
      · have hz0 : 0 < z := lt_of_not_ge hz
        have hcubic : 0 ≤ z ^ (3 : ℕ) := pow_nonneg hz0.le 3
        have hquad : 0 < 5 * z ^ (2 : ℕ) - 6 * z + 9 / 4 := by
          nlinarith [sq_nonneg (z - 3 / 5)]
        nlinarith [hpoly]
    · have hq2lt : 2 < q := lt_of_not_ge hq2
      let y : ℝ := q - 2
      have hy : 0 < y := by dsimp [y]; linarith
      have hy2 : 0 ≤ y ^ (2 : ℕ) := sq_nonneg y
      have hy3 : 0 ≤ y ^ (3 : ℕ) := pow_nonneg hy.le 3
      have hpoly :
          4 * q ^ (3 : ℕ) - 13 * q ^ (2 : ℕ) + 6 * q + 9 =
            4 * y ^ (3 : ℕ) + 11 * y ^ (2 : ℕ) + 2 * y + 1 := by
        dsimp [y]
        ring
      nlinarith

/-- Exact readout-coordinate form of the theta Born--Witten log curvature. -/
theorem thetaCuspBornWittenLogCurvature_eq_readoutProfile
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenLogCurvature n x =
      4 * thetaCuspBornWittenWeight n x + 6 +
        6 / thetaCuspBornWittenWeight n x +
        9 / thetaCuspBornWittenWeight n x ^ (2 : ℕ) := by
  have hq := thetaCuspBornWittenWeight_pos hn hx
  have ht : thetaCuspMorseScale n x =
      thetaCuspBornWittenWeight n x + 3 / 2 := by
    rw [thetaCuspBornWittenWeight_eq]
    ring
  rw [thetaCuspBornWittenLogCurvature, thetaCuspBornWittenCurvature, ht]
  field_simp [hq.ne']
  ring

/-- The exact theta-source log-density curvature has the absolute gap `19`. -/
theorem nineteen_le_thetaCuspBornWittenLogCurvature
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (19 : ℝ) ≤ thetaCuspBornWittenLogCurvature n x := by
  let q := thetaCuspBornWittenWeight n x
  have hq : 0 < q := thetaCuspBornWittenWeight_pos hn hx
  have hq2 : 0 < q ^ (2 : ℕ) := sq_pos_of_pos hq
  have hnum := nineteen_mul_sq_le_thetaBornCurvatureNumerator hq
  rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile hn hx]
  change (19 : ℝ) ≤ 4 * q + 6 + 6 / q + 9 / q ^ (2 : ℕ)
  rw [show 4 * q + 6 + 6 / q + 9 / q ^ (2 : ℕ) =
      (4 * q ^ (3 : ℕ) + 6 * q ^ (2 : ℕ) + 6 * q + 9) / q ^ (2 : ℕ) by
    field_simp [hq.ne']]
  exact (le_div_iff₀ hq2).2 hnum

/-- The source-specific and scale-sensitive curvature floors are simultaneously available. -/
theorem max_nineteen_four_pi_sq_le_thetaCuspBornWittenLogCurvature
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    max (19 : ℝ) (4 * Real.pi * (n : ℝ) ^ (2 : ℕ)) ≤
      thetaCuspBornWittenLogCurvature n x := by
  exact max_le (nineteen_le_thetaCuspBornWittenLogCurvature hn hx)
    (thetaCuspBornWittenLogCurvature_floor hn hx)

/-- For the first atom the new rational gap strictly improves the old `4 * pi` floor. -/
theorem four_pi_lt_nineteen : 4 * Real.pi < (19 : ℝ) := by
  nlinarith [Real.pi_lt_d4]

/-- The supersymmetric partner potential inherits half of the log-curvature gap. -/
theorem nineteen_halves_le_thetaCuspBornWittenPotentialPlus
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (19 / 2 : ℝ) ≤ thetaCuspBornWittenPotentialPlus n x := by
  have hcurv := nineteen_le_thetaCuspBornWittenLogCurvature hn hx
  simp only [thetaCuspBornWittenLogCurvature] at hcurv
  simp only [thetaCuspBornWittenPotentialPlus]
  nlinarith [sq_nonneg (thetaCuspBornWittenSuperpotential n x)]

/-- Radial dressing preserves the absolute gap and adds its exact centrifugal curvature. -/
theorem nineteen_add_centrifugal_le_thetaCuspBornWittenRadialLogCurvature
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (19 : ℝ) + 2 * (k : ℝ) / x ^ (2 : ℕ) ≤
      thetaCuspBornWittenRadialLogCurvature k n x := by
  have hbase := nineteen_le_thetaCuspBornWittenLogCurvature hn hx.le
  calc
    (19 : ℝ) + 2 * (k : ℝ) / x ^ (2 : ℕ) ≤
        thetaCuspBornWittenLogCurvature n x + 2 * (k : ℝ) / x ^ (2 : ℕ) :=
      by simpa only [add_comm] using
        add_le_add_right hbase (2 * (k : ℝ) / x ^ (2 : ℕ))
    _ = thetaCuspBornWittenRadialLogCurvature k n x := by
      simp only [thetaCuspBornWittenRadialLogCurvature,
        thetaCuspBornWittenRadialCurvature,
        thetaCuspBornWittenLogCurvature]
      ring

/-! ### Ward consequence: exact localization of the dominant clock atom -/

/-- The first Born--Witten superpotential starts no lower than `-1/16`. -/
theorem neg_one_sixteenth_le_thetaCuspFirstBornWittenSuperpotential_zero :
    -(1 / 16 : ℝ) ≤ thetaCuspBornWittenSuperpotential 1 0 := by
  have hden : 0 < Real.pi - 3 / 2 := by
    nlinarith [Real.pi_gt_three]
  have hpi : (25 / 8 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d4]
  have hpoly :
      Real.pi ≤ (Real.pi - 19 / 16) * (Real.pi - 3 / 2) := by
    nlinarith [sq_nonneg (Real.pi - 25 / 8)]
  simp only [thetaCuspBornWittenSuperpotential,
    thetaCuspMorseSuperpotential, thetaCuspBornWittenWeight_eq,
    thetaCuspMorseScale, Nat.cast_one, one_mul, Real.exp_zero, one_pow]
  norm_num only [mul_one]
  rw [show -(1 / 16 : ℝ) ≤ Real.pi - 5 / 4 - Real.pi / (Real.pi - 3 / 2) ↔
      Real.pi / (Real.pi - 3 / 2) ≤ Real.pi - 19 / 16 by constructor <;> intro h <;> linarith]
  exact (div_le_iff₀ hden).2 hpoly

/-- The `19` log-curvature gap integrates to a source-specific affine lower support for the first
superpotential. -/
theorem thetaCuspFirstBornWittenSuperpotential_affine_lower
    {x : ℝ} (hx : 0 ≤ x) :
    -(1 / 16 : ℝ) + (19 / 2 : ℝ) * x ≤
      thetaCuspBornWittenSuperpotential 1 x := by
  let W : ℝ → ℝ := thetaCuspBornWittenSuperpotential 1
  have hcontinuous : ContinuousOn W (Ici 0) := by
    intro y hy
    exact (hasDerivAt_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) hy).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ W (interior (Ici 0)) := by
    intro y hy
    rw [interior_Ici] at hy
    exact (hasDerivAt_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) hy.le).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Ici 0),
      (19 / 2 : ℝ) ≤ deriv W y := by
    intro y hy
    rw [interior_Ici] at hy
    have hgap := nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hy.le
    rw [deriv_thetaCuspBornWittenSuperpotential (n := 1) (by norm_num) hy.le]
    simp only [thetaCuspBornWittenLogCurvature] at hgap
    linarith
  have hslope := (convex_Ici 0).mul_sub_le_image_sub_of_le_deriv
    hcontinuous hdifferentiable hderiv 0 (by simp) x hx hx
  have hboundary := neg_one_sixteenth_le_thetaCuspFirstBornWittenSuperpotential_zero
  dsimp only [W] at hslope
  nlinarith

/-- Pointwise Ward-localization inequality.  The small boundary defect is absorbed by one exact
square, leaving a `75/8` quadratic coercivity coefficient. -/
theorem thetaCuspFirstBornWitten_localization_integrand
    {x : ℝ} (hx : 0 ≤ x) :
    ((75 / 8 : ℝ) * x ^ (2 : ℕ) - 1 / 128) *
        thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ) ≤
      x * thetaCuspBornWittenSuperpotential 1 x *
        thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ) := by
  have hW := thetaCuspFirstBornWittenSuperpotential_affine_lower hx
  have hxW : (75 / 8 : ℝ) * x ^ (2 : ℕ) - 1 / 128 ≤
      x * thetaCuspBornWittenSuperpotential 1 x := by
    have hmul := mul_le_mul_of_nonneg_left hW hx
    nlinarith [sq_nonneg (4 * x - 1)]
  exact mul_le_mul_of_nonneg_right hxW
    (sq_nonneg (thetaCuspBornWittenAmplitude 1 x))

/-- The dominant Born--Witten state has strictly positive mass. -/
theorem thetaCuspFirstMorseBornMoment_zero_pos :
    0 < thetaCuspMorseBornMoment 0 1 := by
  rw [thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]
  simp only [Nat.mul_zero, pow_zero, one_mul]
  have hint : IntegrableOn
      (fun x : ℝ => thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq
      0 (n := 1) (by norm_num)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun x : ℝ => thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ) := by
    filter_upwards [] with x
    exact sq_nonneg _
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint).2
  have hcontinuous : Continuous
      (fun x : ℝ => thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) := by
    unfold thetaCuspBornWittenAmplitude thetaCuspBornWittenWeight
      thetaCuspMorseSuperpotential thetaCuspMorseGroundState
      thetaCuspMorseZeroMode thetaCuspMorseScale
    fun_prop
  have hopen : IsOpen
      (Function.support (fun x : ℝ => thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) ∩ Ioi 0) :=
    hcontinuous.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  exact (sq_pos_of_pos
    (thetaCuspBornWittenAmplitude_pos (n := 1) (by norm_num) (by norm_num))).ne'

/-- **Dominant-clock localization law.**  The Ward identity and source-specific curvature gap
give an unconditional normalized second-position bound `E[X^(2 : ℕ)] ≤ 13/240`. -/
theorem two_hundred_forty_mul_firstMorseBornMoment_one_le_thirteen_mass :
    240 * thetaCuspMorseBornMoment 1 1 ≤
      13 * thetaCuspMorseBornMoment 0 1 := by
  let rho : ℝ → ℝ := fun x => thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)
  let lower : ℝ → ℝ := fun x => ((75 / 8 : ℝ) * x ^ (2 : ℕ) - 1 / 128) * rho x
  let ward : ℝ → ℝ := fun x => x * thetaCuspBornWittenSuperpotential 1 x * rho x
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq 0
    (n := 1) (by norm_num)
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq 2
    (n := 1) (by norm_num)
  have hlower : IntegrableOn lower (Ioi 0) := by
    have h := (h2.const_mul (75 / 8 : ℝ)).sub (h0.const_mul (1 / 128 : ℝ))
    apply h.congr
    filter_upwards [] with x
    dsimp only [lower, rho]
    simp only [pow_zero, one_mul, Pi.sub_apply]
    ring
  have hward : IntegrableOn ward (Ioi 0) := by
    simpa only [ward, rho, pow_one] using
      integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
        1 (n := 1) (by norm_num)
  have hmono : (∫ x : ℝ in Ioi 0, lower x) ≤ ∫ x : ℝ in Ioi 0, ward x := by
    apply integral_mono_ae hlower hward
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact thetaCuspFirstBornWitten_localization_integrand hx.le
  have hlowerValue : (∫ x : ℝ in Ioi 0, lower x) =
      (75 / 8 : ℝ) * thetaCuspMorseBornMoment 1 1 -
        (1 / 128 : ℝ) * thetaCuspMorseBornMoment 0 1 := by
    rw [show lower = fun x : ℝ =>
        (75 / 8 : ℝ) * (x ^ (2 : ℕ) * rho x) -
          (1 / 128 : ℝ) * (x ^ (0 : ℕ) * rho x) by
      funext x
      dsimp only [lower]
      simp only [pow_zero, one_mul]
      ring]
    rw [integral_sub (h2.const_mul (75 / 8 : ℝ)) (h0.const_mul (1 / 128 : ℝ)),
      integral_const_mul, integral_const_mul]
    rw [← thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq 1 1,
      ← thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq 0 1]
  have hwardValue : (∫ x : ℝ in Ioi 0, ward x) =
      (1 / 2 : ℝ) * thetaCuspMorseBornMoment 0 1 := by
    simpa only [ward, rho, Nat.mul_zero, Nat.reduceAdd, pow_one,
      Nat.cast_one] using
      thetaCuspBornWitten_odd_superpotential_moment 0 (n := 1) (by norm_num)
  rw [hlowerValue, hwardValue] at hmono
  nlinarith

/-- The same localization bound in the raw atom moments consumed by the theta Hankel route. -/
theorem two_hundred_forty_mul_firstAtomMoment_one_le_thirteen_mass :
    240 * thetaCuspAtomRawEvenMoment 1 1 ≤
      13 * thetaCuspAtomRawEvenMoment 0 1 := by
  rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
    thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
  have h := two_hundred_forty_mul_firstMorseBornMoment_one_le_thirteen_mass
  nlinarith [Real.pi_pos]

/-- **No-go for the coarse mean-floor route.**  The lower mean condition that would combine a
uniform-curvature Brascamp--Lieb estimate with the relaxed fourth-moment gate is false for the
actual first theta atom. -/
theorem not_thetaCuspFirstAtom_uniformCurvature_meanFloor :
    ¬ 64 * (3005 / 2997 : ℝ) ^ (2 : ℕ) * thetaCuspAtomRawEvenMoment 0 1 ≤
      19 * (45 - 16 * (3005 / 2997 : ℝ) ^ (2 : ℕ)) *
        thetaCuspAtomRawEvenMoment 1 1 := by
  intro hfloor
  have hmean := two_hundred_forty_mul_firstAtomMoment_one_le_thirteen_mass
  have hmass : 0 < thetaCuspAtomRawEvenMoment 0 1 := by
    rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      thetaCuspFirstMorseBornMoment_zero_pos
  norm_num at hfloor
  nlinarith

end

end RHTower
