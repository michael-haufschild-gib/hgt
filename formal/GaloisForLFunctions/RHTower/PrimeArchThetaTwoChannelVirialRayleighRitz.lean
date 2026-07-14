import GaloisForLFunctions.RHTower.PrimeArchThetaTwoChannelRayleighRitz

/-!
# Polarized hypervirial form of the theta two-channel Rayleigh matrix

The generalized quantum virial identity is polarized before integration.  It
therefore replaces all three entries of the dilation/quadratic-monomial score
matrix by curvature/field-gradient values while retaining the half-line
boundary current explicitly.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Curvature value of the dilation-score energy. -/
def thetaCuspFirstRadialDilationVirialEnergy : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ((1 / 2 : ℝ) * x ^ 2 * thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ)) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Polarized curvature value of the dilation/quadratic-monomial mixed
energy. -/
def thetaCuspFirstRadialTwoChannelVirialCrossEnergy : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ((1 / 2 : ℝ) * x ^ 3 * thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 2 : ℝ) * x) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Curvature value of the quadratic-monomial score energy. -/
def thetaCuspFirstRadialQuadraticMonomialVirialEnergy : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ((1 / 2 : ℝ) * x ^ 4 * thetaCuspBornWittenRadialCurvature 1 1 x +
        x ^ 2) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Monomial half-line virial current.  The three matrix entries use
`m=2,3,4`. -/
def thetaCuspFirstRadialMonomialVirialCurrent (m : ℕ) (x : ℝ) : ℝ :=
  x ^ m * thetaCuspBornWittenRadialSuperpotential 1 1 x *
    thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Every polynomially weighted radial curvature value is integrable. -/
theorem integrableOn_pow_mul_thetaCuspFirstRadialCurvature (m : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * thetaCuspBornWittenRadialCurvature 1 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  let majorant : ℝ → ℝ := fun x => Real.pi⁻¹ *
    (5 * (x ^ (m + 2) * thetaCuspMorseScale 1 x ^ 2 *
        thetaCuspSourceTerm x 1) + x ^ m * thetaCuspSourceTerm x 1)
  have ht := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source (m + 2)
  have hs0 := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    m thetaCuspSeedPolynomial (n := 1) (by norm_num)
  have hs : IntegrableOn (fun x : ℝ => x ^ m * thetaCuspSourceTerm x 1)
      (Ioi 0) := by
    apply hs0.congr
    filter_upwards [] with x
    rw [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1) x]
  have hmajor : IntegrableOn majorant (Ioi 0) := by
    have hsum := (ht.const_mul 5).add hs
    have hscaled := hsum.const_mul Real.pi⁻¹
    apply hscaled.congr
    filter_upwards [] with x
    simp only [majorant, Pi.add_apply]
  apply Integrable.mono' hmajor
  · exact ((((measurable_id.pow_const m).mul
      measurable_thetaCuspFirstRadialCurvature).mul
        (measurable_thetaCuspFirstRadialAmplitude.pow_const 2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    have hcurv0 : 0 ≤ thetaCuspBornWittenRadialCurvature 1 1 x := by
      have hfloor := thetaCuspBornWittenRadialCurvature_floor
        (k := 1) (n := 1) (by norm_num) hx
      norm_num only [Nat.cast_one, one_pow, mul_one] at hfloor
      have hbase : 0 ≤ 2 * Real.pi + (1 : ℝ) / x ^ 2 := by positivity
      exact hbase.trans hfloor
    have hleft0 : 0 ≤ x ^ m * thetaCuspBornWittenRadialCurvature 1 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hx.le _) hcurv0) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hleft0]
    let t := thetaCuspMorseScale 1 x
    let K := thetaCuspBornWittenRadialCurvature 1 1 x
    let S := thetaCuspSourceTerm x 1
    have ht1 : 1 ≤ t := by
      have ht3 : 3 < t := by
        dsimp [t, thetaCuspMorseScale]
        have hexp : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
        have hexpSq : 1 < Real.exp x ^ 2 := by
          nlinarith [sq_nonneg (Real.exp x - 1)]
        have hmul : Real.pi ≤ Real.pi * Real.exp x ^ 2 :=
          le_mul_of_one_le_right Real.pi_pos.le hexpSq.le
        simpa only [Nat.cast_one, one_mul] using Real.pi_gt_three.trans_le hmul
      linarith
    have htSq : t ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
    have hK : K ≤ 5 * t + 1 / x ^ 2 := by
      simpa only [K, t] using thetaCuspFirstRadialCurvature_le_scale hx
    have hK' : K ≤ 5 * t ^ 2 + 1 / x ^ 2 := by nlinarith
    have hS : 0 ≤ S := thetaCuspSourceTerm_nonneg_of_pos hx 1
    have hxm2 : 0 ≤ x ^ (m + 2) := pow_nonneg hx.le _
    have hmul : x ^ (m + 2) * K * S ≤
        x ^ (m + 2) * (5 * t ^ 2 + 1 / x ^ 2) * S :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK' hxm2) hS
    have hsource := thetaCusp_pow_mul_sourceTerm_eq_pi_mul_radialAmplitude_sq
      1 (n := 1) (by norm_num) hx.le
    have hamp : thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 =
        Real.pi⁻¹ * x ^ 2 * S := by
      norm_num only [Nat.reduceMul] at hsource
      dsimp only [S]
      field_simp [Real.pi_ne_zero]
      nlinarith
    dsimp only [majorant]
    dsimp only [K, t, S] at hmul ⊢
    rw [hamp]
    have hpi : 0 ≤ Real.pi⁻¹ := by positivity
    rw [show x ^ m * thetaCuspBornWittenRadialCurvature 1 1 x *
        (Real.pi⁻¹ * x ^ 2 * thetaCuspSourceTerm x 1) =
      Real.pi⁻¹ * (x ^ m * thetaCuspBornWittenRadialCurvature 1 1 x *
        (x ^ 2 * thetaCuspSourceTerm x 1)) by ring]
    apply mul_le_mul_of_nonneg_left _ hpi
    calc
      x ^ m * thetaCuspBornWittenRadialCurvature 1 1 x *
          (x ^ 2 * thetaCuspSourceTerm x 1) =
          x ^ (m + 2) * thetaCuspBornWittenRadialCurvature 1 1 x *
            thetaCuspSourceTerm x 1 := by rw [pow_add]; ring
      _ ≤ x ^ (m + 2) *
          (5 * thetaCuspMorseScale 1 x ^ 2 + 1 / x ^ 2) *
            thetaCuspSourceTerm x 1 := hmul
      _ = 5 * (x ^ (m + 2) * thetaCuspMorseScale 1 x ^ 2 *
          thetaCuspSourceTerm x 1) + x ^ m * thetaCuspSourceTerm x 1 := by
        rw [pow_add]
        have hcancel : x ^ 2 * (1 / x ^ 2) = 1 := by
          field_simp [hx.ne']
        calc
          x ^ m * x ^ 2 *
                (5 * thetaCuspMorseScale 1 x ^ 2 + 1 / x ^ 2) *
              thetaCuspSourceTerm x 1 =
              5 * (x ^ 2 * x ^ m * thetaCuspMorseScale 1 x ^ 2 *
                thetaCuspSourceTerm x 1) +
                x ^ m * (x ^ 2 * (1 / x ^ 2)) *
                  thetaCuspSourceTerm x 1 := by ring
          _ = _ := by rw [hcancel]; ring

/-- The monomial virial current has a polynomial--Gaussian source form. -/
theorem thetaCuspFirstRadialMonomialVirialCurrent_eq
    (m : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialMonomialVirialCurrent m x =
      -(2 * Real.pi)⁻¹ * x ^ (m + 2) *
          thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1 x -
        Real.pi⁻¹ * x ^ (m + 1) * thetaCuspSourceTerm x 1 := by
  have hB := thetaCuspBornWittenSuperpotential_mul_amplitude_sq_eq_polynomialAtom
    (n := 1) (by norm_num) hx
  have hsource := thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    (n := 1) (by norm_num) hx.le
  have hamp : thetaCuspBornWittenAmplitude 1 x ^ 2 =
      Real.pi⁻¹ * thetaCuspSourceTerm x 1 := by
    field_simp [Real.pi_ne_zero]
    nlinarith
  simp only [thetaCuspFirstRadialMonomialVirialCurrent,
    thetaCuspBornWittenRadialSuperpotential,
    thetaCuspBornWittenRadialAmplitude_sq, Nat.reduceMul, Nat.cast_one]
  rw [show
      x ^ m * (thetaCuspBornWittenSuperpotential 1 x - (1 : ℝ) / x) *
          (x ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) =
        x ^ (m + 2) * (thetaCuspBornWittenSuperpotential 1 x *
            thetaCuspBornWittenAmplitude 1 x ^ 2) -
          x ^ (m + 1) * thetaCuspBornWittenAmplitude 1 x ^ 2 by
      rw [pow_add, pow_add]
      field_simp [hx.ne'],
    hB, hamp]
  ring

/-- Every positive-degree monomial virial current vanishes at the radial
endpoint. -/
theorem thetaCuspFirstRadialMonomialVirialCurrent_tendsto_zero (m : ℕ) :
    Tendsto (thetaCuspFirstRadialMonomialVirialCurrent m)
      (𝓝[>] 0) (𝓝 0) := by
  let g : ℝ → ℝ := fun x =>
    -(2 * Real.pi)⁻¹ * x ^ (m + 2) *
        thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1 x -
      Real.pi⁻¹ * x ^ (m + 1) * thetaCuspSourceTerm x 1
  have hatom : Continuous
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspLogDerivativePolynomial 1) 1 x).continuousAt
  have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x 1) := by
    rw [thetaCuspSourceTerm_eq_polynomialAtom]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial 1 x).continuousAt
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgt := (hg.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0] at hgt
  apply Tendsto.congr' _ hgt
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (thetaCuspFirstRadialMonomialVirialCurrent_eq m hx).symm

/-- Every monomial virial current vanishes at infinity. -/
theorem thetaCuspFirstRadialMonomialVirialCurrent_tendsto_atTop_zero (m : ℕ) :
    Tendsto (thetaCuspFirstRadialMonomialVirialCurrent m) atTop (𝓝 0) := by
  let A : ℝ → ℝ :=
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1
  let S : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  let g : ℝ → ℝ := fun x =>
    -(2 * Real.pi)⁻¹ * x ^ (m + 2) * A x -
      Real.pi⁻¹ * x ^ (m + 1) * S x
  have hA := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (m + 2) (thetaCuspLogDerivativePolynomial 1) (n := 1) (by norm_num)
  have hS : Tendsto (fun x : ℝ => x ^ (m + 1) * S x) atTop (𝓝 0) := by
    simpa only [S, ← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1)] using
      pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        (m + 1) thetaCuspSeedPolynomial (n := 1) (by norm_num)
  have hg0 := (hA.const_mul (-(2 * Real.pi)⁻¹)).sub
    (hS.const_mul Real.pi⁻¹)
  have hg : Tendsto g atTop (𝓝 0) := by
    convert hg0 using 1
    · funext x
      dsimp [g, A]
      ring
    · ring
  apply Tendsto.congr' _ hg
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (thetaCuspFirstRadialMonomialVirialCurrent_eq m hx).symm

theorem integrableOn_thetaCuspFirstRadialDilationVirialEnergy :
    IntegrableOn (fun x : ℝ =>
      ((1 / 2 : ℝ) * x ^ 2 * thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ)) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      (Ioi 0) := by
  have hK := (integrableOn_pow_mul_thetaCuspFirstRadialCurvature 2).const_mul
    (1 / 2 : ℝ)
  have h0 := (integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    0 1 (n := 1) (by norm_num)).const_mul (1 / 4 : ℝ)
  apply (hK.add h0).congr
  filter_upwards [] with x
  simp only [Pi.add_apply, pow_zero, one_mul]
  ring

theorem integrableOn_thetaCuspFirstRadialTwoChannelVirialCrossEnergy :
    IntegrableOn (fun x : ℝ =>
      ((1 / 2 : ℝ) * x ^ 3 * thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 2 : ℝ) * x) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      (Ioi 0) := by
  have hK := (integrableOn_pow_mul_thetaCuspFirstRadialCurvature 3).const_mul
    (1 / 2 : ℝ)
  have h1 := (integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    1 1 (n := 1) (by norm_num)).const_mul (1 / 2 : ℝ)
  apply (hK.add h1).congr
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring

theorem integrableOn_thetaCuspFirstRadialQuadraticMonomialVirialEnergy :
    IntegrableOn (fun x : ℝ =>
      ((1 / 2 : ℝ) * x ^ 4 * thetaCuspBornWittenRadialCurvature 1 1 x +
        x ^ 2) * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      (Ioi 0) := by
  have hK := (integrableOn_pow_mul_thetaCuspFirstRadialCurvature 4).const_mul
    (1 / 2 : ℝ)
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 1 (n := 1) (by norm_num)
  apply (hK.add h2).congr
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring

/-- Bilinear curvature pairing for two arbitrary generators in the selected
two-channel span. -/
def thetaCuspFirstRadialTwoChannelVirialPairing
    (a b c d : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ((1 / 2 : ℝ) * thetaCuspTwoChannelSteinField a b x *
          thetaCuspTwoChannelSteinField c d x *
          thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ) * thetaCuspTwoChannelSteinFieldDerivative a b x *
          thetaCuspTwoChannelSteinFieldDerivative c d x) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- **Source-specific polarized hypervirial theorem.**  Every mixed score
pairing in the two-channel span is exactly its curvature/field-gradient
pairing; both half-line endpoint currents vanish. -/
theorem thetaCuspFirstRadialTwoChannelSteinPairing_eq_virialPairing
    (a b c d : ℝ) :
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialTwoChannelSteinScore a b x *
        thetaCuspFirstRadialTwoChannelSteinScore c d x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      thetaCuspFirstRadialTwoChannelVirialPairing a b c d := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let amp : ℝ → ℝ := thetaCuspBornWittenRadialAmplitude 1 1
  let f : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialTwoChannelSteinScore a b x * amp x
  let g : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialTwoChannelSteinScore c d x * amp x
  have hfMeas : AEStronglyMeasurable f μ :=
    (measurable_thetaCuspFirstRadialTwoChannelSteinScore a b |>.mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g μ :=
    (measurable_thetaCuspFirstRadialTwoChannelSteinScore c d |>.mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hfSq : Integrable (fun x => f x ^ 2) μ := by
    apply (integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy a b).congr
    filter_upwards [] with x
    simp only [f, amp]
    ring
  have hgSq : Integrable (fun x => g x ^ 2) μ := by
    apply (integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy c d).congr
    filter_upwards [] with x
    simp only [g, amp]
    ring
  have hfLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfMeas).2 hfSq
  have hgLp : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgMeas).2 hgSq
  have hscore0 := hfLp.integrable_mul hgLp
  have hscore : IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialTwoChannelSteinScore a b x *
        thetaCuspFirstRadialTwoChannelSteinScore c d x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
    apply hscore0.congr
    filter_upwards [] with x
    simp only [f, g, amp, Pi.mul_apply]
    ring
  have hvirial : IntegrableOn (fun x : ℝ =>
      ((1 / 2 : ℝ) * thetaCuspTwoChannelSteinField a b x *
          thetaCuspTwoChannelSteinField c d x *
          thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ) * thetaCuspTwoChannelSteinFieldDerivative a b x *
          thetaCuspTwoChannelSteinFieldDerivative c d x) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
    have hcomb :=
      ((integrableOn_thetaCuspFirstRadialDilationVirialEnergy.const_mul
          (a * c)).add
        (integrableOn_thetaCuspFirstRadialTwoChannelVirialCrossEnergy.const_mul
          (a * d + b * c))).add
        (integrableOn_thetaCuspFirstRadialQuadraticMonomialVirialEnergy.const_mul
          (b * d))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [Pi.add_apply, thetaCuspTwoChannelSteinField,
      thetaCuspTwoChannelSteinFieldDerivative]
    ring
  have hzero : Tendsto (fun x : ℝ =>
      thetaCuspTwoChannelSteinField a b x *
        thetaCuspTwoChannelSteinField c d x *
        thetaCuspBornWittenRadialSuperpotential 1 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hcomb :=
      (((thetaCuspFirstRadialMonomialVirialCurrent_tendsto_zero 2).const_mul
          (a * c)).add
        ((thetaCuspFirstRadialMonomialVirialCurrent_tendsto_zero 3).const_mul
          (a * d + b * c))).add
        ((thetaCuspFirstRadialMonomialVirialCurrent_tendsto_zero 4).const_mul
          (b * d))
    convert hcomb using 1
    · funext x
      simp only [thetaCuspTwoChannelSteinField,
        thetaCuspFirstRadialMonomialVirialCurrent]
      ring
    · ring
  have hinfty : Tendsto (fun x : ℝ =>
      thetaCuspTwoChannelSteinField a b x *
        thetaCuspTwoChannelSteinField c d x *
        thetaCuspBornWittenRadialSuperpotential 1 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) atTop (𝓝 0) := by
    have hcomb :=
      (((thetaCuspFirstRadialMonomialVirialCurrent_tendsto_atTop_zero 2).const_mul
          (a * c)).add
        ((thetaCuspFirstRadialMonomialVirialCurrent_tendsto_atTop_zero 3).const_mul
          (a * d + b * c))).add
        ((thetaCuspFirstRadialMonomialVirialCurrent_tendsto_atTop_zero 4).const_mul
          (b * d))
    convert hcomb using 1
    · funext x
      simp only [thetaCuspTwoChannelSteinField,
        thetaCuspFirstRadialMonomialVirialCurrent]
      ring
    · ring
  have h := HTGeometry.integral_Ioi_halfLineSteinScore_mul_eq_virial
    (P := thetaCuspTwoChannelSteinField a b)
    (P' := thetaCuspTwoChannelSteinFieldDerivative a b)
    (Q := thetaCuspTwoChannelSteinField c d)
    (Q' := thetaCuspTwoChannelSteinFieldDerivative c d)
    (ρ := fun x => thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
    (W := thetaCuspBornWittenRadialSuperpotential 1 1)
    (W' := thetaCuspBornWittenRadialCurvature 1 1)
    (fun x _ => hasDerivAt_thetaCuspTwoChannelSteinField a b x)
    (fun x _ => hasDerivAt_thetaCuspTwoChannelSteinField c d x)
    (fun x hx => hasDerivAt_thetaCuspBornWittenRadialSuperpotential
      (k := 1) (n := 1) (by norm_num) hx)
    (fun x hx => hasDerivAt_thetaCuspFirstRadialDensity hx)
    (by simpa only [thetaCuspFirstRadialTwoChannelSteinScore] using hscore)
    hvirial hzero hinfty
  simpa only [thetaCuspFirstRadialTwoChannelVirialPairing,
    thetaCuspFirstRadialTwoChannelSteinScore] using h

/-- Dilation score energy equals its curvature value. -/
theorem thetaCuspFirstRadialDilationSteinEnergy_eq_virialEnergy :
    thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 =
      thetaCuspFirstRadialDilationVirialEnergy := by
  rw [thetaCuspFirstRadialTwoChannelSteinEnergy,
    thetaCuspFirstRadialDilationVirialEnergy]
  have h := thetaCuspFirstRadialTwoChannelSteinPairing_eq_virialPairing
    1 0 1 0
  rw [thetaCuspFirstRadialTwoChannelVirialPairing] at h
  simp only [thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative] at h
  ring_nf at h ⊢
  exact h

/-- The mixed score energy is exactly the polarized curvature value. -/
theorem thetaCuspFirstRadialTwoChannelSteinCrossEnergy_eq_virialCrossEnergy :
    thetaCuspFirstRadialTwoChannelSteinCrossEnergy =
      thetaCuspFirstRadialTwoChannelVirialCrossEnergy := by
  rw [thetaCuspFirstRadialTwoChannelSteinCrossEnergy,
    thetaCuspFirstRadialTwoChannelVirialCrossEnergy]
  have h := thetaCuspFirstRadialTwoChannelSteinPairing_eq_virialPairing
    1 0 0 1
  rw [thetaCuspFirstRadialTwoChannelVirialPairing] at h
  simp only [thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative] at h
  ring_nf at h ⊢
  exact h

/-- Quadratic-monomial score energy equals its curvature value. -/
theorem thetaCuspFirstRadialQuadraticMonomialSteinEnergy_eq_virialEnergy :
    thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 =
      thetaCuspFirstRadialQuadraticMonomialVirialEnergy := by
  rw [thetaCuspFirstRadialTwoChannelSteinEnergy,
    thetaCuspFirstRadialQuadraticMonomialVirialEnergy]
  have h := thetaCuspFirstRadialTwoChannelSteinPairing_eq_virialPairing
    0 1 0 1
  rw [thetaCuspFirstRadialTwoChannelVirialPairing] at h
  simp only [thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative] at h
  ring_nf at h ⊢
  exact h

/-- Determinant of the polarized hypervirial energy matrix. -/
def thetaCuspFirstRadialTwoChannelVirialEnergyDet : ℝ :=
  thetaCuspFirstRadialDilationVirialEnergy *
      thetaCuspFirstRadialQuadraticMonomialVirialEnergy -
    thetaCuspFirstRadialTwoChannelVirialCrossEnergy ^ 2

/-- Adjugate response value in polarized hypervirial coordinates. -/
def thetaCuspFirstRadialTwoChannelVirialAdjugateResponse : ℝ :=
  thetaCuspFirstRadialQuadraticMonomialVirialEnergy *
        thetaCuspFirstRadialTwoChannelSteinCoupling 1 0 ^ 2 -
      2 * thetaCuspFirstRadialTwoChannelVirialCrossEnergy *
        thetaCuspFirstRadialTwoChannelSteinCoupling 1 0 *
        thetaCuspFirstRadialTwoChannelSteinCoupling 0 1 +
    thetaCuspFirstRadialDilationVirialEnergy *
      thetaCuspFirstRadialTwoChannelSteinCoupling 0 1 ^ 2

theorem thetaCuspFirstRadialTwoChannelVirialEnergyDet_eq :
    thetaCuspFirstRadialTwoChannelVirialEnergyDet =
      thetaCuspFirstRadialTwoChannelSteinEnergyDet := by
  simp only [thetaCuspFirstRadialTwoChannelVirialEnergyDet,
    thetaCuspFirstRadialTwoChannelSteinEnergyDet,
    thetaCuspFirstRadialDilationSteinEnergy_eq_virialEnergy,
    thetaCuspFirstRadialTwoChannelSteinCrossEnergy_eq_virialCrossEnergy,
    thetaCuspFirstRadialQuadraticMonomialSteinEnergy_eq_virialEnergy]

theorem thetaCuspFirstRadialTwoChannelVirialAdjugateResponse_eq :
    thetaCuspFirstRadialTwoChannelVirialAdjugateResponse =
      thetaCuspFirstRadialTwoChannelSteinAdjugateResponse := by
  simp only [thetaCuspFirstRadialTwoChannelVirialAdjugateResponse,
    thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
    thetaCuspFirstRadialDilationSteinEnergy_eq_virialEnergy,
    thetaCuspFirstRadialTwoChannelSteinCrossEnergy_eq_virialCrossEnergy,
    thetaCuspFirstRadialQuadraticMonomialSteinEnergy_eq_virialEnergy]

theorem thetaCuspFirstRadialTwoChannelVirialEnergyDet_pos :
    0 < thetaCuspFirstRadialTwoChannelVirialEnergyDet := by
  rw [thetaCuspFirstRadialTwoChannelVirialEnergyDet_eq]
  exact thetaCuspFirstRadialTwoChannelSteinEnergyDet_pos

theorem thetaCuspFirstRadialTwoChannelVirialAdjugateResponse_pos :
    0 < thetaCuspFirstRadialTwoChannelVirialAdjugateResponse := by
  rw [thetaCuspFirstRadialTwoChannelVirialAdjugateResponse_eq]
  exact thetaCuspFirstRadialTwoChannelSteinAdjugateResponse_pos

/-- Rayleigh--Ritz certificate with every score product replaced by its
polarized hypervirial value. -/
def ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialTwoChannelVirialEnergyDet ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialTwoChannelVirialAdjugateResponse

/-- Exact certificate replacement: the hypervirial form introduces no new
hypothesis and loses no information. -/
theorem thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff :
    ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate ↔
      ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate := by
  simp only [ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate,
    ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate,
    thetaCuspFirstRadialTwoChannelVirialEnergyDet_eq,
    thetaCuspFirstRadialTwoChannelVirialAdjugateResponse_eq]

/-- Direct first-radial consumer of the polarized hypervirial certificate. -/
theorem thetaCusp_firstRadial_upper_of_twoChannelVirialRayleighRitzCertificate
    (hcert : ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_twoChannelRayleighRitzCertificate
    (thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.mp hcert)

/-- Direct linear Hankel consumer of the polarized hypervirial certificate. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelVirialRayleighRitz
    (hcert : ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelRayleighRitz
    (thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.mp hcert)
    hrelaxed

/-- RH-facing degree-two-tail interface for the polarized hypervirial
certificate. -/
theorem riemannHypothesis_of_twoChannelVirialRayleighRitz_of_primeArchDegreeTwoTail
    (hcert : ThetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_twoChannelRayleighRitz_of_primeArchDegreeTwoTail
    (thetaCuspFirstRadialTwoChannelVirialRayleighRitzCertificate_iff.mp hcert)
    hrelaxed htail

end

end RHTower
