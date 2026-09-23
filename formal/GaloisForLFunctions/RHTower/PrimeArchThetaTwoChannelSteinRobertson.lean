import GaloisForLFunctions.HTGeometry.TwoChannelRobertson
import GaloisForLFunctions.RHTower.PrimeArchThetaQuadraticSteinRobertson
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail

/-!
# Two-channel Stein--Robertson certificate for the first radial theta atom

The dilation field `x` and quadratic monomial field `x^(2 : ℕ)` form a two-channel
quantum-bootstrap family.  The previously selected field `x-x^(2 : ℕ)/2` is one
member.  Allowing the coefficients to vary weakens the source certificate
while preserving the exact first-radial and Hankel consumers.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Dilation generator on the positive half-line. -/
def thetaCuspDilationSteinField (x : ℝ) : ℝ := x

/-- Derivative of the dilation generator. -/
def thetaCuspDilationSteinFieldDerivative (_x : ℝ) : ℝ := 1

/-- Symmetric dilation score in the first radial Born--Witten state. -/
def thetaCuspFirstRadialDilationSteinScore (x : ℝ) : ℝ :=
  HTGeometry.halfLineSteinScore
    thetaCuspDilationSteinField
    thetaCuspDilationSteinFieldDerivative
    (thetaCuspBornWittenRadialSuperpotential 1 1) x

/-- Linear span of the dilation and quadratic-monomial generator channels. -/
def thetaCuspTwoChannelSteinField (a b x : ℝ) : ℝ :=
  a * x + b * x ^ 2

/-- Derivative of the two-channel generator field. -/
def thetaCuspTwoChannelSteinFieldDerivative (a b x : ℝ) : ℝ :=
  a + 2 * b * x

/-- Symmetric score of a two-channel generator in the first radial state. -/
def thetaCuspFirstRadialTwoChannelSteinScore (a b x : ℝ) : ℝ :=
  HTGeometry.halfLineSteinScore
    (thetaCuspTwoChannelSteinField a b)
    (thetaCuspTwoChannelSteinFieldDerivative a b)
    (thetaCuspBornWittenRadialSuperpotential 1 1) x

/-- Squared generator energy of a two-channel score. -/
def thetaCuspFirstRadialTwoChannelSteinEnergy (a b : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspFirstRadialTwoChannelSteinScore a b x ^ 2 *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Mixed energy of the dilation and quadratic-monomial channels. -/
def thetaCuspFirstRadialTwoChannelSteinCrossEnergy : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspFirstRadialTwoChannelSteinScore 1 0 x *
      thetaCuspFirstRadialTwoChannelSteinScore 0 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Exact response coupling of a two-channel generator to the centered
quadratic position observable. -/
def thetaCuspFirstRadialTwoChannelSteinCoupling (a b : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    (a * x ^ 2 + b * x ^ 3) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- The radial singularity cancels from the dilation score on the open
half-line. -/
theorem thetaCuspFirstRadialDilationSteinScore_eq
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialDilationSteinScore x =
      x * thetaCuspBornWittenSuperpotential 1 x - 3 / 2 := by
  simp only [thetaCuspFirstRadialDilationSteinScore,
    HTGeometry.halfLineSteinScore, thetaCuspDilationSteinField,
    thetaCuspDilationSteinFieldDerivative,
    thetaCuspBornWittenRadialSuperpotential]
  field_simp [hx.ne']
  ring

/-- Every two-channel score is an exact linear combination of the dilation
score and the already formalized quadratic score. -/
theorem thetaCuspFirstRadialTwoChannelSteinScore_eq
    (a b x : ℝ) :
    thetaCuspFirstRadialTwoChannelSteinScore a b x =
      (a + 2 * b) * thetaCuspFirstRadialDilationSteinScore x -
        2 * b * thetaCuspFirstRadialQuadraticSteinScore x := by
  simp only [thetaCuspFirstRadialTwoChannelSteinScore,
    thetaCuspFirstRadialDilationSteinScore,
    thetaCuspFirstRadialQuadraticSteinScore,
    HTGeometry.halfLineSteinScore, thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative, thetaCuspDilationSteinField,
    thetaCuspDilationSteinFieldDerivative, thetaCuspQuadraticSteinField,
    thetaCuspQuadraticSteinFieldDerivative]
  ring

/-- The old quadratic channel is the coefficient pair `(1,-1/2)`. -/
theorem thetaCuspFirstRadialTwoChannelSteinScore_one_negHalf
    (x : ℝ) :
    thetaCuspFirstRadialTwoChannelSteinScore 1 (-1 / 2) x =
      thetaCuspFirstRadialQuadraticSteinScore x := by
  rw [thetaCuspFirstRadialTwoChannelSteinScore_eq]
  ring

/-- Polynomial--Morse envelope for the dilation score. -/
theorem thetaCuspFirstRadialDilationSteinScore_sq_le
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialDilationSteinScore x ^ 2 ≤
      2 * x ^ 2 * thetaCuspMorseScale 1 x ^ 2 +
        2 * thetaCuspMorseScale 1 x ^ 2 := by
  let t := thetaCuspMorseScale 1 x
  have ht : 3 < t := by
    dsimp [t, thetaCuspMorseScale]
    have hexp : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
    have hexpSq : 1 < Real.exp x ^ 2 := by
      nlinarith [sq_nonneg (Real.exp x - 1)]
    have hmul : Real.pi ≤ Real.pi * Real.exp x ^ 2 :=
      le_mul_of_one_le_right Real.pi_pos.le hexpSq.le
    simpa only [Nat.cast_one, one_mul] using Real.pi_gt_three.trans_le hmul
  have hq : 1 ≤ t - 3 / 2 := by linarith
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.le
  have hq0 : 0 ≤ t - 3 / 2 := le_trans (by norm_num) hq
  have hdiv0 : 0 ≤ t / (t - 3 / 2) := div_nonneg ht0 hq0
  have hdiv_le : t / (t - 3 / 2) ≤ t := div_le_self ht0 hq
  have hWform : thetaCuspBornWittenSuperpotential 1 x =
      t - 5 / 4 - t / (t - 3 / 2) := by
    simp only [thetaCuspBornWittenSuperpotential,
      thetaCuspMorseSuperpotential, thetaCuspBornWittenWeight_eq]
    rfl
  have hWabs : |thetaCuspBornWittenSuperpotential 1 x| ≤ t := by
    rw [hWform]
    apply (abs_le).2
    constructor <;> nlinarith
  have hscoreAbs : |thetaCuspFirstRadialDilationSteinScore x| ≤ x * t + t := by
    rw [thetaCuspFirstRadialDilationSteinScore_eq hx]
    calc
      |x * thetaCuspBornWittenSuperpotential 1 x - 3 / 2| ≤
      |x * thetaCuspBornWittenSuperpotential 1 x| + |(3 / 2 : ℝ)| :=
        abs_sub _ _
      _ = x * |thetaCuspBornWittenSuperpotential 1 x| + 3 / 2 := by
        rw [abs_mul, show |x| = x from abs_of_pos hx,
          show |(3 / 2 : ℝ)| = 3 / 2 by norm_num]
      _ ≤ x * t + t := by
        exact add_le_add (mul_le_mul_of_nonneg_left hWabs hx.le) (by linarith)
  have hnonneg : 0 ≤ x * t + t := by positivity
  have hsq : thetaCuspFirstRadialDilationSteinScore x ^ 2 ≤
      (x * t + t) ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg hnonneg] using hscoreAbs
  have htwo : (x * t + t) ^ 2 ≤ 2 * x ^ 2 * t ^ 2 + 2 * t ^ 2 := by
    nlinarith [sq_nonneg (x * t - t)]
  exact hsq.trans (by simpa only [t] using htwo)

/-- Explicit integrable envelope for the dilation-generator density. -/
def thetaCuspFirstRadialDilationSteinEnergyMajorant (x : ℝ) : ℝ :=
  Real.pi⁻¹ *
    (2 * (x ^ 4 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1) +
      2 * (x ^ 2 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1))

theorem integrableOn_thetaCuspFirstRadialDilationSteinEnergyMajorant :
    IntegrableOn thetaCuspFirstRadialDilationSteinEnergyMajorant (Ioi 0) := by
  have h4 := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 4
  have h2 := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 2
  have h := (h4.const_mul 2).add (h2.const_mul 2)
  have hscaled := h.const_mul Real.pi⁻¹
  apply hscaled.congr
  filter_upwards [] with x
  simp only [thetaCuspFirstRadialDilationSteinEnergyMajorant, Pi.add_apply]

theorem measurable_thetaCuspFirstRadialDilationSteinScore :
    Measurable thetaCuspFirstRadialDilationSteinScore := by
  unfold thetaCuspFirstRadialDilationSteinScore HTGeometry.halfLineSteinScore
    thetaCuspDilationSteinField thetaCuspDilationSteinFieldDerivative
    thetaCuspBornWittenRadialSuperpotential thetaCuspBornWittenSuperpotential
    thetaCuspMorseSuperpotential thetaCuspMorseScale thetaCuspBornWittenWeight
  fun_prop

theorem measurable_thetaCuspFirstRadialTwoChannelSteinScore (a b : ℝ) :
    Measurable (thetaCuspFirstRadialTwoChannelSteinScore a b) := by
  rw [show thetaCuspFirstRadialTwoChannelSteinScore a b = fun x =>
      (a + 2 * b) * thetaCuspFirstRadialDilationSteinScore x -
        2 * b * thetaCuspFirstRadialQuadraticSteinScore x by
    funext x
    exact thetaCuspFirstRadialTwoChannelSteinScore_eq a b x]
  exact (measurable_thetaCuspFirstRadialDilationSteinScore.const_mul _).sub
    (measurable_thetaCuspFirstRadialQuadraticSteinScore.const_mul _)

theorem thetaCuspFirstRadialDilationSteinEnergy_integrand_le_majorant
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialDilationSteinScore x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 ≤
      thetaCuspFirstRadialDilationSteinEnergyMajorant x := by
  have hscore := thetaCuspFirstRadialDilationSteinScore_sq_le hx
  have hmul := mul_le_mul_of_nonneg_right hscore
    (sq_nonneg (thetaCuspBornWittenRadialAmplitude 1 1 x))
  rw [thetaCuspBornWittenRadialAmplitude_sq] at hmul ⊢
  norm_num only [Nat.reduceMul] at hmul ⊢
  have hsource := thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    (n := 1) (by norm_num) hx.le
  have hamp : thetaCuspBornWittenAmplitude 1 x ^ 2 =
      Real.pi⁻¹ * thetaCuspSourceTerm x 1 := by
    field_simp [Real.pi_ne_zero]
    nlinarith
  rw [hamp] at hmul ⊢
  dsimp [thetaCuspFirstRadialDilationSteinEnergyMajorant]
  convert hmul using 1
  all_goals first | rfl | ring

/-- The dilation channel has finite energy with no new source assumption. -/
theorem integrableOn_thetaCuspFirstRadialDilationSteinEnergy :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialDilationSteinScore x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  apply Integrable.mono'
    integrableOn_thetaCuspFirstRadialDilationSteinEnergyMajorant
  · exact ((measurable_thetaCuspFirstRadialDilationSteinScore.pow_const 2).mul
      (measurable_thetaCuspFirstRadialAmplitude.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact thetaCuspFirstRadialDilationSteinEnergy_integrand_le_majorant hx

/-- Every generator in the two-channel span has finite score energy. -/
theorem integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy (a b : ℝ) :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialTwoChannelSteinScore a b x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let amp : ℝ → ℝ := thetaCuspBornWittenRadialAmplitude 1 1
  let d : ℝ → ℝ := fun x => thetaCuspFirstRadialDilationSteinScore x * amp x
  let q : ℝ → ℝ := fun x => thetaCuspFirstRadialQuadraticSteinScore x * amp x
  have hdMeas : AEStronglyMeasurable d μ :=
    (measurable_thetaCuspFirstRadialDilationSteinScore.mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hqMeas : AEStronglyMeasurable q μ :=
    (measurable_thetaCuspFirstRadialQuadraticSteinScore.mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hdSq : Integrable (fun x => d x ^ 2) μ := by
    apply integrableOn_thetaCuspFirstRadialDilationSteinEnergy.congr
    filter_upwards [] with x
    simp only [d, amp]
    ring
  have hqSq : Integrable (fun x => q x ^ 2) μ := by
    apply integrableOn_thetaCuspFirstRadialQuadraticSteinEnergy.congr
    filter_upwards [] with x
    simp only [q, amp]
    ring
  have hdLp : MemLp d 2 μ := (memLp_two_iff_integrable_sq hdMeas).2 hdSq
  have hqLp : MemLp q 2 μ := (memLp_two_iff_integrable_sq hqMeas).2 hqSq
  have hcomb := (hdLp.const_mul (a + 2 * b)).add (hqLp.const_mul (-2 * b))
  have hscoreLp : MemLp (fun x =>
      thetaCuspFirstRadialTwoChannelSteinScore a b x * amp x) 2 μ := by
    convert hcomb using 1
    funext x
    simp only [Pi.add_apply, d, q]
    rw [thetaCuspFirstRadialTwoChannelSteinScore_eq]
    ring
  apply hscoreLp.integrable_sq.congr
  filter_upwards [] with x
  simp only [amp]
  ring

/-- The response coupling is a finite linear combination of radial power
moments, including the odd third moment exposed by the second channel. -/
theorem thetaCuspFirstRadialTwoChannelSteinCoupling_eq_moments (a b : ℝ) :
    thetaCuspFirstRadialTwoChannelSteinCoupling a b =
      a * thetaCuspBornWittenRadialPowerMoment 2 1 1 +
        b * thetaCuspBornWittenRadialPowerMoment 3 1 1 := by
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 1 (n := 1) (by norm_num)
  have h3 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    3 1 (n := 1) (by norm_num)
  rw [thetaCuspFirstRadialTwoChannelSteinCoupling,
    show (fun x : ℝ => (a * x ^ 2 + b * x ^ 3) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      fun x => a * (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) +
        b * (x ^ 3 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) by
      funext x
      ring,
    integral_add (h2.const_mul a) (h3.const_mul b),
    integral_const_mul, integral_const_mul]
  rfl

/-- Derivative of every two-channel polynomial generator. -/
theorem hasDerivAt_thetaCuspTwoChannelSteinField (a b x : ℝ) :
    HasDerivAt (thetaCuspTwoChannelSteinField a b)
      (thetaCuspTwoChannelSteinFieldDerivative a b x) x := by
  unfold thetaCuspTwoChannelSteinField thetaCuspTwoChannelSteinFieldDerivative
  refine (((hasDerivAt_id x).const_mul a).add
    (((hasDerivAt_id x).pow 2).const_mul b)).congr_deriv ?_
  simp only [id_eq]
  ring

/-- The two-channel Stein boundary current vanishes at the Dirichlet endpoint. -/
theorem thetaCuspFirstRadialTwoChannelSteinCurrent_tendsto_zero (a b : ℝ) :
    Tendsto (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspTwoChannelSteinField a b x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspTwoChannelSteinField a b x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) := by
    unfold thetaCuspFirstRadialCenteredQuadratic thetaCuspTwoChannelSteinField
      thetaCuspBornWittenRadialAmplitude thetaCuspBornWittenAmplitude
      thetaCuspBornWittenWeight thetaCuspMorseSuperpotential
      thetaCuspMorseScale thetaCuspMorseGroundState thetaCuspMorseZeroMode
    fun_prop
  have h := (hcont.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hzero : thetaCuspFirstRadialCenteredQuadratic 0 *
      thetaCuspTwoChannelSteinField a b 0 *
        thetaCuspBornWittenRadialAmplitude 1 1 0 ^ 2 = 0 := by
    simp [thetaCuspTwoChannelSteinField]
  rw [hzero] at h
  exact h

/-- The same polynomial boundary current vanishes at infinity. -/
theorem thetaCuspFirstRadialTwoChannelSteinCurrent_tendsto_atTop_zero
    (a b : ℝ) :
    Tendsto (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspTwoChannelSteinField a b x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      atTop (𝓝 0) := by
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  have hpow (m : ℕ) : Tendsto
      (fun x : ℝ => x ^ m * thetaCuspSourceTerm x 1) atTop (𝓝 0) := by
    have h := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      m thetaCuspSeedPolynomial (n := 1) (by norm_num)
    simpa only [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1)] using h
  have hcomb : Tendsto (fun x : ℝ =>
      Real.pi⁻¹ * (J0 * a * (x ^ 5 * thetaCuspSourceTerm x 1) +
        J0 * b * (x ^ 6 * thetaCuspSourceTerm x 1) -
        J1 * a * (x ^ 3 * thetaCuspSourceTerm x 1) -
        J1 * b * (x ^ 4 * thetaCuspSourceTerm x 1))) atTop (𝓝 0) := by
    have h := ((((((hpow 5).const_mul (J0 * a)).add
      ((hpow 6).const_mul (J0 * b))).sub
        ((hpow 3).const_mul (J1 * a))).sub
          ((hpow 4).const_mul (J1 * b))).const_mul Real.pi⁻¹)
    simpa using h
  apply hcomb.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hsource := thetaCusp_pow_mul_sourceTerm_eq_pi_mul_radialAmplitude_sq
    1 (n := 1) (by norm_num) hx
  simp only [thetaCuspFirstRadialCenteredQuadratic,
    thetaCuspTwoChannelSteinField, J0, J1]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hsource ⊢
  rw [← hsource]
  ring

/-- Exact Stein response of every generator in the two-channel family. -/
theorem integral_thetaCuspFirstRadialCentered_mul_twoChannelSteinScore
    (a b : ℝ) :
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspFirstRadialTwoChannelSteinScore a b x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling a b := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let amp : ℝ → ℝ := thetaCuspBornWittenRadialAmplitude 1 1
  let f : ℝ → ℝ := thetaCuspFirstRadialCenteredQuadratic
  let score : ℝ → ℝ := thetaCuspFirstRadialTwoChannelSteinScore a b
  have hfSq : Integrable (fun x => (f x * amp x) ^ 2) μ := by
    apply integrableOn_thetaCuspFirstRadialCenteredQuadratic_sq.congr
    filter_upwards [] with x
    simp only [f, amp]
    ring
  have hgSq : Integrable (fun x => (score x * amp x) ^ 2) μ := by
    apply (integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy a b).congr
    filter_upwards [] with x
    simp only [score, amp]
    ring
  have hfMeas : AEStronglyMeasurable (fun x => f x * amp x) μ := by
    exact (((by
      unfold f thetaCuspFirstRadialCenteredQuadratic
      fun_prop : Continuous f)).measurable.mul
        measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable (fun x => score x * amp x) μ := by
    exact ((measurable_thetaCuspFirstRadialTwoChannelSteinScore a b).mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hfLp : MemLp (fun x => f x * amp x) 2 μ :=
    (memLp_two_iff_integrable_sq hfMeas).2 hfSq
  have hgLp : MemLp (fun x => score x * amp x) 2 μ :=
    (memLp_two_iff_integrable_sq hgMeas).2 hgSq
  have hprod := hfLp.integrable_mul hgLp
  have hleft : IntegrableOn (fun x : ℝ =>
      f x * score x * amp x ^ 2) (Ioi 0) := by
    apply hprod.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    ring
  have hright : IntegrableOn (fun x : ℝ =>
      (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x) *
        thetaCuspTwoChannelSteinField a b x * amp x ^ 2) (Ioi 0) := by
    have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      2 1 (n := 1) (by norm_num)
    have h3 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      3 1 (n := 1) (by norm_num)
    have hcomb := (h2.const_mul
      (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * a)).add
      (h3.const_mul
        (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * b))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [amp, thetaCuspTwoChannelSteinField, Pi.add_apply]
    ring
  have hstein := HTGeometry.integral_Ioi_mul_halfLineSteinScore
    (f := f)
    (f' := fun x => 2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x)
    (P := thetaCuspTwoChannelSteinField a b)
    (P' := thetaCuspTwoChannelSteinFieldDerivative a b)
    (ρ := fun x => amp x ^ 2)
    (W := thetaCuspBornWittenRadialSuperpotential 1 1)
    (fun x _ => by
      unfold f thetaCuspFirstRadialCenteredQuadratic
      refine ((((hasDerivAt_id x).pow 2 |>.const_mul
        (thetaCuspBornWittenRadialPowerMoment 0 1 1)).sub_const
          (thetaCuspBornWittenRadialPowerMoment 2 1 1))).congr_deriv ?_
      simp only [id_eq]
      ring)
    (fun x _ => hasDerivAt_thetaCuspTwoChannelSteinField a b x)
    (fun x hx => by
      simpa only [amp] using hasDerivAt_thetaCuspFirstRadialDensity hx)
    (by simpa only [f, score, amp,
      thetaCuspFirstRadialTwoChannelSteinScore] using hleft)
    (by simpa only [amp] using hright)
    (by simpa only [f, amp] using
      thetaCuspFirstRadialTwoChannelSteinCurrent_tendsto_zero a b)
    (by simpa only [f, amp] using
      thetaCuspFirstRadialTwoChannelSteinCurrent_tendsto_atTop_zero a b)
  rw [show (fun x : ℝ =>
      (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x) *
        thetaCuspTwoChannelSteinField a b x * amp x ^ 2) =
      fun x => 2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        ((a * x ^ 2 + b * x ^ 3) * amp x ^ 2) by
      funext x
      simp only [thetaCuspTwoChannelSteinField]
      ring, integral_const_mul] at hstein
  rw [thetaCuspFirstRadialTwoChannelSteinCoupling]
  dsimp [f, score, amp] at hstein
  simpa only [thetaCuspFirstRadialTwoChannelSteinScore] using hstein.trans (by ring)

/-- Robertson uncertainty holds uniformly over the complete two-channel
generator span. -/
theorem thetaCuspFirstRadialTwoChannelSteinRobertson (a b : ℝ) :
    (thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling a b) ^ 2 ≤
      (thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
          thetaCuspBornWittenRadialPowerMoment 4 1 1 -
        thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2) *
        thetaCuspFirstRadialTwoChannelSteinEnergy a b := by
  refine thetaCuspFirstRadialSteinRobertson_of_score
    (measurable_thetaCuspFirstRadialTwoChannelSteinScore a b) ?_
    (integral_thetaCuspFirstRadialCentered_mul_twoChannelSteinScore a b) ?_
  · exact integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy a b
  · rw [thetaCuspFirstRadialTwoChannelSteinEnergy]

/-- Source-specific three-vector Gram determinant.  Unlike a fixed-field
Robertson estimate, this relation retains the mixed energy and both response
channels, so the generator coefficients can be optimized algebraically. -/
theorem thetaCuspFirstRadialTwoChannelRobertsonGram :
    (thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling 1 0) ^ 2 *
          thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 -
      2 * (thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspFirstRadialTwoChannelSteinCoupling 1 0) *
        (thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspFirstRadialTwoChannelSteinCoupling 0 1) *
        thetaCuspFirstRadialTwoChannelSteinCrossEnergy +
      (thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspFirstRadialTwoChannelSteinCoupling 0 1) ^ 2 *
        thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 ≤
    (thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
        thetaCuspBornWittenRadialPowerMoment 4 1 1 -
      thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2) *
      (thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 *
          thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 -
        thetaCuspFirstRadialTwoChannelSteinCrossEnergy ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let amp : ℝ → ℝ := thetaCuspBornWittenRadialAmplitude 1 1
  let f : ℝ → ℝ := fun x => thetaCuspFirstRadialCenteredQuadratic x * amp x
  let g : ℝ → ℝ := fun x => thetaCuspFirstRadialTwoChannelSteinScore 1 0 x * amp x
  let h : ℝ → ℝ := fun x => thetaCuspFirstRadialTwoChannelSteinScore 0 1 x * amp x
  have hfMeas : AEStronglyMeasurable f μ := by
    exact (((by
      unfold thetaCuspFirstRadialCenteredQuadratic
      fun_prop : Continuous thetaCuspFirstRadialCenteredQuadratic)).measurable.mul
        measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g μ := by
    exact ((measurable_thetaCuspFirstRadialTwoChannelSteinScore 1 0).mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hhMeas : AEStronglyMeasurable h μ := by
    exact ((measurable_thetaCuspFirstRadialTwoChannelSteinScore 0 1).mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hfSq : Integrable (fun x => f x ^ 2) μ := by
    apply integrableOn_thetaCuspFirstRadialCenteredQuadratic_sq.congr
    filter_upwards [] with x
    simp only [f, amp]
    ring
  have hgSq : Integrable (fun x => g x ^ 2) μ := by
    apply (integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy 1 0).congr
    filter_upwards [] with x
    simp only [g, amp]
    ring
  have hhSq : Integrable (fun x => h x ^ 2) μ := by
    apply (integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy 0 1).congr
    filter_upwards [] with x
    simp only [h, amp]
    ring
  have hfLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfMeas).2 hfSq
  have hgLp : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgMeas).2 hgSq
  have hhLp : MemLp h 2 μ := (memLp_two_iff_integrable_sq hhMeas).2 hhSq
  have hgram := HTGeometry.twoChannelIntegralRobertson hfLp hgLp hhLp
  have hfg : (∫ x, f x * g x ∂μ) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling 1 0 := by
    rw [show (fun x => f x * g x) = fun x =>
        thetaCuspFirstRadialCenteredQuadratic x *
          thetaCuspFirstRadialTwoChannelSteinScore 1 0 x * amp x ^ 2 by
      funext x
      simp only [f, g]
      ring]
    exact integral_thetaCuspFirstRadialCentered_mul_twoChannelSteinScore 1 0
  have hfh : (∫ x, f x * h x ∂μ) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling 0 1 := by
    rw [show (fun x => f x * h x) = fun x =>
        thetaCuspFirstRadialCenteredQuadratic x *
          thetaCuspFirstRadialTwoChannelSteinScore 0 1 x * amp x ^ 2 by
      funext x
      simp only [f, h]
      ring]
    exact integral_thetaCuspFirstRadialCentered_mul_twoChannelSteinScore 0 1
  have hff : (∫ x, f x ^ 2 ∂μ) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
          thetaCuspBornWittenRadialPowerMoment 4 1 1 -
        thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 := by
    rw [show (fun x => f x ^ 2) = fun x =>
        thetaCuspFirstRadialCenteredQuadratic x ^ 2 * amp x ^ 2 by
      funext x
      simp only [f]
      ring]
    exact integral_thetaCuspFirstRadialCenteredQuadratic_sq
  have hgg : (∫ x, g x ^ 2 ∂μ) =
      thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 := by
    rw [thetaCuspFirstRadialTwoChannelSteinEnergy]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, amp]
    ring
  have hhh : (∫ x, h x ^ 2 ∂μ) =
      thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 := by
    rw [thetaCuspFirstRadialTwoChannelSteinEnergy]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [h, amp]
    ring
  have hgh : (∫ x, g x * h x ∂μ) =
      thetaCuspFirstRadialTwoChannelSteinCrossEnergy := by
    rw [thetaCuspFirstRadialTwoChannelSteinCrossEnergy]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, h, amp]
    ring
  rwa [hfg, hfh, hff, hgg, hhh, hgh] at hgram

/-- Variational two-channel source certificate.  Only one nonzero generator in
the span must meet the energy-response inequality. -/
def ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate : Prop :=
  ∃ a b : ℝ,
    0 < thetaCuspFirstRadialTwoChannelSteinEnergy a b ∧
    (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
            thetaCuspFirstRadialTwoChannelSteinEnergy a b ≤
      9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling a b ^ 2

/-- The previous fixed quadratic certificate is exactly the witness
`(a,b)=(1,-1/2)` for the variational certificate. -/
theorem twoChannelSteinEnergyCertificate_of_quadraticSteinEnergyCertificate
    (hcert : ThetaCuspFirstRadialQuadraticSteinEnergyCertificate) :
    ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate := by
  refine ⟨1, -1 / 2, ?_, ?_⟩
  · rw [thetaCuspFirstRadialTwoChannelSteinEnergy]
    convert thetaCuspFirstRadialQuadraticSteinEnergy_pos using 1
    rw [thetaCuspFirstRadialQuadraticSteinEnergy]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [thetaCuspFirstRadialTwoChannelSteinScore_one_negHalf]
  · have hcoupling : thetaCuspFirstRadialTwoChannelSteinCoupling 1 (-1 / 2) =
        thetaCuspFirstRadialQuadraticSteinCoupling := by
      rw [thetaCuspFirstRadialTwoChannelSteinCoupling,
        thetaCuspFirstRadialQuadraticSteinCoupling]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    have henergy : thetaCuspFirstRadialTwoChannelSteinEnergy 1 (-1 / 2) =
        thetaCuspFirstRadialQuadraticSteinEnergy := by
      rw [thetaCuspFirstRadialTwoChannelSteinEnergy,
        thetaCuspFirstRadialQuadraticSteinEnergy]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [thetaCuspFirstRadialTwoChannelSteinScore_one_negHalf]
    simp only [ThetaCuspFirstRadialQuadraticSteinEnergyCertificate] at hcert
    simpa only [henergy, hcoupling] using hcert

/-- The weaker variational certificate discharges the same open upper
first-radial moment inequality. -/
theorem thetaCusp_firstRadial_upper_of_twoChannelSteinEnergyCertificate
    (hcert : ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 := by
  rcases hcert with ⟨a, b, hE, hcert⟩
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  let J2 := thetaCuspBornWittenRadialPowerMoment 4 1 1
  let C := thetaCuspFirstRadialTwoChannelSteinCoupling a b
  let E := thetaCuspFirstRadialTwoChannelSteinEnergy a b
  let c := 14 * (3005 / 2997 : ℝ) ^ 2 - 9
  have hJ0 : 0 < J0 := thetaCuspFirstRadialPowerMoment_zero_pos
  have hunc := thetaCuspFirstRadialTwoChannelSteinRobertson a b
  have huncFactor : J0 * (J0 * C ^ 2) ≤
      J0 * ((J0 * J2 - J1 ^ 2) * E) := by
    dsimp [J0, J1, J2, C, E] at hunc ⊢
    convert hunc using 1 <;> ring
  have hunc' : J0 * C ^ 2 ≤ (J0 * J2 - J1 ^ 2) * E :=
    (mul_le_mul_iff_of_pos_left hJ0).mp huncFactor
  have hEnergy' : c * J1 ^ 2 * E ≤ 9 * J0 * C ^ 2 := by
    simpa only [c, J0, J1, C, E] using hcert
  have hchain : c * J1 ^ 2 * E ≤ 9 * ((J0 * J2 - J1 ^ 2) * E) := by
    calc
      c * J1 ^ 2 * E ≤ 9 * (J0 * C ^ 2) := by
        simpa only [mul_assoc] using hEnergy'
      _ ≤ 9 * ((J0 * J2 - J1 ^ 2) * E) :=
        mul_le_mul_of_nonneg_left hunc' (by norm_num : (0 : ℝ) ≤ 9)
  have hcore : c * J1 ^ 2 ≤ 9 * (J0 * J2 - J1 ^ 2) := by
    have hfactor : E * (c * J1 ^ 2) ≤
        E * (9 * (J0 * J2 - J1 ^ 2)) := by
      convert hchain using 1 <;> ring
    exact (mul_le_mul_iff_of_pos_left hE).mp hfactor
  rw [← thetaCuspBornWittenRadialPowerMoment_even 0 1 1,
    ← thetaCuspBornWittenRadialPowerMoment_even 1 1 1,
    ← thetaCuspBornWittenRadialPowerMoment_even 2 1 1]
  dsimp [J0, J1, J2, c] at hcore
  norm_num only [Nat.reduceMul] at hcore ⊢
  nlinarith

/-- Direct two-channel interface to the existing linear prime--archimedean
Hankel consumer. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelSteinEnergy
    (hcert : ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude
    (thetaCusp_firstRadial_upper_of_twoChannelSteinEnergyCertificate hcert) hrelaxed

/-- The variational source certificate discharges the complete omitted
constant/linear block of the integer-polynomial source cone. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_twoChannelSteinEnergy_of_degreeTwoTail
    (hcert : ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  by_cases hp : 2 ≤ p.natDegree
  · exact htail p hp
  · have hdeg : p.natDegree ≤ 1 := by omega
    have hdegree : p.degree ≤ 1 :=
      Polynomial.natDegree_le_iff_degree_le.mp hdeg
    have hpform := Polynomial.eq_X_add_C_of_degree_le_one hdegree
    have hmap := congrArg (Polynomial.map (Int.castRingHom ℝ)) hpform
    have hpoly : p.map (Int.castRingHom ℝ) =
        C ((p.coeff 0 : ℤ) : ℝ) + C ((p.coeff 1 : ℤ) : ℝ) * X := by
      simpa [add_comm] using hmap
    rw [hpoly]
    exact forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelSteinEnergy
      hcert hrelaxed _ _

/-- Direct RH interface: the two-channel source certificate and the unchanged
relaxed theta condition reduce the remaining source cone to integer
polynomials of degree at least two. -/
theorem riemannHypothesis_of_twoChannelSteinEnergy_of_primeArchDegreeTwoTail
    (hcert : ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_twoChannelSteinEnergy_of_degreeTwoTail
      hcert hrelaxed htail)

end

end RHTower
