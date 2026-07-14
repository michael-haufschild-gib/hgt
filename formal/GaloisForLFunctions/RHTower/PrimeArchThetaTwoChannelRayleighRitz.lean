import GaloisForLFunctions.HTGeometry.TwoChannelRayleighRitz
import GaloisForLFunctions.RHTower.PrimeArchThetaTwoChannelSteinRobertson

/-!
# Rayleigh--Ritz matrix reduction of the theta two-channel certificate

The two score channels form a nonorthogonal Rayleigh--Ritz basis.  Their
energy matrix is strictly positive definite, so applying its adjugate to the
finite response vector removes the existential generator coefficients from
the two-channel Stein certificate.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- On the positive half-line the radial singularity cancels from every
two-channel score. -/
theorem thetaCuspFirstRadialTwoChannelSteinScore_eq_born
    (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialTwoChannelSteinScore a b x =
      thetaCuspTwoChannelSteinField a b x *
          thetaCuspBornWittenSuperpotential 1 x -
        3 * a / 2 - 2 * b * x := by
  simp only [thetaCuspFirstRadialTwoChannelSteinScore,
    HTGeometry.halfLineSteinScore, thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative,
    thetaCuspBornWittenRadialSuperpotential]
  field_simp [hx.ne']
  ring

/-- Exact decomposition in the dilation and quadratic-monomial score basis. -/
theorem thetaCuspFirstRadialTwoChannelSteinScore_eq_basis
    (a b x : ℝ) :
    thetaCuspFirstRadialTwoChannelSteinScore a b x =
      a * thetaCuspFirstRadialTwoChannelSteinScore 1 0 x +
        b * thetaCuspFirstRadialTwoChannelSteinScore 0 1 x := by
  simp only [thetaCuspFirstRadialTwoChannelSteinScore,
    HTGeometry.halfLineSteinScore, thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative]
  ring

/-- The mixed score-energy entry is integrable. -/
theorem integrableOn_thetaCuspFirstRadialTwoChannelSteinCrossEnergy :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialTwoChannelSteinScore 1 0 x *
        thetaCuspFirstRadialTwoChannelSteinScore 0 1 x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let amp : ℝ → ℝ := thetaCuspBornWittenRadialAmplitude 1 1
  let g : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialTwoChannelSteinScore 1 0 x * amp x
  let h : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialTwoChannelSteinScore 0 1 x * amp x
  have hgMeas : AEStronglyMeasurable g μ :=
    ((measurable_thetaCuspFirstRadialTwoChannelSteinScore 1 0).mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hhMeas : AEStronglyMeasurable h μ :=
    ((measurable_thetaCuspFirstRadialTwoChannelSteinScore 0 1).mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
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
  have hgLp : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgMeas).2 hgSq
  have hhLp : MemLp h 2 μ := (memLp_two_iff_integrable_sq hhMeas).2 hhSq
  apply (hgLp.integrable_mul hhLp).congr
  filter_upwards [] with x
  simp only [Pi.mul_apply, g, h, amp]
  ring

/-- Exact Rayleigh--Ritz quadratic form of the two-channel score energy. -/
theorem thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic
    (a b : ℝ) :
    thetaCuspFirstRadialTwoChannelSteinEnergy a b =
      a ^ 2 * thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 +
        2 * a * b * thetaCuspFirstRadialTwoChannelSteinCrossEnergy +
          b ^ 2 * thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 := by
  have hA := integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
  have hB := integrableOn_thetaCuspFirstRadialTwoChannelSteinCrossEnergy
  have hD := integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
  rw [thetaCuspFirstRadialTwoChannelSteinEnergy]
  have hpoint : (fun x : ℝ =>
      thetaCuspFirstRadialTwoChannelSteinScore a b x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      fun x =>
        a ^ 2 * (thetaCuspFirstRadialTwoChannelSteinScore 1 0 x ^ 2 *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) +
        2 * a * b * (thetaCuspFirstRadialTwoChannelSteinScore 1 0 x *
          thetaCuspFirstRadialTwoChannelSteinScore 0 1 x *
            thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) +
        b ^ 2 * (thetaCuspFirstRadialTwoChannelSteinScore 0 1 x ^ 2 *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) := by
    funext x
    rw [thetaCuspFirstRadialTwoChannelSteinScore_eq_basis]
    ring
  rw [hpoint]
  change (∫ x : ℝ,
      (a ^ 2 * (thetaCuspFirstRadialTwoChannelSteinScore 1 0 x ^ 2 *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) +
        2 * a * b * (thetaCuspFirstRadialTwoChannelSteinScore 1 0 x *
          thetaCuspFirstRadialTwoChannelSteinScore 0 1 x *
            thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) +
      b ^ 2 * (thetaCuspFirstRadialTwoChannelSteinScore 0 1 x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      ∂volume.restrict (Ioi 0)) = _
  have hsplit1 := integral_add
    ((hA.const_mul (a ^ 2)).add (hB.const_mul (2 * a * b)))
    (hD.const_mul (b ^ 2))
  have hsplit2 := integral_add
    (hA.const_mul (a ^ 2)) (hB.const_mul (2 * a * b))
  simp only [Pi.add_apply] at hsplit1 hsplit2
  rw [hsplit1, hsplit2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    thetaCuspFirstRadialTwoChannelSteinEnergy,
    thetaCuspFirstRadialTwoChannelSteinEnergy,
    thetaCuspFirstRadialTwoChannelSteinCrossEnergy]

/-- The endpoint value of a two-channel score records its dilation
coefficient. -/
theorem thetaCuspFirstRadialTwoChannelSteinScore_tendsto_zero
    (a b : ℝ) :
    Tendsto (thetaCuspFirstRadialTwoChannelSteinScore a b)
      (𝓝[>] 0) (𝓝 (-(3 * a / 2))) := by
  let g : ℝ → ℝ := fun x =>
    thetaCuspTwoChannelSteinField a b x *
        thetaCuspBornWittenSuperpotential 1 x -
      3 * a / 2 - 2 * b * x
  have hBcont : ContinuousAt (thetaCuspBornWittenSuperpotential 1) 0 :=
    (hasDerivAt_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hgcont : ContinuousAt g 0 := by
    dsimp only [g, thetaCuspTwoChannelSteinField]
    fun_prop
  have hgt : Tendsto g (𝓝[>] 0) (𝓝 (-(3 * a / 2))) := by
    have h := hgcont.tendsto.mono_left
      (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hg0 : g 0 = -(3 * a / 2) := by
      dsimp [g, thetaCuspTwoChannelSteinField]
      ring
    rw [hg0] at h
    exact h
  apply Tendsto.congr' _ hgt
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (thetaCuspFirstRadialTwoChannelSteinScore_eq_born a b hx).symm

/-- One nonzero point makes the corresponding finite score energy strictly
positive. -/
theorem thetaCuspFirstRadialTwoChannelSteinEnergy_pos_of_score_ne
    {a b p : ℝ} (hp : 0 < p)
    (hscore : thetaCuspFirstRadialTwoChannelSteinScore a b p ≠ 0) :
    0 < thetaCuspFirstRadialTwoChannelSteinEnergy a b := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let e : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialTwoChannelSteinScore a b x ^ 2 *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2
  have hInt : Integrable e μ := by
    exact (integrableOn_thetaCuspFirstRadialTwoChannelSteinEnergy a b).congr
      (Eventually.of_forall fun _ => rfl)
  have hamp : 0 < thetaCuspBornWittenRadialAmplitude 1 1 p :=
    thetaCuspBornWittenRadialAmplitude_pos
      (k := 1) (n := 1) (by norm_num) hp
  have hep : 0 < e p := by
    dsimp [e]
    exact mul_pos (sq_pos_of_ne_zero hscore) (sq_pos_of_pos hamp)
  have hWcont : ContinuousAt
      (thetaCuspBornWittenRadialSuperpotential 1 1) p :=
    (hasDerivAt_thetaCuspBornWittenRadialSuperpotential
      (k := 1) (n := 1) (by norm_num) hp).continuousAt
  have hampcont : ContinuousAt
      (thetaCuspBornWittenRadialAmplitude 1 1) p :=
    (hasDerivAt_thetaCuspBornWittenRadialAmplitude
      (k := 1) (n := 1) (by norm_num) hp).continuousAt
  have hscorecont : ContinuousAt
      (thetaCuspFirstRadialTwoChannelSteinScore a b) p := by
    unfold thetaCuspFirstRadialTwoChannelSteinScore
      HTGeometry.halfLineSteinScore thetaCuspTwoChannelSteinField
      thetaCuspTwoChannelSteinFieldDerivative
    fun_prop
  have hecont : ContinuousAt e p := by
    dsimp [e]
    exact (hscorecont.pow 2).mul (hampcont.pow 2)
  have hne : ∀ᶠ x in 𝓝 p, e x ≠ 0 := hecont.eventually_ne hep.ne'
  have hposmem : Function.support e ∩ Ioi (0 : ℝ) ∈ 𝓝 p := by
    filter_upwards [hne, Ioi_mem_nhds hp] with x hx hxi
    exact ⟨Function.mem_support.mpr hx, hxi⟩
  have hvolpos : 0 < volume (Function.support e ∩ Ioi (0 : ℝ)) :=
    Measure.measure_pos_of_mem_nhds volume hposmem
  have heMeas : Measurable e := by
    exact (((measurable_thetaCuspFirstRadialTwoChannelSteinScore a b).pow_const 2).mul
      (measurable_thetaCuspFirstRadialAmplitude.pow_const 2))
  have hsupppos : 0 < μ (Function.support e) := by
    change 0 < (volume.restrict (Ioi (0 : ℝ))) (Function.support e)
    rw [Measure.restrict_apply (measurableSet_support heMeas)]
    exact hvolpos
  have henonneg : 0 ≤ᵐ[μ] e := Eventually.of_forall fun x => by
    dsimp [e]
    positivity
  have hpos := (integral_pos_iff_support_of_nonneg_ae henonneg hInt).2 hsupppos
  rw [thetaCuspFirstRadialTwoChannelSteinEnergy]
  exact hpos

/-- The pure quadratic-monomial score is explicitly nonzero at `x=2`. -/
theorem thetaCuspFirstRadialQuadraticMonomialSteinScore_two_pos :
    0 < thetaCuspFirstRadialTwoChannelSteinScore 0 1 2 := by
  let t := thetaCuspMorseScale 1 2
  have hexp : 3 < Real.exp (2 : ℝ) := by
    have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at h ⊢
    exact h
  have hexpSq : 9 < Real.exp (2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (2 : ℝ) - 3)]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hprod : 0 < (Real.pi - 3) * (Real.exp (2 : ℝ) ^ 2 - 9) :=
    mul_pos (sub_pos.mpr hpi) (sub_pos.mpr hexpSq)
  have ht : 27 < t := by
    dsimp [t, thetaCuspMorseScale]
    norm_num only [Nat.cast_one, one_mul]
    nlinarith
  have hq : 0 < t - 3 / 2 := by linarith
  have hdiv : t / (t - 3 / 2) < 2 := by
    rw [div_lt_iff₀ hq]
    nlinarith
  have hWform : thetaCuspBornWittenSuperpotential 1 2 =
      t - 5 / 4 - t / (t - 3 / 2) := by
    simp only [thetaCuspBornWittenSuperpotential,
      thetaCuspMorseSuperpotential, thetaCuspBornWittenWeight_eq]
    rfl
  have hW : 1 < thetaCuspBornWittenSuperpotential 1 2 := by
    rw [hWform]
    linarith
  simp only [thetaCuspFirstRadialTwoChannelSteinScore,
    HTGeometry.halfLineSteinScore, thetaCuspTwoChannelSteinField,
    thetaCuspTwoChannelSteinFieldDerivative,
    thetaCuspBornWittenRadialSuperpotential]
  norm_num
  nlinarith

/-- The score-energy quadratic form is positive on every nonzero coefficient
pair.  This is the source-specific linear independence required by
nonorthogonal Rayleigh--Ritz. -/
theorem thetaCuspFirstRadialTwoChannelSteinEnergy_pos
    {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < thetaCuspFirstRadialTwoChannelSteinEnergy a b := by
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by
      rcases hab with h | h
      · exact (h rfl).elim
      · exact h
    apply thetaCuspFirstRadialTwoChannelSteinEnergy_pos_of_score_ne
      (p := 2) (by norm_num)
    have heq : thetaCuspFirstRadialTwoChannelSteinScore 0 b 2 =
        b * thetaCuspFirstRadialTwoChannelSteinScore 0 1 2 := by
      simp only [thetaCuspFirstRadialTwoChannelSteinScore,
        HTGeometry.halfLineSteinScore, thetaCuspTwoChannelSteinField,
        thetaCuspTwoChannelSteinFieldDerivative]
      ring
    rw [heq]
    exact mul_ne_zero hb thetaCuspFirstRadialQuadraticMonomialSteinScore_two_pos.ne'
  · have htarget : -(3 * a / 2) ≠ 0 := by
      intro h
      apply ha
      linarith
    have hne : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        thetaCuspFirstRadialTwoChannelSteinScore a b x ≠ 0 :=
      (thetaCuspFirstRadialTwoChannelSteinScore_tendsto_zero a b).eventually_ne htarget
    have hex : ∃ p : ℝ,
        thetaCuspFirstRadialTwoChannelSteinScore a b p ≠ 0 ∧ p ∈ Ioi 0 :=
      (hne.and self_mem_nhdsWithin).exists
    rcases hex with ⟨p, hpne, hp⟩
    exact thetaCuspFirstRadialTwoChannelSteinEnergy_pos_of_score_ne hp hpne

/-- Strict positive definiteness of the two-channel score-energy matrix. -/
theorem thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos :
    0 < thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 *
        thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 -
      thetaCuspFirstRadialTwoChannelSteinCrossEnergy ^ 2 := by
  let A := thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
  let B := thetaCuspFirstRadialTwoChannelSteinCrossEnergy
  let D := thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
  have hA : 0 < A := by
    dsimp [A]
    exact thetaCuspFirstRadialTwoChannelSteinEnergy_pos (Or.inl (by norm_num))
  have hres : 0 < thetaCuspFirstRadialTwoChannelSteinEnergy (-B) A :=
    thetaCuspFirstRadialTwoChannelSteinEnergy_pos (Or.inr hA.ne')
  rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic] at hres
  have hfactor :
      (-B) ^ 2 * A + 2 * (-B) * A * B + A ^ 2 * D =
        A * (A * D - B ^ 2) := by ring
  rw [hfactor] at hres
  dsimp [A, B, D] at hres ⊢
  nlinarith

/-- Every first-radial position power moment is strictly positive. -/
theorem thetaCuspFirstRadialPowerMoment_pos (m : ℕ) :
    0 < thetaCuspBornWittenRadialPowerMoment m 1 1 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let e : ℝ → ℝ := fun x =>
    x ^ m * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2
  have hInt : Integrable e μ := by
    exact (integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      m 1 (n := 1) (by norm_num)).congr (Eventually.of_forall fun _ => rfl)
  have hamp : 0 < thetaCuspBornWittenRadialAmplitude 1 1 1 :=
    thetaCuspBornWittenRadialAmplitude_pos
      (k := 1) (n := 1) (by norm_num) (by norm_num)
  have he1 : 0 < e 1 := by
    dsimp [e]
    simpa using sq_pos_of_pos hamp
  have hampcont : ContinuousAt
      (thetaCuspBornWittenRadialAmplitude 1 1) 1 :=
    (hasDerivAt_thetaCuspBornWittenRadialAmplitude
      (k := 1) (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hecont : ContinuousAt e 1 := by
    dsimp [e]
    fun_prop
  have hne : ∀ᶠ x in 𝓝 (1 : ℝ), e x ≠ 0 := hecont.eventually_ne he1.ne'
  have hposmem : Function.support e ∩ Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) := by
    filter_upwards [hne, Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx hxi
    exact ⟨Function.mem_support.mpr hx, hxi⟩
  have hvolpos : 0 < volume (Function.support e ∩ Ioi (0 : ℝ)) :=
    Measure.measure_pos_of_mem_nhds volume hposmem
  have heMeas : Measurable e := by
    exact ((measurable_id.pow_const m).mul
      (measurable_thetaCuspFirstRadialAmplitude.pow_const 2))
  have hsupppos : 0 < μ (Function.support e) := by
    change 0 < (volume.restrict (Ioi (0 : ℝ))) (Function.support e)
    rw [Measure.restrict_apply (measurableSet_support heMeas)]
    exact hvolpos
  have henonneg : 0 ≤ᵐ[μ] e := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [e]
    exact mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)
  have hpos := (integral_pos_iff_support_of_nonneg_ae henonneg hInt).2 hsupppos
  simpa only [thetaCuspBornWittenRadialPowerMoment, e, μ] using hpos

/-- Determinant of the two-channel score-energy matrix. -/
def thetaCuspFirstRadialTwoChannelSteinEnergyDet : ℝ :=
  thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 *
      thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 -
    thetaCuspFirstRadialTwoChannelSteinCrossEnergy ^ 2

/-- Adjugate quadratic value of the two finite response channels. -/
def thetaCuspFirstRadialTwoChannelSteinAdjugateResponse : ℝ :=
  thetaCuspFirstRadialTwoChannelSteinEnergy 0 1 *
        thetaCuspFirstRadialTwoChannelSteinCoupling 1 0 ^ 2 -
      2 * thetaCuspFirstRadialTwoChannelSteinCrossEnergy *
        thetaCuspFirstRadialTwoChannelSteinCoupling 1 0 *
        thetaCuspFirstRadialTwoChannelSteinCoupling 0 1 +
    thetaCuspFirstRadialTwoChannelSteinEnergy 1 0 *
      thetaCuspFirstRadialTwoChannelSteinCoupling 0 1 ^ 2

theorem thetaCuspFirstRadialTwoChannelSteinEnergyDet_pos :
    0 < thetaCuspFirstRadialTwoChannelSteinEnergyDet := by
  simpa only [thetaCuspFirstRadialTwoChannelSteinEnergyDet] using
    thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos

/-- The adjugate response is strictly positive because the energy matrix is
positive definite and the first response moment is positive. -/
theorem thetaCuspFirstRadialTwoChannelSteinAdjugateResponse_pos :
    0 < thetaCuspFirstRadialTwoChannelSteinAdjugateResponse := by
  let A := thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
  let B := thetaCuspFirstRadialTwoChannelSteinCrossEnergy
  let D := thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
  let c₁ := thetaCuspFirstRadialTwoChannelSteinCoupling 1 0
  let c₂ := thetaCuspFirstRadialTwoChannelSteinCoupling 0 1
  let Q := D * c₁ ^ 2 - 2 * B * c₁ * c₂ + A * c₂ ^ 2
  have hA : 0 < A := by
    dsimp [A]
    exact thetaCuspFirstRadialTwoChannelSteinEnergy_pos (Or.inl (by norm_num))
  have hdet : 0 < A * D - B ^ 2 := by
    simpa only [A, B, D] using thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos
  have hc₁ : 0 < c₁ := by
    dsimp [c₁]
    rw [thetaCuspFirstRadialTwoChannelSteinCoupling_eq_moments]
    simpa using thetaCuspFirstRadialPowerMoment_pos 2
  have hid : A * Q =
      (A * c₂ - B * c₁) ^ 2 + (A * D - B ^ 2) * c₁ ^ 2 := by
    dsimp [Q]
    ring
  have hright : 0 <
      (A * c₂ - B * c₁) ^ 2 + (A * D - B ^ 2) * c₁ ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_pos hc₁))
  have hAQ : 0 < A * Q := by rwa [hid]
  have hQ : 0 < Q := by nlinarith
  simpa only [thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
    Q, A, B, D, c₁, c₂] using hQ

/-- Every response in the two-channel span is the same linear combination of
the two basis responses. -/
theorem thetaCuspFirstRadialTwoChannelSteinCoupling_eq_basis
    (a b : ℝ) :
    thetaCuspFirstRadialTwoChannelSteinCoupling a b =
      a * thetaCuspFirstRadialTwoChannelSteinCoupling 1 0 +
        b * thetaCuspFirstRadialTwoChannelSteinCoupling 0 1 := by
  rw [thetaCuspFirstRadialTwoChannelSteinCoupling_eq_moments,
    thetaCuspFirstRadialTwoChannelSteinCoupling_eq_moments,
    thetaCuspFirstRadialTwoChannelSteinCoupling_eq_moments]
  ring

/-- Explicit Rayleigh--Ritz matrix certificate replacing the existential
generator choice. -/
def ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialTwoChannelSteinEnergyDet ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialTwoChannelSteinAdjugateResponse

/-- The explicit matrix certificate supplies the optimal adjugate generator
and hence the variational two-channel certificate. -/
theorem twoChannelSteinEnergyCertificate_of_rayleighRitzCertificate
    (hcert : ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate) :
    ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate := by
  let A := thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
  let B := thetaCuspFirstRadialTwoChannelSteinCrossEnergy
  let D := thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
  let c₁ := thetaCuspFirstRadialTwoChannelSteinCoupling 1 0
  let c₂ := thetaCuspFirstRadialTwoChannelSteinCoupling 0 1
  let κ := (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
    thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2
  let L := 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1
  have hdet : 0 < A * D - B ^ 2 := by
    simpa only [A, B, D] using thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos
  have hresponse : 0 < D * c₁ ^ 2 - 2 * B * c₁ * c₂ + A * c₂ ^ 2 := by
    simpa only [thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
      A, B, D, c₁, c₂] using
        thetaCuspFirstRadialTwoChannelSteinAdjugateResponse_pos
  have hmatrix : κ * (A * D - B ^ 2) ≤
      L * (D * c₁ ^ 2 - 2 * B * c₁ * c₂ + A * c₂ ^ 2) := by
    simpa only [ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate,
      thetaCuspFirstRadialTwoChannelSteinEnergyDet,
      thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
      κ, L, A, B, D, c₁, c₂] using hcert
  rcases HTGeometry.exists_positive_twoChannelRayleighWitness_of_adjugate
    A B D c₁ c₂ κ L hdet hresponse hmatrix with ⟨a, b, hE, hineq⟩
  refine ⟨a, b, ?_, ?_⟩
  · rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic]
    simpa only [A, B, D, mul_comm, mul_left_comm, mul_assoc] using hE
  · rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic,
      thetaCuspFirstRadialTwoChannelSteinCoupling_eq_basis]
    simpa only [κ, L, A, B, D, c₁, c₂, mul_comm, mul_left_comm,
      mul_assoc] using hineq

/-- Conversely, every positive-energy variational witness forces the explicit
Rayleigh--Ritz matrix inequality.  Thus optimizing away the coefficients loses
no information. -/
theorem rayleighRitzCertificate_of_twoChannelSteinEnergyCertificate
    (hcert : ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate) :
    ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate := by
  rcases hcert with ⟨a, b, henergy, hineq⟩
  let A := thetaCuspFirstRadialTwoChannelSteinEnergy 1 0
  let B := thetaCuspFirstRadialTwoChannelSteinCrossEnergy
  let D := thetaCuspFirstRadialTwoChannelSteinEnergy 0 1
  let c₁ := thetaCuspFirstRadialTwoChannelSteinCoupling 1 0
  let c₂ := thetaCuspFirstRadialTwoChannelSteinCoupling 0 1
  let κ := (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
    thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2
  let L := 9 * thetaCuspBornWittenRadialPowerMoment 0 1 1
  have hdet : 0 < A * D - B ^ 2 := by
    simpa only [A, B, D] using
      thetaCuspFirstRadialTwoChannelSteinEnergy_det_pos
  have hL : 0 ≤ L := by
    have hM0 : 0 < thetaCuspBornWittenRadialPowerMoment 0 1 1 :=
      thetaCuspFirstRadialPowerMoment_zero_pos
    dsimp only [L]
    positivity
  have hE : 0 < A * a ^ 2 + 2 * B * a * b + D * b ^ 2 := by
    rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic] at henergy
    simpa only [A, B, D, mul_comm, mul_left_comm, mul_assoc] using henergy
  have hineq' : κ * (A * a ^ 2 + 2 * B * a * b + D * b ^ 2) ≤
      L * (a * c₁ + b * c₂) ^ 2 := by
    rw [thetaCuspFirstRadialTwoChannelSteinEnergy_eq_quadratic,
      thetaCuspFirstRadialTwoChannelSteinCoupling_eq_basis] at hineq
    simpa only [κ, L, A, B, D, c₁, c₂, mul_comm, mul_left_comm,
      mul_assoc] using hineq
  have hmatrix :=
    HTGeometry.twoChannelRayleighMatrixCertificate_of_positiveWitness
      A B D c₁ c₂ κ L a b hdet hL hE hineq'
  simpa only [ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate,
    thetaCuspFirstRadialTwoChannelSteinEnergyDet,
    thetaCuspFirstRadialTwoChannelSteinAdjugateResponse,
    κ, L, A, B, D, c₁, c₂] using hmatrix

/-- Exact elimination of the existential generator coefficients. -/
theorem thetaCuspFirstRadialTwoChannelRayleighRitzCertificate_iff :
    ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate ↔
      ThetaCuspFirstRadialTwoChannelSteinEnergyCertificate :=
  ⟨twoChannelSteinEnergyCertificate_of_rayleighRitzCertificate,
    rayleighRitzCertificate_of_twoChannelSteinEnergyCertificate⟩

/-- Direct first-radial consumer of the explicit matrix certificate. -/
theorem thetaCusp_firstRadial_upper_of_twoChannelRayleighRitzCertificate
    (hcert : ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_twoChannelSteinEnergyCertificate
    (twoChannelSteinEnergyCertificate_of_rayleighRitzCertificate hcert)

/-- Direct linear Hankel consumer of the explicit Rayleigh--Ritz matrix
certificate. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelRayleighRitz
    (hcert : ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_twoChannelSteinEnergy
    (twoChannelSteinEnergyCertificate_of_rayleighRitzCertificate hcert) hrelaxed

/-- RH-facing degree-two-tail interface for the explicit two-channel
Rayleigh--Ritz determinant certificate. -/
theorem riemannHypothesis_of_twoChannelRayleighRitz_of_primeArchDegreeTwoTail
    (hcert : ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_twoChannelSteinEnergy_of_primeArchDegreeTwoTail
    (twoChannelSteinEnergyCertificate_of_rayleighRitzCertificate hcert)
    hrelaxed htail

end

end RHTower
