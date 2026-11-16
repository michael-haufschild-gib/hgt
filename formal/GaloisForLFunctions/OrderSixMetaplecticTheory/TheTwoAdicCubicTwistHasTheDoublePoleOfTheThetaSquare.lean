import GaloisForLFunctions.OrderSixMetaplecticTheory.BoundedRemaindersHaveAtMostASimplePoleAtFourThirds

/-!
# The two-adic cubic twist has the double pole of the theta square

Let `T` be the Fourier coefficients of the projected cubic theta function, `M(s) = ∫_0^∞ t^{s−1}K_{1/3}(t)²dt`,
`D(s) = Σ_{h≠0} T(h)² (4π|ξ_h|)^{−s}` the squared theta series (STCC: double pole at `4/3` with leading coefficient
`108π³r³`), and

* `D₄(s) = Σ_{h≠0} T(h) T(−4h) (4π|ξ_h|)^{−s}` — the shifted square at the inert prime `2` (`fourShiftCoeff`);
* `L_χ(s) = Σ_{h≠0} χ(h) T(h)² (4π|ξ_h|)^{−s}` — the **2-adic cubic twist** of the theta square, `χ(h)` the cube root of
  unity congruent to `h` modulo `2` (`0` for even `h`) (`cubicTwistCoeff`).

**Theorem** (`twoAdicCubicTwist_double_pole`). `M(s) (2^{−s} D₄(s) + 2^{s−2} L_χ(s))` continues analytically to
`{1 < Re s < 13/3, Im s > 0}` and to a punctured neighbourhood of `4/3`, and

`(s − 4/3)² M(s) (2^{−s} D₄(s) + 2^{s−2} L_χ(s)) → 108 π³ r³ ≠ 0`.

Mechanism. The Hecke-at-four trace `Tr F` of `θ_s` has constant term `8|P|(c²v^{4/3} + ¼R₄(2v) + R_χ(v/2))`
(`R_P(u) = Σ_{h≠0} P(h) u² K_{1/3}(4π|ξ_h|u)²`), and `G' = Tr F − 8θ_s²` is a bounded remainder without growth.
Its Eisenstein pairing has at most a simple pole at `4/3` (`RemainderData.pairing_near_four_thirds`), and its
Mellin transform is `8|P| M(s)(2^{−s}D₄ + 2^{s−2}L_χ − D)`. So the two-adic combination inherits the double pole of
`D` exactly.
-/

noncomputable section

open MeasureTheory Filter Function Asymptotics
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### Series of integrable functions -/

/-- An absolutely summable series of integrable functions is integrable. -/
theorem integrable_tsum_of_summable_integral_norm' {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} {F : ι → α → ℂ} (hF : ∀ i, Integrable (F i) μ) (hFm : ∀ i, Measurable (F i))
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by
  refine ⟨(Measurable.tsum hFm).aestronglyMeasurable, ?_⟩
  have hl : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    intro i
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ := lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum fun i => (hFm i).enorm.aemeasurable
    _ = ∑' i, ‖∫ a, ‖F i a‖ ∂μ‖ₑ := tsum_congr hl
    _ < ⊤ := lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hs.abs)

theorem schlafliIntegral_measurable (ν : ℂ) : Measurable (schlafliIntegral ν) := by
  have h : Measurable (Function.uncurry fun (x t : ℝ) => (t : ℂ) ^ (ν - 1) *
      Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))) := by
    fun_prop
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

theorem schlafliBesselK_measurable (ν : ℂ) : Measurable (schlafliBesselK ν) := by
  unfold schlafliBesselK
  exact (measurable_const.mul ((Complex.measurable_ofReal.div_const _).pow_const _)).mul
    (schlafliIntegral_measurable ν)

theorem besselSq_measurable : Measurable besselSq :=
  (schlafliBesselK_measurable _).pow_const 2

/-- **The Mellin integrand of a Bessel series is integrable.** -/
theorem integrableOn_besselRemainder (P : O → ℂ) (s : ℂ) (hs : 2 / 3 < s.re)
    (hP : Summable (fun h : O => if h = 0 then 0 else ‖P h‖ * ‖cuspFrequency h‖ ^ (-s.re))) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * besselRemainder P v / (v : ℂ) ^ 3) (Set.Ioi 0) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  set a : O → ℝ := fun h => 4 * Real.pi * ‖cuspFrequency h‖ with ha_def
  have ha : ∀ h : O, h ≠ 0 → 0 < a h := fun h hh =>
    by have := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh); positivity
  set F : O → ℝ → ℂ := fun h v => if h = 0 then 0 else P h * ((v : ℂ) ^ (s - 1) • besselSq (a h * v)) with hF
  have hconv := besselSqMellin_convergent s hs
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), (v : ℂ) ^ s * besselRemainder P v / (v : ℂ) ^ 3 = ∑' h, F h v := by
    intro v (hv : 0 < v)
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    have hcp : (v : ℂ) ^ (s - 1) = (v : ℂ) ^ s / v := by
      rw [Complex.cpow_sub _ _ hv0, Complex.cpow_one]
    rw [besselRemainder, ← tsum_mul_left, ← tsum_div_const]
    refine tsum_congr fun h => ?_
    by_cases hh : h = 0
    · simp [hF, hh]
    · simp only [hF, hh, if_false, smul_eq_mul, hcp, ha_def, mul_comm (4 * Real.pi * ‖cuspFrequency h‖) v,
        ← mul_assoc]
      field_simp
  have hint : ∀ h, Integrable (F h) (volume.restrict (Set.Ioi 0)) := by
    intro h
    by_cases hh : h = 0
    · simp only [hF, hh, if_true]
      exact integrable_zero _ _ _
    · simp only [hF, hh, if_false]
      exact ((MellinConvergent.comp_mul_left (ha h hh)).mpr hconv).const_mul _
  have hmeas : ∀ h, Measurable (F h) := by
    intro h
    by_cases hh : h = 0
    · simp only [hF, hh, if_true]
      exact measurable_const
    · simp only [hF, hh, if_false]
      exact measurable_const.mul ((Complex.measurable_ofReal.pow_const _).smul
        (besselSq_measurable.comp (measurable_const.mul measurable_id)))
  have hnorm : ∀ h, ∫ v in Set.Ioi (0 : ℝ), ‖F h v‖ = (∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • besselSq t‖) *
      (4 * Real.pi) ^ (-s.re) * (if h = 0 then 0 else ‖P h‖ * ‖cuspFrequency h‖ ^ (-s.re)) := by
    intro h
    by_cases hh : h = 0
    · simp [hF, hh]
    simp only [hF, hh, if_false]
    have hah := ha h hh
    have hcpow : ∀ v : ℝ, 0 < v → ‖(v : ℂ) ^ (s - 1)‖ = a h ^ (1 - s.re) * ‖((a h * v : ℝ) : ℂ) ^ (s - 1)‖ := by
      intro v hv
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.sub_re, Complex.one_re, Real.mul_rpow hah.le hv.le, ← mul_assoc,
        ← Real.rpow_add hah]
      norm_num
    set N : ℝ := ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • besselSq t‖
    calc ∫ v in Set.Ioi (0 : ℝ), ‖P h * ((v : ℂ) ^ (s - 1) • besselSq (a h * v))‖
        = ∫ v in Set.Ioi (0 : ℝ), ‖P h‖ * a h ^ (1 - s.re) *
            ‖((a h * v : ℝ) : ℂ) ^ (s - 1) • besselSq (a h * v)‖ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
          rw [norm_mul, norm_smul, norm_smul, hcpow v hv]
          ring
      _ = ‖P h‖ * a h ^ (1 - s.re) * ((a h)⁻¹ * N) := by
          rw [integral_const_mul]
          congr 1
          have hc := integral_comp_mul_left_Ioi
            (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • besselSq t‖) 0 hah
          rw [mul_zero] at hc
          rw [hc, smul_eq_mul]
      _ = _ := by
          have hsplit : a h ^ (1 - s.re) * (a h)⁻¹ = (4 * Real.pi) ^ (-s.re) * ‖cuspFrequency h‖ ^ (-s.re) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hah, ha_def, Real.mul_rpow (by positivity)
              (norm_nonneg _)]
            ring_nf
          calc _ = N * ‖P h‖ * (a h ^ (1 - s.re) * (a h)⁻¹) := by ring
            _ = _ := by rw [hsplit]; ring
  have hsum : Summable (fun h => ∫ v in Set.Ioi (0 : ℝ), ‖F h v‖) := by
    simp_rw [hnorm]
    exact hP.mul_left _
  have hI := integrable_tsum_of_summable_integral_norm' hint hmeas hsum
  exact (integrableOn_congr_fun (fun v hv => hpt v hv) measurableSet_Ioi).mpr hI


/-! ### Dilations of Mellin integrands -/

/-- `∫_0^∞ v^s f(bv) v^{−3} dv = b^{2−s} ∫_0^∞ u^s f(u) u^{−3} du` for `b > 0`. -/
theorem integral_mellin_comp_mul (f : ℝ → ℂ) (s : ℂ) {b : ℝ} (hb : 0 < b) :
    ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * f (b * v) / (v : ℂ) ^ 3 =
      (b : ℂ) ^ (2 - s) * ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ s * f u / (u : ℂ) ^ 3 := by
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  set g : ℝ → ℂ := fun u => (b : ℂ) ^ (3 - s) * ((u : ℂ) ^ s * f u / (u : ℂ) ^ 3)
  have hc := integral_comp_mul_left_Ioi g 0 hb
  rw [mul_zero] at hc
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), (v : ℂ) ^ s * f (b * v) / (v : ℂ) ^ 3 = g (b * v) := by
    intro v (hv : 0 < v)
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    have hbs : (b : ℂ) ^ s ≠ 0 := by rw [Complex.cpow_def_of_ne_zero hb0]; exact Complex.exp_ne_zero _
    simp only [g]
    push_cast
    have h3 : (b : ℂ) ^ (3 : ℂ) = (b : ℂ) ^ (3 : ℕ) := by exact_mod_cast Complex.cpow_natCast (b : ℂ) 3
    rw [Complex.mul_cpow_ofReal_nonneg hb.le hv.le, Complex.cpow_sub _ _ hb0, h3]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hc, integral_const_mul, Complex.real_smul]
  push_cast
  rw [show (b : ℂ)⁻¹ * ((b : ℂ) ^ (3 - s) * ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ s * f u / (u : ℂ) ^ 3) =
    ((b : ℂ)⁻¹ * (b : ℂ) ^ (3 - s)) * ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ s * f u / (u : ℂ) ^ 3 by ring]
  congr 1
  rw [show (2 : ℂ) - s = (3 - s) + (-1) by ring, Complex.cpow_add _ _ hb0, Complex.cpow_neg_one]
  ring

theorem integrableOn_mellin_comp_mul (f : ℝ → ℂ) (s : ℂ) {b : ℝ} (hb : 0 < b)
    (hf : IntegrableOn (fun u : ℝ => (u : ℂ) ^ s * f u / (u : ℂ) ^ 3) (Set.Ioi 0)) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * f (b * v) / (v : ℂ) ^ 3) (Set.Ioi 0) := by
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  set g : ℝ → ℂ := fun u => (b : ℂ) ^ (3 - s) * ((u : ℂ) ^ s * f u / (u : ℂ) ^ 3)
  have hg : IntegrableOn g (Set.Ioi (b * 0)) := by rw [mul_zero]; exact hf.const_mul _
  have hc := (integrableOn_Ioi_comp_mul_left_iff g 0 hb).mpr hg
  refine (integrableOn_congr_fun (fun v (hv : 0 < v) => ?_) measurableSet_Ioi).mpr hc
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hbs : (b : ℂ) ^ s ≠ 0 := by rw [Complex.cpow_def_of_ne_zero hb0]; exact Complex.exp_ne_zero _
  simp only [g]
  push_cast
  have h3 : (b : ℂ) ^ (3 : ℂ) = (b : ℂ) ^ (3 : ℕ) := by exact_mod_cast Complex.cpow_natCast (b : ℂ) 3
  rw [Complex.mul_cpow_ofReal_nonneg hb.le hv.le, Complex.cpow_sub _ _ hb0, h3]
  field_simp

/-! ### The coefficients -/

/-- The shifted square `T(h) T(−4h)`. -/
def fourShiftCoeff (h : O) : ℂ :=
  rationalSourceResidualFourierCoefficient h * rationalSourceResidualFourierCoefficient (-(4 * h))

/-- The 2-adic cubic twist `χ(h) T(h)²`. -/
def cubicTwistCoeff (h : O) : ℂ := cubeRootF (red h) * rationalSourceResidualFourierCoefficient h ^ 2

theorem norm_cubeRootF_le (p : F4) : ‖cubeRootF p‖ ≤ 1 := by
  have hω : ‖ringComplex omega‖ = 1 := norm_ringComplex_omega
  unfold cubeRootF
  split_ifs <;> simp [hω]

theorem summable_sq_coeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else
      ‖rationalSourceResidualFourierCoefficient h ^ 2‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  simpa only [norm_pow] using summable_sourceCoefficient_sq_rpow hσ

theorem summable_cubicTwistCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖cubicTwistCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) (summable_sq_coeff hσ)
  · split_ifs <;> positivity
  · split_ifs with hh
    · exact le_rfl
    · rw [cubicTwistCoeff, norm_mul]
      have := norm_cubeRootF_le (red h)
      have h0 : 0 ≤ ‖rationalSourceResidualFourierCoefficient h ^ 2‖ * ‖cuspFrequency h‖ ^ (-σ) := by positivity
      nlinarith [norm_nonneg (rationalSourceResidualFourierCoefficient h ^ 2),
        Real.rpow_nonneg (norm_nonneg (cuspFrequency h)) (-σ)]

theorem norm_cuspFrequency_neg_four (h : O) : ‖cuspFrequency (-(4 * h))‖ = 4 * ‖cuspFrequency h‖ := by
  rw [cuspFrequency_neg, norm_neg, cuspFrequency_mul_four, norm_mul]
  norm_num

theorem summable_fourShiftCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖fourShiftCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  set A : O → ℝ := fun h => if h = 0 then 0 else
    ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) with hAdef
  have hA : Summable A := summable_sourceCoefficient_sq_rpow hσ
  have hinj : Function.Injective (fun h : O => -(4 * h)) := fun x y hxy => by
    have := neg_injective hxy
    exact mul_left_cancel₀ four_ne_zero_O this
  have hA4 : Summable (fun h => A (-(4 * h))) := hA.comp_injective hinj
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) ((hA.add (hA4.mul_left (4 ^ σ))).mul_left (1 / 2))
  · split_ifs <;> positivity
  · split_ifs with hh
    · simp [hAdef, hh]
    · have h4 : -(4 * h) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero four_ne_zero_O hh)
      simp only [hAdef, hh, h4, if_false, fourShiftCoeff, norm_mul, norm_cuspFrequency_neg_four]
      have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
      have hrp : (4 * ‖cuspFrequency h‖) ^ (-σ) = 4 ^ (-σ) * ‖cuspFrequency h‖ ^ (-σ) :=
        Real.mul_rpow (by norm_num) hξ.le
      have h44 : (4 : ℝ) ^ σ * 4 ^ (-σ) = 1 := by rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
      rw [hrp]
      set x := ‖rationalSourceResidualFourierCoefficient h‖
      set y := ‖rationalSourceResidualFourierCoefficient (-(4 * h))‖
      set p := ‖cuspFrequency h‖ ^ (-σ)
      have hp : 0 ≤ p := Real.rpow_nonneg hξ.le _
      have key : x * y * p ≤ 1 / 2 * (x ^ 2 * p + 4 ^ σ * (y ^ 2 * (4 ^ (-σ) * p))) := by
        rw [show 4 ^ σ * (y ^ 2 * (4 ^ (-σ) * p)) = y ^ 2 * p * (4 ^ σ * 4 ^ (-σ)) by ring, h44]
        nlinarith [sq_nonneg (x - y), mul_nonneg (sq_nonneg (x - y)) hp]
      exact key


/-! ### The remainder of the Hecke-at-four trace -/

theorem fourRemainder_automorphy (M : levelThree) (w : HyperbolicSpace) :
    fourRemainder (complexMatrix M • w) = (complexCharacter M)⁻¹ * fourRemainder w := by
  rw [fourRemainder, fourRemainder, sourceFourTrace_automorphy, sourceTheta_automorphy, ← complexCharacter_sq_eq_inv]
  ring

theorem fourRemainder_remainderData : RemainderData fourRemainder where
  automorphy := fourRemainder_automorphy
  measurable := fourRemainder_continuous.measurable
  bounded := fourRemainder_bounded
  high := norm_fourRemainder_strip 2 two_pos
  memLp := fourRemainder_memLp

/-! ### The constant term as Bessel series -/

theorem thetaSqRemainder_eq (v : ℝ) (hv : 0 < v) :
    thetaSqRemainder v = besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2) v := by
  rw [thetaSqRemainder, besselRemainder]
  refine tsum_congr fun h => ?_
  by_cases hh : h = 0
  · simp [hh]
  · rw [if_neg hh, if_neg hh, sourceAmplitude_mul_neg v hv h hh, besselSq]
    ring

theorem summable_amplitude_mul {a b : O → ℂ} (ha : Summable (fun h => ‖a h‖)) (hb : Summable (fun h => ‖b h‖))
    (f : O → O) : Summable (fun h => a h * b (f h)) := by
  refine Summable.of_norm_bounded (ha.mul_right (∑' k : O, ‖b k‖)) fun h => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb.le_tsum (f h) fun k _ => norm_nonneg _) (norm_nonneg _)

theorem tsum_four_amplitude (v : ℝ) (hv : 0 < v) :
    ∑' h : O, rationalSourceModeAmplitude (2 * v) h * rationalSourceModeAmplitude (v / 2) (-(4 * h)) =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) + 1 / 4 * besselRemainder fourShiftCoeff (2 * v) := by
  have hs := summable_amplitude_mul (rationalSourceModeAmplitude_summable (2 * v) (by positivity))
    (rationalSourceModeAmplitude_summable (v / 2) (by positivity)) (fun h => -(4 * h))
  rw [hs.tsum_eq_add_tsum_ite 0, sourceAmplitude_four_zero v hv, besselRemainder, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun h => ?_
  by_cases hh : h = 0
  · simp [hh]
  · rw [if_neg hh, if_neg hh, sourceAmplitude_four_shift v hv h hh, fourShiftCoeff, besselSq]
    have e : 4 * Real.pi * ‖cuspFrequency h‖ * (2 * v) = 8 * Real.pi * ‖cuspFrequency h‖ * v := by ring
    rw [e]
    push_cast
    ring

theorem cubeRootF_zero : cubeRootF 0 = 0 := by
  unfold cubeRootF
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem tsum_twist_amplitude (v : ℝ) (hv : 0 < v) :
    ∑' h : O, cubeRootF (red h) * (rationalSourceModeAmplitude (v / 2) h * rationalSourceModeAmplitude (v / 2) (-h)) =
      besselRemainder cubicTwistCoeff (v / 2) := by
  rw [besselRemainder]
  refine tsum_congr fun h => ?_
  by_cases hh : h = 0
  · simp [hh, red_zero, cubeRootF_zero]
  · rw [if_neg hh, sourceAmplitude_mul_neg (v / 2) (by positivity) h hh, cubicTwistCoeff, besselSq]
    ring

theorem integral_sourceThetaSq_periodDomain (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, sourceTheta (upperPoint z v hv) ^ 2 =
      periodArea * (thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) + thetaSqRemainder v) := by
  simp_rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion]
  rw [integral_cuspCharacterSeries_sq _ (rationalSourceModeAmplitude_summable v hv), tsum_amplitude_mul_neg v hv,
    rationalSourceModeAmplitude_zero]
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [show (4 / 3 : ℂ) = 2 / 3 + 2 / 3 by norm_num, Complex.cpow_add _ _ hv0]
  ring

/-- **The constant term of `G'`.** `a₀(G')(v) = 8|P| (¼R₄(2v) + R_χ(v/2) − R(v))`. -/
theorem cuspConstantTerm_fourRemainder (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm fourRemainder v = 8 * periodArea * (1 / 4 * besselRemainder fourShiftCoeff (2 * v) +
      besselRemainder cubicTwistCoeff (v / 2) -
        besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2) v) := by
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  have hc1 : Continuous (fun z : ℂ => sourceFourTrace (upperPoint z v hv)) := sourceFourTrace_continuous v hv
  have hc2 : Continuous (fun z : ℂ => sourceTheta (upperPoint z v hv) ^ 2) := by
    have h := cuspCharacterSeries_continuous _ (rationalSourceModeAmplitude_summable v hv)
    simp_rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion]
    exact h.pow 2
  rw [cuspConstantTerm]
  simp_rw [hlift, fourRemainder]
  rw [integral_sub (integrableOn_periodDomain_of_continuous _ hc1)
    ((integrableOn_periodDomain_of_continuous _ hc2).const_mul 8), integral_const_mul,
    integral_sourceFourTrace v hv, integral_sourceThetaSq_periodDomain v hv, tsum_four_amplitude v hv,
    tsum_twist_amplitude v hv, thetaSqRemainder_eq v hv]
  ring


/-! ### The Mellin transform and the double pole -/

theorem two_cpow_identities (s : ℂ) :
    1 / 4 * (2 : ℂ) ^ (2 - s) = (2 : ℂ) ^ (-s) ∧ (((1 / 2 : ℝ) : ℂ)) ^ (2 - s) = (2 : ℂ) ^ (s - 2) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  constructor
  · rw [Complex.cpow_sub _ _ h2, Complex.cpow_neg, show (2 : ℂ) ^ (2 : ℂ) = 4 by norm_num]
    field_simp
  · have harg : (2 : ℂ).arg ≠ Real.pi := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm
    rw [show (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ by push_cast; ring, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
    ring_nf

/-- **The Mellin identity.** For `4 < Re s < 13/3`:
`∫_{D_Γ} G' E(s) = 8|P| M(s) (2^{−s} D₄(s) + 2^{s−2} L_χ(s) − D(s))`. -/
theorem integral_fourRemainder_mul_eisenstein (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, fourRemainder w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      8 * periodArea * (besselSqMellin s * ((2 : ℂ) ^ (-s) * besselDirichlet fourShiftCoeff s +
        (2 : ℂ) ^ (s - 2) * besselDirichlet cubicTwistCoeff s - thetaSqDirichlet s)) := by
  have hG := fourRemainder_remainderData
  have hs23 : 2 / 3 < s.re := by linarith
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  set R4 := besselRemainder fourShiftCoeff
  set Rχ := besselRemainder cubicTwistCoeff
  set R := besselRemainder (fun h => rationalSourceResidualFourierCoefficient h ^ 2)
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, fourRemainder (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        8 * periodArea * (1 / 4 * ((v : ℂ) ^ s * R4 (2 * v) / (v : ℂ) ^ 3) +
          (v : ℂ) ^ s * Rχ (1 / 2 * v) / (v : ℂ) ^ 3 - (v : ℂ) ^ s * R v / (v : ℂ) ^ 3) := by
    intro v (hv : 0 < v)
    have hc := cuspConstantTerm_fourRemainder v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show v / 2 = 1 / 2 * v by ring]
    ring
  have hI4base := integrableOn_besselRemainder fourShiftCoeff s hs23 (summable_fourShiftCoeff hs4)
  have hIχbase := integrableOn_besselRemainder cubicTwistCoeff s hs23 (summable_cubicTwistCoeff hs4)
  have hI := integrableOn_besselRemainder _ s hs23 (summable_sq_coeff hs4)
  have hI4 := integrableOn_mellin_comp_mul R4 s two_pos hI4base
  have hIχ := integrableOn_mellin_comp_mul Rχ s (by norm_num : (0 : ℝ) < 1 / 2) hIχbase
  have J1 : IntegrableOn (fun v : ℝ => 1 / 4 * ((v : ℂ) ^ s * R4 (2 * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hI4.const_mul _
  have J12 : IntegrableOn (fun v : ℝ => 1 / 4 * ((v : ℂ) ^ s * R4 (2 * v) / (v : ℂ) ^ 3) +
      (v : ℂ) ^ s * Rχ (1 / 2 * v) / (v : ℂ) ^ 3) (Set.Ioi 0) := J1.add hIχ
  have J3 : IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * R v / (v : ℂ) ^ 3) (Set.Ioi 0) := hI
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_sub J12 J3, integral_add J1 hIχ,
    integral_const_mul, integral_mellin_comp_mul R4 s two_pos,
    integral_mellin_comp_mul Rχ s (by norm_num : (0 : ℝ) < 1 / 2),
    integral_besselRemainder fourShiftCoeff s hs23 (summable_fourShiftCoeff hs4),
    integral_besselRemainder cubicTwistCoeff s hs23 (summable_cubicTwistCoeff hs4),
    integral_besselRemainder _ s hs23 (summable_sq_coeff hs4)]
  obtain ⟨h1, h2⟩ := two_cpow_identities s
  have hD : besselDirichlet (fun h => rationalSourceResidualFourierCoefficient h ^ 2) s = thetaSqDirichlet s := rfl
  rw [hD, h2, show ((2 : ℝ) : ℂ) = 2 by norm_num, ← h1]
  ring

/-- **The two-adic cubic twist has the double pole of the theta square.**
`M(s) (2^{−s} D₄(s) + 2^{s−2} L_χ(s))`, with `D₄(s) = Σ_{h≠0} T(h)T(−4h)(4π|ξ_h|)^{−s}` and
`L_χ(s) = Σ_{h≠0} χ(h)T(h)²(4π|ξ_h|)^{−s}` (`χ(h)` the cube root of unity `≡ h mod 2`), continues to
`{1 < Re s < 13/3, Im s > 0}` and to a punctured neighbourhood of `4/3`, and
`(s − 4/3)² M(s)(2^{−s}D₄(s) + 2^{s−2}L_χ(s)) → 108π³r³ ≠ 0`. -/
theorem twoAdicCubicTwist_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * ((2 : ℂ) ^ (-s) * besselDirichlet fourShiftCoeff s +
          (2 : ℂ) ^ (s - 2) * besselDirichlet cubicTwistCoeff s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) ∧
      (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 ≠ 0) := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, hne⟩ := thetaSqDirichlet_double_pole
  have hG := fourRemainder_remainderData
  have hP : (8 * periodArea : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne')
  refine ⟨fun s => Λ s + (8 * periodArea)⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    hne⟩
  · show Λ s + (8 * periodArea)⁻¹ * hG.pairing s = _
    rw [hΛ s hs4 hs hi, ← hG.pairing_eq s hs4 hs hi, integral_fourRemainder_mul_eisenstein s hs4 hs,
      inv_mul_cancel_left₀ hP]
    ring
  · exact (hΛd s hs1 hs hi).add ((hG.pairing_differentiableAt s hs1 hs hi).const_mul _)
  · filter_upwards [hΛn, hG.pairing_near_four_thirds.1] with s h1 h2
    exact h1.add (h2.const_mul _)
  · have h2 := hG.pairing_near_four_thirds.2
    have hsum := hΛl.add (h2.const_mul (8 * periodArea)⁻¹)
    rw [mul_zero, add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun s => ?_)
    ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
