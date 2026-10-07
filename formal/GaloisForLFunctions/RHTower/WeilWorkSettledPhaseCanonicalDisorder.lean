import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseAbelRigidity
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLittlewood

/-!
# Quantitative disorder of the full canonical cumulative phase

The original Weil-positive source either is von Mangoldt and satisfies RH, or
its full canonical interval phase has recurrent defect at a subpower scale.
No atomic representation, support restriction or critical-edge continuity is used.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity

/-- Reflection phase of the entire canonical measure, including central mass. -/
def canonicalPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I)

theorem measurable_canonicalPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Measurable (canonicalPhase hW) := by
  have hm : Monotone (fun y : ℝ => boundaryMeasure hW (Ioc (-y) y)) := by
    intro a b hab
    exact measure_mono (fun x hx => ⟨(neg_le_neg hab).trans_lt hx.1, hx.2.trans hab⟩)
  have hr : Measurable (fun y : ℝ => (boundaryMeasure hW).real (Ioc (-y) y)) :=
    hm.measurable.ennreal_toReal
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
    (measurable_const.mul hr)).mul_const I)

@[simp] theorem norm_canonicalPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    ‖canonicalPhase hW y‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem inv_lockConstant_neg (θ : ℝ) : (lockConstant (-θ))⁻¹ = lockConstant θ := by
  have h : lockConstant (-θ) = (lockConstant θ)⁻¹ := by
    unfold lockConstant
    rw [show (((2 * Real.pi * -θ : ℝ) : ℂ) * I) =
      -(((2 * Real.pi * θ : ℝ) : ℂ) * I) by push_cast; ring, Complex.exp_neg]
  rw [h, inv_inv]

theorem norm_quantizationTraceF_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    ‖quantizationTraceF hW (-y)‖ = ‖quantizationTraceF hW y‖ := by
  have hs : ((1 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I =
      conj (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  change ‖quantizationCompletedTrace hW (-y) /
    lineFactor (((1 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)‖ =
      ‖quantizationCompletedTrace hW y / lineFactor (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
  rw [quantizationCompletedTrace_neg, hs, lineFactor_conj, norm_div, norm_div,
    Complex.norm_conj, Complex.norm_conj]

/-- Exact a.e. factorization of the source remainder by the full cumulative phase. -/
theorem norm_lowerSourceRemainder_phase_ae {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (θ : ℝ) : ∀ᵐ t : ℝ, 0 < t →
      ‖lowerSourceRemainder hW θ (-t)‖ =
        ‖canonicalPhase hW (2 * t) - (lockConstant θ)⁻¹‖ *
          ‖quantizationTraceF hW (2 * t)‖ := by
  have hpos := (Measure.quasiMeasurePreserving_smul volume (by norm_num : (2 : ℝ) ≠ 0)).ae
    (quantizationCompletedTrace_ae_eq_sourceTrace hW)
  have hneg := (Measure.quasiMeasurePreserving_smul volume (by norm_num : (-2 : ℝ) ≠ 0)).ae
    (quantizationCompletedTrace_ae_eq_sourceTrace hW)
  simp only [smul_eq_mul] at hpos hneg
  filter_upwards [hpos, hneg] with t hp hn
  intro ht
  have href : quantizationCompletedTrace hW (2 * t) =
      canonicalPhase hW (2 * t) * quantizationCompletedTrace hW (-(2 * t)) := by
    rw [hp, show -(2 * t) = -2 * t by ring, hn]
    simpa only [canonicalPhase, neg_mul] using
      sourceTrace_reflection hW (y := 2 * t) (by linarith)
  have hΨ : quantizationReflectedTraceF hW (2 * (-t)) =
      canonicalPhase hW (2 * t) * quantizationTraceF hW (2 * (-t)) := by
    unfold quantizationReflectedTraceF quantizationTraceF
    rw [show -(2 * -t) = 2 * t by ring, href]
    rw [show -(2 * t) = 2 * -t by ring]
    ring
  unfold lowerSourceRemainder
  rw [Set.indicator_of_mem (show -t ∈ Iio (0 : ℝ) by change -t < 0; linarith),
    hΨ, ← sub_mul, norm_mul, norm_sub_rev]
  rw [show 2 * -t = -(2 * t) by ring, norm_quantizationTraceF_neg]

/-- The radial norm bound replaces any assumed continuous extension to the edge. -/
theorem norm_quantizationTraceF_le_exp_producerLogZeta {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T τ : ℝ} (hT2 : 2 ≤ T) (hτ : τ ∈ Ioc T (2 * T)) :
    ‖quantizationTraceF hW (2 * τ)‖ ≤ Real.exp 4 *
      Real.exp (producerLogZeta hW (1 / 2 + 1 / Real.log (2 * T)) (2 * τ)).re := by
  have hT0 : 0 < T := by linarith
  set σ' : ℝ := 1 / 2 + 1 / Real.log (2 * T) with hσ'
  have hlog2T : 1 ≤ Real.log (2 * T) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hσ'1 : 1 / 2 < σ' := by
    have : 0 < 1 / Real.log (2 * T) := by positivity
    linarith
  have hσ'2 : σ' ≤ 2 := by
    have : 1 / Real.log (2 * T) ≤ 1 := by rw [div_le_one (by linarith)]; exact hlog2T
    linarith
  have hτ0 : 0 < τ := hT0.trans hτ.1
  have h2τ : 4 ≤ |2 * τ| := by rw [abs_of_pos (by linarith)]; linarith [hτ.1]
  have hline : lineS τ = ((1 / 2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I := by
    rw [lineS_eq]; push_cast; ring
  have hmono := norm_quantizationCompletedTrace_le hW (2 * τ) hσ'1
  have hGeq := G_eq_lineFactor_mul_cexp hW
    (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW)
    hσ'1 (t := 2 * τ) (by positivity)
  have hD := norm_lineFactor_le hσ'1.le hσ'2 h2τ
  have hDpos : 0 < ‖lineFactor (((1 / 2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I)‖ :=
    norm_pos_iff.mpr (by
      rw [← hline]
      exact mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ))
  have hexp4 : Real.exp ((σ' - 1 / 2) * (Real.log |2 * τ| / 2 + 3)) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_pos (by linarith)]
    have hl : Real.log (2 * τ) ≤ Real.log (4 * T) :=
      Real.log_le_log (by linarith) (by linarith [hτ.2])
    have hl4 : Real.log (4 * T) ≤ 2 * Real.log (2 * T) := by
      have hp := Real.log_pow (2 * T) 2
      push_cast at hp
      rw [← hp]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have e : σ' - 1 / 2 = 1 / Real.log (2 * T) := by rw [hσ']; ring
    rw [e, one_div_mul_eq_div, div_le_iff₀ (by linarith)]
    linarith
  set s₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I
  change ‖quantizationCompletedTrace hW (2 * τ) / lineFactor s₀‖ ≤ _
  rw [norm_div, div_le_iff₀ hDpos]
  calc ‖quantizationCompletedTrace hW (2 * τ)‖ ≤
      ‖quantizationCompletion hW ((σ' : ℂ) + ((2 * τ : ℝ) : ℂ) * I)‖ := hmono
    _ = ‖lineFactor ((σ' : ℂ) + ((2 * τ : ℝ) : ℂ) * I)‖ *
          Real.exp (producerLogZeta hW σ' (2 * τ)).re := by
        rw [hGeq, norm_mul, Complex.norm_exp]
    _ ≤ Real.exp 4 * ‖lineFactor s₀‖ * Real.exp (producerLogZeta hW σ' (2 * τ)).re :=
        mul_le_mul_of_nonneg_right
          (hD.trans (mul_le_mul_of_nonneg_right hexp4 (norm_nonneg _))) (Real.exp_pos _).le
    _ = Real.exp 4 * Real.exp (producerLogZeta hW σ' (2 * τ)).re * ‖lineFactor s₀‖ := by ring

/-- Subpower envelope for the actual measurable radial quotient. -/
theorem exists_norm_quantizationTraceF_le_littlewood {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ T, T₀ ≤ T → ∀ τ ∈ Ioc T (2 * T),
      ‖quantizationTraceF hW (2 * τ)‖ ≤
        Real.exp 4 * Real.exp (K * Real.log T / Real.log (Real.log T)) := by
  obtain ⟨C, TC, hC, hbound⟩ := exists_re_producerLogZeta_le_littlewood_full hW
  refine ⟨4 * C, max TC (Real.exp (Real.exp 2)), by positivity, fun T hT τ hτ => ?_⟩
  have hTC : TC ≤ T := (le_max_left _ _).trans hT
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have hTexp : Real.exp (Real.exp 2) ≤ T := (le_max_right _ _).trans hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp (Real.exp 2)]
  have hT0 : 0 < T := by linarith
  have hlogT : Real.exp 2 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hTexp
  have hlogT0 : 0 < Real.log T := (Real.exp_pos 2).trans_le hlogT
  have hll : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  have hlog2T : 1 ≤ Real.log (2 * T) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hσ : 1 / 2 < 1 / 2 + 1 / Real.log (2 * T) := by
    have : 0 < 1 / Real.log (2 * T) := by positivity
    linarith
  have hσ2 : 1 / 2 + 1 / Real.log (2 * T) ≤ 2 := by
    have : 1 / Real.log (2 * T) ≤ 1 := by
      simpa using one_div_le_one_div_of_le zero_lt_one hlog2T
    linarith
  have hll2 : Real.log (Real.log T) ≤ Real.log (Real.log (2 * T)) :=
    Real.log_le_log (by linarith) (Real.log_le_log hT0 (by linarith))
  have hcap := re_producerLogZeta_le_cap hW hbound (T := 2 * T)
    (by linarith : TC ≤ 2 * T) (by linarith) (hll.trans_le hll2)
    (t := 2 * τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ hσ hσ2
  rw [max_eq_left hC.le] at hcap
  have hdouble : Real.log (2 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2]
  have hratio : 2 * C * Real.log (2 * T) / Real.log (Real.log (2 * T)) ≤
      (4 * C) * Real.log T / Real.log (Real.log T) := by
    calc _ ≤ 2 * C * (2 * Real.log T) / Real.log (Real.log T) := by gcongr
      _ = _ := by ring
  exact (norm_quantizationTraceF_le_exp_producerLogZeta hW hT2 hτ).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hcap.trans hratio)) (Real.exp_pos 4).le)

private theorem source_rigidity_or_phase_disorder_two_mul {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (θ : ℝ) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
        a * T * Real.exp (-(K * Real.log T / Real.log (Real.log T))) ≤
          ∫ t in Ioc T (2 * T), ‖canonicalPhase hW (2 * t) - lockConstant θ‖ := by
  rcases source_rigidity_or_block_disorder hW (-θ) with hR | ⟨η, hη, hlarge⟩
  · exact Or.inl hR
  right
  obtain ⟨K, TK, hK, hphi⟩ := exists_norm_quantizationTraceF_le_littlewood hW
  refine ⟨η * Real.exp (-4), K, mul_pos hη (Real.exp_pos _), hK, fun R => ?_⟩
  obtain ⟨T, hT, hbad⟩ := hlarge (max R (max TK 2))
  have hTR : R ≤ T := (le_max_left _ _).trans hT
  have hTK : TK ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT2 : 2 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  refine ⟨T, hTR, ?_⟩
  let u : ℝ → ℂ := fun t => canonicalPhase hW (2 * t) - lockConstant θ
  have hum : Measurable u :=
    ((measurable_canonicalPhase hW).comp (measurable_const.mul measurable_id)).sub_const _
  have hub : ∀ t, ‖u t‖ ≤ 2 := by
    intro t
    simpa only [norm_canonicalPhase, norm_lockConstant, one_add_one_eq_two] using
      norm_sub_le (canonicalPhase hW (2 * t)) (lockConstant θ)
  have huI : IntegrableOn (fun t => ‖u t‖) (Ioc T (2 * T)) := by
    refine Measure.integrableOn_of_bounded (M := 2) (by simp [Real.volume_Ioc])
      hum.norm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hub t
  let q : ℝ := K * Real.log T / Real.log (Real.log T)
  have hAE : ∀ᵐ t ∂volume.restrict (Ioc T (2 * T)),
      ‖lowerSourceRemainder hW (-θ) (-t)‖ ≤ (Real.exp 4 * Real.exp q) * ‖u t‖ := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [norm_lowerSourceRemainder_phase_ae hW (-θ)] with t ht hmem
    rw [ht (by linarith [hmem.1]), inv_lockConstant_neg]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hphi T hTK t hmem) (norm_nonneg _)
  have hrm := ((measurable_lowerSourceRemainder hW (-θ)).comp measurable_neg).norm
  have hrI : IntegrableOn (fun t => ‖lowerSourceRemainder hW (-θ) (-t)‖) (Ioc T (2 * T)) := by
    refine (huI.const_mul (Real.exp 4 * Real.exp q)).mono' hrm.aestronglyMeasurable ?_
    filter_upwards [hAE] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using ht
  have hmono := setIntegral_mono_ae_restrict hrI (huI.const_mul (Real.exp 4 * Real.exp q)) hAE
  rw [integral_const_mul] at hmono
  have hbad' : η * T ≤ (Real.exp 4 * Real.exp q) * ∫ t in Ioc T (2 * T), ‖u t‖ :=
    hbad.le.trans hmono
  have hcancel : Real.exp (-4) * Real.exp (-q) * (Real.exp 4 * Real.exp q) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    rw [show (-4 : ℝ) + -q + (4 + q) = 0 by ring, Real.exp_zero]
  have h := mul_le_mul_of_nonneg_left hbad' (mul_pos (Real.exp_pos (-4)) (Real.exp_pos (-q))).le
  calc (η * Real.exp (-4)) * T * Real.exp (-q)
      = (Real.exp (-4) * Real.exp (-q)) * (η * T) := by ring
    _ ≤ (Real.exp (-4) * Real.exp (-q)) *
        ((Real.exp 4 * Real.exp q) * ∫ t in Ioc T (2 * T), ‖u t‖) := h
    _ = ∫ t in Ioc T (2 * T), ‖u t‖ := by rw [← mul_assoc, hcancel, one_mul]

/-- Source-only obstruction at the actual height scale. The phase uses the full
canonical measure, with no atomicity or support-gap premise. -/
theorem source_rigidity_or_canonical_phase_disorder {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (θ : ℝ) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ R : ℝ, ∃ Y : ℝ, R ≤ Y ∧
        a * Y * Real.exp (-(K * Real.log Y / Real.log (Real.log Y))) ≤
          ∫ y in Ioc Y (2 * Y), ‖canonicalPhase hW y - lockConstant θ‖ := by
  rcases source_rigidity_or_phase_disorder_two_mul hW θ with hr | ⟨a, K, ha, hK, hlarge⟩
  · exact Or.inl hr
  right
  refine ⟨a, 2 * K, ha, by positivity, fun R => ?_⟩
  obtain ⟨T, hT, hbad⟩ := hlarge (max R (Real.exp 2))
  have hTR : R ≤ T := (le_max_left _ _).trans hT
  have hTexp : Real.exp 2 ≤ T := (le_max_right _ _).trans hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp 2]
  have hT0 : 0 < T := by linarith
  refine ⟨2 * T, by linarith, ?_⟩
  let f : ℝ → ℝ := fun y => ‖canonicalPhase hW y - lockConstant θ‖
  have hchange : ∫ t in Ioc T (2 * T), f (2 * t) =
      2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  change a * T * Real.exp (-(K * Real.log T / Real.log (Real.log T))) ≤
    ∫ t in Ioc T (2 * T), f (2 * t) at hbad
  rw [hchange] at hbad
  have hlogT : 2 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hTexp
  have hllT : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  have hlogmono : Real.log T ≤ Real.log (2 * T) := Real.log_le_log hT0 (by linarith)
  have hll2 : 0 < Real.log (Real.log (2 * T)) :=
    hllT.trans_le (Real.log_le_log (by linarith) hlogmono)
  have hdlog : Real.log (2 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2]
  have hdll : Real.log (Real.log (2 * T)) ≤ 2 * Real.log (Real.log T) := by
    have h := Real.log_le_log (by linarith : 0 < Real.log (2 * T)) hdlog
    rw [Real.log_mul (by norm_num) (by linarith : Real.log T ≠ 0)] at h
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlogT]
  have hratio : Real.log T / Real.log (Real.log T) ≤
      2 * Real.log (2 * T) / Real.log (Real.log (2 * T)) := by
    calc _ ≤ Real.log (2 * T) / Real.log (Real.log T) :=
        div_le_div_of_nonneg_right hlogmono hllT.le
      _ = 2 * Real.log (2 * T) / (2 * Real.log (Real.log T)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hll2 hdll
  have hexp : Real.exp (-((2 * K) * Real.log (2 * T) / Real.log (Real.log (2 * T)))) ≤
      Real.exp (-(K * Real.log T / Real.log (Real.log T))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    calc K * Real.log T / Real.log (Real.log T)
        = K * (Real.log T / Real.log (Real.log T)) := by ring
      _ ≤ K * (2 * Real.log (2 * T) / Real.log (Real.log (2 * T))) :=
        mul_le_mul_of_nonneg_left hratio hK.le
      _ = (2 * K) * Real.log (2 * T) / Real.log (Real.log (2 * T)) := by ring
  have hscale := mul_le_mul_of_nonneg_left hexp (mul_nonneg ha.le hT0.le)
  calc a * (2 * T) * Real.exp (-((2 * K) * Real.log (2 * T) / Real.log (Real.log (2 * T))))
      ≤ 2 * (a * T * Real.exp (-(K * Real.log T / Real.log (Real.log T)))) := by nlinarith
    _ ≤ ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by norm_num at hbad ⊢; linarith

end RHTower.WeilWorkSettledPhase
