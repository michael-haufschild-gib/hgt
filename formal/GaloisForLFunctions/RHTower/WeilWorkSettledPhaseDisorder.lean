import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLittlewood
import GaloisForLFunctions.RHTower.WeilConeSettledAtomicPhase

/-!
# Quantitative phase disorder for a nonrigid Weil source

The coefficient-free Littlewood bound gives a source-dependent envelope
`exp(4) exp(K log T / log log T)` for the normalized boundary producer.
Consequently a bounded reflection lock either forces rigidity or has L1 defect
at least `a T exp(-K log T / log log T)` at arbitrarily large heights.

No phase-decay hypothesis is used in this dichotomy. Its atomic specialization
retains the exact representation and support hypotheses; these are not derived here.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilWorkSettledPhase

open WeilSpectral WeilHerglotz IntegerMassRigidity FractionalMassRigidity
  FractionalMassTailRigidity AbelianTwist PhaseLockRigidity

/-- The new source bound controls the normalized boundary producer on every large
dyadic block, with no coefficient or moment-class premise. -/
theorem exists_norm_phiG_le_littlewood {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) :
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ T, T₀ ≤ T → ∀ τ ∈ Ioc T (2 * T),
      ‖phiG G τ‖ ≤ Real.exp 4 * Real.exp (K * Real.log T / Real.log (Real.log T)) := by
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
  exact (norm_phiG_le_exp_producerLogZeta hW hGc hGd hG2 hT2 hτ).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hcap.trans hratio)) (Real.exp_pos 4).le)

/-- A nonrigid source must have quantitative phase disorder at arbitrarily large
heights. All growth control is obtained from the original full-positive source. -/
theorem rigidity_or_lock_disorder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {w : ℝ → ℂ} (hwm : Measurable w) {Cw : ℝ}
    (hwb : ∀ τ, ‖w τ‖ ≤ Cw) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) = w τ * G (lineS τ)) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
        a * T * Real.exp (-(K * Real.log T / Real.log (Real.log T))) ≤
          ∫ τ in Ioc T (2 * T), ‖w (-τ) - c₀⁻¹‖ := by
  classical
  by_cases hr : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hr
  right
  have hn : ¬ (∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖w (-τ) - c₀⁻¹‖ * ‖phiG G τ‖ ≤ η * T) :=
    fun h => hr (lock_rigidity_of_block_means hW hGc hGd hG2 hwm hwb hc₀ hY hlock h)
  push Not at hn
  obtain ⟨η, hη, hlarge⟩ := hn
  obtain ⟨K, TK, hK, hphi⟩ := exists_norm_phiG_le_littlewood hW hGc hGd hG2
  refine ⟨η * Real.exp (-4), K, mul_pos hη (Real.exp_pos _), hK, fun R => ?_⟩
  obtain ⟨T, hT, hbad⟩ := hlarge (max R TK)
  have hTR : R ≤ T := (le_max_left _ _).trans hT
  have hTK : TK ≤ T := (le_max_right _ _).trans hT
  refine ⟨T, hTR, ?_⟩
  set u : ℝ → ℂ := fun τ => w (-τ) - c₀⁻¹
  have hum : Measurable u := (hwm.comp measurable_neg).sub_const _
  have hub : ∀ τ, ‖u τ‖ ≤ Cw + ‖c₀⁻¹‖ := fun τ =>
    (norm_sub_le _ _).trans (by linarith [hwb (-τ)])
  have huI : IntegrableOn (fun τ => ‖u τ‖) (Ioc T (2 * T)) := by
    refine Measure.integrableOn_of_bounded (M := Cw + ‖c₀⁻¹‖)
      (by simp [Real.volume_Ioc]) hum.norm.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hub τ
  set q : ℝ := K * Real.log T / Real.log (Real.log T)
  have hpt : ∀ τ ∈ Ioc T (2 * T), ‖u τ‖ * ‖phiG G τ‖ ≤
      (Real.exp 4 * Real.exp q) * ‖u τ‖ := fun τ hτ => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hphi T hTK τ hτ) (norm_nonneg _)
  have hmono := setIntegral_mono_on (integrableOn_mul_norm_phiG hGc hum hub T)
    (huI.const_mul (Real.exp 4 * Real.exp q)) measurableSet_Ioc hpt
  rw [integral_const_mul] at hmono
  have hbad' : η * T ≤ (Real.exp 4 * Real.exp q) * ∫ τ in Ioc T (2 * T), ‖u τ‖ :=
    hbad.le.trans hmono
  have hcancel : Real.exp (-4) * Real.exp (-q) * (Real.exp 4 * Real.exp q) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1; ring
  have h := mul_le_mul_of_nonneg_left hbad' (mul_pos (Real.exp_pos (-4)) (Real.exp_pos (-q))).le
  calc (η * Real.exp (-4)) * T * Real.exp (-q)
      = (Real.exp (-4) * Real.exp (-q)) * (η * T) := by ring
    _ ≤ (Real.exp (-4) * Real.exp (-q)) *
        ((Real.exp 4 * Real.exp q) * ∫ τ in Ioc T (2 * T), ‖u τ‖) := h
    _ = ∫ τ in Ioc T (2 * T), ‖u τ‖ := by rw [← mul_assoc, hcancel, one_mul]

/-- For the exact atomic boundary measure, failure of rigidity forces disorder of
its actual strict-cutoff cumulative phase on arbitrarily large dyadic intervals.
The representation inputs remain explicit; there is no assumed phase estimate. -/
theorem rigidity_or_atomic_phase_disorder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (htt : Tendsto t atTop atTop) (hsum : Summable fun j => c j / t j ^ 2)
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      ∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j))))
    (θ : ℝ) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ R : ℝ, ∃ Y : ℝ, R ≤ Y ∧
        a * Y * Real.exp (-(K * Real.log Y / Real.log (Real.log Y))) ≤
          ∫ y in Ioc Y (2 * Y),
            ‖cexp (((2 * Real.pi * phaseSum c t y : ℝ) : ℂ) * I) -
              cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I)‖ := by
  have hid0 := weilFunction_eq_atomicPairSeries hW hc hone hsum hrep
  have hsum0 : Summable fun j => ((fun _ => (0 : ℕ)) j : ℝ) / t j ^ 2 := by simp
  set m : ℕ → ℕ := fun _ => 0
  set G := gInf lam m t c t
  set Φ := phiInf m t c t
  have hidΦ : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := by
    intro s hs
    have h := hid0 s hs
    rw [weilFunction] at h
    have hfun : lamTwo lam = lamC lam := by
      funext n; unfold lamTwo lamC; split_ifs <;> simp
    show atomicPairSeries (fun j => Real.pi * (m j : ℝ)) t s +
      ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (t k : ℂ) ^ 2)) = _
    simp only [m, Nat.cast_zero, mul_zero]
    have h0 : atomicPairSeries (fun _ => (0 : ℝ)) t s = 0 := by unfold atomicPairSeries; simp
    rw [h0, zero_add, ← atomicPairSeries_pi_mul_eq, ← h, zetaArchimedeanDatum, hfun]
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum0 hc hone htt hsum
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum0 hc hone htt hsum hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s := by
    intro s hs
    rw [← eqOn_weilContinuation hW hΦd hidΦ hs]
    exact hasDerivAt_gInf hone hsum0 hc hone htt hsum hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum0 hc hone htt hsum
  set w : ℝ → ℂ := fun τ => cexp (((2 * Real.pi * phaseSum c t (-(2 * τ)) : ℝ) : ℂ) * I)
  have hlock : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) = w τ * G (lineS τ) := by
    intro τ hτ
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    simp only [G, gInf, w]
    rw [atomQ_one_sub hone hsum0, one_sub_lineS_eq_conj, fracInfProd_conj hc hone htt hsum hre,
      hline, conj_fracInfProd_lower hc hone htt hsum hy]
    ring
  have hwm : Measurable w := by
    have hph : Measurable fun τ : ℝ => phaseSum c t (-(2 * τ)) :=
      ((phaseSum_mono hc htt).comp_antitone (show Antitone fun τ : ℝ => -(2 * τ) from
        fun a b hab => by linarith)).measurable
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hph)).mul_const I)
  have hwb : ∀ τ, ‖w τ‖ ≤ 1 := fun τ => by simp only [w, Complex.norm_exp_ofReal_mul_I, le_refl]
  set c₀ : ℂ := (cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I))⁻¹
  have hc₀ : c₀ ≠ 0 := inv_ne_zero (Complex.exp_ne_zero _)
  rcases rigidity_or_lock_disorder hW hGc hGd hG2 hwm hwb hc₀ le_rfl hlock with
    hr | ⟨a, K, ha, hK, hlarge⟩
  · exact Or.inl hr
  right
  refine ⟨a, 2 * K, ha, by positivity, fun R => ?_⟩
  obtain ⟨T, hT, hbad⟩ := hlarge (max R (Real.exp 2))
  have hTR : R ≤ T := (le_max_left _ _).trans hT
  have hTexp : Real.exp 2 ≤ T := (le_max_right _ _).trans hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp 2]
  have hT0 : 0 < T := by linarith
  refine ⟨2 * T, by linarith, ?_⟩
  set f : ℝ → ℝ := fun y => ‖cexp (((2 * Real.pi * phaseSum c t y : ℝ) : ℂ) * I) -
    cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I)‖
  have hfeq : ∀ τ : ℝ, ‖w (-τ) - c₀⁻¹‖ = f (2 * τ) := by
    intro τ
    simp only [w, c₀, inv_inv, f]
    congr 4
    ring_nf
  simp only [hfeq] at hbad
  have hchange : ∫ τ in Ioc T (2 * T), f (2 * τ) =
      2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
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
