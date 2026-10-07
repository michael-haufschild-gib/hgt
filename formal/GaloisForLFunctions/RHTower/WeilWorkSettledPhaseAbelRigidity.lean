import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialTheta
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilConeSettledLockRigidity

/-!
# A full-measure Abel obstruction for the actual Weil source

The actual radial trace already supplies the two arithmetic Laplace identities.
For each constant phase, either the source is von Mangoldt and RH holds, or its
explicit lower reflection remainder fails Abel sublinearity. No continuous
critical-edge extension, atomic representation, or phase-decay premise is used.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  GaloisForLFunctions.HTGeometry HamburgerStability HamburgerTwisted

/-- A candidate unit reflection phase. -/
def lockConstant (θ : ℝ) : ℂ := cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I)

@[simp] theorem norm_lockConstant (θ : ℝ) : ‖lockConstant θ‖ = 1 := by
  rw [lockConstant, Complex.norm_exp]
  simp

/-- The actual lower-half-line remainder for a candidate constant phase. -/
def lowerSourceRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (θ : ℝ) : ℝ → ℂ :=
  (Iio (0 : ℝ)).indicator (fun t => (lockConstant θ)⁻¹ * quantizationTraceF hW (2 * t) -
    quantizationReflectedTraceF hW (2 * t))

theorem measurable_lowerSourceRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (θ : ℝ) :
    Measurable (lowerSourceRemainder hW θ) := by
  exact (((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).const_mul
    (lockConstant θ)⁻¹ |>.sub ((measurable_quantizationReflectedTraceF hW).comp
      (measurable_const.mul measurable_id))).indicator measurableSet_Iio

theorem norm_lowerSourceRemainder_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (θ t : ℝ) :
    ‖lowerSourceRemainder hW θ t‖ ≤
      ‖quantizationTraceF hW (2 * t)‖ + ‖quantizationReflectedTraceF hW (2 * t)‖ := by
  calc ‖lowerSourceRemainder hW θ t‖ ≤
      ‖(lockConstant θ)⁻¹ * quantizationTraceF hW (2 * t) - quantizationReflectedTraceF hW (2 * t)‖ :=
        norm_indicator_le_norm_self _ _
    _ ≤ ‖(lockConstant θ)⁻¹ * quantizationTraceF hW (2 * t)‖ +
        ‖quantizationReflectedTraceF hW (2 * t)‖ := norm_sub_le _ _
    _ = _ := by simp

/-- Full positivity alone supplies this rigidity-or-Abel-disorder alternative
for the original measure, including its diffuse and low-ordinate components. -/
theorem source_rigidity_or_abel_disorder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (θ : ℝ) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ¬ Tendsto (fun δ : ℝ => δ * abelMass (lowerSourceRemainder hW θ) δ) (𝓝[>] 0) (𝓝 0) := by
  classical
  by_cases hA : Tendsto (fun δ : ℝ => δ * abelMass (lowerSourceRemainder hW θ) δ)
      (𝓝[>] 0) (𝓝 0)
  · left
    let a := dirichletExp (lamLog lam)
    let β := betaG (quantizationCompletion hW)
    let κ := lockConstant θ
    let Φ : ℝ → ℂ := fun t => quantizationTraceF hW (2 * t)
    let Ψ : ℝ → ℂ := fun t => quantizationReflectedTraceF hW (2 * t)
    let g : ℝ → ℂ := fun t => Φ t - Ψ t
    let r : ℝ → ℂ := lowerSourceRemainder hW θ
    have hκ : κ ≠ 0 := Complex.exp_ne_zero _
    have hΦm : Measurable Φ :=
      (measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)
    have hΨm : Measurable Ψ :=
      (measurable_quantizationReflectedTraceF hW).comp (measurable_const.mul measurable_id)
    have hgm : Measurable g := hΦm.sub hΨm
    have hrm : Measurable r := measurable_lowerSourceRemainder hW θ
    obtain ⟨C, hC, hB⟩ := exists_quantization_trace_pair_bound hW
    have hΦb : ∀ t : ℝ, ‖Φ t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := fun t =>
      (hB t).1.trans (by gcongr; linarith)
    have hgb : ∀ t : ℝ, ‖g t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
      intro t
      exact (norm_sub_le _ _).trans (by linarith [(hB t).1, (hB t).2])
    have hrb : ∀ t : ℝ, ‖r t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
      intro t
      exact (norm_lowerSourceRemainder_le hW θ t).trans (by linarith [(hB t).1, (hB t).2])
    have hlow : ∀ t : ℝ, t < 0 → g t = (1 - κ⁻¹) * Φ t + r t := by
      intro t ht
      change Φ t - Ψ t = (1 - κ⁻¹) * Φ t +
        (Iio (0 : ℝ)).indicator (fun t => κ⁻¹ * Φ t - Ψ t) t
      rw [Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht)]
      ring
    have ha := fun σ hσ => quantization_coeff_summable hW (σ := σ) hσ
    have ha2 : Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      simpa using summable_sq_of_forall_rpow ha
    let S : ℂ → ℂ := fun τ => ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))
    have hL : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ =
        S τ - β / (Real.pi * τ) + β + defectLaplace g τ :=
      fun _ hτ => quantization_hamburgerSeries_reflection hW hτ
    have hL0 : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ = β + defectLaplace Φ τ :=
      fun _ hτ => quantization_hamburgerSeries_eq hW hτ
    let U : Set ℝ := Ioi 0
    let Lo : Set ℝ := Iio 0
    let Mi : Set ℝ := Icc 0 0
    let K : ℂ → ℂ := fun τ => κ * defectLaplace (U.indicator g) τ -
      (κ - 1) * (defectLaplace (U.indicator Φ) τ + defectLaplace (Mi.indicator Φ) τ) +
      κ * (defectLaplace (Lo.indicator r) τ + defectLaplace (Mi.indicator g) τ)
    have hκinv : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    have hmain : ∀ τ : ℂ, 0 < τ.re →
        hamburgerSeries a τ = κ * S τ - κ * β / Real.pi / τ + β + K τ := by
      intro τ hτ
      have eA := hL τ hτ
      have eB := hL0 τ hτ
      have eC := defectLaplace_split hgm.aestronglyMeasurable hgb (Y := 0) le_rfl hτ
      have eD := defectLaplace_split hΦm.aestronglyMeasurable hΦb (Y := 0) le_rfl hτ
      have eF := defectLaplace_indicator_eq (g := g) hΦm.aestronglyMeasurable hΦb
        hrm.aestronglyMeasurable hrb (measurableSet_Iio (a := 0)) (1 - κ⁻¹)
        (fun t ht => hlow t ht) hτ
      simp only [neg_zero] at eC eD
      have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      dsimp only [K]
      rw [show β / (Real.pi * τ) = β / Real.pi / τ by field_simp] at eA
      linear_combination κ * eA + κ * eC + κ * eF - (κ - 1) * eB - (κ - 1) * eD -
        defectLaplace (Lo.indicator Φ) τ * hκinv
    have hper : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a (τ + I) - hamburgerSeries a τ =
        -(κ * β / Real.pi) / (τ + I) - -(κ * β / Real.pi) / τ + (K (τ + I) - K τ) := by
      intro τ hτ
      have hτ' : 0 < (τ + I).re := by simpa using hτ
      have hexp : S (τ + I) = S τ := by
        dsimp only [S]
        refine tsum_congr fun n => ?_
        rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
          -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
            push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [hmain τ hτ, hmain (τ + I) hτ', hexp]
      ring
    have hmidΦ := tendsto_mul_abelMass_indicator_Icc hΦm.aestronglyMeasurable hΦb 0
    have hmidg := tendsto_mul_abelMass_indicator_Icc hgm.aestronglyMeasurable hgb 0
    simp only [neg_zero] at hmidΦ hmidg
    have hrl := tendsto_mul_abelMass_indicator hrm.aestronglyMeasurable hrb hA
      (measurableSet_Iio (a := 0))
    have hb : ∀ {f : ℝ → ℂ}, (∀ t, ‖f t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ)) →
        ∀ s : Set ℝ, ∀ t, ‖s.indicator f t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) :=
      fun hh s t => (norm_indicator_le_norm_self _ t).trans (hh t)
    have hKrad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * K ((ε : ℂ) + (m : ℂ) * I))
        (𝓝[>] 0) (𝓝 0) := by
      intro m
      have t0 := tendsto_mul_defectLaplace_upper_radial hgm.aestronglyMeasurable hgb (Y := 0) le_rfl m
      have t1 := tendsto_mul_defectLaplace_upper_radial hΦm.aestronglyMeasurable hΦb (Y := 0) le_rfl m
      have t2 := tendsto_mul_defectLaplace_radial (hΦm.aestronglyMeasurable.indicator measurableSet_Icc)
        (hb hΦb Mi) hmidΦ m
      have t4 := tendsto_mul_defectLaplace_radial (hrm.aestronglyMeasurable.indicator measurableSet_Iio)
        (hb hrb Lo) hrl m
      have t5 := tendsto_mul_defectLaplace_radial (hgm.aestronglyMeasurable.indicator measurableSet_Icc)
        (hb hgb Mi) hmidg m
      have h := ((t0.const_mul κ).sub ((t1.add t2).const_mul (κ - 1))).add
        ((t4.add t5).const_mul κ)
      simp only [mul_zero, sub_zero, add_zero] at h
      refine h.congr' (Eventually.of_forall fun ε => ?_)
      dsimp only [K]
      ring
    have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) * (K (τ + I) - K τ))
        (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
      intro n₀
      refine tendsto_sub_mul_defect_of_radial ha2 (-(κ * β / Real.pi))
        (fun τ => K (τ + I) - K τ) hper n₀ ?_
      have h := (hKrad (n₀ + 1)).sub (hKrad n₀)
      rw [sub_zero] at h
      refine h.congr' (Eventually.of_forall fun ε => ?_)
      push_cast
      ring_nf
    have hcoef : ∀ n : ℕ, a (n + 1) = 2 * κ * β := by
      intro n
      have h := coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect ha2 (-(κ * β / Real.pi))
        (fun τ => K (τ + I) - K τ) hper hK n
      rw [h]
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
    have h2β : 2 * κ * β = 1 := by rw [← hcoef 0, ha1]
    have hall : ∀ {n : ℕ}, n ≠ 0 → a n = (1 : ℕ → ℂ) n := by
      intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hcoef k, h2β]
      rfl
    have hζ : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s := by
      intro s hs
      rw [← (quantization_dirichletExp_spec hW hs).2, LSeries_congr hall s,
        LSeries_one_eq_riemannZeta hs]
    have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
    have hLam : ∀ s : ℂ, 1 < s.re →
        LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
      intro s hs
      have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hev : riemannZeta =ᶠ[𝓝 s] zetaOf lam := by
        filter_upwards [hopen.mem_nhds hs] with z hz
        exact (hζ z hz).symm
      have hd := (hasDerivAt_zetaOf hsl hs).congr_of_eventuallyEq hev
      have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hd.deriv, hζ s hs]
      field_simp
    have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
      lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
        fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
        (EReal.coe_lt_top 1)
    have habs2 : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
      lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
        fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
        (EReal.coe_lt_top 1)
    have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
        fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact hLam x (by simpa using hx)
    have hcoeffLam : ∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
      intro n hn
      have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
      simp only [lamTwo, if_pos hn] at h
      exact_mod_cast h
    refine ⟨hcoeffLam, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr ?_⟩
    intro f hf hfc
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (hcoeffLam n hn).symm)]
    exact hW f hf hfc
  · exact Or.inr hA

/-- A nonrigid source must retain linear weighted reflection defect on
arbitrarily large dyadic blocks, for every candidate constant phase. -/
theorem source_rigidity_or_block_disorder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (θ : ℝ) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ η : ℝ, 0 < η ∧ ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
        η * T < ∫ t in Ioc T (2 * T), ‖lowerSourceRemainder hW θ (-t)‖ := by
  classical
  rcases source_rigidity_or_abel_disorder hW θ with hR | hA
  · exact Or.inl hR
  right
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have hb : ∀ t : ℝ, ‖lowerSourceRemainder hW θ t‖ ≤ (2 * C) * (1 + |t|) ^ (1 : ℕ) := by
    intro t
    exact (norm_lowerSourceRemainder_le hW θ t).trans (by linarith [(hB t).1, (hB t).2])
  have hzero : ∀ t : ℝ, 0 ≤ t → lowerSourceRemainder hW θ t = 0 := by
    intro t ht
    exact Set.indicator_of_notMem (show t ∉ Iio (0 : ℝ) from not_lt.mpr ht) _
  have hnot : ¬ (∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      ∫ t in Ioc T (2 * T), ‖lowerSourceRemainder hW θ (-t)‖ ≤ η * T) :=
    fun h => hA (tendsto_mul_abelMass_of_blocks (measurable_lowerSourceRemainder hW θ) hb hzero h)
  push Not at hnot
  obtain ⟨η, hη, hlarge⟩ := hnot
  refine ⟨η, hη, fun R => ?_⟩
  obtain ⟨T, hT, hbad⟩ := hlarge (max R 0) (le_max_right _ _)
  exact ⟨T, (le_max_left _ _).trans hT, hbad⟩

end RHTower.WeilWorkSettledPhase
