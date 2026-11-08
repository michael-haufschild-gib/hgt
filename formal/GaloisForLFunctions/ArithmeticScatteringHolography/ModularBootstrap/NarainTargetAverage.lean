import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellinConvergence
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTargetBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellinContinuation

/-!
# The actual averaged Narain source

A rescaled square-target heat sum uniformly dominates both target
horocycles. Norm-Fubini identifies the Mellin transform of their actual
average with the explicit mean continuation. The same majorant gives
continuity and exponential decay at large worldsheet height.
-/

open Complex RHTower RHTower.HeckeFactorization MeasureTheory Set Filter Topology Asymptotics
set_option autoImplicit false

noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private abbrev targetMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))

/-- The average of the actual nonvacuum scalar heat sum over both target horocycles. -/
def narainScalarHeatAverage (Y Z : Ioi (0 : ℝ)) (y : ℝ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, ∫ w in Ioc (0 : ℝ) 1,
    narainScalarHeat ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ y

private theorem integrable_target_heat (Y Z : Ioi (0 : ℝ)) {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ =>
      narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩ y) targetMeasure := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩ y) :=
    (measurable_narainScalarHeat_horocycles Y Z).comp (measurable_const.prodMk measurable_id)
  apply (integrable_const ‖narainScalarHeat zI zI (y / targetHorocycleCoercivity Y Z)‖).mono'
    hm.aestronglyMeasurable
  have hmem : ∀ᵐ p ∂targetMeasure, p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
    rw [targetMeasure, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  exact norm_narainScalarHeat_uniform_upper Y Z ⟨hp.1.1.le, hp.1.2⟩
    ⟨hp.2.1.le, hp.2.2⟩ hy

private theorem average_eq_product (Y Z : Ioi (0 : ℝ)) {y : ℝ} (hy : 0 < y) :
    narainScalarHeatAverage Y Z y = ∫ p : ℝ × ℝ,
      narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩ y ∂targetMeasure :=
  (integral_prod _ (integrable_target_heat Y Z hy)).symm

/-- Averaging preserves the uniform square-target majorant. -/
theorem norm_narainScalarHeatAverage_le (Y Z : Ioi (0 : ℝ)) {y : ℝ} (hy : 0 < y) :
    ‖narainScalarHeatAverage Y Z y‖ ≤
      ‖narainScalarHeat zI zI (y / targetHorocycleCoercivity Y Z)‖ := by
  rw [average_eq_product Y Z hy]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _p : ℝ × ℝ,
        ‖narainScalarHeat zI zI (y / targetHorocycleCoercivity Y Z)‖ ∂targetMeasure := by
      apply integral_mono_ae (integrable_target_heat Y Z hy).norm (integrable_const _)
      have hmem : ∀ᵐ p ∂targetMeasure, p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
        rw [targetMeasure, Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      filter_upwards [hmem] with p hp
      exact norm_narainScalarHeat_uniform_upper Y Z ⟨hp.1.1.le, hp.1.2⟩
        ⟨hp.2.1.le, hp.2.2⟩ hy
    _ = _ := by
      rw [integral_const]
      have hmass : targetMeasure.real Set.univ = 1 := by
        rw [measureReal_def, ← Set.univ_prod_univ, targetMeasure, Measure.prod_prod]
        simp [Real.volume_Ioc]
      rw [hmass, one_smul]

/-- Uniform Gaussian domination gives continuity of the actual average. -/
theorem continuousOn_narainScalarHeatAverage (Y Z : Ioi (0 : ℝ)) :
    ContinuousOn (narainScalarHeatAverage Y Z) (Ioi 0) := by
  intro y hy
  have ha : 0 < y / 2 := half_pos hy
  have hK := targetHorocycleCoercivity_pos Y Z
  have hc : ContinuousOn (fun v => ∫ p : ℝ × ℝ,
      narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩ v ∂targetMeasure)
      (Ici (y / 2)) := by
    apply continuousOn_of_dominated
      (bound := fun _ => ‖narainScalarHeat zI zI ((y / 2) / targetHorocycleCoercivity Y Z)‖)
    · intro v hv
      exact (integrable_target_heat Y Z (ha.trans_le hv)).aestronglyMeasurable
    · intro v hv
      have hmem : ∀ᵐ p ∂targetMeasure, p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
        rw [targetMeasure, Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      filter_upwards [hmem] with p hp
      exact (norm_narainScalarHeat_uniform_upper Y Z ⟨hp.1.1.le, hp.1.2⟩
        ⟨hp.2.1.le, hp.2.2⟩ (ha.trans_le hv)).trans
          (antitoneOn_norm_narainScalarHeat zI zI (div_pos ha hK)
            (div_pos (ha.trans_le hv) hK) (div_le_div_of_nonneg_right hv hK.le))
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun p =>
        (continuousOn_narainScalarHeat _ _).mono (fun _ hv => ha.trans_le hv))
  have heq : EqOn (fun v => ∫ p : ℝ × ℝ,
      narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩ v ∂targetMeasure)
      (narainScalarHeatAverage Y Z) (Ici (y / 2)) :=
    fun v hv => (average_eq_product Y Z (ha.trans_le hv)).symm
  exact ((hc.congr heq.symm).continuousAt (Ici_mem_nhds (half_lt_self hy))).continuousWithinAt

theorem locallyIntegrableOn_narainScalarHeatAverage (Y Z : Ioi (0 : ℝ)) :
    LocallyIntegrableOn (narainScalarHeatAverage Y Z) (Ioi 0) :=
  (continuousOn_narainScalarHeatAverage Y Z).locallyIntegrableOn measurableSet_Ioi

/-- The averaged source has an exponential large-height tail. -/
theorem exists_isBigO_narainScalarHeatAverage_exp (Y Z : Ioi (0 : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ narainScalarHeatAverage Y Z =O[atTop]
      (fun y : ℝ => Real.exp (-c * y)) := by
  obtain ⟨B, c, _, hc, hb⟩ := narainScalarHeat_exp_tail zI zI
  have hK := targetHorocycleCoercivity_pos Y Z
  refine ⟨c / targetHorocycleCoercivity Y Z, div_pos hc hK, IsBigO.of_bound B ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (targetHorocycleCoercivity Y Z))] with y hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hyK : targetHorocycleCoercivity Y Z ≤ y := (le_max_right _ _).trans hy
  have h := (norm_narainScalarHeatAverage_le Y Z (zero_lt_one.trans_le hy1)).trans
    (hb _ ((le_div_iff₀ hK).mpr (by simpa only [one_mul] using hyK)))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ B * Real.exp (-(c * (y / targetHorocycleCoercivity Y Z))) := h
    _ = _ := by congr 1; congr 1; ring

/-- The rescaled square-target heat sum controls the joint Mellin norm. -/
theorem integrable_narainScalarHeat_target_mellin (Y Z : Ioi (0 : ℝ))
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ (s - 1) *
      narainScalarHeat ⟨p.2.1, Y.val, Y.property⟩ ⟨p.2.2, Z.val, Z.property⟩ p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod targetMeasure) := by
  have hc : MellinConvergent
      (fun y => narainScalarHeat zI zI (y / targetHorocycleCoercivity Y Z)) s := by
    have h := (MellinConvergent.comp_mul_left
      (inv_pos.mpr (targetHorocycleCoercivity_pos Y Z))).mpr
        (mellinConvergent_narainScalarHeat zI zI hs)
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hm : Measurable (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ (s - 1) *
      narainScalarHeat ⟨p.2.1, Y.val, Y.property⟩ ⟨p.2.2, Z.val, Z.property⟩ p.1) := by
    exact (by fun_prop : Measurable (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ (s - 1))).mul
      (measurable_narainScalarHeat_horocycles Y Z)
  apply (hc.norm.comp_fst targetMeasure).mono' hm.aestronglyMeasurable
  have hmem : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod targetMeasure),
      p.1 ∈ Ioi (0 : ℝ) ∧ p.2.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2.2 ∈ Ioc (0 : ℝ) 1 := by
    rw [targetMeasure, Measure.prod_restrict, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_Ioc.prod measurableSet_Ioc))
  filter_upwards [hmem] with p hp
  simp only [smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_narainScalarHeat_uniform_upper Y Z ⟨hp.2.1.1.le, hp.2.1.2⟩
      ⟨hp.2.2.1.le, hp.2.2.2⟩ hp.1) (norm_nonneg _)

theorem mellinConvergent_narainScalarHeatAverage (Y Z : Ioi (0 : ℝ))
    {s : ℂ} (hs : 1 < s.re) : MellinConvergent (narainScalarHeatAverage Y Z) s := by
  refine (integrable_narainScalarHeat_target_mellin Y Z hs).integral_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [smul_eq_mul, integral_const_mul, ← average_eq_product Y Z hy]

theorem mellin_narainScalarHeatAverage (Y Z : Ioi (0 : ℝ))
    {s : ℂ} (hs : 1 < s.re) :
    mellin (narainScalarHeatAverage Y Z) s = narainMellinMean Y Z (s - 1 / 2) := by
  have hi := integrable_narainScalarHeat_target_mellin Y Z hs
  calc
    mellin (narainScalarHeatAverage Y Z) s =
        ∫ y in Ioi (0 : ℝ), ∫ p : ℝ × ℝ,
          (y : ℂ) ^ (s - 1) *
            narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩ y
              ∂targetMeasure := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      simp only [smul_eq_mul, integral_const_mul, ← average_eq_product Y Z hy]
    _ = ∫ p : ℝ × ℝ, mellin
        (narainScalarHeat ⟨p.1, Y.val, Y.property⟩ ⟨p.2, Z.val, Z.property⟩) s
          ∂targetMeasure := integral_integral_swap hi
    _ = ∫ x in Ioc (0 : ℝ) 1, ∫ w in Ioc (0 : ℝ) 1,
        mellin (narainScalarHeat ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩) s :=
      integral_prod _ hi.integral_prod_right
    _ = _ := integral_mellin_narainScalarHeat Y Z hs

#print axioms continuousOn_narainScalarHeatAverage
#print axioms exists_isBigO_narainScalarHeatAverage_exp
#print axioms mellinConvergent_narainScalarHeatAverage
#print axioms mellin_narainScalarHeatAverage
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
