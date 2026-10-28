import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticSchurComplementHasCertifiedErrorBounds
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# Weil isometry and source-graph escape

Every nonzero compact source has a translation orbit whose squared graph norm
dominates every exponential rate. The full Weil value is constant along this
orbit. Exponential amplitude renormalization therefore cannot supply uniform
source-graph control.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar Zeta23

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics ArithmeticIndexDescent

/-- Translation of the literal compact arithmetic test, with its domain retained. -/
def sourceTranslate (t : ℝ) (f : realTests) : realTests :=
  ⟨scaleShift t f.1, scaleShift_mem t f.2⟩

/-- The translated test in the original complete source graph. -/
def translatedSourceGraph (f : realTests) (t : ℝ) : SourceGraph :=
  realTestGraphLift (sourceTranslate t f)

theorem sectionMass_sourceTranslate (t : ℝ) (f : realTests) :
    sectionMass (sourceTranslate t f).1 = sectionMass f.1 := by
  change (∫ u, f.1 (u - t) ^ 2) = ∫ u, f.1 u ^ 2
  exact integral_sub_right_eq_self (fun u => f.1 u ^ 2) t

/-- The full Weil form, including Gamma and both poles, is unchanged. -/
theorem weilForm_translatedSourceGraph (f : realTests) (t : ℝ) :
    weilForm (translatedSourceGraph f t) = realWeilForm f f := by
  rw [translatedSourceGraph, weilForm_realTestGraphLift]
  change weilPair (scaleShift t f.1) (scaleShift t f.1) = weilPair f.1 f.1
  exact weilPair_scaleShift_same t f.1 f.1

private theorem compact_square_integrable (f : realTests) :
    Integrable (fun u => f.1 u ^ 2) := by
  have hs : HasCompactSupport (fun u : ℝ => f.1 u ^ 2) :=
    f.2.2.comp_left (g := fun v : ℝ => v ^ 2) (by norm_num)
  exact (f.2.1.continuous.pow 2).integrable_of_hasCompactSupport hs

private theorem compact_weighted_square_integrable (f : realTests) :
    Integrable (fun u => f.1 u ^ 2 * sourceGraphMassWeight u) := by
  have hs : HasCompactSupport (fun u : ℝ => f.1 u ^ 2) :=
    f.2.2.comp_left (g := fun v : ℝ => v ^ 2) (by norm_num)
  exact ((f.2.1.continuous.pow 2).mul continuous_sourceGraphMassWeight).integrable_of_hasCompactSupport
    hs.mul_right

private theorem sectionMass_pos (f : realTests) (hf : f ≠ 0) :
    0 < sectionMass f.1 := by
  have hex : ∃ u, f.1 u ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply Subtype.ext
    funext u
    exact h u
  obtain ⟨u, hu⟩ := hex
  exact integral_pos_of_integrable_nonneg_nonzero (f.2.1.continuous.pow 2)
    (compact_square_integrable f) (fun v => sq_nonneg _) (pow_ne_zero 2 hu)

/-- Theta arithmetic makes the exact source weight dominate every exponential. -/
theorem exists_exp_le_sourceGraphMassWeight (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ,
      Real.exp (B * |u|) ≤ K * sourceGraphMassWeight u := by
  obtain ⟨C, hC, hdecay⟩ := RHTower.exists_norm_riemannPhiKernel_le_exp hB
  have hK : 0 < C + 1 := by linarith only [hC]
  refine ⟨C + 1, hK, fun u => ?_⟩
  have hphi : riemannKernelReal u ≤ (C + 1) * Real.exp (-(B * |u|)) := by
    have h := hdecay u
    rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos u)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith only)
      (Real.exp_pos _).le)
  rw [sourceGraphMassWeight, ← mul_div_assoc, le_div_iff₀ (riemannKernelReal_pos u)]
  calc
    Real.exp (B * |u|) * riemannKernelReal u ≤
        Real.exp (B * |u|) * ((C + 1) * Real.exp (-(B * |u|))) :=
      mul_le_mul_of_nonneg_left hphi (Real.exp_pos _).le
    _ = C + 1 := by
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ (C + 1) * Real.cosh (u / 2) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.one_le_cosh (u / 2)) hK.le

/-- Literal weighted source mass is one component of the complete graph norm. -/
theorem weightedMass_le_graph_norm_sq (f : realTests) :
    weightedSectionMass sourceGraphMassWeight f ≤ ‖realTestGraphLift f‖ ^ 2 := by
  rw [← norm_realTestGraphLift_source_sq_eq_weightedMass]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_source_le_graph _) 2

private theorem shifted_square_mass_bound (f : realTests) (B R K : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hweight : ∀ u, Real.exp (B * |u|) ≤ K * sourceGraphMassWeight u)
    (hsupport : ∀ u, f.1 u ≠ 0 → |u| ≤ R) (t : ℝ) :
    Real.exp (B * (|t| - R)) * sectionMass f.1 ≤
      K * ‖translatedSourceGraph f t‖ ^ 2 := by
  let g := sourceTranslate t f
  have hpoint (u : ℝ) :
      g.1 u ^ 2 * Real.exp (B * (|t| - R)) ≤
        K * (g.1 u ^ 2 * sourceGraphMassWeight u) := by
    by_cases hu : g.1 u = 0
    · simp only [hu, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, le_refl]
    · have hr : |u - t| ≤ R := hsupport (u - t) hu
      have ht : |t| ≤ |u| + |u - t| := by
        calc
          |t| = |u - (u - t)| := by congr 1; ring
          _ ≤ |u| + |u - t| := abs_sub u (u - t)
      have he : Real.exp (B * (|t| - R)) ≤ Real.exp (B * |u|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith only [hr, ht]) hB)
      have hm := mul_le_mul_of_nonneg_left (he.trans (hweight u)) (sq_nonneg (g.1 u))
      simpa only [mul_left_comm] using hm
  calc
    _ = ∫ u, g.1 u ^ 2 * Real.exp (B * (|t| - R)) := by
      rw [integral_mul_const]
      change _ = sectionMass (sourceTranslate t f).1 * _
      rw [sectionMass_sourceTranslate]
      ring
    _ ≤ ∫ u, K * (g.1 u ^ 2 * sourceGraphMassWeight u) :=
      integral_mono ((compact_square_integrable g).mul_const _)
        ((compact_weighted_square_integrable g).const_mul K) hpoint
    _ = K * weightedSectionMass sourceGraphMassWeight g := integral_const_mul _ _
    _ ≤ K * ‖translatedSourceGraph f t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (weightedMass_le_graph_norm_sq g) hK

/-- Every nonzero compact source orbit dominates every exponential graph rate. -/
theorem translatedSourceGraph_all_exponential_lower_bounds (f : realTests) (hf : f ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * Real.exp (B * |t|) ≤ ‖translatedSourceGraph f t‖ ^ 2 := by
  obtain ⟨K, hK, hweight⟩ := exists_exp_le_sourceGraphMassWeight B hB
  obtain ⟨R, _, hR⟩ := f.2.2.isBounded.exists_pos_norm_le
  have hsupport : ∀ u, f.1 u ≠ 0 → |u| ≤ R := by
    intro u hu
    simpa only [Real.norm_eq_abs] using hR u (subset_tsupport f.1 hu)
  refine ⟨sectionMass f.1 * Real.exp (-(B * R)) / K,
    div_pos (mul_pos (sectionMass_pos f hf) (Real.exp_pos _)) hK, fun t => ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  calc
    sectionMass f.1 * Real.exp (-(B * R)) * Real.exp (B * |t|) =
        Real.exp (B * (|t| - R)) * sectionMass f.1 := by
      rw [mul_assoc, ← Real.exp_add, show -(B * R) + B * |t| = B * (|t| - R) by ring]
      exact mul_comm _ _
    _ ≤ ‖translatedSourceGraph f t‖ ^ 2 * K := by
      simpa only [mul_comm K] using shifted_square_mass_bound f B R K hB hK.le hweight hsupport t

/-- Removing the coercive section cannot absorb graph escape at bounded Weil energy. -/
theorem graph_norm_sq_le_weil_add_residual (x : SourceGraph) :
    ‖x‖ ^ 2 ≤ 4 * weilForm x +
      (4 * weilBilinConst + 2) * ‖arithmeticResidual x‖ ^ 2 := by
  have htri : ‖x‖ ≤ ‖fixedLogCellWeilProjection x‖ + ‖arithmeticResidual x‖ := by
    calc
      ‖x‖ = ‖fixedLogCellWeilProjection x + arithmeticResidual x‖ := by
        congr 1
        rw [arithmeticResidual_apply]
        abel
      _ ≤ _ := norm_add_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg x) htri 2
  have hcoer := norm_closedFixedLogCellGraph_le_weil
    ⟨fixedLogCellWeilProjection x, fixedLogCellWeilProjection_mem x⟩
  change ‖fixedLogCellWeilProjection x‖ ^ 2 ≤
    2 * weilForm (fixedLogCellWeilProjection x) at hcoer
  have hsum : weilForm x = weilForm (arithmeticResidual x) +
      weilForm (fixedLogCellWeilProjection x) := by
    simpa only [ZeroMemClass.coe_zero, sub_zero] using
      arithmetic_trial_energy_decomposition x (0 : closedFixedLogCellGraph)
  have hres : -weilForm (arithmeticResidual x) ≤
      weilBilinConst * ‖arithmeticResidual x‖ ^ 2 := by
    rw [weilForm_eq_weilBilin, pow_two]
    exact (neg_le_abs _).trans (abs_weilBilin_le _ _)
  nlinarith only [hsq, hcoer, hsum, hres,
    sq_nonneg (‖fixedLogCellWeilProjection x‖ - ‖arithmeticResidual x‖)]

/-- The all-rate translation growth persists in the actual arithmetic residual. -/
theorem translated_residual_all_exponential_lower_bounds (f : realTests) (hf : f ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * Real.exp (B * |t|) - 4 * realWeilForm f f ≤
        (4 * weilBilinConst + 2) *
          ‖arithmeticResidual (translatedSourceGraph f t)‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := translatedSourceGraph_all_exponential_lower_bounds f hf B hB
  refine ⟨c, hc, fun t => ?_⟩
  have hr := graph_norm_sq_le_weil_add_residual (translatedSourceGraph f t)
  rw [weilForm_translatedSourceGraph] at hr
  linarith only [hbound t, hr]

/-- Every scalar renormalization has an exponentially vanishing energy-to-graph ratio. -/
theorem scalarRenormalization_energy_graph_bound (f : realTests) (hf : f ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ t a : ℝ,
      c * Real.exp (B * |t|) * |weilForm (a • translatedSourceGraph f t)| ≤
        |realWeilForm f f| * ‖a • translatedSourceGraph f t‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := translatedSourceGraph_all_exponential_lower_bounds f hf B hB
  refine ⟨c, hc, fun t a => ?_⟩
  have hW : weilForm (a • translatedSourceGraph f t) = a ^ 2 * realWeilForm f f := by
    rw [weilForm_eq_weilBilin, ← inner_graphWeilOperator, map_smul,
      inner_smul_graph,
      ← real_inner_comm (graphWeilOperator (translatedSourceGraph f t))
        (a • translatedSourceGraph f t), inner_smul_graph,
      ← real_inner_comm (translatedSourceGraph f t) (graphWeilOperator (translatedSourceGraph f t)),
      inner_graphWeilOperator,
      ← weilForm_eq_weilBilin, weilForm_translatedSourceGraph]
    ring
  rw [hW, abs_mul, abs_of_nonneg (sq_nonneg a), norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    c * Real.exp (B * |t|) * (a ^ 2 * |realWeilForm f f|) =
        (a ^ 2 * |realWeilForm f f|) * (c * Real.exp (B * |t|)) := by ring
    _ ≤ (a ^ 2 * |realWeilForm f f|) * ‖translatedSourceGraph f t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hbound t) (mul_nonneg (sq_nonneg a) (abs_nonneg _))
    _ = |realWeilForm f f| * (a ^ 2 * ‖translatedSourceGraph f t‖ ^ 2) := by ring

/-- Any fixed exponential amplitude still leaves an exponentially escaping graph orbit. -/
theorem exponentialRenormalization_graph_lower (f : realTests) (hf : f ≠ 0) (a : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * Real.exp |t| ≤
        ‖Real.exp (-(a * |t|)) • translatedSourceGraph f t‖ ^ 2 := by
  let B := 2 * |a| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨c, hc, hbound⟩ := translatedSourceGraph_all_exponential_lower_bounds f hf B hB
  refine ⟨c, hc, fun t => ?_⟩
  have hrate : 1 ≤ B - 2 * a := by
    dsimp [B]
    linarith only [le_abs_self a]
  have he : Real.exp |t| ≤ Real.exp ((B - 2 * a) * |t|) := by
    apply Real.exp_le_exp.mpr
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrate (abs_nonneg t)
  have hexp : Real.exp (-(a * |t|)) ^ 2 * Real.exp (B * |t|) =
      Real.exp ((B - 2 * a) * |t|) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  calc
    c * Real.exp |t| ≤ c * Real.exp ((B - 2 * a) * |t|) :=
      mul_le_mul_of_nonneg_left he hc.le
    _ = Real.exp (-(a * |t|)) ^ 2 * (c * Real.exp (B * |t|)) := by
      rw [mul_left_comm, hexp]
    _ ≤ Real.exp (-(a * |t|)) ^ 2 * ‖translatedSourceGraph f t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)

/-- Every translated compact orbit eventually leaves the fixed graph-coercive carrier. -/
theorem translatedSourceGraph_eventually_outside_carrier (f : realTests) (hf : f ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ |t| →
      translatedSourceGraph f t ∉ closedFixedLogCellGraph := by
  obtain ⟨c, hc, hbound⟩ := translatedSourceGraph_all_exponential_lower_bounds f hf 1 zero_le_one
  refine ⟨max 1 ((2 * realWeilForm f f + 1) / c),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht hmem
  have hct : 2 * realWeilForm f f + 1 ≤ c * |t| := by
    have h := (div_le_iff₀ hc).mp ((le_max_right _ _).trans ht)
    simpa only [mul_comm c] using h
  have hexp : |t| ≤ Real.exp |t| :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have he := mul_le_mul_of_nonneg_left hexp hc.le
  have hg := hbound t
  rw [one_mul] at hg
  have hk := norm_closedFixedLogCellGraph_le_weil ⟨translatedSourceGraph f t, hmem⟩
  change ‖translatedSourceGraph f t‖ ^ 2 ≤ 2 * weilForm (translatedSourceGraph f t) at hk
  rw [weilForm_translatedSourceGraph] at hk
  linarith only [hct, he, hg, hk]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.translatedSourceGraph_all_exponential_lower_bounds
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exponentialRenormalization_graph_lower
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.translated_residual_all_exponential_lower_bounds
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.scalarRenormalization_energy_graph_bound
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.translatedSourceGraph_eventually_outside_carrier
