import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.CutoffArchimedeanEdgesRetainTruncationCoercivity
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ArchimedeanTailMassDiverges

/-!
# The literal kernel of the cutoff archimedean energy

Changing from edge coordinates to mass coordinates gives a symmetric bounded kernel.
Its completed mixed energy is exactly row mass minus off-diagonal action. Product
integrability follows from the finite mass measure and the two source L² norms.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar

theorem integral_massMeasure_prod (H : ℝ × ℝ → ℝ) :
    (∫ p, H p ∂massMeasure.prod massMeasure) =
      ∫ p : ℝ × ℝ, massDensity p.1 * massDensity p.2 * H p ∂volume.prod volume := by
  have hf : Measurable (fun p : ℝ × ℝ => massDensity p.1) :=
    continuous_massDensity.measurable.comp measurable_fst
  have hs : Measurable (fun p : ℝ × ℝ => massDensity p.2) :=
    continuous_massDensity.measurable.comp measurable_snd
  unfold massMeasure
  rw [prod_withDensity_left continuous_massDensity.measurable.ennreal_ofReal,
    integral_weighted (volume.prod (volume.withDensity fun x : ℝ => ENNReal.ofReal (massDensity x))) hf
      (Eventually.of_forall fun p => (massDensity_pos p.1).le) H,
    prod_withDensity_right continuous_massDensity.measurable.ennreal_ofReal,
    integral_weighted (volume.prod volume) hs
      (Eventually.of_forall fun p => (massDensity_pos p.2).le)
      (fun p => massDensity p.1 * H p)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by ring

theorem integrable_massMeasure_prod_iff (H : ℝ × ℝ → ℝ) :
    Integrable H (massMeasure.prod massMeasure) ↔
      Integrable (fun p : ℝ × ℝ => massDensity p.1 * massDensity p.2 * H p)
        (volume.prod volume) := by
  have hf : Measurable (fun p : ℝ × ℝ => massDensity p.1) :=
    continuous_massDensity.measurable.comp measurable_fst
  have hs : Measurable (fun p : ℝ × ℝ => massDensity p.2) :=
    continuous_massDensity.measurable.comp measurable_snd
  unfold massMeasure
  rw [prod_withDensity_left continuous_massDensity.measurable.ennreal_ofReal,
    integrable_weighted_iff (volume.prod (volume.withDensity fun x : ℝ => ENNReal.ofReal (massDensity x))) hf
      (Eventually.of_forall fun p => (massDensity_pos p.1).le) H,
    prod_withDensity_right continuous_massDensity.measurable.ennreal_ofReal,
    integrable_weighted_iff (volume.prod volume) hs
      (Eventually.of_forall fun p => (massDensity_pos p.2).le)
      (fun p => massDensity p.1 * H p)]
  apply integrable_congr
  exact Eventually.of_forall fun p => by ring

/-- The mass-coordinate kernel retains the literal theta-weighted edge density. -/
theorem weighted_archTailKernel (δ x y : ℝ) :
    massDensity x * massDensity y * archTailKernel δ x y =
      if δ ≤ |x - y| then
        archLevyDensity |x - y| * riemannKernelReal x * riemannKernelReal y else 0 := by
  unfold archTailKernel
  split_ifs with h
  · unfold massDensity
    field_simp [ne_of_gt (Real.cosh_pos (x / 2)), ne_of_gt (Real.cosh_pos (y / 2))]
  · ring

/-- Symmetric difference pairing in mass coordinates. -/
def archTailDiffIntegrand (δ : ℝ) (F G : MassSpace) (p : ℝ × ℝ) : ℝ :=
  archTailKernel δ p.1 p.2 * (F p.1 - F p.2) * (G p.1 - G p.2)

theorem measurable_archTailDiffIntegrand (δ : ℝ) (F G : MassSpace) :
    Measurable (archTailDiffIntegrand δ F G) := by
  have hF := (Lp.stronglyMeasurable F).measurable
  have hG := (Lp.stronglyMeasurable G).measurable
  exact ((measurable_archTailKernel_pair δ).mul
    ((hF.comp measurable_fst).sub (hF.comp measurable_snd))).mul
      ((hG.comp measurable_fst).sub (hG.comp measurable_snd))

theorem integrable_archTailDiffIntegrand {δ : ℝ} (hδ : 0 < δ) (F G : MassSpace) :
    Integrable (archTailDiffIntegrand δ F G) (massMeasure.prod massMeasure) := by
  have hF := (Lp.memLp F).integrable_sq
  have hG := (Lp.memLp G).integrable_sq
  have hFx := hF.comp_fst massMeasure
  have hFy := hF.comp_snd massMeasure
  have hGx := hG.comp_fst massMeasure
  have hGy := hG.comp_snd massMeasure
  refine (((hFx.add hFy).add hGx).add hGy).const_mul (archTailBound δ) |>.mono'
    (measurable_archTailDiffIntegrand δ F G).aestronglyMeasurable ?_
  filter_upwards [] with p
  let S := F p.1 ^ 2 + F p.2 ^ 2 + G p.1 ^ 2 + G p.2 ^ 2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hdiff : |(F p.1 - F p.2) * (G p.1 - G p.2)| ≤ S := by
    apply abs_le.mpr
    constructor
    · dsimp only [S]
      nlinarith only [sq_nonneg (F p.1 + F p.2), sq_nonneg (G p.1 + G p.2),
        sq_nonneg ((F p.1 - F p.2) + (G p.1 - G p.2))]
    · dsimp only [S]
      nlinarith only [sq_nonneg (F p.1 + F p.2), sq_nonneg (G p.1 + G p.2),
        sq_nonneg ((F p.1 - F p.2) - (G p.1 - G p.2))]
  change ‖archTailDiffIntegrand δ F G p‖ ≤ archTailBound δ * S
  calc
    _ = archTailKernel δ p.1 p.2 * |(F p.1 - F p.2) * (G p.1 - G p.2)| := by
      rw [archTailDiffIntegrand, mul_assoc, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (archTailKernel_nonneg hδ _ _)]
    _ ≤ archTailKernel δ p.1 p.2 * S :=
      mul_le_mul_of_nonneg_left hdiff (archTailKernel_nonneg hδ _ _)
    _ ≤ archTailBound δ * S := mul_le_mul_of_nonneg_right (archTailKernel_le hδ _ _) hS

theorem archTailDiffIntegrand_swap (δ : ℝ) (F G : MassSpace) (x y : ℝ) :
    archTailDiffIntegrand δ F G (y, x) = archTailDiffIntegrand δ F G (x, y) := by
  simp only [archTailDiffIntegrand, archTailKernel_symm δ y x]
  ring

/-- Symmetric pair integrals become twice the positive-lag integral. -/
private theorem integral_symmetric_pair_positive_lag
    (H : ℝ × ℝ → ℝ) (hH : Integrable H (volume.prod volume))
    (hS : ∀ x y : ℝ, H (y, x) = H (x, y)) :
    (∫ p, H p ∂volume.prod volume) =
      2 * ∫ t in Ioi (0 : ℝ), ∫ x : ℝ, H (x, x + t) := by
  have ht : Integrable (fun p : ℝ × ℝ => H (p.1, p.1 + p.2)) (volume.prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable hH
  have hline : (∫ p, H p ∂volume.prod volume) = ∫ t : ℝ, ∫ x : ℝ, H (x, x + t) := by
    rw [integral_prod _ hH]
    calc
      _ = ∫ x : ℝ, ∫ t : ℝ, H (x, x + t) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (integral_add_left_eq_self (fun y => H (x, y)) x).symm
      _ = _ := integral_integral_swap ht
  let g := fun t : ℝ => ∫ x : ℝ, H (x, x + t)
  have hg : Integrable g := ht.integral_prod_right
  have heven (t : ℝ) : g (-t) = g t := by
    change (∫ x : ℝ, H (x, x + -t)) = ∫ x : ℝ, H (x, x + t)
    rw [← integral_add_right_eq_self (fun x => H (x, x + -t)) t]
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [add_neg_cancel_right] using hS x (x + t)
  have hsplit : (∫ t in Iic (0 : ℝ), g t) + ∫ t in Ioi (0 : ℝ), g t = ∫ t, g t :=
    intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn
  have hrefl : (∫ t in Ioi (0 : ℝ), g (-t)) = ∫ t in Iic (0 : ℝ), g t := by
    simpa only [neg_zero] using integral_comp_neg_Ioi (0 : ℝ) g
  have he : (∫ t in Ioi (0 : ℝ), g (-t)) = ∫ t in Ioi (0 : ℝ), g t := by
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => heven t
  rw [hline]
  change (∫ t, g t) = 2 * ∫ t in Ioi (0 : ℝ), g t
  rw [← hsplit, ← hrefl, he]
  ring

theorem weighted_archTailDiff_positive_lag (δ : ℝ) (F G : MassSpace)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    massDensity x * massDensity (x + t) * archTailDiffIntegrand δ F G (x, x + t) =
      archWeight (t, x) *
        ({e : ℝ × ℝ | δ ≤ e.1}).indicator
          (fun e => difference F e * difference G e) (t, x) := by
  have habs : |x - (x + t)| = t := by
    rw [sub_add_cancel_left, abs_neg, abs_of_pos ht]
  calc
    _ = (massDensity x * massDensity (x + t) * archTailKernel δ x (x + t)) *
        ((F x - F (x + t)) * (G x - G (x + t))) := by
      unfold archTailDiffIntegrand
      ring
    _ = _ := by
      rw [weighted_archTailKernel, habs]
      by_cases hδt : δ ≤ t
      · have hmem : (t, x) ∈ {e : ℝ × ℝ | δ ≤ e.1} := hδt
        simp only [if_pos hδt, indicator_of_mem hmem, archWeight, difference, left, right]
      · have hmem : (t, x) ∉ {e : ℝ × ℝ | δ ≤ e.1} := hδt
        simp only [if_neg hδt, indicator_of_notMem hmem, zero_mul, mul_zero]

/-- Exact conversion of completed cutoff edge energy into the symmetric mass kernel. -/
theorem twice_archTailPair_eq_kernel (δ : ℝ) (hδ : 0 < δ) (p q : SourceGraph) :
    2 * archTailPair δ p q =
      ∫ e, archTailDiffIntegrand δ p.val.fst q.val.fst e ∂massMeasure.prod massMeasure := by
  let H := fun e : ℝ × ℝ => massDensity e.1 * massDensity e.2 *
    archTailDiffIntegrand δ p.val.fst q.val.fst e
  have hH : Integrable H (volume.prod volume) :=
    (integrable_massMeasure_prod_iff _).mp (integrable_archTailDiffIntegrand hδ _ _)
  have hsym (x y : ℝ) : H (y, x) = H (x, y) := by
    dsimp only [H]
    rw [archTailDiffIntegrand_swap]
    ring
  have hsplit := integral_symmetric_pair_positive_lag H hH hsym
  let S := {e : ℝ × ℝ | δ ≤ e.1}
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_fst
  have hi : Integrable (fun e => difference p.val.fst e * difference q.val.fst e)
      (archMeasure + Measure.sum primeMeasure) := integrable_full_difference_mul p q
  have hic : Integrable (S.indicator
      (fun e => difference p.val.fst e * difference q.val.fst e)) archMeasure :=
    hi.left_of_add_measure.indicator hS
  have hiw := (integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae _).mp hic
  have he : (∫ t in Ioi (0 : ℝ), ∫ x : ℝ, H (x, x + t)) = archTailPair δ p q := by
    rw [archTailPair_eq_integral, ← integral_indicator hS, archMeasure,
      integral_weighted archBase measurable_archWeight archWeight_nonneg_ae,
      archBase, integral_prod _ hiw]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    apply integral_congr_ae
    filter_upwards [] with x
    exact weighted_archTailDiff_positive_lag δ p.val.fst q.val.fst ht x
  rw [he] at hsplit
  rw [integral_massMeasure_prod]
  exact hsplit.symm

#print axioms twice_archTailPair_eq_kernel

theorem integrable_archTailKernel_mul {δ : ℝ} (hδ : 0 < δ)
    {H : ℝ × ℝ → ℝ} (hH : Integrable H (massMeasure.prod massMeasure)) :
    Integrable (fun p => archTailKernel δ p.1 p.2 * H p) (massMeasure.prod massMeasure) := by
  apply (hH.norm.const_mul (archTailBound δ)).mono'
    ((measurable_archTailKernel_pair δ).aestronglyMeasurable.mul hH.aestronglyMeasurable)
  filter_upwards [] with p
  change ‖archTailKernel δ p.1 p.2 * H p‖ ≤ archTailBound δ * ‖H p‖
  rw [norm_mul, Real.norm_eq_abs (archTailKernel δ p.1 p.2),
    abs_of_nonneg (archTailKernel_nonneg hδ _ _)]
  exact mul_le_mul_of_nonneg_right (archTailKernel_le hδ _ _) (norm_nonneg _)

/-- One row of the polarized cutoff energy. -/
def archTailPartIntegrand (δ : ℝ) (F G : MassSpace) (p : ℝ × ℝ) : ℝ :=
  archTailKernel δ p.1 p.2 * G p.1 * (F p.1 - F p.2)

theorem integrable_archTailPartIntegrand {δ : ℝ} (hδ : 0 < δ) (F G : MassSpace) :
    Integrable (archTailPartIntegrand δ F G) (massMeasure.prod massMeasure) := by
  have hFG : Integrable (fun x => G x * F x) massMeasure :=
    (Lp.memLp G).integrable_mul (Lp.memLp F)
  have hdiag := hFG.comp_fst massMeasure
  have hcross : Integrable (fun p : ℝ × ℝ => G p.1 * F p.2) (massMeasure.prod massMeasure) :=
    ((Lp.memLp G).integrable (by norm_num)).mul_prod ((Lp.memLp F).integrable (by norm_num))
  refine (integrable_archTailKernel_mul hδ (hdiag.sub hcross)).congr ?_
  filter_upwards [] with p
  change archTailKernel δ p.1 p.2 *
      (G p.1 * F p.1 - G p.1 * F p.2) =
    archTailKernel δ p.1 p.2 * G p.1 * (F p.1 - F p.2)
  ring

theorem archTailDiffIntegrand_eq_parts (δ : ℝ) (F G : MassSpace) (p : ℝ × ℝ) :
    archTailDiffIntegrand δ F G p =
      archTailPartIntegrand δ F G p + archTailPartIntegrand δ F G p.swap := by
  change archTailKernel δ p.1 p.2 * (F p.1 - F p.2) * (G p.1 - G p.2) =
    archTailKernel δ p.1 p.2 * G p.1 * (F p.1 - F p.2) +
      archTailKernel δ p.2 p.1 * G p.2 * (F p.2 - F p.1)
  rw [archTailKernel_symm δ p.2 p.1]
  ring

theorem archTailPart_integral_row (δ : ℝ) (hδ : 0 < δ) (F G : MassSpace) (x : ℝ) :
    (∫ y, archTailPartIntegrand δ F G (x, y) ∂massMeasure) =
      G x * (F x * archTailMass δ x - archTailReadout δ hδ F x) := by
  have hr := (memLp_archTailKernel hδ x).integrable (by norm_num)
  have hm : Integrable (fun y => archTailKernel δ x y * F y) massMeasure := by
    refine (L2.integrable_inner (archTailRow δ hδ x) F).congr ?_
    filter_upwards [(memLp_archTailKernel hδ x).coeFn_toLp] with y hy
    change archTailRow δ hδ x y = archTailKernel δ x y at hy
    change inner ℝ (archTailRow δ hδ x y) (F y) = _
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [archTailReadout_eq_integral]
  calc
    _ = ∫ y, G x * (F x * archTailKernel δ x y - archTailKernel δ x y * F y) ∂massMeasure := by
      apply integral_congr_ae
      filter_upwards [] with y
      unfold archTailPartIntegrand
      ring
    _ = _ := by
      rw [integral_const_mul, integral_sub (hr.const_mul (F x)) hm, integral_const_mul]
      rfl

/-- The completed cutoff energy has the exact row-mass minus off-diagonal expression. -/
theorem archTailPair_eq_mass_sub_readout (δ : ℝ) (hδ : 0 < δ) (p q : SourceGraph) :
    archTailPair δ p q =
      ∫ x, q.val.fst x *
        (p.val.fst x * archTailMass δ x - archTailReadout δ hδ p.val.fst x) ∂massMeasure := by
  have hi := integrable_archTailPartIntegrand hδ p.val.fst q.val.fst
  have his : Integrable (fun e => archTailPartIntegrand δ p.val.fst q.val.fst e.swap)
      (massMeasure.prod massMeasure) := hi.swap
  have hs : (∫ e, archTailDiffIntegrand δ p.val.fst q.val.fst e ∂massMeasure.prod massMeasure) =
      2 * ∫ e, archTailPartIntegrand δ p.val.fst q.val.fst e ∂massMeasure.prod massMeasure := by
    simp_rw [archTailDiffIntegrand_eq_parts]
    rw [integral_add hi his, integral_prod_swap]
    ring
  have he : archTailPair δ p q =
      ∫ e, archTailPartIntegrand δ p.val.fst q.val.fst e ∂massMeasure.prod massMeasure := by
    linarith only [twice_archTailPair_eq_kernel δ hδ p q, hs]
  rw [he, integral_prod _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall (archTailPart_integral_row δ hδ p.val.fst q.val.fst)

theorem integrable_archTail_balance (δ : ℝ) (hδ : 0 < δ) (F G : MassSpace) :
    Integrable (fun x => G x * (F x * archTailMass δ x - archTailReadout δ hδ F x)) massMeasure := by
  exact (integrable_archTailPartIntegrand hδ F G).integral_prod_left.congr
    (Eventually.of_forall (archTailPart_integral_row δ hδ F G))

#print axioms archTailPair_eq_mass_sub_readout

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
