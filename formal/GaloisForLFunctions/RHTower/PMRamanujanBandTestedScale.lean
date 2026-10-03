import GaloisForLFunctions.RHTower.PMRamanujanBandMovingMellin
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.MellinTransform

/-!
# Actual tested moving-band scale transform

The literal source is measurable and locally bounded. A proposed norm limit of
its normalized complete band implies the global bound needed for full cutoff-
frequency Fubini and holomorphy of the tested scale transform. The initial
zeta-cleared arithmetic identity retains the complete source. These results do
not assert convergence, spectral escape, or a small-damping energy ceiling.
-/

open MeasureTheory Set Complex Filter Topology
noncomputable section
namespace RHTower

theorem pm_inner_phaseUnitary_eq_integral (h F : Lp ℂ 2 (volume : Measure ℝ)) (a : ℝ) :
    inner ℂ h (MellinL2.fourierPhaseMulUnitary a F) =
      ∫ τ : ℝ, MellinL2.fourierPhase a τ * ((starRingEnd ℂ) (h τ) * F τ) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MellinL2.fourierPhaseMulAux_ae a F] with τ hτ
  change (MellinL2.fourierPhaseMulUnitary a F : ℝ → ℂ) τ = _ at hτ
  rw [hτ, RCLike.inner_apply]
  ring

theorem continuous_pm_inner_phaseUnitary (h F : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun a : ℝ => inner ℂ h (MellinL2.fourierPhaseMulUnitary a F)) := by
  have hf : Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) * F τ) := by
    simpa only [RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) h F)
  simp_rw [pm_inner_phaseUnitary_eq_integral]
  apply continuous_of_dominated
    (bound := fun τ : ℝ => ‖(starRingEnd ℂ) (h τ) * F τ‖)
  · intro a
    exact (MellinL2.fourierPhase_continuous a).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · intro a
    exact .of_forall fun τ => by simp
  · exact hf.norm
  · exact .of_forall fun τ => by
      have hp : Continuous (fun a : ℝ => MellinL2.fourierPhase a τ) := by
        have he : (fun a : ℝ => MellinL2.fourierPhase a τ) = MellinL2.fourierPhase τ := by
          funext a
          simp only [MellinL2.fourierPhase, mul_comm]
        rw [he]
        exact MellinL2.fourierPhase_continuous τ
      exact hp.mul_const _

/-- The bounded frequency test applied to the actual complete moving band. -/
def pmRamanujanBandTestedScale (ε : ℝ) (h : Lp ℂ 2 (volume : Measure ℝ)) (X : ℝ) : ℂ :=
  inner ℂ h (pmRamanujanMovingBandMellinVector ε X)

theorem measurable_pmRamanujanBandTestedScale (ε : ℝ) (h : Lp ℂ 2 (volume : Measure ℝ)) :
    Measurable (pmRamanujanBandTestedScale ε h) := by
  let V : ℕ × ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun p =>
    if hp : 1 ≤ p.1 then pmRamanujanBandMellinVector ε p.1 p.2 hp else 0
  have hm : Measurable (fun p : ℝ × (ℕ × ℕ) =>
      inner ℂ h (MellinL2.fourierPhaseMulUnitary p.1 (V p.2))) :=
    measurable_from_prod_countable_left fun p => (continuous_pm_inner_phaseUnitary h (V p)).measurable
  have hp : Measurable (fun X : ℝ => (Real.log X/(2*Real.pi),(⌊X⌋₊,⌊2*X⌋₊))) := by
    fun_prop
  have hc : Measurable (fun X : ℝ => ((X^ε : ℝ) : ℂ)) := by fun_prop
  have hh := hc.mul (hm.comp hp)
  convert hh using 1
  funext X
  simp only [pmRamanujanBandTestedScale, pmRamanujanMovingBandMellinVector,
    pmRamanujanNormalizedBandMellinVector, pmRamanujanNaturalBandMellinVector,
    map_smul, inner_smul_right, V]
  rfl

theorem exists_bound_pmRamanujanMovingBandMellinVector_on_Icc
    {ε : ℝ} (hε : 0 ≤ ε) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X ∈ Icc (1 : ℝ) B,
      ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C := by
  let V : ℕ × ℕ → Lp ℂ 2 (volume : Measure ℝ) := fun p =>
    if hp : 1 ≤ p.1 then pmRamanujanBandMellinVector ε p.1 p.2 hp else 0
  let J := (Finset.Iic ⌊B⌋₊).product (Finset.Iic ⌊2*B⌋₊)
  let C := (max B 1)^ε * ∑ p ∈ J, ‖V p‖
  have hsum : 0 ≤ ∑ p ∈ J, ‖V p‖ := Finset.sum_nonneg fun p _ => norm_nonneg _
  refine ⟨C, mul_nonneg (Real.rpow_nonneg (by positivity) _) hsum, ?_⟩
  intro X hX
  have hmem : (⌊X⌋₊,⌊2*X⌋₊) ∈ J := by
    exact Finset.mem_product.mpr ⟨Finset.mem_Iic.mpr (Nat.floor_mono hX.2),
      Finset.mem_Iic.mpr (Nat.floor_mono (by linarith [hX.2]))⟩
  have hv : ‖V (⌊X⌋₊,⌊2*X⌋₊)‖ ≤ ∑ p ∈ J, ‖V p‖ :=
    Finset.single_le_sum (fun p _ => norm_nonneg _) hmem
  have hr : X^ε ≤ (max B 1)^ε :=
    Real.rpow_le_rpow (by linarith [hX.1]) (hX.2.trans (le_max_left _ _)) hε
  rw [pmRamanujanMovingBandMellinVector, (MellinL2.fourierPhaseMulUnitary _).norm_map,
    pmRamanujanNormalizedBandMellinVector, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hX.1]) _)]
  exact mul_le_mul hr hv (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

theorem measurable_pmRamanujanMovingBandMellinTrace_guard (ε : ℝ) :
    Measurable (fun p : ℝ × ℝ => if 1 ≤ ⌊p.1⌋₊ then
      pmRamanujanMovingBandMellinTrace ε p.1 p.2 else 0) := by
  let T : ℝ × (ℕ × ℕ) → ℂ := fun p => if hn : 1 ≤ p.2.1 then
    pmRamanujanBandMellinTrace ε p.2.1 p.2.2 p.1 else 0
  have ht : Measurable T := by
    apply measurable_from_prod_countable_left
    intro p
    by_cases hn : 1 ≤ p.1
    · simpa only [T, dif_pos hn] using
        (continuous_pmRamanujanBandMellinTrace ε hn (Y := p.2)).measurable
    · simpa only [T, dif_neg hn] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))
  have hi : Measurable (fun p : ℝ × ℝ => (p.2,(⌊p.1⌋₊,⌊2*p.1⌋₊))) := by fun_prop
  have hp : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)^((ε : ℂ)+(p.2 : ℂ)*I)) := by fun_prop
  convert hp.mul (ht.comp hi) using 1
  funext p
  by_cases hn : 1 ≤ ⌊p.1⌋₊ <;> simp [hn, T, pmRamanujanMovingBandMellinTrace]

theorem integrable_pmRamanujanMovingBandMellinTrace_pair (ε : ℝ)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {X : ℝ} (hX : 1 ≤ X) :
    Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) *
      pmRamanujanMovingBandMellinTrace ε X τ) := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) h
    (pmRamanujanMovingBandMellinVector ε X)
  apply hi.congr
  filter_upwards [pmRamanujanMovingBandMellinVector_ae ε hX] with τ hτ
  rw [hτ, RCLike.inner_apply]
  exact mul_comm _ _

theorem pmRamanujanBandTestedScale_eq_integral (ε : ℝ)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {X : ℝ} (hX : 1 ≤ X) :
    pmRamanujanBandTestedScale ε h X =
      ∫ τ : ℝ, (starRingEnd ℂ) (h τ) * pmRamanujanMovingBandMellinTrace ε X τ := by
  rw [pmRamanujanBandTestedScale, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pmRamanujanMovingBandMellinVector_ae ε hX] with τ hτ
  rw [hτ, RCLike.inner_apply]
  exact mul_comm _ _

theorem exists_bound_pmRamanujanMovingBandMellinVector_of_tendsto
    {ε : ℝ} (hε : 0 ≤ ε) {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X ∈ Ici (1 : ℝ),
      ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C := by
  have he : ∀ᶠ X : ℝ in atTop, ‖pmRamanujanNormalizedBandMellinVector ε X‖ < ‖F‖+1 :=
    hc.norm.eventually (gt_mem_nhds (by linarith : ‖F‖ < ‖F‖+1))
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  obtain ⟨C,hC,hbound⟩ := exists_bound_pmRamanujanMovingBandMellinVector_on_Icc hε B
  refine ⟨max C (‖F‖+1), hC.trans (le_max_left _ _), ?_⟩
  intro X hX
  by_cases hXB : X ≤ B
  · exact (hbound X ⟨hX,hXB⟩).trans (le_max_left _ _)
  · rw [pmRamanujanMovingBandMellinVector, (MellinL2.fourierPhaseMulUnitary _).norm_map]
    exact (hB X (le_of_not_ge hXB)).le.trans (le_max_right _ _)

private theorem pmbp_integral_norm_pair_le (h F : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ τ : ℝ, ‖(starRingEnd ℂ) (h τ) * F τ‖) ≤ ‖h‖^2+‖F‖^2 := by
  have hh := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).mp (Lp.memLp h)
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hp : Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) * F τ) := by
    simpa only [RCLike.inner_apply, mul_comm] using
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) h F)
  calc
    _ ≤ ∫ τ : ℝ, ‖h τ‖^2+‖F τ‖^2 := by
      apply integral_mono hp.norm (hh.add hf)
      intro τ
      simp only [Pi.add_apply, norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖h τ‖-‖F τ‖), mul_nonneg (norm_nonneg (h τ)) (norm_nonneg (F τ))]
    _ = _ := by
      rw [integral_add hh hf, ← GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral,
        ← GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral]

private theorem pmbp_integrable_product (ε : ℝ) (h : Lp ℂ 2 (volume : Measure ℝ))
    {C : ℝ}
    (hb : ∀ X ∈ Ici (1 : ℝ), ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C)
    {z : ℂ} (hz : 1/2 < z.re) :
    Integrable (fun p : ℝ × ℝ => (p.1 : ℂ)^(-z-(1/2 : ℂ)) *
      ((starRingEnd ℂ) (h p.2) * (if 1 ≤ ⌊p.1⌋₊ then
        pmRamanujanMovingBandMellinTrace ε p.1 p.2 else 0)))
      ((volume.restrict (Ici 1)).prod volume) := by
  let G : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ)^(-z-(1/2 : ℂ)) *
    ((starRingEnd ℂ) (h p.2) * (if 1 ≤ ⌊p.1⌋₊ then
      pmRamanujanMovingBandMellinTrace ε p.1 p.2 else 0))
  have hm : AEStronglyMeasurable G ((volume.restrict (Ici 1)).prod volume) := by
    have hp : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)^(-z-(1/2 : ℂ))) := by fun_prop
    exact hp.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable h).star.comp_snd.mul
      (measurable_pmRamanujanMovingBandMellinTrace_guard ε).aestronglyMeasurable)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
    simpa only [G, if_pos ((Nat.one_le_floor_iff X).mpr hX)] using
      (integrable_pmRamanujanMovingBandMellinTrace_pair ε h hX).const_mul
        ((X : ℂ)^(-z-(1/2 : ℂ)))
  · have hd : IntegrableOn (fun X : ℝ => X^(-z.re-1/2)*(‖h‖^2+C^2)) (Ici 1) :=
      ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
        (integrableOn_Ioi_rpow_of_lt (by linarith : -z.re-1/2 < -1) one_pos)).mul_const _
    apply hd.mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
    have hp : ‖(X : ℂ)^(-z-(1/2 : ℂ))‖ = X^(-z.re-1/2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le zero_lt_one hX)]
      congr 1
      simp
    have he : (∫ τ : ℝ, ‖G (X,τ)‖) = X^(-z.re-1/2) *
        ∫ τ : ℝ, ‖(starRingEnd ℂ) (h τ) * (pmRamanujanMovingBandMellinVector ε X) τ‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [pmRamanujanMovingBandMellinVector_ae ε hX] with τ hτ
      simp only [G, if_pos ((Nat.one_le_floor_iff X).mpr hX), norm_mul, hp,
        hτ, pmRamanujanMovingBandMellinTrace]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), he]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_le_one.trans hX) _)
    exact (pmbp_integral_norm_pair_le h _).trans
      (add_le_add_right (pow_le_pow_left₀ (norm_nonneg _) (hb X hX) 2) _)

theorem pmRamanujanBandTestedScale_integral_swap (ε : ℝ)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {C : ℝ}
    (hb : ∀ X ∈ Ici (1 : ℝ), ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C)
    {z : ℂ} (hz : 1/2 < z.re) :
    (∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X) =
      ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
        ∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) *
          pmRamanujanMovingBandMellinTrace ε X τ := by
  calc
    _ = ∫ X in Ici (1 : ℝ), ∫ τ : ℝ, (X : ℂ)^(-z-(1/2 : ℂ)) *
        ((starRingEnd ℂ) (h τ) * (if 1 ≤ ⌊X⌋₊ then
          pmRamanujanMovingBandMellinTrace ε X τ else 0)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
      rw [pmRamanujanBandTestedScale_eq_integral ε h hX, ← integral_const_mul]
      simp only [if_pos ((Nat.one_le_floor_iff X).mpr hX)]
    _ = _ := by
      rw [integral_integral_swap (pmbp_integrable_product ε h hb hz)]
      apply integral_congr_ae
      exact .of_forall fun τ => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
        simp only [if_pos ((Nat.one_le_floor_iff X).mpr hX)]
        ring

private def pmbp_reciprocal (ε : ℝ) (h : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (pmRamanujanBandTestedScale ε h) t⁻¹

private theorem pmbp_reciprocal_bounds (ε : ℝ) (h : Lp ℂ 2 (volume : Measure ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ X ∈ Ici (1 : ℝ), ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C) :
    LocallyIntegrableOn (pmbp_reciprocal ε h) (Ioi 0) ∧
      (pmbp_reciprocal ε h =O[atTop] fun t : ℝ => Real.exp (-1*t)) ∧
      (pmbp_reciprocal ε h =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t^(-(0 : ℝ))) := by
  have hm : Measurable (pmbp_reciprocal ε h) :=
    ((measurable_pmRamanujanBandTestedScale ε h).indicator measurableSet_Ioi).comp measurable_inv
  have hbound : ∀ t : ℝ, ‖pmbp_reciprocal ε h t‖ ≤ ‖h‖*C := by
    intro t
    by_cases ht : 1 < t⁻¹
    · rw [pmbp_reciprocal, indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from ht)]
      exact (norm_inner_le_norm h _).trans (mul_le_mul_of_nonneg_left
        (hb t⁻¹ ht.le) (norm_nonneg _))
    · rw [pmbp_reciprocal, indicator_of_notMem (show t⁻¹ ∉ Ioi (1 : ℝ) from ht), norm_zero]
      exact mul_nonneg (norm_nonneg _) hC
  refine ⟨(locallyIntegrableOn_const (‖h‖*C)).mono hm.aestronglyMeasurable
    (.of_forall fun t => (hbound t).trans (le_abs_self _)), ?_, ?_⟩
  · apply Asymptotics.IsBigO.of_bound 0
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht' : ¬ 1 < t⁻¹ := not_lt.mpr (inv_le_one_of_one_le₀ ht)
    simp [pmbp_reciprocal, ht']
  · apply Asymptotics.IsBigO.of_bound (‖h‖*C)
    exact .of_forall fun t => by simpa using hbound t

private theorem pmbp_mellin_reciprocal_eq (ε : ℝ)
    (h : Lp ℂ 2 (volume : Measure ℝ)) (z : ℂ) :
    mellin (pmbp_reciprocal ε h) (z-(1/2 : ℂ)) =
      ∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X := by
  rw [show mellin (pmbp_reciprocal ε h) (z-(1/2 : ℂ)) =
      mellin ((Ioi (1 : ℝ)).indicator (pmRamanujanBandTestedScale ε h)) (-(z-(1/2 : ℂ))) from
        mellin_comp_inv ((Ioi (1 : ℝ)).indicator (pmRamanujanBandTestedScale ε h)) _]
  change (∫ X in Ioi (0 : ℝ), (X : ℂ)^(-(z-(1/2 : ℂ))-1) *
    (Ioi (1 : ℝ)).indicator (pmRamanujanBandTestedScale ε h) X) = _
  rw [show -(z-(1/2 : ℂ))-1 = -z-(1/2 : ℂ) by ring,
    integral_Ici_eq_integral_Ioi]
  calc
    _ = ∫ X in Ioi (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) *
        (Ioi (1 : ℝ)).indicator (pmRamanujanBandTestedScale ε h) X := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
      intro X hX
      rw [indicator_of_notMem hX.2, mul_zero]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro X hX
      dsimp only
      rw [indicator_of_mem hX]

/-- Holomorphy of the actual tested scale integral, derived from the proposed convergence
inside the spectral-escape contradiction. No separate source-regularity premise is used. -/
theorem differentiableAt_pmRamanujanBandTestedScale_integral_of_tendsto
    {ε : ℝ} (hε : 0 ≤ ε) {F : Lp ℂ 2 (volume : Measure ℝ)}
    (hc : Tendsto (pmRamanujanNormalizedBandMellinVector ε) atTop (𝓝 F))
    (h : Lp ℂ 2 (volume : Measure ℝ)) {z : ℂ} (hz : 1/2 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ X in Ici (1 : ℝ),
      (X : ℂ)^(-w-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X) z := by
  obtain ⟨C,hC,hb⟩ := exists_bound_pmRamanujanMovingBandMellinVector_of_tendsto hε hc
  obtain ⟨hli,htop,hbot⟩ := pmbp_reciprocal_bounds ε h hC hb
  have hd := mellin_differentiableAt_of_isBigO_rpow_exp one_pos hli htop hbot
    (show (0 : ℝ) < (z-(1/2 : ℂ)).re by simp; linarith)
  have hh := hd.comp z (differentiableAt_id.sub_const (1/2 : ℂ))
  simpa only [Function.comp_def, id_eq, pmbp_mellin_reciprocal_eq] using hh

theorem integrableOn_pmRamanujanBandTestedScale_integrand (ε : ℝ)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {C : ℝ}
    (hb : ∀ X ∈ Ici (1 : ℝ), ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C)
    {z : ℂ} (hz : 1/2 < z.re) :
    IntegrableOn (fun X : ℝ => (X : ℂ)^(-z-(1/2 : ℂ)) *
      pmRamanujanBandTestedScale ε h X) (Ici 1) := by
  apply (pmbp_integrable_product ε h hb hz).integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with X hX
  rw [pmRamanujanBandTestedScale_eq_integral ε h hX, ← integral_const_mul]
  simp only [if_pos ((Nat.one_le_floor_iff X).mpr hX)]

theorem pmRamanujanBandTestedScale_cleared_eq {ε : ℝ} (hε : 0 < ε)
    (h : Lp ℂ 2 (volume : Measure ℝ)) {C : ℝ}
    (hb : ∀ X ∈ Ici (1 : ℝ), ‖pmRamanujanMovingBandMellinVector ε X‖ ≤ C)
    {z : ℂ} (hz : 1 < z.re)
    (hr : ∀ᵐ τ : ℝ, h τ ≠ 0 → (ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z ≠ 0) :
    riemannZeta z *
      (∫ X in Ici (1 : ℝ), (X : ℂ)^(-z-(1/2 : ℂ)) * pmRamanujanBandTestedScale ε h X) =
      ∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
        (pmPowerDampedDivisorDensity ε *
          (riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) / ((1/2 : ℂ)+(τ : ℂ)*I)) *
          ((1-(2 : ℂ)^(-((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z)))/
            ((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-z)) *
          (riemannZeta (1+z-((1/2 : ℂ)+(τ : ℂ)*I)) *
            pmRamanujanBandEulerCorrection ε z ((1/2 : ℂ)+(τ : ℂ)*I) - riemannZeta z)) := by
  rw [pmRamanujanBandTestedScale_integral_swap ε h hb (by linarith : 1/2 < z.re),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hr] with τ hτ
  by_cases hh : h τ = 0
  · simp [hh]
  · rw [mul_left_comm, pmRamanujanMovingBandMellin_cleared_eq hε τ hz (hτ hh)]

end RHTower
