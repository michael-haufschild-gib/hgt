import GaloisForLFunctions.MatomakiRadziwill.LadderMaster

/-!
# The master inequality on a set of frequencies

For a measurable `A ⊆ [−W, W]` (`ladder_master_on`): `∫_A |F_S|²` has the bound of
`LadderScales.ladder_master` — the same right-hand side — with the pointwise bound `ρ` for the top
blocks needed only on `A`.

Pointwise, `1_A |F|² ≤` the cover pieces, the top piece taken over `A ∩ E` (`ladder_cover_pointwise_on`).
The Ramaré errors and the first and moment steps are integrals of the same nonnegative functions over
`[−W, W]`; on `A ∩ E` the top blocks are bounded by `ρ`, and Halász–Montgomery on `[−W, W] ∩ A ∩ E`
is at most its value on `[−W, W] ∩ E`.  The low frequencies of `λ`, where no top-scale bound holds,
are left out by taking `A` away from them.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- **The pointwise cover on `A`.** -/
theorem ladder_cover_pointwise_on (F : ℝ → ℂ) (D : ℕ → ℝ → ℂ) (Dtop : ℝ → ℂ)
    (small : ℕ → Set ℝ) {J : ℕ} (hJ : 1 ≤ J) (A : Set ℝ) (w : ℝ) :
    A.indicator (fun w => ‖F w‖ ^ 2) w ≤ coverPiece F (D 0) (small 0) w
      + ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w
      + coverPiece F Dtop (A ∩ (small (J - 1))ᶜ) w := by
  classical
  have h0 := coverPiece_nonneg F (D 0) (small 0) w
  have hs : 0 ≤ ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w :=
    sum_nonneg fun j _ => coverPiece_nonneg _ _ _ w
  have ht := coverPiece_nonneg F Dtop (A ∩ (small (J - 1))ᶜ) w
  by_cases hwA : w ∈ A
  · rw [indicator_of_mem hwA]
    have hc := ladder_cover_pointwise F D Dtop small hJ w
    have heq : coverPiece F Dtop (small (J - 1))ᶜ w = coverPiece F Dtop (A ∩ (small (J - 1))ᶜ) w := by
      unfold coverPiece
      by_cases hwE : w ∈ (small (J - 1))ᶜ
      · rw [indicator_of_mem hwE,
          indicator_of_mem (show w ∈ A ∩ (small (J - 1))ᶜ from ⟨hwA, hwE⟩)]
      · rw [indicator_of_notMem hwE, indicator_of_notMem (fun h => hwE h.2)]
    linarith
  · rw [indicator_of_notMem hwA]
    linarith

/-- **The integrated cover on `A`.** -/
theorem ladder_cover_integral_on {F : ℝ → ℂ} {D : ℕ → ℝ → ℂ} {Dtop : ℝ → ℂ} (hF : Continuous F)
    (hD : ∀ j, Continuous (D j)) (hDtop : Continuous Dtop) {small : ℕ → Set ℝ}
    (hsmall : ∀ j, MeasurableSet (small j)) {J : ℕ} (hJ : 1 ≤ J) {W : ℝ} {A : Set ℝ}
    (hAm : MeasurableSet A) (hAs : A ⊆ Icc (-W) W) :
    (∫ w in A, ‖F w‖ ^ 2)
      ≤ (2 * (∫ w in Icc (-W) W, ‖F w - D 0 w‖ ^ 2)
          + 2 * (∫ w in Icc (-W) W, (small 0).indicator (fun w => ‖D 0 w‖ ^ 2) w))
        + ∑ j ∈ Finset.Ico 1 J, (2 * (∫ w in Icc (-W) W, ‖F w - D j w‖ ^ 2)
          + 2 * (∫ w in Icc (-W) W, (small j ∩ (small (j - 1))ᶜ).indicator
              (fun w => ‖D j w‖ ^ 2) w))
        + (2 * (∫ w in Icc (-W) W, ‖F w - Dtop w‖ ^ 2)
          + 2 * (∫ w in Icc (-W) W, (A ∩ (small (J - 1))ᶜ).indicator
              (fun w => ‖Dtop w‖ ^ 2) w)) := by
  have hmeas : ∀ j, MeasurableSet (small j ∩ (small (j - 1))ᶜ) := fun j =>
    (hsmall j).inter (hsmall (j - 1)).compl
  have hmtop : MeasurableSet (A ∩ (small (J - 1))ᶜ) := hAm.inter (hsmall (J - 1)).compl
  have hi0 := integrableOn_coverPiece hF (hD 0) (hsmall 0) W
  have hij : ∀ j, IntegrableOn (coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ)) (Icc (-W) W) :=
    fun j => integrableOn_coverPiece hF (hD j) (hmeas j) W
  have hit := integrableOn_coverPiece hF hDtop hmtop W
  have hsum : IntegrableOn (fun w => ∑ j ∈ Finset.Ico 1 J,
      coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w) (Icc (-W) W) :=
    integrable_finsetSum _ fun j _ => hij j
  have hFA : IntegrableOn (fun w => ‖F w‖ ^ 2) (Icc (-W) W) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  -- `∫_A |F|² = ∫_{[−W,W]} 1_A |F|²`
  have hAeq : (∫ w in A, ‖F w‖ ^ 2)
      = ∫ w in Icc (-W) W, A.indicator (fun w => ‖F w‖ ^ 2) w := by
    rw [integral_indicator hAm, Measure.restrict_restrict hAm, inter_eq_left.mpr hAs]
  rw [hAeq]
  calc (∫ w in Icc (-W) W, A.indicator (fun w => ‖F w‖ ^ 2) w)
      ≤ ∫ w in Icc (-W) W, (coverPiece F (D 0) (small 0) w
          + ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w
          + coverPiece F Dtop (A ∩ (small (J - 1))ᶜ) w) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            indicator_nonneg (fun _ _ => by positivity) w)
          ((hi0.add hsum).add hit)
          (Filter.Eventually.of_forall fun w => ladder_cover_pointwise_on F D Dtop small hJ A w)
    _ = _ := by
        have hA : IntegrableOn (fun w => coverPiece F (D 0) (small 0) w
            + ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w)
            (Icc (-W) W) := hi0.add hsum
        rw [integral_add hA hit, integral_add hi0 hsum,
          integral_finsetSum _ fun j _ => hij j, integral_coverPiece hF (hD 0) (hsmall 0),
          integral_coverPiece hF hDtop hmtop]
        congr 2
        exact sum_congr rfl fun j _ => integral_coverPiece hF (hD j) (hmeas j) W

/-- The pointwise bound for the exceptional set, needed on that set only. -/
theorem setIntegral_sum_blocks_le_of_bound_on {Q R : ℕ → ℝ → ℂ} (hR : ∀ v, Continuous (R v))
    (V : Finset ℕ) {ρ : ℝ} {E : Set ℝ} (hEm : MeasurableSet E) {W : ℝ} (hEs : E ⊆ Icc (-W) W)
    (hρ : ∀ v ∈ V, ∀ w ∈ E, ‖Q v w‖ ≤ ρ) :
    (∫ w in E, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2)
      ≤ (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ∫ w in E, ‖R v w‖ ^ 2 := by
  have hint : ∀ v, IntegrableOn (fun w => ‖R v w‖ ^ 2) E := fun v =>
    (((hR v).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  have hmaj : IntegrableOn (fun w => (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2) E :=
    (integrable_finsetSum V fun v _ => hint v).const_mul _
  have hpt : ∀ w ∈ E, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2
      ≤ (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2 := by
    intro w hw
    calc ‖∑ v ∈ V, Q v w * R v w‖ ^ 2
        ≤ (V.card : ℝ) * ∑ v ∈ V, ‖Q v w‖ ^ 2 * ‖R v w‖ ^ 2 :=
          normSq_sum_blocks_le (fun v => Q v w) (fun v => R v w)
      _ ≤ (V.card : ℝ) * ∑ v ∈ V, ρ ^ 2 * ‖R v w‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun v hv => ?_) (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hρ v hv w hw) 2) (by positivity)
      _ = (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2 := by rw [← mul_sum]; ring
  calc (∫ w in E, ‖∑ v ∈ V, Q v w * R v w‖ ^ 2)
      ≤ ∫ w in E, (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ‖R v w‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => by positivity) hmaj
          ((ae_restrict_iff' hEm).mpr (Filter.Eventually.of_forall hpt))
    _ = (V.card : ℝ) * ρ ^ 2 * ∑ v ∈ V, ∫ w in E, ‖R v w‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum V fun v _ => hint v]

namespace LadderScales

variable (L : LadderScales)

/-- **The master inequality on a set of frequencies `A ⊆ [−W, W]`.** -/
theorem ladder_master_on {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b, f (a * b) = f a * f b)
    (hJ : 1 ≤ L.J) {X : ℕ} (hX : 1 ≤ X) {W : ℝ} (hW : 1 ≤ W) {A : Set ℝ} (hAm : MeasurableSet A)
    (hAs : A ⊆ Icc (-W) W)
    {H : ℕ → ℝ} (hH : ∀ j, 2 ≤ H j) {Htop : ℝ} (hHtop : 2 ≤ Htop)
    {P : ℕ → ℕ} (hP : ∀ j, 2 ≤ P j) (hPmin : ∀ j, ∀ p ∈ L.scale j, P j ≤ p)
    {Ptop : ℕ} (hPtop : 2 ≤ Ptop) (hPtopmin : ∀ p ∈ L.top, Ptop ≤ p)
    (c : ℕ → ℕ → ℝ) (hc : ∀ j u, 0 < c j u) (ℓ : ℕ → ℕ → ℕ → ℕ)
    {ρ : ℝ} (hρ : ∀ v ∈ L.topBlocks Htop, ∀ w ∈ A, ‖blockQ f L.top Htop v w‖ ≤ ρ) :
    (∫ w in A, ‖logPoly (coefA f) (L.ladderS X) w‖ ^ 2)
      ≤ (2 * ramErr W X (H 0) (P 0)
          + 2 * ((L.blocks H 0).card * ∑ v ∈ L.blocks H 0, c 0 v ^ 2
              * (∫ w in Icc (-W) W, ‖blockR f (L.scale 0) (L.restAt 0) X (H 0) v w‖ ^ 2)))
        + ∑ j ∈ Finset.Ico 1 L.J, (2 * ramErr W X (H j) (P j)
          + 2 * ((L.blocks H j).card * ∑ v ∈ L.blocks H j, ∑ u ∈ L.blocks H (j - 1),
              c j v ^ 2 / c (j - 1) u ^ (2 * ℓ j u v)
              * (∫ w in Icc (-W) W, ‖blockQ f (L.scale (j - 1)) (H (j - 1)) u w ^ ℓ j u v
                  * blockR f (L.scale j) (L.restAt j) X (H j) v w‖ ^ 2)))
        + (2 * ramErr W X Htop Ptop
          + 2 * ((L.topBlocks Htop).card * ρ ^ 2 * ∑ v ∈ L.topBlocks Htop,
              (∫ w in Icc (-W) W ∩ (L.smallSet f H c (L.J - 1))ᶜ,
                ‖blockR f L.top L.restTop X Htop v w‖ ^ 2))) := by
  classical
  set F : ℝ → ℂ := logPoly (coefA f) (L.ladderS X) with hFdef
  set D : ℕ → ℝ → ℂ := fun j => pairPoly f (L.scale j) (L.restAt j) X (H j) with hDdef
  set Dtop : ℝ → ℂ := pairPoly f L.top L.restTop X Htop with hDtopdef
  have hcover := ladder_cover_integral_on (F := F) (D := D) (Dtop := Dtop)
    (continuous_logPoly _ _) (fun j => continuous_pairPoly f (L.prime_scale j) _ X (H j))
    (continuous_pairPoly f L.prime_top _ X Htop) (L.measurableSet_smallSet f H c) hJ hAm hAs
  -- Ramaré's decomposition at every scale
  have hram : ∀ j ∈ range L.J, (∫ w in Icc (-W) W, ‖F w - D j w‖ ^ 2)
      ≤ ramErr W X (H j) (P j) := by
    intro j hj
    have h := integral_normSq_rough_sub_pairPoly_le hf hmul (L.prime_scale j) (hP j) (hPmin j)
      (fun p hp m => L.restAt_mul_iff hp m) hX (hH j) hW
    rw [L.roughSet_restAt_eq hj X] at h
    exact h
  have hramtop : (∫ w in Icc (-W) W, ‖F w - Dtop w‖ ^ 2) ≤ ramErr W X Htop Ptop := by
    have h := integral_normSq_rough_sub_pairPoly_le hf hmul L.prime_top hPtop hPtopmin
      (fun p hp m => L.restTop_mul_iff hp m) hX hHtop hW
    rw [L.roughSet_restTop_eq X] at h
    exact h
  have hDj : ∀ j w, D j w = ∑ v ∈ L.blocks H j, blockQ f (L.scale j) (H j) v w
      * blockR f (L.scale j) (L.restAt j) X (H j) v w := fun j w =>
    pairPoly_eq_sum_blocks f (L.prime_scale j) _ X (H j) w
  -- the first step
  have hfirst : (∫ w in Icc (-W) W, (L.smallSet f H c 0).indicator (fun w => ‖D 0 w‖ ^ 2) w)
      ≤ (L.blocks H 0).card * ∑ v ∈ L.blocks H 0, c 0 v ^ 2
          * (∫ w in Icc (-W) W, ‖blockR f (L.scale 0) (L.restAt 0) X (H 0) v w‖ ^ 2) := by
    have heq : (L.smallSet f H c 0).indicator (fun w => ‖D 0 w‖ ^ 2)
        = (smallAt (blockQ f (L.scale 0) (H 0)) (L.blocks H 0) (c 0)).indicator
            (fun w => ‖∑ v ∈ L.blocks H 0, blockQ f (L.scale 0) (H 0) v w
              * blockR f (L.scale 0) (L.restAt 0) X (H 0) v w‖ ^ 2) := by
      funext w; rw [smallSet]; simp only [hDj]
    rw [heq]
    exact integral_indicator_small_le (fun v => continuous_logPoly _ _) _ _ W
  -- the later steps
  have hstep : ∀ j ∈ Finset.Ico 1 L.J,
      (∫ w in Icc (-W) W, (L.smallSet f H c j ∩ (L.smallSet f H c (j - 1))ᶜ).indicator
        (fun w => ‖D j w‖ ^ 2) w)
      ≤ (L.blocks H j).card * ∑ v ∈ L.blocks H j, ∑ u ∈ L.blocks H (j - 1),
          c j v ^ 2 / c (j - 1) u ^ (2 * ℓ j u v)
          * (∫ w in Icc (-W) W, ‖blockQ f (L.scale (j - 1)) (H (j - 1)) u w ^ ℓ j u v
              * blockR f (L.scale j) (L.restAt j) X (H j) v w‖ ^ 2) := by
    intro j _
    have heq : (L.smallSet f H c j ∩ (L.smallSet f H c (j - 1))ᶜ).indicator
          (fun w => ‖D j w‖ ^ 2)
        = (smallAt (blockQ f (L.scale j) (H j)) (L.blocks H j) (c j)
            ∩ (smallAt (blockQ f (L.scale (j - 1)) (H (j - 1))) (L.blocks H (j - 1))
              (c (j - 1)))ᶜ).indicator
            (fun w => ‖∑ v ∈ L.blocks H j, blockQ f (L.scale j) (H j) v w
              * blockR f (L.scale j) (L.restAt j) X (H j) v w‖ ^ 2) := by
      funext w; rw [smallSet, smallSet]; simp only [hDj]
    rw [heq]
    exact integral_indicator_small_not_small_le (fun v => continuous_logPoly _ _)
      (fun u => continuous_logPoly _ _) _ _ _ _ (fun u _ => hc (j - 1) u) (ℓ j) W
  -- the exceptional set, on `A`
  have hEm : MeasurableSet (A ∩ (L.smallSet f H c (L.J - 1))ᶜ) :=
    hAm.inter (L.measurableSet_smallSet f H c _).compl
  have hEm' : MeasurableSet (L.smallSet f H c (L.J - 1))ᶜ :=
    (L.measurableSet_smallSet f H c _).compl
  have htop : (∫ w in Icc (-W) W, (A ∩ (L.smallSet f H c (L.J - 1))ᶜ).indicator
        (fun w => ‖Dtop w‖ ^ 2) w)
      ≤ (L.topBlocks Htop).card * ρ ^ 2 * ∑ v ∈ L.topBlocks Htop,
          (∫ w in Icc (-W) W ∩ (L.smallSet f H c (L.J - 1))ᶜ,
            ‖blockR f L.top L.restTop X Htop v w‖ ^ 2) := by
    rw [integral_indicator hEm, Measure.restrict_restrict hEm, inter_comm]
    have hDt : ∀ w, Dtop w = ∑ v ∈ L.topBlocks Htop, blockQ f L.top Htop v w
        * blockR f L.top L.restTop X Htop v w := fun w =>
      pairPoly_eq_sum_blocks f L.prime_top _ X Htop w
    simp only [hDt]
    have hsub : Icc (-W) W ∩ (A ∩ (L.smallSet f H c (L.J - 1))ᶜ) ⊆ Icc (-W) W := inter_subset_left
    have hρ' : ∀ v ∈ L.topBlocks Htop, ∀ w ∈ Icc (-W) W ∩ (A ∩ (L.smallSet f H c (L.J - 1))ᶜ),
        ‖blockQ f L.top Htop v w‖ ≤ ρ := fun v hv w hw => hρ v hv w hw.2.1
    refine le_trans (setIntegral_sum_blocks_le_of_bound_on (fun v => continuous_logPoly _ _) _
      (measurableSet_Icc.inter hEm) hsub hρ') ?_
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => ?_) (by positivity)
    have hcont : Continuous fun w => ‖blockR f L.top L.restTop X Htop v w‖ ^ 2 :=
      (continuous_logPoly _ _).norm.pow 2
    have hint : IntegrableOn (fun w => ‖blockR f L.top L.restTop X Htop v w‖ ^ 2)
        (Icc (-W) W ∩ (L.smallSet f H c (L.J - 1))ᶜ) :=
      (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set inter_subset_left
    refine setIntegral_mono_set hint (ae_of_all _ fun w => sq_nonneg _) ?_
    exact (inter_subset_inter_right _ inter_subset_right).eventuallyLE
  -- assemble
  refine le_trans hcover ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact add_le_add (by linarith [hram 0 (mem_range.mpr (by omega))])
      (by linarith [hfirst])
  · refine sum_le_sum fun j hj => ?_
    have hjr : j ∈ range L.J := mem_range.mpr (Finset.mem_Ico.mp hj).2
    exact add_le_add (by linarith [hram j hjr]) (by linarith [hstep j hj])
  · exact add_le_add (by linarith [hramtop]) (by linarith [htop])

end LadderScales

end

end GaloisForLFunctions.MatomakiRadziwill
