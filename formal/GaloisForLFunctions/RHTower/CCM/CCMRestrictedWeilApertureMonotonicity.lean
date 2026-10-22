import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFriedrichsOperator

/-!
# Aperture monotonicity of the exact restricted CCM Weil form

The source form domains are nested with aperture.  This file proves the nesting on the literal
weighted Fourier domain, then identifies every source term under that inclusion.  The only new
prime indices at a larger aperture have logarithmic displacement beyond the smaller support
diameter, so their two translation pairings vanish exactly.  The variational characterization of
the canonical Friedrichs ground energy then gives its monotonicity.
-/

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

private theorem indicatorCutoff_central_eq_self_of_le
    {a b : ℝ} (hab : a ≤ b) (f : SoninL2)
    (hf : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = f) :
    indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) f = f := by
  apply Lp.ext
  have hfix :
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f :
          ℝ → ℂ) =ᵐ[volume] f := by
    rw [hf]
  filter_upwards [
    indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b) f,
    indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f,
    hfix] with x hb ha hfixx
  rw [hb]
  by_cases hxb : x ∈ centralInterval b
  · rw [Set.indicator_of_mem hxb]
  · have hxa : x ∉ centralInterval a := by
      intro hxa
      apply hxb
      rw [centralInterval] at hxa ⊢
      constructor <;> linarith [hxa.1, hxa.2]
    rw [Set.indicator_of_notMem hxb]
    have hzero : f x = 0 := by
      rw [ha, Set.indicator_of_notMem hxa] at hfixx
      exact hfixx.symm
    rw [hzero]

private theorem ccmArchimedeanFormDomain_mem_of_le
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    u.1 ∈ (ccmArchimedeanSupportDefect b).ker := by
  rw [LinearMap.mem_ker]
  change (1 - indicatorCutoff (centralInterval b.1)
    (measurableSet_centralInterval b.1))
      (ccmArchimedeanFourierToTime u.1) = 0
  rw [sub_apply, one_apply_eq_self, sub_eq_zero]
  have hfa : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)
        (ccmArchimedeanFourierToTime u.1) =
      ccmArchimedeanFourierToTime u.1 := by
    have hu := u.property
    rw [LinearMap.mem_ker] at hu
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime u.1) = 0 at hu
    rw [sub_apply, one_apply_eq_self, sub_eq_zero] at hu
    exact hu.symm
  exact (indicatorCutoff_central_eq_self_of_le hab _ hfa).symm

/-- Every smaller-aperture form vector has a larger-aperture representative with identical
weighted Fourier data. -/
theorem exists_ccmArchimedeanFormDomain_extension
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) :
    ∃ v : CCMArchimedeanFormDomain b, v.1 = u.1 :=
  ⟨⟨u.1, ccmArchimedeanFormDomain_mem_of_le hab u⟩, rfl⟩

theorem ccmArchimedeanFormToAperture_coe_eq_of_val_eq
    {a b : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    (ccmArchimedeanFormToAperture b v : SoninL2) =
      (ccmArchimedeanFormToAperture a u : SoninL2) := by
  change ccmArchimedeanFourierToTime v.1 = ccmArchimedeanFourierToTime u.1
  rw [hvu]

theorem norm_ccmArchimedeanFormToAperture_eq_of_val_eq
    {a b : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    ‖ccmArchimedeanFormToAperture b v‖ =
      ‖ccmArchimedeanFormToAperture a u‖ := by
  change ‖(ccmArchimedeanFormToAperture b v : SoninL2)‖ =
    ‖(ccmArchimedeanFormToAperture a u : SoninL2)‖
  rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu]

private theorem indicatorCutoff_ccmPolarL2Vector_of_le
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (s : ℝ) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (ccmPolarL2Vector b s) = ccmPolarL2Vector a s := by
  apply Lp.ext
  filter_upwards [
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (ccmPolarL2Vector b s),
    ccmPolarL2Vector_coeFn b s,
    ccmPolarL2Vector_coeFn a s] with x hcut hb ha
  rw [hcut]
  by_cases hxa : x ∈ centralInterval a.1
  · have hxb : x ∈ centralInterval b.1 := by
      rw [centralInterval] at hxa ⊢
      constructor <;> linarith [hxa.1, hxa.2]
    rw [Set.indicator_of_mem hxa, hb, Set.indicator_of_mem hxb,
      ha, Set.indicator_of_mem hxa]
  · rw [Set.indicator_of_notMem hxa, ha, Set.indicator_of_notMem hxa]

theorem inner_ccmPolarApertureVector_eq_of_val_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (s : ℝ)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    inner ℂ (ccmPolarApertureVector b s)
        (ccmArchimedeanFormToAperture b v) =
      inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a u) := by
  let P := indicatorCutoff (centralInterval a.1)
    (measurableSet_centralInterval a.1)
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  have hfb : (ccmArchimedeanFormToAperture b v : SoninL2) = f :=
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu
  have hPf : P f = f := by
    exact indicatorCutoff_ccmArchimedeanFormEmbedding a u
  change inner ℂ (ccmPolarL2Vector b s)
      (ccmArchimedeanFormToAperture b v : SoninL2) =
    inner ℂ (ccmPolarL2Vector a s) f
  rw [hfb]
  calc
    inner ℂ (ccmPolarL2Vector b s) f =
        inner ℂ (ccmPolarL2Vector b s) (P f) := by rw [hPf]
    _ = inner ℂ (P (ccmPolarL2Vector b s)) f :=
      (indicatorCutoff_symmetric (centralInterval a.1)
        (measurableSet_centralInterval a.1)
        (ccmPolarL2Vector b s) f).symm
    _ = inner ℂ (ccmPolarL2Vector a s) f := by
      rw [indicatorCutoff_ccmPolarL2Vector_of_le hab]

/-- A translation farther than the aperture diameter has zero compressed matrix coefficient. -/
theorem inner_logTranslationCLM_eq_zero_of_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 < h) :
    inner ℂ (logTranslationCLM h f.1) f.1 = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hfix : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) f.1 = f.1 :=
    indicatorCutoff_suzukiApertureHilbert a f
  have hfixAE :
      (indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1) f.1 : ℝ → ℂ) =ᵐ[volume] f.1 := by
    rw [hfix]
  have hcutAE := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  have hfixShift := hfixAE.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have hcutShift := hcutAE.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htrans := Lp.coeFn_compMeasurePreserving f.1
    (MellinL2.realTranslation_measurePreserving h)
  calc
    (∫ x : ℝ, inner ℂ (logTranslationCLM h f.1 x) (f.1 x)) =
        ∫ _x : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hfixAE, hcutAE, hfixShift, hcutShift, htrans] with
          x hfixx hcutx hfixxh hcutxh htransx
      have htransx' : logTranslationCLM h f.1 x = f.1 (x + h) := by
        simpa [logTranslationCLM, MellinL2.additiveTranslationUnitary,
          MellinL2.realTranslationEquiv, Function.comp_apply] using! htransx
      have hfixxh' : indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1) f.1 (x + h) = f.1 (x + h) := by
        simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hfixxh
      have hcutxh' : indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1) f.1 (x + h) =
            (centralInterval a.1).indicator (fun y => f.1 y) (x + h) := by
        simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hcutxh
      rw [htransx']
      by_cases hx : x ∈ centralInterval a.1
      · have hxh : x + h ∉ centralInterval a.1 := by
          intro hmem
          rw [centralInterval, Set.mem_Icc] at hx hmem
          linarith [hx.1, hx.2, hmem.1, hmem.2]
        have hzero : f.1 (x + h) = 0 := by
          rw [hcutxh',
            Set.indicator_of_notMem hxh] at hfixxh'
          exact hfixxh'.symm
        rw [hzero]
        simp
      · have hzero : f.1 x = 0 := by
          rw [hcutx, Set.indicator_of_notMem hx] at hfixx
          exact hfixx.symm
        rw [hzero]
        simp
    _ = 0 := by simp

theorem inner_symmetric_logTranslations_eq_zero_of_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 < h) :
    inner ℂ (logTranslationCLM h f.1) f.1 +
        inner ℂ (logTranslationCLM (-h) f.1) f.1 = 0 := by
  have hpos := inner_logTranslationCLM_eq_zero_of_aperture a f hh
  have hneg : inner ℂ (logTranslationCLM (-h) f.1) f.1 = 0 := by
    rw [inner_logTranslationCLM (-h)]
    simp only [neg_neg]
    exact inner_eq_zero_symm.mpr hpos
  rw [hpos, hneg, add_zero]

/-- Enlarging the floor cutoff adds only translations disjoint from the smaller aperture. -/
theorem ccmFinitePrimeQuadraticSum_eq_of_le
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (f : suzukiApertureHilbert a) :
    (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
              inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re) =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
              inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
  classical
  let term : ℕ → ℝ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℝ) *
      (1 / Real.sqrt n) *
        (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
          inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re
  change (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1))), term n) =
    ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))), term n
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1, hn.2.trans ?_⟩
    apply Nat.floor_mono
    exact Real.exp_le_exp.mpr (by linarith)
  · intro n hnb hna
    rw [Finset.mem_Icc] at hnb
    have hfloor : Nat.floor (Real.exp (2 * a.1)) < n := by
      by_contra hnot
      have hnle : n ≤ Nat.floor (Real.exp (2 * a.1)) := Nat.le_of_not_gt hnot
      exact hna (Finset.mem_Icc.mpr ⟨hnb.1, hnle⟩)
    have hexpN : Real.exp (2 * a.1) < (n : ℝ) :=
      Nat.lt_of_floor_lt hfloor
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hnb.1)
    have hlog : 2 * a.1 < Real.log n := by
      have hstrict := Real.strictMonoOn_log
        (Set.mem_Ioi.mpr (Real.exp_pos (2 * a.1)))
        (Set.mem_Ioi.mpr hnpos) hexpN
      rwa [Real.log_exp] at hstrict
    have hzero := inner_symmetric_logTranslations_eq_zero_of_aperture a f hlog
    dsimp only [term]
    rw [hzero]
    simp

/-- Literal archimedean, polar, and finite-prime source values are preserved by aperture
extension. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_of_val_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    ccmRestrictedWeilSourceQuadratic b v =
      ccmRestrictedWeilSourceQuadratic a u := by
  let fa := ccmArchimedeanFormToAperture a u
  let fb := ccmArchimedeanFormToAperture b v
  have hfb : (fb : SoninL2) = (fa : SoninL2) :=
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu
  have hminus := inner_ccmPolarApertureVector_eq_of_val_eq hab (-1 / 2) hvu
  have hplus := inner_ccmPolarApertureVector_eq_of_val_eq hab (1 / 2) hvu
  have hprime := ccmFinitePrimeQuadraticSum_eq_of_le hab fa
  unfold ccmRestrictedWeilSourceQuadratic
  dsimp only
  change
    (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖(v.1 : ℝ → ℂ) xi‖ ^ 2) +
        ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (-1 / 2)) fb) *
              inner ℂ (ccmPolarApertureVector b (1 / 2)) fb +
            (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector b (1 / 2)) fb) *
              inner ℂ (ccmPolarApertureVector b (-1 / 2)) fb).re -
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1))),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) fb.1) fb.1 +
              inner ℂ (logTranslationCLM (-Real.log n) fb.1) fb.1).re =
      (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) +
        ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) fa) *
              inner ℂ (ccmPolarApertureVector a (1 / 2)) fa +
            (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) fa) *
              inner ℂ (ccmPolarApertureVector a (-1 / 2)) fa).re -
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) fa.1) fa.1 +
              inner ℂ (logTranslationCLM (-Real.log n) fa.1) fa.1).re
  rw [hvu, hminus, hplus]
  have hprime' := hprime
  change
    (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1))),
      (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
        (inner ℂ (logTranslationCLM (Real.log n) (fa : SoninL2)) (fa : SoninL2) +
          inner ℂ (logTranslationCLM (-Real.log n) (fa : SoninL2))
            (fa : SoninL2)).re) = _ at hprime'
  simpa only [hfb] using congrArg
    (fun primePart : ℝ =>
      (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) +
        ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) fa) *
              inner ℂ (ccmPolarApertureVector a (1 / 2)) fa +
            (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) fa) *
              inner ℂ (ccmPolarApertureVector a (-1 / 2)) fa).re - primePart)
    hprime'

/-- The exact restricted CCM ground energy is antitone under aperture enlargement. -/
theorem ccmRestrictedWeilGroundEnergy_antitone
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    ccmRestrictedWeilGroundEnergy b ≤ ccmRestrictedWeilGroundEnergy a := by
  obtain ⟨u, huNe, huGround⟩ :=
    ccmRestrictedWeilSource_exists_groundFormState a
  obtain ⟨v, hvu⟩ := exists_ccmArchimedeanFormDomain_extension hab u
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source b v
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab hvu
  have hnorm := norm_ccmArchimedeanFormToAperture_eq_of_val_eq hvu
  rw [hsource, huGround, hnorm] at hfloor
  have hnormPos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr huNe)
  exact le_of_mul_le_mul_right hfloor hnormPos

end RHTower
