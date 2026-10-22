import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanLaurentFormCore
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFriedrichsOperator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Connes--Consani lower-semicontinuous Laurent reconstruction

This file formalizes Connes--Consani (2021), Proposition `Hilbert1`, for the literal restricted
Weil quadratic form.  The form is extended by `+∞` outside its physical form domain.  Weighted
Fatou closure proves that this extension is lower semicontinuous in physical `L²`; density of
the exact Laurent core then identifies it with the infimum of all Laurent-sequence liminf values.

The off-domain case is substantive: any physical convergent sequence with bounded source energy
would have a weighted-`L²` limit and hence force the target back into the form domain.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

theorem exists_ccmArchimedeanFormDomain_of_fourier_memLp
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (hf : MemLp (fun xi : ℝ => (fourierUnitary f.1 : ℝ → ℂ) xi) 2
      ccmArchimedeanFormMeasure) :
    ∃ u : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a u = f := by
  let g : ℝ → ℂ := fun xi => (fourierUnitary f.1 : ℝ → ℂ) xi
  let w : CCMArchimedeanFourierL2 := hf.toLp g
  have hwL2 : ccmArchimedeanWeightedToL2 w = fourierUnitary f.1 := by
    apply MeasureTheory.Lp.ext
    have hwWeighted : (w : ℝ → ℂ) =ᵐ[ccmArchimedeanFormMeasure] g :=
      hf.coeFn_toLp
    have hwVolume : (w : ℝ → ℂ) =ᵐ[volume] g :=
      hwWeighted.filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn w, hwVolume] with xi hto hw
    rw [hto, hw]
  have htime : ccmArchimedeanFourierToTime w = f.1 := by
    apply fourierUnitary.injective
    rw [fourierUnitary_ccmArchimedeanFourierToTime, hwL2]
  have hwker : w ∈ (ccmArchimedeanSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime w) = 0
    rw [htime, sub_apply, one_apply_eq_self,
      indicatorCutoff_suzukiApertureHilbert a f, sub_self]
  let u : CCMArchimedeanFormDomain a := ⟨w, hwker⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact htime

/-- Weighted Fatou closure of the exact form embedding. -/
theorem exists_ccmArchimedeanFormDomain_norm_enorm_le_of_tendsto
    (a : SuzukiPositiveAperture) (u : ℕ → CCMArchimedeanFormDomain a)
    (f : suzukiApertureHilbert a)
    (huf : Tendsto (fun n => ccmArchimedeanFormToAperture a (u n)) atTop (nhds f))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (huC : ∀ᶠ n in atTop, ‖u n‖ₑ ≤ C) :
    ∃ v : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a v = f ∧ ‖v‖ₑ ≤ C := by
  have hval : Tendsto
      (fun n => (ccmArchimedeanFormToAperture a (u n) : suzukiApertureHilbert a).1)
      atTop (nhds f.1) :=
    (continuous_subtype_val.tendsto f).comp huf
  have hfourier : Tendsto
      (fun n => ccmArchimedeanWeightedToL2 (u n).1) atTop
      (nhds (fourierUnitary f.1)) := by
    have h := (fourierUnitary.continuous.tendsto f.1).comp hval
    have hfun :
        (fourierUnitary ∘ fun n =>
          (ccmArchimedeanFormToAperture a (u n) : suzukiApertureHilbert a).1) =
          fun n => ccmArchimedeanWeightedToL2 (u n).1 := by
      funext n
      exact fourierUnitary_ccmArchimedeanFourierToTime (u n).1
    rw [hfun] at h
    exact h
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hfourier).exists_seq_tendsto_ae
  have hrepresentatives : ∀ᵐ xi : ℝ ∂volume, ∀ n : ℕ,
      (ccmArchimedeanWeightedToL2 (u (ns n)).1 : ℝ → ℂ) xi =
        ((u (ns n)).1 : ℝ → ℂ) xi := by
    exact ae_all_iff.2 fun n => ccmArchimedeanWeightedToL2_coeFn (u (ns n)).1
  have hae' : ∀ᵐ xi : ℝ ∂volume,
      Tendsto (fun n => ((u (ns n)).1 : ℝ → ℂ) xi) atTop
        (nhds ((fourierUnitary f.1 : ℝ → ℂ) xi)) := by
    filter_upwards [hae, hrepresentatives] with xi hxi hrep
    exact hxi.congr' (Eventually.of_forall fun n => hrep n)
  have haeWeighted : ∀ᵐ xi : ℝ ∂ccmArchimedeanFormMeasure,
      Tendsto (fun n => ((u (ns n)).1 : ℝ → ℂ) xi) atTop
        (nhds ((fourierUnitary f.1 : ℝ → ℂ) xi)) :=
    hae'.filter_mono ccmArchimedeanFormMeasure_absolutelyContinuous_volume.ae_le
  have huCsub : ∀ᶠ n in atTop, ‖u (ns n)‖ₑ ≤ C :=
    hns.tendsto_atTop.eventually huC
  have heLpBound : ∀ᶠ n in atTop,
      eLpNorm (fun xi : ℝ => ((u (ns n)).1 : ℝ → ℂ) xi) 2
        ccmArchimedeanFormMeasure ≤ C := by
    filter_upwards [huCsub] with n hn
    change ‖(u (ns n)).1‖ₑ ≤ C at hn
    simpa only [MeasureTheory.Lp.enorm_def] using hn
  have hlimBound :
      eLpNorm (fun xi : ℝ => (fourierUnitary f.1 : ℝ → ℂ) xi) 2
          ccmArchimedeanFormMeasure ≤ C :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto heLpBound
      (fun n => MeasureTheory.Lp.aestronglyMeasurable (u (ns n)).1) haeWeighted
  have hlimitMeas : AEStronglyMeasurable
      (fun xi : ℝ => (fourierUnitary f.1 : ℝ → ℂ) xi)
      ccmArchimedeanFormMeasure :=
    AEStronglyMeasurable.mono_ac
      ccmArchimedeanFormMeasure_absolutelyContinuous_volume
      (MeasureTheory.Lp.aestronglyMeasurable (fourierUnitary f.1))
  have hlimitMem : MemLp
      (fun xi : ℝ => (fourierUnitary f.1 : ℝ → ℂ) xi) 2
      ccmArchimedeanFormMeasure :=
    ⟨hlimitMeas, hlimBound.trans_lt (lt_top_iff_ne_top.2 hC)⟩
  obtain ⟨v, hv⟩ := exists_ccmArchimedeanFormDomain_of_fourier_memLp a f hlimitMem
  refine ⟨v, hv, ?_⟩
  have hvNorm : ‖v‖ₑ =
      eLpNorm (fun xi : ℝ => (fourierUnitary f.1 : ℝ → ℂ) xi) 2
        ccmArchimedeanFormMeasure := by
    change ‖v.1‖ₑ = _
    rw [MeasureTheory.Lp.enorm_def]
    apply eLpNorm_congr_ae
    have hvfourier : ccmArchimedeanWeightedToL2 v.1 = fourierUnitary f.1 := by
      rw [← hv]
      exact (fourierUnitary_ccmArchimedeanFourierToTime v.1).symm
    have hvol : ((v.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) =ᵐ[volume]
        (fourierUnitary f.1 : ℝ → ℂ) :=
      (ccmArchimedeanWeightedToL2_coeFn v.1).symm.trans (by rw [hvfourier])
    exact hvol.filter_mono
      ccmArchimedeanFormMeasure_absolutelyContinuous_volume.ae_le
  rw [hvNorm]
  exact hlimBound

def ccmRestrictedWeilBoundedDiagonal (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : ℝ :=
  (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re

theorem continuous_ccmRestrictedWeilBoundedDiagonal (a : SuzukiPositiveAperture) :
    Continuous (ccmRestrictedWeilBoundedDiagonal a) := by
  unfold ccmRestrictedWeilBoundedDiagonal
  exact Complex.continuous_re.comp
    ((ccmRestrictedWeilBoundedRemainder a).continuous.inner continuous_id)

theorem ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a u =
      ‖u.1‖ ^ 2 + ccmRestrictedWeilBoundedDiagonal a (ccmArchimedeanFormToAperture a u) := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmRestrictedWeilForm ccmRestrictedWeilBoundedDiagonal
  rw [Complex.add_re]
  have hself : (inner ℂ u u).re = ‖u.1‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
    norm_cast
  rw [hself]

theorem continuous_ccmRestrictedWeilSourceQuadratic (a : SuzukiPositiveAperture) :
    Continuous (ccmRestrictedWeilSourceQuadratic a) := by
  have heq : ccmRestrictedWeilSourceQuadratic a = fun u =>
      (ccmRestrictedWeilForm a u u).re := by
    funext u
    exact (ccmRestrictedWeilForm_self_re_eq_source a u).symm
  rw [heq]
  unfold ccmRestrictedWeilForm
  exact Complex.continuous_re.comp
    ((continuous_id.inner continuous_id).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp
          (ccmArchimedeanFormToAperture a).continuous).inner
        (ccmArchimedeanFormToAperture a).continuous))

theorem ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ‖u.1‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u +
      ‖ccmRestrictedWeilBoundedRemainder a‖ *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal]
  have hb : -( ‖ccmRestrictedWeilBoundedRemainder a‖ *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2) ≤
      ccmRestrictedWeilBoundedDiagonal a (ccmArchimedeanFormToAperture a u) := by
    have habs : |ccmRestrictedWeilBoundedDiagonal a (ccmArchimedeanFormToAperture a u)| ≤
        ‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
      unfold ccmRestrictedWeilBoundedDiagonal
      calc
        |(inner ℂ
            (ccmRestrictedWeilBoundedRemainder a
              (ccmArchimedeanFormToAperture a u))
            (ccmArchimedeanFormToAperture a u)).re| ≤
            ‖inner ℂ
              (ccmRestrictedWeilBoundedRemainder a
                (ccmArchimedeanFormToAperture a u))
              (ccmArchimedeanFormToAperture a u)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖ccmRestrictedWeilBoundedRemainder a
              (ccmArchimedeanFormToAperture a u)‖ *
              ‖ccmArchimedeanFormToAperture a u‖ :=
          norm_inner_le_norm (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
            (ccmArchimedeanFormToAperture a u)
        _ ≤ (‖ccmRestrictedWeilBoundedRemainder a‖ *
              ‖ccmArchimedeanFormToAperture a u‖) *
              ‖ccmArchimedeanFormToAperture a u‖ :=
          mul_le_mul_of_nonneg_right
            ((ccmRestrictedWeilBoundedRemainder a).le_opNorm _)
            (norm_nonneg _)
        _ = ‖ccmRestrictedWeilBoundedRemainder a‖ *
              ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by ring
    exact (neg_le_neg habs).trans (neg_abs_le _)
  linarith

theorem isClosed_ccmRestrictedWeilSource_sublevel (a : SuzukiPositiveAperture) (c : ℝ) :
    IsClosed {f : suzukiApertureHilbert a |
      ∃ u : CCMArchimedeanFormDomain a,
        ccmArchimedeanFormToAperture a u = f ∧
          ccmRestrictedWeilSourceQuadratic a u ≤ c} := by
  rw [← isSeqClosed_iff_isClosed]
  intro x f hx hxf
  choose u huJ huQ using hx
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto x hxf)
  have hMx (n : ℕ) : ‖x n‖ ≤ M := hM (x n) ⟨n, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg (x 0)).trans (hMx 0)
  let D : ℝ := max 0
    (c + ‖ccmRestrictedWeilBoundedRemainder a‖ * M ^ 2)
  have hD0 : 0 ≤ D := le_max_left _ _
  have huNormSq (n : ℕ) : ‖(u n).1‖ ^ 2 ≤ D := by
    apply (ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a (u n)).trans
    rw [huJ n]
    apply le_max_of_le_right
    have hxSq : ‖x n‖ ^ 2 ≤ M ^ 2 := by
      nlinarith [hMx n, norm_nonneg (x n)]
    have hmul := mul_le_mul_of_nonneg_left hxSq
      (norm_nonneg (ccmRestrictedWeilBoundedRemainder a))
    linarith [huQ n]
  have huNorm (n : ℕ) : ‖(u n).1‖ ≤ Real.sqrt D := by
    nlinarith [huNormSq n, Real.sq_sqrt hD0, norm_nonneg (u n).1, Real.sqrt_nonneg D]
  have huEnorm : ∀ᶠ n in atTop, ‖u n‖ₑ ≤ ENNReal.ofReal (Real.sqrt D) := by
    filter_upwards with n
    change ‖(u n).1‖ₑ ≤ ENNReal.ofReal (Real.sqrt D)
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (huNorm n)
  obtain ⟨v, hvJ, hvNorm⟩ :=
    exists_ccmArchimedeanFormDomain_norm_enorm_le_of_tendsto a u f
      (by simpa only [huJ] using hxf)
      (ENNReal.ofReal (Real.sqrt D)) (by simp) huEnorm
  refine ⟨v, hvJ, ?_⟩
  by_contra hvc
  have hcv : c < ccmRestrictedWeilSourceQuadratic a v := lt_of_not_ge hvc
  let delta : ℝ := (ccmRestrictedWeilSourceQuadratic a v - c) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hbTendsto : Tendsto (fun n => ccmRestrictedWeilBoundedDiagonal a (x n)) atTop
      (nhds (ccmRestrictedWeilBoundedDiagonal a f)) :=
    ((continuous_ccmRestrictedWeilBoundedDiagonal a).tendsto f).comp hxf
  have hbEventually : ∀ᶠ n in atTop,
      ccmRestrictedWeilBoundedDiagonal a f - delta < ccmRestrictedWeilBoundedDiagonal a (x n) := by
    have hopen : Ioi (ccmRestrictedWeilBoundedDiagonal a f - delta) ∈
        nhds (ccmRestrictedWeilBoundedDiagonal a f) := Ioi_mem_nhds (by linarith)
    exact hbTendsto.eventually hopen
  let E : ℝ := ‖v.1‖ ^ 2 - delta
  have huTightSq : ∀ᶠ n in atTop, ‖(u n).1‖ ^ 2 ≤ E := by
    filter_upwards [hbEventually] with n hbn
    have huQn : ‖(u n).1‖ ^ 2 + ccmRestrictedWeilBoundedDiagonal a (x n) ≤ c := by
      calc
        _ = ccmRestrictedWeilSourceQuadratic a (u n) := by
          rw [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal, huJ n]
        _ ≤ c := huQ n
    have hvdecomp : ccmRestrictedWeilSourceQuadratic a v =
        ‖v.1‖ ^ 2 + ccmRestrictedWeilBoundedDiagonal a f := by
      calc
        _ = ‖v.1‖ ^ 2 +
            ccmRestrictedWeilBoundedDiagonal a (ccmArchimedeanFormToAperture a v) :=
          ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal a v
        _ = _ := by rw [hvJ]
    have hdeltaEq : delta =
        (‖v.1‖ ^ 2 + ccmRestrictedWeilBoundedDiagonal a f - c) / 2 := by
      dsimp [delta]
      rw [hvdecomp]
    dsimp [E]
    rw [hdeltaEq] at hbn ⊢
    nlinarith [huQn]
  have hE0 : 0 ≤ E := by
    obtain ⟨n, hn⟩ := huTightSq.exists
    exact (sq_nonneg ‖(u n).1‖).trans hn
  have huTight : ∀ᶠ n in atTop, ‖(u n).1‖ ≤ Real.sqrt E := by
    filter_upwards [huTightSq] with n hn
    nlinarith [Real.sq_sqrt hE0, norm_nonneg (u n).1, Real.sqrt_nonneg E]
  have huTightEnorm : ∀ᶠ n in atTop,
      ‖u n‖ₑ ≤ ENNReal.ofReal (Real.sqrt E) := by
    filter_upwards [huTight] with n hn
    change ‖(u n).1‖ₑ ≤ ENNReal.ofReal (Real.sqrt E)
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hn
  obtain ⟨w, hwJ, hwNorm⟩ :=
    exists_ccmArchimedeanFormDomain_norm_enorm_le_of_tendsto a u f
      (by simpa only [huJ] using hxf)
      (ENNReal.ofReal (Real.sqrt E)) (by simp) huTightEnorm
  have hwv : w = v := ccmArchimedeanFormToAperture_injective a (hwJ.trans hvJ.symm)
  subst w
  have hvNormReal : ‖v.1‖ ≤ Real.sqrt E := by
    rw [← ofReal_norm] at hwNorm
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg E)).mp hwNorm
  have hvSq : ‖v.1‖ ^ 2 ≤ E := by
    nlinarith [Real.sq_sqrt hE0, norm_nonneg v.1, Real.sqrt_nonneg E]
  dsimp [E] at hvSq
  linarith

def ccmRestrictedWeilPhysicalFormDomain (a : SuzukiPositiveAperture) :
    Set (suzukiApertureHilbert a) :=
  Set.range (ccmArchimedeanFormToAperture a)

noncomputable def ccmRestrictedWeilPhysicalFormLift (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : f ∈ ccmRestrictedWeilPhysicalFormDomain a) :
    CCMArchimedeanFormDomain a :=
  Classical.choose hf

theorem ccmRestrictedWeilPhysicalFormLift_spec (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : f ∈ ccmRestrictedWeilPhysicalFormDomain a) :
    ccmArchimedeanFormToAperture a (ccmRestrictedWeilPhysicalFormLift a f hf) = f :=
  Classical.choose_spec hf

/-- Exact restricted Weil quadratic form extended by `+∞` off its physical form domain. -/
noncomputable def ccmRestrictedWeilExtendedSourceQuadratic (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : EReal :=
  by
    classical
    exact if hf : f ∈ ccmRestrictedWeilPhysicalFormDomain a then
      (ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilPhysicalFormLift a f hf) : EReal)
    else ⊤

theorem ccmRestrictedWeilExtendedSourceQuadratic_embedding (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilExtendedSourceQuadratic a (ccmArchimedeanFormToAperture a u) =
      (ccmRestrictedWeilSourceQuadratic a u : EReal) := by
  unfold ccmRestrictedWeilExtendedSourceQuadratic
  have hmem : ccmArchimedeanFormToAperture a u ∈ ccmRestrictedWeilPhysicalFormDomain a :=
    ⟨u, rfl⟩
  rw [dif_pos hmem]
  apply congrArg (fun v : CCMArchimedeanFormDomain a =>
    (ccmRestrictedWeilSourceQuadratic a v : EReal))
  apply ccmArchimedeanFormToAperture_injective a
  exact ccmRestrictedWeilPhysicalFormLift_spec a _ hmem

theorem ccmRestrictedWeilExtendedSourceQuadratic_eq_top_of_not_mem (a : SuzukiPositiveAperture)
    {f : suzukiApertureHilbert a} (hf : f ∉ ccmRestrictedWeilPhysicalFormDomain a) :
    ccmRestrictedWeilExtendedSourceQuadratic a f = ⊤ := by
  simp [ccmRestrictedWeilExtendedSourceQuadratic, hf]

theorem ccmRestrictedWeilExtendedSourceQuadratic_ne_bot (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : ccmRestrictedWeilExtendedSourceQuadratic a f ≠ ⊥ := by
  unfold ccmRestrictedWeilExtendedSourceQuadratic
  split_ifs <;> simp

theorem ccmRestrictedWeilExtendedSourceQuadratic_le_coe_iff (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (c : ℝ) :
    ccmRestrictedWeilExtendedSourceQuadratic a f ≤ (c : EReal) ↔
      ∃ u : CCMArchimedeanFormDomain a,
        ccmArchimedeanFormToAperture a u = f ∧
          ccmRestrictedWeilSourceQuadratic a u ≤ c := by
  constructor
  · intro h
    unfold ccmRestrictedWeilExtendedSourceQuadratic at h
    split at h
    next hf =>
      refine ⟨ccmRestrictedWeilPhysicalFormLift a f hf,
        ccmRestrictedWeilPhysicalFormLift_spec a f hf, ?_⟩
      exact EReal.coe_le_coe_iff.mp h
    next hf => simp at h
  · rintro ⟨u, rfl, hu⟩
    rw [ccmRestrictedWeilExtendedSourceQuadratic_embedding]
    exact EReal.coe_le_coe hu

theorem lowerSemicontinuous_ccmRestrictedWeilExtendedSourceQuadratic (a : SuzukiPositiveAperture) :
    LowerSemicontinuous (ccmRestrictedWeilExtendedSourceQuadratic a) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  by_cases hytop : y = ⊤
  · subst y
    simp
  by_cases hybot : y = ⊥
  · subst y
    have hempty : ccmRestrictedWeilExtendedSourceQuadratic a ⁻¹' Iic (⊥ : EReal) = ∅ := by
      ext f
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun h => ccmRestrictedWeilExtendedSourceQuadratic_ne_bot a f (le_bot_iff.mp h)
    rw [hempty]
    exact isClosed_empty
  have hycoe : (y.toReal : EReal) = y := EReal.coe_toReal hytop hybot
  rw [← hycoe]
  have hset : ccmRestrictedWeilExtendedSourceQuadratic a ⁻¹' Iic (y.toReal : EReal) =
      {f : suzukiApertureHilbert a |
        ∃ u : CCMArchimedeanFormDomain a,
          ccmArchimedeanFormToAperture a u = f ∧
            ccmRestrictedWeilSourceQuadratic a u ≤ y.toReal} := by
    ext f
    exact ccmRestrictedWeilExtendedSourceQuadratic_le_coe_iff a f y.toReal
  rw [hset]
  exact isClosed_ccmRestrictedWeilSource_sublevel a y.toReal

/-- The extended source form has the literal uniform quadratic lower bound supplied by the
bounded polar--prime remainder.  Off the form domain the value is `+∞`, so the same estimate holds
on the whole physical Hilbert space. -/
theorem ccmRestrictedWeilExtendedSourceQuadratic_lowerBound
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ((-‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖ ^ 2 : ℝ) : EReal) ≤
      ccmRestrictedWeilExtendedSourceQuadratic a f := by
  by_cases hf : f ∈ ccmRestrictedWeilPhysicalFormDomain a
  · let u := ccmRestrictedWeilPhysicalFormLift a f hf
    have huf : ccmArchimedeanFormToAperture a u = f :=
      ccmRestrictedWeilPhysicalFormLift_spec a f hf
    have hlower := ccmRestrictedWeilForm_lowerBound a u
    rw [ccmRestrictedWeilForm_self_re_eq_source, huf] at hlower
    unfold ccmRestrictedWeilExtendedSourceQuadratic
    rw [dif_pos hf]
    exact EReal.coe_le_coe hlower
  · rw [ccmRestrictedWeilExtendedSourceQuadratic_eq_top_of_not_mem a hf]
    exact le_top

/-- **Connes--Consani (2021), Proposition `Hilbert`, literal restricted-Weil form.**

The displayed source formula, extended by `+∞` outside its exact weighted form domain, is a
lower-semicontinuous quadratic form on the physical aperture and is bounded below by a fixed
multiple of physical `L²` mass. -/
theorem connesConsani_Hilbert (a : SuzukiPositiveAperture) :
    LowerSemicontinuous (ccmRestrictedWeilExtendedSourceQuadratic a) ∧
      ∀ f : suzukiApertureHilbert a,
        ((-‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖ ^ 2 : ℝ) : EReal) ≤
          ccmRestrictedWeilExtendedSourceQuadratic a f :=
  ⟨lowerSemicontinuous_ccmRestrictedWeilExtendedSourceQuadratic a,
    ccmRestrictedWeilExtendedSourceQuadratic_lowerBound a⟩

theorem ccmRestrictedWeilExtendedSourceQuadratic_le_liminf_of_tendsto
    (a : SuzukiPositiveAperture) (g : ℕ → CCMArchimedeanFormDomain a)
    (f : suzukiApertureHilbert a)
    (hgf : Tendsto (fun n => ccmArchimedeanFormToAperture a (g n)) atTop (nhds f)) :
    ccmRestrictedWeilExtendedSourceQuadratic a f ≤
      liminf (fun n => (ccmRestrictedWeilSourceQuadratic a (g n) : EReal)) atTop := by
  have hlsc : ccmRestrictedWeilExtendedSourceQuadratic a f ≤
      liminf (ccmRestrictedWeilExtendedSourceQuadratic a) (nhds f) :=
    lowerSemicontinuousAt_iff_le_liminf.mp
      (lowerSemicontinuous_ccmRestrictedWeilExtendedSourceQuadratic a f)
  have hmap := hgf.liminf_le_liminf_comp (u := ccmRestrictedWeilExtendedSourceQuadratic a)
  refine hlsc.trans (hmap.trans_eq ?_)
  apply liminf_congr
  filter_upwards with n
  exact ccmRestrictedWeilExtendedSourceQuadratic_embedding a (g n)

def ccmRestrictedWeilLaurentLiminfValues (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : Set EReal :=
  {L | ∃ g : ℕ → CCMArchimedeanFormDomain a,
    (∀ n, g n ∈ ccmArchimedeanLaurentSubmodule a) ∧
    Tendsto (fun n => ccmArchimedeanFormToAperture a (g n)) atTop (nhds f) ∧
    L = liminf
      (fun n => (ccmRestrictedWeilSourceQuadratic a (g n) : EReal)) atTop}

noncomputable def ccmRestrictedWeilLaurentLiminfEnvelope (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) : EReal :=
  sInf (ccmRestrictedWeilLaurentLiminfValues a f)

theorem ccmRestrictedWeilExtendedSourceQuadratic_le_laurentLiminfEnvelope
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmRestrictedWeilExtendedSourceQuadratic a f ≤ ccmRestrictedWeilLaurentLiminfEnvelope a f := by
  apply le_sInf
  intro L hL
  rcases hL with ⟨g, hgLaurent, hgf, rfl⟩
  exact ccmRestrictedWeilExtendedSourceQuadratic_le_liminf_of_tendsto a g f hgf

theorem exists_ccmRestrictedWeil_laurent_recovery
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ∃ g : ℕ → CCMArchimedeanFormDomain a,
      (∀ n, g n ∈ ccmArchimedeanLaurentSubmodule a) ∧
      Tendsto g atTop (nhds u) ∧
      Tendsto (fun n => ccmArchimedeanFormToAperture a (g n)) atTop
        (nhds (ccmArchimedeanFormToAperture a u)) ∧
      Tendsto (fun n => ccmRestrictedWeilSourceQuadratic a (g n)) atTop
        (nhds (ccmRestrictedWeilSourceQuadratic a u)) := by
  have huClosure : u ∈ closure
      (ccmArchimedeanLaurentSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
    rw [ccmArchimedeanLaurentPolynomials_formCore]
    trivial
  obtain ⟨g, hg, hgu⟩ := mem_closure_iff_seq_limit.mp huClosure
  refine ⟨g, hg, hgu, ?_, ?_⟩
  · exact ((ccmArchimedeanFormToAperture a).continuous.tendsto u).comp hgu
  · exact ((continuous_ccmRestrictedWeilSourceQuadratic a).tendsto u).comp hgu

theorem ccmRestrictedWeilLaurentLiminfEnvelope_le_extended_of_mem
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (hf : f ∈ ccmRestrictedWeilPhysicalFormDomain a) :
    ccmRestrictedWeilLaurentLiminfEnvelope a f ≤ ccmRestrictedWeilExtendedSourceQuadratic a f := by
  let u := ccmRestrictedWeilPhysicalFormLift a f hf
  obtain ⟨g, hgLaurent, hgu, hgf, hgQ⟩ :=
    exists_ccmRestrictedWeil_laurent_recovery a u
  have huf : ccmArchimedeanFormToAperture a u = f :=
    ccmRestrictedWeilPhysicalFormLift_spec a f hf
  have hgf' : Tendsto (fun n => ccmArchimedeanFormToAperture a (g n)) atTop
      (nhds f) := by simpa only [huf] using hgf
  have hgQE : Tendsto
      (fun n => (ccmRestrictedWeilSourceQuadratic a (g n) : EReal)) atTop
      (nhds (ccmRestrictedWeilSourceQuadratic a u : EReal)) :=
    EReal.tendsto_coe.mpr hgQ
  have hvalue : (ccmRestrictedWeilSourceQuadratic a u : EReal) ∈
      ccmRestrictedWeilLaurentLiminfValues a f := by
    refine ⟨g, hgLaurent, hgf', ?_⟩
    exact hgQE.liminf_eq.symm
  apply (sInf_le hvalue).trans_eq
  unfold ccmRestrictedWeilExtendedSourceQuadratic
  rw [dif_pos hf]

/-- Connes--Consani (2021), Proposition `Hilbert1`: exact lower-semicontinuous
extension of the restricted Weil quadratic form is the Laurent-sequence liminf envelope. -/
theorem connesConsani_Hilbert1
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmRestrictedWeilExtendedSourceQuadratic a f = ccmRestrictedWeilLaurentLiminfEnvelope a f := by
  apply le_antisymm
  · exact ccmRestrictedWeilExtendedSourceQuadratic_le_laurentLiminfEnvelope a f
  · by_cases hf : f ∈ ccmRestrictedWeilPhysicalFormDomain a
    · exact ccmRestrictedWeilLaurentLiminfEnvelope_le_extended_of_mem a f hf
    · rw [ccmRestrictedWeilExtendedSourceQuadratic_eq_top_of_not_mem a hf]
      exact le_top

end RHTower

