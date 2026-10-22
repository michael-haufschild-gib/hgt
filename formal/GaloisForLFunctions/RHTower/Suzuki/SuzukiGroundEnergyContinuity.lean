import GaloisForLFunctions.RHTower.Suzuki.SuzukiRayleighInfimum
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilApertureMonotonicity
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniHilbertOne
import Mathlib.Topology.Order.Compact

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-!
# Continuity of Suzuki's exact ground energy

This module formalizes Suzuki (2026), Theorem 1.3 for the literal lowest
eigenvalue of the restricted Weil operator.  Right continuity follows from
compact normalized ground states and a no-boundary-escape theorem.  Left
continuity follows from the exact strict smooth form core: compact support lets
one fixed Rayleigh test survive on a whole smaller-aperture neighborhood.

No Riemann-hypothesis assumption, added axiom, or numerical computation is used.
-/

/-- Unitary interval transport does not change Suzuki's exact ground energy. -/
theorem suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy
    (a : SuzukiPositiveAperture) :
    suzukiWeilIntervalGroundEnergy a =
      ccmRestrictedWeilGroundEnergy a := by
  apply le_antisymm
  · obtain ⟨u, hJu, hu⟩ := ccmRestrictedWeilSource_exists_groundFormState a
    have hfloor := suzukiWeilIntervalGroundEnergy_mul_formNorm_sq_le_source a u
    have hnorm : ‖suzukiWeilIntervalFormEmbedding a u‖ =
        ‖ccmArchimedeanFormToAperture a u‖ := by
      change ‖suzukiPhysicalToApertureCLM a
          (ccmArchimedeanFormToAperture a u)‖ = _
      exact (suzukiApertureL2Equiv a).symm.norm_map _
    rw [hu, hnorm] at hfloor
    exact le_of_mul_le_mul_right hfloor
      (sq_pos_of_pos (norm_pos_iff.mpr hJu))
  · obtain ⟨u, hJu, hu⟩ := exists_suzukiWeilGroundFormVector a
    have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u
    have hnorm : ‖ccmArchimedeanFormToAperture a u‖ =
        ‖suzukiWeilIntervalFormEmbedding a u‖ := by
      change _ = ‖suzukiPhysicalToApertureCLM a
          (ccmArchimedeanFormToAperture a u)‖
      exact ((suzukiApertureL2Equiv a).symm.norm_map _).symm
    rw [hu, hnorm] at hfloor
    exact le_of_mul_le_mul_right hfloor
      (sq_pos_of_pos (norm_pos_iff.mpr hJu))

/-- Concrete Suzuki lowest eigenvalue is antitone under aperture enlargement. -/
theorem antitone_suzukiWeilIntervalGroundEnergy :
    Antitone suzukiWeilIntervalGroundEnergy := by
  intro a b hab
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy,
    suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  exact ccmRestrictedWeilGroundEnergy_antitone hab

/-! ## No boundary escape for right-aperture limits -/

/-- Canonical apertures decreasing to `a` from the right. -/
def suzukiRightAperture (a : SuzukiPositiveAperture) (n : ℕ) :
    SuzukiPositiveAperture :=
  ⟨a.1 + 1 / (n + 1 : ℝ), by
    have hn : 0 < (n + 1 : ℝ) := by positivity
    exact add_pos a.2 (one_div_pos.mpr hn)⟩

@[simp] theorem suzukiRightAperture_coe
    (a : SuzukiPositiveAperture) (n : ℕ) :
    (suzukiRightAperture a n).1 = a.1 + 1 / (n + 1 : ℝ) := rfl

theorem suzukiRightAperture_gt
    (a : SuzukiPositiveAperture) (n : ℕ) :
    a.1 < (suzukiRightAperture a n).1 := by
  simp only [suzukiRightAperture_coe]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  exact lt_add_of_pos_right _ (one_div_pos.mpr hn)

theorem antitone_suzukiRightAperture
    (a : SuzukiPositiveAperture) :
    Antitone (suzukiRightAperture a) := by
  intro m n hmn
  apply Subtype.coe_le_coe.mp
  simp only [suzukiRightAperture_coe]
  gcongr

theorem tendsto_suzukiRightAperture
    (a : SuzukiPositiveAperture) :
    Tendsto (suzukiRightAperture a) atTop (nhds a) := by
  rw [tendsto_subtype_rng]
  simpa only [suzukiRightAperture_coe, add_zero] using
    (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

theorem indicatorCutoff_central_eq_self_of_le'
    {a b : ℝ} (hab : a ≤ b) (f : SoninL2)
    (hf : indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) f = f) :
    indicatorCutoff (centralInterval b)
      (measurableSet_centralInterval b) f = f := by
  apply Lp.ext
  have hfix :
      (indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f : ℝ → ℂ) =ᵐ[volume] f := by
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

/-- Strong `L²` limits of vectors supported in a cofinal sequence of right
apertures are supported in the limiting aperture. -/
theorem indicatorCutoff_limit_suzukiRightAperture
    (a : SuzukiPositiveAperture) (phi : ℕ → ℕ)
    (hphi : Tendsto phi atTop atTop)
    (f : ℕ → SoninL2) (g : SoninL2)
    (hfix : ∀ n,
      indicatorCutoff (centralInterval (suzukiRightAperture a (phi n)).1)
        (measurableSet_centralInterval (suzukiRightAperture a (phi n)).1)
        (f n) = f n)
    (hfg : Tendsto f atTop (nhds g)) :
    indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) g = g := by
  have hfixed : ∀ k,
      indicatorCutoff (centralInterval (suzukiRightAperture a k).1)
        (measurableSet_centralInterval (suzukiRightAperture a k).1) g = g := by
    intro k
    let P := indicatorCutoff (centralInterval (suzukiRightAperture a k).1)
      (measurableSet_centralInterval (suzukiRightAperture a k).1)
    have heq : ∀ᶠ n in atTop, P (f n) = f n := by
      filter_upwards [hphi.eventually (eventually_ge_atTop k)] with n hn
      exact indicatorCutoff_central_eq_self_of_le'
        (show (suzukiRightAperture a (phi n)).1 ≤
          (suzukiRightAperture a k).1 by
          exact Subtype.coe_le_coe.mpr (antitone_suzukiRightAperture a hn))
        (f n) (hfix n)
    have hPfg : Tendsto (fun n => P (f n)) atTop (nhds (P g)) :=
      (P.continuous.tendsto g).comp hfg
    have hPfg' : Tendsto (fun n => P (f n)) atTop (nhds g) :=
      hfg.congr' (heq.mono fun _ hn => hn.symm)
    exact tendsto_nhds_unique hPfg hPfg'
  apply Lp.ext
  have hfixedAE : ∀ᵐ x : ℝ ∂volume, ∀ k,
      (indicatorCutoff (centralInterval (suzukiRightAperture a k).1)
        (measurableSet_centralInterval (suzukiRightAperture a k).1) g :
          ℝ → ℂ) x = g x := by
    exact ae_all_iff.2 fun k => by
      rw [hfixed k]
      exact Eventually.of_forall fun _ => rfl
  have hcutAE : ∀ᵐ x : ℝ ∂volume, ∀ k,
      (indicatorCutoff (centralInterval (suzukiRightAperture a k).1)
        (measurableSet_centralInterval (suzukiRightAperture a k).1) g :
          ℝ → ℂ) x =
        (centralInterval (suzukiRightAperture a k).1).indicator
          (fun y => g y) x := by
    exact ae_all_iff.2 fun k =>
      indicatorCutoff_ae _ _ g
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) g, hfixedAE, hcutAE]
      with x hcut hfixedX hcutX
  rw [hcut]
  by_cases hxa : x ∈ centralInterval a.1
  · rw [Set.indicator_of_mem hxa]
  · rw [Set.indicator_of_notMem hxa]
    have houtside : x < -a.1 ∨ a.1 < x := by
      rw [centralInterval, Set.mem_Icc] at hxa
      rcases not_and_or.mp hxa with hleft | hright
      · exact Or.inl (lt_of_not_ge hleft)
      · exact Or.inr (lt_of_not_ge hright)
    obtain ⟨k, hk⟩ : ∃ k, x ∉ centralInterval (suzukiRightAperture a k).1 := by
      rcases houtside with hxleft | hxright
      · have haNegX : a.1 < -x := by linarith
        obtain ⟨k, hk⟩ := ((tendsto_suzukiRightAperture a).eventually
          (show {b : SuzukiPositiveAperture | b.1 < -x} ∈ nhds a by
            exact (isOpen_lt continuous_subtype_val continuous_const).mem_nhds haNegX)).exists
        refine ⟨k, ?_⟩
        intro hxmem
        rw [centralInterval, Set.mem_Icc] at hxmem
        linarith [hxmem.1, hxmem.2]
      · obtain ⟨k, hk⟩ := ((tendsto_suzukiRightAperture a).eventually
          (show {b : SuzukiPositiveAperture | b.1 < x} ∈ nhds a by
            exact (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hxright)).exists
        refine ⟨k, ?_⟩
        intro hxmem
        rw [centralInterval, Set.mem_Icc] at hxmem
        linarith [hxmem.1, hxmem.2]
    have hzero : g x = 0 := by
      calc
        g x =
            (indicatorCutoff (centralInterval (suzukiRightAperture a k).1)
              (measurableSet_centralInterval (suzukiRightAperture a k).1) g :
                ℝ → ℂ) x := (hfixedX k).symm
        _ = (centralInterval (suzukiRightAperture a k).1).indicator
              (fun y => g y) x := hcutX k
        _ = 0 := Set.indicator_of_notMem hk _
    exact hzero.symm

/-! ## Canonically normalized exact ground states -/

noncomputable def ccmRestrictedWeilGroundFormVector
    (a : SuzukiPositiveAperture) : CCMArchimedeanFormDomain a :=
  Classical.choose (ccmRestrictedWeilSource_exists_groundFormState a)

theorem ccmRestrictedWeilGroundFormVector_embedding_ne_zero
    (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormToAperture a
      (ccmRestrictedWeilGroundFormVector a) ≠ 0 :=
  (Classical.choose_spec
    (ccmRestrictedWeilSource_exists_groundFormState a)).1

theorem ccmRestrictedWeilGroundFormVector_source
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a
        (ccmRestrictedWeilGroundFormVector a) =
      ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a
          (ccmRestrictedWeilGroundFormVector a)‖ ^ 2 :=
  (Classical.choose_spec
    (ccmRestrictedWeilSource_exists_groundFormState a)).2

theorem ccmRestrictedWeilSourceQuadratic_smul
    (a : SuzukiPositiveAperture) (c : ℂ)
    (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a (c • u) =
      ‖c‖ ^ 2 * ccmRestrictedWeilSourceQuadratic a u := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source,
    ← ccmRestrictedWeilForm_self_re_eq_source]
  unfold ccmRestrictedWeilForm
  simp only [map_smul]
  rw [inner_smul_left u (c • u) c, inner_smul_right u u c,
    inner_smul_left
      (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a u))
      (c • ccmArchimedeanFormToAperture a u) c,
    inner_smul_right
      (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u) c]
  rw [← mul_add, ← mul_add, ← mul_assoc]
  have hc : (starRingEnd ℂ) c * c = (‖c‖ ^ 2 : ℝ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hc]
  simp [pow_two]

noncomputable def ccmRestrictedWeilNormalizedGroundFormVector
    (a : SuzukiPositiveAperture) : CCMArchimedeanFormDomain a :=
  ((‖ccmArchimedeanFormToAperture a
      (ccmRestrictedWeilGroundFormVector a)‖ : ℂ)⁻¹) •
    ccmRestrictedWeilGroundFormVector a

theorem norm_ccmRestrictedWeilNormalizedGroundFormVector_embedding
    (a : SuzukiPositiveAperture) :
    ‖ccmArchimedeanFormToAperture a
      (ccmRestrictedWeilNormalizedGroundFormVector a)‖ = 1 := by
  let r := ‖ccmArchimedeanFormToAperture a
    (ccmRestrictedWeilGroundFormVector a)‖
  have hr : 0 < r := norm_pos_iff.mpr
    (ccmRestrictedWeilGroundFormVector_embedding_ne_zero a)
  rw [ccmRestrictedWeilNormalizedGroundFormVector, map_smul]
  change ‖((r : ℂ)⁻¹) • ccmArchimedeanFormToAperture a
      (ccmRestrictedWeilGroundFormVector a)‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  exact inv_mul_cancel₀ hr.ne'

theorem ccmRestrictedWeilNormalizedGroundFormVector_source
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a
        (ccmRestrictedWeilNormalizedGroundFormVector a) =
      ccmRestrictedWeilGroundEnergy a := by
  let r := ‖ccmArchimedeanFormToAperture a
    (ccmRestrictedWeilGroundFormVector a)‖
  have hr : 0 < r := norm_pos_iff.mpr
    (ccmRestrictedWeilGroundFormVector_embedding_ne_zero a)
  rw [ccmRestrictedWeilNormalizedGroundFormVector,
    ccmRestrictedWeilSourceQuadratic_smul,
    ccmRestrictedWeilGroundFormVector_source]
  change ‖((r : ℂ)⁻¹)‖ ^ 2 *
      (ccmRestrictedWeilGroundEnergy a * r ^ 2) = _
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  field_simp [hr.ne']

/-! ## Compact normalized right-ground family in one fixed aperture -/

noncomputable def ccmRestrictedWeilNormalizedRightGroundExtension
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMArchimedeanFormDomain (suzukiRightAperture a 0) :=
  Classical.choose (exists_ccmArchimedeanFormDomain_extension
    (show (suzukiRightAperture a n).1 ≤
        (suzukiRightAperture a 0).1 by
      exact Subtype.coe_le_coe.mpr
        (antitone_suzukiRightAperture a (Nat.zero_le n)))
    (ccmRestrictedWeilNormalizedGroundFormVector
      (suzukiRightAperture a n)))

theorem ccmRestrictedWeilNormalizedRightGroundExtension_val
    (a : SuzukiPositiveAperture) (n : ℕ) :
    (ccmRestrictedWeilNormalizedRightGroundExtension a n).1 =
      (ccmRestrictedWeilNormalizedGroundFormVector
        (suzukiRightAperture a n)).1 :=
  Classical.choose_spec (exists_ccmArchimedeanFormDomain_extension
    (show (suzukiRightAperture a n).1 ≤
        (suzukiRightAperture a 0).1 by
      exact Subtype.coe_le_coe.mpr
        (antitone_suzukiRightAperture a (Nat.zero_le n)))
    (ccmRestrictedWeilNormalizedGroundFormVector
      (suzukiRightAperture a n)))

theorem norm_ccmRestrictedWeilNormalizedRightGroundExtension_embedding
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖ccmArchimedeanFormToAperture (suzukiRightAperture a 0)
      (ccmRestrictedWeilNormalizedRightGroundExtension a n)‖ = 1 := by
  rw [norm_ccmArchimedeanFormToAperture_eq_of_val_eq
    (ccmRestrictedWeilNormalizedRightGroundExtension_val a n)]
  exact norm_ccmRestrictedWeilNormalizedGroundFormVector_embedding _

theorem ccmRestrictedWeilNormalizedRightGroundExtension_source
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilSourceQuadratic (suzukiRightAperture a 0)
        (ccmRestrictedWeilNormalizedRightGroundExtension a n) =
      ccmRestrictedWeilGroundEnergy (suzukiRightAperture a n) := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_of_val_eq
    (show (suzukiRightAperture a n).1 ≤
        (suzukiRightAperture a 0).1 by
      exact Subtype.coe_le_coe.mpr
        (antitone_suzukiRightAperture a (Nat.zero_le n)))
    (ccmRestrictedWeilNormalizedRightGroundExtension_val a n)]
  exact ccmRestrictedWeilNormalizedGroundFormVector_source _

theorem norm_sq_ccmRestrictedWeilNormalizedRightGroundExtension_le
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖(ccmRestrictedWeilNormalizedRightGroundExtension a n).1‖ ^ 2 ≤
      max 0 (ccmRestrictedWeilGroundEnergy a +
        ‖ccmRestrictedWeilBoundedRemainder
          (suzukiRightAperture a 0)‖) := by
  have hbound := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass
    (suzukiRightAperture a 0)
    (ccmRestrictedWeilNormalizedRightGroundExtension a n)
  rw [ccmRestrictedWeilNormalizedRightGroundExtension_source,
    norm_ccmRestrictedWeilNormalizedRightGroundExtension_embedding] at hbound
  simp only [one_pow, mul_one] at hbound
  have hmono : ccmRestrictedWeilGroundEnergy (suzukiRightAperture a n) ≤
      ccmRestrictedWeilGroundEnergy a :=
    ccmRestrictedWeilGroundEnergy_antitone
      (suzukiRightAperture_gt a n).le
  have hadd : ccmRestrictedWeilGroundEnergy (suzukiRightAperture a n) +
        ‖ccmRestrictedWeilBoundedRemainder (suzukiRightAperture a 0)‖ ≤
      ccmRestrictedWeilGroundEnergy a +
        ‖ccmRestrictedWeilBoundedRemainder (suzukiRightAperture a 0)‖ := by
    linarith
  exact hbound.trans (le_max_of_le_right hadd)

theorem norm_ccmRestrictedWeilNormalizedRightGroundExtension_le
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖ccmRestrictedWeilNormalizedRightGroundExtension a n‖ ≤
      Real.sqrt (max 0 (ccmRestrictedWeilGroundEnergy a +
        ‖ccmRestrictedWeilBoundedRemainder
          (suzukiRightAperture a 0)‖)) := by
  have hsq := norm_sq_ccmRestrictedWeilNormalizedRightGroundExtension_le a n
  have hnonneg : 0 ≤ max 0 (ccmRestrictedWeilGroundEnergy a +
      ‖ccmRestrictedWeilBoundedRemainder (suzukiRightAperture a 0)‖) :=
    le_max_left _ _
  have hsqrt : 0 ≤ Real.sqrt (max 0 (ccmRestrictedWeilGroundEnergy a +
      ‖ccmRestrictedWeilBoundedRemainder (suzukiRightAperture a 0)‖)) :=
    Real.sqrt_nonneg _
  change ‖(ccmRestrictedWeilNormalizedRightGroundExtension a n).1‖ ≤ _
  nlinarith [Real.sq_sqrt hnonneg,
    norm_nonneg (ccmRestrictedWeilNormalizedRightGroundExtension a n),
    hsqrt]

/-- Compactness extracts a normalized physical limit from the exact right-ground
family, and the moving-support theorem prevents boundary escape. -/
theorem exists_suzukiRightGroundCompactLimit
    (a : SuzukiPositiveAperture) :
    ∃ fstar : suzukiApertureHilbert (suzukiRightAperture a 0),
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧
        Tendsto
          (fun n => ccmArchimedeanFormToAperture
            (suzukiRightAperture a 0)
            (ccmRestrictedWeilNormalizedRightGroundExtension a (phi n)))
          atTop (nhds fstar) ∧
        indicatorCutoff (centralInterval a.1)
            (measurableSet_centralInterval a.1)
            (fstar : SoninL2) = (fstar : SoninL2) ∧
        ‖fstar‖ = 1 := by
  let b := suzukiRightAperture a 0
  let J := ccmArchimedeanFormToAperture b
  let radius := Real.sqrt (max 0 (ccmRestrictedWeilGroundEnergy a +
    ‖ccmRestrictedWeilBoundedRemainder b‖))
  have hmem : ∀ n : ℕ,
      J (ccmRestrictedWeilNormalizedRightGroundExtension a n) ∈
        closure (J '' Metric.closedBall
          (0 : CCMArchimedeanFormDomain b) radius) := by
    intro n
    apply subset_closure
    refine ⟨ccmRestrictedWeilNormalizedRightGroundExtension a n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_ccmRestrictedWeilNormalizedRightGroundExtension_le a n
  obtain ⟨fstar, -, phi, hphi, hconv⟩ :=
    (isCompactOperator_ccmArchimedeanFormToAperture b
      |>.isCompact_closure_image_closedBall radius).tendsto_subseq hmem
  refine ⟨fstar, phi, hphi, hconv, ?_, ?_⟩
  · have hconvGlobal : Tendsto
        (fun n =>
          (ccmArchimedeanFormToAperture b
            (ccmRestrictedWeilNormalizedRightGroundExtension a (phi n)) :
              SoninL2)) atTop (nhds (fstar : SoninL2)) :=
      (continuous_subtype_val.tendsto fstar).comp hconv
    apply indicatorCutoff_limit_suzukiRightAperture a phi
      hphi.tendsto_atTop _ _ _ hconvGlobal
    intro n
    have hcoe := ccmArchimedeanFormToAperture_coe_eq_of_val_eq
      (ccmRestrictedWeilNormalizedRightGroundExtension_val a (phi n))
    rw [hcoe]
    exact indicatorCutoff_suzukiApertureHilbert
      (suzukiRightAperture a (phi n))
      (ccmArchimedeanFormToAperture
        (suzukiRightAperture a (phi n))
        (ccmRestrictedWeilNormalizedGroundFormVector
          (suzukiRightAperture a (phi n))))
  · have hnormLim : Tendsto
        (fun n => ‖ccmArchimedeanFormToAperture b
          (ccmRestrictedWeilNormalizedRightGroundExtension a (phi n))‖)
        atTop (nhds ‖fstar‖) :=
      (continuous_norm.tendsto fstar).comp hconv
    have hnormOne : Tendsto
        (fun n => ‖ccmArchimedeanFormToAperture b
          (ccmRestrictedWeilNormalizedRightGroundExtension a (phi n))‖)
        atTop (nhds 1) := by
      have hnormEq : ∀ n : ℕ,
          ‖ccmArchimedeanFormToAperture b
            (ccmRestrictedWeilNormalizedRightGroundExtension a (phi n))‖ = 1 := by
        intro n
        simpa only [b] using
          norm_ccmRestrictedWeilNormalizedRightGroundExtension_embedding a (phi n)
      simpa only [hnormEq]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    exact tendsto_nhds_unique hnormLim hnormOne

/-! ## Exact right continuity of the ground energy -/

theorem antitone_ccmRestrictedWeilGroundEnergy :
    Antitone ccmRestrictedWeilGroundEnergy := by
  intro a b hab
  exact ccmRestrictedWeilGroundEnergy_antitone hab

theorem norm_suzukiWeilIntervalFormEmbedding_eq_physical
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ‖suzukiWeilIntervalFormEmbedding a u‖ =
      ‖ccmArchimedeanFormToAperture a u‖ := by
  exact (suzukiApertureL2Equiv a).symm.norm_map _

/-- Compact containment sharpens strict support inside `(-a,a)` to support
inside one genuinely smaller positive aperture. -/
theorem exists_strict_smaller_aperture_of_compact_tsupport
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    ∃ b : SuzukiPositiveAperture,
      b.1 < a.1 ∧ tsupport (u : ℝ → ℂ) ⊆ Ioo (-b.1) b.1 := by
  by_cases hne : (tsupport (u : ℝ → ℂ)).Nonempty
  · obtain ⟨x, hx, hmax⟩ := u.hasCompactSupport.exists_isMaxOn hne
      continuous_abs.continuousOn
    have hxlt : |x| < a.1 := by
      exact abs_lt.mpr (u.tsupport_subset hx)
    let radius := (|x| + a.1) / 2
    have hradiusPos : 0 < radius := by
      dsimp only [radius]
      linarith [abs_nonneg x, a.2]
    have hradiusLt : radius < a.1 := by
      dsimp only [radius]
      linarith
    refine ⟨⟨radius, hradiusPos⟩, hradiusLt, ?_⟩
    intro y hy
    have hyabs : |y| ≤ |x| := hmax hy
    have hyabslt : |y| < radius := by
      dsimp only [radius]
      linarith
    exact abs_lt.mp hyabslt
  · let radius := a.1 / 2
    have hradiusPos : 0 < radius := by
      dsimp only [radius]
      linarith [a.2]
    have hradiusLt : radius < a.1 := by
      dsimp only [radius]
      linarith [a.2]
    refine ⟨⟨radius, hradiusPos⟩, hradiusLt, ?_⟩
    intro y hy
    exact False.elim (hne ⟨y, hy⟩)

/-- Rebundle one strict smooth source at any smaller aperture that still
contains its compact support. -/
def CCMComplexSmoothInteriorSource.restrictAperture
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (b : SuzukiPositiveAperture)
    (hsupport : tsupport (u : ℝ → ℂ) ⊆ Ioo (-b.1) b.1) :
    CCMComplexSmoothInteriorSource b where
  toFun := u.toFun
  smooth := u.smooth
  hasCompactSupport := u.hasCompactSupport
  tsupport_subset := hsupport

@[simp] theorem CCMComplexSmoothInteriorSource.restrictAperture_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (b : SuzukiPositiveAperture)
    (hsupport : tsupport (u : ℝ → ℂ) ⊆ Ioo (-b.1) b.1)
    (x : ℝ) :
    u.restrictAperture b hsupport x = u x := rfl

theorem CCMComplexSmoothInteriorSource.restrictAperture_toCCMFormVector_val
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (b : SuzukiPositiveAperture)
    (hsupport : tsupport (u : ℝ → ℂ) ⊆ Ioo (-b.1) b.1) :
    (u.restrictAperture b hsupport).toCCMFormVector.1 =
      u.toCCMFormVector.1 := by
  apply ccmArchimedeanFourierToTime_injective
  apply Lp.ext
  filter_upwards [
    (u.restrictAperture b hsupport).toCCMFormVector_physical_coeFn,
    u.toCCMFormVector_physical_coeFn] with xi hleft hright
  change ((ccmArchimedeanFourierToTime
      (u.restrictAperture b hsupport).toCCMFormVector.1 : SoninL2) : ℝ → ℂ) xi =
    (u.restrictAperture b hsupport) xi at hleft
  change ((ccmArchimedeanFourierToTime
      u.toCCMFormVector.1 : SoninL2) : ℝ → ℂ) xi = u xi at hright
  exact hleft.trans (hright.symm.trans rfl)

theorem exists_suzukiSmoothInteriorRayleigh_lt_groundEnergy_add
    (a : SuzukiPositiveAperture) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : CCMComplexSmoothInteriorSource a,
      suzukiWeilIntervalFormEmbedding a u.toCCMFormVector ≠ 0 ∧
      suzukiWeilIntervalFormRayleigh a u.toCCMFormVector <
        suzukiWeilIntervalGroundEnergy a + epsilon := by
  have hGLB := isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy a
  have hexists : ∃ r ∈ suzukiSmoothInteriorRayleighSet a,
      r < suzukiWeilIntervalGroundEnergy a + epsilon := by
    by_contra hnone
    have hlower : suzukiWeilIntervalGroundEnergy a + epsilon ∈
        lowerBounds (suzukiSmoothInteriorRayleighSet a) := by
      intro r hr
      exact le_of_not_gt fun hlt => hnone ⟨r, hr, hlt⟩
    have hle := hGLB.2 hlower
    linarith
  obtain ⟨r, ⟨u, huJ, rfl⟩, huray⟩ := hexists
  exact ⟨u, huJ, huray⟩

/-- Exact common-core upper control from the left: one compact smooth test at
`a` works unchanged throughout a whole smaller-aperture neighborhood. -/
theorem exists_left_aperture_uniform_groundEnergy_upper
    (a : SuzukiPositiveAperture) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ b : SuzukiPositiveAperture,
      b.1 < a.1 ∧
      ∀ c : SuzukiPositiveAperture, b.1 ≤ c.1 → c.1 ≤ a.1 →
        ccmRestrictedWeilGroundEnergy c <
          ccmRestrictedWeilGroundEnergy a + epsilon := by
  obtain ⟨u, huJ, huRayleigh⟩ :=
    exists_suzukiSmoothInteriorRayleigh_lt_groundEnergy_add a hepsilon
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy] at huRayleigh
  obtain ⟨b, hba, hsupport⟩ :=
    exists_strict_smaller_aperture_of_compact_tsupport a u
  refine ⟨b, hba, fun c hbc hca => ?_⟩
  have hsupportC : tsupport (u : ℝ → ℂ) ⊆ Ioo (-c.1) c.1 := by
    intro x hx
    have hxb := hsupport hx
    rw [mem_Ioo] at hxb ⊢
    constructor <;> linarith
  let uc := u.restrictAperture c hsupportC
  have hval : uc.toCCMFormVector.1 = u.toCCMFormVector.1 :=
    u.restrictAperture_toCCMFormVector_val c hsupportC
  have hnorm :
      ‖suzukiWeilIntervalFormEmbedding a u.toCCMFormVector‖ =
        ‖suzukiWeilIntervalFormEmbedding c uc.toCCMFormVector‖ := by
    rw [norm_suzukiWeilIntervalFormEmbedding_eq_physical,
      norm_suzukiWeilIntervalFormEmbedding_eq_physical]
    exact norm_ccmArchimedeanFormToAperture_eq_of_val_eq hval.symm
  have hsource : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic c uc.toCCMFormVector :=
    ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hca hval.symm
  have hRayleigh : suzukiWeilIntervalFormRayleigh c uc.toCCMFormVector =
      suzukiWeilIntervalFormRayleigh a u.toCCMFormVector := by
    unfold suzukiWeilIntervalFormRayleigh suzukiWeilIntervalFormMass
    rw [hsource, hnorm]
  have hucJ : suzukiWeilIntervalFormEmbedding c uc.toCCMFormVector ≠ 0 := by
    intro hzero
    apply huJ
    rw [← norm_eq_zero, hnorm, hzero, norm_zero]
  have hfloor := (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy c).1
    ⟨uc, hucJ, rfl⟩
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy,
    hRayleigh] at hfloor
  exact lt_of_le_of_lt hfloor huRayleigh

/-- A larger-aperture form vector whose physical representative is supported in a
smaller aperture canonically descends to that smaller form domain. -/
theorem exists_ccmArchimedeanFormDomain_of_limit_support
    (a b : SuzukiPositiveAperture)
    (w : CCMArchimedeanFormDomain b)
    (fstar : suzukiApertureHilbert b)
    (hwJ : ccmArchimedeanFormToAperture b w = fstar)
    (hsupport : indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1) (fstar : SoninL2) =
      (fstar : SoninL2)) :
    ∃ u : CCMArchimedeanFormDomain a,
      u.1 = w.1 ∧
      (ccmArchimedeanFormToAperture a u : SoninL2) = (fstar : SoninL2) := by
  have htime : ccmArchimedeanFourierToTime w.1 = (fstar : SoninL2) := by
    change (ccmArchimedeanFormToAperture b w : SoninL2) = (fstar : SoninL2)
    rw [hwJ]
  have hwker : w.1 ∈ (ccmArchimedeanSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime w.1) = 0
    rw [sub_apply, one_apply_eq_self, htime, hsupport, sub_self]
  refine ⟨⟨w.1, hwker⟩, rfl, ?_⟩
  exact htime

/-- Exact right-aperture continuity sequence.  Compactness prevents normalized
ground states from losing mass through the moving boundary. -/
theorem tendsto_ccmRestrictedWeilGroundEnergy_suzukiRightAperture
    (a : SuzukiPositiveAperture) :
    Tendsto
      (fun n => ccmRestrictedWeilGroundEnergy (suzukiRightAperture a n))
      atTop (nhds (ccmRestrictedWeilGroundEnergy a)) := by
  have henergyMono : Monotone
      (fun n => ccmRestrictedWeilGroundEnergy (suzukiRightAperture a n)) := by
    intro m n hmn
    exact ccmRestrictedWeilGroundEnergy_antitone
      (antitone_suzukiRightAperture a hmn)
  refine Metric.tendsto_atTop.2 fun epsilon hepsilon => ?_
  have hexists : ∃ k : ℕ,
      ccmRestrictedWeilGroundEnergy a - epsilon <
        ccmRestrictedWeilGroundEnergy (suzukiRightAperture a k) := by
    by_contra hnone
    push Not at hnone
    obtain ⟨fstar, phi, hphi, hconv, hsupport, hnorm⟩ :=
      exists_suzukiRightGroundCompactLimit a
    let b := suzukiRightAperture a 0
    have hmem : ∀ n : ℕ,
        ccmArchimedeanFormToAperture b
            (ccmRestrictedWeilNormalizedRightGroundExtension a (phi n)) ∈
          {f : suzukiApertureHilbert b |
            ∃ u : CCMArchimedeanFormDomain b,
              ccmArchimedeanFormToAperture b u = f ∧
                ccmRestrictedWeilSourceQuadratic b u ≤
                  ccmRestrictedWeilGroundEnergy a - epsilon} := by
      intro n
      refine ⟨ccmRestrictedWeilNormalizedRightGroundExtension a (phi n), rfl, ?_⟩
      rw [ccmRestrictedWeilNormalizedRightGroundExtension_source]
      exact hnone (phi n)
    obtain ⟨w, hwJ, hwQ⟩ :=
      (isClosed_ccmRestrictedWeilSource_sublevel b
        (ccmRestrictedWeilGroundEnergy a - epsilon)).mem_of_tendsto
          hconv (Eventually.of_forall hmem)
    obtain ⟨u, huw, huJ⟩ :=
      exists_ccmArchimedeanFormDomain_of_limit_support a b w fstar hwJ hsupport
    have hab : a.1 ≤ b.1 := by
      exact (suzukiRightAperture_gt a 0).le
    have hnormu : ‖ccmArchimedeanFormToAperture a u‖ = 1 := by
      have hnormeq := norm_ccmArchimedeanFormToAperture_eq_of_val_eq huw.symm
      rw [hwJ, hnorm] at hnormeq
      exact hnormeq.symm
    have hsource : ccmRestrictedWeilSourceQuadratic a u =
        ccmRestrictedWeilSourceQuadratic b w := by
      exact (ccmRestrictedWeilSourceQuadratic_eq_of_val_eq hab huw.symm).symm
    have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u
    rw [hnormu, one_pow, mul_one, hsource] at hfloor
    linarith
  obtain ⟨k, hk⟩ := hexists
  refine ⟨k, fun n hkn => ?_⟩
  have hlower := lt_of_lt_of_le hk (henergyMono hkn)
  have hupper : ccmRestrictedWeilGroundEnergy (suzukiRightAperture a n) ≤
      ccmRestrictedWeilGroundEnergy a :=
    ccmRestrictedWeilGroundEnergy_antitone
      (suzukiRightAperture_gt a n).le
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- Suzuki 2026, Theorem 1.3 for the exact CCM realization: the lowest
eigenvalue varies continuously with every positive aperture. -/
theorem continuousAt_ccmRestrictedWeilGroundEnergy
    (a : SuzukiPositiveAperture) :
    ContinuousAt ccmRestrictedWeilGroundEnergy a := by
  refine Metric.continuousAt_iff.2 fun epsilon hepsilon => ?_
  obtain ⟨b, hba, hleft⟩ :=
    exists_left_aperture_uniform_groundEnergy_upper a hepsilon
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_ccmRestrictedWeilGroundEnergy_suzukiRightAperture a)
    epsilon hepsilon
  let r := suzukiRightAperture a N
  have har : a.1 < r.1 := suzukiRightAperture_gt a N
  let delta := min (a.1 - b.1) (r.1 - a.1)
  have hdelta : 0 < delta := by
    exact lt_min (sub_pos.mpr hba) (sub_pos.mpr har)
  refine ⟨delta, hdelta, fun c hc => ?_⟩
  change dist c.1 a.1 < delta at hc
  rw [Real.dist_eq] at hc
  have hcLeft : b.1 < c.1 := by
    have hdist : |c.1 - a.1| < a.1 - b.1 :=
      lt_of_lt_of_le hc (min_le_left _ _)
    linarith [neg_le_abs (c.1 - a.1)]
  have hcRight : c.1 < r.1 := by
    have hdist : |c.1 - a.1| < r.1 - a.1 :=
      lt_of_lt_of_le hc (min_le_right _ _)
    linarith [le_abs_self (c.1 - a.1)]
  by_cases hca : c.1 ≤ a.1
  · have hlower : ccmRestrictedWeilGroundEnergy a ≤
        ccmRestrictedWeilGroundEnergy c :=
      ccmRestrictedWeilGroundEnergy_antitone hca
    have hupper := hleft c hcLeft.le hca
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  · have hac : a.1 ≤ c.1 := le_of_not_ge hca
    have hlower : ccmRestrictedWeilGroundEnergy r ≤
        ccmRestrictedWeilGroundEnergy c :=
      ccmRestrictedWeilGroundEnergy_antitone hcRight.le
    have hupper : ccmRestrictedWeilGroundEnergy c ≤
        ccmRestrictedWeilGroundEnergy a :=
      ccmRestrictedWeilGroundEnergy_antitone hac
    have hrclose := hN N le_rfl
    change dist (ccmRestrictedWeilGroundEnergy r)
      (ccmRestrictedWeilGroundEnergy a) < epsilon at hrclose
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr
      (ccmRestrictedWeilGroundEnergy_antitone har.le))] at hrclose
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith

theorem continuous_ccmRestrictedWeilGroundEnergy :
    Continuous ccmRestrictedWeilGroundEnergy :=
  continuous_iff_continuousAt.2 continuousAt_ccmRestrictedWeilGroundEnergy

/-- Suzuki 2026, Theorem 1.3 in the paper's literal interval-operator
notation: `a ↦ λₐ` is continuous on `(0,∞)`. -/
theorem continuous_suzukiWeilIntervalGroundEnergy :
    Continuous suzukiWeilIntervalGroundEnergy := by
  have hfun : suzukiWeilIntervalGroundEnergy =
      ccmRestrictedWeilGroundEnergy := by
    funext a
    exact suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy a
  rw [hfun]
  exact continuous_ccmRestrictedWeilGroundEnergy

end RHTower

end
