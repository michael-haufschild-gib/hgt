import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicPhysicalCharacteristicIncidence
import GaloisForLFunctions.HTGeometry.PeriodGaugeComplementarity
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Complete classification of period-gauge attainment

For an integral period source `L ≤ ℂ`, the following are equivalent: `L` is discrete, the
period-incidence multiplier has a continuous left inverse, and the global meromorphic fixed field
contains a nonconstant element. The constructive direction classifies the possible discrete period
ranks `0`, `1`, and `2`; it uses an exponential gauge in rank one and a rescaled theta-defect gauge
in rank two.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

open Bottcher

noncomputable section

set_option maxHeartbeats 600000

open scoped UnivMeroFieldInstances

def complexScale (a : ℂ) : ℂ → ℂ := fun z ↦ a * z

theorem analyticOnNhd_complexScale (a : ℂ) (U : Set ℂ) :
    AnalyticOnNhd ℂ (complexScale a) U :=
  analyticOnNhd_const.mul analyticOnNhd_id

theorem complexScale_comp_inv (a : ℂ) (ha : a ≠ 0) (U : Set ℂ) :
    Set.EqOn (complexScale a ∘ complexScale a⁻¹) id U := by
  intro z hz
  simp [complexScale, ha]

noncomputable def complexScaleAnalyticEquiv (a : ℂ) (ha : a ≠ 0) :
    analyticSubring (Set.univ : Set ℂ) ≃+* analyticSubring (Set.univ : Set ℂ) :=
  precompAnalyticEquiv
    (analyticOnNhd_complexScale a _)
    (analyticOnNhd_complexScale a⁻¹ _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (complexScale_comp_inv a ha _)
    (by
      intro z hz
      simp [complexScale, ha])

noncomputable def complexScaleMeroEquiv (a : ℂ) (ha : a ≠ 0) :
    meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
  precompMeroEquiv
    (analyticOnNhd_complexScale a _)
    (analyticOnNhd_complexScale a⁻¹ _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (complexScale_comp_inv a ha _)
    (by
      intro z hz
      simp [complexScale, ha])
    isOpen_univ isPreconnected_univ Set.univ_nonempty

@[simp] theorem univGermEval_complexScaleAnalyticEquiv
    (a : ℂ) (ha : a ≠ 0) (z : ℂ)
    (x : analyticSubring (Set.univ : Set ℂ)) :
    univGermEval z
        ((complexScaleAnalyticEquiv a ha x : analyticSubring Set.univ) :
          Germ (Filter.principal Set.univ) ℂ) =
      univGermEval (a * z) (x : Germ (Filter.principal Set.univ) ℂ) := by
  change univGermEval z
      ((precompAnalytic (analyticOnNhd_complexScale a _)
        (Set.mapsTo_univ _ _) x : analyticSubring Set.univ) :
          Germ (Filter.principal Set.univ) ℂ) = _
  rw [precompAnalytic_coe]
  induction x.1 using Quotient.inductionOn with
  | _ f => rfl

theorem complexScaleMeroEquiv_algebraMap
    (a : ℂ) (ha : a ≠ 0) (x : analyticSubring (Set.univ : Set ℂ)) :
    complexScaleMeroEquiv a ha
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) x) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (complexScaleAnalyticEquiv a ha x) := by
  exact precompMeroEquiv_algebraMap
    (analyticOnNhd_complexScale a _)
    (analyticOnNhd_complexScale a⁻¹ _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (complexScale_comp_inv a ha _)
    (by
      intro z hz
      simp [complexScale, ha])
    isOpen_univ isPreconnected_univ Set.univ_nonempty x

theorem addTranslationAnalyticEquiv_complexScaleAnalyticEquiv
    (a : ℂ) (ha : a ≠ 0) (q : ℂ)
    (x : analyticSubring (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv q (complexScaleAnalyticEquiv a ha x) =
      complexScaleAnalyticEquiv a ha (addTranslationAnalyticEquiv (a * q) x) := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  simp only [univGermEval_addTranslationAnalyticEquiv,
    univGermEval_complexScaleAnalyticEquiv]
  congr 1
  ring_nf

theorem addTranslationMeroEquiv_complexScaleMeroEquiv
    (a : ℂ) (ha : a ≠ 0) (q : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv q (complexScaleMeroEquiv a ha x) =
      complexScaleMeroEquiv a ha (addTranslationMeroEquiv (a * q) x) := by
  obtain ⟨u, v, hv, rfl⟩ :=
    IsFractionRing.div_surjective (analyticSubring Set.univ) x
  rw [map_div₀, map_div₀, map_div₀, map_div₀]
  simp only [complexScaleMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap,
    addTranslationAnalyticEquiv_complexScaleAnalyticEquiv]

theorem complexScaleMeroEquiv_const (a : ℂ) (ha : a ≠ 0) (c : ℂ) :
    complexScaleMeroEquiv a ha
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ c)) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) := by
  rw [complexScaleMeroEquiv_algebraMap]
  congr 1

private theorem thetaHalf_nonlatticeShift (tau : ℂ) (htau : 0 < tau.im) :
    ThetaNonlatticeShift tau (1 / 2) := by
  rintro ⟨m, n, hmn⟩
  have him := congrArg Complex.im hmn
  have hhalfim : ((1 / 2 : ℂ).im) = 0 := by norm_num
  rw [hhalfim] at him
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im,
    Complex.intCast_re, zero_mul, zero_add] at him
  have hn : n = 0 := by
    by_contra hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have him' : (n : ℝ) * tau.im = 0 := by simpa using him.symm
    exact hn' (mul_eq_zero.mp him' |>.resolve_right (ne_of_gt htau))
  subst n
  have hre := congrArg Complex.re hmn
  have hm : (2 * m : ℤ) = 1 := by
    exact_mod_cast (show (2 : ℝ) * (m : ℝ) = 1 by norm_num at hre ⊢; linarith)
  omega

private theorem cyclicPhysicalExponentialMero_ne_const
    (omega : ℂ) (homega : omega ≠ 0) (c : ℂ) :
    physicalExponentialMero (2 * Real.pi * Complex.I / omega) ≠
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) := by
  intro heq
  have heqA :
      physicalExponentialAnalytic (2 * Real.pi * Complex.I / omega) =
        constToAnalytic Set.univ c := by
    apply IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)
    simpa [physicalExponentialMero] using heq
  have hzero := congrArg
    (fun a : analyticSubring (Set.univ : Set ℂ) ↦
      univGermEval 0 (a : Germ (Filter.principal Set.univ) ℂ)) heqA
  have hc : c = 1 := by simpa [constToAnalytic] using hzero.symm
  have hhalf := congrArg
    (fun a : analyticSubring (Set.univ : Set ℂ) ↦
      univGermEval (omega / 2) (a : Germ (Filter.principal Set.univ) ℂ)) heqA
  rw [hc] at hhalf
  simp only [univGermEval_physicalExponentialAnalytic] at hhalf
  have harg : (2 * Real.pi * Complex.I / omega) * (omega / 2) =
      Real.pi * Complex.I := by field_simp
  rw [harg, Complex.exp_pi_mul_I] at hhalf
  norm_num [constToAnalytic] at hhalf

/-- Every nonzero cyclic period source carries a nonconstant exponential fixed gauge. -/
theorem exists_nonconstant_fixed_cyclicPeriod
    (omega : ℂ) (homega : omega ≠ 0) :
    ∃ z : meroField (Set.univ : Set ℂ),
      (∀ q ∈ Submodule.span ℤ ({omega} : Set ℂ),
        addTranslationMeroEquiv q z = z) ∧
      ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  let lambda := 2 * Real.pi * Complex.I / omega
  let z := physicalExponentialMero lambda
  refine ⟨z, ?_, ?_⟩
  · intro q hq
    have homegaFix : addTranslationMeroEquiv omega z = z := by
      change addTranslationMeroEquiv omega (physicalExponentialMero lambda) =
        physicalExponentialMero lambda
      rw [addTranslationMeroEquiv_physicalExponentialMero]
      have harg : lambda * omega = 2 * Real.pi * Complex.I := by
        dsimp [lambda]
        field_simp
      rw [harg, Complex.exp_two_pi_mul_I]
      simp
    have hgen : ({omega} : Set ℂ) ⊆ meromorphicTranslationStabilizer z := by
      simpa using homegaFix
    have hspan : Submodule.span ℤ ({omega} : Set ℂ) ≤
        (meromorphicTranslationStabilizer z).toIntSubmodule :=
      Submodule.span_le.mpr hgen
    exact hspan hq
  · rintro ⟨c, hc⟩
    exact cyclicPhysicalExponentialMero_ne_const omega homega c hc.symm

/-- A full theta period lattice carries a nonconstant global meromorphic fixed gauge. -/
theorem exists_nonconstant_fixed_thetaPeriodLattice
    (tau : ℂ) (htau : 0 < tau.im) :
    ∃ z : meroField (Set.univ : Set ℂ),
      (∀ q ∈ Submodule.span ℤ ({1, tau} : Set ℂ),
        addTranslationMeroEquiv q z = z) ∧
      ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  let z := thetaLogDerivDefectMero (1 / 2) tau htau
  refine ⟨z, ?_, ?_⟩
  · intro q hq
    have hgen : ({1, tau} : Set ℂ) ⊆ meromorphicTranslationStabilizer z := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp
      · subst p
        exact addTranslationMeroEquiv_thetaLogDerivDefect_one (1 / 2) tau htau
      · subst p
        exact addTranslationMeroEquiv_thetaLogDerivDefect_tau (1 / 2) tau htau
    have hspan : Submodule.span ℤ ({1, tau} : Set ℂ) ≤
        (meromorphicTranslationStabilizer z).toIntSubmodule :=
      Submodule.span_le.mpr hgen
    exact hspan hq
  · rintro ⟨c, hc⟩
    exact thetaLogDerivDefectMero_ne_const_of_nonlattice htau
      (thetaHalf_nonlatticeShift tau htau) c hc.symm

/-- Rescaling transports the normalized theta gauge to every oriented rank-two period pair. -/
theorem exists_nonconstant_fixed_orientedRankTwoPeriod
    (omegaOne omegaTwo : ℂ) (homegaOne : omegaOne ≠ 0)
    (horient : 0 < (omegaTwo / omegaOne).im) :
    ∃ z : meroField (Set.univ : Set ℂ),
      (∀ q ∈ Submodule.span ℤ ({omegaOne, omegaTwo} : Set ℂ),
        addTranslationMeroEquiv q z = z) ∧
      ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  let tau := omegaTwo / omegaOne
  let a := omegaOne⁻¹
  have ha : a ≠ 0 := inv_ne_zero homegaOne
  obtain ⟨z0, hfix0, hnonconstant0⟩ :=
    exists_nonconstant_fixed_thetaPeriodLattice tau (by simpa [tau] using horient)
  let z := complexScaleMeroEquiv a ha z0
  refine ⟨z, ?_, ?_⟩
  · intro q hq
    have hscaled : a * q ∈ Submodule.span ℤ ({1, tau} : Set ℂ) := by
      induction hq using Submodule.span_induction with
      | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with hx | hx
          · subst x
            have : a * omegaOne = 1 := by simp [a, homegaOne]
            rw [this]
            exact Submodule.subset_span (by simp)
          · subst x
            have : a * omegaTwo = tau := by
              dsimp [a, tau]
              field_simp
            rw [this]
            exact Submodule.subset_span (by simp)
      | zero => simp
      | add x y hx hy hxm hym =>
          simpa [mul_add] using Submodule.add_mem _ hxm hym
      | smul n x hx hxm =>
          convert Submodule.smul_mem
            (Submodule.span ℤ ({1, tau} : Set ℂ)) n hxm using 1
          ring
    change addTranslationMeroEquiv q (complexScaleMeroEquiv a ha z0) =
      complexScaleMeroEquiv a ha z0
    rw [addTranslationMeroEquiv_complexScaleMeroEquiv,
      hfix0 (a * q) hscaled]
  · rintro ⟨c, hc⟩
    apply hnonconstant0
    refine ⟨c, ?_⟩
    apply (complexScaleMeroEquiv a ha).injective
    rw [complexScaleMeroEquiv_const]
    exact hc

private theorem div_im_ne_zero_of_linearIndependent
    (omegaOne omegaTwo : ℂ)
    (hlin : LinearIndependent ℝ ![omegaOne, omegaTwo]) :
    (omegaTwo / omegaOne).im ≠ 0 := by
  have homegaOne : omegaOne ≠ 0 := by
    simpa using hlin.ne_zero (0 : Fin 2)
  intro him
  have hreal : (omegaTwo / omegaOne) = ((omegaTwo / omegaOne).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hnot := (LinearIndependent.pair_iff' homegaOne).mp hlin
    (omegaTwo / omegaOne).re
  apply hnot
  change ((omegaTwo / omegaOne).re : ℂ) * omegaOne = omegaTwo
  rw [← hreal]
  field_simp

private theorem span_pair_neg_right (omegaOne omegaTwo : ℂ) :
    Submodule.span ℤ ({omegaOne, -omegaTwo} : Set ℂ) =
      Submodule.span ℤ ({omegaOne, omegaTwo} : Set ℂ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact Submodule.subset_span (by simp)
    · subst x
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact Submodule.subset_span (by simp)
    · subst x
      have hneg : -omegaTwo ∈
          Submodule.span ℤ ({omegaOne, -omegaTwo} : Set ℂ) :=
        Submodule.subset_span (by simp)
      simpa using Submodule.neg_mem _ hneg

private theorem span_range_coe_basis_eq
    {ι : Type*} (L : Submodule ℤ ℂ) (b : Module.Basis ι ℤ L) :
    Submodule.span ℤ (Set.range (fun i ↦ ((b i : L) : ℂ))) = L := by
  change Submodule.span ℤ (Set.range (L.subtype ∘ b)) = L
  rw [Set.range_comp, Submodule.span_image, b.span_eq,
    Submodule.map_subtype_top]

private theorem range_fin_one_eq_singleton (v : Fin 1 → ℂ) :
    Set.range v = ({v 0} : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    simp
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩

private theorem range_fin_two_eq_pair (v : Fin 2 → ℂ) :
    Set.range v = ({v 0, v 1} : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩

/-- Every real-linearly independent rank-two period pair carries a nonconstant fixed gauge,
independently of orientation. -/
theorem exists_nonconstant_fixed_rankTwoPeriod
    (omegaOne omegaTwo : ℂ)
    (hlin : LinearIndependent ℝ ![omegaOne, omegaTwo]) :
    ∃ z : meroField (Set.univ : Set ℂ),
      (∀ q ∈ Submodule.span ℤ ({omegaOne, omegaTwo} : Set ℂ),
        addTranslationMeroEquiv q z = z) ∧
      ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  have homegaOne : omegaOne ≠ 0 := by
    simpa using hlin.ne_zero (0 : Fin 2)
  have himne := div_im_ne_zero_of_linearIndependent omegaOne omegaTwo hlin
  rcases lt_or_gt_of_ne himne with hneg | hpos
  · have horientNeg : 0 < ((-omegaTwo) / omegaOne).im := by
      rw [neg_div]
      simpa using neg_pos.mpr hneg
    obtain ⟨z, hfix, hnonconstant⟩ :=
      exists_nonconstant_fixed_orientedRankTwoPeriod
        omegaOne (-omegaTwo) homegaOne horientNeg
    refine ⟨z, ?_, hnonconstant⟩
    intro q hq
    apply hfix q
    rw [span_pair_neg_right]
    exact hq
  · exact exists_nonconstant_fixed_orientedRankTwoPeriod
      omegaOne omegaTwo homegaOne hpos

/-- Every discrete integral period source in the complex plane carries a nonconstant global
meromorphic fixed gauge. -/
theorem exists_nonconstant_fixed_of_discretePeriodSource
    (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    ∃ z : meroField (Set.univ : Set ℂ),
      (∀ q ∈ L, addTranslationMeroEquiv q z = z) ∧
      ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  have hspanL : Submodule.span ℤ (L : Set ℂ) = L := Submodule.span_eq L
  have hdiscreteSpan : DiscreteTopology (Submodule.span ℤ (L : Set ℂ)) := by
    rw [hspanL]
    infer_instance
  have hrankEq :=
    Real.finrank_eq_int_finrank_of_discrete (s := (L : Set ℂ)) hdiscreteSpan
  have hrankRealLe : Set.finrank ℝ (L : Set ℂ) ≤ 2 := by
    calc
      Set.finrank ℝ (L : Set ℂ) ≤ Module.finrank ℝ ℂ := Submodule.finrank_le _
      _ = 2 := Complex.finrank_real_complex
  have hrankLe : Module.finrank ℤ L ≤ 2 := by
    calc
      Module.finrank ℤ L = Set.finrank ℤ (L : Set ℂ) := by
        change Module.finrank ℤ L =
          Module.finrank ℤ (Submodule.span ℤ (L : Set ℂ))
        rw [hspanL]
      _ = Set.finrank ℝ (L : Set ℂ) := hrankEq.symm
      _ ≤ 2 := hrankRealLe
  have hrankCases : Module.finrank ℤ L = 0 ∨
      Module.finrank ℤ L = 1 ∨ Module.finrank ℤ L = 2 := by
    omega
  rcases hrankCases with hrankZero | hrankOne | hrankTwo
  · letI : Subsingleton L :=
      (Module.finrank_eq_zero_iff_of_free ℤ L).mp hrankZero
    have hzero : ∀ x : L, x = 0 := fun x ↦ Subsingleton.elim x 0
    have hLbot : L = ⊥ := by
      apply le_antisymm
      · intro x hx
        have hxzero := congrArg Subtype.val (hzero ⟨x, hx⟩)
        simpa using hxzero
      · exact bot_le
    obtain ⟨z, _hfix, hnonconstant⟩ :=
      exists_nonconstant_fixed_cyclicPeriod 1 one_ne_zero
    refine ⟨z, ?_, hnonconstant⟩
    intro q hq
    rw [hLbot] at hq
    have hqzero : q = 0 := by simpa using hq
    subst q
    exact addTranslationMeroEquiv_zero_apply z
  · let b : Module.Basis (Fin 1) ℤ L := Module.finBasisOfFinrankEq ℤ L hrankOne
    let v : Fin 1 → ℂ := fun i ↦ ((b i : L) : ℂ)
    let omega := v 0
    have homega : omega ≠ 0 := by
      intro homegaZero
      apply b.ne_zero 0
      exact Subtype.ext homegaZero
    have hspanBasis : Submodule.span ℤ (Set.range v) = L :=
      span_range_coe_basis_eq L b
    have hcyclic : Submodule.span ℤ ({omega} : Set ℂ) = L := by
      rw [← range_fin_one_eq_singleton v]
      exact hspanBasis
    obtain ⟨z, hfix, hnonconstant⟩ :=
      exists_nonconstant_fixed_cyclicPeriod omega homega
    refine ⟨z, ?_, hnonconstant⟩
    intro q hq
    apply hfix q
    rw [hcyclic]
    exact hq
  · let b : Module.Basis (Fin 2) ℤ L := Module.finBasisOfFinrankEq ℤ L hrankTwo
    let v : Fin 2 → ℂ := fun i ↦ ((b i : L) : ℂ)
    have hspanBasis : Submodule.span ℤ (Set.range v) = L :=
      span_range_coe_basis_eq L b
    have hdiscreteBasisSpan : DiscreteTopology
        (Submodule.span ℤ (Set.range v)) := by
      rw [hspanBasis]
      infer_instance
    have hrankBasisEq :=
      Real.finrank_eq_int_finrank_of_discrete
        (s := Set.range v) hdiscreteBasisSpan
    have hlin : LinearIndependent ℝ v := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      simp only [Fintype.card_fin]
      rw [hrankBasisEq]
      change 2 = Module.finrank ℤ (Submodule.span ℤ (Set.range v))
      rw [hspanBasis, hrankTwo]
    have hpair : Submodule.span ℤ ({v 0, v 1} : Set ℂ) = L := by
      rw [← range_fin_two_eq_pair v]
      exact hspanBasis
    obtain ⟨z, hfix, hnonconstant⟩ :=
      exists_nonconstant_fixed_rankTwoPeriod (v 0) (v 1) (by
        have hv : ![v 0, v 1] = v := by
          funext i
          fin_cases i <;> rfl
        rw [hv]
        exact hlin)
    refine ⟨z, ?_, hnonconstant⟩
    intro q hq
    apply hfix q
    rw [hpair]
    exact hq

/-- Exact gauge classification: a complex integral period source admits a nonconstant global
meromorphic fixed gauge exactly when it is discrete. -/
theorem exists_nonconstant_fixed_iff_discretePeriodSource
    (L : Submodule ℤ ℂ) :
    (∃ z : meroField (Set.univ : Set ℂ),
      (∀ q ∈ L, addTranslationMeroEquiv q z = z) ∧
      ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z) ↔
      DiscreteTopology L := by
  constructor
  · rintro ⟨z, hfix, hnonconstant⟩
    exact (periodIncidenceMultiplier_hasLeftInverse_iff_discrete L).mp
      (periodIncidenceMultiplier_hasLeftInverse_of_nonconstant_fixed
        L z hfix hnonconstant)
  · intro hdiscrete
    letI : DiscreteTopology L := hdiscrete
    exact exists_nonconstant_fixed_of_discretePeriodSource L

/-- **Complete gauge--attainment complementarity.** A period-incidence representation has a
continuous left inverse exactly when its source-fixed global meromorphic field contains a
nonconstant element. -/
theorem periodIncidenceMultiplier_hasLeftInverse_iff_exists_nonconstant_fixed
    (L : Submodule ℤ ℂ) :
    (periodIncidenceMultiplier L).HasLeftInverse ↔
      ∃ z : meroField (Set.univ : Set ℂ),
        (∀ q ∈ L, addTranslationMeroEquiv q z = z) ∧
        ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ c) = z := by
  rw [periodIncidenceMultiplier_hasLeftInverse_iff_discrete,
    exists_nonconstant_fixed_iff_discretePeriodSource]

/-- Failure of incidence effectivity is equivalent to maximal fixed-gauge rigidity. -/
theorem periodIncidenceMultiplier_not_hasLeftInverse_iff_all_fixed_constant
    (L : Submodule ℤ ℂ) :
    ¬ (periodIncidenceMultiplier L).HasLeftInverse ↔
      ∀ z : meroField (Set.univ : Set ℂ),
        (∀ q ∈ L, addTranslationMeroEquiv q z = z) →
          ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
            (constToAnalytic Set.univ c) = z := by
  constructor
  · intro hno z hfix
    exact exists_constant_of_periodIncidenceMultiplier_not_hasLeftInverse L hno z hfix
  · intro hrigid hleft
    obtain ⟨z, hfix, hnonconstant⟩ :=
      (periodIncidenceMultiplier_hasLeftInverse_iff_exists_nonconstant_fixed L).mp hleft
    exact hnonconstant (hrigid z hfix)

/-- **Bare-source reconstruction uncertainty.** Uniform source effectivity and fixed-gauge
rigidity modulo constants cannot coexist for any integral translation source in the complex
plane. -/
theorem not_periodIncidenceMultiplier_hasLeftInverse_and_all_fixed_constant
    (L : Submodule ℤ ℂ) :
    ¬ ((periodIncidenceMultiplier L).HasLeftInverse ∧
      ∀ z : meroField (Set.univ : Set ℂ),
        (∀ q ∈ L, addTranslationMeroEquiv q z = z) →
          ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
            (constToAnalytic Set.univ c) = z) := by
  rintro ⟨hleft, hrigid⟩
  exact (periodIncidenceMultiplier_not_hasLeftInverse_iff_all_fixed_constant L).mpr
    hrigid hleft

/-- Every period source lies in exactly one obstruction phase: either incidence is effective and a
nonconstant gauge survives, or incidence is ineffective and all fixed gauges are constant. -/
theorem periodSource_effectivity_gaugeRigidity_dichotomy
    (L : Submodule ℤ ℂ) :
    ((periodIncidenceMultiplier L).HasLeftInverse ∧
      ∃ z : meroField (Set.univ : Set ℂ),
        (∀ q ∈ L, addTranslationMeroEquiv q z = z) ∧
        ¬ ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ c) = z) ∨
    (¬ (periodIncidenceMultiplier L).HasLeftInverse ∧
      ∀ z : meroField (Set.univ : Set ℂ),
        (∀ q ∈ L, addTranslationMeroEquiv q z = z) →
          ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
            (constToAnalytic Set.univ c) = z) := by
  by_cases hleft : (periodIncidenceMultiplier L).HasLeftInverse
  · exact Or.inl ⟨hleft,
      (periodIncidenceMultiplier_hasLeftInverse_iff_exists_nonconstant_fixed L).mp hleft⟩
  · exact Or.inr ⟨hleft,
      (periodIncidenceMultiplier_not_hasLeftInverse_iff_all_fixed_constant L).mp hleft⟩

end

end GaloisForLFunctions
