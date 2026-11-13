/-
Integral cover correspondences adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.RationalSourceResidues

/-!
# Integral cover correspondences

Lower cusp matrices, the integral cover cosets `IntegralCoverCosets` and their intertwiners.
Moving cutoffs leave the residual vector unchanged, adjoint orthogonality forces finite
correspondence combinations of the source residue to vanish, and Dirichlet pairs pull back
to the cover.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff

/-- The mass sandwich of the orthogonal nullspace projection is symmetric. -/
lemma kernelThetaMassProjection_symmetric (F D : KernelQuotientL2) :
    inner ℂ F (kernelThetaMassProjection D) = inner ℂ (kernelThetaMassProjection F) D :=
  hilbertProjectionSandwich_symmetric kernelEnergyMass kernelThetaNull F D

lemma kernelThetaMassProjection_eigenvector (F : KernelQuotientL2)
    (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph) :
    kernelThetaMassProjection F = (9 / 17 : ℂ) • F := by
  let u : kernelEnergyLaplacian.domain := ⟨F, LinearPMap.mem_domain_of_mem_graph hF⟩
  have hu : kernelEnergyLaplacian u = (8 / 9 : ℂ) • F :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph u) hF rfl
  let E : KernelEnergyGraph := kernelVariationalSolution (kernelEnergyLaplacian u + u)
  have hE : E ∈ kernelThetaNull := by
    change kernelSpectralFormOperator (8 / 9 : ℂ) E = 0
    dsimp only [E]
    rw [kernelSpectralFormOperator_of_domain, hu]
    change kernelVariationalSolution ((8 / 9 : ℂ) • F - (8 / 9 : ℂ) • F) = 0
    rw [sub_self, map_zero]
  have hmass : kernelEnergyMass E = F := kernelEnergyLaplacian_resolvent_relation u
  have hscale : kernelEnergyMass.adjoint F = (9 / 17 : ℂ) • E := by
    dsimp only [E]
    rw [hu]
    change kernelVariationalSolution F = (9 / 17 : ℂ) • kernelVariationalSolution ((8 / 9 : ℂ) • F + F)
    rw [map_add, map_smul, smul_add, smul_smul]
    module
  change kernelEnergyMass (kernelThetaNull.starProjection (kernelEnergyMass.adjoint F)) = _
  rw [hscale, map_smul, kernelThetaNull.starProjection_eq_self_iff.mpr hE, map_smul, hmass]

theorem kernelEisensteinResidueVector_pairing (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab) =
      (3 / 2 : ℂ) * inner ℂ F (kernelL2Defect a b ha hab (4 / 3)) := by
  rw [kernelEisensteinResidueVector, inner_smul_right, kernelThetaMassProjection_symmetric,
    kernelThetaMassProjection_eigenvector F hF, inner_smul_left]
  simp only [map_div₀, map_ofNat]
  ring

lemma kernelLocalCorrectedSeed_initial_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1 < a) (hab : a < b) (hc : 1 < c) (hcd : c < d)
    (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    kernelLocalCorrectedSeed S hS a b (by linarith) hab s =
      kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  apply Lp.ext
  filter_upwards [kernelLocalCorrectedSeed_ae_eq S hS a b (by linarith) hab s,
    kernelLocalCorrectedSeed_ae_eq S hS c d (by linarith) hcd s,
    kernelEisensteinL2Correction_initial_overlap a b ha hab s hs hi,
    kernelEisensteinL2Correction_initial_overlap c d hc hcd s hs hi] with q h1 h2 h3 h4
  rw [h1, h2]
  by_cases hq : q ∈ S
  · simp only [Set.indicator_of_mem hq, kernelCorrectedSeed, h3, h4]
    ring
  · simp only [Set.indicator_of_notMem hq]

lemma kernelLocalCorrectedSeed_cutoff_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1 < a) (hab : a < b) (hc : 1 < c) (hcd : c < d) :
    Set.EqOn (kernelLocalCorrectedSeed S hS a b (by linarith) hab)
      (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) cuspUpperParameterRegion := by
  have h1 : AnalyticOnNhd ℂ (kernelLocalCorrectedSeed S hS a b (by linarith) hab) cuspUpperParameterRegion :=
    fun s hs => kernelLocalCorrectedSeed_analyticAt_nonreal S hS a b (by linarith) hab s
      (by linarith [hs.1]) hs.2.ne'
  have h2 : AnalyticOnNhd ℂ (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) cuspUpperParameterRegion :=
    fun s hs => kernelLocalCorrectedSeed_analyticAt_nonreal S hS c d (by linarith) hcd s
      (by linarith [hs.1]) hs.2.ne'
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)
  apply h1.eqOn_of_preconnected_of_eventuallyEq h2 cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion] : (5 + Complex.I : ℂ) ∈ cuspUpperParameterRegion)
  filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
  exact kernelLocalCorrectedSeed_initial_eq S hS a b c d ha hab hc hcd s hs.1 hs.2

lemma kernelEisensteinResidueVector_restrict_cutoff_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1 < a) (hab : a < b) (hc : 1 < c) (hcd : c < d) :
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinResidueVector a b (by linarith) hab) =
      kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinResidueVector c d (by linarith) hcd) := by
  have h1 := (kernelLocalCorrectedSeed_residue_limit S hS a b (by linarith) hab).comp
    thetaApproach_tendsto_complex_punctured
  have h2 := (kernelLocalCorrectedSeed_residue_limit S hS c d (by linarith) hcd).comp
    thetaApproach_tendsto_complex_punctured
  apply tendsto_nhds_unique_of_eventuallyEq h1 h2
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hs : (4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I ∈ cuspUpperParameterRegion := by
    constructor
    · norm_num
      linarith
    · simpa using ht
  exact congrArg (fun u : KernelQuotientL2 =>
    ((4 / 3 : ℂ) + (t : ℂ) + (t : ℂ) * Complex.I - 4 / 3) • u)
    (kernelLocalCorrectedSeed_cutoff_eq S hS a b c d ha hab hc hcd hs)

lemma kernelL2_eq_of_compact_restrictions (F G : KernelQuotientL2)
    (h : ∀ S : Set KernelQuotient, ∀ hS : IsCompact S,
      kernelMassRestrictionCLM S hS.measurableSet F = kernelMassRestrictionCLM S hS.measurableSet G) : F = G := by
  let S : ℕ → Set KernelQuotient := fun n => {q | kernelQuotientBarrier 2 3 q ≤ n}
  have hS (n : ℕ) : IsCompact (S n) := kernelBarrier_sublevel_isCompact n
  have he (n : ℕ) : ∀ᵐ q ∂integralQuotientVolume globalKubotaKernel, q ∈ S n → F q = G q := by
    have hi := h (S n) (hS n)
    filter_upwards [kernelMassRestriction_coe (S n) (hS n).measurableSet F,
      kernelMassRestriction_coe (S n) (hS n).measurableSet G] with q hf hg hq
    rw [Set.indicator_of_mem hq] at hf hg
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet F q = F q at hf
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet G q = G q at hg
    rw [hi] at hf
    exact hf.symm.trans hg
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with q hq
  obtain ⟨n, hn⟩ := exists_nat_ge (kernelQuotientBarrier 2 3 q)
  exact hq n hn

/-- Moving the incoming cutoff does not change the actual residual vector. -/
theorem kernelEisensteinResidueVector_cutoff_independent
    (a b c d : ℝ) (ha : 1 < a) (hab : a < b) (hc : 1 < c) (hcd : c < d) :
    kernelEisensteinResidueVector a b (by linarith) hab = kernelEisensteinResidueVector c d (by linarith) hcd :=
  kernelL2_eq_of_compact_restrictions _ _ (fun S hS =>
    kernelEisensteinResidueVector_restrict_cutoff_eq S hS a b c d ha hab hc hcd)

lemma cuspTransition_dilate (A : ℝ) (hA : A ≠ 0) :
    cuspTransition A (2 * A) = fun v => cuspTransition 1 2 (v / A) := by
  funext v
  unfold cuspTransition
  congr 1
  field_simp

lemma cuspTransition_dilate_deriv (A v : ℝ) (hA : A ≠ 0) :
    deriv (cuspTransition A (2 * A)) v = deriv (cuspTransition 1 2) (v / A) / A := by
  rw [cuspTransition_dilate A hA]
  have hd := (((cuspTransition_contDiff 1 2).differentiable (by simp) (v / A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)
  simpa only [Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using hd.deriv

lemma cuspTransition_dilate_second (A v : ℝ) (hA : A ≠ 0) :
    deriv (deriv (cuspTransition A (2 * A))) v = deriv (deriv (cuspTransition 1 2)) (v / A) / A ^ 2 := by
  have he : deriv (cuspTransition A (2 * A)) = fun x => deriv (cuspTransition 1 2) (x / A) / A :=
    funext (fun x => cuspTransition_dilate_deriv A x hA)
  rw [he]
  have hc := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have hd := (((hc.differentiable (by simp) (v / A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)).div_const A
  simp only [Function.comp_def, id_eq] at hd
  convert hd.deriv using 1
  field_simp

def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 * (deriv (deriv (cuspTransition 1 2)) x : ℝ) +
    (2 * s - 1) * (x : ℂ) * (deriv (cuspTransition 1 2) x : ℝ)

lemma cuspBaseDefectFactor_continuous (s : ℂ) : Continuous (cuspBaseDefectFactor s) := by
  have h1 := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  exact ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_ofReal.comp h2.continuous)).add
    ((continuous_const.mul Complex.continuous_ofReal).mul (Complex.continuous_ofReal.comp h1.continuous))

lemma cuspBaseDefectFactor_compact (s : ℂ) : HasCompactSupport (cuspBaseDefectFactor s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
  intro x hx
  by_contra hn
  have hout : x < 1 ∨ 2 < x := by simpa only [Set.mem_Icc, not_and_or, not_le] using hn
  obtain ⟨h1, h2⟩ := cuspTransition_derivatives 1 2 x (by norm_num) hout
  exact hx (by simp only [cuspBaseDefectFactor, h1, h2, Complex.ofReal_zero, mul_zero, add_zero])

lemma cuspSeedDefectProfile_dilate (A v : ℝ) (hA : A ≠ 0) (s : ℂ) :
    cuspSeedDefectProfile A (2 * A) s v = positiveHeightPower s v * cuspBaseDefectFactor s (v / A) := by
  rw [cuspSeedDefectProfile, cuspTransition_dilate_deriv A v hA, cuspTransition_dilate_second A v hA]
  unfold cuspBaseDefectFactor
  push_cast
  field_simp

/-- Dilating the transition interval gives a quadratic uniform bound on its defect. -/
theorem cuspSeedDefectProfile_dilate_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 1 ≤ A → ∀ v : ℝ,
      ‖cuspSeedDefectProfile A (2 * A) (4 / 3) v‖ ≤ C * A ^ 2 := by
  obtain ⟨B, hB⟩ := (cuspBaseDefectFactor_compact (4 / 3)).exists_bound_of_continuous
    (cuspBaseDefectFactor_continuous (4 / 3))
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : ℝ) : ‖cuspBaseDefectFactor (4 / 3) x‖ ≤ C := (hB x).trans (le_max_left _ _)
  refine ⟨4 * C, by positivity, fun A hA v => ?_⟩
  have hApos : 0 < A := zero_lt_one.trans_le hA
  by_cases hv : v ∈ Set.Icc A (2 * A)
  · have hv1 : 1 ≤ v := hA.trans hv.1
    have hvpos : 0 < v := hApos.trans_le hv.1
    have hp : ‖positiveHeightPower (4 / 3) v‖ ≤ v ^ 2 := by
      rw [positiveHeightPower_eq_cpow _ _ hvpos, Complex.norm_cpow_eq_rpow_re_of_pos hvpos]
      norm_num
      simpa using Real.rpow_le_rpow_of_exponent_le hv1 (show (4 / 3 : ℝ) ≤ 2 by norm_num)
    rw [cuspSeedDefectProfile_dilate A v hApos.ne', norm_mul]
    calc
      _ ≤ v ^ 2 * C := mul_le_mul hp (hbound (v / A)) (norm_nonneg _) (sq_nonneg v)
      _ ≤ (2 * A) ^ 2 * C := mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ hvpos.le (by positivity)).mpr hv.2) hC
      _ = (4 * C) * A ^ 2 := by ring
  · have hout : v < A ∨ 2 * A < v := by simpa only [Set.mem_Icc, not_and_or, not_le] using hv
    rw [cuspSeedDefectProfile_zero A (2 * A) (4 / 3) v (by linarith) hout, norm_zero]
    positivity

theorem smoothCuspSeedDefect_dilate_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 1 ≤ A → ∀ w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2 * A) (4 / 3) w‖ ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := cuspSeedDefectProfile_dilate_bound
  exact ⟨C, hC, fun A hA w => cuspCutoffCorrection_norm_le _ _ (by positivity) (hbound A hA) w⟩

lemma movingDefect_product_bound (f : KernelQuotient → ℂ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hdec : ∀ w : HyperbolicSpace, ∀ r : CuspCosets, 1 < cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖ ≤ K / (cosetHeight r w) ^ 3)
    (hbound : ∀ A : ℝ, 1 ≤ A → ∀ w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2 * A) (4 / 3) w‖ ≤ C * A ^ 2)
    (A : ℝ) (hA : 1 < A) (q : KernelQuotient) :
    ‖f q‖ * ‖kernelQuotientDefect A (2 * A) (4 / 3) q‖ ≤ K * C / A := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change ‖f (integralOrbitProjection globalKubotaKernel w)‖ *
      ‖smoothCuspSeedDefect A (2 * A) (4 / 3) w‖ ≤ _
    have hApos : 0 < A := zero_lt_one.trans hA
    by_cases hz : smoothCuspSeedDefect A (2 * A) (4 / 3) w = 0
    · rw [hz, norm_zero, mul_zero]
      positivity
    obtain ⟨r, hr, _⟩ := smoothCuspSeedDefect_support A (2 * A) (4 / 3) (by linarith) w hz
    have hf : ‖f (integralOrbitProjection globalKubotaKernel w)‖ ≤ K / A ^ 3 :=
      (hdec w r (hA.trans_le hr)).trans (div_le_div_of_nonneg_left hK (pow_pos hApos 3)
        (pow_le_pow_left₀ hApos.le hr 3))
    calc
      _ ≤ (K / A ^ 3) * (C * A ^ 2) := mul_le_mul hf (hbound A hA.le w) (norm_nonneg _) (by positivity)
      _ = K * C / A := by field_simp

lemma movingDefect_inner_bound (F : KernelQuotientL2) (f : KernelQuotient → ℂ)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hdec : ∀ w : HyperbolicSpace, ∀ r : CuspCosets, 1 < cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖ ≤ K / (cosetHeight r w) ^ 3)
    (hbound : ∀ A : ℝ, 1 ≤ A → ∀ w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2 * A) (4 / 3) w‖ ≤ C * A ^ 2)
    (A : ℝ) (hA : 1 < A) :
    ‖inner ℂ F (kernelL2Defect A (2 * A) (by linarith) (by linarith) (4 / 3))‖ ≤
      (K * C / A) * (integralQuotientVolume globalKubotaKernel).real Set.univ := by
  rw [L2.inner_def]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hrep, kernelL2Defect_ae_eq A (2 * A) (by linarith) (by linarith) (4 / 3)] with q hf hd
  rw [hf, hd, RCLike.inner_apply, norm_mul]
  simpa only [starRingEnd_apply, norm_star, mul_comm] using
    movingDefect_product_bound f K C hK hC hdec hbound A hA q

/-- A moving cutoff makes the residual pairing of a rapidly decaying eigenvector tend to zero. -/
theorem cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hdec : ∀ w : HyperbolicSpace, ∀ r : CuspCosets, 1 < cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖ ≤ K / (cosetHeight r w) ^ 3) :
    inner ℂ F cubicEisensteinResidue = 0 := by
  obtain ⟨C, hC, hbound⟩ := smoothCuspSeedDefect_dilate_bound
  let B : ℝ := (3 / 2) * (K * C) * (integralQuotientVolume globalKubotaKernel).real Set.univ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb (A : ℝ) (hA : 1 < A) : ‖inner ℂ F cubicEisensteinResidue‖ ≤ B / A := by
    have he : cubicEisensteinResidue = kernelEisensteinResidueVector A (2 * A) (by linarith) (by linarith) :=
      kernelEisensteinResidueVector_cutoff_independent 2 3 A (2 * A)
        (by norm_num) (by norm_num) hA (by linarith)
    rw [he, kernelEisensteinResidueVector_pairing _ _ _ _ F hF, norm_mul]
    norm_num
    calc
      _ ≤ (3 / 2) * ((K * C / A) * (integralQuotientVolume globalKubotaKernel).real Set.univ) :=
        mul_le_mul_of_nonneg_left (movingDefect_inner_bound F f hrep K C hK hC hdec hbound A hA) (by norm_num)
      _ = B / A := by dsimp only [B]; ring
  apply norm_eq_zero.mp
  by_contra hn
  have hnpos := lt_of_le_of_ne (norm_nonneg (inner ℂ F cubicEisensteinResidue)) (Ne.symm hn)
  let A := B / ‖inner ℂ F cubicEisensteinResidue‖ + 2
  have hA : 1 < A := by
    have hh := div_nonneg hB hnpos.le
    dsimp only [A]
    linarith
  have hh := (le_div_iff₀ (zero_lt_one.trans hA)).mp (hb A hA)
  have he : ‖inner ℂ F cubicEisensteinResidue‖ * A = B + 2 * ‖inner ℂ F cubicEisensteinResidue‖ := by
    dsimp only [A]
    field_simp
  rw [he] at hh
  linarith only [hh, hnpos]

lemma coset_decay_of_cusp_chart_decay (f : KernelQuotient → ℂ) (K : ℝ)
    (hdec : ∀ M : levelThree, ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))‖ ≤ K / v ^ 3) :
    ∀ w : HyperbolicSpace, ∀ r : CuspCosets, 1 < cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖ ≤ K / (cosetHeight r w) ^ 3 := by
  intro w r
  induction r using Quotient.inductionOn with
  | _ M =>
    intro hr
    change 1 < cosetHeight (cosetOf M) w at hr
    change _ ≤ K / (cosetHeight (cosetOf M) w) ^ 3
    rw [cosetHeight_cosetOf] at hr ⊢
    obtain ⟨z, v, hv, hpt⟩ := upperPoint_surjective (complexMatrix M • w)
    have hh : hyperbolicHeight (complexMatrix M • w) = v := by rw [← hpt, hyperbolicHeight_upperPoint]
    rw [hh] at hr ⊢
    have he : complexMatrix M⁻¹ • upperPoint z v hv = w := by rw [hpt, map_inv, inv_smul_smul]
    simpa only [he] using hdec M⁻¹ z v hv hr

theorem cubicEisensteinResidue_orthogonal_of_cusp_chart_decay
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hdec : ∀ M : levelThree, ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))‖ ≤ K / v ^ 3) :
    inner ℂ F cubicEisensteinResidue = 0 :=
  cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay F hF f hrep K hK
    (coset_decay_of_cusp_chart_decay f K hdec)

lemma kernelRationalPullback_pairing_inverse (g : rationalExtension) (F G : KernelQuotientL2) :
    inner ℂ F (kernelRationalPullback g G) = inner ℂ (kernelRationalPullback g⁻¹ F) G := by
  calc
    _ = inner ℂ (kernelRationalPullback g (kernelRationalPullback g⁻¹ F)) (kernelRationalPullback g G) := by
      rw [kernelRationalPullback_comp, inv_mul_cancel, kernelRationalPullback_one]
    _ = _ := LinearIsometry.inner_map_map _ _ _

lemma cubicEisensteinResidue_rational_translate_orthogonal
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ N : SL(2, O), ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f (integralOrbitProjection globalKubotaKernel (integralComplexMatrix N • upperPoint z v hv))‖ ≤ C / v ^ 3)
    (g : rationalExtension) : inner ℂ F (kernelRationalPullback g cubicEisensteinResidue) = 0 := by
  rw [kernelRationalPullback_pairing_inverse]
  have hrepG : kernelRationalPullback g⁻¹ F =ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => f (kernelRationalAction g⁻¹ q) :=
    (kernelRationalPullback_ae g⁻¹ F).trans
      ((kernelRationalAction_measurePreserving g⁻¹).quasiMeasurePreserving.ae_eq_comp hrep)
  apply cubicEisensteinResidue_orthogonal_of_cusp_chart_decay _
    (kernelRational_eigenvector g⁻¹ F (8 / 9) hF) _ hrepG C hC
  intro N z v hv hlarge
  rw [kernelRationalAction_mk]
  have hh := hdec ((g⁻¹ : rationalExtension) * (N : SL(2, O))) z v hv hlarge
  simpa only [map_mul, mul_smul, integralComplexMatrix_levelThree] using hh

theorem cubicSourceResidue_orthogonal_of_integral_cusp_decay
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec : ∀ N : SL(2, O), ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f (integralOrbitProjection globalKubotaKernel (integralComplexMatrix N • upperPoint z v hv))‖ ≤ C / v ^ 3) :
    inner ℂ F (kernelRationalSourceProjection cubicEisensteinResidue) = 0 := by
  rw [kernelRationalSourceProjection_apply, inner_smul_right, inner_sum]
  simp only [cubicEisensteinResidue_rational_translate_orthogonal F hF f hrep C hC hdec,
    Finset.sum_const_zero, mul_zero]

/-- Adjoint orthogonality forces a finite correspondence combination of the source residue to vanish. -/
theorem commonCover_source_span_vanish {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι]
    (leg : ι → KernelQuotientL2 →L[ℂ] E) (c : ι → ℂ) (D : E)
    (hD : D = ∑ i, c i • leg i (kernelRationalSourceProjection cubicEisensteinResidue))
    (hEig : ∀ i, (ContinuousLinearMap.adjoint (leg i) D,
      (8 / 9 : ℂ) • ContinuousLinearMap.adjoint (leg i) D) ∈ kernelEnergyLaplacian.graph)
    (f : ι → KernelQuotient → ℂ)
    (hrep : ∀ i, ContinuousLinearMap.adjoint (leg i) D =ᵐ[integralQuotientVolume globalKubotaKernel] f i)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hdec : ∀ i, ∀ N : SL(2, O), ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f i (integralOrbitProjection globalKubotaKernel (integralComplexMatrix N • upperPoint z v hv))‖ ≤ C i / v ^ 3) :
    D = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    inner ℂ D D = inner ℂ D (∑ i, c i • leg i (kernelRationalSourceProjection cubicEisensteinResidue)) :=
      congrArg (inner ℂ D) hD
    _ = ∑ i, c i * inner ℂ D (leg i (kernelRationalSourceProjection cubicEisensteinResidue)) := by
      simp only [inner_sum, inner_smul_right]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [← ContinuousLinearMap.adjoint_inner_left,
        cubicSourceResidue_orthogonal_of_integral_cusp_decay _ (hEig i) (f i) (hrep i) (C i) (hC i) (hdec i), mul_zero]

/-- Arithmetic residue of the projected source, normalized by the period area. -/
def rationalSourceScatteringResidue (h : O) : ℂ :=
  if h = 0 then constantArithmeticResidue else
    (4 : ℂ)⁻¹ * (nonzeroScatteringResidue h + rationalCuspPhaseSum h *
      oppositeCuspResidue h / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ))

lemma rationalSourceResidualFourierCoefficient_eq (h : O) (hh : h ≠ 0) :
    rationalSourceResidualFourierCoefficient h = rationalSourceScatteringResidue h *
      ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) * (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)) := by
  rw [rationalSourceResidualFourierCoefficient, cubicResidualFourierCoefficient,
    oppositeResidualFourierCoefficient, rationalSourceScatteringResidue, if_neg hh]
  ring

lemma residue_whittaker_bessel (R : ℂ) (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    R * ((v : ℂ) ^ (2 / 3 : ℂ) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) =
      (R * ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
        (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ))) * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * (v : ℂ) ^ 3 = (v : ℂ) ^ (2 / 3 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hv0]
    congr 1
    norm_num
  calc
    _ = R * (((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) *
        sourceFourierKernel (4 / 3) (cuspFrequency h * v)) * (v : ℂ) ^ 3) := by rw [← hp]; ring
    _ = _ := by
      rw [sourceFourierKernel_residual_height h hh v hv]
      field_simp [hv0]

theorem cubicSourceResidualFunction_fourier (v : ℝ) (hv : 0 < v) (h : O) :
    (∫ z in periodDomain, cubicSourceResidualFunction (upperPoint z v hv) * tracePhase (-cuspFrequency h * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * rationalSourceScatteringResidue h *
        ((v : ℂ) ^ (2 / 3 : ℂ) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) := by
  by_cases hh : h = 0
  · subst h
    simp only [cuspFrequency, map_zero, zero_div, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one,
      rationalSourceScatteringResidue, if_true, sourceFourierKernel_zero (4 / 3) (by norm_num)]
    rw [cubicSourceResidualFunction_fourier_zero]
    ring
  · rw [cubicSourceResidualFunction_fourier_bessel v hv h hh,
      rationalSourceResidualFourierCoefficient_eq h hh]
    have he := residue_whittaker_bessel (rationalSourceScatteringResidue h) v hv h hh
    linear_combination -((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * he

theorem rationalSourceScatteringResidue_prime_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceScatteringResidue (h * p ^ 3) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * rationalSourceScatteringResidue h -
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) * cubicUnitGaussSum (9 * h) p *
        rationalSourceScatteringResidue (h * p) := by
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  have hg := unramifiedGaussResidue_prime_recurrence p hp hprimary (9 * h)
    (primary_prime_not_dvd_nine_frequency p hp hprimary h hph)
  rw [primeCubicGauss_one_eq] at hg
  simp only [rationalSourceScatteringResidue, if_neg hh, if_neg (mul_ne_zero hh hp.ne_zero),
    if_neg (mul_ne_zero hh (pow_ne_zero 3 hp.ne_zero)), oppositeCuspResidue_eq_unramified]
  rw [rationalCuspPhaseSum_primary_mul h (p ^ 3) (primary_pow_congruence p hprimary 3),
    rationalCuspPhaseSum_primary_mul h p hprimary, nonzeroScatteringResidue_prime_recurrence p hp hprimary h hph,
    show 9 * (h * p ^ 3) = (9 * h) * p ^ 3 by ring, hg,
    show 9 * (h * p) = (9 * h) * p by ring]
  ring

theorem rationalSourceScatteringResidue_cube_recurrence (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    rationalSourceScatteringResidue (h * p ^ 6) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * rationalSourceScatteringResidue (h * p ^ 3) -
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * rationalSourceScatteringResidue h := by
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul]
    ring
  simp only [rationalSourceScatteringResidue, if_neg hh,
    if_neg (mul_ne_zero hh (pow_ne_zero 3 hp.ne_zero)),
    if_neg (mul_ne_zero hh (pow_ne_zero 6 hp.ne_zero)), oppositeCuspResidue_eq_unramified]
  rw [rationalCuspPhaseSum_primary_mul h (p ^ 6) (primary_pow_congruence p hprimary 6),
    rationalCuspPhaseSum_primary_mul h (p ^ 3) (primary_pow_congruence p hprimary 3),
    nonzeroScatteringResidue_cube_recurrence p hp hprimary h hh,
    show 9 * (h * p ^ 6) = (9 * h) * p ^ 6 by ring,
    show 9 * (h * p ^ 3) = (9 * h) * p ^ 3 by ring,
    unramifiedGaussResidue_cube_recurrence p hp hprimary (9 * h)]
  ring

theorem rationalSourceScatteringResidue_square_cube (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    rationalSourceScatteringResidue (h * p ^ 5) =
      (1 + (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹) * rationalSourceScatteringResidue (h * p ^ 2) := by
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  simp only [rationalSourceScatteringResidue,
    if_neg (mul_ne_zero hh (pow_ne_zero 2 hp.ne_zero)),
    if_neg (mul_ne_zero hh (pow_ne_zero 5 hp.ne_zero)), oppositeCuspResidue_eq_unramified]
  rw [rationalCuspPhaseSum_primary_mul h (p ^ 5) (primary_pow_congruence p hprimary 5),
    rationalCuspPhaseSum_primary_mul h (p ^ 2) (primary_pow_congruence p hprimary 2),
    nonzeroScatteringResidue_square_cube p hp hprimary h hph,
    show 9 * (h * p ^ 5) = (9 * h) * p ^ 5 by ring,
    show 9 * (h * p ^ 2) = (9 * h) * p ^ 2 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (9 * h)
      (primary_prime_not_dvd_nine_frequency p hp hprimary h hph)]
  ring

/-- An absolutely convergent Fourier series on the Eisenstein period lattice. -/
def cuspCharacterSeries (a : O → ℂ) (z : ℂ) : ℂ :=
  ∑' h : O, a h * tracePhase (cuspFrequency h * z)

lemma cuspCharacterSeries_continuous (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) :
    Continuous (cuspCharacterSeries a) := by
  apply continuous_tsum (u := fun h => ‖a h‖) _ ha
  · intro h z
    simp only [norm_mul, tracePhase_norm, mul_one, le_refl]
  · intro h
    change Continuous (fun z : ℂ => a h * Complex.exp (2 * Real.pi * Complex.I *
      ((cuspFrequency h * z) + starRingEnd ℂ (cuspFrequency h * z))))
    fun_prop

lemma cuspCharacterSeries_period (a : O → ℂ) (z : ℂ) (n : O) :
    cuspCharacterSeries a (z + 3 * ringComplex n) = cuspCharacterSeries a z := by
  apply tsum_congr
  intro h
  rw [mul_add, AddChar.map_add_eq_mul, cuspFrequency_period, mul_one]

theorem cuspCharacterSeries_fourier (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (k : O) :
    (∫ z in periodDomain, cuspCharacterSeries a z * tracePhase (-cuspFrequency k * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * a k := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  letI : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : O → ℂ → ℂ := fun h z => a h *
    tracePhase (cuspFrequency h * z) * tracePhase (-cuspFrequency k * z)
  have hc (h : O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => a h *
      Complex.exp (2 * Real.pi * Complex.I * ((cuspFrequency h * z) + starRingEnd ℂ (cuspFrequency h * z))) *
      Complex.exp (2 * Real.pi * Complex.I * ((-cuspFrequency k * z) + starRingEnd ℂ (-cuspFrequency k * z))))
    fun_prop
  have hn (h : O) (z : ℂ) : ‖f h z‖ = ‖a h‖ := by
    simp only [f, norm_mul, tracePhase_norm, mul_one]
  have hi (h : O) : IntegrableOn (f h) periodDomain :=
    periodDomain_continuous_integrable _ (hc h)
  have hs : Summable (fun h : O => ∫ z in periodDomain, ‖f h z‖) := by
    simp only [hn, setIntegral_const, smul_eq_mul]
    exact ha.mul_left (volume.real periodDomain)
  have hterm (h : O) : (∫ z in periodDomain, f h z) =
      if h = k then ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * a h else 0 := by
    dsimp only [f]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫ z in periodDomain, ∑' h : O, f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑' h : O, a h * tracePhase (cuspFrequency h * z)) *
          tracePhase (-cuspFrequency k * z) = _
        rw [← tsum_mul_right])
    _ = ∑' h : O, ∫ z in periodDomain, f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by simp only [hterm, tsum_ite_eq]

/-- A summable majorant controls the entire nonconstant Fourier remainder. -/
lemma cuspCharacterSeries_remainder_bound (a : O → ℂ) (B : O → ℝ) (hB : Summable B)
    (hB0 : ∀ h, 0 ≤ B h) (ha : ∀ h, h ≠ 0 → ‖a h‖ ≤ B h) (z : ℂ) :
    ‖cuspCharacterSeries a z - a 0‖ ≤ ∑' h, B h := by
  let b : O → ℂ := fun h => if h = 0 then 0 else a h * tracePhase (cuspFrequency h * z)
  have hb (h : O) : ‖b h‖ ≤ B h := by
    by_cases hh : h = 0
    · simpa only [b, if_pos hh, norm_zero] using hB0 h
    · simpa only [b, if_neg hh, norm_mul, tracePhase_norm, mul_one] using ha h hh
  have hbs : Summable (fun h => ‖b h‖) := Summable.of_nonneg_of_le (fun h => norm_nonneg _) hb hB
  have hz : Summable (fun h : O => if h = 0 then a 0 else 0) := (hasSum_ite_eq 0 _).summable
  have hsplit (h : O) : a h * tracePhase (cuspFrequency h * z) = (if h = 0 then a 0 else 0) + b h := by
    by_cases hh : h = 0
    · subst h
      simp only [b, if_true, cuspFrequency, map_zero, zero_div, zero_mul,
        AddChar.map_zero_eq_one, mul_one, add_zero]
    · simp only [b, if_neg hh, zero_add]
  rw [cuspCharacterSeries]
  simp_rw [hsplit]
  rw [hz.tsum_add hbs.of_norm, tsum_ite_eq, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hbs).trans (Summable.tsum_le_tsum hb hbs hB)

lemma periodDomain_continuous_memLp (f : ℂ → ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict periodDomain) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply ((hf.norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) (∑ i, ‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz

/-- Continuity and periodicity upgrade equality of Fourier coefficients to pointwise equality. -/
theorem periodDomain_continuous_ext (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfper : ∀ n z, f (z + 3 * ringComplex n) = f z)
    (hgper : ∀ n z, g (z + 3 * ringComplex n) = g z)
    (heq : ∀ h : O, (∫ z in periodDomain, f z * tracePhase (-cuspFrequency h * z)) =
      ∫ z in periodDomain, g z * tracePhase (-cuspFrequency h * z)) : f = g :=
  Measure.eq_of_ae_eq (ae_eq_of_periodDomain_eq f g hfper hgper
    (periodDomain_L2_ext f g (periodDomain_continuous_memLp f hf)
      (periodDomain_continuous_memLp g hg) heq)) hf hg

def rationalSourceModeAmplitude (v : ℝ) (h : O) : ℂ :=
  rationalSourceScatteringResidue h * ((v : ℂ) ^ (2 / 3 : ℂ) *
    sourceFourierKernel (4 / 3) (cuspFrequency h * v))

lemma rationalSourceModeAmplitude_bessel (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    rationalSourceModeAmplitude v h = rationalSourceResidualFourierCoefficient h * (v : ℂ) *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  rw [rationalSourceModeAmplitude, residue_whittaker_bessel _ v hv h hh,
    rationalSourceResidualFourierCoefficient_eq h hh]

lemma rationalSourceModeAmplitude_summable (v : ℝ) (hv : 0 < v) :
    Summable (fun h => ‖rationalSourceModeAmplitude v h‖) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselCoefficient_strip_bound rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_subexponential v v hv le_rfl
  have hs := (summable_exp_neg_cuspFrequency_norm (Real.pi * v)
    (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : O => if h = 0 then ‖rationalSourceModeAmplitude v 0‖ else 0) :=
    (hasSum_ite_eq 0 _).summable
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _ (hz.add hs)
  intro h
  by_cases hh : h = 0
  · subst h
    simp only [if_true]
    exact le_add_of_nonneg_right (mul_nonneg hC (Real.exp_pos _).le)
  · simp only [if_neg hh, zero_add]
    rw [rationalSourceModeAmplitude_bessel v hv h hh]
    exact hb h hh v ⟨le_rfl, le_rfl⟩

lemma cubicSourceResidualFunction_period (v : ℝ) (hv : 0 < v) (z : ℂ) (n : O) :
    cubicSourceResidualFunction (upperPoint (z + 3 * ringComplex n) v hv) =
      cubicSourceResidualFunction (upperPoint z v hv) := by
  have hn := integralTranslation_three_mem_kernel n
  have he := cubicSourceResidualFunction_automorphy
    ⟨integralTranslation (3 * n), levelThree_le_rationalExtension ((globalKubotaKernel_mem _).mp hn).1⟩
      (upperPoint z v hv)
  have hchar : extendedComplexCharacter
      ⟨integralTranslation (3 * n), levelThree_le_rationalExtension ((globalKubotaKernel_mem _).mp hn).1⟩ = 1 := by
    rw [extendedComplexCharacter_restrict ⟨_, ((globalKubotaKernel_mem _).mp hn).1⟩]
    exact ((globalKubotaKernel_mem _).mp hn).2
  simpa only [hchar, one_mul, integralTranslation_action, map_mul, map_ofNat] using he

/-- The projected residual source equals its normally convergent Fourier expansion at every height. -/
theorem cubicSourceResidualFunction_fourier_expansion (v : ℝ) (hv : 0 < v) (z : ℂ) :
    cubicSourceResidualFunction (upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude v) z := by
  have hc : Continuous (fun z : ℂ => cubicSourceResidualFunction (upperPoint z v hv)) :=
    cubicSourceResidualFunction_continuous.comp
      (upperCoordinatesHomeomorph.continuous.comp
        (show Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) by fun_prop))
  have hs := rationalSourceModeAmplitude_summable v hv
  have he := periodDomain_continuous_ext _ _ hc (cuspCharacterSeries_continuous _ hs)
    (fun n z => cubicSourceResidualFunction_period v hv z n)
    (fun n z => cuspCharacterSeries_period _ z n) (fun h => by
      rw [cubicSourceResidualFunction_fourier v hv h, cuspCharacterSeries_fourier _ hs h]
      exact mul_assoc _ _ _)
  exact congrFun he z

lemma height_mul_exp_neg_le_inverse_cube (ε v : ℝ) (hε : 0 < ε) (hv : 0 < v) :
    v * Real.exp (-ε * v) ≤ (24 / ε ^ 4) / v ^ 3 := by
  have hp := Real.pow_div_factorial_le_exp (ε * v) (mul_pos hε hv).le 4
  norm_num only [Nat.factorial] at hp
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (ε * v) ^ 4 / 24) hp
  rw [one_div, ← Real.exp_neg] at hi
  calc
    _ ≤ v * (((ε * v) ^ 4 / 24)⁻¹) :=
      mul_le_mul_of_nonneg_left (by simpa only [neg_mul, one_div] using hi) hv.le
    _ = _ := by field_simp

/-- A fixed frequency gap turns exponential Bessel decay into a summable cubic height bound. -/
theorem cubicBesselCoefficient_cusp_bound (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 → ∀ v : ℝ, 1 ≤ v →
      ‖c h * (v : ℂ) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ ≤
        (C / v ^ 3) * Real.exp (-(Real.pi / 2) * ‖cuspFrequency h‖) := by
  let d : ℝ := ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹
  have hd : 0 < d := inv_pos.mpr (norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero)))
  obtain ⟨B, hB, hb⟩ := schlafliBesselK_one_third_exp_upper (4 * Real.pi * d) (by positivity)
  obtain ⟨A, hA, ha⟩ := hsub (Real.pi / 2) (by positivity)
  refine ⟨A * B * (24 / (Real.pi * d) ^ 4), by positivity, ?_⟩
  intro h hh v hv
  have hvp : 0 < v := zero_lt_one.trans_le hv
  have hgap : d ≤ ‖cuspFrequency h‖ := cuspFrequency_norm_lower h hh
  have hrv : ‖cuspFrequency h‖ ≤ ‖cuspFrequency h‖ * v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg (cuspFrequency h))
  have hdv := mul_le_mul_of_nonneg_right hgap hvp.le
  have hx : 4 * Real.pi * d ≤ 4 * Real.pi * ‖cuspFrequency h‖ * v := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hgap.trans hrv)
      (show 0 ≤ 4 * Real.pi by positivity)
  have he : (Real.pi / 2) * ‖cuspFrequency h‖ -
      (4 * Real.pi * ‖cuspFrequency h‖ * v) / 2 ≤
      -(Real.pi / 2) * ‖cuspFrequency h‖ + -(Real.pi * d) * v := by
    have hm := mul_le_mul_of_nonneg_left (add_le_add hrv hdv) Real.pi_pos.le
    nlinarith only [hm]
  rw [norm_mul, norm_mul, Complex.norm_of_nonneg hvp.le]
  calc
    _ ≤ (A * Real.exp ((Real.pi / 2) * ‖cuspFrequency h‖)) * v *
        (B * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (ha h hh) hvp.le)
        (hb _ hx) (norm_nonneg _) (by positivity)
    _ = (A * B * v) * Real.exp ((Real.pi / 2) * ‖cuspFrequency h‖ -
        (4 * Real.pi * ‖cuspFrequency h‖ * v) / 2) := by
      rw [show -(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2 =
        -((4 * Real.pi * ‖cuspFrequency h‖ * v) / 2) by ring, Real.exp_neg, Real.exp_sub]
      ring
    _ ≤ (A * B * v) * Real.exp (-(Real.pi / 2) * ‖cuspFrequency h‖ + -(Real.pi * d) * v) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = (A * B * Real.exp (-(Real.pi / 2) * ‖cuspFrequency h‖)) *
        (v * Real.exp (-(Real.pi * d) * v)) := by rw [Real.exp_add]; ring
    _ ≤ (A * B * Real.exp (-(Real.pi / 2) * ‖cuspFrequency h‖)) *
        ((24 / (Real.pi * d) ^ 4) / v ^ 3) :=
      mul_le_mul_of_nonneg_left (height_mul_exp_neg_le_inverse_cube _ _ (by positivity) hvp) (by positivity)
    _ = _ := by ring

lemma rationalSourceModeAmplitude_zero (v : ℝ) :
    rationalSourceModeAmplitude v 0 =
      3 * (Real.pi : ℂ) * constantArithmeticResidue * (v : ℂ) ^ (2 / 3 : ℂ) := by
  simp only [rationalSourceModeAmplitude, rationalSourceScatteringResidue, if_true,
    cuspFrequency, map_zero, zero_div, zero_mul, sourceFourierKernel_zero (4 / 3) (by norm_num)]
  ring

/-- The source's nonconstant Fourier series decays cubically, uniformly along each horosphere. -/
theorem cubicSourceResidualFunction_cusp_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ∀ hv : 0 < v, 1 ≤ v → ∀ z : ℂ,
      ‖cubicSourceResidualFunction (upperPoint z v hv) -
        3 * (Real.pi : ℂ) * constantArithmeticResidue * (v : ℂ) ^ (2 / 3 : ℂ)‖ ≤ C / v ^ 3 := by
  obtain ⟨C, hC, hb⟩ := cubicBesselCoefficient_cusp_bound rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_subexponential
  let w : O → ℝ := fun h => Real.exp (-(Real.pi / 2) * ‖cuspFrequency h‖)
  have hw : Summable w := summable_exp_neg_cuspFrequency_norm (Real.pi / 2) (by positivity)
  refine ⟨C * ∑' h, w h, mul_nonneg hC (tsum_nonneg (fun h => (Real.exp_pos _).le)), ?_⟩
  intro v hv hlarge z
  rw [cubicSourceResidualFunction_fourier_expansion v hv z, ← rationalSourceModeAmplitude_zero]
  have he := cuspCharacterSeries_remainder_bound (rationalSourceModeAmplitude v)
    (fun h => (C / v ^ 3) * w h) (hw.mul_left _) (fun h =>
      mul_nonneg (div_nonneg hC (pow_nonneg hv.le _)) (Real.exp_pos _).le)
    (fun h hh => by rw [rationalSourceModeAmplitude_bessel v hv h hh]; exact hb h hh v hlarge) z
  rw [tsum_mul_left] at he
  convert he using 1
  ring

/-- Cubic cusp decay holds uniformly above any fixed positive height. -/
theorem cubicSourceResidualFunction_cusp_decay_from_height (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ∀ hv : 0 < v, a ≤ v → ∀ z : ℂ,
      ‖cubicSourceResidualFunction (upperPoint z v hv) -
        3 * (Real.pi : ℂ) * constantArithmeticResidue * (v : ℂ) ^ (2 / 3 : ℂ)‖ ≤ C / v ^ 3 := by
  obtain ⟨C, hC, hc⟩ := cubicSourceResidualFunction_cusp_decay
  obtain ⟨B, hB, hb⟩ := cubicBesselCoefficient_strip_bound rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_subexponential a (max a 1) ha (le_max_left _ _)
  let w : O → ℝ := fun h => Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖)
  have hw : Summable w := summable_exp_neg_cuspFrequency_norm (Real.pi * a) (mul_pos Real.pi_pos ha)
  let D := B * ∑' h, w h
  have hD : 0 ≤ D := mul_nonneg hB (tsum_nonneg (fun h => (Real.exp_pos _).le))
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro v hv hav z
  by_cases hv1 : 1 ≤ v
  · exact (hc v hv hv1 z).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hD) (pow_nonneg hv.le _))
  have hvlt : v < 1 := lt_of_not_ge hv1
  have hbv : v ∈ Set.Icc a (max a 1) := ⟨hav, hvlt.le.trans (le_max_right _ _)⟩
  have hn : ‖cubicSourceResidualFunction (upperPoint z v hv) -
      3 * (Real.pi : ℂ) * constantArithmeticResidue * (v : ℂ) ^ (2 / 3 : ℂ)‖ ≤ D := by
    rw [cubicSourceResidualFunction_fourier_expansion v hv z, ← rationalSourceModeAmplitude_zero]
    have he := cuspCharacterSeries_remainder_bound (rationalSourceModeAmplitude v)
      (fun h => B * w h) (hw.mul_left _) (fun h => mul_nonneg hB (Real.exp_pos _).le)
      (fun h hh => by rw [rationalSourceModeAmplitude_bessel v hv h hh]; exact hb h hh v hbv) z
    simpa only [tsum_mul_left] using he
  have hv3 : v ^ 3 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hv.le hvlt.le 3
  apply hn.trans
  apply (le_div_iff₀ (pow_pos hv 3)).mpr
  exact (mul_le_of_le_one_right hD hv3).trans (le_add_of_nonneg_left hC)

open scoped Matrix

lemma cusp_omega_relation : omega ^ 2 + omega + 1 = (0 : O) := by
  have h := lambda_sq_eq
  rw [lambda_def] at h
  linear_combination h

def lowerCuspMatrix (t : O) : SL(2, O) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

/-- Translation by three, conjugated to the lower unipotent cusp. -/
def ramifiedParabolic (t x : O) : levelThree := by
  let M : SL(2, O) := ⟨!![1 - 3 * t * x, 3 * x; -3 * t ^ 2 * x, 1 + 3 * t * x], by
    rw [Matrix.det_fin_two]
    change (1 - 3 * t * x) * (1 + 3 * t * x) - (3 * x) * (-3 * t ^ 2 * x) = 1
    ring⟩
  refine ⟨M, levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-t * x, by change 1 - 3 * t * x - 1 = 3 * (-t * x); ring⟩
  · exact ⟨x, by change 3 * x - 0 = 3 * x; ring⟩
  · exact ⟨-t ^ 2 * x, by change -3 * t ^ 2 * x - 0 = 3 * (-t ^ 2 * x); ring⟩
  · exact ⟨t * x, by change 1 + 3 * t * x - 1 = 3 * (t * x); ring⟩

lemma ramifiedParabolic_mul_lower (t x : O) :
    (ramifiedParabolic t x : SL(2, O)) * lowerCuspMatrix t =
      lowerCuspMatrix t * integralTranslation (3 * x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic, lowerCuspMatrix, integralTranslation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma ramifiedParabolic_character (t x : O) :
    complexCharacter (ramifiedParabolic t x) = ringComplex (symbol (-t) (1 - 3 * t * x)) := by
  simp only [complexCharacter, MonoidHom.comp_apply, character, ramifiedParabolic]
  apply congrArg ringComplex
  apply symbol_congr
  refine ⟨t, ?_⟩
  change -3 * t ^ 2 * x - (-t) = (1 - 3 * t * x) * t
  ring

lemma ramifiedParabolic_omega_character (A B : ℤ) :
    complexCharacter (ramifiedParabolic omega (Coordinates.eval A B)) =
      ringComplex (cubicExp (A + B)) := by
  rw [ramifiedParabolic_character]
  have hd : 1 - 3 * omega * Coordinates.eval A B = primaryCoord B (B - A) := by
    rw [primaryCoord_eq]
    change 1 - 3 * omega * ((A : O) + (B : O) * omega) = _
    push_cast
    linear_combination -3 * (B : O) * cusp_omega_relation
  rw [hd, symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _), linearRay_primaryCoord]
  congr 2
  ring

lemma ramifiedParabolic_omega_sq_character (A B : ℤ) :
    complexCharacter (ramifiedParabolic (omega ^ 2) (Coordinates.eval A B)) =
      ringComplex (cubicExp (-(A + B))) := by
  rw [ramifiedParabolic_character]
  have hd : 1 - 3 * omega ^ 2 * Coordinates.eval A B = primaryCoord (A - B) A := by
    rw [primaryCoord_eq]
    change 1 - 3 * omega ^ 2 * ((A : O) + (B : O) * omega) = _
    push_cast
    linear_combination -3 * ((A : O) + (B : O) * omega - (B : O)) * cusp_omega_relation
  rw [hd, symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) 2,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _), linearRay_primaryCoord]
  have he : cubicExp (2 * ((A - B) * 2 + (-1) * A)) = cubicExp (-(A + B)) := by
    apply cubicExp_eq_of_dvd_sub
    exact ⟨A - B, by ring⟩
  have hs : cubicExp ((A - B) * 2 + (-1) * A) ^ 2 = cubicExp (2 * ((A - B) * 2 + (-1) * A)) := by
    rw [pow_two, ← cubicExp_add]
    congr 1
    ring
  convert congrArg ringComplex (hs.trans he) using 1
  congr 2
  ring

def ramifiedSourceFunction (t : O) (w : HyperbolicSpace) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix (lowerCuspMatrix t) • w)

lemma ramifiedSourceFunction_continuous (t : O) : Continuous (ramifiedSourceFunction t) :=
  cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)

lemma ramifiedSourceFunction_period (t x : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ramifiedSourceFunction t (upperPoint (z + 3 * ringComplex x) v hv) =
      ringComplex (symbol (-t) (1 - 3 * t * x)) * ramifiedSourceFunction t (upperPoint z v hv) := by
  let n := ramifiedParabolic t x
  have he := cubicSourceResidualFunction_automorphy
    ⟨(n : SL(2, O)), levelThree_le_rationalExtension n.property⟩
      (integralComplexMatrix (lowerCuspMatrix t) • upperPoint z v hv)
  rw [extendedComplexCharacter_restrict, ramifiedParabolic_character] at he
  change cubicSourceResidualFunction (integralComplexMatrix (n : SL(2, O)) •
    (integralComplexMatrix (lowerCuspMatrix t) • upperPoint z v hv)) = _ at he
  rw [← mul_smul, ← map_mul, ramifiedParabolic_mul_lower, map_mul, mul_smul] at he
  simpa only [ramifiedSourceFunction, integralTranslation_action, map_mul, map_ofNat] using he

lemma ramifiedParabolic_three (t x : O) :
    ramifiedParabolic t (3 * x) = ramifiedParabolic t x ^ 3 := by
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma ramifiedSourceFunction_nine_period (t x : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ramifiedSourceFunction t (upperPoint (z + 9 * ringComplex x) v hv) =
      ramifiedSourceFunction t (upperPoint z v hv) := by
  have he := ramifiedSourceFunction_period t (3 * x) z v hv
  rw [← ramifiedParabolic_character, ramifiedParabolic_three, map_pow, complexCharacter_cube, one_mul] at he
  rw [map_mul, map_ofNat, show 3 * ((3 : ℂ) * ringComplex x) = 9 * ringComplex x by ring] at he
  exact he

lemma ramifiedSourceFunction_scaled_period (t : O) (v : ℝ) (hv : 0 < v) (x : O) (z : ℂ) :
    ramifiedSourceFunction t (upperPoint (3 * (z + 3 * ringComplex x)) v hv) =
      ramifiedSourceFunction t (upperPoint (3 * z) v hv) := by
  rw [show 3 * (z + 3 * ringComplex x) = 3 * z + 9 * ringComplex x by ring]
  exact ramifiedSourceFunction_nine_period t x (3 * z) v hv

/-- A nontrivial translation character annihilates the constant Fourier coefficient. -/
lemma period_integral_zero_of_character (f : ℂ → ℂ)
    (hper : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z)
    (b χ : ℂ) (hχ : χ ≠ 1) (htranslate : ∀ z, f (z + b) = χ * f z) :
    ∫ z in periodDomain, f z = 0 := by
  have he := period_fourier_translation f hper 0 b
  simp only [cuspFrequency, map_zero, zero_div, neg_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one, one_mul] at he
  simp_rw [htranslate] at he
  rw [integral_const_mul] at he
  have hz : (χ - 1) * ∫ z in periodDomain, f z = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχ)

theorem ramifiedSourceFunction_omega_constant_zero (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, ramifiedSourceFunction omega (upperPoint (3 * z) v hv) = 0 := by
  apply period_integral_zero_of_character _ (ramifiedSourceFunction_scaled_period omega v hv)
    1 (ringComplex omega)
  · intro he
    have hω : omega = 1 := ringComplex_injective (by simpa only [map_one] using he)
    have h := (omega_primitive.pow_eq_one_iff_dvd 1).mp (by simpa only [pow_one] using hω)
    norm_num at h
  · intro z
    have he := ramifiedSourceFunction_period omega (Coordinates.eval 1 0) (3 * z) v hv
    rw [← ramifiedParabolic_character, ramifiedParabolic_omega_character] at he
    norm_num [Coordinates.eval, cubicExp] at he
    rw [show 3 * (z + 1) = 3 * z + (3 : ℂ) by ring]
    exact he

theorem ramifiedSourceFunction_omega_sq_constant_zero (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, ramifiedSourceFunction (omega ^ 2) (upperPoint (3 * z) v hv) = 0 := by
  apply period_integral_zero_of_character _ (ramifiedSourceFunction_scaled_period (omega ^ 2) v hv)
    1 (ringComplex (omega ^ 2))
  · intro he
    have hω : omega ^ 2 = 1 := ringComplex_injective (by simpa only [map_one] using he)
    have h := (omega_primitive.pow_eq_one_iff_dvd 2).mp hω
    norm_num at h
  · intro z
    have he := ramifiedSourceFunction_period (omega ^ 2) (Coordinates.eval 1 0) (3 * z) v hv
    rw [← ramifiedParabolic_character, ramifiedParabolic_omega_sq_character] at he
    norm_num [Coordinates.eval, cubicExp] at he
    rw [map_pow, show 3 * (z + 1) = 3 * z + (3 : ℂ) by ring]
    simpa only [Int.toNat] using he

/-- The quotient map induced by inclusion of integral subgroups. -/
def integralCoverMap {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) :
    IntegralOrbitQuotient H → IntegralOrbitQuotient K :=
  Quotient.map' id (by
    rintro w u ⟨M, hM⟩
    exact ⟨Subgroup.inclusion hHK M, hM⟩)

lemma integralCoverMap_projection {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralOrbitProjection H w) = integralOrbitProjection K w := rfl

lemma integralCoverMap_measurable {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) :
    Measurable (integralCoverMap hHK) :=
  measurable_from_quotient.mpr (measurable_integralOrbitProjection K)

lemma integralCoverMap_continuous {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) :
    Continuous (integralCoverMap hHK) := continuous_id.quotient_map' _

lemma integralCoverMap_surjective {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) :
    Function.Surjective (integralCoverMap hHK) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact ⟨integralOrbitProjection H w, rfl⟩

abbrev IntegralCoverCosets (H K : Subgroup (SL(2, O))) := K ⧸ H.subgroupOf K

def integralCoverRep (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K) : K := q.out

def integralCoverSheet (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K) : Set HyperbolicSpace :=
  (fun w => integralCoverRep H K q • w) ⁻¹' hyperbolicFundamentalSet K

/-- Coset translates of a base fundamental domain form a domain for the covering subgroup. -/
def integralCoverDomain (H K : Subgroup (SL(2, O))) : Set HyperbolicSpace :=
  ⋃ q : IntegralCoverCosets H K, integralCoverSheet H K q

lemma integralCoverSheet_measurable (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K) :
    MeasurableSet (integralCoverSheet H K q) :=
  (measurable_const_smul (integralCoverRep H K q)) (hyperbolicFundamentalSet_measurable K)

lemma integralCoverDomain_measurable (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K] :
    MeasurableSet (integralCoverDomain H K) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  exact MeasurableSet.iUnion (integralCoverSheet_measurable H K)

lemma fundamental_reduction_unique (K : Subgroup (SL(2, O))) (hK : K ≤ levelThree)
    (r s : K) (w : HyperbolicSpace) (hr : r • w ∈ hyperbolicFundamentalSet K)
    (hs : s • w ∈ hyperbolicFundamentalSet K) : r = s := by
  obtain ⟨m, _, hm⟩ := hyperbolicFundamentalSet_unique K hK w
  exact (hm r hr).trans (hm s hs).symm

lemma integralCoverSheet_pairwiseDisjoint (H K : Subgroup (SL(2, O))) (hK : K ≤ levelThree) :
    Pairwise (fun q r => Disjoint (integralCoverSheet H K q) (integralCoverSheet H K r)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro w hwq hwr
  exact hqr (Quotient.out_injective
    (fundamental_reduction_unique K hK (integralCoverRep H K q) (integralCoverRep H K r) w hwq hwr))

lemma integralCoverRep_mul_projection {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (q : IntegralCoverCosets H K) (h : H) :
    ((integralCoverRep H K q * Subgroup.inclusion hHK h : K) : IntegralCoverCosets H K) = q := by
  rw [QuotientGroup.mk_mul_of_mem _ (show Subgroup.inclusion hHK h ∈ H.subgroupOf K from h.property)]
  exact QuotientGroup.out_eq' q

lemma integralCoverSheet_membership {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (q : IntegralCoverCosets H K) (h : H) (w : HyperbolicSpace) :
    h • w ∈ integralCoverSheet H K q ↔
      (integralCoverRep H K q * Subgroup.inclusion hHK h) • w ∈ hyperbolicFundamentalSet K := by
  rw [mul_smul]
  rfl

lemma integralCoverDomain_covers {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) (w : HyperbolicSpace) :
    ∃ h : H, h • w ∈ integralCoverDomain H K := by
  obtain ⟨k, hk⟩ := hyperbolicFundamentalSet_covers K w
  let q : IntegralCoverCosets H K := k
  let r := integralCoverRep H K q
  have hr : r⁻¹ * k ∈ H.subgroupOf K := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  let h : H := ⟨((r⁻¹ * k : K) : SL(2, O)), hr⟩
  have hin : Subgroup.inclusion hHK h = r⁻¹ * k := rfl
  refine ⟨h, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  apply (integralCoverSheet_membership hHK q h w).mpr
  change (r * Subgroup.inclusion hHK h) • w ∈ hyperbolicFundamentalSet K
  rw [hin, mul_inv_cancel_left]
  exact hk

lemma integralCoverDomain_unique {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) (hK : K ≤ levelThree)
    (w : HyperbolicSpace) (h1 h2 : H) (hh1 : h1 • w ∈ integralCoverDomain H K)
    (hh2 : h2 • w ∈ integralCoverDomain H K) : h1 = h2 := by
  obtain ⟨q1, hq1⟩ := Set.mem_iUnion.mp hh1
  obtain ⟨q2, hq2⟩ := Set.mem_iUnion.mp hh2
  have he : integralCoverRep H K q1 * Subgroup.inclusion hHK h1 =
      integralCoverRep H K q2 * Subgroup.inclusion hHK h2 :=
    fundamental_reduction_unique K hK _ _ w
      ((integralCoverSheet_membership hHK q1 h1 w).mp hq1)
      ((integralCoverSheet_membership hHK q2 h2 w).mp hq2)
  have hqeq : q1 = q2 := by
    have hproj := congrArg (fun k : K => (k : IntegralCoverCosets H K)) he
    rwa [integralCoverRep_mul_projection hHK q1 h1, integralCoverRep_mul_projection hHK q2 h2] at hproj
  subst q2
  exact (Subgroup.inclusion_injective hHK) (mul_left_cancel he)

theorem integralCoverDomain_isFundamentalDomain {H K : Subgroup (SL(2, O))}
    (hHK : H ≤ K) (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] :
    IsFundamentalDomain H (integralCoverDomain H K) hyperbolicVolume := by
  apply IsFundamentalDomain.mk' (integralCoverDomain_measurable H K).nullMeasurableSet
  intro w
  obtain ⟨h, hh⟩ := integralCoverDomain_covers hHK w
  exact ⟨h, hh, fun g hg => integralCoverDomain_unique hHK hK w g h hg hh⟩

lemma integralCoverSheet_measure (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K)
    (S : Set (IntegralOrbitQuotient K)) (hS : MeasurableSet S) :
    hyperbolicVolume ((integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q) =
      integralQuotientVolume K S := by
  have he : (integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q =
      (fun w => integralCoverRep H K q • w) ⁻¹'
        ((integralOrbitProjection K) ⁻¹' S ∩ hyperbolicFundamentalSet K) := by
    ext w
    change (integralOrbitProjection K w ∈ S ∧ integralCoverRep H K q • w ∈ hyperbolicFundamentalSet K) ↔
      (integralOrbitProjection K (integralCoverRep H K q • w) ∈ S ∧
        integralCoverRep H K q • w ∈ hyperbolicFundamentalSet K)
    rw [integralSubgroup_smul, integralOrbitProjection_eq]
  rw [he, measure_preimage_smul, integralQuotientVolume,
    Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS)]

/-- Quotient volume pushes forward with multiplicity equal to the covering degree. -/
theorem integralCoverMap_measure {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] :
    Measure.map (integralCoverMap hHK) (integralQuotientVolume H) =
      (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  rw [← integralQuotientVolume_independent H (hHK.trans hK) (integralCoverDomain H K)
    (integralCoverDomain_isFundamentalDomain hHK hK),
    Measure.map_map (integralCoverMap_measurable hHK) (measurable_integralOrbitProjection H)]
  change Measure.map (integralOrbitProjection K) (hyperbolicVolume.restrict (integralCoverDomain H K)) = _
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS), Measure.smul_apply, smul_eq_mul,
    integralCoverDomain, Set.inter_iUnion, measure_iUnion]
  · simp_rw [integralCoverSheet_measure H K _ S hS]
    rw [tsum_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  · intro q r hqr
    exact (integralCoverSheet_pairwiseDisjoint H K hK hqr).mono Set.inter_subset_right Set.inter_subset_right
  · intro q
    exact ((measurable_integralOrbitProjection K) hS).inter (integralCoverSheet_measurable H K q)

lemma integralCoverMap_measurePreserving {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralCoverMap hHK) (integralQuotientVolume H)
      ((H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) :=
  ⟨integralCoverMap_measurable hHK, integralCoverMap_measure hHK hK⟩

abbrev IntegralQuotientL2 (H : Subgroup (SL(2, O))) := Lp ℂ 2 (integralQuotientVolume H)

def integralCoverPullback {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] : IntegralQuotientL2 K →L[ℂ] IntegralQuotientL2 H :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤) le_rfl)

theorem integralCoverPullback_ae {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (F : IntegralQuotientL2 K) :
    integralCoverPullback hHK hK F =ᵐ[integralQuotientVolume H] fun q => F (integralCoverMap hHK q) := by
  have hm := integralCoverMap_measurePreserving hHK hK
  have he := dominatedComplexL2_ae (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤)
    (le_rfl : (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K ≤
      (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp he)

theorem integralCoverPullback_inner {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (F G : IntegralQuotientL2 K) :
    inner ℂ (integralCoverPullback hHK hK F) (integralCoverPullback hHK hK G) =
      (H.relIndex K : ℂ) * inner ℂ F G := by
  let changeMeasure : IntegralQuotientL2 K →L[ℂ] Lp ℂ 2 ((H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) :=
    dominatedComplexL2 (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤) le_rfl
  change inner ℂ ((Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)) (changeMeasure F))
    ((Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)) (changeMeasure G)) = _
  rw [LinearIsometry.inner_map_map, L2.inner_def, L2.inner_def]
  have hF := dominatedComplexL2_ae (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤)
    (le_rfl : (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K ≤
      (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) F
  have hG := dominatedComplexL2_ae (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤)
    (le_rfl : (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K ≤
      (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) G
  calc
    _ = ∫ q, inner ℂ (F q) (G q) ∂((H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) := by
      apply integral_congr_ae
      filter_upwards [hF, hG] with q hqF hqG
      change inner ℂ (changeMeasure F q) (changeMeasure G q) = inner ℂ (F q) (G q)
      rw [show changeMeasure F q = F q from hqF, show changeMeasure G q = G q from hqG]
    _ = _ := by
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_natCast]

def integralCoverTrace {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] : IntegralQuotientL2 H →L[ℂ] IntegralQuotientL2 K :=
  ContinuousLinearMap.adjoint (integralCoverPullback hHK hK)

/-- Trace after pullback is multiplication by the finite covering degree. -/
theorem integralCoverTrace_pullback {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (F : IntegralQuotientL2 K) :
    integralCoverTrace hHK hK (integralCoverPullback hHK hK F) = (H.relIndex K : ℂ) • F := by
  apply ext_inner_left ℂ
  intro G
  rw [integralCoverTrace, ContinuousLinearMap.adjoint_inner_right,
    integralCoverPullback_inner, inner_smul_right]

/-- A coset labels one point in each fiber of an integral cover. -/
def integralCoverFiberPoint (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K)
    (w : HyperbolicSpace) : IntegralOrbitQuotient H :=
  Quotient.liftOn' q (fun r : K => integralOrbitProjection H (r⁻¹ • w)) (by
    intro a b hab
    have hh : b⁻¹ * a ∈ H.subgroupOf K := by
      have h := QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev, inv_inv] using (H.subgroupOf K).inv_mem h
    apply Quotient.sound
    refine ⟨⟨((b⁻¹ * a : K) : SL(2, O)), hh⟩, ?_⟩
    change (b⁻¹ * a) • (a⁻¹ • w) = b⁻¹ • w
    simp only [mul_smul, smul_inv_smul])

lemma integralCoverFiberPoint_mk (H K : Subgroup (SL(2, O))) (r : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K r w = integralOrbitProjection H (r⁻¹ • w) := rfl

lemma integralCoverFiberPoint_rep (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K)
    (w : HyperbolicSpace) : integralCoverFiberPoint H K q w =
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹ • w) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

lemma integralCoverFiberPoint_smul (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K)
    (k : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K (k • q) (k • w) = integralCoverFiberPoint H K q w := by
  induction q using Quotient.inductionOn with
  | _ r =>
    change integralOrbitProjection H ((k * r)⁻¹ • (k • w)) = integralOrbitProjection H (r⁻¹ • w)
    rw [mul_inv_rev, mul_smul, inv_smul_smul]

lemma integralCoverFiberPoint_measurable (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K) :
    Measurable (integralCoverFiberPoint H K q) := by
  rw [show integralCoverFiberPoint H K q = fun w =>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹ • w) from
    funext (integralCoverFiberPoint_rep H K q)]
  exact (measurable_integralOrbitProjection H).comp (measurable_const_smul _)

def integralCoverTraceLift (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H → ℂ) (w : HyperbolicSpace) : ℂ :=
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  ∑ q : IntegralCoverCosets H K, f (integralCoverFiberPoint H K q w)

lemma integralCoverTraceLift_smul (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H → ℂ) (k : K) (w : HyperbolicSpace) :
    integralCoverTraceLift H K f (k • w) = integralCoverTraceLift H K f w := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  unfold integralCoverTraceLift
  rw [← (MulAction.bijective k).sum_comp (fun q => f (integralCoverFiberPoint H K q (k • w)))]
  simp only [integralCoverFiberPoint_smul]

/-- The unnormalized fiber sum, descended to the base quotient. -/
def integralCoverTraceFunction (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H → ℂ) : IntegralOrbitQuotient K → ℂ :=
  Quotient.lift (integralCoverTraceLift H K f) (by
    rintro w u ⟨k, rfl⟩
    exact (integralCoverTraceLift_smul H K f k w).symm)

lemma integralCoverTraceFunction_projection (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H → ℂ) (w : HyperbolicSpace) :
    integralCoverTraceFunction H K f (integralOrbitProjection K w) = integralCoverTraceLift H K f w := rfl

lemma integralCoverTraceFunction_measurable (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H → ℂ) (hf : Measurable f) : Measurable (integralCoverTraceFunction H K f) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply measurable_from_quotient.mpr
  change Measurable (integralCoverTraceLift H K f)
  unfold integralCoverTraceLift
  exact Finset.measurable_sum Finset.univ (fun q _ => hf.comp (integralCoverFiberPoint_measurable H K q))

theorem integralCoverTraceFunction_integral_cusp_decay (H K : Subgroup (SL(2, O)))
    [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ) (C : ℝ)
    (hdec : ∀ M : SL(2, O), ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f (integralOrbitProjection H (integralComplexMatrix M • upperPoint z v hv))‖ ≤ C / v ^ 3)
    (M : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v) (hlarge : 1 < v) :
    ‖integralCoverTraceFunction H K f
      (integralOrbitProjection K (integralComplexMatrix M • upperPoint z v hv))‖ ≤
        (H.relIndex K : ℝ) * C / v ^ 3 := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  change ‖∑ q : IntegralCoverCosets H K,
    f (integralCoverFiberPoint H K q (integralComplexMatrix M • upperPoint z v hv))‖ ≤ _
  calc
    _ ≤ ∑ q : IntegralCoverCosets H K,
        ‖f (integralCoverFiberPoint H K q (integralComplexMatrix M • upperPoint z v hv))‖ := norm_sum_le _ _
    _ ≤ ∑ _q : IntegralCoverCosets H K, C / v ^ 3 := by
      apply Finset.sum_le_sum
      intro q _
      rw [integralCoverFiberPoint_rep, integralSubgroup_smul, ← mul_smul, ← map_mul]
      exact hdec _ z v hv hlarge
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : Fintype.card (IntegralCoverCosets H K) = H.relIndex K := by
        rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
      rw [hc]
      ring

lemma integralCoverDomain_projection_measurePreserving {H K : Subgroup (SL(2, O))}
    (hHK : H ≤ K) (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralOrbitProjection H)
      (hyperbolicVolume.restrict (integralCoverDomain H K)) (integralQuotientVolume H) :=
  ⟨measurable_integralOrbitProjection H, integralQuotientVolume_independent H (hHK.trans hK) _
    (integralCoverDomain_isFundamentalDomain hHK hK)⟩

lemma integralCoverSheet_measurePreserving (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K) :
    MeasurePreserving (fun w : HyperbolicSpace => integralCoverRep H K q • w)
      (hyperbolicVolume.restrict (integralCoverSheet H K q))
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) :=
  (measurePreserving_smul (integralCoverRep H K q) hyperbolicVolume).restrict_preimage
    (hyperbolicFundamentalSet_measurable K)

lemma integralCoverFiberPoint_rep_smul (H K : Subgroup (SL(2, O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K q (integralCoverRep H K q • w) = integralOrbitProjection H w := by
  rw [integralCoverFiberPoint_rep, inv_smul_smul]

lemma integralCoverFiber_integrable {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ)
    (hmeas : Measurable f) (hf : Integrable f (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    IntegrableOn (fun w => f (integralCoverFiberPoint H K q w)) (hyperbolicFundamentalSet K) hyperbolicVolume := by
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS : IntegrableOn (fun w => f (integralOrbitProjection H w)) (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  apply ((integralCoverSheet_measurePreserving H K q).integrable_comp
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable).mp
  simpa only [IntegrableOn, Function.comp_def, integralCoverFiberPoint_rep_smul] using hS

lemma integralCoverFiber_integral (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K)
    (f : IntegralOrbitQuotient H → ℂ) :
    (∫ w in hyperbolicFundamentalSet K, f (integralCoverFiberPoint H K q w) ∂hyperbolicVolume) =
      ∫ w in integralCoverSheet H K q, f (integralOrbitProjection H w) ∂hyperbolicVolume := by
  have hh := (measurePreserving_smul (integralCoverRep H K q) hyperbolicVolume).setIntegral_preimage_emb
    (measurableEmbedding_const_smul (integralCoverRep H K q))
    (fun w => f (integralCoverFiberPoint H K q w)) (hyperbolicFundamentalSet K)
  simpa only [integralCoverSheet, integralCoverFiberPoint_rep_smul] using hh.symm

/-- Integrating a fiber sum over the base equals integrating over the covering quotient. -/
theorem integralCoverTraceFunction_integral {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ)
    (hmeas : Measurable f) (hf : Integrable f (integralQuotientVolume H)) :
    (∫ q, integralCoverTraceFunction H K f q ∂integralQuotientVolume K) =
      ∫ q, f q ∂integralQuotientVolume H := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS (q : IntegralCoverCosets H K) :
      IntegrableOn (fun w => f (integralOrbitProjection H w)) (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  rw [integralQuotientVolume_integral K _
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable]
  change (∫ w in hyperbolicFundamentalSet K,
    ∑ q : IntegralCoverCosets H K, f (integralCoverFiberPoint H K q w) ∂hyperbolicVolume) = _
  rw [integral_finsetSum Finset.univ (fun q _ => integralCoverFiber_integrable hHK hK f hmeas hf q)]
  simp_rw [integralCoverFiber_integral H K]
  rw [← integral_iUnion_fintype (integralCoverSheet_measurable H K)
    (integralCoverSheet_pairwiseDisjoint H K hK) hS]
  change (∫ w in integralCoverDomain H K, f (integralOrbitProjection H w) ∂hyperbolicVolume) = _
  rw [← (integralCoverDomain_projection_measurePreserving hHK hK).map_eq]
  exact (integral_map (measurable_integralOrbitProjection H).aemeasurable hmeas.aestronglyMeasurable).symm

lemma integralCoverFiber_memLp {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ)
    (hmeas : Measurable f) (hf : MemLp f 2 (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    MemLp (fun w => f (integralCoverFiberPoint H K q w)) 2
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) := by
  have hD := hf.comp_measurePreserving (integralCoverDomain_projection_measurePreserving hHK hK)
  have hS := MemLp.mono_measure
    (Measure.restrict_mono_set hyperbolicVolume (Set.subset_iUnion (integralCoverSheet H K) q)) hD
  have hm := integralCoverSheet_measurePreserving H K q
  have hi := memLp_map_measure_iff (p := 2)
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  simpa only [Function.comp_def, integralCoverFiberPoint_rep_smul] using hS

theorem integralCoverTraceFunction_memLp {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ)
    (hmeas : Measurable f) (hf : MemLp f 2 (integralQuotientVolume H)) :
    MemLp (integralCoverTraceFunction H K f) 2 (integralQuotientVolume K) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hm := quotient_projection_measurePreserving K
  have hi := memLp_map_measure_iff (p := 2)
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  change MemLp (fun w => ∑ q : IntegralCoverCosets H K, f (integralCoverFiberPoint H K q w)) 2 _
  exact memLp_finsetSum Finset.univ (fun q _ => integralCoverFiber_memLp hHK hK f hmeas hf q)

lemma integralCoverMap_fiberPoint {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralCoverFiberPoint H K q w) = integralOrbitProjection K w := by
  rw [integralCoverFiberPoint_rep, integralCoverMap_projection, integralSubgroup_smul, integralOrbitProjection_eq]

lemma integralCoverTraceFunction_pairing {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    [H.IsFiniteRelIndex K] (F : IntegralOrbitQuotient K → ℂ) (f : IntegralOrbitQuotient H → ℂ)
    (q : IntegralOrbitQuotient K) :
    integralCoverTraceFunction H K (fun r => inner ℂ (F (integralCoverMap hHK r)) (f r)) q =
      inner ℂ (F q) (integralCoverTraceFunction H K f q) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑ r : IntegralCoverCosets H K, inner ℂ
      (F (integralCoverMap hHK (integralCoverFiberPoint H K r w))) (f (integralCoverFiberPoint H K r w))) =
      inner ℂ (F (integralOrbitProjection K w)) (∑ r : IntegralCoverCosets H K, f (integralCoverFiberPoint H K r w))
    simp only [integralCoverMap_fiberPoint, inner_sum]

/-- The Hilbert adjoint of pullback is represented by the actual finite fiber sum. -/
theorem integralCoverTrace_toLp_ae {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ)
    (hmeas : Measurable f) (hf : MemLp f 2 (integralQuotientVolume H)) :
    integralCoverTrace hHK hK (hf.toLp f) =ᵐ[integralQuotientVolume K] integralCoverTraceFunction H K f := by
  let htr := integralCoverTraceFunction_memLp hHK hK f hmeas hf
  let Tf : IntegralQuotientL2 K := htr.toLp (integralCoverTraceFunction H K f)
  have he : Tf = integralCoverTrace hHK hK (hf.toLp f) := by
    apply ext_inner_left ℂ
    intro F
    let pair : IntegralOrbitQuotient H → ℂ := fun r => inner ℂ (F (integralCoverMap hHK r)) (f r)
    have hpm : Measurable pair := by
      have hFm := (Lp.stronglyMeasurable F).measurable.comp (integralCoverMap_measurable hHK)
      have hm := hmeas.mul (continuous_star.measurable.comp hFm)
      change Measurable (fun r => f r * star (F (integralCoverMap hHK r))) at hm
      simpa only [pair, RCLike.inner_apply, starRingEnd_apply] using hm
    have hae : (fun r => inner ℂ (integralCoverPullback hHK hK F r) (hf.toLp f r))
        =ᵐ[integralQuotientVolume H] pair := by
      filter_upwards [integralCoverPullback_ae hHK hK F, hf.coeFn_toLp] with r hr hfR
      dsimp only [pair]
      rw [hr, hfR]
    have hpi : Integrable pair (integralQuotientVolume H) :=
      (L2.integrable_inner (integralCoverPullback hHK hK F) (hf.toLp f)).congr hae
    calc
      inner ℂ F Tf = ∫ q, inner ℂ (F q) (integralCoverTraceFunction H K f q) ∂integralQuotientVolume K := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [htr.coeFn_toLp] with q hq
        change inner ℂ (F q) (htr.toLp (integralCoverTraceFunction H K f) q) = _
        rw [hq]
      _ = ∫ q, integralCoverTraceFunction H K pair q ∂integralQuotientVolume K :=
        integral_congr_ae (Eventually.of_forall (fun q => (integralCoverTraceFunction_pairing hHK F f q).symm))
      _ = ∫ r, pair r ∂integralQuotientVolume H := integralCoverTraceFunction_integral hHK hK pair hpm hpi
      _ = inner ℂ (integralCoverPullback hHK hK F) (hf.toLp f) := (integral_congr_ae hae).symm
      _ = inner ℂ F (integralCoverTrace hHK hK (hf.toLp f)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  rw [← he]
  exact htr.coeFn_toLp

theorem integralCoverTrace_representative {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (G : IntegralQuotientL2 H)
    (f : IntegralOrbitQuotient H → ℂ) (hmeas : Measurable f) (hrep : G =ᵐ[integralQuotientVolume H] f) :
    integralCoverTrace hHK hK G =ᵐ[integralQuotientVolume K] integralCoverTraceFunction H K f := by
  have hf : MemLp f 2 (integralQuotientVolume H) := (memLp_congr_ae hrep).mp (Lp.memLp G)
  have he : G = hf.toLp f := Lp.ext (hrep.trans hf.coeFn_toLp.symm)
  rw [he]
  exact integralCoverTrace_toLp_ae hHK hK f hmeas hf

/-- Compatibility of a subgroup isomorphism with an actual hyperbolic isometry. -/
def IntegralCoverIntertwines {H J : Subgroup (SL(2, O))} (e : H ≃* J) (g : SL(2, ℂ)) : Prop :=
  ∀ h : H, g * integralComplexMatrix (h : SL(2, O)) = integralComplexMatrix (e h : SL(2, O)) * g

lemma integralCoverIntertwines_action {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (h : H) (w : HyperbolicSpace) :
    g • (h • w) = (e h) • (g • w) := by
  rw [integralSubgroup_smul, integralSubgroup_smul, ← mul_smul, he, mul_smul]

lemma integralCoverIntertwines_inverse {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) : IntegralCoverIntertwines e.symm g⁻¹ := by
  intro j
  have hh := he (e.symm j)
  rw [e.apply_symm_apply] at hh
  have hh' := congrArg (fun A : SL(2, ℂ) => g⁻¹ * A * g⁻¹) hh
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh'.symm

def integralConjugateMap {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) : IntegralOrbitQuotient H → IntegralOrbitQuotient J :=
  Quotient.map' (fun w => g • w) (by
    rintro w u ⟨h, rfl⟩
    exact ⟨e h, (integralCoverIntertwines_action e g he h w).symm⟩)

lemma integralConjugateMap_projection {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (w : HyperbolicSpace) :
    integralConjugateMap e g he (integralOrbitProjection H w) = integralOrbitProjection J (g • w) := rfl

lemma integralConjugateMap_measurable {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) : Measurable (integralConjugateMap e g he) :=
  measurable_from_quotient.mpr ((measurable_integralOrbitProjection J).comp (measurable_const_smul g))

lemma integralConjugateMap_continuous {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) : Continuous (integralConjugateMap e g he) :=
  (continuous_hyperbolic_action g).quotient_map' _

lemma integralConjugateMap_inverse {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (q : IntegralOrbitQuotient H) :
    integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) (integralConjugateMap e g he q) = q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection H (g⁻¹ • (g • w)) = integralOrbitProjection H w
    rw [inv_smul_smul]

def integralConjugateHomeomorph {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) : IntegralOrbitQuotient H ≃ₜ IntegralOrbitQuotient J where
  toFun := integralConjugateMap e g he
  invFun := integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
  left_inv := integralConjugateMap_inverse e g he
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ w =>
      change integralOrbitProjection J (g • (g⁻¹ • w)) = integralOrbitProjection J w
      rw [smul_inv_smul]
  continuous_toFun := integralConjugateMap_continuous e g he
  continuous_invFun := integralConjugateMap_continuous e.symm g⁻¹ _

lemma integralConjugate_fundamentalDomain {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (hH : H ≤ levelThree) :
    IsFundamentalDomain J ((fun w : HyperbolicSpace => g • w) '' hyperbolicFundamentalSet H) hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain H hH hyperbolicVolume).image_of_equiv
    (MulAction.toPerm g)
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm g).symm hyperbolicVolume hyperbolicVolume from
      (measurePreserving_smul g⁻¹ hyperbolicVolume).quasiMeasurePreserving) e.symm.toEquiv
  intro j w
  change g • (e.symm j • w) = j • (g • w)
  simpa only [e.apply_symm_apply] using integralCoverIntertwines_action e g he (e.symm j) w

theorem integralConjugateMap_measurePreserving {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (hH : H ≤ levelThree) (hJ : J ≤ levelThree) :
    MeasurePreserving (integralConjugateMap e g he) (integralQuotientVolume H) (integralQuotientVolume J) := by
  refine ⟨integralConjugateMap_measurable e g he, ?_⟩
  have hmap := (measurePreserving_smul g hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul g) (hyperbolicFundamentalSet H)
  change Measure.map (integralConjugateMap e g he)
    (Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))) = _
  rw [Measure.map_map (integralConjugateMap_measurable e g he) (measurable_integralOrbitProjection H)]
  change Measure.map ((integralOrbitProjection J) ∘ (fun w : HyperbolicSpace => g • w))
    (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)) = _
  rw [← Measure.map_map (measurable_integralOrbitProjection J) (measurable_const_smul g), hmap.map_eq]
  exact integralQuotientVolume_independent J hJ _ (integralConjugate_fundamentalDomain e g he hH)

def integralConjugatePullback {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (hH : H ≤ levelThree) (hJ : J ≤ levelThree) :
    IntegralQuotientL2 J →ₗᵢ[ℂ] IntegralQuotientL2 H :=
  Lp.compMeasurePreservingₗᵢ ℂ (integralConjugateMap e g he)
    (integralConjugateMap_measurePreserving e g he hH hJ)

lemma integralConjugatePullback_ae {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (hH : H ≤ levelThree) (hJ : J ≤ levelThree)
    (F : IntegralQuotientL2 J) : integralConjugatePullback e g he hH hJ F =ᵐ[integralQuotientVolume H]
      fun q => F (integralConjugateMap e g he q) :=
  Lp.coeFn_compMeasurePreserving F (integralConjugateMap_measurePreserving e g he hH hJ)

lemma integralConjugatePullback_inverse {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (hH : H ≤ levelThree) (hJ : J ≤ levelThree)
    (F : IntegralQuotientL2 H) :
    integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F) = F := by
  apply Lp.ext
  have hp := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp
    (integralConjugatePullback_ae e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F)
  filter_upwards [integralConjugatePullback_ae e g he hH hJ _, hp] with q hq hq'
  dsimp only [Function.comp_def] at hq'
  rw [hq, hq', integralConjugateMap_inverse]

lemma integralConjugatePullback_adjoint {H J : Subgroup (SL(2, O))} (e : H ≃* J)
    (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (hH : H ≤ levelThree) (hJ : J ≤ levelThree)
    (F : IntegralQuotientL2 H) :
    ContinuousLinearMap.adjoint (integralConjugatePullback e g he hH hJ).toContinuousLinearMap F =
      integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F := by
  apply ext_inner_left ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    _ = inner ℂ (integralConjugatePullback e g he hH hJ G)
        (integralConjugatePullback e g he hH hJ
          (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F)) := by
      rw [integralConjugatePullback_inverse]
      rfl
    _ = _ := LinearIsometry.inner_map_map _ _ _

/-- One correspondence leg: lift to a finite cover, then pull back by the conjugating isometry. -/
def kernelCoverLeg {H J : Subgroup (SL(2, O))} (hHK : H ≤ globalKubotaKernel)
    (hJK : J ≤ globalKubotaKernel) [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) :
    KernelQuotientL2 →L[ℂ] IntegralQuotientL2 H :=
  (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree)

theorem kernelCoverLeg_adjoint {H J : Subgroup (SL(2, O))} (hHK : H ≤ globalKubotaKernel)
    (hJK : J ≤ globalKubotaKernel) [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g) (D : IntegralQuotientL2 H) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) D =
      integralCoverTrace hJK globalKubotaKernel_le_levelThree
        (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
          (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) D) := by
  apply ext_inner_left ℂ
  intro F
  rw [ContinuousLinearMap.adjoint_inner_right, integralCoverTrace,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ ((integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree F)) D = _
  rw [← ContinuousLinearMap.adjoint_inner_right, integralConjugatePullback_adjoint]

def kernelCoverLegAdjointFunction {H J : Subgroup (SL(2, O))}
    [J.IsFiniteRelIndex globalKubotaKernel] (e : H ≃* J) (g : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (f : IntegralOrbitQuotient H → ℂ) : KernelQuotient → ℂ :=
  integralCoverTraceFunction J globalKubotaKernel
    (fun q => f (integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) q))

lemma kernelCoverLegAdjointFunction_measurable {H J : Subgroup (SL(2, O))}
    [J.IsFiniteRelIndex globalKubotaKernel] (e : H ≃* J) (g : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (f : IntegralOrbitQuotient H → ℂ) (hf : Measurable f) :
    Measurable (kernelCoverLegAdjointFunction e g he f) :=
  integralCoverTraceFunction_measurable J globalKubotaKernel _
    (hf.comp (integralConjugateMap_measurable _ _ _))

theorem kernelCoverLegAdjointFunction_represents {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel) [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)
    (D : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H → ℂ) (hf : Measurable f)
    (hrep : D =ᵐ[integralQuotientVolume H] f) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) D =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCoverLegAdjointFunction e g he f := by
  rw [kernelCoverLeg_adjoint]
  apply integralCoverTrace_representative hJK globalKubotaKernel_le_levelThree _ _
    (hf.comp (integralConjugateMap_measurable _ _ _))
  exact (integralConjugatePullback_ae e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
    (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) D).trans
      ((integralConjugateMap_measurePreserving e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
        (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hrep)

theorem kernelCoverLegAdjointFunction_cusp_decay {H J : Subgroup (SL(2, O))}
    [J.IsFiniteRelIndex globalKubotaKernel] (e : H ≃* J) (g : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (f : IntegralOrbitQuotient H → ℂ) (C : ℝ)
    (hdec : ∀ M : SL(2, O), ∀ z : ℂ, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ‖f (integralOrbitProjection H (g⁻¹ • (integralComplexMatrix M • upperPoint z v hv)))‖ ≤ C / v ^ 3)
    (M : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v) (hlarge : 1 < v) :
    ‖kernelCoverLegAdjointFunction e g he f
      (integralOrbitProjection globalKubotaKernel (integralComplexMatrix M • upperPoint z v hv))‖ ≤
        (J.relIndex globalKubotaKernel : ℝ) * C / v ^ 3 :=
  integralCoverTraceFunction_integral_cusp_decay J globalKubotaKernel _ C hdec M z v hv hlarge

/-- A primitive first column can be completed while preserving any given matrix congruence. -/
lemma primitiveColumn_congruent_completion {R : Type*} [CommRing R]
    (M : SL(2, R)) (a c r : R) (hac : IsCoprime a c)
    (ha : r ∣ a - M 0 0) (hc : r ∣ c - M 1 0) :
    ∃ N : SL(2, R), N 0 0 = a ∧ N 1 0 = c ∧ ∀ i j, r ∣ N i j - M i j := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hc
  obtain ⟨u, v, huv⟩ := hac
  let q := x * M 1 1 - M 0 1 * y
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.property
  have hdet0 : a * M 1 1 - M 0 1 * c = 1 + r * q := by
    dsimp only [q]
    linear_combination hM + M 1 1 * hx - M 0 1 * hy
  have hdet : a * (M 1 1 - r * q * u) - (M 0 1 + r * q * v) * c = 1 := by
    linear_combination hdet0 - r * q * huv
  let N : SL(2, R) := ⟨!![a, M 0 1 + r * q * v; c, M 1 1 - r * q * u], by
    rw [Matrix.det_fin_two]
    exact hdet⟩
  refine ⟨N, rfl, rfl, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨x, hx⟩
  · exact ⟨q * v, by change M 0 1 + r * q * v - M 0 1 = r * (q * v); ring⟩
  · exact ⟨y, hy⟩
  · exact ⟨-(q * u), by change M 1 1 - r * q * u - M 1 1 = r * -(q * u); ring⟩

lemma integralMatrix_congruent_levelThree (N M : SL(2, O))
    (h : ∀ i j, (3 : O) ∣ N i j - M i j) : N * M⁻¹ ∈ levelThree := by
  let reduction := Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(3 : O)}))
  have he : reduction N = reduction M := by
    apply Subtype.ext
    funext i j
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr (h i j))
  change reduction (N * M⁻¹) = 1
  rw [map_mul, map_inv, he, mul_inv_cancel]

lemma exists_congruent_cusp_completion (M : SL(2, O)) (a c : O) (hac : IsCoprime a c)
    (ha : (3 : O) ∣ a - M 0 0) (hc : (3 : O) ∣ c - M 1 0) :
    ∃ N : SL(2, O), N 0 0 = a ∧ N 1 0 = c ∧ N * M⁻¹ ∈ levelThree := by
  obtain ⟨N, hN0, hN1, hN⟩ := primitiveColumn_congruent_completion M a c 3 hac ha hc
  exact ⟨N, hN0, hN1, integralMatrix_congruent_levelThree N M hN⟩

lemma integralCoverFiberPoint_continuous (H K : Subgroup (SL(2, O))) (q : IntegralCoverCosets H K) :
    Continuous (integralCoverFiberPoint H K q) := by
  rw [show integralCoverFiberPoint H K q = fun w =>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹ • w) from
    funext (integralCoverFiberPoint_rep H K q)]
  exact (continuous_integralOrbitProjection H).comp
    (continuous_hyperbolic_action (integralComplexMatrix ((integralCoverRep H K q)⁻¹ : SL(2, O))))

lemma integralCoverMap_fiber {H K : Subgroup (SL(2, O))} (hHK : H ≤ K) (w : HyperbolicSpace) :
    (integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w} =
      Set.range (fun q : IntegralCoverCosets H K => integralCoverFiberPoint H K q w) := by
  ext u
  constructor
  · intro hu
    induction u using Quotient.inductionOn with
    | _ z =>
      have he : integralOrbitProjection K z = integralOrbitProjection K w := hu
      obtain ⟨k, hk⟩ := Quotient.exact he
      refine ⟨(k : IntegralCoverCosets H K), ?_⟩
      change integralCoverFiberPoint H K (k : IntegralCoverCosets H K) w = integralOrbitProjection H z
      rw [integralCoverFiberPoint_mk]
      congr 1
      rw [← hk]
      exact inv_smul_smul k z
  · rintro ⟨q, rfl⟩
    exact integralCoverMap_fiberPoint hHK q w

lemma integralCoverMap_preimage_image {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (S : Set (IntegralOrbitQuotient H)) :
    (integralOrbitProjection K) ⁻¹' (integralCoverMap hHK '' S) =
      ⋃ q : IntegralCoverCosets H K, (integralCoverFiberPoint H K q) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨u, hu, huw⟩
    have hh : u ∈ (integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w} := huw
    rw [integralCoverMap_fiber hHK w] at hh
    obtain ⟨q, rfl⟩ := hh
    exact Set.mem_iUnion.mpr ⟨q, hu⟩
  · intro hw
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hw
    exact ⟨integralCoverFiberPoint H K q w, hq, integralCoverMap_fiberPoint hHK q w⟩

theorem integralCoverMap_isClosedMap {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    [H.IsFiniteRelIndex K] : IsClosedMap (integralCoverMap hHK) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  intro S hS
  have hq : Topology.IsQuotientMap (integralOrbitProjection K) := isQuotientMap_quotient_mk'
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [integralCoverMap_preimage_image]
  exact isClosed_iUnion_of_finite (fun q => hS.preimage (integralCoverFiberPoint_continuous H K q))

theorem integralCoverMap_isProperMap {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    [H.IsFiniteRelIndex K] : IsProperMap (integralCoverMap hHK) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨integralCoverMap_continuous hHK, integralCoverMap_isClosedMap hHK, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change IsCompact ((integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w})
    rw [integralCoverMap_fiber hHK w]
    exact (Set.finite_range _).isCompact

lemma integralCoverMap_hasCompactSupport {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient K → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun q => f (integralCoverMap hHK q)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((integralCoverMap_isProperMap hHK).isCompact_preimage hf.isCompact)
  intro q hq
  exact subset_tsupport f hq

lemma integralCoverTraceFunction_hasCompactSupport {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (integralCoverTraceFunction H K f) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply HasCompactSupport.of_support_subset_isCompact (hf.isCompact.image (integralCoverMap_continuous hHK))
  intro q hq
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑ r : IntegralCoverCosets H K, f (integralCoverFiberPoint H K r w)) ≠ 0 at hq
    obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact ⟨integralCoverFiberPoint H K r w, subset_tsupport f hr, integralCoverMap_fiberPoint hHK r w⟩

section CorrespondenceTests
variable {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceFunction (f : KernelQuotient → ℂ) : KernelQuotient → ℂ :=
  integralCoverTraceFunction H globalKubotaKernel
    (fun q => f (integralCoverMap hJK (integralConjugateMap e g he q)))

omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_lift (f : KernelQuotient → ℂ) (w : HyperbolicSpace) :
    kernelCorrespondenceFunction hJK e g he f (integralOrbitProjection globalKubotaKernel w) =
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑ q : IntegralCoverCosets H globalKubotaKernel,
        f (integralOrbitProjection globalKubotaKernel
          ((g * integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹ : globalKubotaKernel) : SL(2, O))) • w)) := by
  letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change (∑ q : IntegralCoverCosets H globalKubotaKernel, f (integralCoverMap hJK
    (integralConjugateMap e g he (integralCoverFiberPoint H globalKubotaKernel q w)))) = _
  apply Finset.sum_congr rfl
  intro q _
  rw [integralCoverFiberPoint_rep, integralSubgroup_smul,
    integralConjugateMap_projection, integralCoverMap_projection, mul_smul]

include hHK in
lemma kernelCorrespondenceFunction_hasCompactSupport (f : KernelQuotient → ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (kernelCorrespondenceFunction hJK e g he f) := by
  apply integralCoverTraceFunction_hasCompactSupport hHK
  exact (integralCoverMap_hasCompactSupport hJK f hf).comp_homeomorph (integralConjugateHomeomorph e g he)

omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_contMDiff (f : KernelQuotient → ℂ)
    (hf : ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ, SpatialCoordinates) 𝓘(ℝ, ℂ) ∞ (kernelCorrespondenceFunction hJK e g he f) := by
  letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  apply kernel_contMDiff_of_lift
  simp_rw [kernelCorrespondenceFunction_lift]
  apply ContMDiff.sum
  intro q _
  exact (hf.comp kernelProjection_contMDiff).comp
    (hyperbolicAction_contMDiff (g * integralComplexMatrix
      (((integralCoverRep H globalKubotaKernel q)⁻¹ : globalKubotaKernel) : SL(2, O))))

def kernelCorrespondenceTest (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨kernelCorrespondenceFunction hJK e g he f.1,
    kernelCorrespondenceFunction_contMDiff hJK e g he f.1 f.2.1,
    kernelCorrespondenceFunction_hasCompactSupport hHK hJK e g he f.1 f.2.2⟩

end CorrespondenceTests

lemma integralCoverMap_quasiMeasurePreserving {H K : Subgroup (SL(2, O))}
    (hHK : H ≤ K) (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] :
    Measure.QuasiMeasurePreserving (integralCoverMap hHK) (integralQuotientVolume H) (integralQuotientVolume K) := by
  refine ⟨integralCoverMap_measurable hHK, ?_⟩
  rw [integralCoverMap_measure hHK hK]
  exact Measure.smul_absolutelyContinuous

lemma integralCoverTraceFunction_integrable {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H → ℂ)
    (hmeas : Measurable f) (hf : Integrable f (integralQuotientVolume H)) :
    Integrable (integralCoverTraceFunction H K f) (integralQuotientVolume K) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply ((quotient_projection_measurePreserving K).integrable_comp
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable).mp
  change Integrable (fun w => ∑ q : IntegralCoverCosets H K, f (integralCoverFiberPoint H K q w)) _
  exact integrable_finsetSum Finset.univ (fun q _ => integralCoverFiber_integrable hHK hK f hmeas hf q)

lemma integralCoverPullback_norm_le {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] (F : IntegralQuotientL2 K) :
    ‖integralCoverPullback hHK hK F‖ ≤ (H.relIndex K : ℝ) ^ ((1 : ℝ) / 2) * ‖F‖ := by
  change ‖Lp.compMeasurePreserving (integralCoverMap hHK) (integralCoverMap_measurePreserving hHK hK)
    (dominatedComplexL2 (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤) le_rfl F)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  simpa only [ENNReal.toReal_natCast] using dominatedComplexL2_norm_le
    (by simp : (H.relIndex K : ℝ≥0∞) ≠ ⊤)
    (le_rfl : (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K ≤
      (H.relIndex K : ℝ≥0∞) • integralQuotientVolume K) F

lemma integralCoverTrace_opNorm_le {H K : Subgroup (SL(2, O))} (hHK : H ≤ K)
    (hK : K ≤ levelThree) [H.IsFiniteRelIndex K] :
    ‖integralCoverTrace hHK hK‖ ≤ (H.relIndex K : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [integralCoverTrace, ContinuousLinearMap.adjoint.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (integralCoverPullback_norm_le hHK hK)

section CorrespondenceOperators
variable {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceL2 : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  (integralCoverTrace hHK globalKubotaKernel_le_levelThree).comp (kernelCoverLeg hHK hJK e g he)

lemma kernelCorrespondenceL2_representative (F : KernelQuotientL2) (f : KernelQuotient → ℂ)
    (hf : Measurable f) (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f) :
    kernelCorrespondenceL2 hHK hJK e g he F =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCorrespondenceFunction hJK e g he f := by
  have hcover := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  have hconj := (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hcover)
  exact integralCoverTrace_representative hHK globalKubotaKernel_le_levelThree _ _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

lemma kernelCorrespondenceTest_mass (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelCorrespondenceTest hHK hJK e g he f) =
      kernelCorrespondenceL2 hHK hJK e g he (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  exact (kernelSmoothTests_memLp (kernelCorrespondenceTest hHK hJK e g he f)).coeFn_toLp.trans
    (kernelCorrespondenceL2_representative hHK hJK e g he _ f.1
      f.2.1.continuous.measurable (kernelSmoothTests_memLp f).coeFn_toLp).symm

lemma kernelCorrespondenceL2_pairing (F G : KernelQuotientL2) :
    inner ℂ (kernelCorrespondenceL2 hHK hJK e g he F) G =
      inner ℂ F (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) G) := by
  change inner ℂ ((integralCoverTrace hHK globalKubotaKernel_le_levelThree)
    ((integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap
        (integralCoverPullback hJK globalKubotaKernel_le_levelThree F))) G = _
  rw [integralCoverTrace, ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.adjoint_inner_right, integralConjugatePullback_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

lemma kernelCorrespondenceL2_norm_le (F : KernelQuotientL2) :
    ‖kernelCorrespondenceL2 hHK hJK e g he F‖ ≤
      Real.sqrt ((H.relIndex globalKubotaKernel : ℝ) * (J.relIndex globalKubotaKernel : ℝ)) * ‖F‖ := by
  let C := integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  let P := integralCoverPullback hJK globalKubotaKernel_le_levelThree
  let Tr := integralCoverTrace hHK globalKubotaKernel_le_levelThree
  have hTr := integralCoverTrace_opNorm_le hHK globalKubotaKernel_le_levelThree
  have hP := integralCoverPullback_norm_le hJK globalKubotaKernel_le_levelThree F
  rw [← Real.sqrt_eq_rpow] at hTr hP
  change ‖Tr (C (P F))‖ ≤ _
  calc
    _ ≤ ‖Tr‖ * ‖C (P F)‖ := Tr.le_opNorm _
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel : ℝ) * ‖C (P F)‖ :=
      mul_le_mul_of_nonneg_right hTr (norm_nonneg _)
    _ = Real.sqrt (H.relIndex globalKubotaKernel : ℝ) * ‖P F‖ := by rw [C.norm_map]
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel : ℝ) *
        (Real.sqrt (J.relIndex globalKubotaKernel : ℝ) * ‖F‖) :=
      mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring

include hHK in
lemma kernelCorrespondenceFunction_integrable (f : KernelQuotient → ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    Integrable (kernelCorrespondenceFunction hJK e g he f) (integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c := (J.relIndex globalKubotaKernel : ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  exact integralCoverTraceFunction_integrable hHK globalKubotaKernel_le_levelThree _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

include hHK in
lemma kernelCorrespondenceFunction_integral (f : KernelQuotient → ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    (∫ q, kernelCorrespondenceFunction hJK e g he f q ∂integralQuotientVolume globalKubotaKernel) =
      (J.relIndex globalKubotaKernel : ℂ) * ∫ q, f q ∂integralQuotientVolume globalKubotaKernel := by
  have hcover := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c := (J.relIndex globalKubotaKernel : ℝ≥0∞)) (by simp))
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  have hconj := hm.integrable_comp_of_integrable hcover
  calc
    _ = ∫ q, f (integralCoverMap hJK (integralConjugateMap e g he q)) ∂integralQuotientVolume H :=
      integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
        ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj
    _ = ∫ q, f (integralCoverMap hJK q) ∂integralQuotientVolume J := by
      have hh := integral_map (μ := integralQuotientVolume H) hm.measurable.aemeasurable
        (hf.comp (integralCoverMap_measurable hJK)).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = ∫ q, f q ∂Measure.map (integralCoverMap hJK) (integralQuotientVolume J) :=
      (integral_map (integralCoverMap_measurable hJK).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [integralCoverMap_measure hJK globalKubotaKernel_le_levelThree, integral_smul_measure]
      simp only [ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_natCast]

end CorrespondenceOperators

/-- Hyperbolic energy of a complex field in upper-half-space coordinates. -/
def coverEnergyDensity (F : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : ℝ :=
  euclideanScalarDirichletDensity (fun x => (F x).re) p +
    euclideanScalarDirichletDensity (fun x => (F x).im) p

def coverGradientAt (F : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (p 2 : ℂ) * fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))

lemma coverGradientAt_norm_sq (F : EuclideanSpatial → ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) : ‖coverGradientAt F p‖ ^ 2 = coverEnergyDensity F p := by
  have hr := (Complex.reCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => (F x).re) p = _ at hr
  change fderiv ℝ (fun x => (F x).im) p = _ at hi
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  rw [hr, hi, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual, ← mul_add, ← Finset.sum_add_distrib,
    PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin 3, ‖(p 2 : ℂ) * fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖ ^ 2) = _
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ‖fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖ ^ 2 =
    (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).re ^ 2 +
      (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).im ^ 2
  simpa only [Complex.normSq_apply, pow_two] using
    (Complex.normSq_eq_norm_sq (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))).symm

lemma coverEnergyDensity_comp (g : SL(2, ℂ)) (F : EuclideanSpatial → ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    coverEnergyDensity (F ∘ euclideanAction g) p = coverEnergyDensity F (euclideanAction g p) :=
  congrArg₂ (fun x y : ℝ => x + y)
    (hyperbolic_cotangent_energy_comp g (fun p => (F p).re) p hp (Complex.reCLM.differentiableAt.comp _ hF))
    (hyperbolic_cotangent_energy_comp g (fun p => (F p).im) p hp (Complex.imCLM.differentiableAt.comp _ hF))

lemma coverGradientAt_sum {ι : Type*} (s : Finset ι) (F : ι → EuclideanSpatial → ℂ)
    (p : EuclideanSpatial) (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) :
    coverGradientAt (fun x => ∑ i ∈ s, F i x) p = ∑ i ∈ s, coverGradientAt (F i) p := by
  apply (WithLp.equiv 2 (Fin 3 → ℂ)).injective
  funext j
  simp only [coverGradientAt, fderiv_fun_sum hF, _root_.sum_apply,
    WithLp.equiv_apply, Finset.mul_sum, WithLp.ofLp_sum, Finset.sum_apply]

lemma cover_norm_sum_sq_le_card {ι E : Type*} [NormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr (norm_sum_le _ _)
    _ ≤ _ := by
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)

lemma coverEnergyDensity_sum_le {ι : Type*} (s : Finset ι) (F : ι → EuclideanSpatial → ℂ)
    (p : EuclideanSpatial) (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) :
    coverEnergyDensity (fun x => ∑ i ∈ s, F i x) p ≤ (s.card : ℝ) * ∑ i ∈ s, coverEnergyDensity (F i) p := by
  rw [← coverGradientAt_norm_sq _ _ (DifferentiableAt.fun_sum hF), coverGradientAt_sum s F p hF]
  calc
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖coverGradientAt (F i) p‖ ^ 2 :=
      cover_norm_sum_sq_le_card s (fun i => coverGradientAt (F i) p)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact coverGradientAt_norm_sq (F i) p (hF i hi)

lemma coverGradientAt_add (F G : EuclideanSpatial → ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F + G) p = coverGradientAt F p + coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3 → ℂ)).injective
  funext j
  simp only [coverGradientAt, fderiv_add hF hG, WithLp.equiv_apply, WithLp.ofLp_add,
    Pi.add_apply, _root_.add_apply, mul_add]

lemma coverGradientAt_sub (F G : EuclideanSpatial → ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F - G) p = coverGradientAt F p - coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3 → ℂ)).injective
  funext j
  simp only [coverGradientAt, fderiv_sub hF hG, WithLp.equiv_apply, WithLp.ofLp_sub,
    Pi.sub_apply, _root_.sub_apply, mul_sub]

lemma coverGradientAt_smul (c : ℂ) (F : EuclideanSpatial → ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) : coverGradientAt (c • F) p = c • coverGradientAt F p := by
  apply (WithLp.equiv 2 (Fin 3 → ℂ)).injective
  funext j
  simp only [coverGradientAt, fderiv_const_smul hF, WithLp.equiv_apply, WithLp.ofLp_smul,
    Pi.smul_apply, _root_.smul_apply, smul_eq_mul, mul_left_comm]

def coverDirichletPair (F G : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : ℂ :=
  inner ℂ (coverGradientAt F p) (coverGradientAt G p)

lemma coverDirichletPair_polarization (F G : EuclideanSpatial → ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverDirichletPair F G p = ((coverEnergyDensity (F + G) p : ℂ) - (coverEnergyDensity (F - G) p : ℂ) +
      ((coverEnergyDensity (F - Complex.I • G) p : ℂ) - (coverEnergyDensity (F + Complex.I • G) p : ℂ)) * Complex.I) / 4 := by
  unfold coverDirichletPair
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [RCLike.I_to_complex]
  rw [← coverGradientAt_add F G p hF hG, ← coverGradientAt_sub F G p hF hG,
    ← coverGradientAt_smul Complex.I G p hG,
    ← coverGradientAt_sub F (Complex.I • G) p hF (hG.const_smul _),
    ← coverGradientAt_add F (Complex.I • G) p hF (hG.const_smul _)]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    coverGradientAt_norm_sq _ _ (hF.add hG), coverGradientAt_norm_sq _ _ (hF.sub hG),
    coverGradientAt_norm_sq _ _ (hF.sub (hG.const_smul _)), coverGradientAt_norm_sq _ _ (hF.add (hG.const_smul _))]

/-- Polarization transfers isometry invariance of scalar energy to the complex Dirichlet pairing. -/
lemma coverDirichletPair_comp (g : SL(2, ℂ)) (F G : EuclideanSpatial → ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p)) (hG : DifferentiableAt ℝ G (euclideanAction g p)) :
    coverDirichletPair (F ∘ euclideanAction g) (G ∘ euclideanAction g) p =
      coverDirichletPair F G (euclideanAction g p) := by
  obtain ⟨der, hder, _⟩ := hyperbolicDifferentialIsometry g p hp
  rw [coverDirichletPair_polarization _ _ p (hF.comp p hder.differentiableAt) (hG.comp p hder.differentiableAt),
    coverDirichletPair_polarization F G _ hF hG]
  have ha : (F ∘ euclideanAction g) + (G ∘ euclideanAction g) = (F + G) ∘ euclideanAction g := rfl
  have hs : (F ∘ euclideanAction g) - (G ∘ euclideanAction g) = (F - G) ∘ euclideanAction g := rfl
  have hai : (F ∘ euclideanAction g) + Complex.I • (G ∘ euclideanAction g) = (F + Complex.I • G) ∘ euclideanAction g := rfl
  have hsi : (F ∘ euclideanAction g) - Complex.I • (G ∘ euclideanAction g) = (F - Complex.I • G) ∘ euclideanAction g := rfl
  rw [ha, hs, hai, hsi, coverEnergyDensity_comp g _ p hp (hF.add hG),
    coverEnergyDensity_comp g _ p hp (hF.sub hG), coverEnergyDensity_comp g _ p hp (hF.add (hG.const_smul _)),
    coverEnergyDensity_comp g _ p hp (hF.sub (hG.const_smul _))]

lemma coverDirichletPair_sum_right {ι : Type*} (s : Finset ι) (F : EuclideanSpatial → ℂ)
    (G : ι → EuclideanSpatial → ℂ) (p : EuclideanSpatial) (hG : ∀ i ∈ s, DifferentiableAt ℝ (G i) p) :
    coverDirichletPair F (fun x => ∑ i ∈ s, G i x) p = ∑ i ∈ s, coverDirichletPair F (G i) p := by
  simp only [coverDirichletPair, coverGradientAt_sum s G p hG, inner_sum]

lemma coverDirichletPair_norm_le (F G : EuclideanSpatial → ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    ‖coverDirichletPair F G p‖ ≤ (coverEnergyDensity F p + coverEnergyDensity G p) / 2 := by
  have hh := norm_inner_le_norm (𝕜 := ℂ) (coverGradientAt F p) (coverGradientAt G p)
  have hs := sq_nonneg (‖coverGradientAt F p‖ - ‖coverGradientAt G p‖)
  rw [← coverGradientAt_norm_sq F p hF, ← coverGradientAt_norm_sq G p hG]
  exact le_trans hh (by nlinarith only [hs])

lemma kernelDirichletPairDensity_eq_cover (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f h (integralOrbitProjection globalKubotaKernel w) =
      coverDirichletPair (kernelTestField f) (kernelTestField h) (hyperbolicEuclideanCoordinates w) := by
  rw [kernelDirichletPairDensity_coordinate]
  rfl

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
