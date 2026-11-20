import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator
import GaloisForLFunctions.HTGeometry.WeightedOrbitInduction
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# Ordinary and essential norms of the zero displacements

On the Hilbert space of individual ξ-divisor copies, multiply the
coordinate at ρ by the positive part of Re ρ − σ. The operator norm
reads the largest zero abscissa, while its distance to compact operators
reads the asymptotic abscissa. Raising σ to the latter gives an explicit
best compact approximation to the operator at the critical line.
-/

noncomputable section
open Set Filter RHTower RHTower.BacklundConverse RHTower.DeBruijn RHTower.LindelofSparse
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ZeroConfigurationGeometry

private def depthCoeff (σ : ℝ) (q : XiZeroCopy) : ℂ := (max ((q.1:ℂ).re-σ) 0 : ℝ)

private theorem norm_depth (σ : ℝ) (q : XiZeroCopy) :
    ‖depthCoeff σ q‖ = max ((q.1:ℂ).re-σ) 0 := by
  rw [depthCoeff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]

private theorem depth_bdd (σ : ℝ) : BddAbove (range fun q => ‖depthCoeff σ q‖) := by
  refine ⟨max (1-σ) 0,?_⟩
  rintro _ ⟨q,rfl⟩
  change ‖depthCoeff σ q‖ ≤ max (1-σ) 0
  rw [norm_depth]
  exact max_le_max_right 0 (sub_le_sub_right (xi_divisor_support_re_mem_open_unit q.1).2.le σ)

private abbrev scalarIdentity := ContinuousLinearMap.id ℂ ℂ
private abbrev trivialFrame (_ : XiZeroCopy) := LinearIsometryEquiv.refl ℂ ℂ

/-- Multiplication by the excess over a prescribed vertical line, with
one coordinate per divisor copy. -/
def zeroDepthOperator (σ : ℝ) := weightedInduction (depthCoeff σ) scalarIdentity
  trivialFrame trivialFrame (depth_bdd σ)

private theorem depth_sup {σ : ℝ} (hσ : 1/2 ≤ σ) :
    ampSup (depthCoeff σ) = max (zetaZeroAbscissa-σ) 0 := by
  refine le_antisymm (ampSup_le fun q => ?_) (max_le ?_ (ampSup_nonneg (depth_bdd σ)))
  · rw [norm_depth]
    exact max_le_max_right 0 (sub_le_sub_right
      (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)) σ)
  · apply sub_le_iff_le_add.mpr
    apply zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le
    · linarith only [hσ,ampSup_nonneg (depth_bdd σ)]
    · intro q
      have h := le_ampSup (depth_bdd σ) q
      rw [norm_depth] at h
      linarith only [(le_max_left _ _).trans h]

private theorem depth_tail {σ : ℝ} (hσ : 1/2 ≤ σ) :
    tailSup (depthCoeff σ) = max (zetaAsymptoticAbscissa-σ) 0 := by
  classical
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (max_le ?_ (tailSup_nonneg (depth_bdd σ)))
  · obtain ⟨t,ht,ht'⟩ := exists_lt_of_csInf_lt zetaAsymptoticAbscissaSet_nonempty
      (show zetaAsymptoticAbscissa < zetaAsymptoticAbscissa+ε by linarith only [hε])
    let F := ht.2.toFinset
    refine (tailSup_le_ampSup_tailAmp (depth_bdd σ) F).trans (ampSup_le fun q => ?_)
    by_cases hq : q ∈ F
    · rw [tailAmp,if_pos hq,norm_zero]
      exact add_nonneg (le_max_right _ _) hε.le
    · have hr : (q.1:ℂ).re ≤ t := le_of_not_gt fun h => hq (ht.2.mem_toFinset.mpr h)
      rw [tailAmp,if_neg hq,norm_depth]
      exact max_le (by linarith only [hr,ht',le_max_left (zetaAsymptoticAbscissa-σ) 0])
        (add_nonneg (le_max_right _ _) hε.le)
  · apply le_ciInf
    intro F
    let b := ampSup (tailAmp F (depthCoeff σ))
    have hb : 0 ≤ b := ampSup_nonneg (bddAbove_tailAmp (depth_bdd σ) F)
    have ht : b+σ ∈ zetaAsymptoticAbscissaSet := by
      refine ⟨by linarith only [hb,hσ],F.finite_toSet.subset ?_⟩
      intro q hq
      change b+σ < (q.1:ℂ).re at hq
      by_contra h
      change q ∉ F at h
      have H := le_ampSup (bddAbove_tailAmp (depth_bdd σ) F) q
      rw [tailAmp,if_neg h,norm_depth] at H
      change max ((q.1:ℂ).re-σ) 0 ≤ b at H
      linarith only [hq,(le_max_left _ _).trans H]
    exact sub_le_iff_le_add.mpr (csInf_le bddBelow_zetaAsymptoticAbscissaSet ht)

/-- The two norms read the full and asymptotic abscissas on the same
thresholded operator, for every line at or right of the critical line. -/
theorem zero_depth_operator_norms {σ : ℝ} (hσ : 1/2 ≤ σ) :
    ‖zeroDepthOperator σ‖ = max (zetaZeroAbscissa-σ) 0 ∧
    rectEssentialNorm (zeroDepthOperator σ) = max (zetaAsymptoticAbscissa-σ) 0 := by
  classical
  have hc : IsCompactOperator scalarIdentity := isCompactOperator_id
  simp only [zeroDepthOperator,norm_weightedInduction,rectEssentialNorm_weightedInduction _ _ _ _ _ hc,
    ContinuousLinearMap.norm_id,mul_one,depth_sup hσ,depth_tail hσ,and_self]

/-- Compactness starts exactly at the asymptotic abscissa, including
the endpoint where infinitely many positive entries may remain. -/
theorem compact_zero_depth_iff {σ : ℝ} (hσ : 1/2 ≤ σ) :
    IsCompactOperator (zeroDepthOperator σ) ↔ zetaAsymptoticAbscissa ≤ σ := by
  constructor
  · intro h
    have hz := rectEssentialNorm_eq_zero_of_isCompactOperator h
    rw [(zero_depth_operator_norms hσ).2] at hz
    linarith only [hz,le_max_left (zetaAsymptoticAbscissa-σ) 0]
  · intro h
    apply isCompactOperator_of_rectEssentialNorm_eq_zero
    rw [(zero_depth_operator_norms hσ).2,max_eq_right (sub_nonpos.mpr h)]

/-- The abscissa law says that compact perturbations cannot lower the
norm at the critical line. The approach law says the operator is compact. -/
theorem abscissa_laws_of_zero_depth_operator :
    (AsymptoticAbscissaLaw ↔ rectEssentialNorm (zeroDepthOperator (1/2)) = ‖zeroDepthOperator (1/2)‖) ∧
    (ZerosApproachLine ↔ IsCompactOperator (zeroDepthOperator (1/2))) := by
  obtain ⟨h,h'⟩ := zero_depth_operator_norms (σ:=1/2) le_rfl
  rw [asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa,
    zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half,compact_zero_depth_iff le_rfl,h,h',
    max_eq_left (sub_nonneg.mpr half_le_zetaZeroAbscissa),
    max_eq_left (sub_nonneg.mpr half_le_zetaAsymptoticAbscissa)]
  exact ⟨sub_left_inj.symm,⟨fun he => he.le,fun hle => le_antisymm hle half_le_zetaAsymptoticAbscissa⟩⟩

private theorem depth_difference {σ τ : ℝ} (h : σ ≤ τ) :
    ‖zeroDepthOperator σ-zeroDepthOperator τ‖ ≤ τ-σ := by
  classical
  let a (q : XiZeroCopy) := depthCoeff σ q-depthCoeff τ q
  have H (q : XiZeroCopy) : ‖a q‖ ≤ τ-σ := by
    change ‖((max ((q.1:ℂ).re-σ) 0:ℝ):ℂ)-(max ((q.1:ℂ).re-τ) 0:ℝ)‖ ≤ _
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (max_le_max_right 0 (sub_le_sub_left h _)))]
    rcases le_or_gt (q.1:ℂ).re σ with hs | hs
    · rw [max_eq_right (sub_nonpos.mpr hs),max_eq_right (sub_nonpos.mpr (hs.trans h)),sub_self]
      exact sub_nonneg.mpr h
    · rw [max_eq_left (sub_nonneg.mpr hs.le)]
      linarith only [le_max_left ((q.1:ℂ).re-τ) 0]
  have ha : BddAbove (range fun q => ‖a q‖) := ⟨τ-σ,by rintro _ ⟨q,rfl⟩; exact H q⟩
  let S := weightedInduction a scalarIdentity trivialFrame trivialFrame ha
  have he : zeroDepthOperator σ = S+zeroDepthOperator τ :=
    weightedInduction_add _ _ _ (fun q => (sub_add_cancel (depthCoeff σ q) (depthCoeff τ q)).symm)
      ha (depth_bdd τ) (depth_bdd σ)
  rw [he,add_sub_cancel_right]
  simpa only [S,norm_weightedInduction,ContinuousLinearMap.norm_id,mul_one] using
    (show ampSup a ≤ τ-σ from ampSup_le H)

/-- Thresholding at the asymptotic abscissa attains the distance to
compact operators, even if the threshold itself is approached from above. -/
theorem optimal_compact_zero_depth_approximation :
    IsCompactOperator (zeroDepthOperator zetaAsymptoticAbscissa) ∧
    ‖zeroDepthOperator (1/2)-zeroDepthOperator zetaAsymptoticAbscissa‖ =
      rectEssentialNorm (zeroDepthOperator (1/2)) := by
  have hc := (compact_zero_depth_iff half_le_zetaAsymptoticAbscissa).mpr le_rfl
  refine ⟨hc,le_antisymm ?_ ?_⟩
  · rw [(zero_depth_operator_norms (σ:=1/2) le_rfl).2,max_eq_left (sub_nonneg.mpr half_le_zetaAsymptoticAbscissa)]
    exact depth_difference half_le_zetaAsymptoticAbscissa
  · exact rectEssentialNorm_le _ _ hc


end GaloisForLFunctions.ZeroConfigurationGeometry
