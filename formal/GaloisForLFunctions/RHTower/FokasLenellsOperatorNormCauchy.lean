import GaloisForLFunctions.RHTower.FokasLenellsOperatorNormRegularity

/-!
# Operator-norm regularity of the full actual jump and Cauchy operator

The time-independent diagonal product separates from two bounded linear
channel insertions. Extracting the upper channel proves that the full jump
has exactly the same operator-norm differentiability gate. The Cauchy
projection then transports derivatives on the whole compatibility locus.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private def lowerChannelLift : (SoninL2 →L[ℂ] SoninL2) →L[ℂ] (Boundary →L[ℂ] Boundary) :=
  -((ContinuousLinearMap.compL ℂ Boundary SoninL2 Boundary (ContinuousLinearMap.inl ℂ SoninL2 SoninL2)).comp
    ((ContinuousLinearMap.compL ℂ Boundary SoninL2 SoninL2).flip (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)))

private def upperChannelLift : (SoninL2 →L[ℂ] SoninL2) →L[ℂ] (Boundary →L[ℂ] Boundary) :=
  (ContinuousLinearMap.compL ℂ Boundary SoninL2 Boundary (ContinuousLinearMap.inr ℂ SoninL2 SoninL2)).comp
    ((ContinuousLinearMap.compL ℂ Boundary SoninL2 SoninL2).flip (ContinuousLinearMap.fst ℂ SoninL2 SoninL2))

private def upperChannelExtract : (Boundary →L[ℂ] Boundary) →L[ℂ] (SoninL2 →L[ℂ] SoninL2) :=
  (ContinuousLinearMap.compL ℂ SoninL2 Boundary SoninL2 (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).comp
    ((ContinuousLinearMap.compL ℂ SoninL2 Boundary Boundary).flip (ContinuousLinearMap.inl ℂ SoninL2 SoninL2))

private theorem actual_jump_channel_decomposition (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    directJumpPerturbation q t x = lowerChannelLift (directMultiplier q t x false)+upperChannelLift (directMultiplier q t x true)-
      (ContinuousLinearMap.inr ℂ SoninL2 SoninL2).comp
        ((directMultiplier q 0 0 false).comp ((directMultiplier q 0 0 true).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · change -directMultiplier q t x false u.2 = -directMultiplier q t x false u.2+0-0
    abel
  · change directMultiplier q t x true u.1-directMultiplier q t x false (directMultiplier q t x true u.2) =
      -0+directMultiplier q t x true u.1-directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2)
    rw [directMultiplier_product_invariant q t x 0 0]
    abel

private theorem actual_jump_derivative_channels (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    lowerChannelLift (directTimeMultiplier q t x false)+upperChannelLift (directTimeMultiplier q t x true) =
      directJumpTimeOperator q t x := by
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext
  · change -directTimeMultiplier q t x false u.2+0 = -directTimeMultiplier q t x false u.2
    exact add_zero _
  · change -0+directTimeMultiplier q t x true u.1 = directTimeMultiplier q t x true u.1
    simp only [neg_zero,zero_add]

private theorem actual_upper_channel_extract (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    upperChannelExtract (directJumpPerturbation q t x) = directMultiplier q t x true := by
  apply ContinuousLinearMap.ext
  intro u
  change directMultiplier q t x true u-directMultiplier q t x false (directMultiplier q t x true 0) = _
  rw [map_zero,map_zero,sub_zero]

private theorem jump_operator_derivative_of_compatibility (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (hm : compatibilityMoment (globalSmallScatteringPotential q) = 0) :
    HasDerivAt (fun s => directJumpPerturbation q s x) (directJumpTimeOperator q t x) t := by
  have h0 := (lowerChannelLift.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (directMultiplier_lower_operator_hasDerivAt q t x)
  have h1 := (upperChannelLift.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    ((directMultiplier_upper_operator_hasDerivAt_iff q t x).2 hm)
  have hd := (h0.fun_add h1).sub_const ((ContinuousLinearMap.inr ℂ SoninL2 SoninL2).comp
    ((directMultiplier q 0 0 false).comp ((directMultiplier q 0 0 true).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2))))
  change HasDerivAt (fun s => lowerChannelLift (directMultiplier q s x false)+upperChannelLift (directMultiplier q s x true)-_)
    (lowerChannelLift (directTimeMultiplier q t x false)+upperChannelLift (directTimeMultiplier q t x true)) t at hd
  simpa only [← actual_jump_channel_decomposition,actual_jump_derivative_channels] using hd

private theorem jump_operator_contDiff_of_compatibility (q : SchwartzMap ℝ ℂ) (x : ℝ)
    (hm : compatibilityMoment (globalSmallScatteringPotential q) = 0) :
    ContDiff ℝ 1 (fun t => directJumpPerturbation q t x) := by
  have h0 := (lowerChannelLift.restrictScalars ℝ).contDiff.comp (directMultiplier_lower_operator_contDiff q x)
  have h1 := (upperChannelLift.restrictScalars ℝ).contDiff.comp ((directMultiplier_upper_operator_contDiff_iff q x).2 hm)
  have hd := (h0.add h1).sub (contDiff_const (c := (ContinuousLinearMap.inr ℂ SoninL2 SoninL2).comp
    ((directMultiplier q 0 0 false).comp ((directMultiplier q 0 0 true).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)))))
  change ContDiff ℝ 1 (fun t => lowerChannelLift (directMultiplier q t x false)+upperChannelLift (directMultiplier q t x true)-_) at hd
  simpa only [← actual_jump_channel_decomposition] using hd

/-- The full actual matrix-jump operator has an operator-norm derivative exactly at compatibility. -/
theorem directJumpPerturbation_operator_differentiableAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => directJumpPerturbation q s x) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · intro h
    have he := (upperChannelExtract.restrictScalars ℝ).differentiableAt.comp t h
    change DifferentiableAt ℝ (fun s => upperChannelExtract (directJumpPerturbation q s x)) t at he
    simp only [actual_upper_channel_extract] at he
    exact (directMultiplier_upper_operator_differentiableAt_iff q t x).1 he
  · intro hm
    exact (jump_operator_derivative_of_compatibility q t x hm).differentiableAt

theorem directJumpPerturbation_operator_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directJumpPerturbation q s x) (directJumpTimeOperator q t x) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 :=
  ⟨fun h => (directJumpPerturbation_operator_differentiableAt_iff q t x).1 h.differentiableAt,
    jump_operator_derivative_of_compatibility q t x⟩

/-- The entire jump is globally C1 in operator norm exactly on the full compatibility locus. -/
theorem directJumpPerturbation_operator_contDiff_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => directJumpPerturbation q t x) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 :=
  ⟨fun h => (directJumpPerturbation_operator_differentiableAt_iff q 0 x).1 ((h.differentiable (by simp)) 0),
    jump_operator_contDiff_of_compatibility q x⟩

private theorem cauchy_operator_derivative_of_compatibility (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (hm : compatibilityMoment (globalSmallScatteringPotential q) = 0) :
    HasDerivAt (fun s => directCauchyOperator q s x) (directCauchyTimeOperator q t x) t := by
  have h := ((ContinuousLinearMap.compL ℂ Boundary Boundary Boundary boundaryCauchy).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (jump_operator_derivative_of_compatibility q t x hm)
  exact h

private theorem cauchy_operator_contDiff_of_compatibility (q : SchwartzMap ℝ ℂ) (x : ℝ)
    (hm : compatibilityMoment (globalSmallScatteringPotential q) = 0) :
    ContDiff ℝ 1 (fun t => directCauchyOperator q t x) := by
  have h := ((ContinuousLinearMap.compL ℂ Boundary Boundary Boundary boundaryCauchy).restrictScalars ℝ).contDiff.comp
    (jump_operator_contDiff_of_compatibility q x hm)
  exact h

/-- Both the full jump and its actual Cauchy projection differentiate in operator norm exactly at compatibility. -/
theorem directJumpCauchy_operator_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    (HasDerivAt (fun s => directJumpPerturbation q s x) (directJumpTimeOperator q t x) t ∧
      HasDerivAt (fun s => directCauchyOperator q s x) (directCauchyTimeOperator q t x) t) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · exact fun h => (directJumpPerturbation_operator_hasDerivAt_iff q t x).1 h.1
  · intro hm
    exact ⟨jump_operator_derivative_of_compatibility q t x hm,cauchy_operator_derivative_of_compatibility q t x hm⟩

/-- The same exact condition gives global C1 operator-norm regularity of both actual jump and Cauchy families. -/
theorem directJumpCauchy_operator_contDiff_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (ContDiff ℝ 1 (fun t => directJumpPerturbation q t x) ∧
      ContDiff ℝ 1 (fun t => directCauchyOperator q t x)) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · exact fun h => (directJumpPerturbation_operator_contDiff_iff q x).1 h.1
  · intro hm
    exact ⟨jump_operator_contDiff_of_compatibility q x hm,cauchy_operator_contDiff_of_compatibility q x hm⟩

theorem directCauchyOperator_oddInitialPart_operator_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directCauchyOperator (oddInitialPart q) s x) (directCauchyTimeOperator (oddInitialPart q) t x) t :=
  cauchy_operator_derivative_of_compatibility _ t x (compatibilityMoment_globalSmall_oddInitialPart q)

theorem directCauchyOperator_oddInitialPart_operator_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => directCauchyOperator (oddInitialPart q) t x) :=
  cauchy_operator_contDiff_of_compatibility _ x (compatibilityMoment_globalSmall_oddInitialPart q)

/-- The Gaussian obstruction survives in the full actual matrix-jump operator. -/
theorem directJumpPerturbation_Gaussian_not_operator_differentiableAt (a t x : ℝ) :
    ¬ DifferentiableAt ℝ (fun s => directJumpPerturbation (compatibilityGaussian a) s x) t := by
  rw [directJumpPerturbation_operator_differentiableAt_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

end
end RHTower.FokasLenells
