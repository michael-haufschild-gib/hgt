import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResolventAssembly
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteAngularSourceBounds

/-! The finite full-source assembly retains the actual outer endpoint and spatial boundedness. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem continuedPrincipalDifference_physical_boundary (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (i : Fin 3) :
    Tendsto (continuedPrincipalDifference q branch w a i) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  apply (principalDifference_boundary q branch w a (onsetTransform (2*physicalRate q branch) w)
    (principalChamber_of_three_halves q w hd) i).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (continuedPrincipalDifference_eq_original q branch w a hwi (by linarith) (by linarith) i t ht).symm

/-- Every retained channel has its original zero outer trace, so the complete assembly does too. -/
theorem clearedPhysicalGreen_boundary (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) :
    Tendsto (clearedPhysicalGreen q r branch w a) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have hU (J : ℂ) := continuedReducedGreen_physical_boundary q branch w (physicalRadialFrequency r) a J hd hwi
    (physicalRadialFrequency_chamber r w (by linarith))
  have hV (i : Fin 3) := continuedPrincipalDifference_physical_boundary q branch w a hd hwi i
  have hs := tendsto_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    ((hV i).sub (hU (principalAmplitude q i))).const_mul
      (physicalAngularGapCofactor q r i*scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q i)))
  simpa only [clearedPhysicalGreen,physicalResolventAssembly,sub_zero,mul_zero,Finset.sum_const_zero,add_zero] using!
    ((hU (scalarResidualPeriod q (physicalAngularParameter r))).const_mul (physicalAngularGapProduct q r)).add hs

/-- The original finite full-source assembly is uniformly bounded on the physical response overlap. -/
theorem clearedPhysicalGreen_bounded (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0, ‖clearedPhysicalGreen q r branch w a t‖ ≤ C := by
  choose U hU hUb using (fun J : ℂ =>
    continuedReducedGreen_physical_bounded q branch w (physicalRadialFrequency r) a J hd hwi
      (physicalRadialFrequency_chamber r w (by linarith)))
  choose V hV hVb using continuedPrincipalDifference_bounded q branch w a hd hwi
  refine ⟨‖physicalAngularGapProduct q r‖*U (scalarResidualPeriod q (physicalAngularParameter r))+
    ∑ i : Fin 3, ‖physicalAngularGapCofactor q r i*scalarCutoffPeriod (physicalAngularParameter r) (principalExponent q i)‖*
      (V i+U (principalAmplitude q i)),?_,fun t ht => ?_⟩
  · exact add_nonneg (mul_nonneg (norm_nonneg _) (hU _)) (Finset.sum_nonneg
      (fun i _ => mul_nonneg (norm_nonneg _) (add_nonneg (hV i) (hU _))))
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hUb _ t ht) (norm_nonneg _)
    · apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add (hVb i t ht) (hUb _ t ht))

end
end RHTower.D4BMJointSource
