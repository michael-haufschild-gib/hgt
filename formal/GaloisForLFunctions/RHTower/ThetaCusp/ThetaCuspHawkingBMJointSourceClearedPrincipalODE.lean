import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedPrincipal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalHorizonBound

/-! The actual principal ODE, forcing, and spatial derivatives with their original denominator cleared. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original angular principal potential on the tortoise ray. -/
def principalPotential (q : XiZeroCopy) (i : Fin 3) (t : ℝ) : ℂ :=
  -(horizonCoordinate t:ℂ)*(principalExponent q i*(principalExponent q i-1))

/-- Original reduced squared-source forcing with its actual source and connection denominators cleared. -/
def clearedPrincipalForcing (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  -connection w (principalFrequency q i)*
    reducedCoefficient (physicalRate q branch) w a (clearedOnset (physicalRate q branch) w) t*principalAmplitude q i

/-- The undivided forcing is exactly the original forcing multiplied by the same clearing factor. -/
theorem clearedPrincipalForcing_eq (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3)
    (hs : w-2*physicalRate q branch ≠ 0) (t : ℝ) :
    clearedPrincipalForcing q branch w a i t = principalClearingFactor q branch w i*
      (reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i) := by
  dsimp [clearedPrincipalForcing,principalClearingFactor,reducedCoefficient,sourceAmplitude,clearedOnset,continuedOnset]
  field_simp [hs]

/-- The cleared principal first jet and its derivative are the actual original ODE jets off the denominator. -/
theorem clearedPrincipalDifference_hasDerivAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3)
    (hs : w-2*physicalRate q branch ≠ 0) (hc : connection w (principalFrequency q i) ≠ 0)
    (t : ℝ) (ht : t < 0) :
    HasDerivAt (clearedPrincipalDifference q branch w a i)
      (clearedPrincipalDifferenceFirst q branch w a i t) t ∧
    HasDerivAt (clearedPrincipalDifferenceFirst q branch w a i)
      (w^(2 : ℕ)*clearedPrincipalDifference q branch w a i t+
        principalPotential q i t*clearedPrincipalDifference q branch w a i t-
        clearedPrincipalForcing q branch w a i t) t := by
  have hU : clearedPrincipalDifference q branch w a i =
      fun r => principalClearingFactor q branch w i*continuedPrincipalDifference q branch w a i r :=
    funext (clearedPrincipalDifference_eq q branch w a i hs hc)
  have hV : clearedPrincipalDifferenceFirst q branch w a i =
      fun r => principalClearingFactor q branch w i*continuedPrincipalDifferenceFirst q branch w a i r :=
    funext (clearedPrincipalDifferenceFirst_eq q branch w a i hs hc)
  rw [hU,hV]
  have hd := continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht
  refine ⟨hd.1.const_mul _,?_⟩
  have he := continuedPrincipalDifference_equation q branch w a hw hwre i hc t ht
  rw [continuedPrincipalDifference_secondDerivative q branch w a hw hwre i t ht] at he
  convert! hd.2.const_mul (principalClearingFactor q branch w i) using 1
  rw [clearedPrincipalForcing_eq q branch w a i hs t]
  dsimp [principalPotential]
  linear_combination (principalClearingFactor q branch w i)*he

/-- The fixed principal potential has its uniform, exact two-power horizon bound. -/
theorem principalPotential_norm_le_exp (q : XiZeroCopy) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    ‖principalPotential q i t‖ ≤ (4*‖principalExponent q i*(principalExponent q i-1)‖)*Real.exp (2*t) := by
  rw [principalPotential,norm_mul,norm_neg]
  calc
    _ ≤ (4*Real.exp (2*t))*‖principalExponent q i*(principalExponent q i-1)‖ :=
      mul_le_mul_of_nonneg_right (horizonCoordinate_norm_le_exp t ht) (norm_nonneg _)
    _ = _ := by ring

/-- The actual source and connection denominators are simultaneously nonzero on a punctured germ. -/
theorem principal_denominators_eventually_ne_zero (q : XiZeroCopy) (branch : Bool) (w : ℂ)
    (hw : w.im ≠ 0) (i : Fin 3) :
    ∀ᶠ u in 𝓝[≠] w, u-2*physicalRate q branch ≠ 0 ∧ connection u (principalFrequency q i) ≠ 0 := by
  have hs : ∀ᶠ u in 𝓝[≠] w, u-2*physicalRate q branch ≠ 0 := by
    by_cases he : w = 2*physicalRate q branch
    · have hn : ∀ᶠ u in 𝓝[≠] w, u ≠ w := self_mem_nhdsWithin
      filter_upwards [hn] with u hu
      exact sub_ne_zero.mpr (by simpa [← he] using hu)
    · exact ((continuous_id.sub continuous_const).continuousAt.eventually_ne
        (sub_ne_zero.mpr he)).filter_mono nhdsWithin_le_nhds
  exact hs.and (connection_eventually_ne_zero w (principalFrequency q i) hw)

end
end RHTower.D4BMJointSource
