import GaloisForLFunctions.HTGeometry.ContinuousWeakSecondRegularity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalLaplaceRadial

/-! The actual causal Laplace profile satisfies the original classical radial equation. -/
open MeasureTheory Set Filter
open scoped SchwartzMap
namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMJointWave D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- The original reduced radial source is continuous at every finite tortoise coordinate. -/
theorem reducedCoefficient_continuous (s w a T : ℂ) : Continuous (reducedCoefficient s w a T) := by
  have hA : Continuous (sourceAmplitude s w a T) :=
    continuous_iff_continuousAt.mpr (fun t => (sourceAmplitude_hasDerivAt s w a T t).continuousAt)
  have hU : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun t => (radialUnit_hasDerivAt t).continuousAt)
  unfold reducedCoefficient
  apply hA.mul
  unfold reducedPolynomial liftSecondPolynomial amplitudeRate
  fun_prop

/-- The second spatial derivative demanded by the literal original radial equation. -/
def principalLaplaceSecond (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (x : ℝ) : ℂ :=
  w^2*principalLaplaceProfile q branch a i w hw x-
    principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*principalLaplaceProfile q branch a i w hw x-
      principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) x

theorem principalLaplaceSecond_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) : Continuous (principalLaplaceSecond q branch a i w hw) := by
  have hP := principalLaplaceProfile_continuous q branch a i w hw
  have hR := reducedCoefficient_continuous (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w)
  have hH := horizonCoordinate_continuous
  unfold principalLaplaceSecond
  fun_prop

private theorem negativePairing (φ f : ℝ → ℂ) (hs : tsupport φ ⊆ Iio (0:ℝ)) :
    (∫ x in Iio (0:ℝ), φ x*f x) = ∫ x : ℝ, φ x*f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),zero_mul]

private theorem principal_local_weak (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (l r : ℝ) (hr : r < 0)
    (ψ : 𝓢(ℝ,ℂ)) (hs : ∀ x, x ∉ Ioo l r → ψ x = 0) :
    (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*
      principalLaplaceProfile q branch a i w hw x) = ∫ x : ℝ, ψ x*principalLaplaceSecond q branch a i w hw x := by
  have hb : tsupport (ψ : ℝ → ℂ) ⊆ Icc l r := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    exact hx (hs x (fun h => hn ⟨h.1.le,h.2.le⟩))
  have hψ : tsupport (ψ : ℝ → ℂ) ⊆ Iio (0:ℝ) := fun x hx => lt_of_le_of_lt (hb hx).2 hr
  have h₂ : tsupport (deriv (deriv (ψ : ℝ → ℂ))) ⊆ Iio (0:ℝ) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hψ)
  have h := principalLaplaceProfile_weak_equation q branch a i w hw ψ hψ
  simp only [smul_eq_mul] at h
  rw [negativePairing _ _ hψ,negativePairing _ _ h₂,negativePairing _ _ hψ,negativePairing _ _ hψ] at h
  let f := principalLaplaceProfile q branch a i w hw
  let V : ℝ → ℂ := fun x => principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*f x
  let S : ℝ → ℂ := fun x => principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
    (onsetTransform (2*physicalRate q branch) w) x
  have hfc := principalLaplaceProfile_continuous q branch a i w hw
  have hVc : Continuous V := by
    have hh := horizonCoordinate_continuous
    unfold V f
    fun_prop
  have hSc : Continuous S := continuous_const.mul (reducedCoefficient_continuous _ _ _ _)
  have hk := schwartz_compact_of_zero_outside_Ioo ψ l r hs
  have hiF := schwartz_pair_integrable ψ hk f hfc
  have hiV := schwartz_pair_integrable ψ hk V hVc
  have hiS := schwartz_pair_integrable ψ hk S hSc
  have he (x : ℝ) : ψ x*principalLaplaceSecond q branch a i w hw x =
      w^2*(ψ x*f x)-ψ x*V x-ψ x*S x := by dsimp [principalLaplaceSecond,f,V,S]; ring
  simp only [he]
  have hiFV : Integrable (fun x => w^2*(ψ x*f x)-ψ x*V x) := by
    convert (hiF.const_mul (w^2)).sub hiV using 1; rfl
  rw [integral_sub hiFV hiS,integral_sub (hiF.const_mul (w^2)) hiV,integral_const_mul]
  change (∫ x : ℝ, deriv (deriv (ψ : ℝ → ℂ)) x*f x) = _
  change w^2*(∫ x : ℝ, ψ x*f x)-(∫ x : ℝ, deriv (deriv (ψ : ℝ → ℂ)) x*f x) =
    (∫ x : ℝ, ψ x*S x)+(∫ x : ℝ, ψ x*V x) at h
  linear_combination -h

/-- Both spatial derivatives of the actual transformed profile exist in the original radial interior. -/
theorem principalLaplaceProfile_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (x : ℝ) (hx : x < 0) :
    HasDerivAt (principalLaplaceProfile q branch a i w hw)
      (deriv (principalLaplaceProfile q branch a i w hw) x) x ∧
    HasDerivAt (deriv (principalLaplaceProfile q branch a i w hw))
      (principalLaplaceSecond q branch a i w hw x) x := by
  have h := continuous_weak_second_hasDerivAt _ _
    (principalLaplaceProfile_continuous q branch a i w hw) (principalLaplaceSecond_continuous q branch a i w hw)
    (x-1) (x/2) (by linarith) (principal_local_weak q branch a i w hw (x-1) (x/2) (by linarith))
    x (by constructor <;> linarith)
  exact ⟨h.1.hasDerivAt,h.2⟩

/-- The causal Laplace profile satisfies the same literal classical equation as the endpoint Green difference. -/
theorem principalLaplaceProfile_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalResponseGrowth q i < w.re) (x : ℝ) (hx : x < 0) :
    w^2*principalLaplaceProfile q branch a i w hw x-
      deriv (deriv (principalLaplaceProfile q branch a i w hw)) x-
        (horizonCoordinate x:ℂ)*principalExponent q i*(principalExponent q i-1)*principalLaplaceProfile q branch a i w hw x =
      reducedCoefficient (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w) x*principalAmplitude q i := by
  rw [(principalLaplaceProfile_hasDerivAt q branch a i w hw x hx).2.deriv]
  unfold principalLaplaceSecond
  ring

end
end RHTower.D4BMJointSource
