import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResponseWeakIntegral
import GaloisForLFunctions.HTGeometry.ContinuousWeakSecondLocalRegularity

/-! The actual physical response has two classical radial derivatives with its complete original forcing. -/
open Complex MeasureTheory Set Filter
open scoped SchwartzMap
namespace RHTower.D4BMJointSource
open D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original radial equation's second derivative density for the actual complete physical response. -/
def physicalCuspSecond (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) (t : ℝ) : ℂ :=
  w^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t-
    (physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t-
    continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t

theorem physicalCuspSecond_continuousOn (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ContinuousOn (physicalCuspSecond q r branch w a hw hd hwi hwr) (Iio (0:ℝ)) := by
  have hp : ContinuousOn (physicalCuspProfile q r branch w a hw hd hwi hwr) (Iio (0:ℝ)) :=
    (physicalCuspProfile_continuous q r branch w a hw hd hwi hwr).continuousOn
  have hv : ContinuousOn angularWeight (Iio (0:ℝ)) := angularWeight_smooth.continuous.continuousOn
  have hs := continuedAngularSourceProjection_continuousOn q branch (physicalAngularParameter r) a w hwi
    (abs_lt.mp hwr).1
  exact ((continuousOn_const.mul hp).sub ((continuousOn_const.mul (hv.pow 2)).mul hp)).sub hs

private theorem negativePairing (φ f : ℝ → ℂ) (hs : tsupport φ ⊆ Iio (0:ℝ)) :
    (∫ t in Iio (0:ℝ), φ t*f t) = ∫ t : ℝ, φ t*f t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hs h)),zero_mul]

private theorem physical_local_weak (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (l v : ℝ) (hv : v < 0) (ψ : 𝓢(ℝ,ℂ)) (hs : ∀ t, t ∉ Ioo l v → ψ t = 0) :
    (∫ t : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) t*
      physicalCuspProfile q r branch w a hw hd hwi hwr t) =
      ∫ t : ℝ, ψ t*physicalCuspSecond q r branch w a hw hd hwi hwr t := by
  have hb : tsupport (ψ : ℝ → ℂ) ⊆ Icc l v := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    exact ht (hs t (fun h => hn ⟨h.1.le,h.2.le⟩))
  have hψ : tsupport (ψ : ℝ → ℂ) ⊆ Iio (0:ℝ) := fun t ht => (hb ht).2.trans_lt hv
  have hk := schwartz_compact_of_zero_outside_Ioo ψ l v hs
  let f : RadialCore := ⟨ψ,ψ.smooth ⊤,hk,hψ⟩
  have h₂ : tsupport (deriv (deriv (ψ : ℝ → ℂ))) ⊆ Iio (0:ℝ) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hψ)
  have h := physicalCuspProfile_weak_equation q r branch w a hw hd hwi hwr f
  change (∫ t in Iio (0:ℝ), deriv (deriv (ψ : ℝ → ℂ)) t*_) + _ - _ = _ at h
  rw [negativePairing _ _ h₂,negativePairing _ _ hψ,negativePairing _ _ hψ,
    negativePairing _ _ hψ] at h
  let P := physicalCuspProfile q r branch w a hw hd hwi hwr
  let V : ℝ → ℂ := fun t => angularWeight t^(2 : ℕ)*P t
  let S := continuedAngularSourceProjection q branch (physicalAngularParameter r) a w
  let lambda := physicalAngularParameter r^(2 : ℕ)-1/4
  have hiP := schwartz_pair_integrable ψ hk P (physicalCuspProfile_continuous q r branch w a hw hd hwi hwr)
  have hVc : Continuous V := (angularWeight_smooth.continuous.pow 2).mul
    (physicalCuspProfile_continuous q r branch w a hw hd hwi hwr)
  have hiV := schwartz_pair_integrable ψ hk V hVc
  have hiS : Integrable (fun t => ψ t*S t) :=
    radial_test_representative_integrable f _ S (continuedAngularSourceL2_ae q branch _ a w hwi hwr)
  have he (t : ℝ) : ψ t*physicalCuspSecond q r branch w a hw hd hwi hwr t =
      w^(2 : ℕ)*(ψ t*P t)-lambda*(ψ t*V t)-ψ t*S t := by
    dsimp [physicalCuspSecond,P,V,S,lambda]
    ring
  simp only [he]
  have hiPV : Integrable (fun t => w^(2 : ℕ)*(ψ t*P t)-lambda*(ψ t*V t)) := by
    convert (hiP.const_mul (w^(2 : ℕ))).sub (hiV.const_mul lambda) using 1
    rfl
  rw [integral_sub hiPV hiS,
    integral_sub (hiP.const_mul (w^(2 : ℕ))) (hiV.const_mul lambda),integral_const_mul,integral_const_mul]
  change (∫ t : ℝ, deriv (deriv (ψ : ℝ → ℂ)) t*P t) = _
  change (∫ t : ℝ, deriv (deriv (ψ : ℝ → ℂ)) t*P t)+lambda*(∫ t : ℝ, ψ t*V t)-
    w^(2 : ℕ)*(∫ t : ℝ, ψ t*P t) = -(∫ t : ℝ, ψ t*S t) at h
  linear_combination h

/-- Both classical radial derivatives belong to the original complete-source physical profile. -/
theorem physicalCuspProfile_hasDerivAt (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    HasDerivAt (physicalCuspProfile q r branch w a hw hd hwi hwr)
      (deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t) t ∧
    HasDerivAt (deriv (physicalCuspProfile q r branch w a hw hd hwi hwr))
      (physicalCuspSecond q r branch w a hw hd hwi hwr t) t := by
  have hv : t/2 < 0 := by linarith
  have hg := (physicalCuspSecond_continuousOn q r branch w a hw hd hwi hwr).mono
    (show Ioo (t-1) (t/2) ⊆ Iio (0:ℝ) from fun _ hx => hx.2.trans hv)
  have h := continuousOn_weak_second_hasDerivAt _ _
    (physicalCuspProfile_continuous q r branch w a hw hd hwi hwr) (t-1) (t/2) hg
    (physical_local_weak q r branch w a hw hd hwi hwr (t-1) (t/2) hv) t
    (by constructor <;> linarith)
  exact ⟨h.1.hasDerivAt,h.2⟩

/-- The original physical response satisfies the literal classical equation with all four projected source channels. -/
theorem physicalCuspProfile_equation (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t-
      deriv (deriv (physicalCuspProfile q r branch w a hw hd hwi hwr)) t-
      (physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t =
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t := by
  rw [(physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr t ht).2.deriv]
  unfold physicalCuspSecond
  ring

end
end RHTower.D4BMJointSource
