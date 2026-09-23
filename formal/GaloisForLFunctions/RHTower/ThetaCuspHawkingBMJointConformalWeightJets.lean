import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointConformalChartJets

/-! The actual nonzero field weight and all coordinate derivatives in the joint conjugation. -/
open Filter Topology Set
open scoped ContDiff
namespace RHTower.D4BMJointConformal
open D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def weight (p : Point3) : ℂ := (Real.sqrt (p 2):ℂ)*(radialRoot (p 0):ℂ)

def weightFirst (p : Point3) (i : Fin 3) : ℂ :=
  ![(-radialUnit (p 0)/2:ℝ)*weight p,0,weight p/(2*(p 2:ℂ))] i

def weightSecond (p : Point3) (i : Fin 3) : ℂ :=
  ![(warp (p 0)^(2 : ℕ)/2+radialUnit (p 0)^(2 : ℕ)/4:ℝ)*weight p,0,-weight p/(4*(p 2:ℂ)^(2 : ℕ))] i

theorem weight_ne_zero (p : Point3) (hp : 0 < p 2) : weight p ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hp)))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (radialRoot_pos _)))

theorem weight_smooth (p : Point3) (hp : 0 < p 2) : ContDiffAt ℝ ∞ weight p := by
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
    ((ContinuousLinearMap.proj 2 : Point3 →L[ℝ] ℝ).contDiff.contDiffAt.sqrt (ne_of_gt hp))).mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (radialRoot_smooth.comp (ContinuousLinearMap.proj 0 : Point3 →L[ℝ] ℝ).contDiff).contDiffAt)

theorem weightCurve_hasDerivAt (p : Point3) (i : Fin 3) (s : ℝ)
    (hp : 0 < (coordinateLine p i s) 2) :
    HasDerivAt (fun x => weight (coordinateLine p i x)) (weightFirst (coordinateLine p i s) i) s := by
  fin_cases i
  · apply ((radialRoot_hasDerivAt s).ofReal_comp.const_mul (Real.sqrt (p 2):ℂ)).congr_deriv
    simp only [weight,weightFirst,coordinateLine]
    simp only [Function.update,Fin.isValue]
    push_cast
    ring
  · simpa [weight,weightFirst,coordinateLine] using! hasDerivAt_const s (weight p)
  · have hs : 0 < s := by simpa [coordinateLine] using hp
    apply ((heightRoot_hasDerivAt s hs).ofReal_comp.mul_const (radialRoot (p 0):ℂ)).congr_deriv
    simp only [weight,weightFirst,coordinateLine,heightRootFirst]
    simp only [Function.update,Fin.isValue]
    push_cast
    ring

theorem weightFirstCurve_hasDerivAt (p : Point3) (i : Fin 3) (s : ℝ)
    (hp : 0 < (coordinateLine p i s) 2) :
    HasDerivAt (fun x => weightFirst (coordinateLine p i x) i)
      (weightSecond (coordinateLine p i s) i) s := by
  fin_cases i
  · have hm := weightCurve_hasDerivAt p 0 s hp
    apply (((radialUnit_warp_derivative s).neg.div_const 2).ofReal_comp.mul hm).congr_deriv
    simp only [weight,weightFirst,weightSecond,coordinateLine,Pi.neg_apply]
    simp only [Function.update,Fin.isValue]
    push_cast
    ring
  · simpa [weightFirst,weightSecond,coordinateLine] using! hasDerivAt_const s (0:ℂ)
  · have hs : 0 < s := by simpa [coordinateLine] using hp
    have hs0 : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
    have hden : (2:ℂ)*(s:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hs))
    apply ((weightCurve_hasDerivAt p 2 s hp).div
      ((hasDerivAt_id s).ofReal_comp.const_mul 2) hden).congr_deriv
    simp only [weight,weightFirst,weightSecond,coordinateLine]
    simp only [Function.update,Fin.isValue,id_eq]
    push_cast
    field_simp [hs0]
    ring

/-- Both field-weight slots are actual derivatives at every physical positive-height point. -/
theorem weightCurve_derivatives (p : Point3) (hp : 0 < p 2) (i : Fin 3) :
    deriv (fun x => weight (coordinateLine p i x)) (p i) = weightFirst p i ∧
      deriv (deriv (fun x => weight (coordinateLine p i x))) (p i) = weightSecond p i := by
  have hp' : 0 < (coordinateLine p i (p i)) 2 := by simpa [coordinateLine_base] using hp
  have hN : ∀ᶠ x in 𝓝 (p i), 0 < (coordinateLine p i x) 2 :=
    (coordinateLine_smooth p i).continuous.continuousAt.preimage_mem_nhds
      ((isOpen_lt continuous_const (continuous_apply 2)).mem_nhds hp')
  have he : deriv (fun x => weight (coordinateLine p i x)) =ᶠ[𝓝 (p i)]
      (fun x => weightFirst (coordinateLine p i x) i) := by
    filter_upwards [hN] with x hx
    exact (weightCurve_hasDerivAt p i x hx).deriv
  constructor
  · simpa [coordinateLine_base] using (weightCurve_hasDerivAt p i (p i) hp').deriv
  · rw [he.deriv_eq]
    simpa [coordinateLine_base] using (weightFirstCurve_hasDerivAt p i (p i) hp').deriv

end
end RHTower.D4BMJointConformal
