import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMClassicalResponse

/-!
The original angular coordinate derivatives coincide with the complex planar chart derivatives. The exact linear identification transports the full hyperbolic Laplacian.
-/

open Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

/-- The exact real linear coordinate identification used by the original angular metric. -/
def angularCoordinates : ℂ ≃L[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z.re,z.im]
  invFun w := (w 0 : ℂ)+(w 1 : ℂ)*Complex.I
  left_inv z := by simp
  right_inv w := by ext i; fin_cases i <;> simp
  map_add' z w := by ext i; fin_cases i <;> simp
  map_smul' c z := by ext i; fin_cases i <;> simp
  continuous_toFun := by apply continuous_pi; intro i; fin_cases i <;> fun_prop
  continuous_invFun := by fun_prop

private theorem angularCoordinates_direction (i : Fin 2) :
    angularCoordinates (direction i) = Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [angularCoordinates,direction]

/-- Real coordinate derivatives and the actual complex chart directions coincide exactly. -/
theorem angularCoordinates_derivative (f : (Fin 2 → ℝ) → ℂ) (i : Fin 2) (z : ℂ) :
    fderiv ℝ (f ∘ angularCoordinates) z (direction i) = coordDeriv i f (angularCoordinates z) := by
  rw [angularCoordinates.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,angularCoordinates_direction]

/-- Both coordinate derivatives transfer through the exact linear chart without regularity assumptions. -/
theorem angularCoordinates_second (f : (Fin 2 → ℝ) → ℂ) (i : Fin 2) (z : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ (f ∘ angularCoordinates) w (direction i)) z (direction i) =
      coordDeriv i (coordDeriv i f) (angularCoordinates z) := by
  simp_rw [angularCoordinates_derivative]
  exact angularCoordinates_derivative (coordDeriv i f) i z

/-- The classical chart Laplacian is the original hyperbolic angular differential operator. -/
theorem chartLaplacian_coordinates (f : (Fin 2 → ℝ) → ℂ) (z : UpperHalfPlane) :
    chartLaplacian (fun w => f (coordinates w)) z = hyperbolicLaplacian f (coordinates z) := by
  have he : (fun w : UpperHalfPlane => f (coordinates w)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      f ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  have hd (i : Fin 2) :
      (fun w => fderiv ℝ ((fun w : UpperHalfPlane => f (coordinates w)) ∘ ofComplex) w (direction i))
        =ᶠ[𝓝 (z:ℂ)] (fun w => fderiv ℝ (f ∘ angularCoordinates) w (direction i)) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    rw [hw]
  unfold chartLaplacian planarLaplacian hyperbolicLaplacian
  simp only [Fin.sum_univ_two]
  rw [(hd 0).fderiv_eq,(hd 1).fderiv_eq,angularCoordinates_second,angularCoordinates_second]
  rfl

/-- Entire chart germs preserve the actual hyperbolic Laplacian. -/
theorem chartLaplacian_congr {f g : UpperHalfPlane → ℂ} {z : UpperHalfPlane}
    (he : f =ᶠ[𝓝 z] g) : chartLaplacian f z = chartLaplacian g z := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hp : f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] g ∘ ofComplex := by
    change ∀ᶠ w in 𝓝 (z:ℂ), f (ofComplex w) = g (ofComplex w)
    apply hc.eventually (p := fun w => f w = g w)
    rw [ofComplex_apply]
    filter_upwards [he] with w hw
    exact hw
  unfold chartLaplacian planarLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hd : (fun w => fderiv ℝ (f ∘ ofComplex) w (direction i)) =ᶠ[𝓝 (z:ℂ)]
      (fun w => fderiv ℝ (g ∘ ofComplex) w (direction i)) := by
    filter_upwards [hp.fderiv (𝕜 := ℝ)] with w hw
    rw [hw]
  rw [hd.fderiv_eq]

end
end RHTower.D4BMModularCore
