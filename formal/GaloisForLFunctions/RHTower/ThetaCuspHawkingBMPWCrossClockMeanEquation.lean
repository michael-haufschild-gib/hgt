import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspMeanLaplacian

/-! The literal cross-branch clock source under the original periodic cusp mean. -/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace RHTower.D4BMPWCrossClockMeanEquation
open D4BMModularCore D4BMCuspProjection D4BMCuspResponse
open D4BMLiteralCyclicPeierlsCrossBranchBidegree
open D4BMLiteralCyclicPeierlsCrossBranchSource D4BMHorizon
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false

def crossPlanar (q : XiZeroCopy) (z : ℂ) : ℂ :=
  fullAngular q true (ofComplex z) * fullAngular q false (ofComplex z)

def crossMean (q : XiZeroCopy) : ℝ → ℂ := average (crossPlanar q)

def forcingMean (q : XiZeroCopy) (y : ℝ) : ℂ :=
  mean (fun x => crossBranchClockForcing q ![x,y])

private theorem crossPlanar_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (crossPlanar q) {z : ℂ | 0 < z.im} := by
  exact ((fullAngular_smooth q true).planar_contDiffOn).mul
    ((fullAngular_smooth q false).planar_contDiffOn)

private theorem crossPlanar_periodic (q : XiZeroCopy) {y : ℝ} (hy : 0 < y)
    (x : ℝ) : crossPlanar q (point (x+1) y) = crossPlanar q (point x y) := by
  have hpos (t : ℝ) : 0 < (point t y).im := by simpa [point] using hy
  have ht : ofComplex (point (x+1) y)=T • ofComplex (point x y) := by
    rw [ofComplex_apply_of_im_pos (hpos x),ofComplex_apply_of_im_pos (hpos (x+1))]
    apply UpperHalfPlane.ext_re_im
    · rw [ModularGroup.re_T_smul]
      simp [point]
    · rw [ModularGroup.im_T_smul]
      simp [point]
  have hb (b : Bool) : fullAngular q b (T • ofComplex (point x y)) =
      fullAngular q b (ofComplex (point x y)) := by
    simpa only [PSL2Z_mk_smul] using
      fullAngular_invariant q b (QuotientGroup.mk T) (ofComplex (point x y))
  simp only [crossPlanar,ht,hb]

theorem crossMean_laplacian (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    average (planarLaplacian (crossPlanar q)) y =
      deriv (deriv (crossMean q)) y := by
  exact average_laplacian (crossPlanar q) (crossPlanar_smooth q) hy
    (crossPlanar_periodic q hy)

private theorem crossPlanar_chart (q : XiZeroCopy) (w : UpperHalfPlane) :
    crossBranchField q (coordinates w) = crossPlanar q w := by
  change fullAngular q true (ofComplex (angularCoordinates.symm (angularCoordinates (w:ℂ)))) *
      fullAngular q false (ofComplex (angularCoordinates.symm (angularCoordinates (w:ℂ)))) =
    fullAngular q true (ofComplex (w:ℂ)) * fullAngular q false (ofComplex (w:ℂ))
  rw [angularCoordinates.symm_apply_apply]

private theorem crossPlanar_comp (q : XiZeroCopy) :
    ((fun w : UpperHalfPlane => crossBranchField q (coordinates w)) ∘ ofComplex) =
      crossPlanar q := by
  funext z
  rw [Function.comp_apply, crossPlanar_chart]
  simp only [crossPlanar, ofComplex_apply]

/-- The literal source equation survives in the original planar cusp chart. -/
theorem crossPlanar_clock_equation (q : XiZeroCopy) (z : ℂ) (hz : 0 < z.im) :
    (z.im : ℂ) ^ (2 : ℕ) * planarLaplacian (crossPlanar q) z =
      crossBranchClockParameter q * crossPlanar q z +
        crossBranchClockForcing q (angularCoordinates z) := by
  let w : UpperHalfPlane := ⟨z,hz⟩
  have hchart := chartLaplacian_coordinates (crossBranchField q) w
  change (z.im : ℂ) ^ (2 : ℕ) *
      planarLaplacian (((fun v : UpperHalfPlane =>
        crossBranchField q (coordinates v)) ∘ ofComplex)) z =
      hyperbolicLaplacian (crossBranchField q) (angularCoordinates z) at hchart
  rw [crossPlanar_comp] at hchart
  have hoperator : scalarLaplacian (crossBranchField q) (angularCoordinates z) =
      hyperbolicLaplacian (crossBranchField q) (angularCoordinates z) := by
    rw [scalarLaplacian_eq _ _ (by simpa [angularCoordinates] using hz)]
    rfl
  have hfield : crossBranchField q (angularCoordinates z) = crossPlanar q z := by
    have h := crossPlanar_chart q w
    change crossBranchField q (angularCoordinates z) = crossPlanar q z at h
    exact h
  have he := crossBranchField_clock_equation q (angularCoordinates z)
    (by simpa [angularCoordinates] using hz)
  rw [hoperator,hfield] at he
  rw [← hchart] at he
  exact he

/-- Horizontal averaging of the literal source loses no Laplacian term except
the exact periodic horizontal derivative. -/
theorem crossMean_clock_equation (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (2 : ℕ) * deriv (deriv (crossMean q)) y -
      crossBranchClockParameter q * crossMean q y = forcingMean q y := by
  have hF : IntegrableOn (fun x : ℝ => crossPlanar q (point x y))
      (Ioc (-1/2:ℝ) (1/2)) :=
    (slice_continuous (crossPlanar q) (crossPlanar_smooth q) hy).integrableOn_Ioc
  have hD : IntegrableOn (fun x : ℝ =>
      planarLaplacian (crossPlanar q) (point x y)) (Ioc (-1/2:ℝ) (1/2)) :=
    (slice_continuous (planarLaplacian (crossPlanar q))
      (planarLaplacian_contDiffOn (crossPlanar_smooth q)) hy).integrableOn_Ioc
  have hp (x : ℝ) : angularCoordinates (point x y) = ![x,y] := by
    ext i
    fin_cases i <;> simp [angularCoordinates,point]
  have he (x : ℝ) : crossBranchClockForcing q ![x,y] =
      (y:ℂ)^(2:ℕ) * planarLaplacian (crossPlanar q) (point x y) -
        crossBranchClockParameter q * crossPlanar q (point x y) := by
    have h := crossPlanar_clock_equation q (point x y)
      (by simpa [point] using hy)
    rw [hp] at h
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,
      Complex.ofReal_re,zero_add] at h ⊢
    linear_combination -h
  have hmean : forcingMean q y =
      (y:ℂ)^(2:ℕ) * average (planarLaplacian (crossPlanar q)) y -
        crossBranchClockParameter q * crossMean q y := by
    calc
      forcingMean q y = ∫ x in Ioc (-1/2:ℝ) (1/2),
          (y:ℂ)^(2:ℕ) * planarLaplacian (crossPlanar q) (point x y) -
            crossBranchClockParameter q * crossPlanar q (point x y) := by
        dsimp [forcingMean, mean]
        exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => he x)
      _ = _ := by
        rw [integral_sub (hD.const_mul _) (hF.const_mul _),
          integral_const_mul, integral_const_mul]
        rfl
  rw [crossMean_laplacian q hy] at hmean
  exact hmean.symm

end
end RHTower.D4BMPWCrossClockMeanEquation
