import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceDressing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceOuterFactor

/-! Actual physical BM radial solutions with independent Laplace frequency. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def horizon (w chi : ℂ) : ℝ → ℂ := dress w (fun z => gaussFactor w chi false z)
def horizonFirst (w chi : ℂ) : ℝ → ℂ :=
  dressFirst w (fun z => gaussFactor w chi false z) (fun z => gaussFirst w chi false z)
def horizonSecond (w chi : ℂ) : ℝ → ℂ :=
  dressSecond w (fun z => gaussFactor w chi false z) (fun z => gaussFirst w chi false z)
    (fun z => gaussSecond w chi false z)

def normalizable (w chi : ℂ) : ℝ → ℂ := dress w (outerFactor w chi)
def normalizableFirst (w chi : ℂ) : ℝ → ℂ := dressFirst w (outerFactor w chi) (outerFirst w chi)
def normalizableSecond (w chi : ℂ) : ℝ → ℂ :=
  dressSecond w (outerFactor w chi) (outerFirst w chi) (outerSecond w chi)

/-- The full physical horizon branch has actual first and second radial derivatives. -/
theorem horizon_derivatives {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (horizon w chi) (horizonFirst w chi z) z ∧
    HasDerivAt (horizonFirst w chi) (horizonSecond w chi z) z := by
  obtain ⟨hF,hD⟩ := gaussFactor_derivatives h false (enorm_ofReal_lt_one hz.1 hz.2)
  exact dress_derivatives w hz.1 hF.comp_ofReal hD.comp_ofReal

/-- The full physical outer branch has actual first and second radial derivatives. -/
theorem normalizable_derivatives {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (normalizable w chi) (normalizableFirst w chi z) z ∧
    HasDerivAt (normalizableFirst w chi) (normalizableSecond w chi z) z := by
  obtain ⟨hF,hD⟩ := outerFactor_derivatives h hz
  exact dress_derivatives w hz.1 hF hD

/-- The horizon solution obeys the original physical radial equation at free frequency. -/
theorem horizon_equation {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (horizon w chi z) (horizonFirst w chi z) (horizonSecond w chi z)=0 := by
  unfold horizon horizonFirst horizonSecond
  rw [dress_physical w chi _ _ _ hz.1,horizonFactor_equation h (enorm_ofReal_lt_one hz.1 hz.2),mul_zero]

/-- The normalizable solution obeys the same original physical radial equation. -/
theorem normalizable_equation {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (normalizable w chi z) (normalizableFirst w chi z) (normalizableSecond w chi z)=0 := by
  unfold normalizable normalizableFirst normalizableSecond
  rw [dress_physical w chi _ _ _ hz.1,outerFactor_original_equation h hz,mul_zero]

end
end RHTower.D4BMLaplaceRadial
