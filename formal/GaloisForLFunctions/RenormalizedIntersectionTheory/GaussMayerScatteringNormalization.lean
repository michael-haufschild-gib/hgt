import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCofactorContinuation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerUnitEvenWordDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import Mathlib.Analysis.Meromorphic.Complex

/-! The constant-mode Mayer cofactor has the normalization of the actual
level-one Poincare scattering coefficient. The latter is defined by its
zero Fourier integral, independently of the transfer determinant. -/

open Complex Set
open scoped FourierTransform
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerParameter
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringNormalization

/-- Height-one base point of the actual upper-half-plane Poincare series. -/
def basePoint : _root_.RHTower.D4BMUpperHalfPlaneCoordinate := ⟨0,1,by norm_num⟩

/-- Archimedean factor in the uncompleted Eisenstein constant term. -/
def archimedeanFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^(1/2 : ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s

/-- The independent zeta/Gamma expression for the scattering continuation. -/
def scatteringEntry (s : ℂ) : ℂ :=
  archimedeanFactor s*(riemannZeta (2*s-1)/riemannZeta (2*s))

/-- The independent scattering expression continues meromorphically to the plane. -/
theorem meromorphic_scatteringEntry : Meromorphic scatteringEntry := by
  intro s
  have hG : MeromorphicAt (fun z : ℂ => Complex.Gamma (z-1/2)) s :=
    (Meromorphic.Gamma (s-1/2)).comp_analyticAt (x := s)
      (g := fun z : ℂ => z-1/2) (analyticAt_id.sub analyticAt_const)
  have hZ (z : ℂ) : MeromorphicAt riemannZeta z :=
    GaloisForLFunctions.HTGeometry.meromorphicOn_riemannZeta z (mem_univ z)
  have hZ₀ : MeromorphicAt (fun z : ℂ => riemannZeta (2*z)) s :=
    (hZ (2*s)).comp_analyticAt (x := s)
      (g := fun z : ℂ => 2*z) (analyticAt_const.mul analyticAt_id)
  have hZ₁ : MeromorphicAt (fun z : ℂ => riemannZeta (2*z-1)) s :=
    (hZ (2*s-1)).comp_analyticAt (x := s)
      (g := fun z : ℂ => 2*z-1) ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
  exact (((MeromorphicAt.const ((Real.pi : ℂ)^(1/2 : ℂ)) s).mul hG).div
    (Meromorphic.Gamma s)).mul (hZ₁.div hZ₀)

/-- The reflected coefficient of the genuine Poincare series at height one. -/
def actualScattering (P : _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (∫ x in Ioc (0 : ℝ) 1,
    fourier (0 : ℤ) (x : UnitAddCircle)*
      _root_.RHTower.d4BMRawEisensteinHorizontalFunction basePoint P x)-1

/-- The zero-frequency Cauchy transform fixes the Gamma normalization. -/
theorem kernel_normalization (P : _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter) :
    𝓕 (_root_.RHTower.d4BMCauchyPowerKernel basePoint P.s) 0=archimedeanFactor P.s := by
  rw [_root_.RHTower.fourier_d4BMCauchyPowerKernel_zero]
  simp only [basePoint,one_pow,mul_one]
  have hp : (Real.pi : ℂ)^P.s*(Real.pi : ℂ)^(-(P.s-1/2))=
      (Real.pi : ℂ)^(1/2 : ℂ) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  calc
    ((Real.pi : ℂ)^P.s/Complex.Gamma P.s)*
        (Complex.Gamma (P.s-1/2)*(Real.pi : ℂ)^(-(P.s-1/2))) =
      ((Real.pi : ℂ)^P.s*(Real.pi : ℂ)^(-(P.s-1/2)))*
        Complex.Gamma (P.s-1/2)/Complex.Gamma P.s := by ring
    _ = archimedeanFactor P.s := by rw [hp]; rfl

/-- Actual Fourier extraction gives the independent scattering expression. -/
theorem actualScattering_eq (P : _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter) :
    actualScattering P=scatteringEntry P.s := by
  rw [actualScattering,_root_.RHTower.d4BM_actualRawPoincare_zeroFourierCoefficient_eq_zetaRatio]
  change ((1 : ℂ)^P.s+((1 : ℂ)^P.s*
    𝓕 (_root_.RHTower.d4BMCauchyPowerKernel basePoint P.s) 0)*
    (riemannZeta (2*P.s-1)/riemannZeta (2*P.s)))-1=_
  rw [Complex.one_cpow,one_mul,kernel_normalization]
  unfold scatteringEntry
  ring

/-- The actual scattering coefficient and signed Mayer cofactor obey the same source identity. -/
theorem actual_cofactor_identity (P : _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter) :
    2*sourceDeterminant (2*P.s) 1*actualScattering P+
      archimedeanFactor P.s*MayerPole.polePart (2*P.s) 1=0 := by
  have hw : 2 < (2*P.s).re := by
    norm_num [Complex.mul_re]
    linarith only [P.re_gt_one]
  rw [actualScattering_eq,scatteringEntry,MayerCoprimeCofactor.polePart_eq_response hw,
    MayerCoprimeHeight.green_zero hw]
  ring

/-- The normalized cofactor is the genuine scattering coefficient in the absolute chamber. -/
theorem actualScattering_eq_cofactor (P : _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter) :
    actualScattering P=-(archimedeanFactor P.s/2)*
      (MayerPole.polePart (2*P.s) 1/sourceDeterminant (2*P.s) 1) := by
  have hw : 2 < (2*P.s).re := by
    norm_num [Complex.mul_re]
    linarith only [P.re_gt_one]
  have hD : sourceDeterminant (2*P.s) 1 ≠ 0 := by
    rw [sourceDeterminant_eq (show 0 < (2*P.s).re by linarith only [hw])]
    exact MayerUnitOrbitDeterminant.determinant_ne_zero_on_closed_unit hw (by simp)
  have h := actual_cofactor_identity P
  field_simp [hD]
  linear_combination h

/-- The independently normalized, denominator-cleared scattering identity continues
through the source half-plane away from the two scalar poles. -/
theorem continued_scattering_identity {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2) :
    2*sourceDeterminant w 1*(archimedeanFactor (w/2)*riemannZeta (w-1))+
      (archimedeanFactor (w/2)*riemannZeta w)*MayerPole.polePart w 1=0 := by
  have h := MayerCofactorContinuation.zeta_cofactor_identity hw hw1 hw2
  linear_combination archimedeanFactor (w/2)*h

#print axioms meromorphic_scatteringEntry
#print axioms kernel_normalization
#print axioms actualScattering_eq
#print axioms actual_cofactor_identity
#print axioms actualScattering_eq_cofactor
#print axioms continued_scattering_identity
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringNormalization
