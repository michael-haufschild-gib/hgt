import GaloisForLFunctions.RHTower.CCMRationalMoritaTraceClassAlgebra

/-!
# Exact rational-orbit trace formula on the full CCM crossed product

At every genuine nonzero adelic Morita base, ordinary operator trace of the full finite-support
crossed-product representation equals the rational-orbit sum of its identity-scaling coefficient.
This is the degree-zero CCM restriction formula on the actual algebra, proved from trace-class
summability and the weighted-shift diagonal calculation.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct

theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_complexSummable
    (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    Summable (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b) :=
  summable_norm_iff.mp
    (ccmRationalAdelicBruhatTensorOrbitCoefficient_summable t hbInf b)

/-- Linear rational-orbit sum at one nonzero adelic base. -/
def ccmRationalAdelicBruhatOrbitSum
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Core →ₗ[ℂ] ℂ where
  toFun t := ∑' q, ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q
  map_add' t u := by
    change (∑' q, ccmRationalAdelicBruhatTensorOrbitCoefficient (t + u) bInf b q) = _
    have ht := ccmRationalAdelicBruhatTensorOrbitCoefficient_complexSummable t hbInf b
    have hu := ccmRationalAdelicBruhatTensorOrbitCoefficient_complexSummable u hbInf b
    rw [show (fun q => ccmRationalAdelicBruhatTensorOrbitCoefficient (t + u) bInf b q) =
        fun q => ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q +
          ccmRationalAdelicBruhatTensorOrbitCoefficient u bInf b q by
      funext q
      exact ccmRationalAdelicBruhatTensorOrbit_add t u bInf b q]
    exact ht.tsum_add hu
  map_smul' z t := by
    change (∑' q, ccmRationalAdelicBruhatTensorOrbitCoefficient (z • t) bInf b q) =
      z * ∑' q, ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q
    rw [show (fun q => ccmRationalAdelicBruhatTensorOrbitCoefficient (z • t) bInf b q) =
        fun q => z * ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q by
      funext q
      exact ccmRationalAdelicBruhatTensorOrbit_smul z t bInf b q]
    exact tsum_mul_left

/-- Operator trace of the fixed-base representation, bundled linearly on the full source. -/
def ccmRationalAdelicMoritaRepresentationTrace
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Crossed →ₗ[ℂ] ℂ where
  toFun F := opTrace (ccmRationalAdelicMoritaRepresentation hbInf b F)
  map_add' F H := by
    rw [ccmRationalAdelicMoritaRepresentation_add]
    exact _root_.RHTower.opTrace_add_of_memSchattenClass_one
      (_root_.RHTower.IsTraceClass.memSchattenClass_one
        (ccmRationalAdelicMoritaRepresentation_isTraceClass hbInf b F))
      (_root_.RHTower.IsTraceClass.memSchattenClass_one
        (ccmRationalAdelicMoritaRepresentation_isTraceClass hbInf b H))
  map_smul' z F := by
    rw [map_smul, _root_.RHTower.opTrace_smul]
    rfl

/-- Rational-orbit sum of the identity-scaling crossed-product coefficient. -/
def ccmRationalAdelicMoritaIdentityCoefficientTrace
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ) :
    Crossed →ₗ[ℂ] ℂ :=
  (ccmRationalAdelicBruhatOrbitSum hbInf b).comp (Finsupp.lapply 1)

theorem ccmRationalAdelicMoritaRepresentationTrace_single
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (k : Scale) (t : Core) :
    ccmRationalAdelicMoritaRepresentationTrace hbInf b (Finsupp.single k t) =
      ccmRationalAdelicMoritaIdentityCoefficientTrace hbInf b
        (Finsupp.single k t) := by
  classical
  change opTrace (ccmRationalAdelicMoritaRepresentation hbInf b
      (Finsupp.single k t)) =
    ccmRationalAdelicMoritaIdentityCoefficientTrace hbInf b
      (Finsupp.single k t)
  rw [ccmRationalAdelicMoritaRepresentation_single,
    ccmRationalAdelicMoritaMonomial_opTrace]
  by_cases hk : k = 1
  · subst k
    simp [ccmRationalAdelicMoritaIdentityCoefficientTrace,
      ccmRationalAdelicBruhatOrbitSum]
  · have hOneK : (1 : Scale) ≠ k := fun h => hk h.symm
    simp [ccmRationalAdelicMoritaIdentityCoefficientTrace,
      ccmRationalAdelicBruhatOrbitSum, hk, hOneK]
    symm
    simpa only [ccmRationalAdelicBruhatTensorOrbitCoefficient,
      ccmRationalAdelicBruhatTensorOrbit_zero] using
      (tsum_zero : (∑' _q : CCMRationalUnit, (0 : ℂ)) = 0)

/-- **Exact full degree-zero CCM trace formula.** -/
theorem ccmRationalAdelicMoritaRepresentation_opTrace_eq_orbitSum
    {bInf : ℝ} (hbInf : bInf ≠ 0) (b : CCMRationalFiniteAdeleˣ)
    (F : Crossed) :
    opTrace (ccmRationalAdelicMoritaRepresentation hbInf b F) =
      ∑' q, ccmRationalAdelicBruhatTensorOrbitCoefficient (F 1) bInf b q := by
  have hmaps : ccmRationalAdelicMoritaRepresentationTrace hbInf b =
      ccmRationalAdelicMoritaIdentityCoefficientTrace hbInf b := by
    apply Finsupp.lhom_ext
    intro k t
    exact ccmRationalAdelicMoritaRepresentationTrace_single hbInf b k t
  exact LinearMap.congr_fun hmaps F

end RHTower
end GaloisForLFunctions
