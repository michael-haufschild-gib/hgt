import GaloisForLFunctions.RHTower.FokasLenellsCausalRationalEigenvectors
import GaloisForLFunctions.RHTower.FokasLenellsCausalPoleRate
import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorGraph
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual rational eigenvectors of the full maximal causal generator

Differentiating the proved scalar orbit puts every rational upper-pole probe
in the actual maximal domain. The rational rate involution reaches every
point of the open left half-plane, with explicit nonzero eigenvectors. These
are completed-domain vectors outside the earlier encoded analytic range.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Every actual rational causal eigenvector has its literal right derivative in the Hilbert norm. -/
theorem causalCauchyEigenvector_hasRightDeriv (w : {z : ℂ // 0 < z.im}) :
    HasDerivWithinAt (causalForwardOrbit (causalCauchyEigenvector w))
      (causalPoleRate w.val • causalCauchyEigenvector w) (Ioi 0) 0 := by
  have hc : HasDerivAt (fun z : ℂ => Complex.exp (z*causalPoleRate w.val)) (causalPoleRate w.val) 0 := by
    simpa only [id_eq,zero_mul,Complex.exp_zero,one_mul] using
      ((hasDerivAt_id (0:ℂ)).mul_const (causalPoleRate w.val)).cexp
  have hr : HasDerivAt (fun r : ℝ => Complex.exp ((r:ℂ)*causalPoleRate w.val)) (causalPoleRate w.val) 0 :=
    hc.comp_ofReal
  have hv := hr.smul_const (causalCauchyEigenvector w)
  apply hv.hasDerivWithinAt.congr
  · intro r hr0
    change causalLowerCauchyEvolution r.toNNReal (causalCauchyEigenvector w) = _
    rw [causalLowerCauchyEvolution_eigenvector,causalAnalyticPhase_rate,Real.coe_toNNReal r hr0.le]
  · rw [causalForwardOrbit_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul]

/-- Every rational upper-pole vector belongs to the actual maximal generator domain. -/
theorem causalCauchyEigenvector_mem_domain (w : {z : ℂ // 0 < z.im}) :
    causalCauchyEigenvector w ∈ causalGeneratorDomain :=
  (causalGeneratorDomain_mem_iff _).2 ⟨_,causalCauchyEigenvector_hasRightDeriv w⟩

/-- The actual rational eigenvector as an element of the proved maximal domain. -/
def causalCauchyEigenDomain (w : {z : ℂ // 0 < z.im}) : causalGeneratorDomain :=
  ⟨causalCauchyEigenvector w,causalCauchyEigenvector_mem_domain w⟩

/-- The rational eigenvector remains nonzero in the actual maximal domain. -/
theorem causalCauchyEigenDomain_ne_zero (w : {z : ℂ // 0 < z.im}) : causalCauchyEigenDomain w ≠ 0 := by
  intro h
  exact causalCauchyEigenvector_ne_zero w (congrArg (fun u : causalGeneratorDomain => u.val) h)

/-- The maximal generator acts on each actual rational vector by exactly its complex phase rate. -/
theorem causalGenerator_cauchyEigenDomain (w : {z : ℂ // 0 < z.im}) :
    causalGenerator (causalCauchyEigenDomain w) = causalPoleRate w.val • (causalCauchyEigenDomain w).val :=
  (causalGenerator_eq_iff _ _).2 (causalCauchyEigenvector_hasRightDeriv w)

/-- A concrete maximal-domain eigenvector for each point of the open left half-plane. -/
def causalLeftEigenvector (z : {z : ℂ // z.re < 0}) : causalGeneratorDomain :=
  causalCauchyEigenDomain (causalEigenPole z)

/-- Every open-left-half-plane eigenvector is actually nonzero. -/
theorem causalLeftEigenvector_ne_zero (z : {z : ℂ // z.re < 0}) : causalLeftEigenvector z ≠ 0 :=
  causalCauchyEigenDomain_ne_zero (causalEigenPole z)

/-- Every number in the open left half-plane is an actual maximal-generator eigenvalue. -/
theorem causalGenerator_leftEigenvector (z : {z : ℂ // z.re < 0}) :
    causalGenerator (causalLeftEigenvector z) = z.val • (causalLeftEigenvector z).val := by
  change causalGenerator (causalCauchyEigenDomain (causalEigenPole z)) = _
  rw [causalGenerator_cauchyEigenDomain,causalPoleRate_eigenPole]
  rfl

/-- Existing rational pole probes give genuine generator eigenvectors outside the encoded analytic range. -/
theorem upperPoleProbe_generator_outside_encodedRange (r a : ℝ) :
    ∃ u : causalGeneratorDomain, u.val.val = upperPoleProbe r a ∧
      causalGenerator u = causalPoleRate (causalUpperPolePoint r a).val • u.val ∧
      u.val.val ∉ rawComplexCauchyCoreRange := by
  refine ⟨causalCauchyEigenDomain (causalUpperPolePoint r a),
    causalCauchyEigenvector_upperPole r a,causalGenerator_cauchyEigenDomain _,?_⟩
  change (causalCauchyEigenvector (causalUpperPolePoint r a)).val ∉ rawComplexCauchyCoreRange
  rw [causalCauchyEigenvector_upperPole]
  exact upperPoleProbe_not_mem_rawComplexCauchyCoreRange r a

end
end RHTower.FokasLenells
