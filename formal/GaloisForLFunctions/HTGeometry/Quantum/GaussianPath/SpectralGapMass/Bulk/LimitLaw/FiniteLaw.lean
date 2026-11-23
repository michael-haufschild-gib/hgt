import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.Characteristic
import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure

/-! # Empirical energy and gap probability laws with spectral multiplicities -/
open MeasureTheory Finset
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
open FourierLLogL
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- A uniform index samples the list with multiplicity. -/
def listLaw (E : I → ℝ) : ProbabilityMeasure ℝ := (Law.uniform I).atomicProbability E

theorem integral_listLaw (E : I → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(listLaw E : Measure ℝ)) = (Fintype.card I:ℝ)⁻¹*∑ i, f (E i) := by
  rw [listLaw,Law.integral_atomicProbability,Law.Ex,mul_sum]
  rfl

theorem integrable_listLaw (E : I → ℝ) (f : ℝ → ℝ) :
    Integrable f (listLaw E : Measure ℝ) := Law.integrable_atomicProbability _ _ _

theorem charFun_listLaw (E : I → ℝ) (t : ℝ) :
    charFun (listLaw E : Measure ℝ) t = energyCharacteristic E t := by
  rw [charFun_apply_real]
  change (∫ x : ℝ, _ ∂(∑ i, ENNReal.ofReal ((Fintype.card I:ℝ)⁻¹) • Measure.dirac (E i)))=_
  rw [integral_finsetSum_measure (fun _ _ => (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (by positivity : 0 ≤ (Fintype.card I:ℝ)⁻¹),
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,energyCharacteristic,mul_sum,Complex.ofReal_mul]

/-- The gap of two independently sampled eigenlines has characteristic
function equal to the product of the positive and negative time traces. -/
theorem gap_characteristic (E : I → ℝ) (t : ℝ) :
    energyCharacteristic (fun p : I×I => E p.1-E p.2) t =
      energyCharacteristic E t*energyCharacteristic E (-t) := by
  unfold energyCharacteristic
  rw [Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type]
  conv_rhs => rw [mul_mul_mul_comm]
  congr 1
  simp only [sum_mul,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
