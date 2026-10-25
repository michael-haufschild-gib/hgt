import GaloisForLFunctions.ArithmeticDefectRigidity.RealWienerConvolutionTransportsCofactorGrams
import GaloisForLFunctions.ArithmeticOrientationTheory.AnIndexFormulaForTheActualReceiver

/-!
# Möbius and Liouville cofactor modules are unit equivalent

The damped square kernel is a critical Wiener unit carrying the Möbius
source to the Liouville source. On escape their normalized cofactor Grams
are related by the complete unit transport.
-/

section

noncomputable section
set_option autoImplicit false
open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The mean in real Wiener convolution is its canonical absolutely convergent source mean. -/
theorem wienerConvolvedReceiver_eq_canonical (ε : SubcriticalDamping) (g : ℕ → ℝ)
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g) :
    wienerConvolvedReceiver ε g =
      TransHorizonIncidenceMechanics.weightCenteredPrefix
        (dirichletConv g (pmPowerDampedRealWeight ε))
        (∑' d : ℕ, dirichletConv g (pmPowerDampedRealWeight ε) d / d) := by
  have hm : (∑' d : ℕ, dirichletConv g (pmPowerDampedRealWeight ε) d / d) =
      (∑' d : ℕ, g d / d) * TransHorizonIncidenceMechanics.dampedDensity ε :=
    (TransHorizonIncidenceMechanics.hasSum_dirichletConv_div hg.summable_abs_div.of_abs.hasSum
      (TransHorizonIncidenceMechanics.hasSum_pmPowerDampedRealWeight_div ε.property.1)
      hg.summable_abs_div
      (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1)).tsum_eq
  rw [hm]
  rfl

/-- The canonical centered Liouville receiver at positive subcritical damping. -/
def liouvilleReceiver (ε : SubcriticalDamping) : ℕ → ℝ :=
  TransHorizonIncidenceMechanics.weightCenteredPrefix (dampedSignWeight liouvilleR ε)
    (∑' d : ℕ, dampedSignWeight liouvilleR ε d / d)

/-- The square-indicator unit produces exactly the canonical Liouville source. -/
theorem wienerConvolvedReceiver_dampedSquare (ε : SubcriticalDamping) :
    wienerConvolvedReceiver ε (dampedSignWeight squareIndicatorR ε) = liouvilleReceiver ε := by
  rw [wienerConvolvedReceiver_eq_canonical ε _
    (TransHorizonIncidenceMechanics.criticalWiener_dampedSquare ε.property.1)]
  have hsource : dirichletConv (dampedSignWeight squareIndicatorR ε)
      (pmPowerDampedRealWeight ε) = dampedSignWeight liouvilleR ε :=
    funext fun n => (TransHorizonIncidenceMechanics.dampedLiouville_eq_dirichletConv ε n).symm
  rw [hsource]
  rfl

namespace ActualCofactorLimit

/-- Every actual Möbius escape module is also the module of the corresponding Liouville source limit. -/
theorem admits_or_liouville_gram_is_unit_transport {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      ∃ u : (WienerAlgebraAt (1 / 2))ˣ,
        (u : WienerAlgebraAt (1 / 2)) =
          toWiener (dampedSignWeight squareIndicatorR ε)
            (TransHorizonIncidenceMechanics.criticalWiener_dampedSquare ε.property.1) ∧
        ∀ j k : ℕ+,
          Tendsto (fun m => (normalizedSourceGram (liouvilleReceiver ε)
            (L.subsequence m) j k : ℂ)) atTop
            (𝓝 (unitGram L (normalizedUnit L u) j k)) := by
  rcases admits_or_real_unit_convolution_gram_tendsto L with hpaid | htrans
  · exact Or.inl hpaid
  · have hu := (isWienerUnit_iff_isUnit (dampedSignWeight squareIndicatorR ε)
      (TransHorizonIncidenceMechanics.criticalWiener_dampedSquare ε.property.1)).mp
        (isWienerUnit_dampedSquare ε.property.1)
    obtain ⟨u, hu⟩ := hu
    refine Or.inr ⟨u, hu, fun j k => ?_⟩
    simpa only [wienerConvolvedReceiver_dampedSquare] using
      htrans (dampedSignWeight squareIndicatorR ε)
        (TransHorizonIncidenceMechanics.criticalWiener_dampedSquare ε.property.1) u hu j k

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.admits_or_liouville_gram_is_unit_transport
end
end
