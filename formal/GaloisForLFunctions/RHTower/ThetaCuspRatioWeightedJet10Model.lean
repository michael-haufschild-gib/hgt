import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn0
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn1
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn2
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn3
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn4
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn5
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn6
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn7
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn8
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn9
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn10
import GaloisForLFunctions.RHTower.ThetaCuspRatioWeightedJet10KColumn11
namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def weightedJet10KCleanColumn : ℕ → Poly
  | 0 => weightedJet10KColumn0Clean.val
  | 1 => weightedJet10KColumn1Clean.val
  | 2 => weightedJet10KColumn2Clean.val
  | 3 => weightedJet10KColumn3Clean.val
  | 4 => weightedJet10KColumn4Clean.val
  | 5 => weightedJet10KColumn5Clean.val
  | 6 => weightedJet10KColumn6Clean.val
  | 7 => weightedJet10KColumn7Clean.val
  | 8 => weightedJet10KColumn8Clean.val
  | 9 => weightedJet10KColumn9Clean.val
  | 10 => weightedJet10KColumn10Clean.val
  | 11 => weightedJet10KColumn11Clean.val
  | _ => 0

def weightedJet10KCleanModel : Poly := ∑ k ∈ Finset.range 12, weightedJet10KCleanColumn k

theorem weightedJet10KCleanModel_eq : weightedJet 10=weightedJet10KCleanModel := by
  rw [weightedJet10_K_grid]
  unfold weightedJet10KCleanModel
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < 12 := Finset.mem_range.mp hk
  interval_cases k
  · exact weightedJet10KColumn0Clean.property
  · exact weightedJet10KColumn1Clean.property
  · exact weightedJet10KColumn2Clean.property
  · exact weightedJet10KColumn3Clean.property
  · exact weightedJet10KColumn4Clean.property
  · exact weightedJet10KColumn5Clean.property
  · exact weightedJet10KColumn6Clean.property
  · exact weightedJet10KColumn7Clean.property
  · exact weightedJet10KColumn8Clean.property
  · exact weightedJet10KColumn9Clean.property
  · exact weightedJet10KColumn10Clean.property
  · exact weightedJet10KColumn11Clean.property
end
end HTGeometry.ThetaRatioWeightedSquare
