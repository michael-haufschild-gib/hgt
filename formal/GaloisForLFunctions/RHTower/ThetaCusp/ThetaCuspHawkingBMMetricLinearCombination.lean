import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent

/-! Linearity of the actual metric-field jet and cosmological Einstein variation. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMMetricReconstruction ComplexCoordinateMetricTwoJet
noncomputable section

/-- Linear combination in the complete metric-jet space, retaining every ordered derivative. -/
def metricJetCombination (c : ℂ) (K L : CoordinateMetricTwoJet 4 ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  ofSpace (toSpace K-c • toSpace L)

/-- The complete cosmological Einstein linearization acts linearly on the retained jet combination. -/
theorem cosmological_metricJetCombination (J K L : CoordinateMetricTwoJet 4 ℂ)
    (hJ : J.metric.det ≠ 0) (c Λ : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological J (metricJetCombination c K L) Λ i j =
      CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j-
        c*CoordinateMetricTwoJet.Linearization.cosmological J L Λ i j := by
  simp only [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv _ _ hJ,
    metricJetCombination,toSpace_ofSpace,map_sub,map_smul]
  change _+Λ*(K.metric i j-c*L.metric i j) = _
  simp only [smul_eq_mul]
  ring

/-- An actual field combination realizes the complete combined jet; none of its derivative slots is supplied. -/
theorem ofMetricField_combination (c : ℂ)
    (F G : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℝ)
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun y => G y i j) x) :
    ofMetricField (fun y i j => F y i j-c*G y i j) x =
      metricJetCombination c (ofMetricField F x) (ofMetricField G x) := by
  have hj (i j : Fin 4) : ofField (fun y => F y i j-c*G y i j) x =
      (ofField (fun y => F y i j) x).add ((constant (-c)).mul (ofField (fun y => G y i j) x)) := by
    have he : (fun y => F y i j-c*G y i j) = (fun y => F y i j+(-c)*G y i j) := by
      funext y
      ring
    rw [he,ofField_add (hF i j) (contDiffAt_const.mul (hG i j)),
      ofField_mul contDiffAt_const (hG i j),ofField_constant]
  have hs : toSpace (ofMetricField (fun y i j => F y i j-c*G y i j) x) =
      toSpace (metricJetCombination c (ofMetricField F x) (ofMetricField G x)) := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext k i j
      have h := congrArg (fun a => a.first k) (hj i j)
      change coordDeriv k (fun y => F y i j-c*G y i j) x =
        coordDeriv k (fun y => F y i j) x-c*coordDeriv k (fun y => G y i j) x
      simpa [ofField,ScalarTwoJet.add,ScalarTwoJet.mul,constant,sub_eq_add_neg] using h
    · funext k l i j
      have h := congrArg (fun a => a.second k l) (hj i j)
      change coordDeriv k (coordDeriv l (fun y => F y i j-c*G y i j)) x =
        coordDeriv k (coordDeriv l (fun y => F y i j)) x-
          c*coordDeriv k (coordDeriv l (fun y => G y i j)) x
      simpa [ofField,ScalarTwoJet.add,ScalarTwoJet.mul,constant,sub_eq_add_neg] using h
  exact congrArg ofSpace hs

end
end RHTower.D4BMModularCore
