import GaloisForLFunctions.HTGeometry.NonautonomousFinitePuiseuxValuationFlag
import GaloisForLFunctions.HTGeometry.MeroFieldConstants

/-!
# Nonvanishing of actual finite Puiseux derivative branches

Every state of a transcendental entire cascade is transcendental over the complex constants.
Since the constants of the global meromorphic differential field are exactly `ℂ`, its derivative
cannot vanish.  This proves nonvanishing of each actual derivative element, both in the ambient
meromorphic field and in the finite branch field used by the valuative selection program.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- Every actual cascade-state derivative is nonzero. -/
theorem cascadeMeroDeriv_ne_zero_of_transcendental
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (k : ℕ) :
    cascadeMeroDeriv hfan k ≠ 0 := by
  intro hzero
  have hstateDeriv : (cascadeMero hfan k)′ = 0 := by
    rw [← differentialJet_one_cascadeMero hfan k] at hzero
    exact hzero
  obtain ⟨c, hc⟩ := exists_complex_of_deriv_eq_zero hstateDeriv
  have hAI := algebraicIndependent_cascadeMero_over_complex hfan hall k
  let i : Fin (k + 1) := ⟨k, by omega⟩
  have htrans : Transcendental ℂ (cascadeMero hfan k) := by
    simpa [i] using hAI.transcendental i
  let cascadeMap : ℂ →+* meroField Set.univ :=
    @algebraMap ℂ (meroField Set.univ) _ _ cascadeUnitCostComplexAlgebra
  let relativeMap : ℂ →+* meroField Set.univ :=
    @algebraMap ℂ (meroField Set.univ) _ _ relativeGaugeComplexAlgebra
  have hmaps : cascadeMap c = relativeMap c := by
    change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ (algebraMap ℂ (RatFunc ℂ) c) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c)
    exact algebraMap_complex_meroField isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ c
  have hcCascade : cascadeMap c = cascadeMero hfan k := hmaps.trans hc
  apply htrans
  rw [← hcCascade]
  exact (isAlgebraic_algebraMap c : IsAlgebraic ℂ (cascadeMap c))

/-- Every actual derivative remains nonzero when corestricted to the finite branch field. -/
theorem nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (N : ℕ) (i : Fin (N + 1)) :
    nonautonomousFiniteCascadeDerivativeInBranchField hfan N i ≠ 0 := by
  intro hzero
  have hcoe := congrArg
    (fun x : NonautonomousFiniteCascadeBranchField hfan N =>
      (x : meroField Set.univ)) hzero
  rw [nonautonomousFiniteCascadeDerivativeInBranchField_coe] at hcoe
  have hzero' : cascadeMeroDeriv hfan i = 0 := by simpa using hcoe
  exact cascadeMeroDeriv_ne_zero_of_transcendental hfan hall i hzero'

/-- The unconditional algebraic-closure lift preserves nonvanishing of every actual derivative
branch. -/
theorem nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding_derivative_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (r : Fin N → ℕ) (hr : ∀ i, 0 < r i) (j : Fin (N + 1)) :
    nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding hfan hall h1 r hr
        (nonautonomousFiniteCascadeDerivativeInBranchField hfan N j) ≠ 0 := by
  intro hzero
  apply nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall N j
  apply (nonautonomousFiniteCascadeBranchAlgebraicClosureEmbedding
    hfan hall h1 r hr).injective
  simpa using hzero

end

end GaloisForLFunctions.HTGeometry
