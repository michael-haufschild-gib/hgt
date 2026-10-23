import GaloisForLFunctions.RHTower.ModularLambdaCellEnergyBound
import GaloisForLFunctions.RHTower.NonvacuousWitnessBound

/-!
# The `Γ(2)`-cell energy of `log λ`, without a finiteness premise

`exists_lintegral_sum_lambdaLogEnergy_le` summed over the cosets `SL(2,ℤ)/Γ(2)` under an assumed
`Fintype` structure.  `Γ(2)` has finite index (`CongruenceSubgroup.instFiniteIndexGamma`), which
supplies it.  The resulting area estimate `(Λ)` is in turn the premise of the windowed coset-energy
bound on the cyclic cover `Γ_N`, whose coset count is finite because `Γ_N` has finite index.
-/

open UpperHalfPlane MeasureTheory CongruenceSubgroup
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.ModularLambdaWinding

open ModularGroup

noncomputable section

/-- The cosets of the finite-index subgroup `Γ(2)` form a finite type. -/
@[reducible] def fintypeCosetsGammaTwo : Fintype (SL(2, ℤ) ⧸ Gamma 2) :=
  haveI : (Gamma 2).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma 2
  Subgroup.fintypeQuotientOfFiniteIndex

attribute [local instance] fintypeCosetsGammaTwo

/-- **The `Γ(2)`-cell energy of `log λ` grows linearly in the height**:
`∫_{𝒟 ∩ {Im ≤ T}} Σ_p Im(h_p⁻¹z)² |(log λ)'(h_p⁻¹z)|² dμ(z) ≤ C T`. -/
theorem exists_lintegral_sum_lambdaLogEnergy_le_unconditional :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫⁻ z in ModularGroup.fd ∩ {z : ℍ | z.im ≤ T},
          ∑ p : SL(2, ℤ) ⧸ Gamma 2, ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) ≤
        ENNReal.ofReal (C * T) :=
  exists_lintegral_sum_lambdaLogEnergy_le

end

end GaloisForLFunctions.RHTower.ModularLambdaWinding

namespace GaloisForLFunctions.RHTower.NonvacuousWitness

open GaloisForLFunctions.HTGeometry RepPointPair RepCoset ModularLambdaWinding ModularGroup

noncomputable section

/-- **The windowed coset energy of `log λ` on `Γ_N`** is at most `k C T`, `k = [Γ(2) : Γ_N]`, with
one constant `C` for all heights `T ≥ 1`. -/
theorem exists_lintegral_cosetEnergy_window_le (N : ℕ) [NeZero N] :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫⁻ z in fd, ENNReal.ofReal ({η : ℍ | invHeight η ≤ T}.indicator
        (cosetEnergy N lambdaLogEnergy) z) ≤
        (Nat.card (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) : ℝ≥0∞) *
          ENNReal.ofReal (C * T) := by
  obtain ⟨C, hΛ⟩ := exists_lintegral_sum_lambdaLogEnergy_le_unconditional
  set e := Subgroup.quotientEquivProdOfLE (windingSubgroup_le_gammaTwo N)
  haveI : Finite (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) :=
    Finite.of_surjective (Prod.snd ∘ e) (Prod.snd_surjective.comp e.surjective)
  letI : Fintype (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) := Fintype.ofFinite _
  refine ⟨C, fun T hT => ?_⟩
  rw [Nat.card_eq_fintype_card]
  convert lintegral_cosetEnergy_window_le N hΛ hT

end

end GaloisForLFunctions.RHTower.NonvacuousWitness
