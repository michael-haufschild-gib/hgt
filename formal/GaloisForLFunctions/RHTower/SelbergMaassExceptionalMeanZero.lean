import GaloisForLFunctions.RHTower.SelbergMaassDeckAverage
import GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
import GaloisForLFunctions.RHTower.SelbergMaassGeneratorComparison
import GaloisForLFunctions.RHTower.SelbergMaassUnipotentBlocks

/-!
# Exceptional Maass sources have zero congruence mean

For an exceptional principal-congruence Maass cusp eigenform, the proved
vanishing of the full deck trace is exactly the vanishing of the source mean.
This discharges the mean-zero premise in the existing source variance,
generator, and unipotent-block comparisons. No spectral-gap or quarter
coercivity is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
namespace GaloisForLFunctions.RHTower.SelbergMaassExceptionalMeanZero
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassDeckAverage SelbergMaassGeneratorComparison SelbergMaassUnipotentBlocks
open GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- The exceptional source's full deck cancellation is exactly zero congruence mean. -/
theorem sourceMean_eq_zero : sourceMean N f = 0 := by
  funext z
  change (Fintype.card (Deck N) : ℂ)⁻¹ *
    ∑ q : Deck N, (quotientForm N f q).1.1 z = (0 : ℂ)
  rw [sum_deck_values_zero N lam f z, mul_zero]

/-- Pointwise form of `sourceMean_eq_zero` for existing source comparisons. -/
theorem sourceMean_apply_eq_zero (z : ℍ) : sourceMean N f z = 0 :=
  congrFun (sourceMean_eq_zero N lam f) z

/-- Full deck mixing energy equals original density for every exceptional source. -/
theorem source_mixing_energy_eq_density (z : ℍ) :
    (2 * (Fintype.card (Deck N) : ℝ))⁻¹ *
        ∑ g : Deck N, ‖finiteRegularUnitary g (sourceVector N f z) - sourceVector N f z‖ ^ 2 =
      density N f z := by
  rw [source_mixing_energy, density_mean_variance, sourceMean_apply_eq_zero]
  simp

/-- Complete unipotent-block motion controls exceptional source density. -/
theorem density_le_blockEnergy (z : ℍ) :
    density N f z ≤ 16 * blockEnergy N f z :=
  density_le_blockEnergy_of_mean_zero N f z (sourceMean_apply_eq_zero N lam f z)

/-- Literal `S,T` motion controls exceptional source density with the existing finite cost. -/
theorem density_le_generatorEnergy (z : ℍ) :
    density N f z ≤ generatorConstant N * generatorEnergy N f z :=
  density_le_generatorEnergy_of_mean_zero N f z (sourceMean_apply_eq_zero N lam f z)

/-- An exceptional Maass cusp eigenform cannot occur at principal level one.

At `N = 0`, the deck is the quotient by `Γ(1) = ⊤`; deck cancellation is then
the original source itself, contradicting cusp-form nonvanishing. -/
theorem no_exceptional_level_one
    (mu : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (0 + 1))) (mu : ℝ)) : False := by
  letI : Subsingleton (Deck 0) := by
    change Subsingleton (SL2Z ⧸ CongruenceSubgroup.Gamma 1)
    rw [CongruenceSubgroup.Gamma_one_top]
    exact QuotientGroup.subsingleton_quotient_top
  letI : Unique (Deck 0) :=
  {
    default := QuotientGroup.mk (1 : SL2Z)
    uniq _ := Subsingleton.elim _ _
  }
  apply g.2.1
  apply Subtype.ext
  funext z
  have h := sum_deck_values_zero 0 mu g z
  rw [Fintype.sum_unique] at h
  change (g.1.1 z : ℂ) = 0
  change (quotientForm 0 g (QuotientGroup.mk (1 : SL2Z))).1.1 z = 0 at h
  simpa only [quotientForm_mk, SelbergMaassCuspTransport.translate_one] using h

end
end GaloisForLFunctions.RHTower.SelbergMaassExceptionalMeanZero
