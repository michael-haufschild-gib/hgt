import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.QuasiRHIsATailLaw
import GaloisForLFunctions.BezoutValuationIncidence.TheParityPairAtTheLeadingExponent
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.AZeroFreeRegionBoundsTheHeavyReturns

/-!
# Arithmetic bounds in the finite-top-layer alternative

Failure of the asymptotic abscissa law forces a global strip strictly inside
`Re s < 1`. The Mertens sum has a power saving. Heavy prime returns depend
only on the tail strip and therefore gain an exponent strictly above `1-Θ`.
-/

open Complex Filter Topology Finset Zeta23
open RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The abscissa law or a power saving for the actual Mertens sum. -/
theorem asymptoticAbscissaLaw_or_mertens_power_saving :
    AsymptoticAbscissaLaw ∨ ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 1 ∧
      ∀ x : ℕ, 1 ≤ x → |∑ e ∈ Icc 1 x, BezoutValuationIncidence.moebiusReal e| ≤ C * (x : ℝ) ^ β := by
  rcases ZeroConfigurationGeometry.quasiRH_or_asymptoticAbscissaLaw with hstrip | hA
  · exact Or.inr (BezoutValuationIncidence.zetaZeroAbscissa_lt_one_iff_moebius_rate.mp hstrip)
  · exact Or.inl hA

/-- A finite top layer leaves a stronger heavy-return exponent than its global width. -/
theorem asymptoticAbscissaLaw_or_stronger_heavy_return_power_bound :
    AsymptoticAbscissaLaw ∨
      ∃ β : ℝ, 1 / 2 ≤ β ∧ β < zetaZeroAbscissa ∧ β < 1 ∧
        ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ,
        ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
          ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
            IsDeltaReturn H (fun p : ℕ => Real.log p) δ t →
              c * (y : ℝ) ^ (1 - β) ≤ Real.log t := by
  by_cases hA : AsymptoticAbscissaLaw
  · exact Or.inl hA
  · obtain ⟨β, βstar, T, hβ, hgap, hstar, _, _, _, _, ⟨ρ, hρ⟩,
      _, _, _, _, _, _, htail⟩ :=
      ZeroConfigurationGeometry.not_asymptoticAbscissaLaw_iff_bilateral_spectralGap.mp hA
    have htop : βstar ≤ zetaZeroAbscissa := by
      rw [← hρ.2]
      exact re_le_zetaZeroAbscissa hρ.1
    refine Or.inr ⟨β, hβ, hgap.trans_le htop, hgap.trans hstar, ?_⟩
    have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier,
        T + 1 ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ β - 1 / 2 := by
      intro ρ hρ hheight
      obtain ⟨hleft, hright⟩ := htail ρ hρ.1 hρ.2.1 hρ.2.2
        (by linarith only [hheight])
      exact abs_le.mpr ⟨by linarith only [hleft], by linarith only [hright]⟩
    have h := log_ge_of_heavy_return_of_strip
      (sub_nonneg.mpr hβ) hwidth
    have he : 1 / 2 - (β - 1 / 2) = 1 - β := by ring
    simpa only [he] using h

#print axioms asymptoticAbscissaLaw_or_mertens_power_saving
#print axioms asymptoticAbscissaLaw_or_stronger_heavy_return_power_bound

end GaloisForLFunctions.ExceptionalLayerTheory
