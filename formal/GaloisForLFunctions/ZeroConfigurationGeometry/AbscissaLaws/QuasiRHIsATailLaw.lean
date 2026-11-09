import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator

/-!
# Quasi-RH depends only on the tail of the zeros

If the asymptotic abscissa law fails, the finite top layer attains the global
abscissa strictly below one. Consequently a tail bounded away from one forces
the entire zero set to be bounded away from one, though not at the same width.
-/

open Complex Set RHTower

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Failure of the abscissa law supplies a genuine zero-free half-plane. -/
theorem quasiRH_of_not_asymptoticAbscissaLaw :
    ¬ AsymptoticAbscissaLaw → zetaZeroAbscissa < 1 := by
  intro hnot
  obtain ⟨β₁, β, T, _, _, hβ, _, hfree, _⟩ :=
    not_asymptoticAbscissaLaw_iff_bilateral_spectralGap.mp hnot
  refine lt_of_le_of_lt (csSup_le zetaZeroReSet_nonempty ?_) hβ
  rintro x ⟨ρ, hρ, rfl⟩
  exact le_of_not_gt fun h => hfree ρ h hρ

/-- Either all zeros lie in a narrower strip, or the tail reaches the global abscissa. -/
theorem quasiRH_or_asymptoticAbscissaLaw :
    zetaZeroAbscissa < 1 ∨ AsymptoticAbscissaLaw := by
  by_cases hA : AsymptoticAbscissaLaw
  · exact Or.inr hA
  · exact Or.inl (quasiRH_of_not_asymptoticAbscissaLaw hA)

/-- Quasi-RH is equivalent to a strict upper bound on the tail abscissa. -/
theorem quasiRH_iff_zetaAsymptoticAbscissa_lt_one :
    zetaZeroAbscissa < 1 ↔ zetaAsymptoticAbscissa < 1 := by
  constructor
  · exact lt_of_le_of_lt zetaAsymptoticAbscissa_le_zetaZeroAbscissa
  · intro htail
    rcases quasiRH_or_asymptoticAbscissaLaw with hstrip | hA
    · exact hstrip
    · rwa [asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa.mp hA]
        at htail

/-- Failure of quasi-RH forces both abscissas to equal one and forces the abscissa law. -/
theorem not_quasiRH_iff_abscissas_eq_one :
    ¬ zetaZeroAbscissa < 1 ↔
      zetaZeroAbscissa = 1 ∧ zetaAsymptoticAbscissa = 1 ∧ AsymptoticAbscissaLaw := by
  constructor
  · intro hnot
    have hglobal := le_antisymm zetaZeroAbscissa_le_one (not_lt.mp hnot)
    have hA := quasiRH_or_asymptoticAbscissaLaw.resolve_left hnot
    exact ⟨hglobal,
      (asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa.mp hA).trans
        hglobal, hA⟩
  · rintro ⟨hglobal, _⟩
    rw [hglobal]
    exact lt_irrefl _

#print axioms quasiRH_of_not_asymptoticAbscissaLaw
#print axioms quasiRH_or_asymptoticAbscissaLaw
#print axioms quasiRH_iff_zetaAsymptoticAbscissa_lt_one
#print axioms not_quasiRH_iff_abscissas_eq_one

end GaloisForLFunctions.ZeroConfigurationGeometry
