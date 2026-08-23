import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.DeningerLogKummerQuotient

/-!
# Hasse classification for logarithmic Kummer sections

The valuation profile is a complete local invariant of a groupified divisorial logarithmic
section modulo ordinary units.  Every finite profile occurs, and its realizing section is unique
modulo the unit image.
-/

namespace RHTower

open TopologicalSpace
open GaloisForLFunctions.HTGeometry

/-- Two logarithmic sections have the same finite valuation profile exactly when they differ by
an ordinary unit section. -/
theorem deningerLogKummer_congr_hasse_iff
    (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (s t : (deningerLogGpAddCond P).sub U) :
    s - t ∈ (deningerUnitToGpSections P U).range ↔
      deningerGpResidueHom P U s = deningerGpResidueHom P U t :=
  addHasse_congr_iff (deningerUnitToGpSections P U) (deningerGpResidueHom P U)
    (deningerLogKummer_sections_exact P U) s t

/-- Every finite valuation profile is realized by a logarithmic section, uniquely modulo ordinary
units. -/
theorem deningerLogKummer_exists_unique_mod_units
    (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (a : deningerLogIdx P U → ℤ) :
    ∃ s : (deningerLogGpAddCond P).sub U,
      deningerGpResidueHom P U s = a ∧
        ∀ t : (deningerLogGpAddCond P).sub U,
          deningerGpResidueHom P U t = a ↔
            t - s ∈ (deningerUnitToGpSections P U).range :=
  addHasse_exists_unique_mod_global
    (deningerUnitToGpSections P U) (deningerGpResidueHom P U)
    (deningerLogKummer_sections_exact P U) (deningerGpResidue_surjective P U) a

end RHTower
