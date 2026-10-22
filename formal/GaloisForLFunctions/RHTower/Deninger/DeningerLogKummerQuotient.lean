import GaloisForLFunctions.RHTower.Deninger.DeningerLogKummerSequence

/-!
# Quotient form of the divisorial logarithmic Kummer sequence

On every open subset of the arithmetic curve, groupified divisorial log sections modulo ordinary
units are exactly the finite valuation profiles at the marked primes.  This is the quotient form of
the local residue realization in the logarithmic Kummer sequence.
-/

namespace RHTower

open TopologicalSpace

section LogKummer

/-- Unit sections included in the groupified divisorial log structure. -/
def deningerUnitToGpSections (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    deningerUnitAddCond.sub U →+ (deningerLogGpAddCond P).sub U :=
  deningerUnitAddCond.inclSub (deningerLogGpAddCond P)
    (fun _ _ h p hxp _ => h p hxp) U

/-- The divisorial log sequence is exact on every open set. -/
theorem deningerLogKummer_sections_exact (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    Function.Exact (deningerUnitToGpSections P U) (deningerGpResidueHom P U) := by
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := deningerLogKummer_exact_sections P U s hs
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    rw [← ht]
    apply (deningerGpResidue_eq_zero_iff (deningerUnitToGpSections P U t)).2
    exact t.2

/-- Divisorial log sections modulo ordinary units are exactly their finite valuation profile. -/
noncomputable def deningerLogKummerSectionQuotientEquiv
    (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    ((deningerLogGpAddCond P).sub U ⧸ (deningerUnitToGpSections P U).range) ≃+
      (deningerLogIdx P U → ℤ) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (AddMonoidHom.exact_iff.mp (deningerLogKummer_sections_exact P U)).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (deningerGpResidueHom P U) (deningerGpResidue_surjective P U))

theorem deningerLogKummerSectionQuotientEquiv_mk
    (P : Finset Nat.Primes) (U : Opens deningerArithBase)
    (s : (deningerLogGpAddCond P).sub U) :
    deningerLogKummerSectionQuotientEquiv P U (QuotientAddGroup.mk s) =
      deningerGpResidueHom P U s := by
  simp only [deningerLogKummerSectionQuotientEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  change QuotientAddGroup.kerLift (deningerGpResidueHom P U)
    (QuotientAddGroup.mk s) = _
  rfl

end LogKummer

end RHTower
