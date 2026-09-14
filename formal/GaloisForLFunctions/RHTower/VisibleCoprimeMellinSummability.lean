import GaloisForLFunctions.RHTower.VisibleCoprimeMellinSymbol
import GaloisForLFunctions.RHTower.PrimeCpowAbsoluteAbscissa

/-!
# Exact summability domain of the complete coprime Mellin family

The complete coprime family is unconditionally summable precisely when each exponent has real
part greater than one. Necessity already follows from its two prime-coordinate subfamilies;
sufficiency is the existing absolutely convergent coprime-pair theorem.

This classifies the literal infinite family. It does not classify an ordered cutoff or a
renormalized continuation, and its boundary supplies no zeta-zero location theorem.
-/

noncomputable section

namespace RHTower

/-- The exact domain of ordinary unconditional summability, detected by the two prime rays. -/
theorem summable_visibleCoprimeMellinTerm_iff (s t : ℂ) :
    Summable (visibleCoprimeMellinTerm s t) ↔ 1 < s.re ∧ 1 < t.re := by
  constructor
  · intro h
    let row : Nat.Primes → ThetaCuspPrimitiveDirection := fun p =>
      ⟨(⟨(p : ℕ), p.property.pos⟩, 1),
        PNat.coprime_coe.mp ((Nat.coprime_one_right_iff _).mpr True.intro)⟩
    let col : Nat.Primes → ThetaCuspPrimitiveDirection := fun p =>
      ⟨(1, ⟨(p : ℕ), p.property.pos⟩),
        PNat.coprime_coe.mp ((Nat.coprime_one_left_iff _).mpr True.intro)⟩
    have hrow : Function.Injective row := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg (fun d : ThetaCuspPrimitiveDirection => (d.1.1 : ℕ)) hpq
    have hcol : Function.Injective col := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg (fun d : ThetaCuspPrimitiveDirection => (d.1.2 : ℕ)) hpq
    have hs : Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖) := by
      simpa [row, visibleCoprimeMellinTerm, positiveDirichletTerm] using
        (h.comp_injective hrow).norm
    have ht : Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-t)‖) := by
      simpa [col, visibleCoprimeMellinTerm, positiveDirichletTerm] using
        (h.comp_injective hcol).norm
    exact ⟨(GaloisForLFunctions.RHTower.summable_norm_primeCpow_neg_iff s).mp hs,
      (GaloisForLFunctions.RHTower.summable_norm_primeCpow_neg_iff t).mp ht⟩
  · rintro ⟨hs, ht⟩
    exact summable_visibleCoprimeMellinTerm s t hs ht

end RHTower
