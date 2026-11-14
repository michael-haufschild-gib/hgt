import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Ramification divisibility for a radical equation

For Dedekind extensions, a relation `z^N=a` forces `N` to divide the
ramification index times the valuation order of `a`. Integer logarithms
of the normalized adic valuations handle both zeros and poles.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain

variable {A K B L : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
variable [Algebra A B] [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

/-- A radical degree divides the ramified logarithmic valuation of its right-hand side. -/
theorem radical_ramification_log_dvd (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (N : ℕ) (z : L) (a : K)
    (heq : z ^ N = algebraMap K L a) :
    (N : ℤ) ∣ (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * (v.valuation K a).log := by
  have h := congrArg (w.valuation L) heq
  rw [map_pow, ← HeightOneSpectrum.valuation_liesOver L v w] at h
  have hl := congrArg WithZero.log h
  simp only [WithZero.log_pow, nsmul_eq_mul] at hl
  exact ⟨(w.valuation L z).log, hl.symm⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
