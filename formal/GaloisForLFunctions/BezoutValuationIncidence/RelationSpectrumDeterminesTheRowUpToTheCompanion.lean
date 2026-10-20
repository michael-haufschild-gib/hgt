import GaloisForLFunctions.BezoutValuationIncidence.ParsevalForTranslatedMomentArrays
import GaloisForLFunctions.BiScaleUncertainty.SieveAffineTranslationAnchoring

/-!
# The relation spectrum determines the row up to the companion translation

The degree-`m` relation spectrum of a row is the family of products `Π_i Y(ord ζ_i)` over
zero-product `m`-tuples of response frequencies. Parseval over shift vectors makes it equivalent to
the full array of degree-`m` translated moments. In one direction the moments are finite exponential
sums of the relation coefficients. In the other, the mean-square moment difference is `P^m` times the
energy of the coefficient difference.

The translated moments of degrees five and six determine a row up to one explicit companion, the
reflection by the canonical half period that flips the top dyadic layer. Combining the two:

**Two rows have the same relation spectra in degrees five and six — equivalently in all degrees —
iff they agree on `[1, N]` or one is the companion of the other.**

Apart from this single half-period translation, no row is invisible to its relation spectrum. The
Galois action is already absorbed, since `Y` depends on a frequency only through its order.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Equal degree-`m` relation spectra. -/
def SameRelationSpectrum (N m : ℕ) (c e : ℕ → ℝ) : Prop :=
  ∀ ζ ∈ zeroProductTuples N m, relationCoeff N c ζ = relationCoeff N e ζ

/-- **Relation spectrum ⟺ translated moments, at each degree.** -/
theorem sameRelationSpectrum_iff_translatedMoment (N m : ℕ) (c e : ℕ → ℝ) :
    SameRelationSpectrum N m c e ↔
      ∀ v : Fin m → ℕ, SieveMoments.translatedMoment N c v = SieveMoments.translatedMoment N e v := by
  constructor
  · intro h v
    have hc := translatedMoment_eq_sum_relationCoeff N c v
    have he := translatedMoment_eq_sum_relationCoeff N e v
    have hsum : ∑ ζ ∈ zeroProductTuples N m, (relationCoeff N c ζ : ℂ) * ∏ i, ζ i ^ v i =
        ∑ ζ ∈ zeroProductTuples N m, (relationCoeff N e ζ : ℂ) * ∏ i, ζ i ^ v i :=
      sum_congr rfl fun ζ hζ => by rw [h ζ hζ]
    exact_mod_cast hc.trans (hsum.trans he.symm)
  · intro h
    have hpars := sum_sq_translatedMoment_sub_eq N m c e
    have hzero : ∑ v ∈ Fintype.piFinset (fun _ : Fin m => range N.factorial),
        (SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N e v) ^ 2 = 0 :=
      sum_eq_zero fun v _ => by rw [h v, sub_self, sq, mul_zero]
    rw [hzero] at hpars
    have hP : (0 : ℝ) < (N.factorial : ℝ) ^ m := by positivity
    have hsum0 : ∑ ζ ∈ zeroProductTuples N m, (relationCoeff N c ζ - relationCoeff N e ζ) ^ 2 = 0 := by
      have := hpars.symm
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hP.ne'
      · exact h0
    intro ζ hζ
    have h0 := (sum_eq_zero_iff_of_nonneg fun ζ _ => sq_nonneg _).mp hsum0 ζ hζ
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h0
    linarith

/-- **The relation spectrum determines the row up to the companion.** -/
theorem sameRelationSpectrum_five_six_iff (N : ℕ) (c e : ℕ → ℝ) :
    (SameRelationSpectrum N 5 c e ∧ SameRelationSpectrum N 6 c e) ↔
      (∀ d ∈ Icc 1 N, e d = c d) ∨
        (∀ d ∈ Icc 1 N, e d = SieveMoments.ValuationPhase.companion N c d) := by
  rw [sameRelationSpectrum_iff_translatedMoment, sameRelationSpectrum_iff_translatedMoment]
  exact SieveMoments.ValuationPhase.fifth_sixth_eq_iff N c e

/-- Equal relation spectra in every degree have the same classification. -/
theorem sameRelationSpectrum_all_iff (N : ℕ) (c e : ℕ → ℝ) :
    (∀ m, SameRelationSpectrum N m c e) ↔
      (∀ d ∈ Icc 1 N, e d = c d) ∨
        (∀ d ∈ Icc 1 N, e d = SieveMoments.ValuationPhase.companion N c d) := by
  constructor
  · intro h
    exact (sameRelationSpectrum_five_six_iff N c e).mp ⟨h 5, h 6⟩
  · intro h m
    rw [sameRelationSpectrum_iff_translatedMoment]
    exact (SieveMoments.ValuationPhase.all_translated_eq_iff_fifth_sixth N c e).mpr
      ((SieveMoments.ValuationPhase.fifth_sixth_eq_iff N c e).mpr h) m

end

end GaloisForLFunctions.BezoutValuationIncidence
