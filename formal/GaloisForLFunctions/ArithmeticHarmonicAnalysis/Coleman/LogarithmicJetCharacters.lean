import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.FormalLogarithmicJets

/-!
# Logarithmic jets as integral characters

Positive logarithmic jets turn multiplication of formal units into addition.
Consequently the division-series congruence holds relative to every base
unit, giving the difference-of-logarithms mechanism of Goto–Ishii,
Lemma 5.3, without constructing rational logarithm series.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal
open PowerSeries
variable {R : Type*} [CommRing R]

theorem jet_add (k : ℕ) (f g : R⟦X⟧) : jet k (f + g) = jet k f + jet k g := by
  have hi : (invariantDerivative^[k]) (f + g) =
      (invariantDerivative^[k]) f + (invariantDerivative^[k]) g := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, invariantDerivative_add,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
  simp only [jet, hi, map_add]

/-- The integral logarithmic derivative is additive on products of units. -/
theorem logarithmicDerivative_mul (u v : R⟦X⟧ˣ) :
    logarithmicDerivative (u * v) = logarithmicDerivative u + logarithmicDerivative v := by
  simp only [logarithmicDerivative, Units.val_mul, invariantDerivative_mul, mul_inv_rev]
  calc
    _ = logarithmicDerivative u * ((v : R⟦X⟧) * ((v⁻¹ : R⟦X⟧ˣ) : R⟦X⟧)) +
        logarithmicDerivative v * ((u : R⟦X⟧) * ((u⁻¹ : R⟦X⟧ˣ) : R⟦X⟧)) := by
      unfold logarithmicDerivative
      ring
    _ = _ := by simp [logarithmicDerivative]

/-- Every positive logarithmic jet is an additive character of the formal-unit group. -/
theorem logarithmicJet_mul (k : ℕ) (u v : R⟦X⟧ˣ) :
    logarithmicJet k (u * v) = logarithmicJet k u + logarithmicJet k v := by
  simp only [logarithmicJet, logarithmicDerivative_mul, jet_add]

/-- Division-series perturbations preserve every logarithmic jet modulo the division level. -/
theorem dvd_logarithmicJet_perturbation (n k : ℕ) (u : R⟦X⟧ˣ) (g : R⟦X⟧) :
    (n : R) ∣ logarithmicJet k (u * congruenceUnit n g) - logarithmicJet k u := by
  rw [logarithmicJet_mul, add_sub_cancel_left]
  exact dvd_logarithmicJet_congruenceUnit n k g

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal.logarithmicJet_mul
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal.dvd_logarithmicJet_perturbation
