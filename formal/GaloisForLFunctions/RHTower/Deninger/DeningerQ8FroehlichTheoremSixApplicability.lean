import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualBiquadraticDiscriminant
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualMaximalAbelianField
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8FroehlichFiniteSign

/-!
# Applicability certificate for Fröhlich Theorem 6(i)

Fröhlich's root-number identity `W_N = α_K β_K` requires that `K` be the
maximal abelian subfield of the quaternion extension and that every rational
prime dividing `disc(K)` be `1 mod 4`.  It does not require `disc(N)` to be
odd; that extra condition appears only in the theorem's normal-basis formulas.

This leaf packages all source-side hypotheses for the literal SST field and
the already computed value `α_K β_K = -1`.  It deliberately does not call the
finite sign an Artin root number: formalizing Fröhlich's independent global
epsilon-factor identity remains the final bridge.
-/

namespace RHTower

noncomputable section

local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance deningerQ8FroehlichTheoremSixApplicabilityLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective

noncomputable local instance deningerQ8FroehlichTheoremSixApplicabilityLocalInst2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis

noncomputable local instance deningerQ8FroehlichTheoremSixApplicabilityLocalInst3 : NumberField K2 := NumberField.mk

/-- The literal SST quaternion field satisfies every arithmetic hypothesis
of Fröhlich Theorem 6(i), and its finite formula side is `-1`. -/
theorem deningerQ8_froehlichTheoremSix_i_applicability :
    (deningerQ8ActualBiquadraticField =
      IntermediateField.fixedField
        (commutator Gal(deningerQ8RootNumberNegOneTopField/ℚ))) ∧
    (∀ (p : ℕ), p.Prime →
      (p : ℤ) ∣ NumberField.discr K2 → p % 4 = 1) ∧
    deningerQ8FroehlichFiniteSign = -1 := by
  exact ⟨deningerQ8ActualBiquadraticField_eq_fixedField_commutator,
    fun p hp hpd => q8Biquad_prime_dvd_discr_mod_four_eq_one p hp hpd,
    deningerQ8FroehlichFiniteSign_eq_neg_one⟩

end

end RHTower
