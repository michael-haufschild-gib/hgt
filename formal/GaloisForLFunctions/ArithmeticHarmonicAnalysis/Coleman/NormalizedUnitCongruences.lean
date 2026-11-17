import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.FormalLogarithmicJets
import GaloisForLFunctions.HTGeometry.GomesNormalizedFormalLogEquiv
import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm

/-!
# Integral congruences in the normalized formal-unit group

Integral division-series units map to the existing complex normalized-unit
group. Their positive logarithmic jets are integral multiples of the division
level. This retains arithmetic content after extending coefficients to `ℂ`,
where ordinary ring divisibility alone would be vacuous.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman
open PowerSeries
open GaloisForLFunctions.HTGeometry.GammaFactorialFock

private theorem map_invariantDerivative {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : R⟦X⟧) :
    PowerSeries.map f (Formal.invariantDerivative g) =
      Formal.invariantDerivative (PowerSeries.map f g) := by
  simp only [Formal.invariantDerivative, map_mul, map_add, map_one, PowerSeries.map_X,
    GaloisForLFunctions.map_powerSeriesDerivative]

private theorem map_iterate_invariantDerivative {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : R⟦X⟧) (k : ℕ) :
    PowerSeries.map f ((Formal.invariantDerivative^[k]) g) =
      (Formal.invariantDerivative^[k]) (PowerSeries.map f g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      map_invariantDerivative, ih]

private theorem map_jet {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : R⟦X⟧) (k : ℕ) :
    f (Formal.jet k g) = Formal.jet k (PowerSeries.map f g) := by
  unfold Formal.jet
  rw [← map_iterate_invariantDerivative]
  rfl

/-- An integral division-series unit as a member of the existing normalized group. -/
def integralNormalizedUnit (n : ℕ) (g : ℤ⟦X⟧) : gomesNormalizedFormalUnitGroup :=
  ⟨Units.map (PowerSeries.map (Int.castRingHom ℂ)).toMonoidHom (Formal.congruenceUnit n g), by
    rw [gomesNormalizedFormalUnitGroup_mem_iff]
    change constantCoeff (PowerSeries.map (Int.castRingHom ℂ)
      (Formal.congruenceUnit n g : ℤ⟦X⟧)) = 1
    simp [Formal.coe_congruenceUnit, Formal.divisionSeries]⟩

private theorem integralNormalizedUnit_logarithmicJet (n k : ℕ) (g : ℤ⟦X⟧) :
    Formal.logarithmicJet k (integralNormalizedUnit n g).val =
      ((Formal.logarithmicJet k (Formal.congruenceUnit n g) : ℤ) : ℂ) := by
  change Formal.jet k (Formal.logarithmicDerivative (integralNormalizedUnit n g).val) =
    (Int.castRingHom ℂ) (Formal.jet k (Formal.logarithmicDerivative (Formal.congruenceUnit n g)))
  rw [map_jet]
  congr 1
  change Formal.invariantDerivative
      (PowerSeries.map (Int.castRingHom ℂ) (Formal.congruenceUnit n g : ℤ⟦X⟧)) *
      PowerSeries.map (Int.castRingHom ℂ) ((Formal.congruenceUnit n g)⁻¹ : ℤ⟦X⟧ˣ) =
    PowerSeries.map (Int.castRingHom ℂ)
      (Formal.invariantDerivative (Formal.congruenceUnit n g : ℤ⟦X⟧) *
        ((Formal.congruenceUnit n g)⁻¹ : ℤ⟦X⟧ˣ))
  rw [map_mul, map_invariantDerivative]

/-- Each complex logarithmic jet is an integral multiple of the congruence level. -/
theorem integralNormalizedUnit_logarithmicJet_integral (n k : ℕ) (g : ℤ⟦X⟧) :
    ∃ z : ℤ, Formal.logarithmicJet k (integralNormalizedUnit n g).val =
      (n : ℂ) * (z : ℂ) := by
  obtain ⟨z, hz⟩ := Formal.dvd_logarithmicJet_congruenceUnit n k g
  refine ⟨z, ?_⟩
  rw [integralNormalizedUnit_logarithmicJet]
  exact_mod_cast hz

/-- The first logarithmic jet gives the exact congruence level times the initial coefficient. -/
theorem Formal.logarithmicJet_zero_congruenceUnit {R : Type*} [CommRing R]
    (n : ℕ) (g : R⟦X⟧) :
    Formal.logarithmicJet 0 (Formal.congruenceUnit n g) = (n : R) * constantCoeff g := by
  have hc : constantCoeff (((Formal.congruenceUnit n g)⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) = 1 := by
    have h := congrArg (constantCoeff : R⟦X⟧ →+* R)
      (show (Formal.congruenceUnit n g : R⟦X⟧) *
        (((Formal.congruenceUnit n g)⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) = 1 by simp)
    simpa [Formal.coe_congruenceUnit, Formal.divisionSeries] using h
  change constantCoeff (Formal.invariantDerivative (Formal.congruenceUnit n g : R⟦X⟧) *
    (((Formal.congruenceUnit n g)⁻¹ : R⟦X⟧ˣ) : R⟦X⟧)) = _
  rw [map_mul, hc, mul_one, Formal.coe_congruenceUnit, Formal.invariantDerivative_add,
    Formal.invariantDerivative_mul, Formal.invariantDerivative_divisionSeries]
  simp [Formal.invariantDerivative, Formal.divisionSeries]

/-- The first jet of the basic division unit is exactly `n`, so the congruence is sharp. -/
theorem Formal.logarithmicJet_zero_basicUnit (n : ℕ) :
    Formal.logarithmicJet 0 (Formal.congruenceUnit n (1 : ℤ⟦X⟧)) = (n : ℤ) := by
  rw [Formal.logarithmicJet_zero_congruenceUnit, map_one, mul_one]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.integralNormalizedUnit_logarithmicJet_integral

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.Formal.logarithmicJet_zero_basicUnit
