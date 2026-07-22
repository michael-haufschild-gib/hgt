import GaloisForLFunctions.RHTower.PrimeCoherenceHalfDensityFiniteReservoirUniversalityLaw
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.PolynomialFirstOrderActivationBoundary

/-!
# Prime-coherence filtered circuit-activation universality

One coherent continuum-rank prime family simultaneously survives every nonzero finite-reservoir
differential filter.  Each filtered output then has two universal source boundaries: any
scalar-aware finite differential circuit contains a genuinely hypertranscendental atom, and any
polynomial first-order activation law is driven by a hypertranscendental latent input.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- **Filtered circuit-activation universality law.**  Every coherence neighborhood of the
positive prime pointing contains a continuum-rank, uniquely positive-definite family whose every
nonzero finite-reservoir differential observation forces both finite-circuit and polynomial-law
hypertranscendental sources. -/
theorem exists_orderPointedContinuumPrimeFilteredCircuitActivationUniversality
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      DifferentialIndependent finitePrimeRationalCoefficientField
        (fun xa : (ℕ → Bool) × ℕ =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2) ∧
      Algebra.trdeg finitePrimeRationalCoefficientField
        (differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range fun z : ℕ → Bool =>
            signedPrimeNaturalShiftPalette
              (continuumSparsePrimeOrientation (fun _ => false) e z) 0)) =
        Cardinal.continuum ∧
      (∀ z, (∑' p,
        (booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e z) p -
          booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (fun _ => false) p) ^ 2) < eta ^ 2) ∧
      (∀ z w, (∑' p,
        (booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e z) p -
          booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e w) p) ^ 2) < eta ^ 2) ∧
      (∀ epsilon : Nat.Primes → Bool,
        PositiveDefiniteOnReal (signedPrimeVerticalTrace epsilon x) ↔
          epsilon = fun _ => false) ∧
      ∀ z (S : IntermediateField ℂ arithmeticFunctionRationalCoordinateField),
        DerivationClosed S →
        Algebra.trdeg ℂ S < Cardinal.aleph0 →
        ∀ c : (Unit × ℕ) →₀ S, c ≠ 0 →
          let y := finsuppLinearDifferentialObservation S c
            (signedPrimeNaturalShiftPalette
              (continuumSparsePrimeOrientation (fun _ => false) e z) 0)
          HypertranscendentalOver ℂ y ∧
            (∀ Atom : arithmeticFunctionRationalCoordinateField → Prop,
              FiniteDifferentialCircuit
                (BaseScalarOrAtom ℂ arithmeticFunctionRationalCoordinateField Atom) y →
              ∃ a : arithmeticFunctionRationalCoordinateField,
                Atom a ∧ HypertranscendentalOver ℂ a) ∧
            ∀ h : arithmeticFunctionRationalCoordinateField,
              ∀ P : Polynomial (differentialAdjoin ℂ
                ({h} : Set arithmeticFunctionRationalCoordinateField)),
                y′ = Polynomial.eval₂
                  (algebraMap
                    (differentialAdjoin ℂ
                      ({h} : Set arithmeticFunctionRationalCoordinateField))
                    arithmeticFunctionRationalCoordinateField) y P →
                  HypertranscendentalOver ℂ h := by
  obtain ⟨e, hdiff, htrdeg, hbase, hpair, hpd, hfilter⟩ :=
    exists_orderPointedContinuumPrimeHalfDensityFiniteReservoirUniversality
      sigma eta x hsigma heta hx
  refine ⟨e, hdiff, htrdeg, hbase, hpair, hpd, ?_⟩
  intro z S hS hSfinite c hc
  let y := finsuppLinearDifferentialObservation S c
    (signedPrimeNaturalShiftPalette
      (continuumSparsePrimeOrientation (fun _ => false) e z) 0)
  have hy : HypertranscendentalOver ℂ y := by
    simpa only [y] using hfilter z S hS hSfinite c hc
  refine ⟨hy, ?_, ?_⟩
  · intro Atom hcircuit
    letI : Differential ℂ := ⟨0⟩
    letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
      ⟨fun c => by
        rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
        change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
        rw [map_zero]⟩
    letI : CharZero arithmeticFunctionRationalCoordinateField :=
      charZero_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
    exact exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hy hcircuit
  · intro h P hrel
    letI : Differential ℂ := ⟨0⟩
    letI : DifferentialAlgebra ℂ arithmeticFunctionRationalCoordinateField :=
      ⟨fun c => by
        rw [arithmeticFunctionRationalCoordinateField_deriv_complexConstant]
        change 0 = algebraMap ℂ arithmeticFunctionRationalCoordinateField 0
        rw [map_zero]⟩
    letI : CharZero arithmeticFunctionRationalCoordinateField :=
      charZero_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective ℂ arithmeticFunctionRationalCoordinateField)
    exact hypertranscendentalOver_input_of_polynomial_firstOrder_output hy P hrel

end

end RHTower
