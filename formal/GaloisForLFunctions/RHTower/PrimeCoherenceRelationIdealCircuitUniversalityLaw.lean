import GaloisForLFunctions.RHTower.PrimeCoherenceFilteredCircuitActivationUniversalityLaw

/-!
# Prime-coherence relation-ideal circuit universality

The continuum coherent prime family has no differential-polynomial equations over the finite-prime
rational coefficient field.  The same family remains universally source-rigid after every nonzero
finite-reservoir differential observation: exact finite circuits must expose a
hypertranscendental atom, and polynomial first-order laws must expose a hypertranscendental latent
input.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- **Prime-coherence relation-ideal circuit universality law.**  Every positive coherence
neighborhood contains a continuum family with trivial complete differential relation ideal over
the finite-prime rational coefficient field.  Simultaneously, all nonzero finite-reservoir
observations retain the finite-circuit and polynomial first-order hypertranscendental source
boundaries. -/
theorem exists_orderPointedContinuumPrimeRelationIdealCircuitUniversality
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      differentialRelationIdeal
          (C := finitePrimeRationalCoefficientField)
          (fun xa : (ℕ → Bool) × ℕ =>
            signedPrimeNaturalShiftPalette
              (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2) = ⊥ ∧
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
            (fun _ => false) p) ^ (2 : ℕ)) < eta ^ (2 : ℕ)) ∧
      (∀ z w, (∑' p,
        (booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e z) p -
          booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e w) p) ^ (2 : ℕ)) < eta ^ (2 : ℕ)) ∧
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
  obtain ⟨e, hdiff, hrest⟩ :=
    exists_orderPointedContinuumPrimeFilteredCircuitActivationUniversality
      sigma eta x hsigma heta hx
  refine ⟨e, ?_, hdiff, hrest⟩
  exact
    (differentialIndependent_iff_relationIdeal_eq_bot
      (fun xa : (ℕ → Bool) × ℕ =>
        signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2)).mp hdiff

end

end RHTower
