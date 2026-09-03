import GaloisForLFunctions.HTGeometry.NonautonomousFinitePuiseuxAnalyticComponent

/-!
# Wiman components for every layer of a finite actual cascade

For a finite cascade of transcendental entire first-order differential-algebraic functions, this
module chooses the exact irreducible Wiman package at every layer and identifies the actual
constituent velocity with an algebraic point of that package over its adjacent rational state
field.  The resulting minimum polynomial divides the exact Wiman derivative polynomial.  Thus
every later valuation or Puiseux realization must select a conjugate of the actual analytic
component; it cannot replace that component by an unrelated root.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- Canonical chosen exact Wiman initial data for every layer of a finite actual cascade. -/
noncomputable def nonautonomousFiniteCascadeWimanData
    {f : ℕ → ℂ → ℂ} {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) : EntireFirstOrderWimanInitialData (f k) :=
  Classical.choice (exists_entireFirstOrderWimanInitialData (hall k) (h1 k k.isLt))

/-- The chosen layer slope has the exact positive Wiman charge. -/
theorem nonautonomousFiniteCascadeWimanData_charge_pos
    {f : ℕ → ℂ → ℂ} {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) :
    0 < ((nonautonomousFiniteCascadeWimanData hall h1 k).slope : ℝ) + 1 :=
  (nonautonomousFiniteCascadeWimanData hall h1 k).charge_pos

/-- The chosen layer edge coefficient is nonzero. -/
theorem nonautonomousFiniteCascadeWimanData_root_ne_zero
    {f : ℕ → ℂ → ℂ} {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) :
    (nonautonomousFiniteCascadeWimanData hall h1 k).root ≠ 0 :=
  (nonautonomousFiniteCascadeWimanData hall h1 k).root_ne_zero

/-- The actual velocity at every layer lies on its chosen exact irreducible Wiman component inside
the one common finite branch field. -/
theorem nonautonomousFiniteCascadeVelocity_chosen_component_root
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) :
    ((firstOrderDerivativePolynomial
        (nonautonomousFiniteCascadeWimanData hall h1 k).P).map
      (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toRingHom).IsRoot
        (nonautonomousFiniteCascadeLocalJet hfan k 2) :=
  nonautonomousFiniteCascadeVelocity_component_root hfan hall k
    (nonautonomousFiniteCascadeWimanData hall h1 k)

/-- The actual velocity is algebraic over its literal adjacent rational state field. -/
theorem nonautonomousFiniteCascadeVelocity_isAlgebraic_localState
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) :
    letI : Algebra FirstOrderRationalStateField
        (NonautonomousFiniteCascadeBranchField hfan N) :=
      (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toAlgebra
    IsAlgebraic FirstOrderRationalStateField
      (nonautonomousFiniteCascadeLocalJet hfan k 2) := by
  let data := nonautonomousFiniteCascadeWimanData hall h1 k
  let p := firstOrderDerivativePolynomial data.P
  letI : Algebra FirstOrderRationalStateField
      (NonautonomousFiniteCascadeBranchField hfan N) :=
    (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toAlgebra
  refine ⟨p, ?_, ?_⟩
  · exact (firstOrderDerivativePolynomial_irreducible data).ne_zero
  · rw [Polynomial.aeval_def]
    change Polynomial.eval₂
      (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k)
      (nonautonomousFiniteCascadeLocalJet hfan k 2) p = 0
    rw [← Polynomial.eval_map]
    exact nonautonomousFiniteCascadeVelocity_chosen_component_root hfan hall h1 k

/-- The actual layer minimum polynomial divides the exact chosen Wiman derivative polynomial.
This is the conjugacy bridge required by a valuation-compatible branch realization. -/
theorem minpoly_nonautonomousFiniteCascadeVelocity_dvd_wimanDerivativePolynomial
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) :
    letI : Algebra FirstOrderRationalStateField
        (NonautonomousFiniteCascadeBranchField hfan N) :=
      (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toAlgebra
    minpoly FirstOrderRationalStateField
        (nonautonomousFiniteCascadeLocalJet hfan k 2) ∣
      firstOrderDerivativePolynomial
        (nonautonomousFiniteCascadeWimanData hall h1 k).P := by
  letI : Algebra FirstOrderRationalStateField
      (NonautonomousFiniteCascadeBranchField hfan N) :=
    (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toAlgebra
  apply minpoly.dvd FirstOrderRationalStateField
  rw [Polynomial.aeval_def]
  change Polynomial.eval₂
    (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k)
    (nonautonomousFiniteCascadeLocalJet hfan k 2)
      (firstOrderDerivativePolynomial
        (nonautonomousFiniteCascadeWimanData hall h1 k).P) = 0
  rw [← Polynomial.eval_map]
  exact nonautonomousFiniteCascadeVelocity_chosen_component_root hfan hall h1 k

/-- The actual analytic component has, up to a scalar unit, exactly the chosen irreducible Wiman
derivative polynomial as its minimum polynomial.  In particular the Wiman edge root belongs to
the same conjugacy class as the actual constituent velocity. -/
theorem minpoly_nonautonomousFiniteCascadeVelocity_associated_wimanDerivativePolynomial
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (k : Fin N) :
    letI : Algebra FirstOrderRationalStateField
        (NonautonomousFiniteCascadeBranchField hfan N) :=
      (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toAlgebra
    Associated
      (minpoly FirstOrderRationalStateField
        (nonautonomousFiniteCascadeLocalJet hfan k 2))
      (firstOrderDerivativePolynomial
        (nonautonomousFiniteCascadeWimanData hall h1 k).P) := by
  letI : Algebra FirstOrderRationalStateField
      (NonautonomousFiniteCascadeBranchField hfan N) :=
    (nonautonomousFiniteCascadeLocalRationalStateEval hfan hall k).toAlgebra
  have halg : IsAlgebraic FirstOrderRationalStateField
      (nonautonomousFiniteCascadeLocalJet hfan k 2) :=
    nonautonomousFiniteCascadeVelocity_isAlgebraic_localState hfan hall h1 k
  have hint : IsIntegral FirstOrderRationalStateField
      (nonautonomousFiniteCascadeLocalJet hfan k 2) :=
    isAlgebraic_iff_isIntegral.mp halg
  exact (minpoly.irreducible hint).associated_of_dvd
    (firstOrderDerivativePolynomial_irreducible
      (nonautonomousFiniteCascadeWimanData hall h1 k))
    (minpoly_nonautonomousFiniteCascadeVelocity_dvd_wimanDerivativePolynomial
      hfan hall h1 k)

end

end GaloisForLFunctions.HTGeometry
