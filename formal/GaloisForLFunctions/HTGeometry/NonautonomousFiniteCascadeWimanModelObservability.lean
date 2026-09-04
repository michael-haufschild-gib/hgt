import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeWimanSlopeClearing

/-!
# Unconditional observability of the exact finite Wiman initial model

This module realizes every chosen finite-cascade Wiman initial law as its literal signed Hahn
monomial.  The denominator-cleared charge inequalities then feed the full output-jet theorem,
giving algebraic independence of the complete raw jet block without genericity or omitted higher
terms.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions HahnSeries

noncomputable section

/-- A literal Hahn monomial regarded in the Hahn fraction field. -/
noncomputable def hahnFractionSingleBase
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (d : Γ) (c : K) : HahnFraction Γ K :=
  algebraMap (HahnSeries Γ K) (HahnFraction Γ K) (HahnSeries.single d c)

theorem hahnFractionSingleBase_hasLeadAt
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (d : Γ) (c : K) :
    FracHasLeadAt (hahnFractionSingleBase d c) d c := by
  apply FracHasLeadAt.of_hahn
  constructor
  · intro k hk
    rw [HahnSeries.coeff_single]
    simp [ne_of_lt hk]
  · rw [HahnSeries.coeff_single]
    simp

/-- Exact signed Wiman initial velocity model attached to the actual cascade's chosen initial
data. -/
noncomputable def nonautonomousFiniteCascadeWimanModelVelocity
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (n + 1)) : HahnFraction (mgDeg (n + 1)) ℂ :=
  hahnFractionSingleBase
    (mgRamWimanVelocityDegree
      (nonautonomousFiniteCascadeWimanRamification hall h1)
      (nonautonomousFiniteCascadeWimanTail hall h1) j)
    (nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder hall h1 j)

theorem nonautonomousFiniteCascadeWimanModelVelocity_hasLeadAt
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (n + 1)) :
    FracHasLeadAt
      (nonautonomousFiniteCascadeWimanModelVelocity hall h1 j)
      (mgRamWimanVelocityDegree
        (nonautonomousFiniteCascadeWimanRamification hall h1)
        (nonautonomousFiniteCascadeWimanTail hall h1) j)
      (nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder hall h1 j) :=
  hahnFractionSingleBase_hasLeadAt _ _

/-- **Reduction-II capstone.**  For every finite family of transcendental entire order-one ADE
layers, its exact prescribed Wiman initial monomial cascade has a full algebraically independent
raw output-jet block. -/
theorem algebraicIndependent_nonautonomousFiniteCascadeWimanModelOutputJets
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) =>
        ((hahnFractionRamCascadeDerivationBase ℂ
            (nonautonomousFiniteCascadeWimanRamification hall h1)
            (nonautonomousFiniteCascadeWimanModelVelocity hall h1) :
              HahnFraction (mgDeg (n + 1)) ℂ →
                HahnFraction (mgDeg (n + 1)) ℂ)^[(j : ℕ)])
          (hahnFractionRamCoordinateBase ℂ
            (nonautonomousFiniteCascadeWimanRamification hall h1) 0)) := by
  exact algebraicIndependent_hahnFractionRamCascadeOutputJetsBase_wiman
    (nonautonomousFiniteCascadeWimanRamification hall h1)
    (nonautonomousFiniteCascadeWimanRamification_pos hall h1)
    (nonautonomousFiniteCascadeWimanTail hall h1)
    (nonautonomousFiniteCascadeWimanChargesPositive hall h1)
    (nonautonomousFiniteCascadeWimanModelVelocity hall h1)
    (nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder hall h1)
    (nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder_ne_zero hall h1)
    (nonautonomousFiniteCascadeWimanModelVelocity_hasLeadAt hall h1)

end

end GaloisForLFunctions.HTGeometry
