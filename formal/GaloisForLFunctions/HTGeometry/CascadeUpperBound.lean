import GaloisForLFunctions.HTGeometry.CascadeStateAlgebraic
import GaloisForLFunctions.HTGeometry.EntireCascadeStateFieldOrder

/-!
# The cascade order upper bound

A cascade of `n` transcendental entire constituents, each satisfying a first-order equation and each
consecutive pair of states algebraically independent over the constants, has differential order at
most `n`.

The states generate the field, their derivatives are algebraic over it by the edge relation, and the
transcendence-degree count does the rest.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- The domain of entire germs. -/
local instance cascadeUpperDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- The rational coordinate field inside the global meromorphic field. -/
local instance cascadeUpperRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

/-- The ordinary derivative as the differential structure on the global meromorphic field. -/
local instance cascadeUpperDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

variable {f : ℕ → ℂ → ℂ}

/-- The zeroth state is the coordinate. -/
theorem cascadeMero_zero (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) :
    cascadeMero hfan 0
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) RatFunc.X := by
  have hx : (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) RatFunc.X
      = ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ RatFunc.X := rfl
  have hfun : (fun z : ℂ => (Polynomial.X : Polynomial ℂ).eval z) = entireCascade f 0 := by
    funext z
    simp [entireCascade]
  rw [hx, ← RatFunc.algebraMap_X, ratfuncToMero_algebraMap_polynomial, polyToMero,
    RingHom.comp_apply, cascadeMero, analyticMeroElement]
  congr 1
  apply Subtype.ext
  exact congrArg (fun h : ℂ → ℂ => (Germ.coeRingHom (Filter.principal (Set.univ : Set ℂ)) h))
    hfun.symm

/-- The first algebraic jet of a state is the germ of its derivative. -/
theorem differentialJet_one_cascadeMero (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (j : ℕ) :
    differentialJet 1 (cascadeMero hfan j) = cascadeMeroDeriv hfan j := by
  rw [cascadeMero, differentialJet_analyticMeroElement isOpen_univ isPreconnected_univ
      Set.univ_nonempty, cascadeMeroDeriv, analyticMeroElement, analyticJetElement,
    analyticFunctionElement]
  congr 1
  apply Subtype.ext
  exact congrArg (fun h : ℂ → ℂ => (Germ.coeRingHom (Filter.principal (Set.univ : Set ℂ)) h))
    (iteratedDeriv_one (f := entireCascade f j))

/-! ## The state field of a cascade -/

/-- The states of a cascade of length `n`, as a family in the meromorphic field. -/
def cascadeStates (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) :
    Fin n → meroField (Set.univ : Set ℂ) :=
  fun i => cascadeMero hfan (i.1 + 1)

/-- Every state up to the length of the cascade lies in the generated field. -/
theorem cascadeMero_mem_adjoin (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n j : ℕ}
    (hj : j ≤ n) :
    cascadeMero hfan j
      ∈ IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n)) := by
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · rw [hj0, cascadeMero_zero hfan]
    exact IntermediateField.algebraMap_mem _ RatFunc.X
  · have hlt : j - 1 < n := by omega
    have hval : (j - 1) + 1 = j := by omega
    have hmem : cascadeStates hfan n ⟨j - 1, hlt⟩ = cascadeMero hfan j := by
      show cascadeMero hfan ((j - 1) + 1) = cascadeMero hfan j
      rw [hval]
    rw [← hmem]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_range_self _)

/-- **The derivatives of the states are algebraic over the state field.** -/
theorem cascadeMeroDeriv_mem_algebraicClosure (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {n : ℕ}
    (hft : ∀ k, k < n → TranscendentalEntire (f k))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hindep : ∀ k, k < n →
      PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k + 1))) :
    ∀ j, j ≤ n → cascadeMeroDeriv hfan j ∈
      algebraicClosure
        ((IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n)) : Type))
        (meroField (Set.univ : Set ℂ)) := by
  intro j
  induction j with
  | zero =>
      intro _
      rw [cascadeMeroDeriv_zero hfan]
      exact one_mem _
  | succ k ih =>
      intro hk
      refine cascadeMeroDeriv_succ_mem_algebraicClosure hfan (hft k (by omega))
        (h1 k (by omega)) _ (cascadeMero_mem_adjoin hfan (by omega))
        (cascadeMero_mem_adjoin hfan hk) (ih (by omega)) (hindep k (by omega))

/-- **The cascade order upper bound.**  A cascade of `n` transcendental entire constituents with
first-order equations and algebraically independent consecutive states satisfies an algebraic
differential equation of order at most `n`. -/
theorem differentiallyAlgebraicOfOrder_entireCascade
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hft : ∀ k, k < n → TranscendentalEntire (f k))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hindep : ∀ k, k < n →
      PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k + 1))) :
    DifferentiallyAlgebraicOfOrder (entireCascade f n) n := by
  have hderiv := cascadeMeroDeriv_mem_algebraicClosure hfan hft h1 hindep
  refine differentiallyAlgebraicOfOrder_of_algebraic_state_derivatives
    (analyticOnNhd_entireCascade hfan n) (cascadeStates hfan n) ?_ ?_
  · rintro y ⟨i, rfl⟩
    have hjet : (cascadeStates hfan n i)′ = cascadeMeroDeriv hfan (i.1 + 1) := by
      rw [cascadeStates]
      have := differentialJet_one_cascadeMero hfan (i.1 + 1)
      rw [differentialJet_succ, differentialJet_zero] at this
      exact this
    rw [hjet]
    exact hderiv (i.1 + 1) (by omega)
  · exact cascadeMero_mem_adjoin hfan (le_refl n)

/-- **The cascade order upper bound, with no independence hypothesis.**  Transcendental entire
constituents with first-order equations suffice: consecutive states are automatically independent. -/
theorem differentiallyAlgebraicOfOrder_entireCascade_of_transcendental
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    DifferentiallyAlgebraicOfOrder (entireCascade f n) n :=
  differentiallyAlgebraicOfOrder_entireCascade hfan (fun k _ => hall k) h1
    (fun k _ => pairAlgIndep_of_transcendental hfan hall k)

end

end GaloisForLFunctions.HTGeometry
