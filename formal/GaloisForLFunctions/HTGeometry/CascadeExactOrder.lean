import GaloisForLFunctions.HTGeometry.CascadeUpperBound

/-!
# The unit-cost law for first-order entire cascades

Both halves together: a cascade of `n` transcendental entire constituents with first-order equations,
algebraically independent consecutive states, and algebraically independent first `n` jets of the
last state, has differential order exactly `n`.

The upper bound is the transcendence-degree count on the state field; the lower bound is jet
independence read through the forward jet bridge.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- The domain of entire germs. -/
local instance cascadeExactDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- The rational coordinate field inside the global meromorphic field. -/
local instance cascadeExactRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

/-- The ordinary derivative as the differential structure on the global meromorphic field. -/
local instance cascadeExactDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

variable {f : ℕ → ℂ → ℂ}

/-- **The order lower bound for a cascade.**  Independence of the first `n` jets of the last state
forbids every equation of order below `n`. -/
theorem not_differentiallyAlgebraicOfOrder_entireCascade_of_jets
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hjets : AlgebraicIndependent (RatFunc ℂ)
      (fun j : Fin n => differentialJet (j : ℕ) (cascadeMero hfan n)))
    {m : ℕ} (hm : m < n) :
    ¬ DifferentiallyAlgebraicOfOrder (entireCascade f n) m := by
  have hle : m + 1 ≤ n := hm
  have hcomp : (fun j : Fin (m + 1) => differentialJet (j : ℕ) (cascadeMero hfan n))
      = (fun j : Fin n => differentialJet (j : ℕ) (cascadeMero hfan n)) ∘ Fin.castLE hle := by
    funext j
    rfl
  have hsub : AlgebraicIndependent (RatFunc ℂ)
      (fun j : Fin (m + 1) => differentialJet (j : ℕ) (cascadeMero hfan n)) := by
    rw [hcomp]
    exact hjets.comp _ (Fin.castLE_injective hle)
  exact not_differentiallyAlgebraicOfOrder_of_algebraicIndependent_jets
    (analyticOnNhd_entireCascade hfan n) hsub

/-- **The unit-cost law.**  A cascade of `n` transcendental entire constituents, each satisfying a
first-order algebraic differential equation, with algebraically independent consecutive states and
algebraically independent first `n` jets of the last state, has exact differential order `n`. -/
theorem exactDifferentialOrder_entireCascade
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hft : ∀ k, k < n → TranscendentalEntire (f k))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hindep : ∀ k, k < n →
      PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k + 1)))
    (hjets : AlgebraicIndependent (RatFunc ℂ)
      (fun j : Fin n => differentialJet (j : ℕ) (cascadeMero hfan n))) :
    ExactDifferentialOrder (entireCascade f n) n := by
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade hfan hft h1 hindep, ?_⟩
  intro m hm
  exact not_differentiallyAlgebraicOfOrder_entireCascade_of_jets hfan hjets hm

/-- **The unit-cost law, with the state independence discharged.**  A cascade of transcendental
entire constituents with first-order equations has exact differential order `n` as soon as the first
`n` jets of the last state are independent — which by `algebraicIndependent_jets_iff` is precisely the
lower bound itself. -/
theorem exactDifferentialOrder_entireCascade_of_transcendental
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hjets : AlgebraicIndependent (RatFunc ℂ)
      (fun j : Fin n => differentialJet (j : ℕ) (cascadeMero hfan n))) :
    ExactDifferentialOrder (entireCascade f n) n :=
  exactDifferentialOrder_entireCascade hfan (fun k _ => hall k) h1
    (fun k _ => pairAlgIndep_of_transcendental hfan hall k) hjets

/-! ## The length-one case is unconditional

For a cascade of length one the jet hypothesis is the statement that the single constituent is not
algebraic, which its transcendence already gives.  So the capstone's hypothesis class is inhabited by
every transcendental entire solution of a first-order equation. -/

/-- **The unit-cost law at length one, with no residual hypothesis.** -/
theorem exactDifferentialOrder_entireCascade_one
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : DifferentiallyAlgebraicOfOrder (f 0) 1) :
    ExactDifferentialOrder (entireCascade f 1) 1 := by
  refine exactDifferentialOrder_entireCascade_of_transcendental hfan hall
    (fun k hk => by
      have : k = 0 := by omega
      rw [this]
      exact h1) ?_
  exact (algebraicIndependent_jets_iff (analyticOnNhd_entireCascade hfan 1) (n := 0)).mpr
    (not_differentiallyAlgebraicOfOrder_zero_of_transcendental (hall 0).1 (hall 0).2)

/-- **The exponential tower of length one.** -/
theorem exactDifferentialOrder_expCascade_one :
    ExactDifferentialOrder (entireCascade (fun _ : ℕ => Complex.exp) 1) 1 := by
  have hfan : ∀ i : ℕ, AnalyticOnNhd ℂ ((fun _ : ℕ => Complex.exp) i) (Set.univ : Set ℂ) :=
    fun _ => DifferentiableOn.analyticOnNhd
      (fun z _ => (Complex.differentiable_exp z).differentiableWithinAt) isOpen_univ
  exact exactDifferentialOrder_entireCascade_one hfan (fun _ => transcendentalEntire_exp)
    differentiallyAlgebraicOfOrder_one_exp

end

end GaloisForLFunctions.HTGeometry
