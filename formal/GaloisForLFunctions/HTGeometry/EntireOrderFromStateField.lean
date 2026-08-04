import GaloisForLFunctions.HTGeometry.AnalyticJetOrderBridge
import GaloisForLFunctions.HTGeometry.ScalarDifferentialOrderUpperBound

/-!
# A bounded state field caps the differential order of an entire function

The abstract order bound says that `n+1` jets inside an intermediate field of transcendence degree
`n` are algebraically dependent.  Read through the jet bridge, this becomes a statement about
functions: an entire function whose first `n+1` derivative germs lie in a state field of
transcendence degree at most `n` over `ℂ(z)` satisfies an algebraic differential equation of order at
most `n`.

The state field is where a composition law supplies its content — for a cascade of `n` first-order
constituents the states themselves generate it — and the transcendence-degree count is the only thing
the order bound ever needs about them.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-! ## The abstract dependence of jets -/

/-- **Jets in a bounded field are dependent.**  If the first `n+1` jets of `x` lie in an intermediate
field of transcendence degree at most `n`, a nonzero polynomial in `n+1` variables over the base
annihilates them. -/
theorem exists_jet_relation_of_trdeg_le
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (M : IntermediateField K L) {x : L} {n : ℕ}
    (htr : Algebra.trdeg K M ≤ (n : Cardinal))
    (hjets : ∀ i : Fin (n + 1), differentialJet (i : ℕ) x ∈ M) :
    ∃ Q : MvPolynomial (Fin (n + 1)) K, Q ≠ 0 ∧
      MvPolynomial.aeval (fun i : Fin (n + 1) => differentialJet (i : ℕ) x) Q = 0 := by
  classical
  set y : Fin (n + 1) → M := fun i => ⟨differentialJet (i : ℕ) x, hjets i⟩ with hy
  have hdep : ¬ AlgebraicIndependent K y := not_algebraicIndependent_of_trdeg_le htr y
  rw [algebraicIndependent_iff_injective_aeval] at hdep
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q : MvPolynomial (Fin (n + 1)) K, Q ≠ 0 ∧
      MvPolynomial.aeval y Q = 0 := by
    obtain ⟨Q₁, Q₂, hEq, hne⟩ := Function.not_injective_iff.mp hdep
    exact ⟨Q₁ - Q₂, sub_ne_zero.mpr hne, by rw [map_sub, hEq, sub_self]⟩
  refine ⟨Q, hQ0, ?_⟩
  have h := MvPolynomial.comp_aeval_apply y M.val Q
  rw [hQ, map_zero] at h
  exact h.symm

/-! ## The entire-function form -/

/-- The domain of entire germs. -/
local instance entireAnalyticDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- The rational coordinate field inside the global meromorphic field. -/
local instance entireRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

/-- The ordinary derivative as the differential structure on the global meromorphic field. -/
local instance entireMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- **The order bound from a bounded state field.**  An entire function whose first `n+1` derivative
germs lie in an intermediate field of transcendence degree at most `n` over `ℂ(z)` satisfies an
algebraic differential equation of order at most `n`. -/
theorem differentiallyAlgebraicOfOrder_of_trdeg_le {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) {n : ℕ}
    (M : IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
    (htr : Algebra.trdeg (RatFunc ℂ) M ≤ (n : Cardinal))
    (hjets : ∀ i : Fin (n + 1),
      differentialJet (i : ℕ) (analyticMeroElement f hf) ∈ M) :
    DifferentiallyAlgebraicOfOrder f n := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_jet_relation_of_trdeg_le M htr hjets
  exact differentiallyAlgebraicOfOrder_of_jet_relation hf hQ0 hQ

end

end GaloisForLFunctions.HTGeometry
