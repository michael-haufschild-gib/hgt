import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.DifferentialOrder

/-!
# The jet bridge with the order preserved

The backward direction of the jet bridge produces *some* algebraic differential equation.  The order
statement of a composition law needs more: a field relation among the first `n+1` jets must descend
to a pointwise equation of order at most `n`.

Nothing analytic changes — the same clearing of denominators and the same inverse jet reshaping — but
the jet index is supplied rather than extracted, so the arity of the resulting polynomial is fixed by
the relation instead of by an existential.

This is what turns a transcendence-degree bound in the meromorphic differential field into the
corpus's `DifferentiallyAlgebraicOfOrder`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

variable {U : Set ℂ}

/-- **The backward bridge, with the order kept.**  A nonzero polynomial relation among the first
`n+1` algebraic jets of the meromorphic realization descends to a nonzero pointwise algebraic
differential equation of order at most `n`. -/
theorem exists_relation_of_jet_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {n : ℕ}
    {Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ)} (hQ0 : Q ≠ 0)
    (hQ :
      letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      letI := meroFieldDifferential hUo hUc hUne
      MvPolynomial.aeval
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) Q = 0) :
    ∃ P : MvPolynomial (Fin (n + 2)) ℂ, P ≠ 0 ∧
      ∀ z ∈ U, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0 := by
  classical
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  set G : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) := clearRatFuncCoefficients Q with hGdef
  have hG0 : G ≠ 0 := clearRatFuncCoefficients_ne_zero Q hQ0
  have hfield : MvPolynomial.eval₂ (polyToMero U)
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) G = 0 := by
    have hmapG : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G =
        MvPolynomial.C ((algebraMap (Polynomial ℂ) (RatFunc ℂ))
          (ratFuncCommonDenominator Q)) * Q := map_clearRatFuncCoefficients Q
    have hQ' : MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) (meroField U))
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) Q = 0 := by
      rw [← MvPolynomial.aeval_def]
      exact hQ
    calc
      MvPolynomial.eval₂ (polyToMero U)
          (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) G =
          MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) (meroField U))
            (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf))
            (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G) := by
          rw [MvPolynomial.eval₂_map]
          rw [polyToMero_eq_comp hUo hUc hUne hUinf]
          rfl
      _ = 0 := by
          rw [hmapG, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hQ', mul_zero]
  have hmap : algebraMap (analyticSubring U) (meroField U)
      (MvPolynomial.eval₂ (polyToAnalytic U)
        (fun j : Fin (n + 1) => analyticJetElement f hf (j : ℕ)) G) = 0 := by
    rw [MvPolynomial.eval₂_comp_right, MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ (polyToMero U)
      (fun j : Fin (n + 1) => algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ))) G = 0
    rw [show (fun j : Fin (n + 1) => algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ))) =
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) by
      funext j
      exact (differentialJet_analyticMeroElement hUo hUc hUne f hf (j : ℕ)).symm]
    exact hfield
  have hanalytic : MvPolynomial.eval₂ (polyToAnalytic U)
      (fun j : Fin (n + 1) => analyticJetElement f hf (j : ℕ)) G = 0 :=
    (IsFractionRing.injective (analyticSubring U) (meroField U)) (by simpa using hmap)
  have hpoint := (eval₂_analyticJetElement_eq_zero_iff f hf G).mp hanalytic
  refine ⟨reshapeJetInv n G, ?_, ?_⟩
  · exact fun hzero => hG0 (reshapeJetInv_injective n (by simpa using hzero))
  · intro z hz
    have hre : reshapeJet n (reshapeJetInv n G) = G :=
      RingHom.congr_fun (reshapeJet_comp_reshapeJetInv n) G
    have hev := hpoint z hz
    rw [← hre, eval₂_reshapeJet] at hev
    exact hev

/-- **The global order bridge.**  An entire function whose meromorphic realization satisfies a
nonzero polynomial relation among its first `n+1` algebraic jets satisfies an algebraic differential
equation of order at most `n`. -/
theorem differentiallyAlgebraicOfOrder_of_jet_relation {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) {n : ℕ}
    {Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ)} (hQ0 : Q ≠ 0)
    (hQ :
      letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
        isPreconnected_univ Set.univ_nonempty
      letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
        (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ).toAlgebra
      letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
        Set.univ_nonempty
      MvPolynomial.aeval
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) Q = 0) :
    DifferentiallyAlgebraicOfOrder f n := by
  obtain ⟨P, hP, hrel⟩ := exists_relation_of_jet_relation isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hf hQ0 hQ
  exact ⟨P, hP, fun z => hrel z (Set.mem_univ z)⟩

end

end GaloisForLFunctions.HTGeometry
