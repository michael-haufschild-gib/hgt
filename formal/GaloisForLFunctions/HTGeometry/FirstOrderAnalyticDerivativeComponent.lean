import GaloisForLFunctions.HTGeometry.FirstOrderStateEvaluation
import GaloisForLFunctions.HTGeometry.CascadeStateAlgebraic
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Actual analytic root of the irreducible first-order derivative component

For a transcendental entire first-order differential-algebraic function, the coordinate and the
function germ are algebraically independent.  Their polynomial evaluation therefore embeds the
literal state ring `ℂ[U][V]`, extends to `ℂ(U,V)`, and sends the irreducible derivative
polynomial to a polynomial annihilating the actual derivative germ.  This selects the analytic
component without an auxiliary compatibility assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped UnivMeroFieldInstances

noncomputable section

/-- Coordinate, function, and first derivative as an entire three-coordinate family. -/
noncomputable def firstOrderEntireJetFunctions (f : ℂ → ℂ) : Fin 3 → ℂ → ℂ :=
  Fin.cons id (fun j : Fin 2 ↦ iteratedDeriv (j : ℕ) f)

theorem firstOrderEntireJetFunctions_analytic
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    ∀ i : Fin 3, AnalyticOnNhd ℂ (firstOrderEntireJetFunctions f i) Set.univ := by
  intro i
  refine Fin.cases analyticOnNhd_id ?_ i
  intro j
  fin_cases j
  · simpa [firstOrderEntireJetFunctions] using hf
  · change AnalyticOnNhd ℂ (iteratedDeriv 1 f) Set.univ
    rw [iteratedDeriv_one]
    exact hf.deriv

theorem transcendentalEntire_analyticOnNhd
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    AnalyticOnNhd ℂ f Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr hf.1

/-- Global meromorphic realization of the coordinate, function, and derivative. -/
noncomputable def firstOrderAnalyticJet
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    Fin 3 → meroField (Set.univ : Set ℂ) :=
  fun i ↦ analyticMeroElement (firstOrderEntireJetFunctions f i)
    (firstOrderEntireJetFunctions_analytic hf i)

/-- The exact pointwise Wiman relation annihilates the global analytic jet. -/
theorem firstOrderAnalyticJet_relation
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (data : EntireFirstOrderWimanInitialData f) :
    MvPolynomial.aeval (firstOrderAnalyticJet f hf) data.P = 0 := by
  have htransfer := analyticMeroElement_eval_mvPolynomial
    (firstOrderEntireJetFunctions f) (firstOrderEntireJetFunctions_analytic hf) data.P
  have hfun :
      (fun z ↦ MvPolynomial.eval
        (fun i ↦ firstOrderEntireJetFunctions f i z) data.P) =
        (fun _ ↦ (0 : ℂ)) := by
    funext z
    have hvec : (fun i ↦ firstOrderEntireJetFunctions f i z) =
        Fin.cons z (fun j : Fin 2 ↦ iteratedDeriv (j : ℕ) f z) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rfl
      · rfl
    rw [hvec, data.relation z]
  have hleft :
      analyticMeroElement
          (fun z ↦ MvPolynomial.eval
            (fun i ↦ firstOrderEntireJetFunctions f i z) data.P)
          (analyticOnNhd_eval_mvPolynomial
            (firstOrderEntireJetFunctions f)
            (firstOrderEntireJetFunctions_analytic hf) data.P) = 0 := by
    rw [analyticMeroElement_congr _ analyticOnNhd_const hfun,
      analyticMeroElement_zero]
  rw [hleft] at htransfer
  rw [MvPolynomial.aeval_def]
  change MvPolynomial.eval₂ (constToMero Set.univ)
    (firstOrderAnalyticJet f hf) data.P = 0
  exact htransfer.symm

/-- No nonzero bivariate complex polynomial annihilates the coordinate and transcendental entire
function germs. -/
theorem pairAlgIndep_firstOrderAnalyticJet
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    PairAlgIndep
      (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 0)
      (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 1) := by
  intro P hP hzero
  refine not_differentiallyAlgebraicOfOrder_zero_of_transcendental hf.1 hf.2
    ⟨P, hP, ?_⟩
  have hfunctions : ∀ i : Fin 2,
      AnalyticOnNhd ℂ ((![id, f] : Fin 2 → ℂ → ℂ) i) Set.univ := by
    intro i
    fin_cases i
    · exact analyticOnNhd_id
    · exact transcendentalEntire_analyticOnNhd hf
  have hbase := analyticMeroElement_eval_mvPolynomial
    (![id, f] : Fin 2 → ℂ → ℂ) hfunctions P
  have hvec :
      (fun i : Fin 2 ↦ analyticMeroElement
        ((![id, f] : Fin 2 → ℂ → ℂ) i) (hfunctions i)) =
      ![firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 0,
        firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, hzero] at hbase
  have hpt := (analyticMeroElement_eq_zero_iff _).mp hbase
  intro z
  have hz := hpt z (Set.mem_univ z)
  have hvec : (![z, f z] : Fin 2 → ℂ) =
      Fin.cons z (fun j : Fin 1 ↦ iteratedDeriv (j : ℕ) f z) := by
    funext i
    fin_cases i <;> simp [iteratedDeriv_zero]
  rw [← hvec]
  have hpoint : (fun i : Fin 2 ↦ (![id, f] : Fin 2 → ℂ → ℂ) i z) =
      (![z, f z] : Fin 2 → ℂ) := by
    funext i
    fin_cases i <;> rfl
  rw [← hpoint]
  exact hz

/-- Algebraic independence of the actual clock/value state, in the exact subtype indexing used by
the derivative split. -/
theorem algebraicIndependent_firstOrderAnalyticState
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    AlgebraicIndependent ℂ
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦
        firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) j.1) := by
  have hpair : AlgebraicIndependent ℂ
      (![firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 0,
        firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 1] :
          Fin 2 → meroField (Set.univ : Set ℂ)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    intro P Q hPQ
    by_contra hne
    have hsub : P - Q ≠ 0 := sub_ne_zero.mpr hne
    apply pairAlgIndep_firstOrderAnalyticJet hf (P - Q) hsub
    change MvPolynomial.aeval
      (![firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 0,
        firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 1] :
          Fin 2 → meroField (Set.univ : Set ℂ)) (P - Q) = 0
    rw [map_sub, hPQ, sub_self]
  have hcomp := hpair.comp firstOrderStateIndexEquiv
    firstOrderStateIndexEquiv.injective
  have hfamily :
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦
        firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) j.1) =
      ((![firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 0,
        firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 1] :
          Fin 2 → meroField (Set.univ : Set ℂ)) ∘ firstOrderStateIndexEquiv) := by
    funext j
    rcases j with ⟨j, hj⟩
    fin_cases j
    · rfl
    · rfl
    · exact (hj rfl).elim
  rw [hfamily]
  exact hcomp

/-- The actual clock/value polynomial evaluation is injective. -/
theorem firstOrderAnalyticStatePolynomialEval_injective
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    Function.Injective (firstOrderStatePolynomialEval
      (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf))) :=
  firstOrderStatePolynomialEval_injective_of_algebraicIndependent _
    (algebraicIndependent_firstOrderAnalyticState hf)

/-- Canonical embedding of the rational clock/value state field into the global meromorphic
field. -/
noncomputable def firstOrderAnalyticRationalStateEval
    {f : ℂ → ℂ} (hf : TranscendentalEntire f) :
    FirstOrderRationalStateField →ₐ[ℂ] meroField (Set.univ : Set ℂ) :=
  firstOrderRationalStateEval
    (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf))
    (firstOrderAnalyticStatePolynomialEval_injective hf)

/-- **Actual irreducible derivative component.**  The actual derivative germ is a root of the
image of the irreducible Wiman derivative polynomial over the literal rational state field. -/
theorem firstOrderAnalyticDerivative_component_root
    {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    (data : EntireFirstOrderWimanInitialData f) :
    ((firstOrderDerivativePolynomial data.P).map
      (firstOrderAnalyticRationalStateEval hf).toRingHom).IsRoot
        (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 2) := by
  change Polynomial.eval
    (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf) 2)
      ((firstOrderDerivativePolynomial data.P).map
        (firstOrderAnalyticRationalStateEval hf).toRingHom) = 0
  rw [Polynomial.eval_map]
  exact (firstOrderDerivativePolynomial_eval
    (firstOrderAnalyticJet f (transcendentalEntire_analyticOnNhd hf))
    (firstOrderAnalyticStatePolynomialEval_injective hf) data.P).trans
      (firstOrderAnalyticJet_relation (transcendentalEntire_analyticOnNhd hf) data)

end

end GaloisForLFunctions.HTGeometry
