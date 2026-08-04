import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.CascadeEdgeRelation

/-!
# The cascade in the meromorphic function field

The states of a cascade and their derivatives, as elements of the global meromorphic function field,
and the edge relation read there.

A pointwise identity between analytic functions is an identity between their germs, so the transfer
needs no analytic continuation — only that the realization is additive and multiplicative.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

variable {U : Set ℂ}

/-- **A pointwise vanishing sum vanishes in the field.** -/
theorem analyticMeroElement_sum_eq_zero {ι : Type*} (s : Finset ι) (G : ι → ℂ → ℂ)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) U) (h : ∀ z, ∑ i ∈ s, G i z = 0) :
    ∑ i ∈ s, analyticMeroElement (G i) (hG i) = (0 : meroField U) := by
  have hpi : (fun z => ∑ i ∈ s, G i z) = ∑ i ∈ s, G i := by
    funext z
    rw [Finset.sum_apply]
  have hsum : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, G i z) U := by
    rw [hpi]
    exact Finset.sum_induction G (fun h => AnalyticOnNhd ℂ h U)
      (fun a b ha hb => ha.add hb) analyticOnNhd_const (fun i _ => hG i)
  rw [← analyticMeroElement_finsetSum s G hG hsum]
  refine Eq.trans (analyticMeroElement_congr hsum analyticOnNhd_const ?_)
    (analyticMeroElement_zero U)
  funext z
  exact h z

/-! ## The states -/

variable {f : ℕ → ℂ → ℂ}

/-- A cascade state as an element of the global meromorphic function field. -/
def cascadeMero (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (j : ℕ) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (entireCascade f j) (analyticOnNhd_entireCascade hfan j)

/-- The derivative of a cascade state as an element of the field. -/
def cascadeMeroDeriv (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (j : ℕ) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (deriv (entireCascade f j))
    (analyticOnNhd_entireCascade hfan j).deriv

/-- The two-element family of consecutive states. -/
def cascadeVec (f : ℕ → ℂ → ℂ) (k : ℕ) : Fin 2 → ℂ → ℂ :=
  ![entireCascade f k, entireCascade f (k + 1)]

theorem cascadeVec_analytic (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ) :
    ∀ i : Fin 2, AnalyticOnNhd ℂ (cascadeVec f k i) (Set.univ : Set ℂ) := by
  intro i
  fin_cases i
  · exact analyticOnNhd_entireCascade hfan k
  · exact analyticOnNhd_entireCascade hfan (k + 1)

theorem cascadeVec_apply (f : ℕ → ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (fun i : Fin 2 => cascadeVec f k i z)
      = ![entireCascade f k z, entireCascade f (k + 1) z] := by
  funext i
  fin_cases i <;> rfl

theorem analyticMeroElement_cascadeVec (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ) :
    (fun i : Fin 2 => analyticMeroElement (cascadeVec f k i) (cascadeVec_analytic hfan k i))
      = ![cascadeMero hfan k, cascadeMero hfan (k + 1)] := by
  funext i
  fin_cases i
  · rfl
  · rfl

/-- The coefficient of the edge relation, as an element of the field. -/
theorem analyticMeroElement_edgeCoeff (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ)
    (B : MvPolynomial (Fin 2) ℂ)
    (hB : AnalyticOnNhd ℂ (fun z => MvPolynomial.eval
      ![entireCascade f k z, entireCascade f (k + 1) z] B) (Set.univ : Set ℂ)) :
    analyticMeroElement (fun z => MvPolynomial.eval
        ![entireCascade f k z, entireCascade f (k + 1) z] B) hB
      = MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ))
          ![cascadeMero hfan k, cascadeMero hfan (k + 1)] B := by
  have hfun : (fun z => MvPolynomial.eval
      (fun i : Fin 2 => cascadeVec f k i z) B)
      = fun z => MvPolynomial.eval
          ![entireCascade f k z, entireCascade f (k + 1) z] B := by
    funext z
    rw [cascadeVec_apply]
  have hbase := analyticMeroElement_eval_mvPolynomial (cascadeVec f k)
    (cascadeVec_analytic hfan k) B
  rw [analyticMeroElement_cascadeVec hfan k] at hbase
  rw [← hbase]
  exact analyticMeroElement_congr _ _ hfun.symm

/-! ## The edge relation in the field -/

/-- One term of the edge relation, transferred. -/
theorem analyticMeroElement_edgeTerm (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ)
    (B : MvPolynomial (Fin 2) ℂ) (c d : ℕ)
    (h : AnalyticOnNhd ℂ (fun z =>
      MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] B
        * (deriv (entireCascade f (k + 1)) z) ^ c
        * (deriv (entireCascade f k) z) ^ d) (Set.univ : Set ℂ)) :
    analyticMeroElement (fun z =>
        MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] B
          * (deriv (entireCascade f (k + 1)) z) ^ c
          * (deriv (entireCascade f k) z) ^ d) h
      = MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ))
            ![cascadeMero hfan k, cascadeMero hfan (k + 1)] B
          * (cascadeMeroDeriv hfan (k + 1)) ^ c * (cascadeMeroDeriv hfan k) ^ d := by
  have hcoeff : AnalyticOnNhd ℂ (fun z =>
      MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] B)
      (Set.univ : Set ℂ) := by
    have hbase := analyticOnNhd_eval_mvPolynomial (cascadeVec f k)
      (cascadeVec_analytic hfan k) B
    have hfun : (fun z => MvPolynomial.eval (fun i : Fin 2 => cascadeVec f k i z) B)
        = fun z => MvPolynomial.eval
            ![entireCascade f k z, entireCascade f (k + 1) z] B := by
      funext z
      rw [cascadeVec_apply]
    rwa [hfun] at hbase
  have hup : AnalyticOnNhd ℂ (fun z => (deriv (entireCascade f (k + 1)) z) ^ c)
      (Set.univ : Set ℂ) := ((analyticOnNhd_entireCascade hfan (k + 1)).deriv).pow c
  have hlow : AnalyticOnNhd ℂ (fun z => (deriv (entireCascade f k) z) ^ d)
      (Set.univ : Set ℂ) := ((analyticOnNhd_entireCascade hfan k).deriv).pow d
  rw [analyticMeroElement_mul (hcoeff.mul hup) hlow,
    analyticMeroElement_mul hcoeff hup,
    analyticMeroElement_pow ((analyticOnNhd_entireCascade hfan (k + 1)).deriv) c,
    analyticMeroElement_pow ((analyticOnNhd_entireCascade hfan k).deriv) d,
    analyticMeroElement_edgeCoeff hfan k B hcoeff]
  rfl

/-- **The edge relation, in the meromorphic function field.**  Two consecutive states and their
derivatives satisfy a polynomial relation whose coefficients are polynomials in the states, of
positive degree in the new state's derivative. -/
theorem exists_cascade_edge_relation_mero {k : ℕ}
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hft : TranscendentalEntire (f k))
    (h1 : DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∃ (e : ℕ) (B : ℕ → MvPolynomial (Fin 2) ℂ), 1 ≤ e ∧ B e ≠ 0 ∧
      ∑ c ∈ Finset.range (e + 1),
          MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ))
              ![cascadeMero hfan k, cascadeMero hfan (k + 1)] (B c)
            * (cascadeMeroDeriv hfan (k + 1)) ^ c
            * (cascadeMeroDeriv hfan k) ^ (e - c) = 0 := by
  obtain ⟨e, B, he, hBe, hrel⟩ := exists_cascade_edge_relation_of_forall hfan hft h1
  refine ⟨e, B, he, hBe, ?_⟩
  set G : ℕ → ℂ → ℂ := fun c z =>
    MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] (B c)
      * (deriv (entireCascade f (k + 1)) z) ^ c
      * (deriv (entireCascade f k) z) ^ (e - c) with hG
  have hGan : ∀ c : ℕ, AnalyticOnNhd ℂ (G c) (Set.univ : Set ℂ) := by
    intro c
    have hcoeff : AnalyticOnNhd ℂ (fun z =>
        MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] (B c))
        (Set.univ : Set ℂ) := by
      have hbase := analyticOnNhd_eval_mvPolynomial (cascadeVec f k)
        (cascadeVec_analytic hfan k) (B c)
      have hfun : (fun z => MvPolynomial.eval (fun i : Fin 2 => cascadeVec f k i z) (B c))
          = fun z => MvPolynomial.eval
              ![entireCascade f k z, entireCascade f (k + 1) z] (B c) := by
        funext z
        rw [cascadeVec_apply]
      rwa [hfun] at hbase
    exact (hcoeff.mul (((analyticOnNhd_entireCascade hfan (k + 1)).deriv).pow c)).mul
      (((analyticOnNhd_entireCascade hfan k).deriv).pow (e - c))
  have hzero := analyticMeroElement_sum_eq_zero (Finset.range (e + 1)) G hGan hrel
  rw [← hzero]
  refine Finset.sum_congr rfl ?_
  intro c _
  exact (analyticMeroElement_edgeTerm hfan k (B c) c (e - c) (hGan c)).symm

end

end GaloisForLFunctions.HTGeometry
