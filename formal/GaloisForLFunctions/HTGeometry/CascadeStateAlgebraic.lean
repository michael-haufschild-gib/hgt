import GaloisForLFunctions.HTGeometry.CascadeMeroField
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg

/-!
# The states' derivatives are algebraic over the state field

Reading the edge relation as a polynomial in the new state's derivative, its coefficients lie in the
relative algebraic closure of the state field as soon as the previous state's derivative does, and
its top coefficient is a nonzero polynomial in the two states.

The only input that is not formal is that the top coefficient does not vanish *as a field element* —
algebraic independence of the two consecutive states over the constants.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- The domain of entire germs. -/
local instance cascadeStateDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- The rational coordinate field inside the global meromorphic field. -/
local instance cascadeStateRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

/-- A pair of field elements is *independent over the constants* when no nonzero two-variable
complex polynomial annihilates it. -/
def PairAlgIndep (X Y : meroField (Set.univ : Set ℂ)) : Prop :=
  ∀ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 →
    MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ)) ![X, Y] P ≠ 0

/-- **The edge relation makes the new derivative algebraic.**  Given the relation, membership of the
two states in `E`, membership of the old derivative in the closure, and nonvanishing of the top
coefficient, the new derivative lies in the closure. -/
theorem mem_algebraicClosure_of_edge_relation
    (E : IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
    {X Y D T : meroField (Set.univ : Set ℂ)} {e : ℕ} {B : ℕ → MvPolynomial (Fin 2) ℂ}
    (hX : X ∈ E) (hY : Y ∈ E)
    (hT : T ∈ algebraicClosure ((E : Type)) (meroField (Set.univ : Set ℂ)))
    (htop : MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ)) ![X, Y] (B e) ≠ 0)
    (hrel : ∑ c ∈ Finset.range (e + 1),
      MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ)) ![X, Y] (B c) * D ^ c
        * T ^ (e - c) = 0) :
    D ∈ algebraicClosure ((E : Type)) (meroField (Set.univ : Set ℂ)) := by
  classical
  have hxy : ∀ i : Fin 2, (![X, Y] : Fin 2 → meroField (Set.univ : Set ℂ)) i ∈ E := by
    intro i
    fin_cases i
    · exact hX
    · exact hY
  have hEM : ∀ w : meroField (Set.univ : Set ℂ), w ∈ E →
      w ∈ algebraicClosure ((E : Type)) (meroField (Set.univ : Set ℂ)) := by
    intro w hw
    have := mem_algebraicClosure_restrictScalars_of_mem E hw
    rwa [IntermediateField.mem_restrictScalars] at this
  refine mem_algebraicClosure_of_root (e := e)
    (A := fun c => MvPolynomial.eval₂ (constToMero (Set.univ : Set ℂ)) ![X, Y] (B c)
      * T ^ (e - c)) ?_ ?_ ?_
  · intro c
    exact mul_mem (hEM _ (eval₂_constToMero_mem E _ hxy (B c))) (pow_mem hT (e - c))
  · rw [Nat.sub_self, pow_zero, mul_one]
    exact htop
  · rw [← hrel]
    refine Finset.sum_congr rfl ?_
    intro c _
    ring

/-! ## Along a cascade -/

variable {f : ℕ → ℂ → ℂ}

/-- The zeroth state's derivative is one. -/
theorem cascadeMeroDeriv_zero (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) :
    cascadeMeroDeriv hfan 0 = 1 := by
  have hid : deriv (entireCascade f 0) = fun _ : ℂ => (1 : ℂ) := by
    funext z
    simp [entireCascade]
  have hone : analyticMeroElement (fun _ : ℂ => (1 : ℂ)) analyticOnNhd_const
      = (1 : meroField (Set.univ : Set ℂ)) := by
    rw [analyticMeroElement_const, map_one]
  rw [cascadeMeroDeriv, ← hone]
  exact analyticMeroElement_congr _ _ hid

/-- **One step of the algebraicity induction.** -/
theorem cascadeMeroDeriv_succ_mem_algebraicClosure
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {k : ℕ}
    (hft : TranscendentalEntire (f k)) (h1 : DifferentiallyAlgebraicOfOrder (f k) 1)
    (E : IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
    (hX : cascadeMero hfan k ∈ E) (hY : cascadeMero hfan (k + 1) ∈ E)
    (hT : cascadeMeroDeriv hfan k ∈
      algebraicClosure ((E : Type)) (meroField (Set.univ : Set ℂ)))
    (hindep : PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k + 1))) :
    cascadeMeroDeriv hfan (k + 1) ∈
      algebraicClosure ((E : Type)) (meroField (Set.univ : Set ℂ)) := by
  obtain ⟨e, B, _, hBe, hrel⟩ := exists_cascade_edge_relation_mero hfan hft h1
  exact mem_algebraicClosure_of_edge_relation E hX hY hT (hindep (B e) hBe) hrel

end

end GaloisForLFunctions.HTGeometry
