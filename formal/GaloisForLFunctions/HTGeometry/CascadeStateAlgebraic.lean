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

/-! ## The first edge is free

The zeroth state is the coordinate, so independence of the first pair says exactly that the first
constituent is not algebraic over the coordinate — which is the order-zero theorem. -/

/-- **The coordinate and a transcendental entire function are independent.** -/
theorem pairAlgIndep_zero (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hft : TranscendentalEntire (f 0)) :
    PairAlgIndep (cascadeMero hfan 0) (cascadeMero hfan 1) := by
  intro P hP0 hzero
  refine not_differentiallyAlgebraicOfOrder_zero_of_transcendental hft.1 hft.2 ⟨P, hP0, ?_⟩
  have hbase := analyticMeroElement_eval_mvPolynomial (cascadeVec f 0)
    (cascadeVec_analytic hfan 0) P
  rw [analyticMeroElement_cascadeVec hfan 0, hzero] at hbase
  have hpt := (analyticMeroElement_eq_zero_iff _).mp hbase
  intro z
  have hz := hpt z (Set.mem_univ z)
  rw [cascadeVec_apply] at hz
  have hvec : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) (f 0) z)
      = ![entireCascade f 0 z, entireCascade f 1 z] := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [entireCascade]
    · rw [Fin.cons_succ]
      fin_cases i
      simp [entireCascade, iteratedDeriv_zero]
  rw [hvec]
  exact hz

/-! ## Every edge is free

The state `F_k` is a nonconstant entire function, so its image contains a nonempty open set.  A
polynomial relation between `F_k` and `F_{k+1} = f_k ∘ F_k` therefore forces the same relation
between the coordinate and `f_k` on that open set, hence everywhere. -/

/-- A transcendental entire function is nonconstant. -/
theorem exists_ne_of_transcendentalEntire {g : ℂ → ℂ} (hg : TranscendentalEntire g) :
    ∃ w₀ w₁ : ℂ, g w₀ ≠ g w₁ := by
  by_contra hcon
  refine hg.2 ⟨Polynomial.C (g 0), fun z => ?_⟩
  rw [Polynomial.eval_C]
  by_contra hne
  exact hcon ⟨z, 0, hne⟩

/-- **Consecutive states are always independent.**  No Clunie--Steinmetz input is needed: a
polynomial relation between two consecutive states would make the constituent algebraic. -/
theorem pairAlgIndep_of_transcendental (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (k : ℕ) :
    PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k + 1)) := by
  intro P hP0 hzero
  have hnc : ∀ i : ℕ, ∃ w₀ w₁ : ℂ, f i w₀ ≠ f i w₁ :=
    fun i => exists_ne_of_transcendentalEntire (hall i)
  -- the relation holds pointwise along the state
  have hbase := analyticMeroElement_eval_mvPolynomial (cascadeVec f k)
    (cascadeVec_analytic hfan k) P
  rw [analyticMeroElement_cascadeVec hfan k, hzero] at hbase
  have hpt := (analyticMeroElement_eq_zero_iff _).mp hbase
  -- the corresponding entire function of the argument
  have hg2an : ∀ i : Fin 2, AnalyticOnNhd ℂ ((![id, f k] : Fin 2 → ℂ → ℂ) i)
      (Set.univ : Set ℂ) := by
    intro i
    fin_cases i
    · exact analyticOnNhd_id
    · exact hfan k
  have hGan : AnalyticOnNhd ℂ
      (fun w => MvPolynomial.eval (fun i : Fin 2 => (![id, f k] : Fin 2 → ℂ → ℂ) i w) P)
      (Set.univ : Set ℂ) :=
    analyticOnNhd_eval_mvPolynomial (![id, f k] : Fin 2 → ℂ → ℂ) hg2an P
  have hGval : ∀ z : ℂ, MvPolynomial.eval
      (fun i : Fin 2 => (![id, f k] : Fin 2 → ℂ → ℂ) i (entireCascade f k z)) P = 0 := by
    intro z
    have h := hpt z (Set.mem_univ z)
    rw [cascadeVec_apply] at h
    have hvec : (fun i : Fin 2 => (![id, f k] : Fin 2 → ℂ → ℂ) i (entireCascade f k z))
        = ![entireCascade f k z, entireCascade f (k + 1) z] := by
      funext i
      fin_cases i
      · rfl
      · rfl
    rw [hvec]
    exact h
  -- the state is an open map
  have hFan : AnalyticOnNhd ℂ (entireCascade f k) (Set.univ : Set ℂ) :=
    analyticOnNhd_entireCascade hfan k
  have hFnc : ∃ z₀ z₁ : ℂ, entireCascade f k z₀ ≠ entireCascade f k z₁ :=
    exists_ne_entireCascade hfan hnc k
  have hopen : IsOpenMap (entireCascade f k) := by
    rcases hFan.is_constant_or_isOpenMap with hc | ho
    · exfalso
      obtain ⟨w, hw⟩ := hc
      obtain ⟨z₀, z₁, hz⟩ := hFnc
      exact hz ((hw z₀).trans (hw z₁).symm)
    · exact ho
  have hUopen : IsOpen (entireCascade f k '' Set.univ) := hopen Set.univ isOpen_univ
  have hmem : entireCascade f k 0 ∈ entireCascade f k '' Set.univ := ⟨0, Set.mem_univ 0, rfl⟩
  have hev : (fun w => MvPolynomial.eval
      (fun i : Fin 2 => (![id, f k] : Fin 2 → ℂ → ℂ) i w) P)
      =ᶠ[nhds (entireCascade f k 0)] 0 := by
    filter_upwards [hUopen.mem_nhds hmem] with w hw
    obtain ⟨z, _, hz⟩ := hw
    simp only [Pi.zero_apply]
    rw [← hz]
    exact hGval z
  have heq := hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ _) hev
  -- hence the constituent satisfies an order-zero equation
  refine not_differentiallyAlgebraicOfOrder_zero_of_transcendental (hall k).1 (hall k).2
    ⟨P, hP0, ?_⟩
  intro w
  have hw := heq (Set.mem_univ w)
  have hvec : (Fin.cons w fun j : Fin 1 => iteratedDeriv (j : ℕ) (f k) w)
      = fun i : Fin 2 => (![id, f k] : Fin 2 → ℂ → ℂ) i w := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [Fin.cons_succ]
      fin_cases i
      simp [iteratedDeriv_zero]
  rw [hvec]
  simpa using hw

end

end GaloisForLFunctions.HTGeometry
