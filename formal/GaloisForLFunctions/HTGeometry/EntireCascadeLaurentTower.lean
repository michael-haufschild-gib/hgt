import GaloisForLFunctions.HTGeometry.CascadeTowerStep
import GaloisForLFunctions.HTGeometry.FirstOrderRelationAbsoluteIrreducibility
import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalStateTranscendence
import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeWimanComponents
import GaloisForLFunctions.HTGeometry.CascadeExactOrder

/-!
# The Laurent tower of an entire first-order cascade

The finite branch fields `B_N = ℂ(z, F_1, …, F_N, F_0', …, F_N')` of a cascade of transcendental
entire functions with first-order equations form the tower `B_(N+1) = B_N(F_(N+1), v_(N+1))` of the
abstract tower step: the new state is transcendental over `B_N`, the new velocity
`v_(N+1) = f_N'(F_N)` satisfies the layer relation `P_N(F_N, F_(N+1), v_(N+1)) = 0`, which is
irreducible over `B_N(V)` by the absolute irreducibility of `P_N`, and `F_(N+1)' = F_N' v_(N+1)`.

The base `B_0 = ℂ(z)` has the model `ℂ(z)̄` with the extension of `d/dz`, and the layer-0 Wiman
lead is any nonzero root of the top symbol of `P_0` at `z`.
-/

open Polynomial IntermediateField

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

variable {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)

/-- The terminal state of the depth-`N` branch field. -/
abbrev cascadeTerminalState (N : ℕ) : NonautonomousFiniteCascadeBranchField hfan N :=
  nonautonomousFiniteCascadeStateInBranchField hfan N (Fin.last N)

/-- The terminal velocity `F_N'` of the depth-`N` branch field. -/
abbrev cascadeTerminalDeriv (N : ℕ) : NonautonomousFiniteCascadeBranchField hfan N :=
  nonautonomousFiniteCascadeDerivativeInBranchField hfan N (Fin.last N)

theorem cascadeBranchInclusionSucc_rat (N : ℕ) (r : RatFunc ℂ) :
    nonautonomousFiniteRatFuncToBranch hfan (N + 1) r =
      nonautonomousFiniteCascadeBranchInclusionSucc hfan N
        (nonautonomousFiniteRatFuncToBranch hfan N r) :=
  Subtype.ext rfl

theorem cascadeBranchInclusionSucc_deriv (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (x : NonautonomousFiniteCascadeBranchField hfan N) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeBranchInclusionSucc hfan N x) =
      nonautonomousFiniteCascadeBranchInclusionSucc hfan N
        (nonautonomousFiniteCascadeDerivation hfan hall
          (fun k hk => h1 k (Nat.lt_succ_of_lt hk)) x) := by
  refine Subtype.ext ?_
  calc ((nonautonomousFiniteCascadeDerivation hfan hall h1
          (nonautonomousFiniteCascadeBranchInclusionSucc hfan N x) :
            NonautonomousFiniteCascadeBranchField hfan (N + 1)) : meroField Set.univ)
      = ((nonautonomousFiniteCascadeBranchInclusionSucc hfan N x :
          NonautonomousFiniteCascadeBranchField hfan (N + 1)) : meroField Set.univ)′ :=
        nonautonomousFiniteCascadeDerivation_coe hfan hall h1 _
    _ = ((x : meroField Set.univ))′ := congrArg (fun y => y′) (IntermediateField.coe_inclusion _ x)
    _ = ((nonautonomousFiniteCascadeDerivation hfan hall
          (fun k hk => h1 k (Nat.lt_succ_of_lt hk)) x :
            NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ) :=
        (nonautonomousFiniteCascadeDerivation_coe hfan hall _ x).symm
    _ = _ := (IntermediateField.coe_inclusion _ _).symm

theorem cascadeTerminalState_deriv (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    nonautonomousFiniteCascadeDerivation hfan hall h1 (cascadeTerminalState hfan N) =
      cascadeTerminalDeriv hfan N :=
  nonautonomousFiniteCascadeDerivation_state hfan hall h1 (Fin.last N)

theorem cascadeTerminalStateSucc_deriv (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeTerminalStateSucc hfan N) =
      nonautonomousFiniteCascadeBranchInclusionSucc hfan N (cascadeTerminalDeriv hfan N) *
        nonautonomousFiniteCascadeTerminalVelocitySucc hfan N := by
  rw [nonautonomousFiniteCascadeTerminalDerivativeSucc hfan hall N]
  exact nonautonomousFiniteCascadeDerivation_state hfan hall h1 (Fin.last (N + 1))

/-- The terminal state is transcendental over `ℂ`. -/
theorem transcendental_cascadeTerminalState (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (N : ℕ) :
    Transcendental ℂ (cascadeTerminalState hfan N) :=
  (algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField hfan hall N).transcendental
    (Fin.last N)

/-- Evaluation of `ℂ(U)` at the terminal state. -/
def cascadeStateEval (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    RatFunc ℂ →+* NonautonomousFiniteCascadeBranchField hfan N :=
  (ratFuncEval (cascadeTerminalState hfan N) (transcendental_cascadeTerminalState hfan hall N) :
    RatFunc ℂ →+* NonautonomousFiniteCascadeBranchField hfan N)

theorem cascadeStateEval_algebraMap (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (p : Polynomial ℂ) :
    cascadeStateEval hfan hall N (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      aeval (cascadeTerminalState hfan N) p := by
  rw [cascadeStateEval, ← RingHom.comp_apply, ratFuncEval_comp_algebraMap]
  rfl

/-- **The layer relation in the branch tower.**  The new state and velocity satisfy the relation
of layer `N` over the included terminal state of depth `N`. -/
theorem cascade_layer_relation (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (data : EntireFirstOrderWimanInitialData (f N)) :
    ∑ i ∈ data.indexSupport, nonautonomousFiniteCascadeBranchInclusionSucc hfan N
        (aeval (cascadeTerminalState hfan N) (data.coeff i)) *
      nonautonomousFiniteCascadeTerminalStateSucc hfan N ^ i.1 *
      nonautonomousFiniteCascadeTerminalVelocitySucc hfan N ^ i.2 = 0 := by
  have hrel := nonautonomousFiniteCascadeLocalJet_relation hfan hall (Fin.last N) data
  have hjet : nonautonomousFiniteCascadeLocalJet hfan (Fin.last N) =
      fun j : Fin 3 => ![nonautonomousFiniteCascadeBranchInclusionSucc hfan N
          (cascadeTerminalState hfan N),
        nonautonomousFiniteCascadeTerminalStateSucc hfan N,
        nonautonomousFiniteCascadeTerminalVelocitySucc hfan N] j := by
    funext j
    fin_cases j
    · exact (nonautonomousFiniteCascadeBranchInclusionSucc_state hfan N (Fin.last N)).symm
    · rfl
    · change nonautonomousFiniteCascadeVelocityInBranchField hfan (Fin.last N).rev =
        nonautonomousFiniteCascadeTerminalVelocitySucc hfan N
      rw [Fin.rev_last]
      rfl
  rw [hjet, ← data.coefficient_reconstruction, MvPolynomial.aeval_def,
    eval₂_firstOrderMvPoly] at hrel
  rw [← hrel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← aeval_def, aeval_algHom_apply]

/-! ## The base model -/

/-- The branch field of depth zero is the rational clock field. -/
theorem nonautonomousFiniteRatFuncToBranch_zero_surjective :
    Function.Surjective (nonautonomousFiniteRatFuncToBranch hfan 0) := by
  let Rg : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).fieldRange
  have hE0 : NonautonomousRamifiedCascadeStateField hfan 0 ≤ Rg := by
    rw [adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    exact ⟨RatFunc.X, (cascadeMero_zero hfan).symm⟩
  have hB0 : NonautonomousFiniteCascadeBranchFieldOverState hfan 0 ≤
      IntermediateField.extendScalars hE0 := by
    rw [adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    change cascadeMeroDeriv hfan 0 ∈ Rg
    rw [cascadeMeroDeriv_zero hfan]
    exact Rg.one_mem
  intro y
  obtain ⟨r, hr⟩ := hB0 y.2
  exact ⟨r, Subtype.ext hr⟩

/-- The rational clock field as the depth-zero branch field. -/
def cascadeBranchZeroEquiv : RatFunc ℂ ≃+* NonautonomousFiniteCascadeBranchField hfan 0 :=
  RingEquiv.ofBijective (nonautonomousFiniteRatFuncToBranch hfan 0)
    ⟨(nonautonomousFiniteRatFuncToBranch hfan 0).injective,
      nonautonomousFiniteRatFuncToBranch_zero_surjective hfan⟩

/-- The extension of `d/dz` to the algebraic closure of `ℂ(z)`. -/
def clockClosureDerivation :
    Derivation ℂ (AlgebraicClosure (RatFunc ℂ)) (AlgebraicClosure (RatFunc ℂ)) :=
  Classical.choose (exists_derivation_algebraicClosure (ratFuncCoordinateDerivation ℂ))

theorem clockClosureDerivation_algebraMap (r : RatFunc ℂ) :
    clockClosureDerivation (algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) r) =
      algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) (ratFuncCoordinateDerivation ℂ r) :=
  Classical.choose_spec (exists_derivation_algebraicClosure (ratFuncCoordinateDerivation ℂ)) r

theorem cascadeDerivation_zero_rat (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < 0 → DifferentiallyAlgebraicOfOrder (f k) 1) (r : RatFunc ℂ) :
    nonautonomousFiniteCascadeDerivation hfan hall h1 (nonautonomousFiniteRatFuncToBranch hfan 0 r) =
      nonautonomousFiniteRatFuncToBranch hfan 0 (ratFuncCoordinateDerivation ℂ r) := by
  refine Subtype.ext ?_
  exact (nonautonomousFiniteCascadeDerivation_coe hfan hall h1 _).trans
    (meroField_deriv_ratfuncToMero r)

/-- **The base model** `ℂ(z)̄` of the depth-zero branch field. -/
def cascadeBaseModel (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < 0 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    CascadeModel (NonautonomousFiniteCascadeBranchField hfan 0)
      (nonautonomousFiniteCascadeDerivation hfan hall h1)
      (nonautonomousFiniteRatFuncToBranch hfan 0) 0 where
  K := AlgebraicClosure (RatFunc ℂ)
  δK := clockClosureDerivation
  pK := Fin.elim0
  ι := (algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ))).comp
    (cascadeBranchZeroEquiv hfan).symm.toRingHom
  map_deriv x := by
    obtain ⟨r, rfl⟩ := nonautonomousFiniteRatFuncToBranch_zero_surjective hfan x
    rw [cascadeDerivation_zero_rat, RingHom.comp_apply, RingHom.comp_apply]
    change algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) ((cascadeBranchZeroEquiv hfan).symm
        ((cascadeBranchZeroEquiv hfan) (ratFuncCoordinateDerivation ℂ r))) =
      clockClosureDerivation (algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ))
        ((cascadeBranchZeroEquiv hfan).symm ((cascadeBranchZeroEquiv hfan) r)))
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, clockClosureDerivation_algebraMap]
  map_complex c := by
    have hc : algebraMap ℂ (NonautonomousFiniteCascadeBranchField hfan 0) c =
        cascadeBranchZeroEquiv hfan (algebraMap ℂ (RatFunc ℂ) c) := Subtype.ext rfl
    rw [RingHom.comp_apply, hc]
    change algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) ((cascadeBranchZeroEquiv hfan).symm
      ((cascadeBranchZeroEquiv hfan) (algebraMap ℂ (RatFunc ℂ) c))) = _
    rw [RingEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply]
  coord_rat i := i.elim0

theorem cascadeBaseModel_ι_rat (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < 0 → DifferentiallyAlgebraicOfOrder (f k) 1) (r : RatFunc ℂ) :
    (cascadeBaseModel hfan hall h1).ι (nonautonomousFiniteRatFuncToBranch hfan 0 r) =
      algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) r := by
  change algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ))
    ((cascadeBranchZeroEquiv hfan).symm ((cascadeBranchZeroEquiv hfan) r)) = _
  rw [RingEquiv.symm_apply_apply]

theorem cascadeTerminalState_zero :
    cascadeTerminalState hfan 0 = nonautonomousFiniteRatFuncToBranch hfan 0 RatFunc.X :=
  (nonautonomousFiniteBranch_algebraMap_X hfan 0).symm

theorem cascadeTerminalDeriv_zero : cascadeTerminalDeriv hfan 0 = 1 :=
  Subtype.ext ((nonautonomousFiniteCascadeDerivativeInBranchField_coe hfan 0 _).trans
    (cascadeMeroDeriv_zero hfan))

theorem transcendental_algebraMap_ratFunc_X :
    Transcendental ℂ (algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) RatFunc.X) :=
  fun h => RatFunc.transcendental_X ((isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)))
    (algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ))).injective).mp h)

theorem topFace_mem_first {g : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData g) :
    data.firstIndex ∈ firstOrderTopNewtonFace data.indexSupport data.coeff data.totalDegree :=
  (Finset.mem_filter.mp data.first_mem_face).1

theorem topFace_mem_second {g : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData g) :
    data.secondIndex ∈ firstOrderTopNewtonFace data.indexSupport data.coeff data.totalDegree :=
  (Finset.mem_filter.mp data.second_mem_face).1

/-- **The layer-0 Wiman lead**: a nonzero root of the top symbol of the first relation at the
clock. -/
noncomputable def cascadeBaseWimanLead (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < 0 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (data : EntireFirstOrderWimanInitialData (f 0)) :
    (cascadeBaseModel hfan hall h1).WimanLead data.indexSupport data.coeff data.totalDegree
      (cascadeTerminalState hfan 0) (cascadeTerminalDeriv hfan 0) :=
  have hu : (cascadeBaseModel hfan hall h1).ι (cascadeTerminalState hfan 0) =
      algebraMap (RatFunc ℂ) (AlgebraicClosure (RatFunc ℂ)) RatFunc.X := by
    rw [cascadeTerminalState_zero, cascadeBaseModel_ι_rat]
  have hex := exists_ne_zero_isRoot_topSymbolAt (topFace_mem_first data)
    (topFace_mem_second data) data.derivativeExponents_ne
    (hu ▸ transcendental_algebraMap_ratFunc_X)
  { σ := Classical.choose hex.2
    isRoot := (Classical.choose_spec hex.2).2
    topSymbol_ne := hex.1
    lead_ne := by
      rw [cascadeTerminalDeriv_zero, map_one, mul_one]
      exact (Classical.choose_spec hex.2).1
    jac_top := by rw [Matrix.det_isEmpty]; exact one_ne_zero
    jac_step := fun _ _ => by rw [Matrix.det_isEmpty]; exact one_ne_zero }

/-! ## The tower -/

/-- The chosen Wiman package of layer `N < n`. -/
abbrev cascadeWimanData (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) (N : ℕ) (hN : N < n) :
    EntireFirstOrderWimanInitialData (f N) :=
  nonautonomousFiniteCascadeWimanData hall h1 ⟨N, hN⟩

/-- **The Laurent tower.**  Every layer `N < n` of the cascade has a model with a Wiman lead of its
relation at the terminal state. -/
theorem exists_cascadeModel_wimanLead (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∀ (N : ℕ) (hN : N < n), ∃ M : CascadeModel (NonautonomousFiniteCascadeBranchField hfan N)
      (nonautonomousFiniteCascadeDerivation hfan hall (fun k hk => h1 k (lt_trans hk hN)))
      (nonautonomousFiniteRatFuncToBranch hfan N) N,
      Nonempty (M.WimanLead (cascadeWimanData hall h1 N hN).indexSupport
        (cascadeWimanData hall h1 N hN).coeff (cascadeWimanData hall h1 N hN).totalDegree
        (cascadeTerminalState hfan N) (cascadeTerminalDeriv hfan N)) := by
  intro N
  induction N with
  | zero =>
      intro hN
      exact ⟨cascadeBaseModel hfan hall _, ⟨cascadeBaseWimanLead hfan hall _ _⟩⟩
  | succ N ih =>
      intro hN1
      have hN : N < n := Nat.lt_of_succ_lt hN1
      obtain ⟨M, ⟨w⟩⟩ := ih hN
      set data := cascadeWimanData hall h1 N hN
      set data' := cascadeWimanData hall h1 (N + 1) hN1
      obtain ⟨e, he, k, τ, hτroot, hτlead, hk⟩ := exists_wiman_topSymbol_laurent_root data'
      have hD := M.exists_step (nonautonomousFiniteCascadeBranchInclusionSucc hfan N)
        (cascadeBranchInclusionSucc_deriv hfan hall (fun k hk => h1 k (lt_trans hk hN1)))
        data.support_degree_le data.coefficient_ne_zero
        (cascadeTerminalStateSucc_deriv hfan hall (fun k hk => h1 k (lt_trans hk hN1)))
        (cascadeStateEval hfan hall N) (cascadeStateEval_algebraMap hfan hall N)
        (relIrrVia_wiman (hall N) data (cascadeStateEval hfan hall N))
        (nonautonomousFiniteCascadeTerminalState_transcendental_lowerBranch hfan hall
          (fun k hk => h1 k (lt_trans hk hN)))
        (adjoin_lowerBranch_terminalState_terminalVelocity_eq_top hfan hall N)
        (cascade_layer_relation hfan hall N data) w e he
      obtain ⟨D⟩ := hD
      refine ⟨D.model (nonautonomousFiniteRatFuncToBranch hfan (N + 1))
        (cascadeBranchInclusionSucc_rat hfan N), ?_⟩
      rw [show cascadeTerminalDeriv hfan (N + 1) =
          nonautonomousFiniteCascadeBranchInclusionSucc hfan N (cascadeTerminalDeriv hfan N) *
            nonautonomousFiniteCascadeTerminalVelocitySucc hfan N from
          (nonautonomousFiniteCascadeTerminalDerivativeSucc hfan hall N).symm]
      exact ⟨D.model_wimanLead _ _ he w.lead_ne w.jac_step (topFace_mem_first data') hτroot
        hτlead hk data'.root_ne_zero⟩

/-! ## The lower bound -/

theorem coe_iterate_cascadeDerivation (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ}
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) (r : ℕ) :
    (((nonautonomousFiniteCascadeDerivation hfan hall h1 :
        NonautonomousFiniteCascadeBranchField hfan N → NonautonomousFiniteCascadeBranchField hfan N)^[r]
          (cascadeTerminalState hfan N) : NonautonomousFiniteCascadeBranchField hfan N) :
        meroField Set.univ) = differentialJet r (cascadeMero hfan N) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', nonautonomousFiniteCascadeDerivation_coe, ih,
        differentialJet_succ]

/-- **The lower bound of the unit-cost law.**  For a cascade of `n` transcendental entire functions
each satisfying a first-order algebraic differential equation, the first `n` derivatives of the
last state are algebraically independent over `ℂ(z)`. -/
theorem algebraicIndependent_jets_entireCascade (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    {n : ℕ} (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    AlgebraicIndependent (RatFunc ℂ)
      (fun j : Fin n => differentialJet (j : ℕ) (cascadeMero hfan n)) := by
  cases n with
  | zero => exact algebraicIndependent_empty_type
  | succ N =>
      obtain ⟨M, ⟨w⟩⟩ := exists_cascadeModel_wimanLead hfan hall h1 N (Nat.lt_succ_self N)
      set data := cascadeWimanData hall h1 N (Nat.lt_succ_self N)
      obtain ⟨D⟩ := M.exists_step (nonautonomousFiniteCascadeBranchInclusionSucc hfan N)
        (cascadeBranchInclusionSucc_deriv hfan hall h1)
        data.support_degree_le data.coefficient_ne_zero
        (cascadeTerminalStateSucc_deriv hfan hall h1)
        (cascadeStateEval hfan hall N) (cascadeStateEval_algebraMap hfan hall N)
        (relIrrVia_wiman (hall N) data (cascadeStateEval hfan hall N))
        (nonautonomousFiniteCascadeTerminalState_transcendental_lowerBranch hfan hall
          (fun k hk => h1 k (Nat.lt_succ_of_lt hk)))
        (adjoin_lowerBranch_terminalState_terminalVelocity_eq_top hfan hall N)
        (cascade_layer_relation hfan hall N data) w 1 one_ne_zero
      have htop := D.model_top (nonautonomousFiniteRatFuncToBranch hfan (N + 1))
        (cascadeBranchInclusionSucc_rat hfan N) one_ne_zero w.jac_top
      have hB := (D.model (nonautonomousFiniteRatFuncToBranch hfan (N + 1))
        (cascadeBranchInclusionSucc_rat hfan N)).algebraicIndependent_iterate _ htop
      have hmero := hB.map' (f := nonautonomousFiniteBranchEmbedding hfan (N + 1))
        (fun a b h => Subtype.ext h)
      convert hmero using 1
      · funext r
        exact (coe_iterate_cascadeDerivation hfan hall h1 r).symm
      · rfl

/-- **The unit-cost law for first-order entire cascades.**  A composition `F_n = f_(n-1) ∘ ⋯ ∘ f_0`
of transcendental entire functions, each satisfying a first-order algebraic differential equation,
has differential order exactly `n`. -/
theorem exactDifferentialOrder_entireCascade_unconditional
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ}
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ExactDifferentialOrder (entireCascade f n) n :=
  have hfan' : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ := fun i =>
    (hall i).1.differentiableOn.analyticOnNhd isOpen_univ
  exactDifferentialOrder_entireCascade_of_transcendental hfan' hall h1
    (algebraicIndependent_jets_entireCascade hfan' hall h1)

/-- **The unit-cost law, finite form.**  Only the constituents actually composed matter: if
`f_0, …, f_(n-1)` are transcendental entire and each satisfies a first-order algebraic differential
equation, then `F_n = f_(n-1) ∘ ⋯ ∘ f_0` has differential order exactly `n`. -/
theorem exactDifferentialOrder_entireCascade_of_lt {n : ℕ}
    (hall : ∀ k, k < n → TranscendentalEntire (f k))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ExactDifferentialOrder (entireCascade f n) n := by
  classical
  let g : ℕ → ℂ → ℂ := fun i => if i < n then f i else Complex.exp
  have hg : ∀ i, i < n → g i = f i := fun i hi => if_pos hi
  have hcasc : ∀ m, m ≤ n → entireCascade g m = entireCascade f m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        funext z
        rw [entireCascade_succ, entireCascade_succ, ih (by omega), hg m (by omega)]
  have hallg : ∀ i : ℕ, TranscendentalEntire (g i) := by
    intro i
    by_cases hi : i < n
    · rw [hg i hi]
      exact hall i hi
    · simp only [g, if_neg hi]
      exact transcendentalEntire_exp
  have h1g : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (g k) 1 := fun k hk => by
    rw [hg k hk]
    exact h1 k hk
  rw [← hcasc n le_rfl]
  exact exactDifferentialOrder_entireCascade_unconditional hallg h1g

end

end GaloisForLFunctions.HTGeometry
