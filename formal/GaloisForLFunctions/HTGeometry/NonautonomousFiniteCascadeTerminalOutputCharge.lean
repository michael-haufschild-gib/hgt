import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalResidueCoefficient
import GaloisForLFunctions.HTGeometry.AlgebraicIndependentPair
import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic
import GaloisForLFunctions.HTGeometry.FiniteAlgebraicBasisExchange

/-!
# Algebraic independence of the terminal output and Wiman charge

The terminal coordinate response separates the literal output from its actual Wiman charge carrier
inside the complete successor branch field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- The literal terminal output and its actual Wiman charge carrier are algebraically independent
inside the complete successor branch field. -/
theorem algebraicIndependent_nonautonomousFiniteCascadeTerminal_output_charge
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    let B := NonautonomousFiniteCascadeBranchField hfan (N + 1)
    let state : Fin (N + 2) → B :=
      nonautonomousFiniteCascadeStateInBranchField hfan (N + 1)
    let g := algebraMap
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) B
    AlgebraicIndependent ℂ ![
      g (nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan N),
      state ⟨N + 1, by omega⟩] := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan (N + 1)
  let state : Fin (N + 2) → B :=
    nonautonomousFiniteCascadeStateInBranchField hfan (N + 1)
  let g := algebraMap
    (NonautonomousFiniteCascadeTerminalComponentField hfan N) B
  let y := state ⟨N + 1, by omega⟩
  let w := g (nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan N)
  change AlgebraicIndependent ℂ ![w, y]
  obtain ⟨P, hP, hPw⟩ :=
    exists_nonautonomousFiniteCascadeTerminal_coordinateDerivation_response
      hfan hall N h1
  change P w ≠ 0 at hPw
  have hfullAI : AlgebraicIndependent ℂ state :=
    algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField
      hfan hall (N + 1)
  have hyTrans : Transcendental ℂ y := by
    exact hfullAI.transcendental ⟨N + 1, by omega⟩
  have hPy : P y = 0 := by
    change P (state ⟨N + 1, by omega⟩) = 0
    rw [hP]
    simp
  have hwTrans : Transcendental (IntermediateField.adjoin ℂ ({y} : Set B)) w := by
    intro hwAlg
    apply hPw
    exact derivationBase_eq_zero_of_isAlgebraic_adjoin P
      (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        simpa [hz] using hPy)
      hwAlg
  have hwAdjoin : Transcendental (Algebra.adjoin ℂ ({y} : Set B)) w := by
    rw [GaloisForLFunctions.transcendental_algebraAdjoin_iff]
    exact hwTrans
  exact algebraicIndependent_pair_of_transcendental (R := ℂ) (A := B)
    y w hyTrans hwAdjoin

/-- The actual terminal derivative component is algebraic over the literal Wiman charge and output
coordinates.  Thus the Wiman response replaces, rather than supplements, the adjacent-state frame:
both are transcendence bases of the same two-dimensional component. -/
theorem nonautonomousFiniteCascadeTerminalComponent_isAlgebraic_chargeOutput
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    let A := NonautonomousFiniteCascadeTerminalComponentField hfan N
    let frame : Fin 2 → A := ![
      nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan N,
      nonautonomousFiniteCascadeTerminalOutputInComponent hfan N]
    Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range frame)) A := by
  classical
  let B := NonautonomousFiniteCascadeBranchField hfan (N + 1)
  let E := NonautonomousFiniteCascadeTerminalPairField hfan N
  let A := NonautonomousFiniteCascadeTerminalComponentField hfan N
  let frame : Fin 2 → A := ![
    nonautonomousFiniteCascadeTerminalChargedVelocityInComponent hfan N,
    nonautonomousFiniteCascadeTerminalOutputInComponent hfan N]
  change Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range frame)) A
  have hpairB : AlgebraicIndependent ℂ
      (nonautonomousFiniteCascadeTerminalStatePair hfan N) := by
    let state := nonautonomousFiniteCascadeStateInBranchField hfan (N + 1)
    let index : Fin 2 → Fin (N + 2) := fun i => ⟨N + i, by omega⟩
    have hindex : Function.Injective index := by
      intro i j hij
      apply Fin.ext
      have hv := congrArg Fin.val hij
      simp [index] at hv
      omega
    have hfull : AlgebraicIndependent ℂ state :=
      algebraicIndependent_nonautonomousFiniteCascadeStateInBranchField
        hfan hall (N + 1)
    have hcomp := hfull.comp index hindex
    convert hcomp using 1
    funext i
    rfl
  have hEtr : Algebra.trdeg ℂ
      (NonautonomousFiniteCascadeTerminalPairField hfan N) = 2 := by
    have h :=
      trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent
        (nonautonomousFiniteCascadeTerminalStatePair hfan N) hpairB
    simpa using h
  letI : IsScalarTower ℂ
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) :=
    nonautonomousFiniteCascadeTerminalComponent_isAlgebraic hfan hall N h1
  have hzero : Algebra.trdeg
      (NonautonomousFiniteCascadeTerminalPairField hfan N)
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) = 0 :=
    trdeg_eq_zero_iff.mpr inferInstance
  have hsum := trdeg_add_eq ℂ
    (NonautonomousFiniteCascadeTerminalPairField hfan N)
    (A := NonautonomousFiniteCascadeTerminalComponentField hfan N)
  have hAtr : Algebra.trdeg ℂ
      (NonautonomousFiniteCascadeTerminalComponentField hfan N) = 2 := by
    rw [hEtr, hzero, add_zero] at hsum
    exact hsum.symm
  have hframe : AlgebraicIndependent ℂ frame := by
    letI : IsScalarTower ℂ
        (NonautonomousFiniteCascadeTerminalComponentField hfan N)
        (NonautonomousFiniteCascadeBranchField hfan (N + 1)) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    let gAB : NonautonomousFiniteCascadeTerminalComponentField hfan N →ₐ[ℂ]
        NonautonomousFiniteCascadeBranchField hfan (N + 1) :=
      IsScalarTower.toAlgHom ℂ _ _
    apply AlgebraicIndependent.of_comp gAB
    have h := algebraicIndependent_nonautonomousFiniteCascadeTerminal_output_charge
      hfan hall N h1
    convert h using 1
    funext i
    fin_cases i <;> rfl
  exact isAlgebraic_adjoin_of_algebraicIndependent_fin_of_trdeg_eq frame hframe hAtr

end

end GaloisForLFunctions.HTGeometry
