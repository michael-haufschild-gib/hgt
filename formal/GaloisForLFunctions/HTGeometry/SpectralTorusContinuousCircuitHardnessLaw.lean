import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentSpecialUnitaryPhasePacket
import GaloisForLFunctions.HTGeometry.HaferkampContinuousCircuitImageCompactness
import GaloisForLFunctions.HTGeometry.ExactCircuitComplexityBound
import GaloisForLFunctions.HTGeometry.HaferkampFlattenedCoordinateDerivative
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-!
# Every spectral torus contains a robust continuous-circuit-hard phase

A fixed eigenbasis may have arbitrary transcendental entries.  Adjoin those
entries and the inverse eigenbasis entries to one countable coefficient field,
then construct `D - 1` determinant-one phase coordinates algebraically
independent over that entire field.  A word of `s` continuous two-qubit gates
carries at most `16s` matrix-entry parameters.  Conjugating its endpoint back
by the fixed eigenbasis recovers every projective phase.  Therefore
`16s < D - 1` excludes exact realization, and compactness upgrades exact
exclusion to one positive operator-norm error against all architectures.

This removes algebraicity, Galois-group, and eigenbasis-genericity assumptions:
the hard phase exists on every spectral torus.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StaticLocalLaboratoryComplexityGrowthLaw

theorem TwoQubitCircuit.generatedBy_sixteen_of_isTwoQubitGate
    {K : Type} [Field K] [Algebra K ℂ]
    {n : ℕ} {a b : Fin n}
    {G : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hG : IsTwoQubitGate a b G) :
    CircuitAdjoin.GeneratedBy K 16 G := by
  classical
  obtain ⟨U, hU⟩ := hG
  refine ⟨fun t => U ((gateParamIndex 1).symm t).2.1
    ((gateParamIndex 1).symm t).2.2, ?_⟩
  intro x y
  rw [hU]
  split_ifs with hxy
  · apply Algebra.subset_adjoin
    refine ⟨gateParamIndex 1 (0, ((x a, x b), (y a, y b))), ?_⟩
    simp
  · exact Subalgebra.zero_mem _

theorem TwoQubitArchitecture.gateLift_generatedBy_sixteen
    {K : Type} [Field K] [Algebra K ℂ]
    {n R : ℕ} (A : TwoQubitArchitecture n R) (r : Fin R)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    CircuitAdjoin.GeneratedBy K 16
      ((A.gateLift r U : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  exact TwoQubitCircuit.generatedBy_sixteen_of_isTwoQubitGate
    (twoQubitLift_isTwoQubitGate _ _ (A.distinct r) U)

theorem TwoQubitCircuit.exists_sixteenGenerators_eval_entries
    {K : Type} [Field K] [Algebra K ℂ]
    {n : ℕ} (C : TwoQubitCircuit n) :
    ∃ g : Fin (C.gateCount * 16) → ℂ,
      ∀ i j, (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈
        Algebra.adjoin K (Set.range g) := by
  classical
  let l : List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    (List.ofFn fun r =>
      ((C.architecture.gateLift r (C.gates r) :
        Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).reverse
  have hl : ∀ M ∈ l, CircuitAdjoin.GeneratedBy (L := ℂ) K 16 M := by
    intro M hM
    simp only [l, List.mem_reverse, List.mem_ofFn] at hM
    obtain ⟨r, rfl⟩ := hM
    exact C.architecture.gateLift_generatedBy_sixteen r (C.gates r)
  obtain ⟨g, hg⟩ := CircuitAdjoin.exists_generators_of_list
    (K := K) 16 l hl
  have hresult : ∃ g : Fin (l.length * 16) → ℂ,
      ∀ i j, (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈
        Algebra.adjoin K (Set.range g) := by
    refine ⟨g, ?_⟩
    intro i j
    have hp := CircuitAdjoin.prod_entries_mem l hg i j
    have hword : l.prod =
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
      rw [TwoQubitCircuit.eval, TwoQubitArchitecture.contraction]
      dsimp only [l]
      let word : List (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
        List.ofFn fun r => C.architecture.gateLift r (C.gates r)
      have hmap :
          List.map (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
            (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) word =
          List.ofFn (fun r =>
            ((C.architecture.gateLift r (C.gates r) :
              Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
        dsimp only [word]
        rw [List.map_ofFn]
        congr 1
      rw [← hmap]
      exact List.map_coe_unitary_reverse_prod word
    rw [← hword]
    exact hp
  have hlen : l.length = C.gateCount := by
    dsimp only [l]
    simp
  rw [hlen] at hresult
  exact hresult

def spectralPhaseUnitary {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  let D : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    ⟨Matrix.diagonal (phase ∘ e),
      mem_unitaryGroup_diagonal_general _ (fun i => hphase (e i))⟩
  V * D * V⁻¹

theorem inverse_mul_spectralPhaseUnitary_mul
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    V⁻¹ * spectralPhaseUnitary e V phase hphase * V =
      (⟨Matrix.diagonal (phase ∘ e),
        mem_unitaryGroup_diagonal_general _ (fun i => hphase (e i))⟩ :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) := by
  simp [spectralPhaseUnitary, mul_assoc]

theorem det_spectralPhaseUnitary_eq_one
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (hprod : ∏ i, phase i = 1) :
    Matrix.det (spectralPhaseUnitary e V phase hphase :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 1 := by
  have hpairGroup : V * V⁻¹ = 1 := mul_inv_cancel V
  have hpairMatrix := congrArg Subtype.val hpairGroup
  change ((V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
    (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1) = 1 at hpairMatrix
  have hdetPair := congrArg Matrix.det hpairMatrix
  rw [Matrix.det_mul, Matrix.det_one] at hdetPair
  change Matrix.det
    (((V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      Matrix.diagonal (phase ∘ e)) *
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1) = 1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    show (∏ i, (phase ∘ e) i) = ∏ i, phase i by
      simpa only [Function.comp_apply] using Equiv.prod_comp e phase,
    hprod]
  simpa only [mul_one] using hdetPair

theorem gateCount_mul_sixteen_ge_of_spectralPhase
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (K : Subfield ℂ)
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hVK : ∀ i j,
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ K)
    (hVinvK : ∀ i j,
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j ∈ K)
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (hphaseInd : AlgebraicIndependent K (fun i : Fin d => phase i.succ))
    (C : TwoQubitCircuit n)
    (hC : C.eval = spectralPhaseUnitary e V phase hphase) :
    d ≤ C.gateCount * 16 := by
  classical
  obtain ⟨g, hg⟩ :=
    TwoQubitCircuit.exists_sixteenGenerators_eval_entries (K := K) C
  rw [hC] at hg
  let A : Subalgebra K ℂ := Algebra.adjoin K (Set.range g)
  have hVA : ∀ i j,
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ A := by
    intro i j
    have hmem := A.algebraMap_mem
      (⟨(V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j, hVK i j⟩ : K)
    exact hmem
  have hVinvA : ∀ i j,
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j ∈ A := by
    intro i j
    have hmem := A.algebraMap_mem
      (⟨(V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j,
        hVinvK i j⟩ : K)
    exact hmem
  have hUA : ∀ i j,
      (spectralPhaseUnitary e V phase hphase :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ A := hg
  have hleftA : ∀ i j,
      (((V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 *
        (spectralPhaseUnitary e V phase hphase :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) i j) ∈ A :=
    CircuitAdjoin.mul_entries_mem hVinvA hUA
  have hrecoverA : ∀ i j,
      ((((V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 *
          (spectralPhaseUnitary e V phase hphase :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *
        (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) i j) ∈ A :=
    CircuitAdjoin.mul_entries_mem hleftA hVA
  have hrecoverGroup :=
    inverse_mul_spectralPhaseUnitary_mul e V phase hphase
  have hrecoverMatrix := congrArg Subtype.val hrecoverGroup
  change (((V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 *
      (spectralPhaseUnitary e V phase hphase :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) =
        Matrix.diagonal (phase ∘ e) at hrecoverMatrix
  have hphaseMem : ∀ i : Fin d, phase i.succ ∈ A := by
    intro i
    let q : Fin n → Bool := e.symm i.succ
    have hmem := hrecoverA q q
    rw [hrecoverMatrix] at hmem
    simpa [q] using hmem
  exact card_le_of_algebraicIndependent_of_mem_adjoin hphaseInd hphaseMem

/-- Every fixed eigenbasis admits a determinant-one phase packet whose
conjugate cannot be realized below the projective parameter threshold. -/
theorem exists_spectralPhase_gateCount_mul_sixteen_ge
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    ∃ phase : Fin (d + 1) → ℂ,
      ∃ hphase : ∀ i, ‖phase i‖ = 1,
      (∏ i, phase i = 1) ∧
      ∀ C : TwoQubitCircuit n,
        C.eval = spectralPhaseUnitary e V phase hphase →
        d ≤ C.gateCount * 16 := by
  classical
  let coeff : Set ℂ :=
    {Complex.I} ∪
    Set.range (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) p.1 p.2) ∪
    Set.range (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 p.1 p.2)
  have hcoeff : coeff.Countable := by
    exact ((Set.countable_singleton _).union (Set.countable_range _)).union
      (Set.countable_range _)
  let K : Subfield ℂ := Subfield.closure coeff
  letI : Countable ↥K := by
    dsimp only [K]
    exact GaloisForLFunctions.countable_subfield_closure (s := coeff) hcoeff
  have hI : Complex.I ∈ K := by
    exact Subfield.subset_closure (by exact Or.inl (Or.inl rfl))
  obtain ⟨phase, hnorm, hprod, hind⟩ :=
    exists_algebraicIndependent_specialUnitPhasePacket K hI d
  refine ⟨phase, hnorm, hprod, ?_⟩
  intro C hC
  have hVK : ∀ i j,
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ K := by
    intro i j
    exact Subfield.subset_closure (by
      exact Or.inl (Or.inr ⟨(i, j), rfl⟩))
  have hVinvK : ∀ i j,
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j ∈ K := by
    intro i j
    exact Subfield.subset_closure (by
      exact Or.inr ⟨(i, j), rfl⟩)
  exact gateCount_mul_sixteen_ge_of_spectralPhase
    e K V hVK hVinvK phase hnorm hind C hC

/-- **Every spectral torus contains a robust exponentially hard phase.**
For an arbitrary fixed eigenbasis, if `16 s < d`, one determinant-one phase
packet has positive operator-norm distance from every continuous `SU(4)`
two-qubit circuit of gate count at most `s`. -/
theorem exists_fixedError_spectralPhase_continuousCircuitHard
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hs : s * 16 < d) :
    ∃ phase : Fin (d + 1) → ℂ,
      ∃ hphase : ∀ i, ‖phase i‖ = 1,
      (∏ i, phase i = 1) ∧
      ∃ ε : ℝ, 0 < ε ∧
        Matrix.det (spectralPhaseUnitary e V phase hphase :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 1 ∧
        ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
          ε ≤ ‖(spectralPhaseUnitary e V phase hphase :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
            (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨phase, hphase, hprod, hbound⟩ :=
    exists_spectralPhase_gateCount_mul_sixteen_ge e V
  obtain ⟨ε, hε, hsep⟩ :=
    TwoQubitArchitecture.exists_positive_operator_error_of_exact_circuit_exclusion
      (U := spectralPhaseUnitary e V phase hphase) (by
        intro C hCs hEq
        have hlow := hbound C hEq
        have hupp : C.gateCount * 16 ≤ s * 16 :=
          Nat.mul_le_mul_right 16 hCs
        omega)
  exact ⟨phase, hphase, hprod, ε, hε,
    det_spectralPhaseUnitary_eq_one e V phase hphase hprod, hsep⟩

end
end GaloisForLFunctions.HTGeometry

