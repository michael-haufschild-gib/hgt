import GaloisForLFunctions.HTGeometry.SpectralTorusContinuousCircuitHardnessLaw
import GaloisForLFunctions.HTGeometry.GroupCharacter.Integrality

/-!
# Projective continuous-circuit hardness on every spectral torus

Global phase does not weaken the spectral-torus obstruction.  Every continuous
two-qubit circuit in this model has determinant one.  Hence an exact equality
between a determinant-one hard target and a global-phase multiple of a circuit
forces that phase to be algebraic.  Adjoining all algebraic numbers to the
countable eigenbasis coefficient field therefore preserves the full
`D - 1`-coordinate transcendence obstruction.

Consequently every eigenbasis torus contains one target with positive operator
distance from every global-phase representative of every circuit with
`16s < D - 1`.  No gate discretisation or eigenbasis genericity is used.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A circuit assembled from lifted `SU(4)` gates has determinant one. -/
theorem TwoQubitCircuit.det_eval_eq_one
    {n : ℕ} (C : TwoQubitCircuit n) :
    Matrix.det (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 1 := by
  let word : List (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
    List.ofFn fun r => C.architecture.gateLift r (C.gates r)
  let matrixWord : List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    (word.map fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
      (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).reverse
  have hmatrix :
      (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        matrixWord.prod := by
    rw [TwoQubitCircuit.eval, TwoQubitArchitecture.contraction]
    exact (List.map_coe_unitary_reverse_prod word).symm
  have hgate : ∀ M ∈ matrixWord, Matrix.det M = 1 := by
    intro M hM
    simp only [matrixWord, List.mem_reverse, List.mem_map] at hM
    obtain ⟨U, hUword, rfl⟩ := hM
    have hmem :
        (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈
          Matrix.specialUnitaryGroup (Fin n → Bool) ℂ := by
      simp only [word, List.mem_ofFn] at hUword
      obtain ⟨r, rfl⟩ := hUword
      exact twoQubitLift_mem_specialUnitary _ _ _ _
    exact (Matrix.mem_specialUnitaryGroup_iff.mp hmem).2
  rw [hmatrix]
  have det_prod_one : ∀ l : List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      (∀ M ∈ l, Matrix.det M = 1) → Matrix.det l.prod = 1 := by
    intro l hl
    induction l with
    | nil => simp
    | cons U l ih =>
        rw [List.prod_cons, Matrix.det_mul, hl U (by simp),
          ih (fun M hM => hl M (by simp [hM])), one_mul]
  exact det_prod_one matrixWord hgate

/-- Complete continuous circuit image, saturated by every unit global phase. -/
def phaseCircuitMatrixImageAtMost (n s : ℕ) :
    Set (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
  (fun p : ℂ × Matrix (Fin n → Bool) (Fin n → Bool) ℂ => p.1 • p.2) ''
    (Metric.sphere 0 1 ×ˢ TwoQubitArchitecture.circuitMatrixImageAtMost n s)

theorem isCompact_phaseCircuitMatrixImageAtMost (n s : ℕ) :
    IsCompact (phaseCircuitMatrixImageAtMost n s) := by
  exact ((isCompact_sphere (0 : ℂ) 1).prod
    (TwoQubitArchitecture.isCompact_circuitMatrixImageAtMost n s)).image
      continuous_smul

theorem phaseCircuitMatrixImageAtMost_nonempty (n s : ℕ) :
    (phaseCircuitMatrixImageAtMost n s).Nonempty := by
  let A : TwoQubitArchitecture n 0 := ⟨Fin.elim0, fun r => Fin.elim0 r⟩
  refine ⟨(1 : ℂ) •
      (A.contraction Fin.elim0 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ), ?_⟩
  refine ⟨(1, (A.contraction Fin.elim0 :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ)), ?_, rfl⟩
  constructor
  · simp
  · rw [TwoQubitArchitecture.circuitMatrixImageAtMost]
    refine ⟨A.contraction Fin.elim0, ?_, rfl⟩
    rw [TwoQubitArchitecture.circuitImageAtMost]
    simp only [Set.mem_iUnion]
    refine ⟨⟨0, Nat.zero_lt_succ s⟩, ?_⟩
    rw [TwoQubitArchitecture.circuitImageExact]
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨A, Fin.elim0, rfl⟩

theorem mem_phaseCircuitMatrixImageAtMost_iff
    {n s : ℕ} {M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ} :
    M ∈ phaseCircuitMatrixImageAtMost n s ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
        C.gateCount ≤ s ∧ M = c •
          (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  constructor
  · rintro ⟨⟨c, U⟩, ⟨hc, hU⟩, rfl⟩
    obtain ⟨Ug, hUg, rfl⟩ := hU
    obtain ⟨C, hC, rfl⟩ :=
      TwoQubitArchitecture.mem_circuitImageAtMost_iff.mp hUg
    refine ⟨c, ?_, C, hC, rfl⟩
    simpa [Metric.mem_sphere] using hc
  · rintro ⟨c, hc, C, hC, rfl⟩
    refine ⟨(c, (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)), ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_sphere] using hc
    · exact ⟨C.eval,
        TwoQubitArchitecture.mem_circuitImageAtMost_iff.mpr ⟨C, hC, rfl⟩, rfl⟩

/-- Compact projective circuit exclusion supplies one common positive error. -/
theorem exists_pos_norm_sub_of_not_mem_phaseCircuitMatrixImageAtMost
    {n s : ℕ} {U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hU : U ∉ phaseCircuitMatrixImageAtMost n s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ V ∈ phaseCircuitMatrixImageAtMost n s,
      ε ≤ ‖U - V‖ := by
  let ε := Metric.infDist U (phaseCircuitMatrixImageAtMost n s)
  have hε : 0 < ε :=
    ((isCompact_phaseCircuitMatrixImageAtMost n s).isClosed.notMem_iff_infDist_pos
      (phaseCircuitMatrixImageAtMost_nonempty n s)).mp hU
  refine ⟨ε, hε, ?_⟩
  intro V hV
  simpa [dist_eq_norm, norm_sub_rev] using
    (Metric.infDist_le_dist_of_mem (x := U) hV)

/-- Projective equality still needs at least one gate per sixteen independent
spectral coordinates.  Determinant one forces the scalar phase into the
algebraic part of the coefficient field. -/
theorem gateCount_mul_sixteen_ge_of_spectralPhase_eq_smul
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (K : Subfield ℂ)
    (hAlgK : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ K)
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hVK : ∀ i j,
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ K)
    (hVinvK : ∀ i j,
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j ∈ K)
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (hprod : ∏ i, phase i = 1)
    (hphaseInd : AlgebraicIndependent K (fun i : Fin d => phase i.succ))
    (c : ℂ) (C : TwoQubitCircuit n)
    (hC : (spectralPhaseUnitary e V phase hphase :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = c •
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    d ≤ C.gateCount * 16 := by
  classical
  have hcard : Fintype.card (Fin n → Bool) = d + 1 :=
    by simpa using Fintype.card_congr e
  have hdetC : Matrix.det
      (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 1 :=
    C.det_eval_eq_one
  have hdetEq := congrArg Matrix.det hC
  rw [det_spectralPhaseUnitary_eq_one e V phase hphase hprod,
    Matrix.det_smul, hdetC, mul_one, hcard] at hdetEq
  have hcPow : c ^ (d + 1) = 1 := hdetEq.symm
  have hcAlgZ : IsAlgebraic ℤ c :=
    (GroupCharacter.isIntegral_of_pow_eq_one (Nat.succ_ne_zero d) hcPow).isAlgebraic
  have hcAlgQ : IsAlgebraic ℚ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hcAlgZ
  have hcK : c ∈ K := hAlgK c hcAlgQ
  obtain ⟨g, hg⟩ :=
    TwoQubitCircuit.exists_sixteenGenerators_eval_entries (K := K) C
  let A : Subalgebra K ℂ := Algebra.adjoin K (Set.range g)
  have hcA : c ∈ A := A.algebraMap_mem (⟨c, hcK⟩ : K)
  have hUA : ∀ i j,
      (spectralPhaseUnitary e V phase hphase :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ A := by
    intro i j
    have hij := A.mul_mem hcA (hg i j)
    rw [hC]
    simpa [smul_eq_mul] using hij
  have hVA : ∀ i j,
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j ∈ A := by
    intro i j
    exact A.algebraMap_mem
      (⟨(V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) i j,
        hVK i j⟩ : K)
  have hVinvA : ∀ i j,
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j ∈ A := by
    intro i j
    exact A.algebraMap_mem
      (⟨(V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 i j,
        hVinvK i j⟩ : K)
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

/-- Every eigenbasis admits a phase packet whose realization up to arbitrary
global phase has the same `D - 1` projective gate lower bound. -/
theorem exists_spectralPhase_projective_gateCount_mul_sixteen_ge
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    ∃ phase : Fin (d + 1) → ℂ,
      ∃ hphase : ∀ i, ‖phase i‖ = 1,
      (∏ i, phase i = 1) ∧
      ∀ (c : ℂ) (C : TwoQubitCircuit n),
        (spectralPhaseUnitary e V phase hphase :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = c •
            (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) →
        d ≤ C.gateCount * 16 := by
  classical
  let coeff : Set ℂ :=
    {z : ℂ | IsAlgebraic ℚ z} ∪
    {Complex.I} ∪
    Set.range (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) p.1 p.2) ∪
    Set.range (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 p.1 p.2)
  have hcoeff : coeff.Countable := by
    exact (((GaloisForLFunctions.countable_isAlgebraic_rat.union
      (Set.countable_singleton _)).union (Set.countable_range _)).union
        (Set.countable_range _))
  let K : Subfield ℂ := Subfield.closure coeff
  letI : Countable ↥K := by
    dsimp only [K]
    exact GaloisForLFunctions.countable_subfield_closure hcoeff
  have hAlgK : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ K := by
    intro z hz
    exact Subfield.subset_closure (by
      exact Or.inl (Or.inl (Or.inl hz)))
  have hI : Complex.I ∈ K := by
    exact Subfield.subset_closure (by
      exact Or.inl (Or.inl (Or.inr rfl)))
  obtain ⟨phase, hnorm, hprod, hind⟩ :=
    exists_algebraicIndependent_specialUnitPhasePacket K hI d
  refine ⟨phase, hnorm, hprod, ?_⟩
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
  intro c C hC
  exact gateCount_mul_sixteen_ge_of_spectralPhase_eq_smul
    e K hAlgK V hVK hVinvK phase hnorm hprod hind c C hC

/-- **Projective hard seed on every spectral torus.**  If `16s < D - 1`,
every fixed eigenbasis has one determinant-one phase target at positive common
operator distance from all global-phase representatives of all continuous
`SU(4)` two-qubit circuits of gate count at most `s`. -/
theorem exists_fixedError_projectiveSpectralPhase_continuousCircuitHard
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hs : s * 16 < d) :
    ∃ phase : Fin (d + 1) → ℂ,
      ∃ hphase : ∀ i, ‖phase i‖ = 1,
      (∏ i, phase i = 1) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ (c : ℂ), ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
          C.gateCount ≤ s →
          ε ≤ ‖(spectralPhaseUnitary e V phase hphase :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨phase, hphase, hprod, hbound⟩ :=
    exists_spectralPhase_projective_gateCount_mul_sixteen_ge e V
  have hnot :
      (spectralPhaseUnitary e V phase hphase :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∉
          phaseCircuitMatrixImageAtMost n s := by
    intro hmem
    obtain ⟨c, _hc, C, hCs, hEq⟩ :=
      mem_phaseCircuitMatrixImageAtMost_iff.mp hmem
    have hlow := hbound c C hEq
    have hupp : C.gateCount * 16 ≤ s * 16 :=
      Nat.mul_le_mul_right 16 hCs
    omega
  obtain ⟨ε, hε, hsep⟩ :=
    exists_pos_norm_sub_of_not_mem_phaseCircuitMatrixImageAtMost hnot
  refine ⟨phase, hphase, hprod, ε, hε, ?_⟩
  intro c hc C hCs
  apply hsep
  exact mem_phaseCircuitMatrixImageAtMost_iff.mpr
    ⟨c, hc, C, hCs, rfl⟩

end
end GaloisForLFunctions.HTGeometry
