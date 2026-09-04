import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeVelocityGeneration

/-!
# Terminal tower of finite actual cascade branch fields

Increasing cascade depth gives literal inclusions of both the state and finite actual branch
fields.  At a successor depth, the lower branch field together with the new terminal state and
the new terminal constituent velocity generates the whole field.  This is the exact algebraic
tower needed for terminal-inward branch and valuation constructions; no independently chosen
layer field is introduced.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- Actual cascade state fields increase with cascade depth. -/
theorem nonautonomousRamifiedCascadeStateField_mono_succ
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    NonautonomousRamifiedCascadeStateField hfan N ≤
      NonautonomousRamifiedCascadeStateField hfan (N + 1) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact IntermediateField.subset_adjoin ℂ _
    (Set.mem_range_self (i.castSucc : Fin (N + 2)))

/-- Finite actual branch fields increase with cascade depth. -/
theorem nonautonomousFiniteCascadeBranchField_mono_succ
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    NonautonomousFiniteCascadeBranchField hfan N ≤
      NonautonomousFiniteCascadeBranchField hfan (N + 1) := by
  let EN := NonautonomousRamifiedCascadeStateField hfan N
  let BN := NonautonomousFiniteCascadeBranchFieldOverState hfan N
  let BS := NonautonomousFiniteCascadeBranchFieldOverState hfan (N + 1)
  intro x hx
  change x ∈ BS
  change x ∈ BN at hx
  apply IntermediateField.adjoin_induction EN (s := Set.range
      (fun i : Fin (N + 1) => cascadeMeroDeriv hfan i))
    (p := fun x _ => x ∈ BS)
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin
      (NonautonomousRamifiedCascadeStateField hfan (N + 1)) _
      (Set.mem_range_self (i.castSucc : Fin (N + 2)))
  · intro e
    exact IntermediateField.algebraMap_mem BS
      ⟨e, nonautonomousRamifiedCascadeStateField_mono_succ hfan N e.2⟩
  · intro a b _ _ ha hb
    exact BS.add_mem ha hb
  · intro a _ ha
    exact BS.inv_mem ha
  · intro a b _ _ ha hb
    exact BS.mul_mem ha hb
  · exact hx

/-- Canonical inclusion of one finite actual branch field into the successor field. -/
noncomputable def nonautonomousFiniteCascadeBranchInclusionSucc
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    NonautonomousFiniteCascadeBranchField hfan N →ₐ[ℂ]
      NonautonomousFiniteCascadeBranchField hfan (N + 1) :=
  IntermediateField.inclusion
    (nonautonomousFiniteCascadeBranchField_mono_succ hfan N)

@[simp] theorem nonautonomousFiniteCascadeBranchInclusionSucc_state
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) :
    nonautonomousFiniteCascadeBranchInclusionSucc hfan N
        (nonautonomousFiniteCascadeStateInBranchField hfan N i) =
      nonautonomousFiniteCascadeStateInBranchField hfan (N + 1) i.castSucc := by
  apply Subtype.ext
  rfl

@[simp] theorem nonautonomousFiniteCascadeBranchInclusionSucc_derivative
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) :
    nonautonomousFiniteCascadeBranchInclusionSucc hfan N
        (nonautonomousFiniteCascadeDerivativeInBranchField hfan N i) =
      nonautonomousFiniteCascadeDerivativeInBranchField hfan (N + 1) i.castSucc := by
  apply Subtype.ext
  rfl

/-- New terminal state at depth `N + 1`. -/
noncomputable def nonautonomousFiniteCascadeTerminalStateSucc
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousFiniteCascadeBranchField hfan (N + 1) :=
  nonautonomousFiniteCascadeStateInBranchField hfan (N + 1) (Fin.last (N + 1))

/-- New terminal constituent velocity at depth `N + 1`, in forward cascade order. -/
noncomputable def nonautonomousFiniteCascadeTerminalVelocitySucc
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousFiniteCascadeBranchField hfan (N + 1) :=
  nonautonomousFiniteCascadeVelocityInBranchField hfan (0 : Fin (N + 1))

/-- The new terminal derivative is the previous terminal derivative times the new constituent
velocity. -/
theorem nonautonomousFiniteCascadeTerminalDerivativeSucc
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    nonautonomousFiniteCascadeBranchInclusionSucc hfan N
        (nonautonomousFiniteCascadeDerivativeInBranchField hfan N (Fin.last N)) *
      nonautonomousFiniteCascadeTerminalVelocitySucc hfan N =
    nonautonomousFiniteCascadeDerivativeInBranchField hfan (N + 1) (Fin.last (N + 1)) := by
  rw [nonautonomousFiniteCascadeBranchInclusionSucc_derivative]
  apply Subtype.ext
  change cascadeMeroDeriv hfan N *
      (cascadeMeroDeriv hfan (N + 1) / cascadeMeroDeriv hfan N) =
    cascadeMeroDeriv hfan (N + 1)
  field_simp [cascadeMeroDeriv_ne_zero_of_transcendental hfan hall N]

/-- Lower branch field, new terminal state, and new terminal velocity generate the complete next
branch field. -/
theorem adjoin_lowerBranch_terminalState_terminalVelocity_eq_top
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ) :
    IntermediateField.adjoin ℂ
      (Set.range (nonautonomousFiniteCascadeBranchInclusionSucc hfan N) ∪
        {nonautonomousFiniteCascadeTerminalStateSucc hfan N,
          nonautonomousFiniteCascadeTerminalVelocitySucc hfan N}) = ⊤ := by
  let EN := NonautonomousRamifiedCascadeStateField hfan (N + 1)
  let B := NonautonomousFiniteCascadeBranchField hfan (N + 1)
  let S : Set B :=
    Set.range (nonautonomousFiniteCascadeBranchInclusionSucc hfan N) ∪
      {nonautonomousFiniteCascadeTerminalStateSucc hfan N,
        nonautonomousFiniteCascadeTerminalVelocitySucc hfan N}
  let L : IntermediateField ℂ B := IntermediateField.adjoin ℂ S
  change L = ⊤
  apply top_unique
  intro x _
  have hstate : ∀ e : EN,
      (⟨(e : meroField Set.univ),
        IntermediateField.algebraMap_mem
          (NonautonomousFiniteCascadeBranchFieldOverState hfan (N + 1)) e⟩ : B) ∈ L := by
    intro e
    apply IntermediateField.adjoin_induction ℂ
      (s := Set.range (fun i : Fin (N + 2) => cascadeMero hfan i))
      (p := fun y hy =>
        (⟨y, IntermediateField.algebraMap_mem
          (NonautonomousFiniteCascadeBranchFieldOverState hfan (N + 1)) ⟨y, hy⟩⟩ : B) ∈ L)
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      by_cases hi : i.val < N + 1
      · let j : Fin (N + 1) := ⟨i.val, hi⟩
        have hij : j.castSucc = i := Fin.ext rfl
        have hmem : nonautonomousFiniteCascadeBranchInclusionSucc hfan N
            (nonautonomousFiniteCascadeStateInBranchField hfan N j) ∈ L :=
          IntermediateField.subset_adjoin ℂ S
            (Or.inl (Set.mem_range_self
              (nonautonomousFiniteCascadeStateInBranchField hfan N j)))
        have heq :
            (⟨cascadeMero hfan i,
              IntermediateField.algebraMap_mem
                (NonautonomousFiniteCascadeBranchFieldOverState hfan (N + 1))
                ⟨cascadeMero hfan i,
                  IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩⟩ : B) =
              nonautonomousFiniteCascadeBranchInclusionSucc hfan N
                (nonautonomousFiniteCascadeStateInBranchField hfan N j) := by
          rw [nonautonomousFiniteCascadeBranchInclusionSucc_state]
          apply Subtype.ext
          rw [hij]
          rfl
        rw [heq]
        exact hmem
      · have hiLast : i = Fin.last (N + 1) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        have hmem := IntermediateField.subset_adjoin ℂ S (by
          right
          exact Or.inl rfl)
        have heq :
            (⟨cascadeMero hfan (Fin.last (N + 1)),
              IntermediateField.algebraMap_mem
                (NonautonomousFiniteCascadeBranchFieldOverState hfan (N + 1))
                ⟨cascadeMero hfan (Fin.last (N + 1)),
                  IntermediateField.subset_adjoin ℂ _
                    (Set.mem_range_self (Fin.last (N + 1)))⟩⟩ : B) =
              nonautonomousFiniteCascadeTerminalStateSucc hfan N := by
          apply Subtype.ext
          rfl
        rw [heq]
        exact hmem
    · intro c
      exact L.algebraMap_mem c
    · intro a b _ _ ha hb
      exact L.add_mem ha hb
    · intro a _ ha
      exact L.inv_mem ha
    · intro a b _ _ ha hb
      exact L.mul_mem ha hb
    · exact e.2
  have hx : (x : meroField Set.univ) ∈
      NonautonomousFiniteCascadeBranchFieldOverState hfan (N + 1) := x.2
  apply IntermediateField.adjoin_induction EN
    (s := Set.range (fun i : Fin (N + 2) => cascadeMeroDeriv hfan i))
    (p := fun y hy => (⟨y, hy⟩ : B) ∈ L)
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    by_cases hi : i.val < N + 1
    · let j : Fin (N + 1) := ⟨i.val, hi⟩
      have hij : j.castSucc = i := Fin.ext rfl
      have hmem : nonautonomousFiniteCascadeBranchInclusionSucc hfan N
          (nonautonomousFiniteCascadeDerivativeInBranchField hfan N j) ∈ L :=
        IntermediateField.subset_adjoin ℂ S
          (Or.inl (Set.mem_range_self
            (nonautonomousFiniteCascadeDerivativeInBranchField hfan N j)))
      have heq :
          (⟨cascadeMeroDeriv hfan i,
            IntermediateField.subset_adjoin
              (NonautonomousRamifiedCascadeStateField hfan (N + 1)) _
              (Set.mem_range_self i)⟩ : B) =
            nonautonomousFiniteCascadeBranchInclusionSucc hfan N
              (nonautonomousFiniteCascadeDerivativeInBranchField hfan N j) := by
        rw [nonautonomousFiniteCascadeBranchInclusionSucc_derivative]
        apply Subtype.ext
        rw [hij]
        rfl
      rw [heq]
      exact hmem
    · have hiLast : i = Fin.last (N + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      have hprev : nonautonomousFiniteCascadeBranchInclusionSucc hfan N
          (nonautonomousFiniteCascadeDerivativeInBranchField hfan N (Fin.last N)) ∈ L :=
        IntermediateField.subset_adjoin ℂ S
          (Or.inl (Set.mem_range_self
            (nonautonomousFiniteCascadeDerivativeInBranchField hfan N (Fin.last N))))
      have hvel : nonautonomousFiniteCascadeTerminalVelocitySucc hfan N ∈ L :=
        IntermediateField.subset_adjoin ℂ S (by right; simp)
      have hterminal := nonautonomousFiniteCascadeTerminalDerivativeSucc hfan hall N
      have hmem := L.mul_mem hprev hvel
      rw [hterminal] at hmem
      have heq :
          (⟨cascadeMeroDeriv hfan (Fin.last (N + 1)),
            IntermediateField.subset_adjoin
              (NonautonomousRamifiedCascadeStateField hfan (N + 1)) _
              (Set.mem_range_self (Fin.last (N + 1)))⟩ : B) =
            nonautonomousFiniteCascadeDerivativeInBranchField hfan (N + 1)
              (Fin.last (N + 1)) := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact hmem
  · intro e
    exact hstate e
  · intro a b _ _ ha hb
    exact L.add_mem ha hb
  · intro a _ ha
    exact L.inv_mem ha
  · intro a b _ _ ha hb
    exact L.mul_mem ha hb

end

end GaloisForLFunctions.HTGeometry
