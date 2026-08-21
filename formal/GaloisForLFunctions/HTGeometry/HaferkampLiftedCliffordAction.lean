import GaloisForLFunctions.HTGeometry.HaferkampBlockPauliTransport
import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitCliffordAction

/-!
# Finite-register Clifford closure for Haferkamp light-cone transports

The explicit local transport gate normalizes every two-qubit Pauli label.
This module lifts that invariant through an arbitrary finite register and
through the reverse-chronological gate words used by a light-cone block.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite-register unitary normalizes the literal finite Pauli family. -/
def IsFinitePauliClifford
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Matrix.unitaryGroup (Q → Bool) ℂ) : Prop :=
  ∀ P : Q → Option (Fin 3), ∃ c : ℂ, ∃ R : Q → Option (Fin 3), c ≠ 0 ∧
    (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix R

/-- The literal all-identity finite Pauli label is the identity matrix. -/
theorem haferkamp_finitePauliMatrix_const_none
    {Q : Type*} [Fintype Q] [DecidableEq Q] :
    finitePauliMatrix (fun _ : Q => (none : Option (Fin 3))) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    rw [Matrix.one_apply_eq]
    refine Finset.prod_eq_one fun q _ => ?_
    simp [boolPauliOptionEntry, boolPauliOption]
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨q, hq⟩ : ∃ q, x q ≠ y q := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
    simp [boolPauliOptionEntry, boolPauliOption, hq]

theorem trace_unitary_conjugation
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Matrix.unitaryGroup (Q → Bool) ℂ)
    (M : Matrix (Q → Bool) (Q → Bool) ℂ) :
    Matrix.trace ((U : Matrix (Q → Bool) (Q → Bool) ℂ) * M *
      Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ)) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle]
  have hU : Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
      (U : Matrix (Q → Bool) (Q → Bool) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]
    exact mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp U.2)
  rw [hU, Matrix.one_mul]

/-- A Pauli-Clifford transport of a nonidentity label cannot have the
identity label as its Pauli output. -/
theorem IsFinitePauliClifford.target_ne_identity
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {U : Matrix.unitaryGroup (Q → Bool) ℂ}
    (_hU : IsFinitePauliClifford U)
    {P R : Q → Option (Fin 3)} {c : ℂ}
    (hP : P ≠ fun _ => none) (hc : c ≠ 0)
    (htransport :
      (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c • finitePauliMatrix R) :
    R ≠ fun _ => none := by
  intro hR
  have htrace := congrArg Matrix.trace htransport
  rw [trace_unitary_conjugation, hR, haferkamp_finitePauliMatrix_const_none,
    Matrix.trace_smul, Matrix.trace_one,
    finitePauliMatrix_trace_eq_zero_of_ne_identity P hP] at htrace
  exact mul_ne_zero hc (by exact_mod_cast Fintype.card_ne_zero) htrace.symm

theorem IsFinitePauliClifford.exists_transport_of_nonidentity
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {U : Matrix.unitaryGroup (Q → Bool) ℂ}
    (hU : IsFinitePauliClifford U)
    (P : Q → Option (Fin 3)) (hP : P ≠ fun _ => none) :
    ∃ c : ℂ, ∃ R : Q → Option (Fin 3), c ≠ 0 ∧ (R ≠ fun _ => none) ∧
      (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c • finitePauliMatrix R := by
  obtain ⟨c, R, hc, htransport⟩ := hU P
  exact ⟨c, R, hc, hU.target_ne_identity hP hc htransport, htransport⟩

/-- Reverse a nonzero scalar Pauli-conjugation identity through a unitary. -/
theorem reverse_unitary_conjugation_of_smul_finitePauli
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Matrix.unitaryGroup (Q → Bool) ℂ)
    (P R : Q → Option (Fin 3)) (c : ℂ) (hc : c ≠ 0)
    (h : (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix R) :
    Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix R *
        (U : Matrix (Q → Bool) (Q → Bool) ℂ) = c⁻¹ • finitePauliMatrix P := by
  have hconj : Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
      (U : Matrix (Q → Bool) (Q → Bool) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]
    exact mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp U.2)
  have h' := congrArg (fun X : Matrix (Q → Bool) (Q → Bool) ℂ =>
    Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) * X *
      (U : Matrix (Q → Bool) (Q → Bool) ℂ)) h
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h'
  have hleft : Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
      ((U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ)) *
      (U : Matrix (Q → Bool) (Q → Bool) ℂ) = finitePauliMatrix P := by
    calc
      Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
          ((U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
            Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ)) *
          (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        (Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
          (U : Matrix (Q → Bool) (Q → Bool) ℂ)) * finitePauliMatrix P *
          (Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
            (U : Matrix (Q → Bool) (Q → Bool) ℂ)) := by
              simp only [Matrix.mul_assoc]
      _ = finitePauliMatrix P := by rw [hconj, Matrix.one_mul, Matrix.mul_one]
  rw [hleft] at h'
  calc
    Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix R *
        (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
      (c⁻¹ * c) • (Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
        finitePauliMatrix R * (U : Matrix (Q → Bool) (Q → Bool) ℂ)) := by
          rw [inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • finitePauliMatrix P := by
      rw [← smul_smul, ← h']

/-- A finite Pauli Clifford transports every nonidentity label to another
nonidentity label, with mutually compatible forward and reverse identities. -/
theorem IsFinitePauliClifford.exists_forward_reverse_transport_of_nonidentity
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {U : Matrix.unitaryGroup (Q → Bool) ℂ}
    (hU : IsFinitePauliClifford U)
    (P : Q → Option (Fin 3)) (hP : P ≠ fun _ => none) :
    ∃ c : ℂ, ∃ R : Q → Option (Fin 3), c ≠ 0 ∧ (R ≠ fun _ => none) ∧
      ((U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c • finitePauliMatrix R) ∧
      (Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
          finitePauliMatrix R * (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c⁻¹ • finitePauliMatrix P) := by
  obtain ⟨c, R, hc, hR, hforward⟩ := hU.exists_transport_of_nonidentity P hP
  exact ⟨c, R, hc, hR, hforward,
    reverse_unitary_conjugation_of_smul_finitePauli U P R c hc hforward⟩

theorem one_isFinitePauliClifford
    {Q : Type*} [Fintype Q] [DecidableEq Q] :
    IsFinitePauliClifford (1 : Matrix.unitaryGroup (Q → Bool) ℂ) := by
  intro P
  exact ⟨1, P, one_ne_zero, by simp⟩

theorem isFinitePauliClifford_mul
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U V : Matrix.unitaryGroup (Q → Bool) ℂ)
    (hU : IsFinitePauliClifford U) (hV : IsFinitePauliClifford V) :
    IsFinitePauliClifford (U * V) := by
  intro P
  obtain ⟨cV, R, hcV, hVP⟩ := hV P
  obtain ⟨cU, S, hcU, hUR⟩ := hU R
  refine ⟨cV * cU, S, mul_ne_zero hcV hcU, ?_⟩
  rw [unitary_mul_conjugation_smul U V _ _ _ hVP, hUR, smul_smul]

theorem twoQubitLift_isFinitePauliClifford
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (hU : IsBoolTwoQubitPauliClifford
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) :
    IsFinitePauliClifford (twoQubitLift a b hab U) := by
  intro P
  obtain ⟨c, pa, pb, hc, hlocal⟩ := hU (P a) (P b)
  exact ⟨c, updateTwoQubitPauliLabel P a b pa pb, hc,
    twoQubitLift_conjugation_of_local a b hab U P pa pb c hlocal⟩

theorem totalTwoQubitLift_isFinitePauliClifford
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (edge : Q × Q) (hedge : edge.1 ≠ edge.2)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (hU : IsBoolTwoQubitPauliClifford
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) :
    IsFinitePauliClifford (totalTwoQubitLift edge U) := by
  rw [totalTwoQubitLift_eq_twoQubitLift edge hedge U]
  exact twoQubitLift_isFinitePauliClifford edge.1 edge.2 hedge U hU

theorem finitePauliMatrix_exists_twoQubitLift_transport_clifford
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (P : Q → Option (Fin 3)) (a b : Q) (hab : a ≠ b)
    (hlocal : P a ≠ none ∨ P b ≠ none) :
    ∃ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ, ∃ c : ℂ, c ≠ 0 ∧
      IsBoolTwoQubitPauliClifford
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∧
      (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) *
          finitePauliMatrix P *
          Matrix.conjTranspose (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c • finitePauliMatrix (updateTwoQubitPauliLabel P a b none (some 2)) := by
  obtain ⟨c, hc, hlocalTransport⟩ := boolTwoQubitTransport_conj (P a) (P b) hlocal
  refine ⟨scalarSpecialUnitaryRepresentative (boolTwoQubitTransport (P a) (P b)), c, hc,
    boolTwoQubitTransportSpecial_isBoolTwoQubitPauliClifford (P a) (P b), ?_⟩
  apply twoQubitLift_conjugation_of_local a b hab _ P none (some 2) c
  rw [scalarSpecialUnitaryRepresentative_conjugation_eq]
  exact hlocalTransport

theorem haferkampGateWordReverseProduct_isFinitePauliClifford
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (edges : List (Q × Q))
    (gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ))
    (hlen : gates.length = edges.length)
    (hedges : ∀ edge ∈ edges, edge.1 ≠ edge.2)
    (hgates : ∀ U ∈ gates, IsBoolTwoQubitPauliClifford
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) :
    IsFinitePauliClifford
      (haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
        totalTwoQubitLift edge U) edges gates) := by
  induction edges generalizing gates with
  | nil =>
      cases gates with
      | nil => simpa [haferkampGateWordReverseProduct] using
          (one_isFinitePauliClifford (Q := Q))
      | cons U gates => simp at hlen
  | cons edge edges ih =>
      cases gates with
      | nil => simp at hlen
      | cons U gates =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [haferkampGateWordReverseProduct_cons]
          apply isFinitePauliClifford_mul
          · apply ih gates hlen
            · intro edge' hedge'
              exact hedges edge' (by simp [hedge'])
            · intro U' hU'
              exact hgates U' (by simp [hU'])
          · apply totalTwoQubitLift_isFinitePauliClifford edge
              (hedges edge (by simp)) U
            exact hgates U (by simp)

namespace PauliMergeSchedule

/-- A certified merge schedule has an aligned local gate word whose every
entry is a Pauli Clifford, while retaining its exact terminal transport. -/
theorem exists_localGateWord_transport_clifford
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {P R : Q → Option (Fin 3)}
    (schedule : PauliMergeSchedule Q P R) :
    ∃ localGates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      localGates.length = schedule.edgeList.length ∧
      (∀ U ∈ localGates, IsBoolTwoQubitPauliClifford
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
      ∃ c : ℂ, c ≠ 0 ∧
        ((haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
          totalTwoQubitLift edge U) schedule.edgeList localGates :
          Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ) *
            finitePauliMatrix P *
            Matrix.conjTranspose
              ((haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
                totalTwoQubitLift edge U) schedule.edgeList localGates :
                Matrix.unitaryGroup (Q → Bool) ℂ) :
                Matrix (Q → Bool) (Q → Bool) ℂ) =
          c • finitePauliMatrix R := by
  induction schedule with
  | done P =>
      refine ⟨[], rfl, ?_, 1, one_ne_zero, ?_⟩
      · simp
      · simp [haferkampGateWordReverseProduct]
  | @step P a b hab hlocal R tail ih =>
      obtain ⟨U₁, c₁, hc₁, hU₁cliff, hU₁⟩ :=
        finitePauliMatrix_exists_twoQubitLift_transport_clifford P a b hab hlocal
      obtain ⟨gates, hgates, hall, c₂, hc₂, htail⟩ := ih
      refine ⟨U₁ :: gates, by simp [edgeList, hgates], ?_, c₁ * c₂,
        mul_ne_zero hc₁ hc₂, ?_⟩
      · intro U hU
        simp only [List.mem_cons] at hU
        rcases hU with rfl | hU
        · exact hU₁cliff
        · exact hall U hU
      · have htotal : totalTwoQubitLift (a, b) U₁ = twoQubitLift a b hab U₁ :=
          totalTwoQubitLift_eq_twoQubitLift (a, b) hab U₁
        simp only [edgeList]
        rw [haferkampGateWordReverseProduct_cons]
        rw [htotal]
        rw [unitary_mul_conjugation_smul
          (haferkampGateWordReverseProduct (fun (edge : Q × Q) U =>
            totalTwoQubitLift edge U) tail.edgeList gates)
          (twoQubitLift a b hab U₁) _ _ c₁ hU₁]
        rw [htail]
        simp [smul_smul]

end PauliMergeSchedule

/-- Extending a selected word by a default gate preserves any pointwise gate
invariant held by that default and by all selected entries. -/
theorem HaferkampGateWordEmbedding.forall_blockGates
    {α : Type*} {β : Type*} {default : β} {test : β → Prop}
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding :
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates)
    (hdefault : test default)
    (hselected : ∀ gate ∈ selectedGates, test gate) :
    ∀ gate ∈ blockGates, test gate := by
  induction embedding with
  | nil => simp
  | skip h ih =>
      intro gate hgate
      simp only [List.mem_cons] at hgate
      rcases hgate with rfl | hgate
      · exact hdefault
      · exact ih hselected gate hgate
  | take h ih =>
      intro gate hgate
      simp only [List.mem_cons] at hgate
      rcases hgate with rfl | hgate
      · exact hselected _ (by simp)
      · exact ih (fun gate hgate => hselected gate (by simp [hgate])) gate hgate

namespace BackwardsLightCone

/-- Every nonidentity Pauli direction has a full block realization whose local
and global gate words are Pauli Cliffords, with exact terminal root-`Z`
transport. -/
theorem exists_full_block_transport_clifford
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      gates.length = edges.length ∧
      (∀ U ∈ gates, IsBoolTwoQubitPauliClifford
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
      IsFinitePauliClifford (edgeListBlockContraction edges gates) ∧
      ∃ R : Fin n → Option (Fin 3), ∃ c : ℂ, c ≠ 0 ∧
        ((edgeListBlockContraction edges gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose
            (edgeListBlockContraction edges gates :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          c • finitePauliMatrix R) ∧ R root = some 2 := by
  obtain ⟨R, schedule, hsub, hroot⟩ :=
    cone.exists_embedded_root_schedule_of_nontrivial hn P hP
  obtain ⟨selectedGates, hselectedLength, hselectedClifford, c, hc, htransport⟩ :=
    schedule.exists_localGateWord_transport_clifford
  obtain ⟨gates, embedding⟩ :=
    exists_haferkampGateWordEmbedding 1 hsub selectedGates hselectedLength
  have hgatesClifford : ∀ U ∈ gates, IsBoolTwoQubitPauliClifford
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :=
    embedding.forall_blockGates one_isBoolTwoQubitPauliClifford hselectedClifford
  refine ⟨gates, embedding.blockGates_length_eq, hgatesClifford, ?_, R, c, hc, ?_, hroot⟩
  · change IsFinitePauliClifford
      (haferkampGateWordReverseProduct totalTwoQubitLift edges gates)
    exact haferkampGateWordReverseProduct_isFinitePauliClifford edges gates
      embedding.blockGates_length_eq cone.edge_distinct hgatesClifford
  · change ((haferkampGateWordReverseProduct totalTwoQubitLift edges gates :
      Matrix.unitaryGroup (Fin n → Bool) ℂ) :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
      Matrix.conjTranspose
        ((haferkampGateWordReverseProduct totalTwoQubitLift edges gates :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      c • finitePauliMatrix R
    rw [embedding.reverseProduct_eq totalTwoQubitLift_one]
    exact htransport

/-- The coalescing light-cone construction realizes the stronger Appendix-B
identity: the full block sends every nonidentity Pauli string to the literal
root-only `Z`, while every local gate remains a Pauli Clifford. -/
theorem exists_full_block_transport_root_Z_clifford
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      gates.length = edges.length ∧
      (∀ U ∈ gates, IsBoolTwoQubitPauliClifford
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
      IsFinitePauliClifford (edgeListBlockContraction edges gates) ∧
      ∃ c : ℂ, c ≠ 0 ∧
        ((edgeListBlockContraction edges gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose
            (edgeListBlockContraction edges gates :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          c • finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
  obtain ⟨schedule, hsub⟩ :=
    cone.exists_embedded_root_only_schedule_of_nontrivial hn P hP
  obtain ⟨selectedGates, hselectedLength, hselectedClifford, c, hc, htransport⟩ :=
    schedule.exists_localGateWord_transport_clifford
  obtain ⟨gates, embedding⟩ :=
    exists_haferkampGateWordEmbedding 1 hsub selectedGates hselectedLength
  refine ⟨gates, embedding.blockGates_length_eq,
    embedding.forall_blockGates one_isBoolTwoQubitPauliClifford hselectedClifford,
    ?_, c, hc, ?_⟩
  · change IsFinitePauliClifford
      (haferkampGateWordReverseProduct totalTwoQubitLift edges gates)
    exact haferkampGateWordReverseProduct_isFinitePauliClifford edges gates
      embedding.blockGates_length_eq cone.edge_distinct
      (embedding.forall_blockGates one_isBoolTwoQubitPauliClifford hselectedClifford)
  · change ((haferkampGateWordReverseProduct totalTwoQubitLift edges gates :
      Matrix.unitaryGroup (Fin n → Bool) ℂ) :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
      Matrix.conjTranspose
        ((haferkampGateWordReverseProduct totalTwoQubitLift edges gates :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        c • finitePauliMatrix (Function.update (fun _ => none) root (some 2))
    rw [embedding.reverseProduct_eq totalTwoQubitLift_one]
    exact htransport

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
