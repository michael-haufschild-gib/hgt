import GaloisForLFunctions.HTGeometry.TwoReplicaPauliHallSymmetryReduction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cyclic successor on the three nonidentity Pauli axes. -/
def pauliAxisNext (a : Fin 3) : Fin 3 :=
  if a = 0 then 1 else if a = 1 then 2 else 0

/-- Cyclic predecessor on the three nonidentity Pauli axes. -/
def pauliAxisPrev (a : Fin 3) : Fin 3 :=
  if a = 0 then 2 else if a = 1 then 0 else 1

@[simp] theorem pauliAxisPrev_next (a : Fin 3) :
    pauliAxisPrev (pauliAxisNext a) = a := by
  fin_cases a <;> rfl

@[simp] theorem pauliAxisNext_prev (a : Fin 3) :
    pauliAxisNext (pauliAxisPrev a) = a := by
  fin_cases a <;> rfl

theorem pauliAxisNext_ne (a : Fin 3) : pauliAxisNext a ≠ a := by
  fin_cases a <;> decide

theorem pauliAxisPrev_ne (a : Fin 3) : pauliAxisPrev a ≠ a := by
  fin_cases a <;> decide

theorem pauliAxisPrev_ne_next (a : Fin 3) :
    pauliAxisPrev a ≠ pauliAxisNext a := by
  fin_cases a <;> decide

def pauliCharacterZero {σ : Type*} : σ → Option (Fin 3) := fun _ => none

def pauliCharacterSupport
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : σ → Option (Fin 3)) : Finset σ :=
  Finset.univ.filter fun i => P i ≠ none

abbrev NonzeroPauliCharacter
    (σ : Type*) [Fintype σ] [DecidableEq σ] :=
  {P : σ → Option (Fin 3) // P ≠ pauliCharacterZero}

theorem pauliCharacterSupport_nonempty
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : NonzeroPauliCharacter σ) :
    (pauliCharacterSupport P.1).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply P.2
  funext i
  have hi : i ∉ pauliCharacterSupport P.1 := by simp [h]
  simpa [pauliCharacterSupport, pauliCharacterZero] using hi

def firstActivePauliSite
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) : σ :=
  (pauliCharacterSupport P.1).min' (pauliCharacterSupport_nonempty P)

theorem firstActivePauliSite_mem
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    P.1 (firstActivePauliSite P) ≠ none := by
  have hmem := Finset.min'_mem (pauliCharacterSupport P.1)
    (pauliCharacterSupport_nonempty P)
  simpa [firstActivePauliSite, pauliCharacterSupport] using hmem

def rotatePauliAt
    {σ : Type*} [DecidableEq σ]
    (next : Fin 3 → Fin 3) (P : σ → Option (Fin 3)) (i : σ) :
    σ → Option (Fin 3) :=
  Function.update P i (P i |>.map next)

theorem pauliCharacterSupport_rotatePauliAt
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (next : Fin 3 → Fin 3) (P : σ → Option (Fin 3)) (i : σ) :
    pauliCharacterSupport (rotatePauliAt next P i) =
      pauliCharacterSupport P := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [pauliCharacterSupport, rotatePauliAt]
  · simp [pauliCharacterSupport, rotatePauliAt, hji]

def rotateFirstPauliCharacter
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (next : Fin 3 → Fin 3) (P : NonzeroPauliCharacter σ) :
    NonzeroPauliCharacter σ :=
  ⟨rotatePauliAt next P.1 (firstActivePauliSite P), by
    intro hzero
    have hsupp : pauliCharacterSupport
        (rotatePauliAt next P.1 (firstActivePauliSite P)) = ∅ := by
      ext i
      have hi := congrFun hzero i
      simp [pauliCharacterSupport, pauliCharacterZero, hi]
    rw [pauliCharacterSupport_rotatePauliAt] at hsupp
    exact (pauliCharacterSupport_nonempty P).ne_empty hsupp⟩

theorem firstActivePauliSite_rotateFirst
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (next : Fin 3 → Fin 3) (P : NonzeroPauliCharacter σ) :
    firstActivePauliSite (rotateFirstPauliCharacter next P) =
      firstActivePauliSite P := by
  unfold firstActivePauliSite
  change (pauliCharacterSupport
      (rotatePauliAt next P.1 (firstActivePauliSite P))).min' _ = _
  have hs := pauliCharacterSupport_rotatePauliAt next P.1
    (firstActivePauliSite P)
  apply le_antisymm
  · apply Finset.min'_le
    rw [hs]
    exact Finset.min'_mem _ _
  · apply Finset.min'_le
    rw [← hs]
    exact Finset.min'_mem _ _

theorem rotatePauliAt_comp
    {σ : Type*} [DecidableEq σ]
    (f g : Fin 3 → Fin 3) (P : σ → Option (Fin 3)) (i : σ) :
    rotatePauliAt f (rotatePauliAt g P i) i =
      rotatePauliAt (f ∘ g) P i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [rotatePauliAt, Function.comp_def]
  · simp [rotatePauliAt, hji]

theorem rotateFirstPauliCharacter_prev_next
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    rotateFirstPauliCharacter pauliAxisPrev
        (rotateFirstPauliCharacter pauliAxisNext P) = P := by
  apply Subtype.ext
  change rotatePauliAt pauliAxisPrev
      (rotatePauliAt pauliAxisNext P.1 (firstActivePauliSite P))
        (firstActivePauliSite
          (rotateFirstPauliCharacter pauliAxisNext P)) = P.1
  rw [firstActivePauliSite_rotateFirst]
  rw [rotatePauliAt_comp]
  funext i
  by_cases hi : i = firstActivePauliSite P
  · subst i
    simp [rotatePauliAt, Function.comp_def]
  · simp [rotatePauliAt, hi]

theorem rotateFirstPauliCharacter_next_prev
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    rotateFirstPauliCharacter pauliAxisNext
        (rotateFirstPauliCharacter pauliAxisPrev P) = P := by
  apply Subtype.ext
  change rotatePauliAt pauliAxisNext
      (rotatePauliAt pauliAxisPrev P.1 (firstActivePauliSite P))
        (firstActivePauliSite
          (rotateFirstPauliCharacter pauliAxisPrev P)) = P.1
  rw [firstActivePauliSite_rotateFirst]
  rw [rotatePauliAt_comp]
  funext i
  by_cases hi : i = firstActivePauliSite P
  · subst i
    simp [rotatePauliAt, Function.comp_def]
  · simp [rotatePauliAt, hi]

def rotateFirstPauliCharacterEquiv
    (σ : Type*) [Fintype σ] [DecidableEq σ] [LinearOrder σ] :
    NonzeroPauliCharacter σ ≃ NonzeroPauliCharacter σ where
  toFun := rotateFirstPauliCharacter pauliAxisNext
  invFun := rotateFirstPauliCharacter pauliAxisPrev
  left_inv := rotateFirstPauliCharacter_prev_next
  right_inv := rotateFirstPauliCharacter_next_prev

/-- Axis carried by the first active site of a nonzero Pauli character. -/
def firstActivePauliAxis
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) : Fin 3 :=
  (P.1 (firstActivePauliSite P)).get
    ((Option.isSome_iff_ne_none).mpr (firstActivePauliSite_mem P))

theorem firstActivePauliAxis_spec
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    some (firstActivePauliAxis P) = P.1 (firstActivePauliSite P) := by
  exact Option.some_get _

/-- Weight-one Pauli axis which changes the first active label to its cyclic
successor and anticommutes with the source label. -/
def firstDefectPauliLabel
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) : σ → Option (Fin 3) :=
  fun i => if i = firstActivePauliSite P then
    some (pauliAxisPrev (firstActivePauliAxis P)) else none

theorem finitePauliWeight_firstDefectPauliLabel
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    finitePauliWeight (firstDefectPauliLabel P) = 1 := by
  unfold finitePauliWeight
  have hfilter : (Finset.univ.filter fun i =>
      firstDefectPauliLabel P i ≠ none) = {firstActivePauliSite P} := by
    ext i
    simp [firstDefectPauliLabel]
  rw [hfilter, Finset.card_singleton]

theorem rotateFirstPauliCharacter_value_first
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    (rotateFirstPauliCharacter pauliAxisNext P).1
        (firstActivePauliSite P) =
      some (pauliAxisNext (firstActivePauliAxis P)) := by
  simp [rotateFirstPauliCharacter, rotatePauliAt,
    ← firstActivePauliAxis_spec P]

theorem rotateFirstPauliCharacter_value_of_ne_first
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) (i : σ)
    (hi : i ≠ firstActivePauliSite P) :
    (rotateFirstPauliCharacter pauliAxisNext P).1 i = P.1 i := by
  simp [rotateFirstPauliCharacter, rotatePauliAt, hi]

/-- Selected first-defect axis anticommutes with the source local axis. -/
theorem finiteQubitPauli_firstDefect_anticommutes_source
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    finiteQubitPauli (pauliAxisPrev (firstActivePauliAxis P)) *
        finiteQubitPauli (firstActivePauliAxis P) =
      -(finiteQubitPauli (firstActivePauliAxis P) *
        finiteQubitPauli (pauliAxisPrev (firstActivePauliAxis P))) := by
  exact finiteQubitPauli_mul_eq_neg_mul_of_ne
    (pauliAxisPrev_ne (firstActivePauliAxis P))

/-- Selected first-defect axis is also distinct from the target local axis. -/
theorem firstDefectPauliAxis_ne_target
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (P : NonzeroPauliCharacter σ) :
    pauliAxisPrev (firstActivePauliAxis P) ≠
      pauliAxisNext (firstActivePauliAxis P) :=
  pauliAxisPrev_ne_next _

end

end GaloisForLFunctions.HTGeometry
