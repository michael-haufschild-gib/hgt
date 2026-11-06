import GaloisForLFunctions.HTGeometry.SymmetricCharacters.FiniteColoring
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.MultiplicityBranching

/-!
# Partition stabilizers and coherent blockwise characters

Preserving an unmarked partition allows whole blocks to be exchanged. It gives a positive class
function at each rank, but its restriction from rank three to rank two loses exactly twice the
ordered repeated-letter mass. Fixing every block individually restores the coloring character
and its restriction law for arbitrary probability alphabets.
-/

open scoped BigOperators Classical ComplexOrder
noncomputable section
namespace GaloisForLFunctions.SymmetricCharacters

variable {A X J : Type*} [Fintype A] [Fintype X]
/-- The unmarked partition of positions determined by equal letters. -/
def wordRelation (x : X → A) : X → X → Prop := fun i j => x i = x j

/-- Probability that a permutation preserves the partition, allowing exchange of blocks. -/
def partitionCharacter (w : A → NNReal) (σ : Equiv.Perm X) : ℝ :=
  ∑ x : X → A, if wordRelation (x ∘ σ) = wordRelation x then wordWeight w x else 0

omit [Fintype A] [Fintype X] in
/-- A partition stabilizer gives an equality kernel on translated relations. -/
theorem partition_fixed_inv_mul_iff (x : X → A) (σ τ : Equiv.Perm X) :
    wordRelation (x ∘ (σ⁻¹ * τ)) = wordRelation x ↔
      wordRelation (x ∘ σ.symm) = wordRelation (x ∘ τ.symm) := by
  constructor
  · intro h
    funext i j
    simpa [wordRelation] using congrFun (congrFun h (τ⁻¹ i)) (τ⁻¹ j)
  · intro h
    funext i j
    simpa [wordRelation] using congrFun (congrFun h (τ i)) (τ j)

/-- Unmarked partition stabilizers give positive finite-rank Gram matrices. -/
theorem partitionCharacter_posSemidef (w : A → NNReal) (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun i j => (partitionCharacter w ((g i)⁻¹ * g j) : ℂ)) := by
  have h := Matrix.posSemidef_sum Finset.univ
    (fun (x : X → A) _ =>
      ((Matrix.PosSemidef.one : Matrix.PosSemidef (1 : Matrix (X → X → Prop) (X → X → Prop) ℂ)).submatrix
        (fun j => wordRelation (x ∘ (g j).symm))).smul
        (Complex.zero_le_real.mpr (wordWeight_nonneg w x)))
  convert h using 1
  ext i j
  simp only [partitionCharacter, Complex.ofReal_sum, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [partition_fixed_inv_mul_iff]
  split_ifs <;> simp

omit [Fintype A] in
/-- Every partition of two positions is invariant under their exchange. -/
theorem partition_swap_bool (x : Bool → A) :
    wordRelation (x ∘ Equiv.swap false true) = wordRelation x := by
  funext i j
  cases i <;> cases j <;> simp [wordRelation, eq_comm]

omit [Fintype A] in
/-- The fixed letter must match both swapped letters or neither of them. -/
theorem partition_swap_option_bool (x : Option Bool → A) :
    wordRelation (x ∘ Equiv.optionCongr (Equiv.swap false true)) = wordRelation x ↔
      (x none = x (some false) ↔ x none = x (some true)) := by
  constructor
  · intro h
    have hh := congrFun (congrFun h none) (some false)
    simpa [wordRelation, Equiv.swap_apply_def, eq_comm] using (Iff.of_eq hh).symm
  · intro h
    funext i j
    apply propext
    cases i with
    | none =>
      cases j with
      | none => simp [wordRelation]
      | some b =>
        cases b with
        | false => simpa [wordRelation, Equiv.swap_apply_def] using h.symm
        | true => simpa [wordRelation, Equiv.swap_apply_def] using h
    | some a =>
      cases j with
      | none =>
        cases a with
        | false => simpa [wordRelation, Equiv.swap_apply_def, eq_comm] using h.symm
        | true => simpa [wordRelation, Equiv.swap_apply_def, eq_comm] using h
      | some b => cases a <;> cases b <;> simp [wordRelation, eq_comm]

/-- Mass of partitions of three positions invariant under swapping the last two. -/
def partitionTripleMass (w : A → NNReal) : ℝ :=
  ∑ a, ∑ b, ∑ c, if (a = b ↔ a = c) then (w a : ℝ) * (w b : ℝ) * (w c : ℝ) else 0

/-- The rank-two transposition fixes every unmarked partition. -/
theorem partitionCharacter_bool_swap (w : A → NNReal) :
    partitionCharacter w (Equiv.swap false true) = (∑ a, (w a : ℝ)) ^ 2 := by
  letI : DecidableEq Bool := Classical.decEq _
  simp only [partitionCharacter, partition_swap_bool, ite_true, wordWeight]
  simpa using (Fintype.prod_sum (fun (_ : Bool) (a : A) => (w a : ℝ))).symm

/-- The extended transposition tests whether the fixed letter distinguishes its two neighbors. -/
theorem partitionCharacter_option_bool_swap (w : A → NNReal) :
    partitionCharacter w (Equiv.optionCongr (Equiv.swap false true)) = partitionTripleMass w := by
  letI : DecidableEq (Option Bool) := Classical.decEq _
  let e : (Option Bool → A) ≃ A × A × A :=
    { toFun := fun x => (x none, x (some false), x (some true))
      invFun := fun t i => match i with
        | none => t.1
        | some false => t.2.1
        | some true => t.2.2
      left_inv := fun x => by funext i; cases i with
        | none => rfl
        | some b => cases b <;> rfl
      right_inv := fun t => rfl }
  unfold partitionCharacter
  refine (Fintype.sum_equiv e _ (fun t : A × A × A =>
    if (t.1 = t.2.1 ↔ t.1 = t.2.2) then (w t.1 : ℝ) * (w t.2.1 : ℝ) * (w t.2.2 : ℝ)
    else 0) ?_).trans ?_
  · intro x
    simp only [partition_swap_option_bool]
    change (if (x none = x (some false) ↔ x none = x (some true)) then wordWeight w x else 0) =
      (if (x none = x (some false) ↔ x none = x (some true)) then
        (w (x none) : ℝ) * (w (x (some false)) : ℝ) * (w (x (some true)) : ℝ) else 0)
    split_ifs
    · simp [wordWeight, Fintype.prod_option, mul_assoc, mul_comm]
    · rfl
  · simp only [Fintype.sum_prod_type, partitionTripleMass]

/-- Two disjoint repeated-letter events account for the entire restriction loss. -/
theorem partitionTripleMass_defect (w : A → NNReal) :
    partitionTripleMass w + 2 * repeatedLetterMass w = (∑ a, (w a : ℝ)) ^ 3 := by
  have hpoint (a b c : A) :
      (if (a = b ↔ a = c) then (w a : ℝ) * (w b : ℝ) * (w c : ℝ) else 0) +
      (if a = b then (if a = c then 0 else (w a : ℝ) ^ 2 * (w c : ℝ)) else 0) +
      (if a = c then (if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)) else 0) =
        (w a : ℝ) * (w b : ℝ) * (w c : ℝ) := by
    by_cases hab : a = b
    · subst b
      by_cases hac : a = c
      · subst c; simp
      · simp [hac, pow_two]
    · by_cases hac : a = c
      · subst c; simp [hab, pow_two]; ring
      · simp [hab, hac]
  have h₁ : (∑ a, ∑ b, ∑ c,
      if a = b then (if a = c then 0 else (w a : ℝ) ^ 2 * (w c : ℝ)) else 0) =
      repeatedLetterMass w := by
    unfold repeatedLetterMass
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp
  have h₂ : (∑ a, ∑ b, ∑ c,
      if a = c then (if a = b then 0 else (w a : ℝ) ^ 2 * (w b : ℝ)) else 0) =
      repeatedLetterMass w := by simp [repeatedLetterMass]
  have hs := congrArg (fun f : A → A → A → ℝ => ∑ a, ∑ b, ∑ c, f a b c)
    (funext fun a => funext fun b => funext fun c => hpoint a b c)
  simp only [Finset.sum_add_distrib, h₁, h₂] at hs
  change partitionTripleMass w + repeatedLetterMass w + repeatedLetterMass w = _ at hs
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hs
  nlinarith only [hs]

omit [Fintype A] [Fintype X] in
/-- Fixing every block is exactly the fixed-word condition. -/
theorem blockwiseFixed_iff (x : X → A) (σ : Equiv.Perm X) :
    (∀ i j, x i = x j → x (σ i) = x j) ↔ x ∘ σ = x := by
  constructor
  · intro h
    exact funext fun i => h i i rfl
  · intro h i j hij
    exact (congrFun h i).trans hij

/-- The identity has the full independent-word mass. -/
theorem partitionCharacter_one (w : A → NNReal) :
    partitionCharacter (X := X) w 1 = (∑ a, (w a : ℝ)) ^ Fintype.card X := by
  simp only [partitionCharacter, Equiv.Perm.coe_one, Function.comp_id, ite_true, wordWeight]
  simpa using (Fintype.prod_sum (fun (_ : X) (a : A) => (w a : ℝ))).symm

/-- Exchangeability makes the unmarked partition stabilizer trace central. -/
theorem partitionCharacter_conj (w : A → NNReal) (σ τ : Equiv.Perm X) :
    partitionCharacter w (τ * σ * τ⁻¹) = partitionCharacter w σ := by
  unfold partitionCharacter
  apply Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl A))
  intro x
  have hweight : wordWeight w ((Equiv.arrowCongr τ.symm (Equiv.refl A)) x) =
      wordWeight w x := wordWeight_comp w x τ
  rw [hweight]
  have hfix : wordRelation (x ∘ (τ * σ * τ⁻¹)) = wordRelation x ↔
      wordRelation ((x ∘ τ) ∘ σ) = wordRelation (x ∘ τ) := by
    constructor
    · intro h
      funext i j
      simpa [wordRelation] using congrFun (congrFun h (τ i)) (τ j)
    · intro h
      funext i j
      simpa [wordRelation] using congrFun (congrFun h (τ⁻¹ i)) (τ⁻¹ j)
  change (if wordRelation (x ∘ (τ * σ * τ⁻¹)) = wordRelation x then wordWeight w x else 0) =
    (if wordRelation ((x ∘ τ) ∘ σ) = wordRelation (x ∘ τ) then wordWeight w x else 0)
  simp only [hfix]

/-- The rank-two to rank-three restriction defect is twice the ordered collision mass. -/
theorem partitionCharacter_restriction_defect (w : A → NNReal) :
    (∑ a, (w a : ℝ)) * partitionCharacter w (Equiv.swap false true) -
      partitionCharacter w (Equiv.optionCongr (Equiv.swap false true)) =
      2 * repeatedLetterMass w := by
  rw [partitionCharacter_bool_swap, partitionCharacter_option_bool_swap]
  have h := partitionTripleMass_defect w
  nlinarith only [h]

/-- Unmarked partition stabilizers pass this restriction test only for one supported color. -/
theorem partitionCharacter_restriction_eq_iff (w : A → NNReal) :
    partitionCharacter w (Equiv.optionCongr (Equiv.swap false true)) =
      (∑ a, (w a : ℝ)) * partitionCharacter w (Equiv.swap false true) ↔
      ∀ a b, w a = 0 ∨ w b = 0 ∨ a = b := by
  rw [eq_comm, ← sub_eq_zero, partitionCharacter_restriction_defect,
    mul_eq_zero, repeatedLetterMass_eq_zero_iff]
  simp

/-- Probability that every block is fixed individually. -/
def blockwisePartitionCharacter (w : A → NNReal) (σ : Equiv.Perm X) : ℝ :=
  ∑ x : X → A, if ∀ i j, x i = x j → x (σ i) = x j then wordWeight w x else 0

/-- Blockwise stabilization is exactly the independent-color character. -/
theorem blockwisePartitionCharacter_eq (w : A → NNReal) (σ : Equiv.Perm X) :
    blockwisePartitionCharacter w σ = coloringCharacter w σ := by
  simp only [blockwisePartitionCharacter, blockwiseFixed_iff, coloringCharacter]

/-- The corrected blockwise trace has positive Gram matrices at every rank. -/
theorem blockwisePartitionCharacter_posSemidef (w : A → NNReal) (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun i j => (blockwisePartitionCharacter w ((g i)⁻¹ * g j) : ℂ)) := by
  simp only [blockwisePartitionCharacter_eq]
  exact coloringCharacter_posSemidef w g

/-- Blockwise stabilization has the exact restriction law for every alphabet. -/
theorem blockwisePartitionCharacter_restriction (w : A → NNReal) (σ : Equiv.Perm X) :
    blockwisePartitionCharacter w (Equiv.optionCongr σ) =
      (∑ a, (w a : ℝ)) * blockwisePartitionCharacter w σ := by
  simp only [blockwisePartitionCharacter_eq]
  exact coloringCharacter_optionCongr w σ

end GaloisForLFunctions.SymmetricCharacters
