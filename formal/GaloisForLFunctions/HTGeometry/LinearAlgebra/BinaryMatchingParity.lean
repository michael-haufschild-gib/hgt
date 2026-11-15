import GaloisForLFunctions.HTGeometry.LinearAlgebra.SymmetricPairDeterminant
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySymmetricCompletion
import GaloisForLFunctions.HTGeometry.ABHN.ZModReciprocitySupportCongruence

/-!
# Odd counts of binary matching completions

For every symmetric binary matrix on paired coordinates, the sum of the
determinants over all matching perturbations is one. Summing one binary
parameter deletes its matched pair; finite-type induction reaches the empty
minor. The determinant support therefore has odd cardinality. If the matching
is nonempty, the complementary singular set also has odd cardinality.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix
universe u
variable {ι κ : Type*}

/-- Splitting off one binary coordinate turns a function sum into two evaluations. -/
private theorem sum_binary_option {A : Type*} [AddCommMonoid A] [Fintype ι] [DecidableEq ι]
    [DecidableEq (Option ι)]
    (f : (Option ι → ZMod 2) → A) :
    ∑ ε : Option ι → ZMod 2, f ε =
      ∑ ε : ι → ZMod 2, (f (fun o => o.elim 0 ε) + f (fun o => o.elim 1 ε)) := by
  classical
  let e : (Option ι → ZMod 2) ≃ (ZMod 2) × (ι → ZMod 2) := Equiv.piOptionEquivProd
  rw [← e.symm.sum_comp f, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ε _
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      simpa using ZMod.pow_card_sub_one_eq_one hx
  have he (t : ZMod 2) : e.symm (t, ε) = fun o => o.elim t ε := by
    funext o
    cases o <;> rfl
  simp only [hu, Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, he]

private theorem matchingOption_blocks (ε : ι → ZMod 2) (t : ZMod 2) :
    (matchingPerturbation (fun o : Option ι => o.elim t ε)).submatrix
      (optionPairEquiv ι).symm (optionPairEquiv ι).symm =
      fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) := by
  classical
  ext i j
  rcases i with ⟨a, i⟩ | a <;> rcases j with ⟨b, j⟩ | b <;>
    simp [matchingPerturbation, blockDiagonal_apply, optionPairEquiv, fromBlocks]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Relabelling the matched pairs preserves the sum over all binary completions. -/
theorem sum_binaryMatching_det_reindex
    (M : Matrix (Fin 2 × κ) (Fin 2 × κ) (ZMod 2)) (e : ι ≃ κ) :
    (∑ ε : ι → ZMod 2,
      (M.submatrix ((Equiv.refl (Fin 2)).prodCongr e) ((Equiv.refl (Fin 2)).prodCongr e) +
        matchingPerturbation ε).det) =
      ∑ ε : κ → ZMod 2, (M + matchingPerturbation ε).det := by
  classical
  let eε : (κ → ZMod 2) ≃ (ι → ZMod 2) := Equiv.arrowCongr e.symm (Equiv.refl _)
  have hp (ε : κ → ZMod 2) :
      (M.submatrix ((Equiv.refl (Fin 2)).prodCongr e) ((Equiv.refl (Fin 2)).prodCongr e) +
        matchingPerturbation (eε ε)).det = (M + matchingPerturbation ε).det := by
    have h := det_submatrix_equiv_self ((Equiv.refl (Fin 2)).prodCongr e)
      (M + matchingPerturbation ε)
    simp only [submatrix_add, Pi.add_apply, matchingPerturbation_submatrix] at h
    exact h
  calc
    _ = ∑ ε : κ → ZMod 2,
        (M.submatrix ((Equiv.refl (Fin 2)).prodCongr e) ((Equiv.refl (Fin 2)).prodCongr e) +
          matchingPerturbation (eε ε)).det := (eε.sum_comp _).symm
    _ = _ := Finset.sum_congr rfl fun ε _ => hp ε

/-- Summing the two choices of the final matched edge leaves the principal deletion. -/
theorem sum_binaryMatching_det_option [DecidableEq (Option ι)]
    (M : Matrix (Fin 2 × Option ι) (Fin 2 × Option ι) (ZMod 2)) (hM : M.IsSymm) :
    (∑ ε : Option ι → ZMod 2, (M + matchingPerturbation ε).det) =
      ∑ ε : ι → ZMod 2,
        (M.submatrix (fun p : Fin 2 × ι => (p.1, some p.2))
          (fun p : Fin 2 × ι => (p.1, some p.2)) + matchingPerturbation ε).det := by
  classical
  let e := optionPairEquiv ι
  let B := M.submatrix e.symm e.symm
  have hJ : alternatingPair (0 : ZMod 2) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [alternatingPair]
  rw [sum_binary_option]
  apply Finset.sum_congr rfl
  intro ε _
  let C := fromBlocks (B.toBlocks₁₁ + matchingPerturbation ε)
    B.toBlocks₁₂ B.toBlocks₂₁ B.toBlocks₂₂
  have hr (t : ZMod 2) :
      (M + matchingPerturbation (fun o : Option ι => o.elim t ε)).submatrix e.symm e.symm =
        C + fromBlocks (0 : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) 0 0 (alternatingPair t) := by
    have hpert := matchingOption_blocks ε t
    change (matchingPerturbation (fun o : Option ι => o.elim t ε)).submatrix e.symm e.symm =
      fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) at hpert
    simp only [submatrix_add, Pi.add_apply, hpert]
    change B + fromBlocks (matchingPerturbation ε) 0 0 (alternatingPair t) = _
    dsimp only [C]
    conv_lhs => arg 1; rw [← fromBlocks_toBlocks B]
    simp only [fromBlocks_add, add_zero]
  have hzero :
      (M + matchingPerturbation (fun o : Option ι => o.elim 0 ε)).submatrix e.symm e.symm = C := by
    simpa only [hJ, fromBlocks_zero, add_zero] using hr 0
  have hC : C.IsSymm := by
    have hs := hM.add
      (isAlternatingMatrix_matchingPerturbation (fun o : Option ι => o.elim 0 ε)).isSymm_binary
    have h := hs.submatrix e.symm
    rwa [hzero] at h
  have hd0 : (M + matchingPerturbation (fun o : Option ι => o.elim 0 ε)).det = C.det :=
    (det_submatrix_equiv_self e.symm _).symm.trans (congrArg Matrix.det hzero)
  have hd1 : (M + matchingPerturbation (fun o : Option ι => o.elim 1 ε)).det =
      (C + fromBlocks (0 : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) 0 0 (alternatingPair 1)).det :=
    (det_submatrix_equiv_self e.symm _).symm.trans (congrArg Matrix.det (hr 1))
  rw [hd0, hd1]
  exact binary_pairBorder_det_sum C hC

/-- Every symmetric binary matching family has determinant sum one. -/
theorem sum_binaryMatching_det_eq_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    (∑ ε : ι → ZMod 2, (M + matchingPerturbation ε).det) = 1 := by
  classical
  suffices h : ∀ (α : Type u) [Fintype α] [DecidableEq α]
      (N : Matrix (Fin 2 × α) (Fin 2 × α) (ZMod 2)), N.IsSymm →
        (∑ ε : α → ZMod 2, (N + matchingPerturbation ε).det) = 1 from h ι M hM
  intro α _
  apply Fintype.induction_empty_option
    (P := fun α _ => ∀ [DecidableEq α]
      (N : Matrix (Fin 2 × α) (Fin 2 × α) (ZMod 2)), N.IsSymm →
        (∑ ε : α → ZMod 2, (N + matchingPerturbation ε).det) = 1)
  · intro α β _ e ih _ N hN
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← sum_binaryMatching_det_reindex N e]
    exact ih _ (hN.submatrix ((Equiv.refl (Fin 2)).prodCongr e))
  · intro _ N _
    simp
  · intro α _ ih _ N hN
    exact (sum_binaryMatching_det_option N hN).trans
      (ih _ (hN.submatrix (fun p : Fin 2 × α => (p.1, some p.2))))

/-- The finite determinant profile of a binary matching family. -/
noncomputable def binaryMatchingDetProfile
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) : (ι → ZMod 2) →₀ ZMod 2 := by
  classical
  exact Finsupp.onFinset Finset.univ (fun ε => (M + matchingPerturbation ε).det)
    (fun ε _ => Finset.mem_univ ε)

@[simp]
theorem binaryMatchingDetProfile_apply
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (ε : ι → ZMod 2) :
    binaryMatchingDetProfile M ε = (M + matchingPerturbation ε).det := rfl

/-- The determinant profile has total invariant one. -/
theorem binaryMatchingDetProfile_sum
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    (binaryMatchingDetProfile M).sum (fun _ x => x) = 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simpa only [binaryMatchingDetProfile_apply] using sum_binaryMatching_det_eq_one M hM

/-- The support of the determinant profile is exactly the nonsingular completion set. -/
theorem card_binaryMatchingDetProfile_support
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) :
    (binaryMatchingDetProfile M).support.card =
      Fintype.card {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det ≠ 0} := by
  classical
  let e : {ε // ε ∈ (binaryMatchingDetProfile M).support} ≃
      {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det ≠ 0} :=
    Equiv.subtypeEquivRight (fun ε => by simp)
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- The number of nonsingular matched completions is one modulo two. -/
theorem cast_card_binaryMatching_nonsingular
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    (Fintype.card {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det ≠ 0} : ZMod 2) = 1 := by
  classical
  have hone : ∀ ε ∈ (binaryMatchingDetProfile M).support, binaryMatchingDetProfile M ε = 1 := by
    intro ε hε
    simpa using ZMod.pow_card_sub_one_eq_one (Finsupp.mem_support_iff.mp hε)
  have h := ABHN.finsuppZMod_natCast_support_card_eq_sum_of_eq_one 2
    (binaryMatchingDetProfile M) hone
  rwa [binaryMatchingDetProfile_sum M hM, card_binaryMatchingDetProfile_support] at h

/-- Every symmetric binary matrix has an odd number of nonsingular matching completions. -/
theorem odd_card_binaryMatching_nonsingular
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    Odd (Fintype.card {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det ≠ 0}) := by
  have h := congrArg ZMod.val (cast_card_binaryMatching_nonsingular M hM)
  apply Nat.odd_iff.mpr
  rw [ZMod.val_natCast] at h
  have hone : (1 : ZMod 2).val = 1 := by rfl
  rwa [hone] at h

/-- Singular and nonsingular matching choices partition the binary cube. -/
theorem card_binaryMatching_singular_add_nonsingular
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) :
    Fintype.card {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det = 0} +
      Fintype.card {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det ≠ 0} =
        2 ^ Fintype.card ι := by
  classical
  have hle := Fintype.card_subtype_le
    (fun ε : ι → ZMod 2 => (M + matchingPerturbation ε).det = 0)
  have ht : Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by simp
  rw [Fintype.card_subtype_compl, ht]
  rw [ht] at hle
  omega

/-- A nonempty matching also has an odd number of singular completions. -/
theorem odd_card_binaryMatching_singular [Nonempty ι]
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    Odd (Fintype.card {ε : ι → ZMod 2 // (M + matchingPerturbation ε).det = 0}) := by
  have ho := Nat.odd_iff.mp (odd_card_binaryMatching_nonsingular M hM)
  have hc := card_binaryMatching_singular_add_nonsingular M
  have hp : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have he : 2 ^ Fintype.card ι % 2 = 0 := by
    rw [hn, pow_succ, Nat.mul_mod]
    simp
  apply Nat.odd_iff.mpr
  omega

/-- Every symmetric binary family with a matched pair has a singular member. -/
theorem exists_singular_binary_matching_completion [Nonempty ι]
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) (ZMod 2)) (hM : M.IsSymm) :
    ∃ ε : ι → ZMod 2, (M + matchingPerturbation ε).det = 0 := by
  have ho := Nat.odd_iff.mp (odd_card_binaryMatching_singular M hM)
  have hp : 0 < Fintype.card {ε : ι → ZMod 2 //
      (M + matchingPerturbation ε).det = 0} := by omega
  obtain ⟨⟨ε, hε⟩⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨ε, hε⟩

#print axioms odd_card_binaryMatching_singular
#print axioms exists_singular_binary_matching_completion

#print axioms sum_binaryMatching_det_reindex
#print axioms sum_binaryMatching_det_option
#print axioms sum_binaryMatching_det_eq_one
#print axioms cast_card_binaryMatching_nonsingular
#print axioms odd_card_binaryMatching_nonsingular
end GaloisForLFunctions.HTGeometry.LinearAlgebra
