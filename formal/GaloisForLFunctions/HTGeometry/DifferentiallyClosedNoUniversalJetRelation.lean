import GaloisForLFunctions.HTGeometry.FreeJetTangentClosure
import GaloisForLFunctions.HTGeometry.KolchinNullstellensatz
import GaloisForLFunctions.HTGeometry.MvPolynomialTotalDerivation

/-!
# Differentially closed fields admit no universal linear jet relation

A nonzero finite linear differential operator becomes a nonzero element of a finite polynomial
algebra whose variables form a truncated free jet.  Kolchin's Nullstellensatz supplies a
differential point where that element remains nonzero.  Consequently it cannot annihilate every
element of a differentially closed field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable {C : Type u} [Field C] [Algebra ℚ C] [Differential C]

/-- **A differentially closed field admits no nonzero universal linear jet relation.** -/
theorem noUniversalJetRelation_of_isDifferentiallyClosed [IsDifferentiallyClosed C] :
    NoUniversalJetRelation C := by
  classical
  intro s c hrel k hk
  by_contra hck
  let N := s.max' ⟨k, hk⟩
  have hle : ∀ m ∈ s, m ≤ N := fun m hm => s.le_max' m hm
  let idx : ℕ → Fin (N + 1) := fun m => ⟨min m N, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hidx_val : ∀ {m : ℕ}, m ≤ N → (idx m : ℕ) = m := by
    intro m hm
    simp [idx, Nat.min_eq_left hm]
  let E := MvPolynomial (Fin (N + 1)) C
  let shift : Fin (N + 1) → E := fun i =>
    if hi : (i : ℕ) < N then MvPolynomial.X ⟨(i : ℕ) + 1, Nat.succ_lt_succ hi⟩ else 0
  letI : Differential E := ⟨mvTotalDerivation shift⟩
  letI : DifferentialAlgebra C E := ⟨fun a => mvTotalDerivation_C shift a⟩
  let e : E := ∑ m ∈ s, MvPolynomial.C (c m) * MvPolynomial.X (idx m)
  have hidx_ne : ∀ {m : ℕ}, m ∈ s → m ≠ k → idx m ≠ idx k := by
    intro m hm hmk heq
    apply hmk
    have hval := congrArg Fin.val heq
    simpa [hidx_val (hle m hm), hidx_val (hle k hk)] using hval
  have heval : MvPolynomial.eval (fun i => if i = idx k then 1 else 0) e = c k := by
    change MvPolynomial.eval (fun i => if i = idx k then 1 else 0)
      (∑ m ∈ s, MvPolynomial.C (c m) * MvPolynomial.X (idx m)) = c k
    rw [map_sum, Finset.sum_eq_single k]
    · rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, if_pos rfl, mul_one]
    · intro m hm hmk
      rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        if_neg (hidx_ne hm hmk), mul_zero]
    · exact fun h => (h hk).elim
  have he : e ≠ 0 := by
    intro hezero
    rw [hezero, map_zero] at heval
    exact hck heval.symm
  obtain ⟨χ, hχδ, hχe⟩ := exists_differentialAlgHom_ne_zero (C := C) (E := E) he
  let x : C := χ (MvPolynomial.X (idx 0))
  have hjet : ∀ m, m ≤ N → differentialJet m x = χ (MvPolynomial.X (idx m)) := by
    intro m
    induction m with
    | zero =>
        intro
        simp [x]
    | succ m ih =>
        intro hm
        have hmlt : m < N := by omega
        rw [differentialJet_succ, ih (Nat.le_of_lt hmlt), ← hχδ]
        change χ (mvTotalDerivation shift (MvPolynomial.X (idx m))) = _
        rw [mvTotalDerivation_X]
        change χ (if hi : (idx m : ℕ) < N then
          MvPolynomial.X ⟨(idx m : ℕ) + 1, Nat.succ_lt_succ hi⟩ else 0) = _
        rw [dif_pos (by simpa [hidx_val (Nat.le_of_lt hmlt)] using hmlt)]
        apply congrArg χ
        apply congrArg MvPolynomial.X
        apply Fin.ext
        change (idx m : ℕ) + 1 = (idx (m + 1) : ℕ)
        rw [hidx_val (Nat.le_of_lt hmlt), hidx_val hm]
  have hχeval : χ e = ∑ m ∈ s, c m * differentialJet m x := by
    change χ (∑ m ∈ s, MvPolynomial.C (c m) * MvPolynomial.X (idx m)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hχC : χ (MvPolynomial.C (c m)) = c m := χ.commutes (c m)
    rw [map_mul, hχC, hjet m (hle m hm)]
  rw [hχeval, hrel x] at hχe
  exact hχe rfl

end

end GaloisForLFunctions.HTGeometry
