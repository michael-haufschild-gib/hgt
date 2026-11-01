import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPositiveConjugators

/-!
# Integral conjugacy and roots of positive modular words

Positive words in the two oriented unipotent generators classify all
positive-trace hyperbolic integral determinant-one matrices up to conjugacy:
conjugacy of positive representatives is cyclic word splitting, and integral
roots are exactly whole-word repetitions. For roots, squaring a signed
positive centralizer representative preserves the exact exponent relation.
-/

open Matrix
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolic
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerConjugacy
set_option autoImplicit false
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerIntegralWords

def intMatrix (A : NatMatrix) : IntMatrix := fun i j => (A i j : ℤ)

@[simp] theorem intMatrix_mul (A B : NatMatrix) :
    intMatrix (A*B) = intMatrix A*intMatrix B := by
  ext i j
  simp only [intMatrix,Matrix.mul_apply,Fin.sum_univ_two,Nat.cast_add,Nat.cast_mul]

theorem intMatrix_injective : Function.Injective intMatrix := by
  intro A B he
  ext i j
  have h : (A i j : ℤ) = (B i j : ℤ) := congrArg (fun M : IntMatrix => M i j) he
  exact_mod_cast h

/-- Nonnegative determinant one agrees with the integer determinant convention. -/
theorem unimodular_iff_det (A : NatMatrix) : Unimodular A ↔ (intMatrix A).det = 1 := by
  rw [Matrix.det_fin_two]
  change (A 0 0*A 1 1 = A 0 1*A 1 0+1) ↔
    (A 0 0 : ℤ)*A 1 1-(A 0 1 : ℤ)*A 1 0 = 1
  constructor
  · intro h
    have he : (A 0 0 : ℤ)*A 1 1 = (A 0 1 : ℤ)*A 1 0+1 := by exact_mod_cast h
    linarith only [he]
  · intro h
    have he : (A 0 0 : ℤ)*A 1 1 = (A 0 1 : ℤ)*A 1 0+1 := by linarith only [h]
    exact_mod_cast he

/-- Strictly positive integral matrices have an exact nonnegative representative. -/
theorem exists_natMatrix (D : IntMatrix) (hpos : ∀ i j, 0 < D i j) :
    ∃ N : NatMatrix, intMatrix N = D := by
  refine ⟨fun i j => (D i j).toNat,?_⟩
  ext i j
  exact Int.toNat_of_nonneg (hpos i j).le

/-- Arbitrary integral unimodular conjugacy of positive words is exactly cyclic word splitting. -/
theorem integral_intertwiner_iff_cyclic_split (u v : List Bool)
    (hu : ∀ i j, 0 < matrixWord u i j) (hv : ∀ i j, 0 < matrixWord v i j) :
    (∃ C : IntMatrix, C.det = 1 ∧ C*intMatrix (matrixWord u) = intMatrix (matrixWord v)*C) ↔
      ∃ a b : List Bool, u = a++b ∧ v = b++a := by
  constructor
  · rintro ⟨C,hC,he⟩
    have hA := (unimodular_iff_det (matrixWord u)).mp (matrixWord_unimodular u)
    have hposA : ∀ i j, 0 < intMatrix (matrixWord u) i j := by
      intro i j
      change (0 : ℤ) < (matrixWord u i j : ℤ)
      exact_mod_cast hu i j
    have hposB : ∀ i j, 0 < intMatrix (matrixWord v) i j := by
      intro i j
      change (0 : ℤ) < (matrixWord v i j : ℤ)
      exact_mod_cast hv i j
    obtain ⟨D,hD,hinter,hpos⟩ := exists_positive_intertwiner
      (intMatrix (matrixWord u)) (intMatrix (matrixWord v)) C hA hposA hposB hC he
    obtain ⟨N,hN⟩ := exists_natMatrix D hpos
    have hNu : Unimodular N := (unimodular_iff_det N).mpr (by rw [hN]; exact hD)
    apply (positive_intertwiner_iff_cyclic_split u v).mp
    refine ⟨N,hNu,intMatrix_injective ?_⟩
    rw [intMatrix_mul,intMatrix_mul,hN,hinter]
  · intro h
    obtain ⟨N,hN,he⟩ := (positive_intertwiner_iff_cyclic_split u v).mpr h
    refine ⟨intMatrix N,(unimodular_iff_det N).mp hN,?_⟩
    simpa only [intMatrix_mul] using congrArg intMatrix he

#print axioms unimodular_iff_det
#print axioms integral_intertwiner_iff_cyclic_split


@[simp] theorem intMatrix_one : intMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [intMatrix]

@[simp] theorem intMatrix_pow (A : NatMatrix) (n : ℕ) : intMatrix (A^n) = intMatrix A^n := by
  induction n with
  | zero => simp only [pow_zero,intMatrix_one]
  | succ n ih => simp only [pow_succ,intMatrix_mul,ih]

private theorem positive_shifted_centralizer (A B : IntMatrix) (hA : A.det = 1)
    (hpos : ∀ i j, 0 < A i j) (hB : B.det = 1) (he : B*A = A*B) :
    ∃ n : ℕ, ∃ D : IntMatrix, (D = B*A^n ∨ D = -(B*A^n)) ∧
      D.det = 1 ∧ D*A = A*D ∧ ∀ i j, 0 < D i j := by
  have hdet (n : ℕ) : (B*A^n).det = 1 := by
    rw [Matrix.det_mul,Matrix.det_pow,hB,hA,one_pow,mul_one]
  have hinter (n : ℕ) : (B*A^n)*A = A*(B*A^n) := by
    calc
      _ = B*(A^n*A) := by rw [Matrix.mul_assoc]
      _ = B*(A*A^n) := by rw [← pow_succ,← pow_succ']
      _ = (B*A)*A^n := by rw [Matrix.mul_assoc]
      _ = _ := by rw [he,Matrix.mul_assoc]
  rcases eventually_intertwiner_one_sign A A B hA hpos hpos hB he with hp | hn
  · obtain ⟨n,hn⟩ := hp.exists
    exact ⟨n,B*A^n,Or.inl rfl,hdet n,hinter n,hn⟩
  · obtain ⟨n,hn⟩ := hn.exists
    refine ⟨n,-(B*A^n),Or.inr rfl,?_,?_,?_⟩
    · have hd := hdet n
      rw [Matrix.det_fin_two] at hd ⊢
      simp only [Matrix.neg_apply]
      nlinarith only [hd]
    · rw [Matrix.neg_mul,Matrix.mul_neg,hinter n]
    · intro i j
      exact neg_pos.mpr (hn i j)

private theorem wordPower_length {α : Type*} (w : List α) (n : ℕ) :
    (wordPower w n).length = n*w.length := by
  induction n with
  | zero => simp only [wordPower,List.length_nil,Nat.zero_mul]
  | succ n ih =>
    rw [wordPower,List.length_append,ih,Nat.succ_mul]
    omega

/-- Integral determinant-one roots of a strictly positive word are exactly its whole-word repetitions.
The proof squares a signed positive centralizer representative, so no orientation sign is discarded. -/
theorem integral_root_iff_word_power (u : List Bool) (hu : ∀ i j, 0 < matrixWord u i j) (k : ℕ) :
    (∃ B : IntMatrix, B.det = 1 ∧ B^k = intMatrix (matrixWord u)) ↔
      ∃ w : List Bool, u = wordPower w k := by
  constructor
  · rintro ⟨B,hB,hroot⟩
    let A := intMatrix (matrixWord u)
    have hA : A.det = 1 := (unimodular_iff_det (matrixWord u)).mp (matrixWord_unimodular u)
    have hpos : ∀ i j, 0 < A i j := by
      intro i j
      change (0 : ℤ) < (matrixWord u i j : ℤ)
      exact_mod_cast hu i j
    have hBA : Commute B A := by
      change Commute B (intMatrix (matrixWord u))
      rw [← hroot]
      exact Commute.self_pow B k
    obtain ⟨n,D,hsign,hD,hDA,hposD⟩ := positive_shifted_centralizer A B hA hpos hB hBA.eq
    have hpow : (B*A^n)^k = A^(n*k+1) := by
      rw [(hBA.pow_right n).mul_pow k,hroot,← pow_mul]
      change A*A^(n*k) = A^(n*k+1)
      exact (pow_succ' A (n*k)).symm
    have hsq : D^(2*k) = (B*A^n)^(2*k) := by
      rcases hsign with rfl | rfl
      · rfl
      · simp only [pow_mul,pow_two,neg_mul_neg]
    have hDpow : D^(2*k) = A^(2*(n*k+1)) := by
      rw [hsq,show 2*k = k*2 by omega,pow_mul,hpow,← pow_mul]
      congr 1
      omega
    obtain ⟨N,hN⟩ := exists_natMatrix D hposD
    have hNu := (unimodular_iff_det N).mpr (show (intMatrix N).det = 1 by rw [hN]; exact hD)
    have hcomm : matrixWord u*N = N*matrixWord u := by
      apply intMatrix_injective
      rw [intMatrix_mul,intMatrix_mul,hN]
      exact hDA.symm
    obtain ⟨w,m,l,hm,hl⟩ := commuting_matrices_common_root (matrixWord u) N
      (matrixWord_unimodular u) hNu hcomm
    have hNp : N^(2*k) = matrixWord u^(2*(n*k+1)) := by
      apply intMatrix_injective
      rw [intMatrix_pow,intMatrix_pow,hN]
      exact hDpow
    have hw : w ≠ [] := by
      intro hw
      simp only [hw,matrixWord,one_pow] at hm
      have hh := congrArg (fun M : NatMatrix => M 0 1) hm
      norm_num at hh
      have hp := hu 0 1
      omega
    have hlen : 0 < w.length := by
      cases w with
      | nil => exact (hw rfl).elim
      | cons b w => exact Nat.succ_pos _
    have hwords : wordPower w (l*(2*k)) = wordPower w (m*(2*(n*k+1))) := by
      apply matrixWord_injective
      rw [matrixWord_wordPower,matrixWord_wordPower,
        pow_mul (matrixWord w) l (2*k),pow_mul (matrixWord w) m (2*(n*k+1)),← hl,← hm]
      exact hNp
    have hlength := congrArg List.length hwords
    rw [wordPower_length,wordPower_length] at hlength
    have hcount : l*(2*k) = m*(2*(n*k+1)) :=
      mul_right_cancel₀ (ne_of_gt hlen) hlength
    have he : l*k = (m*n)*k+m := by nlinarith only [hcount]
    have hq : (l-m*n)*k = m := by
      rw [Nat.sub_mul,he]
      omega
    refine ⟨wordPower w (l-m*n),matrixWord_injective ?_⟩
    rw [matrixWord_wordPower,matrixWord_wordPower,← pow_mul,hq,← hm]
  · rintro ⟨w,rfl⟩
    refine ⟨intMatrix (matrixWord w),(unimodular_iff_det (matrixWord w)).mp
      (matrixWord_unimodular w),?_⟩
    rw [matrixWord_wordPower,intMatrix_pow]

/-- Every positive-trace integral hyperbolic matrix is integrally conjugate to a strictly positive word. -/
theorem exists_integral_word_conjugate (A : IntMatrix) (hA : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) :
    ∃ P Q : IntMatrix, ∃ u : List Bool,
      P.det = 1 ∧ Q.det = 1 ∧ P*Q = 1 ∧ Q*P = 1 ∧
      Q*A*P = intMatrix (matrixWord u) ∧ ∀ i j, 0 < matrixWord u i j := by
  obtain ⟨P,Q,hP,hQ,hPQ,hQP,hpos⟩ := exists_positive_integral_conjugate A hA ht
  obtain ⟨N,hN⟩ := exists_natMatrix (Q*A*P) hpos
  have hdet : (Q*A*P).det = 1 := by rw [Matrix.det_mul,Matrix.det_mul,hQ,hA,hP]; norm_num
  have hNu := (unimodular_iff_det N).mpr (show (intMatrix N).det = 1 by rw [hN]; exact hdet)
  obtain ⟨u,hu⟩ := exists_matrixWord N hNu
  refine ⟨P,Q,u,hP,hQ,hPQ,hQP,?_,?_⟩
  · rw [hu,hN]
  · intro i j
    have he : (N i j : ℤ) = (Q*A*P) i j := congrArg (fun M : IntMatrix => M i j) hN
    have hp : (0 : ℤ) < N i j := by rw [he]; exact hpos i j
    rw [hu]
    exact_mod_cast hp

#print axioms integral_root_iff_word_power
#print axioms exists_integral_word_conjugate

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerIntegralWords
