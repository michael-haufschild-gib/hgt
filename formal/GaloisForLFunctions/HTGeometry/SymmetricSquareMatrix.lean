import GaloisForLFunctions.HTGeometry.Sl2ProperAdjointNormalForm

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CommRing A]

/-- Symmetric product coordinates `(x₀y₀, x₀y₁+x₁y₀, x₁y₁)`. -/
def symmetricPair (x y : Fin 2 → A) : Fin 3 → A :=
  ![x 0 * y 0, x 0 * y 1 + x 1 * y 0, x 1 * y 1]

/-- Matrix of the symmetric-square representation in product coordinates. -/
def symmetricSquareMatrix (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix (Fin 3) (Fin 3) A :=
  !![M 0 0 ^ 2, M 0 0 * M 0 1, M 0 1 ^ 2;
     2 * M 0 0 * M 1 0, M 0 0 * M 1 1 + M 0 1 * M 1 0, 2 * M 0 1 * M 1 1;
     M 1 0 ^ 2, M 1 0 * M 1 1, M 1 1 ^ 2]

/-- Symmetric products intertwine matrix-vector multiplication. -/
theorem symmetricPair_mulVec (M : Matrix (Fin 2) (Fin 2) A) (x y : Fin 2 → A) :
    symmetricPair (M.mulVec x) (M.mulVec y) =
      (symmetricSquareMatrix M).mulVec (symmetricPair x y) := by
  funext i
  fin_cases i <;>
    simp [symmetricPair, symmetricSquareMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- The symmetric-square construction preserves multiplication. -/
theorem symmetricSquareMatrix_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    symmetricSquareMatrix (M * N) =
      symmetricSquareMatrix M * symmetricSquareMatrix N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricSquareMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

@[simp] theorem symmetricSquareMatrix_one :
    symmetricSquareMatrix (1 : Matrix (Fin 2) (Fin 2) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricSquareMatrix]

/-- The symmetric-square construction commutes with coefficient maps. -/
theorem symmetricSquareMatrix_map
    {B : Type*} [CommRing B] (f : A →+* B) (M : Matrix (Fin 2) (Fin 2) A) :
    (symmetricSquareMatrix M).map f = symmetricSquareMatrix (M.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricSquareMatrix, map_ofNat]

/-- Matrix-vector multiplication is linear in the vector. -/
theorem matrix_mulVec_smul (M : Matrix (Fin 3) (Fin 3) A) (a : A) (v : Fin 3 → A) :
    M.mulVec (a • v) = a • M.mulVec v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The symmetric product of the two columns of an invertible matrix is nonzero. -/
theorem symmetricPair_columns_ne_zero
    [Nontrivial A] (P Q : Matrix (Fin 2) (Fin 2) A) (hPQ : P * Q = 1) :
    symmetricPair (fun i => P i 0) (fun i => P i 1) ≠ 0 := by
  intro hzero
  have h0 : P 0 0 * P 0 1 = 0 := by
    simpa [symmetricPair] using congrFun hzero 0
  have h1 : P 0 0 * P 1 1 + P 1 0 * P 0 1 = 0 := by
    simpa [symmetricPair] using congrFun hzero 1
  have h2 : P 1 0 * P 1 1 = 0 := by
    simpa [symmetricPair] using congrFun hzero 2
  have hdetSq : P.det ^ 2 = 0 := by
    rw [Matrix.det_fin_two]
    calc
      (P 0 0 * P 1 1 - P 0 1 * P 1 0) ^ 2 =
          (P 0 0 * P 1 1 + P 1 0 * P 0 1) ^ 2 -
            4 * (P 0 0 * P 0 1) * (P 1 0 * P 1 1) := by ring
      _ = 0 := by rw [h0, h1, h2]; ring
  have hdetprod : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have hone : P.det ^ 2 * Q.det ^ 2 = 1 := by
    calc
      P.det ^ 2 * Q.det ^ 2 = (P.det * Q.det) ^ 2 := by ring
      _ = 1 := by rw [hdetprod]; ring
  rw [hdetSq, zero_mul] at hone
  exact zero_ne_one hone

end

section

variable {F : Type*} [Field F]

/-- An invariant unordered pair of lines becomes an invariant line in the symmetric square. -/
theorem exists_symmetricSquare_semiInvariant_of_invariantPairNormalForm
    {G : Set (Matrix (Fin 2) (Fin 2) F)} (hpair : HasInvariantPairNormalForm G) :
    ∃ c : Fin 3 → F, c ≠ 0 ∧ ∀ g ∈ G, ∃ lam : F,
      (symmetricSquareMatrix g).mulVec c = lam • c := by
  obtain ⟨P, Q, hPQ, hQP, hnormal⟩ := hpair
  let m : Fin 3 → F := ![0, 1, 0]
  let c : Fin 3 → F := (symmetricSquareMatrix P).mulVec m
  have hc : c ≠ 0 := by
    intro hc0
    have hback := congrArg (fun v => (symmetricSquareMatrix Q).mulVec v) hc0
    have hQP' : symmetricSquareMatrix Q * symmetricSquareMatrix P = 1 := by
      rw [← symmetricSquareMatrix_mul, hQP, symmetricSquareMatrix_one]
    rw [show c = (symmetricSquareMatrix P).mulVec m from rfl,
      Matrix.mulVec_mulVec, hQP', Matrix.one_mulVec, Matrix.mulVec_zero] at hback
    have hm : m 1 = 0 := congrFun hback 1
    simp [m] at hm
  refine ⟨c, hc, ?_⟩
  intro g hg
  let T := Q * g * P
  have hGP : g * P = P * T := by
    dsimp [T]
    calc
      g * P = (P * Q) * g * P := by rw [hPQ, one_mul]
      _ = P * (Q * g * P) := by noncomm_ring
  rcases hnormal g hg with hdiag | hanti
  · refine ⟨T 0 0 * T 1 1, ?_⟩
    change T 0 1 = 0 ∧ T 1 0 = 0 at hdiag
    have hTm : (symmetricSquareMatrix T).mulVec m =
        (T 0 0 * T 1 1) • m := by
      funext i
      fin_cases i <;>
        simp [symmetricSquareMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          m, hdiag.1, hdiag.2]
    calc
      (symmetricSquareMatrix g).mulVec c =
          (symmetricSquareMatrix g).mulVec ((symmetricSquareMatrix P).mulVec m) := rfl
      _ = (symmetricSquareMatrix (g * P)).mulVec m := by
        rw [Matrix.mulVec_mulVec, symmetricSquareMatrix_mul]
      _ = (symmetricSquareMatrix (P * T)).mulVec m := by rw [hGP]
      _ = (symmetricSquareMatrix P).mulVec ((symmetricSquareMatrix T).mulVec m) := by
        rw [symmetricSquareMatrix_mul, Matrix.mulVec_mulVec]
      _ = (symmetricSquareMatrix P).mulVec ((T 0 0 * T 1 1) • m) := by rw [hTm]
      _ = (T 0 0 * T 1 1) • c := matrix_mulVec_smul _ _ _
  · refine ⟨T 0 1 * T 1 0, ?_⟩
    change T 0 0 = 0 ∧ T 1 1 = 0 at hanti
    have hTm : (symmetricSquareMatrix T).mulVec m =
        (T 0 1 * T 1 0) • m := by
      funext i
      fin_cases i <;>
        simp [symmetricSquareMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          m, hanti.1, hanti.2, mul_comm]
    calc
      (symmetricSquareMatrix g).mulVec c =
          (symmetricSquareMatrix g).mulVec ((symmetricSquareMatrix P).mulVec m) := rfl
      _ = (symmetricSquareMatrix (g * P)).mulVec m := by
        rw [Matrix.mulVec_mulVec, symmetricSquareMatrix_mul]
      _ = (symmetricSquareMatrix (P * T)).mulVec m := by rw [hGP]
      _ = (symmetricSquareMatrix P).mulVec ((symmetricSquareMatrix T).mulVec m) := by
        rw [symmetricSquareMatrix_mul, Matrix.mulVec_mulVec]
      _ = (symmetricSquareMatrix P).mulVec ((T 0 1 * T 1 0) • m) := by rw [hTm]
      _ = (T 0 1 * T 1 0) • c := matrix_mulVec_smul _ _ _

/-- A common invariant coordinate line after change of basis is a genuine semi-invariant vector. -/
theorem exists_semiInvariant_of_invariantLineNormalForm
    {G : Set (Matrix (Fin 2) (Fin 2) F)} (hline : HasInvariantLineNormalForm G) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ ∀ g ∈ G, ∃ lam : F, g.mulVec c = lam • c := by
  obtain ⟨P, Q, hPQ, hQP, hnormal⟩ := hline
  have hGP (g : Matrix (Fin 2) (Fin 2) F) : g * P = P * (Q * g * P) := by
    calc
      g * P = (P * Q) * g * P := by rw [hPQ, one_mul]
      _ = P * (Q * g * P) := by noncomm_ring
  rcases hnormal with hlower | hupper
  · let e : Fin 2 → F := ![1, 0]
    let c : Fin 2 → F := P.mulVec e
    have hc : c ≠ 0 := by
      intro hc0
      have hback := congrArg (fun v => Q.mulVec v) hc0
      rw [show c = P.mulVec e from rfl, Matrix.mulVec_mulVec, hQP,
        Matrix.one_mulVec, Matrix.mulVec_zero] at hback
      have he := congrFun hback 0
      simp [e] at he
    refine ⟨c, hc, ?_⟩
    intro g hg
    let T := Q * g * P
    have hT : T.mulVec e = T 0 0 • e := by
      have hzero : T 1 0 = 0 := hlower g hg
      funext i
      fin_cases i <;>
        simp [T, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hzero]
    refine ⟨T 0 0, ?_⟩
    calc
      g.mulVec c = g.mulVec (P.mulVec e) := rfl
      _ = (g * P).mulVec e := Matrix.mulVec_mulVec _ _ _
      _ = (P * T).mulVec e := by rw [hGP]
      _ = P.mulVec (T.mulVec e) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = P.mulVec (T 0 0 • e) := by rw [hT]
      _ = T 0 0 • c := by
        funext i
        fin_cases i <;> simp [c, e, Matrix.mulVec, dotProduct] <;> ring
  · let e : Fin 2 → F := ![0, 1]
    let c : Fin 2 → F := P.mulVec e
    have hc : c ≠ 0 := by
      intro hc0
      have hback := congrArg (fun v => Q.mulVec v) hc0
      rw [show c = P.mulVec e from rfl, Matrix.mulVec_mulVec, hQP,
        Matrix.one_mulVec, Matrix.mulVec_zero] at hback
      have he := congrFun hback 1
      simp [e] at he
    refine ⟨c, hc, ?_⟩
    intro g hg
    let T := Q * g * P
    have hT : T.mulVec e = T 1 1 • e := by
      have hzero : T 0 1 = 0 := hupper g hg
      funext i
      fin_cases i <;>
        simp [T, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hzero]
    refine ⟨T 1 1, ?_⟩
    calc
      g.mulVec c = g.mulVec (P.mulVec e) := rfl
      _ = (g * P).mulVec e := Matrix.mulVec_mulVec _ _ _
      _ = (P * T).mulVec e := by rw [hGP]
      _ = P.mulVec (T.mulVec e) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = P.mulVec (T 1 1 • e) := by rw [hT]
      _ = T 1 1 • c := by
        funext i
        fin_cases i <;> simp [c, e, Matrix.mulVec, dotProduct] <;> ring

end

end GaloisForLFunctions.HTGeometry
