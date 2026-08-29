import GaloisForLFunctions.HTGeometry.MonoidTangentTranslation

/-!
# Left-invariant derivations of the jet ring, and bracket closure

For a matrix `Z` over the base, the assignment `𝐗_{ij}^{(k)} ↦ δ^k((𝐗·Z)_{ij})` extends uniquely to
a derivation `E_Z` of the differential polynomial ring in the matrix entries.  Its value at a matrix
`x` is the linearisation of the polynomial at `x` in the direction `x·Z` — the left-invariant vector
field of the matrix group in direction `Z`.

Two facts make it the tool that replaces the bi-dual numbers in Cassidy's classification:

* `E_Z` preserves the defining ideal of a zero set whose tangent directions translate — that is
  exactly the statement that the linearisation kills `x·Z` at every point `x`;
* the commutator of two of them is again one: `⁅E_Y, E_Z⁆ = E_{Y·Z − Z·Y}`.

Evaluating the second at the identity gives closure of the tangent space under the bracket, with no
second-order deformation theory and no group-scheme structure.

* `rightMulEntry`, `leftInvariantDeriv`;
* `evalOver_leftInvariantDeriv`;
* `leftInvariantDeriv_commutator`;
* `bracket_mem_matrixTangentM` — **bracket closure.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

attribute [local instance] differentialPolynomialOverDifferential

variable {C : Type*} [Field C] [Differential C]

/-- The entries of `𝐗 · Z`, as differential polynomials. -/
def rightMulEntry (Z : Matrix (Fin 2) (Fin 2) C) (q : Fin 2 × Fin 2) :
    DifferentialPolynomial (Fin 2 × Fin 2) C :=
  ∑ l : Fin 2, MvPolynomial.X (((q.1, l), 0) : (Fin 2 × Fin 2) × ℕ) * MvPolynomial.C (Z l q.2)

theorem evalOver_rightMulEntry (Z x : Matrix (Fin 2) (Fin 2) C) (q : Fin 2 × Fin 2) :
    differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
        (rightMulEntry Z q)
      = (x * Z) q.1 q.2 := by
  rw [rightMulEntry, map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, differentialPolynomialEvalOver_X, differentialPolynomialEvalOver_C,
    differentialJet_zero, Algebra.algebraMap_self_apply]

omit [Differential C] in
theorem rightMulEntry_add (Y Z : Matrix (Fin 2) (Fin 2) C) (q : Fin 2 × Fin 2) :
    rightMulEntry (Y + Z) q = rightMulEntry Y q + rightMulEntry Z q := by
  rw [rightMulEntry, rightMulEntry, rightMulEntry, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.add_apply, map_add, mul_add]

omit [Differential C] in
theorem rightMulEntry_neg (Z : Matrix (Fin 2) (Fin 2) C) (q : Fin 2 × Fin 2) :
    rightMulEntry (-Z) q = -rightMulEntry Z q := by
  rw [rightMulEntry, rightMulEntry, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.neg_apply, map_neg, mul_neg]

/-- **The left-invariant jet derivation** in direction `Z`. -/
def leftInvariantDeriv (Z : Matrix (Fin 2) (Fin 2) C) :
    Derivation C (DifferentialPolynomial (Fin 2 × Fin 2) C)
      (DifferentialPolynomial (Fin 2 × Fin 2) C) :=
  MvPolynomial.mkDerivation C
    (fun v : (Fin 2 × Fin 2) × ℕ => differentialJet v.2 (rightMulEntry Z v.1))

@[simp] theorem leftInvariantDeriv_X (Z : Matrix (Fin 2) (Fin 2) C) (v : (Fin 2 × Fin 2) × ℕ) :
    leftInvariantDeriv Z (MvPolynomial.X v) = differentialJet v.2 (rightMulEntry Z v.1) :=
  MvPolynomial.mkDerivation_X C _ v

theorem evalOver_differentialJet (x : Matrix (Fin 2) (Fin 2) C)
    (Q : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    ∀ k : ℕ, differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
        (differentialJet k Q)
      = differentialJet k (differentialPolynomialEvalOver (K := C)
          (fun r : Fin 2 × Fin 2 => x r.1 r.2) Q)
  | 0 => by rw [differentialJet_zero, differentialJet_zero]
  | (k + 1) => by
      rw [differentialJet_succ, differentialJet_succ, ← evalOver_differentialJet x Q k]
      exact differentialPolynomialEvalOver_derivation (K := C)
        (fun r : Fin 2 × Fin 2 => x r.1 r.2) (differentialJet k Q)

theorem leftInvariantDeriv_C (Z : Matrix (Fin 2) (Fin 2) C) (a : C) :
    leftInvariantDeriv Z (MvPolynomial.C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact Derivation.map_algebraMap _ a

/-- **The value of the left-invariant derivation is the linearisation in the translated
direction.** -/
theorem evalOver_leftInvariantDeriv (Z x : Matrix (Fin 2) (Fin 2) C)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
        (leftInvariantDeriv Z P)
      = (differentialPolynomialEvalOver (K := C)
          (dualPoint (fun r : Fin 2 × Fin 2 => x r.1 r.2)
            (fun r : Fin 2 × Fin 2 => (x * Z) r.1 r.2)) P).snd := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [leftInvariantDeriv_C, map_zero, differentialPolynomialEvalOver_C,
        TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
  | add p q hp hq =>
      rw [map_add, map_add, map_add, TrivSqZeroExt.snd_add, hp, hq]
  | mul_X p v hp =>
      have hXv : differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
          (MvPolynomial.X v) = differentialJet v.2 (x v.1.1 v.1.2) :=
        differentialPolynomialEvalOver_X _ _ _
      have hEZ : differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
          (leftInvariantDeriv Z (MvPolynomial.X v))
          = differentialJet v.2 ((x * Z) v.1.1 v.1.2) := by
        rw [leftInvariantDeriv_X, evalOver_differentialJet, evalOver_rightMulEntry]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [map_add, map_mul, map_mul, hEZ, hXv, hp, map_mul, TrivSqZeroExt.snd_mul,
        evalOver_dual_X, dualMk_snd, dualMk_fst, fst_differentialPolynomialEvalOver_dual]
      simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring

theorem differentialJet_sub (a b : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    ∀ k : ℕ, differentialJet k (a - b) = differentialJet k a - differentialJet k b
  | 0 => by rw [differentialJet_zero, differentialJet_zero, differentialJet_zero]
  | (k + 1) => by
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ,
        differentialJet_sub a b k, map_sub]

theorem deriv_mul_poly (a b : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    (a * b)′ = a′ * b + a * b′ := by
  show differentialPolynomialOverDerivation (Fin 2 × Fin 2) C (a * b)
    = differentialPolynomialOverDerivation (Fin 2 × Fin 2) C a * b
      + a * differentialPolynomialOverDerivation (Fin 2 × Fin 2) C b
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- The left-invariant derivation commutes with the total derivation. -/
theorem leftInvariantDeriv_deriv (W : Matrix (Fin 2) (Fin 2) C)
    (Q : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    leftInvariantDeriv W (Q′) = (leftInvariantDeriv W Q)′ := by
  have hgen : ∀ v : (Fin 2 × Fin 2) × ℕ,
      leftInvariantDeriv W ((MvPolynomial.X v : DifferentialPolynomial (Fin 2 × Fin 2) C)′)
        = (leftInvariantDeriv W (MvPolynomial.X v))′ := by
    intro v
    have hv : (MvPolynomial.X v : DifferentialPolynomial (Fin 2 × Fin 2) C)′
        = MvPolynomial.X ((v.1, v.2 + 1) : (Fin 2 × Fin 2) × ℕ) := by
      show differentialPolynomialOverDerivation (Fin 2 × Fin 2) C (MvPolynomial.X (v.1, v.2)) = _
      rw [differentialPolynomialOverDerivation_X]
    rw [hv, leftInvariantDeriv_X, leftInvariantDeriv_X, ← differentialJet_succ]
  induction Q using MvPolynomial.induction_on with
  | C a =>
      have hC : (MvPolynomial.C a : DifferentialPolynomial (Fin 2 × Fin 2) C)′
          = MvPolynomial.C (a′) := by
        show differentialPolynomialOverDerivation (Fin 2 × Fin 2) C (MvPolynomial.C a) = _
        rw [differentialPolynomialOverDerivation_C]
      rw [hC, leftInvariantDeriv_C, leftInvariantDeriv_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
      rw [deriv_mul_poly, map_add, Derivation.leibniz, Derivation.leibniz, hp, hgen v,
        Derivation.leibniz, map_add]
      simp only [smul_eq_mul]
      rw [deriv_mul_poly, deriv_mul_poly]
      ring

/-- **The commutator of two left-invariant derivations is the one of the commutator direction.** -/
theorem leftInvariantDeriv_commutator (Y Z : Matrix (Fin 2) (Fin 2) C) :
    ⁅leftInvariantDeriv Y, leftInvariantDeriv Z⁆ = leftInvariantDeriv (Y * Z - Z * Y) := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.commutator_apply, leftInvariantDeriv_X, leftInvariantDeriv_X,
    leftInvariantDeriv_X]
  have hcomm : ∀ (W : Matrix (Fin 2) (Fin 2) C) (Q : DifferentialPolynomial (Fin 2 × Fin 2) C)
      (k : ℕ), leftInvariantDeriv W (differentialJet k Q)
        = differentialJet k (leftInvariantDeriv W Q) := by
    intro W Q k
    induction k with
    | zero => rw [differentialJet_zero, differentialJet_zero]
    | succ k ih =>
        rw [differentialJet_succ, differentialJet_succ, ← ih]
        exact leftInvariantDeriv_deriv W (differentialJet k Q)
  rw [hcomm, hcomm]
  have hprod : ∀ (A B : Matrix (Fin 2) (Fin 2) C) (q : Fin 2 × Fin 2),
      leftInvariantDeriv A (rightMulEntry B q) = rightMulEntry (A * B) q := by
    intro A B q
    have hstep : ∀ l : Fin 2, leftInvariantDeriv A
        (MvPolynomial.X (((q.1, l), 0) : (Fin 2 × Fin 2) × ℕ) * MvPolynomial.C (B l q.2))
        = ∑ p : Fin 2, MvPolynomial.X (((q.1, p), 0) : (Fin 2 × Fin 2) × ℕ)
            * MvPolynomial.C (A p l * B l q.2) := by
      intro l
      rw [Derivation.leibniz, leftInvariantDeriv_C, smul_zero, zero_add, smul_eq_mul,
        leftInvariantDeriv_X, differentialJet_zero, rightMulEntry, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul]
      ring
    rw [rightMulEntry, map_sum, Finset.sum_congr rfl (fun l _ => hstep l),
      Finset.sum_comm, rightMulEntry]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_sum, ← map_sum, Matrix.mul_apply]
  rw [hprod, hprod, ← differentialJet_sub]
  congr 1
  rw [rightMulEntry, rightMulEntry, rightMulEntry, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.sub_apply, map_sub, mul_sub]


/-! ### Bracket closure -/

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- **Left-invariant derivations preserve the defining ideal** of a zero set whose tangent
directions translate, provided the ideal is the full vanishing ideal of its zero set. -/
theorem leftInvariantDeriv_mem_of_tangentTranslates
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hIS : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ g ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P = 0) →
      P ∈ S)
    {Z : Matrix (Fin 2) (Fin 2) C} (hZ : Z ∈ matrixTangentM S hone)
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C} (hP : P ∈ S) :
    leftInvariantDeriv Z P ∈ S := by
  refine hIS _ fun g hg => ?_
  rw [evalOver_leftInvariantDeriv]
  have hpt : (fun q : Fin 2 × Fin 2 => dualMatrix g (g * Z) q.1 q.2)
      = dualPoint (fun r : Fin 2 × Fin 2 => g r.1 r.2)
          (fun r : Fin 2 × Fin 2 => (g * Z) r.1 r.2) :=
    funext fun q => dualMatrix_eq_dualPoint g (g * Z) q
  have hval := htrans g hg Z hZ P hP
  rw [hpt] at hval
  rw [hval, TrivSqZeroExt.snd_zero]

/-- **Bracket closure of the tangent space**, with no second-order deformation theory, no dual or
bi-dual numbers beyond the first order, and no group-scheme structure.  The commutator of two
left-invariant derivations is the left-invariant derivation of the commutator direction, and both
factors preserve the defining ideal. -/
theorem bracket_mem_matrixTangentM
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hIS : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ g ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) P = 0) →
      P ∈ S)
    {Y Z : Matrix (Fin 2) (Fin 2) C} (hY : Y ∈ matrixTangentM S hone)
    (hZ : Z ∈ matrixTangentM S hone) :
    Y * Z - Z * Y ∈ matrixTangentM S hone := by
  show dualMatrix 1 (Y * Z - Z * Y) ∈ matrixZeroSet (C := C) (A := DualNumber C) S
  intro P hP
  have hpt : ∀ W : Matrix (Fin 2) (Fin 2) C,
      (fun q : Fin 2 × Fin 2 => dualMatrix 1 W q.1 q.2)
        = dualPoint (fun r : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) r.1 r.2)
            (fun r : Fin 2 × Fin 2 => W r.1 r.2) :=
    fun W => funext fun q => dualMatrix_eq_dualPoint 1 W q
  rw [hpt]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_differentialPolynomialEvalOver_dual, TrivSqZeroExt.fst_zero]
    exact hone P hP
  · rw [TrivSqZeroExt.snd_zero]
    have hone_mul : (1 : Matrix (Fin 2) (Fin 2) C) * (Y * Z - Z * Y) = Y * Z - Z * Y :=
      Matrix.one_mul _
    have hval := evalOver_leftInvariantDeriv (Y * Z - Z * Y)
      (1 : Matrix (Fin 2) (Fin 2) C) P
    rw [hone_mul] at hval
    rw [← hval, ← leftInvariantDeriv_commutator, Derivation.commutator_apply, map_sub]
    have hZP : leftInvariantDeriv Z P ∈ S :=
      leftInvariantDeriv_mem_of_tangentTranslates S htrans hIS hZ hP
    have hYP : leftInvariantDeriv Y P ∈ S :=
      leftInvariantDeriv_mem_of_tangentTranslates S htrans hIS hY hP
    have hstep : ∀ (W : Matrix (Fin 2) (Fin 2) C),
        W ∈ matrixTangentM S hone → ∀ Q ∈ S,
        differentialPolynomialEvalOver (K := C)
          (fun r : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) r.1 r.2)
          (leftInvariantDeriv W Q) = 0 := by
      intro W hW Q hQ
      have h1 := evalOver_leftInvariantDeriv W (1 : Matrix (Fin 2) (Fin 2) C) Q
      rw [Matrix.one_mul] at h1
      have hWmem : dualMatrix 1 W ∈ matrixZeroSet (C := C) (A := DualNumber C) S := hW
      have h2 := hWmem Q hQ
      rw [hpt W] at h2
      rw [h1, h2, TrivSqZeroExt.snd_zero]
    rw [hstep Y hY _ hZP, hstep Z hZ _ hYP, sub_zero]

end

end GaloisForLFunctions.HTGeometry
