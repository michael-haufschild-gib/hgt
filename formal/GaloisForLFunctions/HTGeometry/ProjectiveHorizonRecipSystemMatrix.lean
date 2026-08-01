import GaloisForLFunctions.HTGeometry.ProjectiveHorizonReciprocalRelations
import GaloisForLFunctions.HTGeometry.BinomialNodeDeterminant

/-!
# The reconstruction system of the reciprocal, and its nonsingularity

The reciprocal relations of orders `2n, 2n+1, ..., 4n-1` form a square system in the `2n` jets of
the base coordinate and of its reciprocal that lie below order `n`.  Its matrix pairs each unknown
coordinate jet with a binomial coefficient times a deep reciprocal jet, and each unknown reciprocal
jet with a binomial coefficient times a deep coordinate jet.

Clearing the denominators row by row turns that matrix into a polynomial one, and the exponential
specialisation carries the polynomial matrix to the alternating two-block binomial matrix, which is
nonsingular.  So the reconstruction system is nonsingular over the free jet field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C]

/-! ## The nodes -/

/-- The even reconstruction nodes. -/
def reconEven (n : ℕ) (i : Fin n) : ℕ := 2 * n + 2 * (i : ℕ)

/-- The odd reconstruction nodes. -/
def reconOdd (n : ℕ) (i : Fin n) : ℕ := 2 * n + 1 + 2 * (i : ℕ)

/-- All reconstruction nodes. -/
def reconNode (n : ℕ) : Fin n ⊕ Fin n → ℕ := Sum.elim (reconEven n) (reconOdd n)

theorem reconEven_injective (n : ℕ) : Function.Injective (reconEven n) := by
  intro a b hab
  rw [reconEven, reconEven] at hab
  exact Fin.ext (by omega)

theorem reconOdd_injective (n : ℕ) : Function.Injective (reconOdd n) := by
  intro a b hab
  rw [reconOdd, reconOdd] at hab
  exact Fin.ext (by omega)

theorem reconEven_even (n : ℕ) (i : Fin n) : Even (reconEven n i) :=
  ⟨n + (i : ℕ), by rw [reconEven]; omega⟩

theorem reconOdd_odd (n : ℕ) (i : Fin n) : Odd (reconOdd n i) :=
  ⟨n + (i : ℕ), by rw [reconOdd]; omega⟩

theorem two_mul_le_reconNode (n : ℕ) (r : Fin n ⊕ Fin n) : 2 * n ≤ reconNode n r := by
  cases r with
  | inl i => rw [reconNode, Sum.elim_inl, reconEven]; omega
  | inr i => rw [reconNode, Sum.elim_inr, reconOdd]; omega

theorem lt_reconNode {n : ℕ} (r : Fin n ⊕ Fin n) (k : Fin n) : (k : ℕ) < reconNode n r := by
  have h := two_mul_le_reconNode n r
  have := k.2
  omega

/-! ## The system matrix -/

/-- The reconstruction system matrix over the free jet field: each unknown coordinate jet is paired
with a deep reciprocal jet, and each unknown reciprocal jet with a deep coordinate jet. -/
def recipSystemMatrix (C : Type*) [Field C] (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (FreeScalarJetField C) :=
  Matrix.of fun r =>
    Sum.elim
      (fun k : Fin n => (Nat.choose (reconNode n r) (k : ℕ) : FreeScalarJetField C) *
        recipJet C (reconNode n r - (k : ℕ)))
      (fun j : Fin n => (Nat.choose (reconNode n r) (j : ℕ) : FreeScalarJetField C) *
        freeCoordinate C ℕ (reconNode n r - (j : ℕ)))

/-- The same matrix with the denominators cleared row by row. -/
def recipSystemPoly (C : Type*) [Field C] (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (FreeScalarJetPolynomial C) :=
  Matrix.of fun r =>
    Sum.elim
      (fun k : Fin n => (Nat.choose (reconNode n r) (k : ℕ) : FreeScalarJetPolynomial C) *
        recipNumer C (reconNode n r - (k : ℕ)) * MvPolynomial.X 0 ^ (k : ℕ))
      (fun j : Fin n => (Nat.choose (reconNode n r) (j : ℕ) : FreeScalarJetPolynomial C) *
        MvPolynomial.X (reconNode n r - (j : ℕ)) * MvPolynomial.X 0 ^ (reconNode n r + 1))

/-! ## The exponential specialisation of the system -/

/-- Substitution of one value for every jet coordinate. -/
def specOne (C : Type*) [Field C] : FreeScalarJetPolynomial C →+* C :=
  (Polynomial.evalRingHom (1 : C)).comp (expJetEval C).toRingHom

@[simp]
theorem specOne_X (j : ℕ) : specOne C (MvPolynomial.X j) = 1 := by
  rw [specOne, RingHom.comp_apply]
  show Polynomial.eval (1 : C) (expJetEval C (MvPolynomial.X j)) = 1
  rw [expJetEval_X, Polynomial.eval_X]

theorem specOne_recipNumer (j : ℕ) : specOne C (recipNumer C j) = (-1 : C) ^ j := by
  rw [specOne, RingHom.comp_apply]
  show Polynomial.eval (1 : C) (expJetEval C (recipNumer C j)) = _
  rw [expJetEval_recipNumer]
  simp

theorem neg_one_pow_sub (m k : ℕ) (hk : k ≤ m) : ((-1 : C)) ^ (m - k) = (-1 : C) ^ (m + k) := by
  have hsplit : m + k = (m - k) + 2 * k := by omega
  rw [hsplit, pow_add, pow_mul]
  norm_num

/-- **The specialised system is the alternating two-block binomial matrix.** -/
theorem map_recipSystemPoly (n : ℕ) :
    (recipSystemPoly C n).map (specOne C) = alternatingBinomBlock C (reconEven n) (reconOdd n) := by
  ext r c
  rw [Matrix.map_apply, recipSystemPoly, Matrix.of_apply, alternatingBinomBlock, Matrix.of_apply]
  cases c with
  | inl k =>
      rw [Sum.elim_inl, Sum.elim_inl, map_mul, map_mul, map_natCast, specOne_recipNumer,
        map_pow, specOne_X, one_pow, mul_one,
        neg_one_pow_sub _ _ (le_of_lt (lt_reconNode r k)), reconNode]
      ring
  | inr j =>
      rw [Sum.elim_inr, Sum.elim_inr, map_mul, map_mul, map_natCast, specOne_X, map_pow,
        specOne_X, one_pow, mul_one, mul_one]
      rfl

theorem det_recipSystemPoly_ne_zero [CharZero C] (n : ℕ) :
    (recipSystemPoly C n).det ≠ 0 := by
  intro hzero
  have hdet := det_alternatingBinomBlock_ne_zero (K := C) (reconEven_injective n)
    (reconOdd_injective n) (reconEven_even n) (reconOdd_odd n)
  refine hdet ?_
  rw [← map_recipSystemPoly (C := C) n, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hzero,
    map_zero]

/-! ## Nonsingularity over the free jet field -/

theorem algebraMap_recipSystemPoly (n : ℕ) :
    (recipSystemPoly C n).map
        (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)) =
      Matrix.diagonal (fun r => (freeCoordinate C ℕ 0) ^ (reconNode n r + 1)) *
        recipSystemMatrix C n := by
  have hX : ∀ i : ℕ,
      algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) (MvPolynomial.X i) =
        freeCoordinate C ℕ i := fun _ => rfl
  ext r c
  rw [Matrix.map_apply, Matrix.diagonal_mul, recipSystemPoly, Matrix.of_apply, recipSystemMatrix,
    Matrix.of_apply]
  cases c with
  | inl k =>
      have hk : (k : ℕ) ≤ reconNode n r := le_of_lt (lt_reconNode r k)
      have hexp : reconNode n r - (k : ℕ) + 1 + (k : ℕ) = reconNode n r + 1 := by omega
      rw [Sum.elim_inl, Sum.elim_inl, map_mul, map_mul, map_natCast, algebraMap_recipNumer,
        map_pow, hX]
      rw [show (Nat.choose (reconNode n r) (k : ℕ) : FreeScalarJetField C) *
            (recipJet C (reconNode n r - (k : ℕ)) *
              freeCoordinate C ℕ 0 ^ (reconNode n r - (k : ℕ) + 1)) *
            freeCoordinate C ℕ 0 ^ (k : ℕ) =
          (Nat.choose (reconNode n r) (k : ℕ) : FreeScalarJetField C) *
            recipJet C (reconNode n r - (k : ℕ)) *
              (freeCoordinate C ℕ 0 ^ (reconNode n r - (k : ℕ) + 1) *
                freeCoordinate C ℕ 0 ^ (k : ℕ)) from by ring,
        ← pow_add, hexp]
      ring
  | inr j =>
      rw [Sum.elim_inr, Sum.elim_inr, map_mul, map_mul, map_natCast, map_pow, hX, hX]
      ring

/-- **The reconstruction system is nonsingular.** -/
theorem det_recipSystemMatrix_ne_zero [CharZero C] (n : ℕ) :
    (recipSystemMatrix C n).det ≠ 0 := by
  intro hzero
  refine det_recipSystemPoly_ne_zero (C := C) n ?_
  have hinj : Function.Injective
      (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)) :=
    IsFractionRing.injective _ _
  refine hinj ?_
  rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, algebraMap_recipSystemPoly,
    Matrix.det_mul, hzero, mul_zero]

end

end GaloisForLFunctions.HTGeometry
