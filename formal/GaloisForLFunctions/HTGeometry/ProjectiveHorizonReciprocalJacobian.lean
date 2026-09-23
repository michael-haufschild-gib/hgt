import GaloisForLFunctions.HTGeometry.ProjectiveHorizonProlongation
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCramerJetSystem
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# The reconstruction Jacobian of the reciprocal observation

The reciprocal of the base jet coordinate has order zero, so by the prolongation formula the
derivative of its `m`-th jet along the `j`-th coordinate is `m choose j` times the `(m-j)`-th jet of
its order-zero derivative.  The Jacobian of the reciprocal jets against the missing coordinates is
therefore the shifted Pascal matrix in the jets of that derivative.

Those jets are algebraically independent, because against the coordinate derivations they are
triangular with nonzero diagonal, so the Jacobian specialises to the Pascal minor and its
determinant does not vanish.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

/-- The reciprocal of the base jet coordinate. -/
def recipBase (C : Type*) [Field C] : FreeScalarJetField C := (freeCoordinate C ℕ 0)⁻¹

/-- Its order-zero derivative, the principal symbol of every reciprocal jet. -/
def recipSymbol (C : Type*) [Field C] : FreeScalarJetField C :=
  freeCoordinateDerivation C ℕ 0 (recipBase C)

/-- The jets of that symbol. -/
def recipSymbolJet (C : Type*) [Field C] (k : ℕ) : FreeScalarJetField C :=
  (freeJetShift C)^[k] (recipSymbol C)

omit [CharZero C] in
theorem recipSymbol_eq :
    recipSymbol C = -((freeCoordinate C ℕ 0)⁻¹ ^ (2 : ℕ)) := by
  rw [recipSymbol, recipBase, Derivation.leibniz_inv,
    freeCoordinateDerivation_freeCoordinate_self, smul_eq_mul, mul_one]

omit [CharZero C] in
theorem recipSymbol_ne_zero : recipSymbol C ≠ 0 := by
  rw [recipSymbol_eq]
  exact neg_ne_zero.2 (pow_ne_zero 2 (inv_ne_zero (freeScalarJetCoordinate_ne_zero 0)))

omit [CharZero C] in
theorem recipBase_order_zero (j : ℕ) (hj : 0 < j) :
    freeCoordinateDerivation C ℕ j (recipBase C) = 0 := by
  rw [recipBase, Derivation.leibniz_inv,
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega), smul_zero]

omit [CharZero C] in
theorem recipSymbol_order_zero (j : ℕ) (hj : 0 < j) :
    freeCoordinateDerivation C ℕ j (recipSymbol C) = 0 := by
  rw [recipSymbol_eq, map_neg, Derivation.leibniz_pow, Derivation.leibniz_inv,
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega), smul_zero, smul_zero]
  simp

/-! ## Triangularity of the symbol jets -/

omit [CharZero C] in
theorem freeCoordinateDerivation_recipSymbolJet_of_gt {k j : ℕ} (hj : k < j) :
    freeCoordinateDerivation C ℕ j (recipSymbolJet C k) = 0 :=
  freeCoordinateDerivation_shift_iterate_of_gt
    (C := C) (fun i hi => recipSymbol_order_zero i hi) k j (by omega)

omit [CharZero C] in
theorem freeCoordinateDerivation_recipSymbolJet_top (k : ℕ) :
    freeCoordinateDerivation C ℕ k (recipSymbolJet C k) =
      freeCoordinateDerivation C ℕ 0 (recipSymbol C) := by
  have h := freeCoordinateDerivation_shift_iterate_top
    (C := C) (fun i hi => recipSymbol_order_zero i hi) k
  rwa [Nat.zero_add] at h

theorem freeCoordinateDerivation_recipSymbol_eq :
    freeCoordinateDerivation C ℕ 0 (recipSymbol C) =
      2 * ((freeCoordinate C ℕ 0)⁻¹) ^ (3 : ℕ) := by
  rw [recipSymbol_eq, map_neg, Derivation.leibniz_pow, Derivation.leibniz_inv,
    freeCoordinateDerivation_freeCoordinate_self]
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The principal symbol of the reciprocal never vanishes.** -/
theorem freeCoordinateDerivation_recipSymbol_ne_zero :
    freeCoordinateDerivation C ℕ 0 (recipSymbol C) ≠ 0 := by
  rw [freeCoordinateDerivation_recipSymbol_eq]
  exact mul_ne_zero two_ne_zero
    (pow_ne_zero 3 (inv_ne_zero (freeScalarJetCoordinate_ne_zero 0)))

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

/-! ## The symbol jets are algebraically independent -/

/-- The Jacobian of the first `N` symbol jets against the coordinate derivations of the same
indices. -/
def recipSymbolJacobian (C : Type*) [Field C] (N : ℕ) :
    Matrix (Fin N) (Fin N) (FreeScalarJetField C) :=
  Matrix.of fun i j => freeCoordinateDerivation C ℕ (i : ℕ) (recipSymbolJet C (j : ℕ))

theorem recipSymbolJacobian_det_ne_zero (N : ℕ) : (recipSymbolJacobian C N).det ≠ 0 := by
  have htri : (recipSymbolJacobian C N).BlockTriangular id := by
    intro i j hji
    exact freeCoordinateDerivation_recipSymbolJet_of_gt (C := C) (k := (j : ℕ)) (j := (i : ℕ)) hji
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  show freeCoordinateDerivation C ℕ (i : ℕ) (recipSymbolJet C (i : ℕ)) ≠ 0
  rw [freeCoordinateDerivation_recipSymbolJet_top]
  exact freeCoordinateDerivation_recipSymbol_ne_zero

theorem algebraicIndependent_recipSymbolBlock (N : ℕ) :
    AlgebraicIndependent C (fun i : Fin N => recipSymbolJet C (i : ℕ)) := by
  classical
  exact algebraicIndependent_of_domain_jacobian
    (K := C) (R := FreeScalarJetField C)
    (fun i : Fin N => recipSymbolJet C (i : ℕ))
    (fun i f => freeCoordinateDerivation C ℕ (i : ℕ) f)
    (fun i a b => map_add _ a b)
    (fun i a b => by rw [Derivation.leibniz]; simp only [smul_eq_mul])
    (fun i c => Derivation.map_algebraMap _ c)
    (recipSymbolJacobian C N) (recipSymbolJacobian_det_ne_zero N)
    (fun i j => rfl)

/-- **The jets of the reciprocal symbol are algebraically independent.** -/
theorem algebraicIndependent_recipSymbolJet :
    AlgebraicIndependent C (recipSymbolJet C) := by
  classical
  refine algebraicIndependent_of_finite_type fun t ht => ?_
  obtain ⟨b, hb⟩ := ht.bddAbove
  set N := b + 1 with hN
  have hlt : ∀ m : t, (m : ℕ) < N := by
    intro m
    have := hb m.2
    omega
  have hinj : Function.Injective (fun m : t => (⟨(m : ℕ), hlt m⟩ : Fin N)) := by
    intro a c hac
    exact Subtype.ext (congrArg Fin.val hac)
  have h := (algebraicIndependent_recipSymbolBlock (C := C) N).comp _ hinj
  exact h

/-! ## The reconstruction Jacobian -/

/-- The jets of the reciprocal of the base coordinate. -/
def recipJet (C : Type*) [Field C] (m : ℕ) : FreeScalarJetField C :=
  (freeJetShift C)^[m] (recipBase C)

omit [CharZero C] in
/-- **The prolongation of the reciprocal.**  The derivative of the `m`-th reciprocal jet along the
`j`-th coordinate is `m choose j` times the `(m-j)`-th symbol jet. -/
theorem freeCoordinateDerivation_recipJet {m j : ℕ} (hjm : j ≤ m) :
    freeCoordinateDerivation C ℕ j (recipJet C m) =
      (Nat.choose m j : FreeScalarJetField C) * recipSymbolJet C (m - j) :=
  freeCoordinateDerivation_shift_iterate_binomial
    (C := C) (fun i hi => recipBase_order_zero i hi) m j hjm

/-- The reconstruction Jacobian: rows are the coordinates `0, ..., r-1` and columns the reciprocal
jet orders `n, ..., n+r-1`. -/
def recipReconstructionJacobian (C : Type*) [Field C] (n r : ℕ) :
    Matrix (Fin r) (Fin r) (FreeScalarJetField C) :=
  Matrix.of fun k i => freeCoordinateDerivation C ℕ (k : ℕ) (recipJet C (n + (i : ℕ)))

omit [CharZero C] in
/-- **The reconstruction Jacobian is the Pascal matrix in the symbol jets.** -/
theorem recipReconstructionJacobian_eq {n r : ℕ} (hr : r ≤ n + 1) :
    recipReconstructionJacobian C n r =
      Matrix.transpose (cramerJetMatrix (FreeScalarJetField C) n r (recipSymbolJet C)) := by
  ext k i
  rw [recipReconstructionJacobian, Matrix.of_apply, Matrix.transpose_apply, cramerJetMatrix,
    Matrix.of_apply]
  exact freeCoordinateDerivation_recipJet (by have := k.2; omega)

/-- **The Pascal matrix in the symbol jets is nondegenerate.**  The symbol jets are algebraically
independent, so evaluation at them is injective and carries the nonvanishing Pascal determinant to
a nonvanishing determinant. -/
theorem det_cramerJetMatrix_recipSymbolJet_ne_zero (n r : ℕ) :
    (cramerJetMatrix (FreeScalarJetField C) n r (recipSymbolJet C)).det ≠ 0 := by
  classical
  intro hcon
  have key : (MvPolynomial.aeval (recipSymbolJet C) :
        MvPolynomial ℕ C →ₐ[C] FreeScalarJetField C).toRingHom
        (cramerJetMatrix (MvPolynomial ℕ C) n r MvPolynomial.X).det =
      (cramerJetMatrix (FreeScalarJetField C) n r (recipSymbolJet C)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, cramerJetMatrix_map]
    congr 1
    funext j
    simp
  refine det_cramerJetMatrix_X_ne_zero (K := C) n r ?_
  refine algebraicIndependent_recipSymbolJet (C := C) ?_
  rw [map_zero]
  rw [show (MvPolynomial.aeval (recipSymbolJet C) :
      MvPolynomial ℕ C →ₐ[C] FreeScalarJetField C)
        (cramerJetMatrix (MvPolynomial ℕ C) n r MvPolynomial.X).det =
      (MvPolynomial.aeval (recipSymbolJet C) :
        MvPolynomial ℕ C →ₐ[C] FreeScalarJetField C).toRingHom
        (cramerJetMatrix (MvPolynomial ℕ C) n r MvPolynomial.X).det from rfl, key, hcon]

/-- **The reconstruction Jacobian is nondegenerate.** -/
theorem det_recipReconstructionJacobian_ne_zero {n r : ℕ} (hr : r ≤ n + 1) :
    (recipReconstructionJacobian C n r).det ≠ 0 := by
  rw [recipReconstructionJacobian_eq hr, Matrix.det_transpose]
  exact det_cramerJetMatrix_recipSymbolJet_ne_zero n r

/-- **The recovered reciprocal jets are algebraically independent.**  From order `n` on, the next
`r` jets of the reciprocal of the base coordinate are algebraically independent over the base
field, because their Jacobian against the coordinates they recover is the nondegenerate Pascal
matrix in the symbol jets. -/
theorem algebraicIndependent_recipJet_block {n r : ℕ} (hr : r ≤ n + 1) :
    AlgebraicIndependent C (fun i : Fin r => recipJet C (n + (i : ℕ))) := by
  classical
  exact algebraicIndependent_of_domain_jacobian
    (K := C) (R := FreeScalarJetField C)
    (fun i : Fin r => recipJet C (n + (i : ℕ)))
    (fun k f => freeCoordinateDerivation C ℕ (k : ℕ) f)
    (fun k a b => map_add _ a b)
    (fun k a b => by rw [Derivation.leibniz]; simp only [smul_eq_mul])
    (fun k c => Derivation.map_algebraMap _ c)
    (recipReconstructionJacobian C n r)
    (det_recipReconstructionJacobian_ne_zero hr)
    (fun k i => rfl)

end

end GaloisForLFunctions.HTGeometry
