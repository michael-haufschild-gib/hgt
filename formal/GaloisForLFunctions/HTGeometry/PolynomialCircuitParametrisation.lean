import GaloisForLFunctions.HTGeometry.OrbitExceptionalTimes

/-!
# A circuit is a polynomial parametrisation

The state prepared from a fixed input by a fixed sequence of gates is, coordinatewise, a *fixed*
polynomial in the gate entries with rational coefficients: only the parameters vary, not the
polynomials.  That is what turns a bounded-depth circuit into the image of a polynomial map, which
is the hypothesis of `AnalyticImageFiniteness.finite_meets_image`.

Two facts do it: evaluating the entries commutes with matrix-vector multiplication and with
products of matrices.  The second is `map_prod` for the algebra map `AlgHom.mapMatrix`, so it is
free once the first is stated.

The generic matrices — every entry its own indeterminate — realise every real gate sequence: a real
matrix family is the evaluation of the generic family at the tuple of its entries.  No unitarity is
imposed: constraints only shrink the parameter set, and the argument needs the reachable states to
lie *inside* a polynomial image, not to fill it.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {n m : ℕ}

/-! ## Evaluation commutes with the linear algebra -/

/-- Evaluating the entries commutes with matrix-vector multiplication. -/
theorem aeval_mulVec (u : Fin m → ℝ)
    (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℚ))
    (v : Fin n → MvPolynomial (Fin m) ℚ) (i : Fin n) :
    MvPolynomial.aeval u (A.mulVec v i)
      = (A.map (MvPolynomial.aeval u)).mulVec (fun j => MvPolynomial.aeval u (v j)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- Evaluating the entries commutes with products of matrices, taken in order. -/
theorem aeval_matrix_prod (u : Fin m → ℝ)
    (A : List (Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℚ))) :
    (A.prod).map (MvPolynomial.aeval u)
      = (A.map (fun N => Matrix.map N (MvPolynomial.aeval u))).prod := by
  have hhom := List.prod_hom A
    ((MvPolynomial.aeval u : MvPolynomial (Fin m) ℚ →ₐ[ℚ] ℝ).mapMatrix
      (m := Fin n))
  have hfun : (⇑((MvPolynomial.aeval u : MvPolynomial (Fin m) ℚ →ₐ[ℚ] ℝ).mapMatrix (m := Fin n)))
      = fun N => Matrix.map N (MvPolynomial.aeval u) := by
    funext N
    rfl
  rw [← hfun]
  exact hhom.symm

/-- **A circuit output is the evaluation of fixed polynomials.** -/
theorem aeval_circuit (u : Fin m → ℝ)
    (A : List (Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℚ)))
    (v : Fin n → MvPolynomial (Fin m) ℚ) (i : Fin n) :
    MvPolynomial.aeval u ((A.prod.mulVec v) i)
      = ((A.map (fun N => Matrix.map N (MvPolynomial.aeval u))).prod.mulVec
          (fun j => MvPolynomial.aeval u (v j))) i := by
  rw [aeval_mulVec, aeval_matrix_prod]

/-! ## Generic matrices realise every gate sequence -/

/-- The parameters of `s` matrices of size `n`: one indeterminate per entry. -/
noncomputable def paramIndex (s n : ℕ) : Fin s × Fin n × Fin n ≃ Fin (s * (n * n)) :=
  Fintype.equivFinOfCardEq (by simp)

/-- The `k`-th generic matrix: every entry its own indeterminate. -/
noncomputable def genericMatrix (s n : ℕ) (k : Fin s) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (s * (n * n))) ℚ) :=
  fun i j => MvPolynomial.X (paramIndex s n (k, i, j))

/-- The parameter tuple carrying a given family of real matrices. -/
noncomputable def paramOf (s n : ℕ) (M : Fin s → Matrix (Fin n) (Fin n) ℝ) :
    Fin (s * (n * n)) → ℝ :=
  fun idx => M ((paramIndex s n).symm idx).1 ((paramIndex s n).symm idx).2.1
    ((paramIndex s n).symm idx).2.2

/-- **Every real gate sequence is an evaluation of the generic one.** -/
theorem map_aeval_genericMatrix (s n : ℕ) (M : Fin s → Matrix (Fin n) (Fin n) ℝ) (k : Fin s) :
    (genericMatrix s n k).map (MvPolynomial.aeval (paramOf s n M)) = M k := by
  ext i j
  simp [genericMatrix, paramOf, Matrix.map_apply]

/-- **The states prepared by `s` gates lie in the image of one polynomial parametrisation.**  For
any real gate sequence and any input vector with rational entries, the prepared state is the
evaluation of the fixed generic coordinates at the tuple of gate entries. -/
theorem circuit_mem_image (s n : ℕ) (M : Fin s → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → MvPolynomial (Fin (s * (n * n))) ℚ) (i : Fin n) :
    ((List.ofFn M).prod.mulVec (fun j => MvPolynomial.aeval (paramOf s n M) (v j))) i
      = MvPolynomial.aeval (paramOf s n M)
          (((List.ofFn (genericMatrix s n)).prod.mulVec v) i) := by
  rw [aeval_circuit]
  have hlist : (List.ofFn (genericMatrix s n)).map
      (fun N => Matrix.map N (MvPolynomial.aeval (paramOf s n M))) = List.ofFn M := by
    rw [List.map_ofFn]
    congr 1
    funext k
    exact map_aeval_genericMatrix s n M k
  rw [hlist]

end GaloisForLFunctions.HTGeometry
