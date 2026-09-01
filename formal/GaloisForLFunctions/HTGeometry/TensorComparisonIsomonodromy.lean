import GaloisForLFunctions.HTGeometry.TensorSquareEqualizer
import GaloisForLFunctions.HTGeometry.TensorSquareDerivation
import GaloisForLFunctions.HTGeometry.FundamentalMatrixIsomonodromy

/-!
# Isomonodromy from a constant tensor comparison

Two tensor copies of a fundamental matrix differ by a comparison matrix.  If that comparison
matrix is constant for the tensor-square derivation, then the two tensor copies of the fundamental
matrix's logarithmic derivative agree.  The tensor-square equalizer descends every entry to the
base field, producing an isomonodromy connection there.

This descent uses no torsor basis, fixed-field theorem, no-new-constants hypothesis, or simplicity
hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
/-- A ring homomorphism sends an invertible matrix to an invertible matrix, with no requirement that
source and target rings coincide. -/
@[reducible] def invertibleMapRingHomTo {S : Type*} [CommRing S] (f : R →+* S)
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) [Invertible M] : Invertible (M.map f) where
  invOf := (⅟M).map f
  invOf_mul_self := by
    rw [← Matrix.map_mul, invOf_mul_self]
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply]
    split <;> simp
  mul_invOf_self := by
    rw [← Matrix.map_mul, mul_invOf_self]
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply]
    split <;> simp

/-- The logarithmic derivative is natural for a derivation-preserving ring homomorphism between
possibly different rings. -/
theorem logDerivMatrix_map_to {S : Type*} [CommRing S] [Differential S]
    (f : R →+* S) (hf : ∀ x : R, f (Differential.deriv x) = Differential.deriv (f x))
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) [Invertible M] [Invertible (M.map f)] :
    (logDerivMatrix M).map f = logDerivMatrix (M.map f) := by
  have hderiv : matrixDeriv (M.map f) = (matrixDeriv M).map f := by
    ext i j
    exact (hf (M i j)).symm
  have hinv : (⅟M).map f = ⅟(M.map f) := by
    refine (invOf_eq_right_inv ?_).symm
    rw [← Matrix.map_mul, mul_invOf_self]
    ext i j
    simp only [Matrix.map_apply, Matrix.one_apply]
    split <;> simp
  simp only [logDerivMatrix, Matrix.map_mul]
  rw [hinv, hderiv]

/-- A derivation-constant tensor comparison descends the fundamental logarithmic derivative to the
base field. -/
theorem exists_base_logDerivMatrix_of_tensor_comparison_constant [Nontrivial R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (Y : Matrix n n R) [Invertible Y]
    (D : Matrix n n (R ⊗[K] R))
    (hD : (Y.map (fun x => x ⊗ₜ[K] (1 : R))) * D =
      Y.map (fun x => (1 : R) ⊗ₜ[K] x))
    (hDconst : (Matrix.of fun i j =>
      tensorSquareDerivation (K := K) (D i j)) = 0) :
    ∃ B : Matrix n n K, logDerivMatrix Y = B.map (algebraMap K R) := by
  letI : Differential (R ⊗[K] R) :=
    { deriv := tensorSquareDerivation (K := K) }
  let incL : R →+* (R ⊗[K] R) :=
    (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] R).toRingHom
  let incR : R →+* (R ⊗[K] R) :=
    (Algebra.TensorProduct.includeRight : R →ₐ[K] R ⊗[K] R).toRingHom
  let L : Matrix n n (R ⊗[K] R) := Y.map incL
  let RR : Matrix n n (R ⊗[K] R) := Y.map incR
  letI hLinv : Invertible L := by
    dsimp [L]
    exact invertibleMapRingHomTo incL Y
  letI hRinv : Invertible RR := by
    dsimp [RR]
    exact invertibleMapRingHomTo incR Y
  have hfactor : L * D = RR := by
    exact hD
  have hincL : ∀ x : R, incL (Differential.deriv x) = Differential.deriv (incL x) := by
    intro x
    change Differential.deriv x ⊗ₜ[K] (1 : R) =
      tensorSquareDerivation (K := K) (x ⊗ₜ[K] (1 : R))
    rw [tensorSquareDerivation_tmul, Derivation.map_one_eq_zero]
    simp
  have hincR : ∀ x : R, incR (Differential.deriv x) = Differential.deriv (incR x) := by
    intro x
    change (1 : R) ⊗ₜ[K] Differential.deriv x =
      tensorSquareDerivation (K := K) ((1 : R) ⊗ₜ[K] x)
    rw [tensorSquareDerivation_tmul, Derivation.map_one_eq_zero]
    simp
  have hDderiv : matrixDeriv D = 0 := by
    exact hDconst
  have hdiff := congrArg matrixDeriv hfactor
  rw [matrixDeriv_mul, hDderiv, mul_zero, add_zero] at hdiff
  have hDinvR : D * ⅟RR = ⅟L := by
    have hmul : L * (D * ⅟RR) = L * ⅟L := by
      calc
        L * (D * ⅟RR) = (L * D) * ⅟RR := by rw [mul_assoc]
        _ = RR * ⅟RR := by rw [hfactor]
        _ = 1 := mul_invOf_self RR
        _ = L * ⅟L := (mul_invOf_self L).symm
    have hcancel := congrArg (fun M => ⅟L * M) hmul
    simpa only [← mul_assoc, invOf_mul_self, one_mul] using hcancel
  have hlog : logDerivMatrix L = logDerivMatrix RR := by
    simp only [logDerivMatrix]
    calc
      matrixDeriv L * ⅟L = matrixDeriv L * (D * ⅟RR) := by rw [hDinvR]
      _ = (matrixDeriv L * D) * ⅟RR := by rw [mul_assoc]
      _ = matrixDeriv RR * ⅟RR := by rw [hdiff]
  have hleft : (logDerivMatrix Y).map incL = logDerivMatrix L := by
    exact logDerivMatrix_map_to incL hincL Y
  have hright : (logDerivMatrix Y).map incR = logDerivMatrix RR := by
    exact logDerivMatrix_map_to incR hincR Y
  have heq : (logDerivMatrix Y).map incL = (logDerivMatrix Y).map incR := by
    rw [hleft, hright, hlog]
  have hbase : ∀ i j, ∃ c : K,
      logDerivMatrix Y i j = algebraMap K R c := by
    intro i j
    apply exists_eq_algebraMap_of_tmul_comm
    exact congrFun (congrFun heq i) j
  choose B hB using hbase
  refine ⟨Matrix.of fun i j => B i j, ?_⟩
  ext i j
  exact hB i j

/-- A derivation-constant tensor comparison gives an isomonodromy connection over the base. -/
theorem isomonodromy_of_tensor_comparison_constant [Nontrivial R]
    {n : Type*} [Fintype n] [DecidableEq n]
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (A : Matrix n n K) (Y : Matrix n n R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = A.map (algebraMap K R) * Y)
    (D : Matrix n n (R ⊗[K] R))
    (hD : (Y.map (fun x => x ⊗ₜ[K] (1 : R))) * D =
      Y.map (fun x => (1 : R) ⊗ₜ[K] x))
    (hDconst : (Matrix.of fun i j =>
      tensorSquareDerivation (K := K) (D i j)) = 0) :
    ∃ B : Matrix n n K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  obtain ⟨B, hB⟩ := exists_base_logDerivMatrix_of_tensor_comparison_constant
    Y D hD hDconst
  refine ⟨B, isomonodromy_descend
    ((σK : K ≃+* K) : K →+* K) ((σR : R ≃+* R) : R →+* R) hcompat A B ?_⟩
  have h := isomonodromy_of_fundamentalMatrix
    ((σR : R ≃+* R) : R →+* R) hσδ (A.map (algebraMap K R)) Y hsys
  rw [hB] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
