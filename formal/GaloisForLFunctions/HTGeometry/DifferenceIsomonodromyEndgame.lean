import GaloisForLFunctions.HTGeometry.GaloisAutConstantConnection

/-!
# A rigid difference equation with a constrained Galois monoid is isomonodromic

Conjugating the fundamental matrix by a matrix of constants conjugates every Galois matrix, so the
classification — which makes the Galois matrices constant after one conjugation — makes the Galois
matrices of the conjugated fundamental matrix differentially constant.  The logarithmic derivative
of that fundamental matrix is then Galois invariant, hence defined over the base, and differentiating
the system shows it solves the isomonodromy equation there.

The hypotheses are the ones the Bessel order recurrence supplies: no Riccati solution over the base,
a separating set of Galois points, and a scalar stabiliser cut out by a linear differential equation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

variable {K R C : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

omit [Nontrivial R] in
/-- **The Galois matrix of the fundamental matrix is the specialised comparison matrix.** -/
theorem invOf_mul_map_galoisAutAt (E : Subalgebra C (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) {n : ℕ} (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) :
    ⅟Y * Y.map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R)
      = (Matrix.of fun i j => algebraMap C R (χ ⟨Z i j, hZE i j⟩)) := by
  have hmap : Y.map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R)
      = Y * (Matrix.of fun i j => algebraMap C R (χ ⟨Z i j, hZE i j⟩)) := by
    ext i j
    rw [Matrix.map_apply, galoisAutAt_fundamental E b hgen hindep χ Y Z hZE hZ,
      Matrix.mul_apply]
    rfl
  rw [hmap, ← mul_assoc, invOf_mul_self, one_mul]

variable [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- **Isomonodromy over the base.**  A second-order difference equation without a base Riccati
solution, whose Galois monoid has a differentially constrained scalar stabiliser, carries a
connection over the base. -/
theorem isomonodromy_of_no_riccati_of_differentialSolution
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    (E : Subalgebra C (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = (A.map (algebraMap K R)) * Y)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hδgal : ∀ χ ∈ S, ∀ x : R, (galoisAutAt E b hgen hindep χ) (Differential.deriv x)
      = Differential.deriv ((galoisAutAt E b hgen hindep χ) x))
    {m : ℕ} (aa : Fin m → C)
    (hsol : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) (galoisMonoid E Z hZE S) →
      differentialJet m x = ∑ i, aa i * differentialJet (i : ℕ) x) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  classical
  obtain ⟨P, Q, hPQ, hQP, hcst⟩ :=
    constant_conjugate_galoisMonoid_of_no_riccati E b hgen hindep S hsep hcompat hconstC hsimple
      hric Y (Matrix.isUnit_det_of_invertible Y) hY1 hYrec Z hZE hZ aa hsol
  set PR : Matrix (Fin 2) (Fin 2) R := P.map (algebraMap C R) with hPR
  set QR : Matrix (Fin 2) (Fin 2) R := Q.map (algebraMap C R) with hQR
  have hPQR : PR * QR = 1 := by
    rw [hPR, hQR, ← Matrix.map_mul, hPQ]
    ext i j
    simp [Matrix.one_apply, Matrix.map_apply, apply_ite (algebraMap C R)]
  have hQPR : QR * PR = 1 := by
    rw [hPR, hQR, ← Matrix.map_mul, hQP]
    ext i j
    simp [Matrix.one_apply, Matrix.map_apply, apply_ite (algebraMap C R)]
  letI hQRinv : Invertible QR := ⟨PR, hPQR, hQPR⟩
  letI hYQ : Invertible (Y * QR) := invertibleMul Y QR
  have hσQR : QR.map ((σR : R ≃+* R) : R →+* R) = QR := by
    ext i j
    simp only [Matrix.map_apply, hQR]
    exact hconstC (Q i j)
  have hsys' : (Y * QR).map ((σR : R ≃+* R) : R →+* R) = (A.map (algebraMap K R)) * (Y * QR) := by
    rw [Matrix.map_mul, hsys, hσQR, mul_assoc]
  have hgalconj : ∀ χ ∈ S,
      matrixDeriv (⅟(Y * QR)
        * (Y * QR).map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R)) = 0 := by
    intro χ hχ
    have hφQR : QR.map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R) = QR := by
      ext i j
      simp only [Matrix.map_apply, hQR]
      exact (galoisAutAt E b hgen hindep χ).commutes (Q i j)
    have hgR := invOf_mul_map_galoisAutAt E b hgen hindep χ Y Z hZE hZ
    have hstep : ⅟(Y * QR)
        * (Y * QR).map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R)
        = (P * galoisMatrixAt E Z hZE χ * Q).map (algebraMap C R) := by
      have hQRinvEq : ⅟QR = PR := rfl
      rw [Matrix.map_mul, hφQR, invOf_mul, hQRinvEq]
      calc PR * ⅟Y * (Y.map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R) * QR)
          = PR * (⅟Y * Y.map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R)) * QR := by
            simp only [mul_assoc]
        _ = PR * (Matrix.of fun i j => algebraMap C R (χ ⟨Z i j, hZE i j⟩)) * QR := by
            rw [hgR]
        _ = (P * galoisMatrixAt E Z hZE χ * Q).map (algebraMap C R) := by
            rw [Matrix.map_mul, Matrix.map_mul, hPR, hQR]
            rfl
    rw [hstep]
    ext i j
    rw [matrixDeriv_apply, Matrix.map_apply, Matrix.zero_apply]
    have hx : ((P * galoisMatrixAt E Z hZE χ * Q) i j)′ = 0 :=
      hcst _ (galoisMatrixAt_mem_galoisMonoid E Z hZE S hχ) i j
    rw [deriv_algebraMap, hx, map_zero]
  obtain ⟨Bfun, hBfun⟩ : ∃ f : Fin 2 → Fin 2 → K,
      ∀ i j, logDerivMatrix (Y * QR) i j = algebraMap K R (f i j) := by
    have hex := exists_base_logDerivMatrix_of_galoisAutAt_constant E b hgen hindep S hsep
      (Y * QR) hδgal hgalconj
    choose f hf using hex
    exact ⟨f, hf⟩
  set B : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => Bfun i j with hB
  have hlog : logDerivMatrix (Y * QR) = B.map (algebraMap K R) := by
    ext i j
    rw [Matrix.map_apply, hB]
    exact hBfun i j
  have hiso := isomonodromy_of_fundamentalMatrix ((σR : R ≃+* R) : R →+* R) hσδ
    (A.map (algebraMap K R)) (Y * QR) hsys'
  rw [hlog] at hiso
  exact ⟨B, isomonodromy_descend ((σK : K ≃+* K) : K →+* K) ((σR : R ≃+* R) : R →+* R)
    hcompat A B hiso⟩

end

end GaloisForLFunctions.HTGeometry
