import GaloisForLFunctions.HTGeometry.TensorComparisonIsomonodromy
import GaloisForLFunctions.HTGeometry.DifferenceGaloisIrreducibility
import GaloisForLFunctions.HTGeometry.DifferentialGaloisSeparation

/-!
# Constant-conjugate differential points force isomonodromy

Suppose every differential specialization of a comparison matrix becomes derivation-constant after
one fixed conjugation.  Point separation makes the conjugated comparison matrix constant already
inside the tensor square.  Gauging the fundamental matrix by the same constant matrix then invokes
tensor-comparison descent and produces a connection over the base.

No torsor decomposition, module basis, fixed-field theorem, no-new-constants hypothesis, or
difference-simplicity hypothesis is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C]

/-- Pointwise constant conjugacy of the comparison matrices forces isomonodromy over the base. -/
theorem isomonodromy_of_pointwise_constant_conjugate
    (E : Subalgebra C (R ⊗[K] R))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (S : Set (E →ₐ[C] C))
    (hpoint : ∀ χ ∈ S, ∀ e (he : e ∈ E),
      χ ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩ =
        Differential.deriv (χ ⟨e, he⟩))
    (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = A.map (algebraMap K R) * Y)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (P Q : Matrix (Fin 2) (Fin 2) C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hconj : ∀ χ ∈ S, ∀ i j,
      (P * galoisMatrixAt E Z hZE χ * Q) i j ∈ differentialConstants C) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  let PE : Matrix (Fin 2) (Fin 2) E := P.map (algebraMap C E)
  let ZE : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ⟨Z i j, hZE i j⟩
  let QE : Matrix (Fin 2) (Fin 2) E := Q.map (algebraMap C E)
  let DE : Matrix (Fin 2) (Fin 2) E := PE * ZE * QE
  let D : Matrix (Fin 2) (Fin 2) (R ⊗[K] R) := DE.map E.val
  have hmapDE : ∀ χ : E →ₐ[C] C,
      DE.map χ = P * galoisMatrixAt E Z hZE χ * Q := by
    intro χ
    rw [show DE = PE * ZE * QE from rfl, Matrix.map_mul, Matrix.map_mul]
    have hPE : PE.map χ = P := by
      ext i j
      simp [PE]
    have hZEval : ZE.map χ = galoisMatrixAt E Z hZE χ := by
      ext i j
      rfl
    have hQE : QE.map χ = Q := by
      ext i j
      simp [QE]
    rw [hPE, hZEval, hQE]
  have hDconst : (Matrix.of fun i j =>
      tensorSquareDerivation (K := K) (D i j)) = 0 := by
    ext i j
    simp only [Matrix.of_apply, Matrix.zero_apply]
    change tensorSquareDerivation (K := K) ((DE i j : E) : R ⊗[K] R) = 0
    have hmem : ((DE i j : E) : R ⊗[K] R) ∈ E := (DE i j).property
    have hzeroE :
        (⟨tensorSquareDerivation (K := K) ((DE i j : E) : R ⊗[K] R),
          hEδ _ hmem⟩ : E) = 0 := by
      apply hsep
      intro χ hχ
      rw [hpoint χ hχ ((DE i j : E) : R ⊗[K] R) hmem]
      have hm := congrFun (congrFun (hmapDE χ) i) j
      change χ (DE i j) = (P * galoisMatrixAt E Z hZE χ * Q) i j at hm
      change Differential.deriv (χ (DE i j)) = 0
      rw [hm]
      exact mem_differentialConstants_iff.mp (hconj χ hχ i j)
    exact congrArg Subtype.val hzeroE
  let PT : Matrix (Fin 2) (Fin 2) (R ⊗[K] R) :=
    P.map (algebraMap C (R ⊗[K] R))
  let QT : Matrix (Fin 2) (Fin 2) (R ⊗[K] R) :=
    Q.map (algebraMap C (R ⊗[K] R))
  have hDform : D = PT * Z * QT := by
    rw [show D = DE.map E.val from rfl, show DE = PE * ZE * QE from rfl,
      Matrix.map_mul, Matrix.map_mul]
    have hPEval : PE.map E.val = PT := by
      ext i j
      simp [PE, PT]
    have hZEval : ZE.map E.val = Z := by
      ext i j
      rfl
    have hQEval : QE.map E.val = QT := by
      ext i j
      simp [QE, QT]
    rw [hPEval, hZEval, hQEval]
  let PR : Matrix (Fin 2) (Fin 2) R := P.map (algebraMap C R)
  let QR : Matrix (Fin 2) (Fin 2) R := Q.map (algebraMap C R)
  have hPQR : PR * QR = 1 := by
    rw [← Matrix.map_mul, hPQ]
    exact Matrix.map_one (algebraMap C R) (map_zero _) (map_one _)
  have hQPR : QR * PR = 1 := by
    rw [← Matrix.map_mul, hQP]
    exact Matrix.map_one (algebraMap C R) (map_zero _) (map_one _)
  letI hQRinv : Invertible QR := ⟨PR, hPQR, hQPR⟩
  let YQ : Matrix (Fin 2) (Fin 2) R := Y * QR
  letI : Invertible YQ := by
    refine ⟨PR * ⅟Y, ?_, ?_⟩
    · calc
        (PR * ⅟Y) * YQ = PR * (⅟Y * Y) * QR := by simp only [YQ, mul_assoc]
        _ = PR * QR := by rw [invOf_mul_self, mul_one]
        _ = 1 := hPQR
    · calc
        YQ * (PR * ⅟Y) = Y * (QR * PR) * ⅟Y := by simp only [YQ, mul_assoc]
        _ = Y * ⅟Y := by rw [hQPR, mul_one]
        _ = 1 := mul_invOf_self Y
  have hQRsigma : QR.map ((σR : R ≃+* R) : R →+* R) = QR := by
    ext i j
    exact hconstC (Q i j)
  have hsysQ : YQ.map ((σR : R ≃+* R) : R →+* R) =
      A.map (algebraMap K R) * YQ := by
    rw [show YQ = Y * QR from rfl, Matrix.map_mul, hQRsigma, hsys, mul_assoc]
  have hleftC : ∀ c : C,
      (algebraMap C R c) ⊗ₜ[K] (1 : R) = algebraMap C (R ⊗[K] R) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
    rfl
  have hrightC : ∀ c : C,
      (1 : R) ⊗ₜ[K] algebraMap C R c = algebraMap C (R ⊗[K] R) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply C K R]
    calc
      (1 : R) ⊗ₜ[K] algebraMap K R (algebraMap C K c) =
          (1 : R) ⊗ₜ[K] ((algebraMap C K c) • (1 : R)) := by
            simp [Algebra.smul_def]
      _ = ((algebraMap C K c) • (1 : R)) ⊗ₜ[K] (1 : R) := by
            exact (TensorProduct.smul_tmul (algebraMap C K c) (1 : R) (1 : R)).symm
      _ = algebraMap K R (algebraMap C K c) ⊗ₜ[K] (1 : R) := by
            simp [Algebra.smul_def]
      _ = (algebraMap C R c) ⊗ₜ[K] (1 : R) := by
            rw [IsScalarTower.algebraMap_apply C K R]
      _ = algebraMap C (R ⊗[K] R) c := hleftC c
  let incL : R →+* (R ⊗[K] R) :=
    (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] R).toRingHom
  let incR : R →+* (R ⊗[K] R) :=
    (Algebra.TensorProduct.includeRight : R →ₐ[K] R ⊗[K] R).toRingHom
  have hQL : QR.map incL = QT := by
    ext i j
    exact hleftC (Q i j)
  have hQR : QR.map incR = QT := by
    ext i j
    exact hrightC (Q i j)
  have hQPT : QT * PT = 1 := by
    rw [← Matrix.map_mul, hQP]
    exact Matrix.map_one (algebraMap C (R ⊗[K] R)) (map_zero _) (map_one _)
  have hYQL : YQ.map (fun x => x ⊗ₜ[K] (1 : R)) =
      Y.map incL * QT := by
    change YQ.map incL = _
    rw [show YQ = Y * QR from rfl, Matrix.map_mul, hQL]
  have hYQR : YQ.map (fun x => (1 : R) ⊗ₜ[K] x) =
      Y.map incR * QT := by
    change YQ.map incR = _
    rw [show YQ = Y * QR from rfl, Matrix.map_mul, hQR]
  have hfactorQ :
      (YQ.map (fun x => x ⊗ₜ[K] (1 : R))) * D =
        YQ.map (fun x => (1 : R) ⊗ₜ[K] x) := by
    rw [hYQL, hYQR, hDform]
    calc
      (Y.map incL * QT) * (PT * Z * QT) =
          Y.map incL * (QT * PT) * Z * QT := by
            simp only [mul_assoc]
      _ = Y.map incL * Z * QT := by rw [hQPT, mul_one]
      _ = Y.map incR * QT := by exact congrArg (fun M => M * QT) hZ
  exact isomonodromy_of_tensor_comparison_constant
    hcompat hσδ A YQ hsysQ D hfactorQ hDconst

end

end GaloisForLFunctions.HTGeometry
