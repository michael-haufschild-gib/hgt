import GaloisForLFunctions.HTGeometry.ConstantConjugateTensorDescent
import GaloisForLFunctions.HTGeometry.CassidyMonoidDichotomy
import GaloisForLFunctions.HTGeometry.DifferentialCassidyClassification
import GaloisForLFunctions.HTGeometry.DifferentialGaloisScalarZeroSet
import GaloisForLFunctions.HTGeometry.TensorDifferentialPointsDiffFG
import GaloisForLFunctions.HTGeometry.FiniteConstantSpanOperator

/-!
# Basis-free Galois-monoid descent

Cassidy's constant-conjugacy conclusion descends a parameterized connection directly through
differential points.  Explicit irreducibility replaces the old torsor-basis and
difference-simplicity route; finite differential generation supplies point separation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

omit [DifferentialAlgebra C R] in
/-- Irreducibility and one scalar differential constraint force isomonodromy, with point
separation supplied directly. -/
theorem isomonodromy_of_irreducible_of_differentialSolution
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
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
    (hirr : ∀ v : Fin 2 → C, v ≠ 0 → ∀ u : Fin 2 → C,
      u ∈ Submodule.span C {x : Fin 2 → C |
        ∃ g ∈ galoisMonoid E Z hZE S, g.mulVec v = x})
    {m : ℕ} (aa : Fin m → C)
    (hsol : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) (galoisMonoid E Z hZE S) →
      differentialJet m x = ∑ i, aa i * differentialJet (i : ℕ) x) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  let G := galoisMonoid E Z hZE S
  have hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G := Submonoid.one_mem _
  have hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G := fun _ hg _ hh => Submonoid.mul_mem _ hg hh
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ :=
    constant_conjugate_of_irreducible G hone hmul hirr aa hsol
  exact isomonodromy_of_pointwise_constant_conjugate E hEδ S hpoint hsep hcompat hconstC hσδ
    A Y hsys Z hZE hZ P Q hPQ hQP
    (fun χ hχ => hconj (galoisMatrixAt E Z hZE χ)
      (galoisMatrixAt_mem_galoisMonoid E Z hZE S hχ))

/-- A finite comparison Galois monoid forces isomonodromy directly: finiteness gives one common
linear differential operator on all matrix entries, and irreducibility descends the resulting
constant conjugacy through separating differential points. -/
theorem isomonodromy_of_finite_galoisMonoid_irreducible_jetAdjoin
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (E : Subalgebra C (R ⊗[K] R))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] {k : ℕ} (v : Fin k → R ⊗[K] R) (hv : ∀ i, v i ∈ E)
    (hadj : Algebra.adjoin C
      (Set.range fun p : Fin k × ℕ => tensorJet (K := K) p.2 (v p.1)) = E)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = A.map (algebraMap K R) * Y)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hirr : ∀ q : Fin 2 → C, q ≠ 0 → ∀ u : Fin 2 → C,
      u ∈ Submodule.span C {x : Fin 2 → C |
        ∃ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ), g.mulVec q = x})
    (hfinite : (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) :
      Set (Matrix (Fin 2) (Fin 2) C)).Finite) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  let S := tensorDifferentialPoints E hEδ
  let G := galoisMonoid E Z hZE S
  have hGone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G := Submonoid.one_mem _
  have hGmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G :=
    fun _ ha _ hb => Submonoid.mul_mem _ ha hb
  obtain ⟨n, Lop, i₀, hi₀, hL, hGL⟩ :=
    exists_nonzero_linearJet_relation_of_finite_matrixSet hfinite
  have hderiv : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
      Submodule.span (differentialConstants C) G → Differential.deriv x = 0 :=
    deriv_eq_zero_of_scalarSpan_of_linear G hGone hGmul hi₀ hL hGL
  refine isomonodromy_of_irreducible_of_differentialSolution E hEδ S
    (fun χ hχ => hχ)
    (fun e he => eq_zero_of_forall_mem_tensorDifferentialPoints_of_jetAdjoin
      E hEδ v hv hadj e he)
    hcompat hconstC hσδ A Y hsys Z hZE hZ hirr (m := 1) (aa := fun _ => 0) ?_
  intro x hx
  rw [differentialJet_succ, differentialJet_zero, hderiv x hx]
  simp

/-- Determinant-one Cassidy dichotomy with the isomonodromy branch descended directly from
differential points.  Finite differential generation supplies point separation, while explicit
irreducibility replaces every torsor-basis and difference-simplicity premise. -/
theorem isomonodromy_or_sl2_galoisMonoid_detOne_irreducible_jetAdjoin
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (hrank : NoUniversalJetRelation C)
    (E : Subalgebra C (R ⊗[K] R))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] {k : ℕ} (v : Fin k → R ⊗[K] R) (hv : ∀ i, v i ∈ E)
    (hadj : Algebra.adjoin C
      (Set.range fun p : Fin k × ℕ => tensorJet (K := K) p.2 (v p.1)) = E)
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = A.map (algebraMap K R) * Y)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hirr : ∀ q : Fin 2 → C, q ≠ 0 → ∀ u : Fin 2 → C,
      u ∈ Submodule.span C {x : Fin 2 → C |
        ∃ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ), g.mulVec q = x})
    (hdense : ∀ W : Matrix (Fin 2) (Fin 2) C, W.trace = 0 →
      W ∈ Submodule.span C
        ((matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) | h.det = 1})
          (subset_matrixZeroSet_vanishingIdeal _
            ⟨Submonoid.one_mem _, Matrix.det_one⟩) : Submodule _ _) : Set _))
    (hGdetK : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ),
      g.det ∈ differentialConstants C)
    (hGdet0 : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ), g.det ≠ 0)
    (hGinv : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ),
      ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
        ∀ W ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) | h.det = 1})
          (subset_matrixZeroSet_vanishingIdeal _ ⟨Submonoid.one_mem _, Matrix.det_one⟩),
          g * W * g' ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) | h.det = 1})
            (subset_matrixZeroSet_vanishingIdeal _ ⟨Submonoid.one_mem _, Matrix.det_one⟩)) :
    (∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 →
        g ∈ matrixZeroSet (C := C) (A := C)
          (matrixVanishingIdeal
            {h ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) | h.det = 1}))
      ∨ ∃ B : Matrix (Fin 2) (Fin 2) K,
          B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  set S := tensorDifferentialPoints E hEδ
  set G := galoisMonoid E Z hZE S
  have hGone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G := Submonoid.one_mem _
  have hGmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G :=
    fun _ ha _ hb => Submonoid.mul_mem _ ha hb
  have hH1one : (1 : Matrix (Fin 2) (Fin 2) C) ∈ {h ∈ G | h.det = 1} :=
    ⟨hGone, Matrix.det_one⟩
  have hH1mul : ∀ a ∈ {h ∈ G | h.det = 1},
      ∀ b ∈ {h ∈ G | h.det = 1}, a * b ∈ {h ∈ G | h.det = 1} := by
    intro a ha b hb
    refine ⟨hGmul a ha.1 b hb.1, ?_⟩
    rw [Matrix.det_mul, ha.2, hb.2, one_mul]
  rcases cassidy_monoid_dichotomy hrank hH1mul hH1one (fun h hh => hh.2) hdense G
    hGdetK hGdet0 hGinv with hfull | ⟨n, Lop, i₀, hi₀, hL, hGL⟩
  · exact Or.inl hfull
  · refine Or.inr ?_
    have hderiv : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G → Differential.deriv x = 0 :=
      deriv_eq_zero_of_scalarSpan_of_linear G hGone hGmul hi₀ hL hGL
    refine isomonodromy_of_irreducible_of_differentialSolution E hEδ S
      (fun χ hχ => hχ)
      (fun e he => eq_zero_of_forall_mem_tensorDifferentialPoints_of_jetAdjoin
        E hEδ v hv hadj e he)
      hcompat hconstC hσδ A Y hsys Z hZE hZ hirr (m := 1) (aa := fun _ => 0) ?_
    intro x hx
    rw [differentialJet_succ, differentialJet_zero, hderiv x hx]
    simp

end

end GaloisForLFunctions.HTGeometry
