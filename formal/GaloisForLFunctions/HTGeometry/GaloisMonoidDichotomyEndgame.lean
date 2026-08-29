import GaloisForLFunctions.HTGeometry.DifferentialGaloisSeparation
import GaloisForLFunctions.HTGeometry.CassidyMonoidDichotomy

/-!
# The endgame dichotomy for the difference Galois monoid

Cassidy's dichotomy for a matrix monoid, applied to the Galois monoid of a second-order difference
equation and fed into the isomonodromy endgame, gives a clean alternative:

> either the whole of `SL₂` lies in the Kolchin closure of the Galois monoid,
> or the equation carries a connection over the base.

The first branch is the improper case — the group is everything, so no solution is differentially
algebraic; the second is the isomonodromy conclusion the card contradicts.  Everything between the
two is now a theorem: tracelessness, bracket closure, the improper branch, and the passage from a
linear jet relation on the group entries to the differential constraint on the scalar stabiliser.

* `isomonodromy_or_sl2_galoisMonoid`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- **The endgame dichotomy.**  Either the Kolchin closure of the Galois monoid contains all of
`SL₂`, or the difference equation carries a connection over the base. -/
theorem isomonodromy_or_sl2_galoisMonoid
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (hrank : NoUniversalJetRelation C)
    (E : Subalgebra C (R ⊗[K] R)) (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
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
    (hHdet : ∀ h ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ), h.det = 1)
    (hdense : ∀ W : Matrix (Fin 2) (Fin 2) C, W.trace = 0 →
      W ∈ Submodule.span C
        ((matrixTangentM (matrixVanishingIdeal
            (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)))
          (subset_matrixZeroSet_vanishingIdeal _
            (Submonoid.one_mem _)) : Submodule _ _) : Set _))
    (hGdetK : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ),
      g.det ∈ differentialConstants C)
    (hGdet0 : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ), g.det ≠ 0)
    (hGinv : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ),
      ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
        ∀ W ∈ matrixTangentM (matrixVanishingIdeal
            (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)))
          (subset_matrixZeroSet_vanishingIdeal _ (Submonoid.one_mem _)),
          g * W * g' ∈ matrixTangentM (matrixVanishingIdeal
            (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)))
            (subset_matrixZeroSet_vanishingIdeal _ (Submonoid.one_mem _))) :
    (∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 →
        g ∈ matrixZeroSet (C := C) (A := C)
          (matrixVanishingIdeal (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ))))
      ∨ ∃ B : Matrix (Fin 2) (Fin 2) K,
          B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  set G := galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) with hG
  have hGone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G := Submonoid.one_mem _
  have hGmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G := fun _ ha _ hb => Submonoid.mul_mem _ ha hb
  rcases cassidy_monoid_dichotomy hrank hGmul hGone hHdet hdense G hGdetK hGdet0
    hGinv with hfull | ⟨n, Lop, i₀, hi₀, hL, hGL⟩
  · exact Or.inl hfull
  · refine Or.inr ?_
    have hderiv : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G → Differential.deriv x = 0 :=
      deriv_eq_zero_of_scalarSpan_of_linear G hGone hGmul hi₀ hL hGL
    refine isomonodromy_of_no_riccati_of_differentiallyClosed E hEδ b hgen hindep hcompat
      hconstC hσδ hsimple hric A Y hsys hY1 hYrec Z hZE hZ (m := 1) (aa := fun _ => 0) ?_
    intro x hx
    rw [differentialJet_succ, differentialJet_zero, hderiv x hx]
    simp


/-! ### The determinant-one part -/

omit [Differential C] in
/-- The determinant-one part of a matrix monoid is a monoid. -/
theorem mul_mem_detOne {G : Set (Matrix (Fin 2) (Fin 2) C)}
    (hGmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G)
    {a b : Matrix (Fin 2) (Fin 2) C} (ha : a ∈ {h ∈ G | h.det = 1})
    (hb : b ∈ {h ∈ G | h.det = 1}) : a * b ∈ {h ∈ G | h.det = 1} := by
  refine ⟨hGmul a ha.1 b hb.1, ?_⟩
  rw [Matrix.det_mul, ha.2, hb.2, one_mul]

/-- **The endgame dichotomy, run on the determinant-one part of the Galois monoid.**  The
comparison matrix of a system whose companion determinant is a root of unity has determinant a root
of unity too, so the Galois monoid need not lie in `SL₂`; its determinant-one part does, and the
group step is unaffected because Cassidy's classification takes the Lie algebra and the group as
independent inputs. -/
theorem isomonodromy_or_sl2_galoisMonoid_detOne
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (hrank : NoUniversalJetRelation C)
    (E : Subalgebra C (R ⊗[K] R)) (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
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
  set G := galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ) with hG
  have hGone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G := Submonoid.one_mem _
  have hGmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G := fun _ ha _ hb => Submonoid.mul_mem _ ha hb
  have hH1one : (1 : Matrix (Fin 2) (Fin 2) C) ∈ {h ∈ G | h.det = 1} :=
    ⟨hGone, Matrix.det_one⟩
  rcases cassidy_monoid_dichotomy hrank (fun a ha bb hbb => mul_mem_detOne hGmul ha hbb)
    hH1one (fun h hh => hh.2) hdense G hGdetK hGdet0 hGinv with
    hfull | ⟨n, Lop, i₀, hi₀, hL, hGL⟩
  · exact Or.inl hfull
  · refine Or.inr ?_
    have hderiv : ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G → Differential.deriv x = 0 :=
      deriv_eq_zero_of_scalarSpan_of_linear G hGone hGmul hi₀ hL hGL
    refine isomonodromy_of_no_riccati_of_differentiallyClosed E hEδ b hgen hindep hcompat
      hconstC hσδ hsimple hric A Y hsys hY1 hYrec Z hZE hZ (m := 1) (aa := fun _ => 0) ?_
    intro x hx
    rw [differentialJet_succ, differentialJet_zero, hderiv x hx]
    simp

end

end GaloisForLFunctions.HTGeometry
