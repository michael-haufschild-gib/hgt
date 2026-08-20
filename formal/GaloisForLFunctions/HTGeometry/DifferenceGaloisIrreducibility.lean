import GaloisForLFunctions.HTGeometry.DifferenceIrreducibilityCriterion
import GaloisForLFunctions.HTGeometry.DifferenceTensorTorsor

/-!
# The Galois action of a second-order difference equation leaves no line stable

A point of the Galois group specialises the torsor, and the specialisation carries the fundamental
matrix to itself multiplied by the Galois matrix read off at that point.  So a coordinate vector
scaled by every Galois matrix produces a solution scaled by every specialisation, and such a
solution is hyperexponential over the base — its ratio solves the Riccati equation.

An equation whose Riccati equation has no base solution therefore has no stable coordinate line:
the Galois action is irreducible.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {K R C : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [IsAlgClosed C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

omit [Nontrivial R] [IsAlgClosed C] in
/-- The value of a specialisation on a constant of the torsor. -/
theorem torsorSpecialization_coe (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) (e : E) :
    torsorSpecialization E b hgen hindep χ (e : R ⊗[K] R) = algebraMap C R (χ e) := by
  have hval := torsorSpecialization_apply E b hgen hindep χ 1 e
  have hone : tensorDecompositionEquiv E b hgen hindep ((1 : R) ⊗ₜ[C] e) = (e : R ⊗[K] R) := by
    show tensorDecompositionHom (R := R) E ((1 : R) ⊗ₜ[C] e) = _
    rw [tensorDecompositionHom_tmul]
    rw [map_one, one_mul]
  rw [hone, one_mul] at hval
  exact hval

/-- The Galois matrix read off at a point of the group. -/
def galoisMatrixAt (E : Subalgebra C (R ⊗[K] R)) (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R))
    (hZE : ∀ i j, Z i j ∈ E) (χ : E →ₐ[C] C) : Matrix (Fin 2) (Fin 2) C :=
  Matrix.of fun i j => χ ⟨Z i j, hZE i j⟩

/-- The Galois automorphism attached to a point of the group. -/
def galoisAutAt (E : Subalgebra C (R ⊗[K] R)) {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) : R →ₐ[C] R :=
  ((torsorSpecialization E b hgen hindep χ).restrictScalars C).comp (rightEmbedding K C)

omit [Nontrivial R] [IsAlgClosed C] in
theorem galoisAutAt_apply (E : Subalgebra C (R ⊗[K] R)) {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) (r : R) :
    galoisAutAt E b hgen hindep χ r
      = torsorSpecialization E b hgen hindep χ ((1 : R) ⊗ₜ[K] r) := rfl

omit [Nontrivial R] [IsAlgClosed C] in
/-- **The Galois automorphism moves the fundamental matrix by the Galois matrix.** -/
theorem galoisAutAt_fundamental (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (χ : E →ₐ[C] C) {n : ℕ} (Y : Matrix (Fin n) (Fin n) R)
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) (i j : Fin n) :
    galoisAutAt E b hgen hindep χ (Y i j)
      = ∑ l, Y i l * algebraMap C R (χ ⟨Z l j, hZE l j⟩) := by
  have hentry := congrFun (congrFun hZ i) j
  simp only [Matrix.mul_apply, leftFundamental, rightFundamental, Matrix.map_apply] at hentry
  have happ := congrArg (torsorSpecialization E b hgen hindep χ) hentry
  rw [map_sum] at happ
  rw [galoisAutAt_apply]
  rw [← happ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  congr 1
  · exact (torsorSpecialization E b hgen hindep χ).commutes (Y i l)
  · exact torsorSpecialization_coe E b hgen hindep χ ⟨Z l j, hZE l j⟩

omit [IsAlgClosed C] in
/-- **No Galois-stable line.**  If the recurrence has no Riccati solution over the base, no nonzero
coordinate vector is scaled by every Galois matrix. -/
theorem not_semiInvariant_coordinate_of_no_riccati
    (E : Subalgebra C (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι C E)
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (hconst : ∀ c : C, σR (algebraMap C R c) = algebraMap C R c)
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (Y : Matrix (Fin 2) (Fin 2) R) (hYdet : IsUnit Y.det)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (c : Fin 2 → C) (hc : c ≠ 0) :
    ¬ ∀ χ ∈ S, ∃ lam : C, (galoisMatrixAt E Z hZE χ).mulVec c = lam • c := by
  classical
  intro hstable
  set y : R := ∑ j, Y 0 j * algebraMap C R (c j) with hy
  have hrow : ∀ i : Fin 2, ∑ j, Y i j * algebraMap C R (c j) = Y.mulVec (fun j => algebraMap C R (c j)) i := by
    intro i
    simp [Matrix.mulVec, dotProduct]
  have hv1 : ∑ j, Y 1 j * algebraMap C R (c j) = σR y := by
    rw [hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hY1 j, hconst]
  have hyne : y ≠ 0 := by
    intro h0
    have h1 : σR y = 0 := by rw [h0, map_zero]
    have hzero : Y.mulVec (fun j => algebraMap C R (c j)) = 0 := by
      funext i
      have hall : ∀ i : Fin 2, Y.mulVec (fun j => algebraMap C R (c j)) i = 0 := by
        rw [Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · rw [← hrow 0, ← hy, h0]
        · rw [← hrow 1, hv1, h1]
      exact hall i
    have hc0 : (fun j => algebraMap C R (c j)) = (0 : Fin 2 → R) := by
      have hmul := congrArg (fun v : Fin 2 → R => (Y⁻¹ : Matrix (Fin 2) (Fin 2) R).mulVec v) hzero
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Y hYdet, Matrix.one_mulVec,
        Matrix.mulVec_zero] at hmul
      exact hmul
    apply hc
    funext j
    have := congrFun hc0 j
    simpa using (algebraMap C R).injective (by simpa using this)
  have hrec : σR (σR y) = algebraMap K R a₁ * σR y + algebraMap K R a₀ * y := by
    rw [← hv1, map_sum]
    have hterm : ∀ j : Fin 2, σR (Y 1 j * algebraMap C R (c j))
        = (algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j) * algebraMap C R (c j) := by
      intro j
      rw [map_mul, hconst, hYrec j]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [hy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine not_forall_specialization_semiInvariant_of_no_riccati_subset E b hgen hindep S hsep
    hcompat hsimple hric hyne hrec ?_
  intro χ hχ
  obtain ⟨lam, hlam⟩ := hstable χ hχ
  have hgal : ∀ i : Fin 2, galoisAutAt E b hgen hindep χ (∑ j, Y i j * algebraMap C R (c j))
      = algebraMap C R lam * (∑ j, Y i j * algebraMap C R (c j)) := by
    intro i
    rw [map_sum]
    have hstep : ∀ j : Fin 2,
        galoisAutAt E b hgen hindep χ (Y i j * algebraMap C R (c j))
          = ∑ l, Y i l * algebraMap C R (χ ⟨Z l j, hZE l j⟩ * c j) := by
      intro j
      rw [map_mul, galoisAutAt_fundamental E b hgen hindep χ Y Z hZE hZ,
        AlgHom.commutes, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hml : ∑ j, Y i l * algebraMap C R (χ ⟨Z l j, hZE l j⟩ * c j)
        = Y i l * algebraMap C R ((galoisMatrixAt E Z hZE χ).mulVec c l) := by
      rw [← Finset.mul_sum, ← map_sum]
      congr 2
    rw [hml]
    have hlamc : (galoisMatrixAt E Z hZE χ).mulVec c l = lam * c l := by
      have hcomp := congrFun hlam l
      simpa using hcomp
    rw [hlamc, map_mul]
    ring
  have h0 := hgal 0
  have h1 := hgal 1
  rw [← hy] at h0
  rw [hv1] at h1
  show y * galoisAutAt E b hgen hindep χ (σR y) = σR y * galoisAutAt E b hgen hindep χ y
  rw [h0, h1]
  ring

end

end GaloisForLFunctions.HTGeometry
