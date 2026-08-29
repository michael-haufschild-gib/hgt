import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]
  {n : ℕ}

/-- The tensor difference automorphism commutes with every tensor jet. -/
theorem differenceTensorEquiv_tensorJet
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (k : ℕ) (x : R ⊗[K] R) :
    differenceTensorEquiv σK σR hcompat (tensorJet (K := K) k x) =
      tensorJet (K := K) k (differenceTensorEquiv σK σR hcompat x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tensorJet_succ, tensorJet_succ,
        tensorSquareDerivation_commutes σK σR hcompat hσδ, ih]

omit [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R] in
/-- The tensor difference automorphism fixes the scalar constants. -/
theorem differenceTensorEquiv_algebraMap_fixed
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (c : C) :
    differenceTensorEquiv σK σR hcompat (algebraMap C (R ⊗[K] R) c) =
      algebraMap C (R ⊗[K] R) c := by
  rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
  change differenceTensorEquiv σK σR hcompat
      (algebraMap C R c ⊗ₜ[K] (1 : R)) = algebraMap C R c ⊗ₜ[K] (1 : R)
  rw [differenceTensorEquiv_tmul, hconstC, map_one]

/-- If a comparison matrix is fixed, every jet of every entry is fixed. -/
theorem comparisonJet_fixed
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZσ : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j)
    (k : ℕ) (i j : Fin n) :
    differenceTensorEquiv σK σR hcompat (tensorJet (K := K) k (Z i j)) =
      tensorJet (K := K) k (Z i j) := by
  rw [differenceTensorEquiv_tensorJet hcompat hσδ, hZσ]

omit [Differential K] [Differential R] [DifferentialAlgebra K R] in
/-- The chosen inverse determinant is fixed whenever the comparison matrix is fixed. -/
theorem comparisonInverseDet_fixed
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZσ : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j)
    (w : R ⊗[K] R) (hw : Z.det * w = 1) :
    differenceTensorEquiv σK σR hcompat w = w := by
  let τ := differenceTensorEquiv σK σR hcompat
  have hZmap : Z.map τ = Z := by
    ext i j
    exact hZσ i j
  have hdetσ : τ Z.det = Z.det := by
    calc
      τ Z.det = (Z.map τ).det := RingHom.map_det τ.toRingHom Z
      _ = Z.det := by rw [hZmap]
  have hright : Z.det * τ w = 1 := by
    calc
      Z.det * τ w = τ Z.det * τ w := by rw [hdetσ]
      _ = τ (Z.det * w) := by rw [map_mul]
      _ = 1 := by rw [hw, map_one]
  calc
    τ w = (Z.det * w) * τ w := by rw [hw, one_mul]
    _ = w * (Z.det * τ w) := by ring
    _ = w := by rw [hright, mul_one]

omit [Differential C] [DifferentialAlgebra C R] in
/-- The comparison-jet algebra lies in the fixed ring of the tensor difference automorphism. -/
theorem comparisonJetAlgebra_fixed
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZσ : ∀ i j, differenceTensorEquiv σK σR hcompat (Z i j) = Z i j)
    (w : R ⊗[K] R) (hw : Z.det * w = 1)
    {e : R ⊗[K] R} (he : e ∈ comparisonJetAlgebra (C := C) Z w) :
    differenceTensorEquiv σK σR hcompat e = e := by
  let τ := differenceTensorEquiv σK σR hcompat
  induction he using Algebra.adjoin_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · obtain ⟨k, p, rfl⟩ := Set.mem_iUnion.mp hy
        exact comparisonJet_fixed hcompat hσδ Z hZσ k p.1 p.2
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact comparisonInverseDet_fixed hcompat Z hZσ w hw
  | algebraMap c => exact differenceTensorEquiv_algebraMap_fixed hcompat hconstC c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

end

end GaloisForLFunctions.HTGeometry
