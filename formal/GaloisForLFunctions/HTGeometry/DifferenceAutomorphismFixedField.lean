import GaloisForLFunctions.HTGeometry.GaloisDifferentialPointGroup
import GaloisForLFunctions.HTGeometry.DifferenceGaloisEndgame
import GaloisForLFunctions.HTGeometry.SigmaConstantsReduced

/-!
# Fixed-field descent for an ordinary difference Picard--Vessiot torsor

Rational points of the comparison algebra give difference endomorphisms.  Sigma-simplicity makes
them injective, Picard--Vessiot generation makes them surjective, and point separation then turns
invariance under the full difference automorphism group into membership in the base field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u

variable {K R C : Type u} [Field K] [CharZero K] [CommRing R] [Nontrivial R]
  [Algebra K R] [Field C] [IsAlgClosed C]
  [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- Bundle a bijective algebra endomorphism commuting with the difference operator. -/
def differenceAutOfBijectiveAlgHom (σR : R ≃+* R) (f : R →ₐ[K] R)
    (hf : Function.Bijective f) (hcomm : ∀ x : R, f (σR x) = σR (f x)) :
    differenceAut (K := K) σR :=
  ⟨AlgEquiv.ofBijective f hf, fun x => by
    rw [AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply]
    exact hcomm x⟩

omit [CharZero K] [Nontrivial R] in
@[simp]
theorem differenceAutOfBijectiveAlgHom_apply (σR : R ≃+* R) (f : R →ₐ[K] R)
    (hf : Function.Bijective f) (hcomm : ∀ x : R, f (σR x) = σR (f x)) (x : R) :
    (differenceAutOfBijectiveAlgHom σR f hf hcomm).1 x = f x :=
  AlgEquiv.ofBijective_apply f hf x

/-- A family of torsor points realized by genuine difference automorphisms. -/
structure DifferencePointRealization
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (σR : R ≃+* R) where
  aut : (E →ₐ[C] C) → differenceAut (K := K) σR
  aut_apply : ∀ (χ : E →ₐ[C] C) (x : R),
    (aut χ).1 x = galoisAutAt E b hgen hindep χ x

/-- Point realization and sigma-simplicity give fixed-field descent without exposing the
endomorphism construction to the Galois-correspondence proof. -/
theorem differenceAut_fixedField_of_realization
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (σR : R ≃+* R) (hsimple : IsSigmaSimple σR)
    (A : DifferencePointRealization E b hgen hindep σR)
    {x : R} (hx : ∀ g : differenceAut (K := K) σR, g.1 x = x) :
    ∃ k : K, x = algebraMap K R k := by
  have hsep : ∀ e : E, (∀ χ ∈ (Set.univ : Set (E →ₐ[C] C)), χ e = 0) → e = 0 := by
    intro e he
    exact eq_zero_of_forall_algHom_eq_zero_tensorSquare hsimple E
      (fun χ => he χ (Set.mem_univ χ))
  apply exists_eq_algebraMap_of_forall_galoisAutAt E b hgen hindep Set.univ hsep
  intro χ _
  exact (A.aut_apply χ x).symm.trans (hx (A.aut χ))

/-- Finite Picard--Vessiot generation realizes every torsor point as a difference automorphism. -/
def pvDifferencePointRealization
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} (σR : R ≃+* R)
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hGdet : ∀ χ : E →ₐ[C] C, IsUnit (galoisMatrixAt E Z hZE χ).det)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤) :
    DifferencePointRealization E b hgen hindep σR := by
  let hfinj := fun χ : E →ₐ[C] C =>
    galoisAutAtK_injective (K := K) (R := R) (C := C)
      E b hgen hindep hcompat hconstC hEσ hsimple χ
  let hfsurj := fun χ : E →ₐ[C] C =>
      galoisAutAtK_surjective_of_pvGeneration (K := K) (R := R) (C := C)
        E b hgen hindep χ Y Z hZE hZ
        (hGdet χ) u hu htop
  let hσ := fun χ : E →ₐ[C] C =>
    galoisAutAtK_sigma (K := K) (R := R) (C := C)
      E b hgen hindep hcompat hconstC hEσ χ
  exact
    { aut := fun χ => differenceAutOfBijectiveAlgHom σR
        (galoisAutAtK (K := K) (R := R) (C := C) E b hgen hindep χ)
        ⟨hfinj χ, hfsurj χ⟩ (hσ χ)
      aut_apply := fun χ x =>
        (differenceAutOfBijectiveAlgHom_apply σR
          (galoisAutAtK (K := K) (R := R) (C := C) E b hgen hindep χ)
          ⟨hfinj χ, hfsurj χ⟩ (hσ χ) x).trans
        (galoisAutAtK_apply (K := K) (R := R) (C := C) E b hgen hindep χ x) }

/-- Fixed-field descent when specialized comparison matrices are known to be invertible. -/
theorem differenceAut_fixedField_of_det
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (hGdet : ∀ χ : E →ₐ[C] C, IsUnit (galoisMatrixAt E Z hZE χ).det)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : ∀ g : differenceAut (K := K) σR, g.1 x = x) :
    ∃ k : K, x = algebraMap K R k :=
  differenceAut_fixedField_of_realization E b hgen hindep σR hsimple
    (pvDifferencePointRealization E b hgen hindep σR hcompat hconstC hEσ hsimple
      Y Z hZE hZ hGdet u hu htop) hx

omit [CharZero K] [Nontrivial R] [IsAlgClosed C] in
/-- An inverse determinant in the comparison algebra makes every specialized comparison matrix
invertible. -/
theorem galoisMatrixAt_det_isUnit
    (E : Subalgebra C (R ⊗[K] R))
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (w : R ⊗[K] R) (hwE : w ∈ E) (hw : Z.det * w = 1)
    (χ : E →ₐ[C] C) : IsUnit (galoisMatrixAt E Z hZE χ).det := by
  let ZE : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ⟨Z i j, hZE i j⟩
  have hZE_map : E.val.mapMatrix ZE = Z := by
    ext i j
    rfl
  have hdetE : (ZE.det : R ⊗[K] R) = Z.det := by
    have hmap := RingHom.map_det E.val.toRingHom ZE
    calc
      E.val.toRingHom ZE.det = (E.val.mapMatrix ZE).det := hmap
      _ = Z.det := congrArg Matrix.det hZE_map
  have hw_sub : ZE.det * (⟨w, hwE⟩ : E) = 1 := by
    apply Subtype.ext
    change (ZE.det : R ⊗[K] R) * w = 1
    rw [hdetE]
    exact hw
  have hGmap : χ.toRingHom.mapMatrix ZE = galoisMatrixAt E Z hZE χ := by
    ext i j
    rfl
  have hdetG : (galoisMatrixAt E Z hZE χ).det = χ ZE.det := by
    have hmap := RingHom.map_det χ.toRingHom ZE
    calc
      (galoisMatrixAt E Z hZE χ).det = (χ.toRingHom.mapMatrix ZE).det :=
        congrArg Matrix.det hGmap.symm
      _ = χ ZE.det := hmap.symm
  refine ⟨⟨(galoisMatrixAt E Z hZE χ).det, χ ⟨w, hwE⟩, ?_, ?_⟩, rfl⟩
  · rw [hdetG, ← map_mul, hw_sub, map_one]
  · rw [mul_comm, hdetG, ← map_mul, hw_sub, map_one]

/-- Fixed-field descent with specialized invertibility derived from the inverse determinant in the
comparison algebra. -/
theorem exists_eq_algebraMap_of_forall_differenceAut
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (w : R ⊗[K] R) (hwE : w ∈ E) (hw : Z.det * w = 1)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : ∀ g : differenceAut (K := K) σR, g.1 x = x) :
    ∃ k : K, x = algebraMap K R k :=
  differenceAut_fixedField_of_det E b hgen hindep
    hcompat hconstC hEσ hsimple Y Z hZE hZ
    (fun χ => galoisMatrixAt_det_isUnit E Z hZE w hwE hw χ) u hu htop hx

end

end GaloisForLFunctions.HTGeometry
