import GaloisForLFunctions.HTGeometry.SeparableKaehlerBaseChange
import GaloisForLFunctions.HTGeometry.PlueckerFieldOfDefinition

/-!
# The defect kernel is defined over the small field

A family of differentials of a small field, extended to a big algebraic extension, spans the same
relations over the big field as it does over the small one: the base-change map of Kähler
differentials is injective in characteristic zero, and a field extension is flat, so the kernel of
the extended defect map is the extension of the kernel of the small one.

When the extended family is an integral matrix transform of a second family, the two kernels differ
by the transposed matrix, so the kernel of the big defect map is spanned by vectors whose
coordinates lie in the small field.  Every normalized Plücker coordinate of that kernel therefore
lies in the small field: the defect Grassmannian point descends.
-/

open TensorProduct Matrix

namespace GaloisForLFunctions.RHTower

set_option linter.unusedSectionVars false

open GaloisForLFunctions.HTGeometry

noncomputable section

section DefectMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- The defect map of a family of differentials: the linear combination map of the family. -/
def defectMap (ε : Fin n → M) : (Fin n → R) →ₗ[R] M where
  toFun u := ∑ i, u i • ε i
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

theorem defectMap_apply (ε : Fin n → M) (u : Fin n → R) :
    defectMap ε u = ∑ i, u i • ε i := rfl

theorem mem_ker_defectMap_iff (ε : Fin n → M) (u : Fin n → R) :
    u ∈ LinearMap.ker (defectMap ε) ↔ ∑ i, u i • ε i = 0 := Iff.rfl

end DefectMap

section Descent

variable {A F K : Type u} [Field A] [Field F] [Field K]
  [Algebra A F] [Algebra A K] [Algebra F K] [IsScalarTower A F K]
  [CharZero F] [Algebra.IsAlgebraic F K]
variable {n : ℕ}

/-- The extension of a small-field differential to the big field. -/
def extendDifferential (ω : Ω[F⁄A]) : Ω[K⁄A] :=
  KaehlerDifferential.mapBaseChange A F K ((1 : K) ⊗ₜ[F] ω)

/-- The base-changed defect map computes the extended defect combination. -/
theorem mapBaseChange_lTensor_defectMap (ε' : Fin n → Ω[F⁄A]) (u : K ⊗[F] (Fin n → F)) :
    KaehlerDifferential.mapBaseChange A F K
        (AlgebraTensorModule.lTensor K K (defectMap ε') u)
      = ∑ j, (Algebra.TensorProduct.piScalarRight F K K (Fin n) u) j •
          extendDifferential (A := A) (K := K) (ε' j) := by
  classical
  induction u with
  | zero => simp
  | tmul k r =>
    rw [AlgebraTensorModule.lTensor_tmul, defectMap_apply]
    have hleft : KaehlerDifferential.mapBaseChange A F K (k ⊗ₜ[F] ∑ j, r j • ε' j)
        = ∑ j, (algebraMap F K (r j) * k) • extendDifferential (A := A) (K := K) (ε' j) := by
      rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      have hstep : (r j • k) ⊗ₜ[F] ε' j = (algebraMap F K (r j) * k) • ((1 : K) ⊗ₜ[F] ε' j) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.smul_def]
      rw [hstep, map_smul, extendDifferential]
    rw [hleft]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.piScalarRight_tmul_apply, Algebra.smul_def]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, add_smul]

/-- **Kernel descent.**  A big-field relation among extended small-field differentials is a
big-field combination of small-field relations. -/
theorem mem_span_image_ker_of_extended (ε' : Fin n → Ω[F⁄A]) (c : Fin n → K)
    (hc : ∑ j, c j • extendDifferential (A := A) (K := K) (ε' j) = 0) :
    c ∈ Submodule.span K
      ((fun r : Fin n → F => fun j => algebraMap F K (r j)) ''
        {r : Fin n → F | ∑ j, r j • ε' j = 0}) := by
  classical
  set e := Algebra.TensorProduct.piScalarRight F K K (Fin n) with he
  set u : K ⊗[F] (Fin n → F) := e.symm c with hu
  have hue : e u = c := by
    rw [hu]
    exact e.apply_symm_apply c
  have hzero : AlgebraTensorModule.lTensor K K (defectMap ε') u = 0 := by
    refine mapBaseChange_injective_of_separable A F K ?_
    rw [mapBaseChange_lTensor_defectMap, map_zero, hue]
    simpa only [one_smul, smul_eq_mul] using hc
  obtain ⟨w, hw⟩ := exists_of_mem_ker_lTensor (F := F) (K := K) (defectMap ε') hzero
  have hspan : ∀ w : K ⊗[F] (LinearMap.ker (defectMap ε')),
      e (AlgebraTensorModule.lTensor K K (LinearMap.ker (defectMap ε')).subtype w) ∈
        Submodule.span K
          ((fun r : Fin n → F => fun j => algebraMap F K (r j)) ''
            {r : Fin n → F | ∑ j, r j • ε' j = 0}) := by
    intro w
    induction w with
    | zero => simp
    | tmul k z =>
      rw [AlgebraTensorModule.lTensor_tmul]
      simp only [Submodule.subtype_apply]
      have hval : e (k ⊗ₜ[F] (z : Fin n → F)) = k • fun j => algebraMap F K ((z : Fin n → F) j) := by
        funext j
        rw [he, Algebra.TensorProduct.piScalarRight_tmul_apply]
        rw [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
      rw [hval]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(z : Fin n → F), ?_, rfl⟩)
      exact (mem_ker_defectMap_iff ε' _).mp z.2
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  have := hspan w
  rw [hw, hue] at this
  exact this

end Descent

section Transform

variable {A F K : Type u} [Field A] [Field F] [Field K]
  [Algebra A F] [Algebra A K] [Algebra F K] [IsScalarTower A F K]
  [CharZero F] [Algebra.IsAlgebraic F K]
variable {n : ℕ}

/-- The integral matrix acting on big-field coordinate vectors. -/
def intMatrixVec (M : Matrix (Fin n) (Fin n) ℤ) (K : Type*) [Field K] :
    Matrix (Fin n) (Fin n) K :=
  M.map (fun m => (m : K))

/-- **`(5)` transported to kernels.**  If the extended small-field differentials are the integral
transform of the big-field family, then a big-field kernel vector is the transposed transform of a
big-field combination of small-field kernel vectors. -/
theorem mem_span_transform_of_mem_ker (ε : Fin n → Ω[K⁄A]) (ε' : Fin n → Ω[F⁄A])
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hrel : ∀ j, extendDifferential (A := A) (K := K) (ε' j)
      = ∑ i, (intMatrixVec M K) j i • ε i)
    (v : Fin n → K) (hv : ∑ i, v i • ε i = 0)
    (hM : IsUnit (intMatrixVec M K).det) :
    v ∈ Submodule.span K
      ((fun r : Fin n → F => (intMatrixVec M K)ᵀ *ᵥ (fun j => algebraMap F K (r j))) ''
        {r : Fin n → F | ∑ j, r j • ε' j = 0}) := by
  classical
  set N : Matrix (Fin n) (Fin n) K := intMatrixVec M K with hN
  set c : Fin n → K := (Nᵀ)⁻¹ *ᵥ v with hc
  have hNT : IsUnit (Nᵀ).det := by
    rwa [Matrix.det_transpose]
  have hNc : Nᵀ *ᵥ c = v := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hNT, Matrix.one_mulVec]
  have hkey : ∑ j, c j • extendDifferential (A := A) (K := K) (ε' j) = 0 := by
    have hexpand : ∑ j, c j • extendDifferential (A := A) (K := K) (ε' j)
        = ∑ i, (Nᵀ *ᵥ c) i • ε i := by
      calc ∑ j, c j • extendDifferential (A := A) (K := K) (ε' j)
          = ∑ j, c j • ∑ i, N j i • ε i := by
            exact Finset.sum_congr rfl fun j _ => by rw [hrel j]
        _ = ∑ j, ∑ i, (c j * N j i) • ε i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        _ = ∑ i, ∑ j, (c j * N j i) • ε i := Finset.sum_comm
        _ = ∑ i, (Nᵀ *ᵥ c) i • ε i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_smul]
            congr 1
            rw [Matrix.mulVec, dotProduct]
            exact Finset.sum_congr rfl fun j _ => by rw [Matrix.transpose_apply, mul_comm]
    rw [hexpand, hNc, hv]
  have hcspan := mem_span_image_ker_of_extended (A := A) (K := K) ε' c hkey
  have himg := Submodule.apply_mem_span_image_of_mem_span
    (f := (Matrix.mulVecLin (Nᵀ) : (Fin n → K) →ₗ[K] (Fin n → K))) hcspan
  rw [show Matrix.mulVecLin (Nᵀ) c = v from hNc] at himg
  refine Submodule.span_mono ?_ himg
  rintro y ⟨z, ⟨r, hr, rfl⟩, rfl⟩
  exact ⟨r, hr, rfl⟩

/-- **Theorem 2, the Plücker step.**  A spanning matrix of the defect kernel whose rows are
transposed integral transforms of small-field vectors has all its normalized Plücker ratios in the
small field. -/
theorem pluecker_ratio_transform_mem_range {k : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (B' : Matrix (Fin k) (Fin n) F) (B : Matrix (Fin k) (Fin n) K)
    (hB : B = (B'.map (algebraMap F K)) * (intMatrixVec M K)ᵀ)
    (I J : Fin k → Fin n) (hI : pluecker B I ≠ 0) :
    pluecker B J / pluecker B I ∈ Set.range (algebraMap F K : F →+* K) := by
  refine pluecker_ratio_mem_range (algebraMap F K : F →+* K) (B := B) ?_ I J hI
  intro i j
  refine ⟨∑ l, B' i l * ((M l j : ℤ) : F), ?_⟩
  rw [hB, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, Matrix.map_apply, Matrix.transpose_apply, intMatrixVec, Matrix.map_apply,
    map_intCast]

end Transform

end

end GaloisForLFunctions.RHTower
