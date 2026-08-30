import GaloisForLFunctions.HTGeometry.GenericCurvatureInvariantField
import GaloisForLFunctions.HTGeometry.JetFieldConstantKernel

/-!
# The Galois group of the generic torsor is the constant gauge group

A differential automorphism of the free differential rational field that fixes the curvature field
pointwise moves the generic matrix by `Y ↦ Z·Y` with `Z` a matrix of *constants*: the matrix
`Z = φ(Y)·Y⁻¹` has vanishing componentwise derivative, and the corpus's
`JetFieldConstantKernel` puts its entries in the base field.  Since `Y^{(m)} = Y·B_m` and the slice
coordinates lie in the curvature field, `φ` is then determined on every jet, hence on the whole
field; it is the constant left translation `σ_Z`.

Together with `GenericCurvatureInvariantField.leftTranslationInvariants_eq_curvatureField` this is
the differential Galois correspondence for the generic torsor: the automorphism group over the
curvature field is exactly `GL_N` of the constants, and its fixed field is exactly the curvature
field.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

omit [CharZero K] in
/-- The generic matrix recovers every jet from the slice coordinates. -/
theorem genericJetMatrix_mul_slice (m : ℕ) :
    genericJetMatrix K N * genericSliceMatrix K N m = genericJetPower K N m := by
  rw [genericSliceMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ isUnit_det_genericJetMatrix, Matrix.one_mul]

/-- **Every differential automorphism over the curvature field is a constant gauge.** -/
theorem exists_constant_of_differentialAut_fixing_curvature
    (φ : JetField K (Fin N × Fin N) ≃+* JetField K (Fin N × Fin N))
    (hφderiv : ∀ x, φ (x′) = (φ x)′)
    (hφfix : ∀ u ∈ differentialAdjoin K (systemEntries K N), φ u = u) :
    ∃ Z : Matrix (Fin N) (Fin N) K,
      (genericJetMatrix K N).map (φ : JetField K (Fin N × Fin N) →+* JetField K (Fin N × Fin N))
        = (Z.map (algebraMap K (JetField K (Fin N × Fin N)))) * genericJetMatrix K N := by
  classical
  set E := JetField K (Fin N × Fin N)
  set Y := genericJetMatrix K N with hY
  set A := genericSystemMatrix K N with hA
  set φr : E →+* E := (φ : E →+* E) with hφr
  have hAfix : A.map φr = A := by
    apply Matrix.ext
    intro i j
    exact hφfix _ (genericSystemMatrix_mem_curvatureField i j)
  have hsys : matDeriv Y = Y * A := matDeriv_genericJetMatrix
  have hmapderiv : matDeriv (Y.map φr) = (matDeriv Y).map φr :=
    (matDeriv_map Y φr (fun x => (hφderiv x))).symm ▸ rfl
  have hYmap : matDeriv (Y.map φr) = (Y.map φr) * A := by
    rw [hmapderiv, hsys]
    have := map_mul (φr.mapMatrix) Y A
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
    rw [this, hAfix]
  set Z : Matrix (Fin N) (Fin N) E := (Y.map φr) * Y⁻¹ with hZ
  have hZconst : matDeriv Z = 0 := by
    rw [hZ, matDeriv_mul, hYmap, matDeriv_inv Y isUnit_det_genericJetMatrix, hsys]
    rw [Matrix.mul_neg]
    have hcancel : Y.map φr * (Y⁻¹ * (Y * A) * Y⁻¹) = Y.map φr * A * Y⁻¹ := by
      simp only [Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ isUnit_det_genericJetMatrix,
        Matrix.one_mul]
    rw [hcancel]
    abel
  have hZmem : ∀ i j, ∃ c : K, Z i j = algebraMap K E c := by
    intro i j
    have hd : (Z i j)′ = 0 := congrFun (congrFun hZconst i) j
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp (jetField_mem_range_algebraMap_of_deriv_eq_zero hd)
    exact ⟨c, hc.symm⟩
  choose c hc using hZmem
  refine ⟨Matrix.of fun i j => c i j, ?_⟩
  have hZeq : (Matrix.of fun i j => c i j).map (algebraMap K E) = Z := by
    apply Matrix.ext
    intro i j
    rw [Matrix.map_apply]
    simp only [Matrix.of_apply]
    exact (hc i j).symm
  rw [hZeq, hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ isUnit_det_genericJetMatrix,
    Matrix.mul_one]

/-- **The Galois group of the generic torsor is exactly the constant gauge group.** -/
theorem exists_leftTranslation_of_differentialAut_fixing_curvature
    (φ : JetField K (Fin N × Fin N) ≃+* JetField K (Fin N × Fin N))
    (hφderiv : ∀ x, φ (x′) = (φ x)′)
    (hφfix : ∀ u ∈ differentialAdjoin K (systemEntries K N), φ u = u) :
    ∃ (Z W : Matrix (Fin N) (Fin N) K) (hZW : Z * W = 1) (hWZ : W * Z = 1),
      ∀ u, φ u = leftTranslationFieldEquiv Z W hZW hWZ u := by
  classical
  set E := JetField K (Fin N × Fin N)
  set φr : E →+* E := (φ : E →+* E) with hφr
  obtain ⟨Z, hZ⟩ := exists_constant_of_differentialAut_fixing_curvature φ hφderiv hφfix
  have hZdet : Z.det ≠ 0 := by
    intro hd
    have hmapdet : (Z.map (algebraMap K E)).det = algebraMap K E Z.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hYdet := congrArg Matrix.det hZ
    rw [Matrix.det_mul, hmapdet, hd, map_zero, zero_mul] at hYdet
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hYdet
    have hzero : ((φ : E →+* E)) ((genericJetMatrix K N).det) = ((φ : E →+* E)) 0 := by
      rw [hYdet, map_zero]
    exact det_genericJetMatrix_ne_zero (φ.injective hzero)
  have hunit : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZdet
  have hZW : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hunit
  have hWZ : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hunit
  refine ⟨Z, Z⁻¹, hZW, hWZ, ?_⟩
  set σ : E ≃+* E := leftTranslationFieldEquiv Z Z⁻¹ hZW hWZ with hσ
  have hslicefix : ∀ m : ℕ, (genericSliceMatrix K N m).map φr = genericSliceMatrix K N m := by
    intro m
    apply Matrix.ext
    intro i j
    exact hφfix _ (genericSliceMatrix_mem_curvatureField m i j)
  have hjet : ∀ (m : ℕ) (i j : Fin N),
      φ (JetField.jet ((i, j), m)) = σ (JetField.jet ((i, j), m)) := by
    intro m i j
    have hleft : φ (JetField.jet ((i, j), m))
        = ((Z.map (algebraMap K E)) * genericJetPower K N m) i j := by
      rw [← genericJetPower_apply]
      have hmul := map_mul (φr.mapMatrix) (genericJetMatrix K N) (genericSliceMatrix K N m)
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        genericJetMatrix_mul_slice, hZ, hslicefix m, Matrix.mul_assoc,
        genericJetMatrix_mul_slice] at hmul
      exact congrFun (congrFun hmul i) j
    have hright : σ (JetField.jet ((i, j), m))
        = ((Z.map (algebraMap K E)) * genericJetPower K N m) i j := by
      rw [hσ, leftTranslationFieldEquiv_jet, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply, genericJetPower_apply]
    rw [hleft, hright]
  have hpoly : ∀ p : JetPoly K (Fin N × Fin N),
      φ (algebraMap (JetPoly K (Fin N × Fin N)) E p)
        = σ (algebraMap (JetPoly K (Fin N × Fin N)) E p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hb : algebraMap (JetPoly K (Fin N × Fin N)) E (MvPolynomial.C a)
            = algebraMap K E a := by
          rw [IsScalarTower.algebraMap_apply K (JetPoly K (Fin N × Fin N)) E,
            MvPolynomial.algebraMap_eq]
        rw [hb, hσ, leftTranslationFieldEquiv_algebraMap_base]
        exact hφfix _ (IntermediateField.algebraMap_mem _ a)
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p q hp =>
        obtain ⟨⟨a, b⟩, r⟩ := q
        rw [map_mul, map_mul, map_mul, hp]
        congr 1
        exact hjet r a b
  intro u
  obtain ⟨p, q, hqmem, hu⟩ := IsFractionRing.div_surjective (JetPoly K (Fin N × Fin N)) u
  rw [← hu, map_div₀, map_div₀, hpoly p, hpoly q]

end

end GaloisForLFunctions.HTGeometry
