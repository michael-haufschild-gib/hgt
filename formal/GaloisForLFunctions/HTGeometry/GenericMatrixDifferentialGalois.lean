import GaloisForLFunctions.HTGeometry.FreeDifferentialJetField
import GaloisForLFunctions.HTGeometry.DifferentialLinearChangeAutomorphism
import GaloisForLFunctions.HTGeometry.DifferentialMatrixGauge

/-!
# The generic matrix as a differential Galois torsor

The free differential rational field `E = C⟨x_{ij}⟩` on `N²` coordinates carries the generic matrix
`Y`, whose determinant is nonzero.  Its own system matrix `A = Y⁻¹ δY` makes `Y` a fundamental
matrix, and the slice coordinates `B_k = Y⁻¹ Y^{(k)}` obey the recursion `B_{k+1} = δB_k + A B_k`,
so every jet of `Y` is a differential polynomial in `A` after left division by `Y`.

Every constant invertible matrix `Z` acts on `E` by the jetwise substitution
`x_{ij}^{(m)} ↦ (Z Y^{(m)})_{ij}`.  That substitution is a differential automorphism of `E`, it
multiplies the generic matrix on the left, and it therefore fixes the system matrix `A` — the whole
general linear group acts on the generic torsor over its own invariant base.  Since the corpus
already proves that `E` has no constants beyond `C`
(`JetFieldConstantKernel.jetFieldContainConstants`), this is a Picard--Vessiot situation with no
δ-simplicity or no-new-constants input required.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {C : Type*} [Field C] {N : ℕ}


/-! ### Matrix calculus supplements -/

theorem matDeriv_one {R : Type*} [CommRing R] [Differential R] {n : Type*} [DecidableEq n] :
    matDeriv (1 : Matrix n n R) = 0 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne h]

theorem matDeriv_inv {R : Type*} [CommRing R] [Differential R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    matDeriv M⁻¹ = -(M⁻¹ * matDeriv M * M⁻¹) := by
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M h
  have hd : matDeriv M * M⁻¹ + M * matDeriv M⁻¹ = 0 := by
    have := matDeriv_mul M M⁻¹
    rw [hmul, matDeriv_one] at this
    exact this.symm
  have hstep : M * matDeriv M⁻¹ = -(matDeriv M * M⁻¹) := by
    have := hd
    linear_combination (norm := module) this
  calc matDeriv M⁻¹ = M⁻¹ * (M * matDeriv M⁻¹) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M h, Matrix.one_mul]
    _ = M⁻¹ * (-(matDeriv M * M⁻¹)) := by rw [hstep]
    _ = -(M⁻¹ * matDeriv M * M⁻¹) := by
        rw [Matrix.mul_neg, Matrix.mul_assoc]



/-- The generic matrix of jet coordinates. -/
def genericJetMatrix (C : Type*) [Field C] (N : ℕ) :
    Matrix (Fin N) (Fin N) (JetField C (Fin N × Fin N)) :=
  Matrix.of fun i j => JetField.jet ((i, j), 0)

@[simp] theorem genericJetMatrix_apply (i j : Fin N) :
    genericJetMatrix C N i j = JetField.jet ((i, j), 0) := rfl

/-- The generic matrix of jet coordinates, over the polynomial ring. -/
def genericJetPolyMatrix (C : Type*) [Field C] (N : ℕ) :
    Matrix (Fin N) (Fin N) (JetPoly C (Fin N × Fin N)) :=
  Matrix.of fun i j => MvPolynomial.X ((i, j), 0)

theorem det_genericJetPolyMatrix_ne_zero : (genericJetPolyMatrix C N).det ≠ 0 := by
  classical
  intro h
  set f : (Fin N × Fin N) × ℕ → C := fun p => if p.2 = 0 ∧ p.1.1 = p.1.2 then 1 else 0 with hf
  have hmap : ((MvPolynomial.eval f).mapMatrix (genericJetPolyMatrix C N))
      = (1 : Matrix (Fin N) (Fin N) C) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [genericJetPolyMatrix, RingHom.mapMatrix_apply, hf, Matrix.one_apply]
    · simp [genericJetPolyMatrix, RingHom.mapMatrix_apply, hf, Matrix.one_apply, hij]
  have := RingHom.map_det (MvPolynomial.eval f) (genericJetPolyMatrix C N)
  rw [h, hmap] at this
  simp at this

/-! ### The generic fundamental matrix -/

theorem genericJetMatrix_eq_map :
    genericJetMatrix C N = (genericJetPolyMatrix C N).map
      (algebraMap (JetPoly C (Fin N × Fin N)) (JetField C (Fin N × Fin N))) := rfl

theorem det_genericJetMatrix_ne_zero : (genericJetMatrix C N).det ≠ 0 := by
  have hmap := RingHom.map_det
    (algebraMap (JetPoly C (Fin N × Fin N)) (JetField C (Fin N × Fin N)))
    (genericJetPolyMatrix C N)
  have hinj : Function.Injective
      (algebraMap (JetPoly C (Fin N × Fin N)) (JetField C (Fin N × Fin N))) :=
    IsFractionRing.injective _ _
  intro h
  rw [genericJetMatrix_eq_map, ← RingHom.mapMatrix_apply, ← hmap] at h
  exact det_genericJetPolyMatrix_ne_zero (hinj (by simpa using h))

theorem isUnit_det_genericJetMatrix : IsUnit (genericJetMatrix C N).det :=
  isUnit_iff_ne_zero.mpr det_genericJetMatrix_ne_zero

/-- The system matrix of the generic fundamental matrix, `A = Y⁻¹ δY`. -/
def genericSystemMatrix (C : Type*) [Field C] (N : ℕ) :
    Matrix (Fin N) (Fin N) (JetField C (Fin N × Fin N)) :=
  (genericJetMatrix C N)⁻¹ * matDeriv (genericJetMatrix C N)

/-- **The generic matrix is a fundamental matrix of its own system.** -/
theorem matDeriv_genericJetMatrix :
    matDeriv (genericJetMatrix C N)
      = genericJetMatrix C N * genericSystemMatrix C N := by
  rw [genericSystemMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ isUnit_det_genericJetMatrix, Matrix.one_mul]

/-- The `k`-th jet of the generic fundamental matrix. -/
def genericJetPower (C : Type*) [Field C] (N : ℕ) (k : ℕ) :
    Matrix (Fin N) (Fin N) (JetField C (Fin N × Fin N)) :=
  matDeriv^[k] (genericJetMatrix C N)

/-- The slice coordinates `B_k = Y⁻¹ Y^{(k)}`. -/
def genericSliceMatrix (C : Type*) [Field C] (N : ℕ) (k : ℕ) :
    Matrix (Fin N) (Fin N) (JetField C (Fin N × Fin N)) :=
  (genericJetMatrix C N)⁻¹ * genericJetPower C N k

@[simp] theorem genericJetPower_zero : genericJetPower C N 0 = genericJetMatrix C N := rfl

theorem genericJetPower_succ (k : ℕ) :
    genericJetPower C N (k + 1) = matDeriv (genericJetPower C N k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem genericSliceMatrix_zero : genericSliceMatrix C N 0 = 1 := by
  rw [genericSliceMatrix, genericJetPower_zero,
    Matrix.nonsing_inv_mul _ isUnit_det_genericJetMatrix]

@[simp] theorem genericSliceMatrix_one :
    genericSliceMatrix C N 1 = genericSystemMatrix C N := by
  rw [genericSliceMatrix, genericJetPower_succ, genericJetPower_zero, genericSystemMatrix]

/-- **The slice recursion.**  `B_{k+1} = δB_k + A · B_k`; every slice coordinate is therefore a
differential polynomial in the system matrix. -/
theorem genericSliceMatrix_succ (k : ℕ) :
    genericSliceMatrix C N (k + 1)
      = matDeriv (genericSliceMatrix C N k)
        + genericSystemMatrix C N * genericSliceMatrix C N k := by
  have hinv : matDeriv (genericJetMatrix C N)⁻¹
      = -((genericJetMatrix C N)⁻¹ * matDeriv (genericJetMatrix C N)
          * (genericJetMatrix C N)⁻¹) :=
    matDeriv_inv _ isUnit_det_genericJetMatrix
  have hstep : matDeriv (genericSliceMatrix C N k)
      = -(genericSystemMatrix C N * genericSliceMatrix C N k)
        + genericSliceMatrix C N (k + 1) := by
    rw [genericSliceMatrix, matDeriv_mul, hinv, genericSliceMatrix, genericJetPower_succ,
      genericSystemMatrix]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
  rw [hstep]
  abel



/-- The index matrix `Z ⊗ 1` of a left translation of the generic matrix. -/
def leftTranslationIndexMatrix (Z : Matrix (Fin N) (Fin N) C) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) C :=
  Matrix.of fun p q => Z p.1 q.1 * (if p.2 = q.2 then 1 else 0)

theorem leftTranslationIndexMatrix_mul (Z W : Matrix (Fin N) (Fin N) C) :
    leftTranslationIndexMatrix Z * leftTranslationIndexMatrix W
      = leftTranslationIndexMatrix (Z * W) := by
  classical
  ext p q
  obtain ⟨i, m⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [Matrix.mul_apply, leftTranslationIndexMatrix, Matrix.of_apply,
    Fintype.sum_prod_type]
  by_cases hml : m = l
  · subst hml
    have hinner : ∀ r1 : Fin N, (∑ r2 : Fin N,
        (Z i r1 * (if m = r2 then 1 else 0)) * (W r1 k * (if r2 = m then 1 else 0)))
        = Z i r1 * W r1 k := by
      intro r1
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb
        simp [Ne.symm hb, hb]
      · intro h
        exact absurd (Finset.mem_univ m) h
    simp only [hinner]
    simp
  · have hzero : ∀ r1 : Fin N, (∑ r2 : Fin N,
        (Z i r1 * (if m = r2 then 1 else 0)) * (W r1 k * (if r2 = l then 1 else 0))) = 0 := by
      intro r1
      refine Finset.sum_eq_zero fun r2 _ => ?_
      by_cases h1 : m = r2
      · subst h1
        simp [hml]
      · simp [h1]
    simp only [hzero, Finset.sum_const_zero, hml, if_false, mul_zero]

theorem leftTranslationIndexMatrix_one :
    leftTranslationIndexMatrix (1 : Matrix (Fin N) (Fin N) C) = 1 := by
  classical
  ext p q
  obtain ⟨i, m⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [leftTranslationIndexMatrix, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : i = k <;> by_cases h2 : m = l <;> simp [h1, h2]

/-! ### The left-translation automorphism -/

/-- The left translation of the generic matrix, as an algebra automorphism of the jet polynomial
ring. -/
def leftTranslationPolyEquiv (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) :
    JetPoly C (Fin N × Fin N) ≃ₐ[C] JetPoly C (Fin N × Fin N) :=
  differentialJetLinearChangeAlgEquiv (leftTranslationIndexMatrix Z)
    (leftTranslationIndexMatrix W)
    (by rw [leftTranslationIndexMatrix_mul, hZW, leftTranslationIndexMatrix_one])
    (by rw [leftTranslationIndexMatrix_mul, hWZ, leftTranslationIndexMatrix_one])

theorem leftTranslationPolyEquiv_X (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) (a b : Fin N) (r : ℕ) :
    leftTranslationPolyEquiv Z W hZW hWZ (MvPolynomial.X ((a, b), r))
      = ∑ k : Fin N, MvPolynomial.C (Z a k) * MvPolynomial.X ((k, b), r) := by
  classical
  rw [leftTranslationPolyEquiv, differentialJetLinearChangeAlgEquiv_X]
  rw [jetwiseMatrixLinearPolynomial]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [leftTranslationIndexMatrix]
  · intro c _ hc
    simp [leftTranslationIndexMatrix, Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem leftTranslationPolyEquiv_derivation (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) (P : JetPoly C (Fin N × Fin N)) :
    leftTranslationPolyEquiv Z W hZW hWZ
        (differentialPolynomialDerivation (Fin N × Fin N) C P)
      = differentialPolynomialDerivation (Fin N × Fin N) C
          (leftTranslationPolyEquiv Z W hZW hWZ P) :=
  differentialJetLinearChangeAlgEquiv_derivation _ _ _ _ P

/-- The left translation as an automorphism of the free differential rational field. -/
def leftTranslationFieldEquiv (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) :
    JetField C (Fin N × Fin N) ≃+* JetField C (Fin N × Fin N) :=
  IsFractionRing.ringEquivOfRingEquiv (K := JetField C (Fin N × Fin N))
    (L := JetField C (Fin N × Fin N)) (leftTranslationPolyEquiv Z W hZW hWZ).toRingEquiv

theorem leftTranslationFieldEquiv_algebraMap (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) (P : JetPoly C (Fin N × Fin N)) :
    leftTranslationFieldEquiv Z W hZW hWZ
        (algebraMap (JetPoly C (Fin N × Fin N)) (JetField C (Fin N × Fin N)) P)
      = algebraMap (JetPoly C (Fin N × Fin N)) (JetField C (Fin N × Fin N))
          (leftTranslationPolyEquiv Z W hZW hWZ P) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ P

theorem leftTranslationFieldEquiv_jet (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) (a b : Fin N) (r : ℕ) :
    leftTranslationFieldEquiv Z W hZW hWZ (JetField.jet ((a, b), r))
      = ∑ k : Fin N, algebraMap C (JetField C (Fin N × Fin N)) (Z a k)
          * JetField.jet ((k, b), r) := by
  rw [JetField.jet, leftTranslationFieldEquiv_algebraMap, leftTranslationPolyEquiv_X,
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1

theorem jetDerivation_algebraMap {ι : Type*} (P : JetPoly C ι) :
    JetField.jetDerivation (algebraMap (JetPoly C ι) (JetField C ι) P)
      = algebraMap (JetPoly C ι) (JetField C ι)
          (differentialPolynomialDerivation ι C P) := by
  rw [JetField.jetDerivation, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- The conjugate of the jet derivation by a left translation. -/
def leftTranslationConjDerivation (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) :
    Derivation ℤ (JetField C (Fin N × Fin N)) (JetField C (Fin N × Fin N)) := by
  let σ := leftTranslationFieldEquiv Z W hZW hWZ
  let D : JetField C (Fin N × Fin N) →+ JetField C (Fin N × Fin N) :=
    { toFun := fun z => σ.symm (JetField.jetDerivation (σ z))
      map_zero' := by simp
      map_add' := by intro x y; simp }
  refine Derivation.mk' D.toIntLinearMap ?_
  intro x y
  show σ.symm (JetField.jetDerivation (σ (x * y)))
    = x • σ.symm (JetField.jetDerivation (σ y)) + y • σ.symm (JetField.jetDerivation (σ x))
  rw [map_mul, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul, RingEquiv.symm_apply_apply]

@[simp] theorem leftTranslationConjDerivation_apply (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) (z : JetField C (Fin N × Fin N)) :
    leftTranslationConjDerivation Z W hZW hWZ z
      = (leftTranslationFieldEquiv Z W hZW hWZ).symm
          (JetField.jetDerivation (leftTranslationFieldEquiv Z W hZW hWZ z)) := rfl

/-- **The left translation is a differential automorphism.** -/
theorem leftTranslationFieldEquiv_deriv (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) (z : JetField C (Fin N × Fin N)) :
    leftTranslationFieldEquiv Z W hZW hWZ (z′)
      = (leftTranslationFieldEquiv Z W hZW hWZ z)′ := by
  have hconj : leftTranslationConjDerivation Z W hZW hWZ
      = (JetField.jetDerivation (C := C) (ι := Fin N × Fin N)).restrictScalars ℤ := by
    refine GaloisForLFunctions.fractionRing_derivation_ext
      (A := JetPoly C (Fin N × Fin N)) _ _ ?_
    intro P
    rw [leftTranslationConjDerivation_apply, leftTranslationFieldEquiv_algebraMap,
      jetDerivation_algebraMap, ← leftTranslationPolyEquiv_derivation,
      ← leftTranslationFieldEquiv_algebraMap, RingEquiv.symm_apply_apply]
    show _ = JetField.jetDerivation _
    rw [jetDerivation_algebraMap]
  have hz := congrArg (fun D => D z) hconj
  simp only [leftTranslationConjDerivation_apply, Derivation.coe_restrictScalars] at hz
  rw [JetField.deriv_eq, JetField.deriv_eq, ← hz, RingEquiv.apply_symm_apply]

/-- The base field consists of constants. -/
theorem deriv_algebraMap_jetField {ι : Type*} (c : C) :
    (algebraMap C (JetField C ι) c)′ = 0 := by
  have hb : (algebraMap C (JetField C ι) c)
      = algebraMap (JetPoly C ι) (JetField C ι) (MvPolynomial.C c) := by
    rw [IsScalarTower.algebraMap_apply C (JetPoly C ι) (JetField C ι)]
    rfl
  rw [hb, JetField.deriv_eq, jetDerivation_algebraMap]
  have : differentialPolynomialDerivation ι C (MvPolynomial.C c) = 0 := by
    simp [differentialPolynomialDerivation]
  rw [this, map_zero]


end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {C : Type*} [Field C] {N : ℕ}

/-- A constant matrix, seen inside the free differential rational field. -/
def baseMatrix (Z : Matrix (Fin N) (Fin N) C) :
    Matrix (Fin N) (Fin N) (JetField C (Fin N × Fin N)) :=
  (algebraMap C (JetField C (Fin N × Fin N))).mapMatrix Z

@[simp] theorem baseMatrix_apply (Z : Matrix (Fin N) (Fin N) C) (i j : Fin N) :
    baseMatrix Z i j = algebraMap C (JetField C (Fin N × Fin N)) (Z i j) := rfl

theorem baseMatrix_mul (Z W : Matrix (Fin N) (Fin N) C) :
    baseMatrix Z * baseMatrix W = baseMatrix (Z * W) :=
  (map_mul ((algebraMap C (JetField C (Fin N × Fin N))).mapMatrix) Z W).symm

@[simp] theorem baseMatrix_one :
    baseMatrix (1 : Matrix (Fin N) (Fin N) C) = 1 :=
  map_one ((algebraMap C (JetField C (Fin N × Fin N))).mapMatrix)

theorem matDeriv_baseMatrix (Z : Matrix (Fin N) (Fin N) C) :
    matDeriv (baseMatrix Z) = 0 := by
  ext i j
  simp [deriv_algebraMap_jetField]

/-- **The left translation multiplies the generic matrix on the left.** -/
theorem map_leftTranslationFieldEquiv_genericJetMatrix (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) :
    (genericJetMatrix C N).map
        ((leftTranslationFieldEquiv Z W hZW hWZ : JetField C (Fin N × Fin N) →+*
          JetField C (Fin N × Fin N)))
      = baseMatrix Z * genericJetMatrix C N := by
  ext i j
  rw [Matrix.map_apply, genericJetMatrix_apply]
  show leftTranslationFieldEquiv Z W hZW hWZ (JetField.jet ((i, j), 0)) = _
  rw [leftTranslationFieldEquiv_jet]
  simp [Matrix.mul_apply]

/-- **The left translation fixes the system matrix.**  The whole general linear group of constants
acts on the generic torsor over its own invariant base. -/
theorem map_leftTranslationFieldEquiv_genericSystemMatrix (Z W : Matrix (Fin N) (Fin N) C)
    (hZW : Z * W = 1) (hWZ : W * Z = 1) :
    (genericSystemMatrix C N).map
        ((leftTranslationFieldEquiv Z W hZW hWZ : JetField C (Fin N × Fin N) →+*
          JetField C (Fin N × Fin N)))
      = genericSystemMatrix C N := by
  set σ : JetField C (Fin N × Fin N) →+* JetField C (Fin N × Fin N) :=
    (leftTranslationFieldEquiv Z W hZW hWZ : JetField C (Fin N × Fin N) →+*
      JetField C (Fin N × Fin N)) with hσ
  have hφ : ∀ x : JetField C (Fin N × Fin N), σ (x′) = (σ x)′ :=
    leftTranslationFieldEquiv_deriv Z W hZW hWZ
  have hY : (genericJetMatrix C N).map σ = baseMatrix Z * genericJetMatrix C N :=
    map_leftTranslationFieldEquiv_genericJetMatrix Z W hZW hWZ
  have hsys : matDeriv (genericJetMatrix C N)
      = genericJetMatrix C N * genericSystemMatrix C N := matDeriv_genericJetMatrix
  have hleft : matDeriv ((genericJetMatrix C N).map σ)
      = (genericJetMatrix C N).map σ * (genericSystemMatrix C N).map σ := by
    rw [matDeriv_map _ _ hφ, hsys]
    simp
  have hright : matDeriv ((genericJetMatrix C N).map σ)
      = baseMatrix Z * (genericJetMatrix C N * genericSystemMatrix C N) := by
    rw [hY, matDeriv_const_mul _ (fun i j => by
      simp [deriv_algebraMap_jetField]), hsys]
  have hkey : baseMatrix Z * genericJetMatrix C N * (genericSystemMatrix C N).map σ
      = baseMatrix Z * (genericJetMatrix C N * genericSystemMatrix C N) := by
    rw [← hY, ← hleft, hright]
  have hcancelZ : genericJetMatrix C N * (genericSystemMatrix C N).map σ
      = genericJetMatrix C N * genericSystemMatrix C N := by
    have hW := congrArg (fun M => baseMatrix W * M) hkey
    simp only [← Matrix.mul_assoc, baseMatrix_mul, hWZ, baseMatrix_one, Matrix.one_mul] at hW
    exact hW
  have hYinv := Matrix.nonsing_inv_mul (genericJetMatrix C N) isUnit_det_genericJetMatrix
  have := congrArg (fun M => (genericJetMatrix C N)⁻¹ * M) hcancelZ
  simpa [← Matrix.mul_assoc, hYinv] using this

end

end GaloisForLFunctions.HTGeometry
