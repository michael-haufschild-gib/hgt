import GaloisForLFunctions.HTGeometry.GaloisMonoidDichotomyDiffFG

/-!
# Root-of-unity determinants in the Galois monoid

If the determinant of the tensor comparison matrix has finite order, every specialization has the
same determinant order, and so does the multiplicative Galois monoid it generates.  In the
order-two case this discharges both determinant hypotheses used by the Cassidy group step: the
determinant is nonzero and is a differential constant.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

variable {K R C : Type*} [Field K] [CommRing R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- If the two tensor copies of the Casoratian have the same `m`-th power, then the determinant of
their comparison matrix has `m`-th power one. -/
theorem comparisonMatrix_det_pow_eq_one_of_balanced
    {n : ℕ} (Y : Matrix (Fin n) (Fin n) R)
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hYdet : IsUnit Y.det) {m : ℕ}
    (hbalanced : (Y.det ⊗ₜ[K] (1 : R)) ^ m = ((1 : R) ⊗ₜ[K] Y.det) ^ m)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) :
    Z.det ^ m = 1 := by
  have hdetEq := congrArg Matrix.det hZ
  rw [Matrix.det_mul, det_leftFundamental, det_rightFundamental] at hdetEq
  have hleftUnit : IsUnit (Y.det ⊗ₜ[K] (1 : R)) :=
    hYdet.map (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] R).toRingHom
  apply (hleftUnit.pow m).mul_left_cancel
  calc
    (Y.det ⊗ₜ[K] (1 : R)) ^ m * Z.det ^ m =
        ((Y.det ⊗ₜ[K] (1 : R)) * Z.det) ^ m := by rw [mul_pow]
    _ = ((1 : R) ⊗ₜ[K] Y.det) ^ m := by rw [hdetEq]
    _ = (Y.det ⊗ₜ[K] (1 : R)) ^ m := hbalanced.symm
    _ = (Y.det ⊗ₜ[K] (1 : R)) ^ m * 1 := by rw [mul_one]

/-- For a system with determinant `-1`, no new difference constants force the comparison
determinant to have square one. -/
theorem comparisonMatrix_det_sq_eq_one_of_neg_one_system
    {σR : R ≃+* R} (A Y : Matrix (Fin 2) (Fin 2) R)
    (hAdet : A.det = -1) (hYdet : IsUnit Y.det)
    (hsys : Y.map (σR : R → R) = A * Y)
    (hnew : ∀ x : R, σR x = x → ∃ a : K, x = algebraMap K R a)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R))
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) :
    Z.det ^ 2 = 1 := by
  have hdetSys := congrArg Matrix.det hsys
  have hmapY : (Y.map (σR : R → R)).det = σR Y.det := by
    have hmap := RingHom.map_det σR.toRingHom Y
    rw [RingHom.mapMatrix_apply] at hmap
    exact hmap.symm
  rw [Matrix.det_mul, hmapY, hAdet, neg_mul, one_mul] at hdetSys
  have hfixed : σR (Y.det ^ 2) = Y.det ^ 2 := by
    rw [map_pow, hdetSys]
    ring
  obtain ⟨a, ha⟩ := hnew (Y.det ^ 2) hfixed
  apply comparisonMatrix_det_pow_eq_one_of_balanced Y Z hYdet (m := 2) ?_ hZ
  rw [pow_two, pow_two, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, ← pow_two, ← pow_two]
  rw [ha]
  simp only [one_pow]
  calc
    (algebraMap K R a) ⊗ₜ[K] (1 : R) = (a • (1 : R)) ⊗ₜ[K] (1 : R) := by
      rw [Algebra.smul_def, mul_one]
    _ = (1 : R) ⊗ₜ[K] (a • (1 : R)) := (TensorProduct.tmul_smul a 1 1).symm
    _ = (1 : R) ⊗ₜ[K] (algebraMap K R a) := by rw [Algebra.smul_def, mul_one]

/-- Specializing a comparison matrix preserves every finite-order determinant relation. -/
theorem galoisMatrixAt_det_pow_eq_one
    (E : Subalgebra C (R ⊗[K] R))
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    {m : ℕ} (hdet : Z.det ^ m = 1) (χ : E →ₐ[C] C) :
    (galoisMatrixAt E Z hZE χ).det ^ m = 1 := by
  let ZE : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ⟨Z i j, hZE i j⟩
  have hZE_map : ZE.map (Subalgebra.val E) = Z := by
    ext i j
    rfl
  have hdet_coe : ((ZE.det : E) : R ⊗[K] R) = Z.det := by
    have hmap := RingHom.map_det (Subalgebra.val E).toRingHom ZE
    rw [RingHom.mapMatrix_apply] at hmap
    calc
      ((ZE.det : E) : R ⊗[K] R) = (ZE.map (Subalgebra.val E)).det := by simpa using hmap
      _ = Z.det := by rw [hZE_map]
  have hdetE : ZE.det ^ m = 1 := by
    apply Subtype.ext
    change ((ZE.det : E) : R ⊗[K] R) ^ m = 1
    rw [hdet_coe, hdet]
  have hg : galoisMatrixAt E Z hZE χ = ZE.map χ.toRingHom := by
    ext i j
    rfl
  rw [hg]
  have hmap := RingHom.map_det χ.toRingHom ZE
  rw [RingHom.mapMatrix_apply] at hmap
  calc
    (ZE.map χ.toRingHom).det ^ m = (χ ZE.det) ^ m := by
      exact congrArg (fun x : C => x ^ m) hmap.symm
    _ = χ (ZE.det ^ m) := by rw [map_pow]
    _ = 1 := by rw [hdetE, map_one]

/-- A finite-order determinant relation on the comparison matrix propagates through the whole
multiplicative Galois monoid. -/
theorem galoisMonoid_det_pow_eq_one
    (E : Subalgebra C (R ⊗[K] R))
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    {m : ℕ} (hdet : Z.det ^ m = 1) (S : Set (E →ₐ[C] C))
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ galoisMonoid E Z hZE S) :
    g.det ^ m = 1 := by
  let U : Submonoid (Matrix (Fin 2) (Fin 2) C) :=
    { carrier := {g | g.det ^ m = 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change a.det ^ m = 1 at ha
        change b.det ^ m = 1 at hb
        change (a * b).det ^ m = 1
        rw [Matrix.det_mul, mul_pow, ha, hb, one_mul] }
  have hgen : {g : Matrix (Fin 2) (Fin 2) C |
      ∃ χ ∈ S, galoisMatrixAt E Z hZE χ = g} ⊆ U := by
    rintro g ⟨χ, hχ, rfl⟩
    exact galoisMatrixAt_det_pow_eq_one E Z hZE hdet χ
  change g ∈ Submonoid.closure {g : Matrix (Fin 2) (Fin 2) C |
    ∃ χ ∈ S, galoisMatrixAt E Z hZE χ = g} at hg
  exact (Submonoid.closure_le.mpr hgen) hg

/-- A square-one determinant is nonzero. -/
theorem galoisMonoid_det_ne_zero_of_sq_eq_one
    (E : Subalgebra C (R ⊗[K] R))
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hdet : Z.det ^ 2 = 1) (S : Set (E →ₐ[C] C))
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ galoisMonoid E Z hZE S) :
    g.det ≠ 0 := by
  have hs := galoisMonoid_det_pow_eq_one E Z hZE hdet S hg
  intro hzero
  rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  exact zero_ne_one hs

/-- In a differential field, every square root of one is a differential constant. -/
theorem mem_differentialConstants_of_sq_eq_one
    [Differential C] {x : C} (hx : x ^ 2 = 1) :
    x ∈ differentialConstants C := by
  have hfactor : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hfactor with h | h
  · rw [sub_eq_zero.mp h]
    exact (differentialConstants C).one_mem
  · have hxneg : x = -1 := eq_neg_of_add_eq_zero_left h
    rw [hxneg]
    exact (differentialConstants C).neg_mem (differentialConstants C).one_mem

/-- In the order-two case every determinant in the Galois monoid is a differential constant. -/
theorem galoisMonoid_det_mem_differentialConstants_of_sq_eq_one
    [Differential C]
    (E : Subalgebra C (R ⊗[K] R))
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hdet : Z.det ^ 2 = 1) (S : Set (E →ₐ[C] C))
    {g : Matrix (Fin 2) (Fin 2) C} (hg : g ∈ galoisMonoid E Z hZE S) :
    g.det ∈ differentialConstants C :=
  mem_differentialConstants_of_sq_eq_one
    (galoisMonoid_det_pow_eq_one E Z hZE hdet S hg)

end

end GaloisForLFunctions.HTGeometry
