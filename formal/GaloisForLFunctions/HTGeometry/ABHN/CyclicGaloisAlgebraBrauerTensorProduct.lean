import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraTensorDiagonal
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisTensorProductDecomposition
import GaloisForLFunctions.HTGeometry.ABHN.TransformationSkewMatrix
import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure

/-!
# Tensor-product addition for cyclic Galois algebras

For a finite cyclic Galois extension `L/K` and nonzero parameters `a,b ∈ K`, this file proves

`[A(L/K,σ,a)] + [A(L/K,σ,b)] = [A(L/K,σ,a*b)]`

in `BrauerGroup K`.

The proof is explicit.  It embeds `A(a*b)` diagonally into `A(a) ⊗ A(b)`, identifies
`L ⊗_K L` with functions on `Gal(L/K)`, constructs a weighted right generator whose degree
power is one, and realizes the resulting transformation crossed product as a split matrix
centralizer.  Commutation and equal dimensions then give

`A(a*b) ⊗ ((K^G) ⋊ G) ≃ A(a) ⊗ A(b)`.

This is the missing multiplicative-parameter/additive-Brauer-class law needed to make cyclic
cohomology-to-Brauer maps additive.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

noncomputable def cyclicGaloisCoefficientAlgHom (a : K) :
    L →ₐ[K] cyclicGaloisAlgebra K L a :=
  AlgHom.mk'
    (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)) (by
      intro c x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1)

@[simp]
theorem cyclicGaloisCoefficientAlgHom_apply (a : K) (x : L) :
    cyclicGaloisCoefficientAlgHom K L a x = cyclicGaloisAlgebraC K L a x := rfl

noncomputable def cyclicGaloisTensorCoefficientAlgHom (a b : K) :
    L ⊗[K] L →ₐ[K]
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  Algebra.TensorProduct.map (cyclicGaloisCoefficientAlgHom K L a)
    (cyclicGaloisCoefficientAlgHom K L b)

@[simp]
theorem cyclicGaloisTensorCoefficientAlgHom_tmul (a b : K) (x y : L) :
    cyclicGaloisTensorCoefficientAlgHom K L a b (x ⊗ₜ[K] y) =
      cyclicGaloisAlgebraC K L a x ⊗ₜ[K] cyclicGaloisAlgebraC K L b y := by
  rfl

noncomputable def cyclicTensorCentralizerCoefficientAlgHom (a b : K) :
    TransformationFunctions K Gal(L/K) →ₐ[K]
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  (cyclicGaloisTensorCoefficientAlgHom K L a b).comp
    (cyclicGaloisTensorFixedCoefficientEmbedding K L)

noncomputable def cyclicTensorCentralizerRightGenerator (a b : K) :
    cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b :=
  1 ⊗ₜ[K] cyclicGaloisAlgebraX K L b

theorem cyclicTensorCentralizerRightGenerator_covariant_tensor
    (a b : K) (t : L ⊗[K] L) :
    cyclicTensorCentralizerRightGenerator K L a b * cyclicGaloisTensorCoefficientAlgHom K L a b t =
      cyclicGaloisTensorCoefficientAlgHom K L a b
          (Algebra.TensorProduct.map (AlgHom.id K L)
            (cyclicGaloisGenerator K L).toAlgHom t) *
        cyclicTensorCentralizerRightGenerator K L a b := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, mul_add, add_mul, hx, hy]
  | tmul x y =>
      simp only [cyclicTensorCentralizerRightGenerator, cyclicGaloisTensorCoefficientAlgHom_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [mul_one]
      apply congrArg (fun z : cyclicGaloisAlgebra K L b =>
        cyclicGaloisAlgebraC K L a x ⊗ₜ[K] z)
      change cyclicGaloisAlgebraX K L b * cyclicGaloisAlgebraC K L b y =
        cyclicGaloisAlgebraC K L b
            ((cyclicGaloisGenerator K L).toRingEquiv y) *
          cyclicGaloisAlgebraX K L b
      simpa only [pow_one] using
        (cyclicAlgebraX_pow_mul_C (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L b) y 1)

theorem cyclicTensorCentralizerRightGenerator_covariant
    (a b : K) (f : TransformationFunctions K Gal(L/K)) :
    cyclicTensorCentralizerRightGenerator K L a b * cyclicTensorCentralizerCoefficientAlgHom K L a b f =
      cyclicTensorCentralizerCoefficientAlgHom K L a b
          ((cyclicGaloisGenerator K L) • f) *
        cyclicTensorCentralizerRightGenerator K L a b := by
  change cyclicTensorCentralizerRightGenerator K L a b *
      cyclicGaloisTensorCoefficientAlgHom K L a b
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) =
    cyclicGaloisTensorCoefficientAlgHom K L a b
        (cyclicGaloisTensorFixedCoefficientEmbedding K L
          ((cyclicGaloisGenerator K L) • f)) *
      cyclicTensorCentralizerRightGenerator K L a b
  rw [cyclicTensorCentralizerRightGenerator_covariant_tensor,
    cyclicGaloisTensorFixedCoefficientEmbedding_map_right]
  rfl

noncomputable def cyclicGaloisGeneratorFinEquiv :
    Fin (Module.finrank K L) ≃ Gal(L/K) :=
  Equiv.ofBijective (fun i => cyclicGaloisGenerator K L ^ (i : ℕ)) (by
    classical
    constructor
    · intro i j hij
      apply Fin.ext
      apply pow_injOn_Iio_orderOf (x := cyclicGaloisGenerator K L)
      · simpa [cyclicGaloisGenerator_orderOf K L] using i.isLt
      · simpa [cyclicGaloisGenerator_orderOf K L] using j.isLt
      · exact hij
    · intro σ
      have hfull := IsCyclic.image_range_orderOf (cyclicGaloisGenerator_spec K L)
      have hmem : σ ∈ (Finset.range (orderOf (cyclicGaloisGenerator K L))).image
          (cyclicGaloisGenerator K L ^ ·) := by
        rw [hfull]
        simp
      obtain ⟨i, hi, hpow⟩ := Finset.mem_image.mp hmem
      refine ⟨⟨i, ?_⟩, hpow⟩
      simpa [cyclicGaloisGenerator_orderOf K L] using Finset.mem_range.mp hi)

noncomputable def cyclicTensorCentralizerTwist (b : K) :
    TransformationFunctions K Gal(L/K) :=
  by
    classical
    exact fun σ => if σ = 1 then b⁻¹ else 1

theorem cyclicTensorCentralizerTwist_prod (b : K) (τ : Gal(L/K)) :
    ∏ i : Fin (Module.finrank K L),
        ((cyclicGaloisGenerator K L ^ (i : ℕ)) •
          cyclicTensorCentralizerTwist K L b) τ = b⁻¹ := by
  classical
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let e : Fin (Module.finrank K L) ≃ Gal(L/K) :=
    (cyclicGaloisGeneratorFinEquiv K L).trans (Equiv.mulLeft τ)
  calc
    ∏ i : Fin (Module.finrank K L),
        ((cyclicGaloisGenerator K L ^ (i : ℕ)) •
          cyclicTensorCentralizerTwist K L b) τ =
      ∏ i : Fin (Module.finrank K L), cyclicTensorCentralizerTwist K L b (e i) := by
        rfl
    _ = ∏ σ : Gal(L/K), cyclicTensorCentralizerTwist K L b σ := e.prod_comp _
    _ = b⁻¹ := by
      simp [cyclicTensorCentralizerTwist]

theorem cyclicTensorCentralizerRightGenerator_pow_covariant
    (a b : K) (m : ℕ) (f : TransformationFunctions K Gal(L/K)) :
    cyclicTensorCentralizerRightGenerator K L a b ^ m * cyclicTensorCentralizerCoefficientAlgHom K L a b f =
      cyclicTensorCentralizerCoefficientAlgHom K L a b
          ((cyclicGaloisGenerator K L ^ m) • f) *
        cyclicTensorCentralizerRightGenerator K L a b ^ m := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, mul_assoc, cyclicTensorCentralizerRightGenerator_covariant]
      rw [← mul_assoc, ih, mul_assoc, ← pow_succ]
      congr 1

noncomputable def cyclicTensorCentralizerTwistProduct (b : K) (m : ℕ) :
    TransformationFunctions K Gal(L/K) :=
  ∏ i ∈ Finset.range m,
    (cyclicGaloisGenerator K L ^ i) • cyclicTensorCentralizerTwist K L b

noncomputable def cyclicTensorCentralizerGenerator (a b : K) :
    cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b :=
  cyclicTensorCentralizerCoefficientAlgHom K L a b (cyclicTensorCentralizerTwist K L b) *
    cyclicTensorCentralizerRightGenerator K L a b

theorem cyclicTensorCentralizerGenerator_pow
    (a b : K) (m : ℕ) :
    cyclicTensorCentralizerGenerator K L a b ^ m =
      cyclicTensorCentralizerCoefficientAlgHom K L a b
          (cyclicTensorCentralizerTwistProduct K L b m) *
        cyclicTensorCentralizerRightGenerator K L a b ^ m := by
  induction m with
  | zero =>
      simp [cyclicTensorCentralizerTwistProduct]
  | succ m ih =>
      rw [pow_succ, ih, cyclicTensorCentralizerGenerator]
      calc
        cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwistProduct K L b m) *
            cyclicTensorCentralizerRightGenerator K L a b ^ m *
              (cyclicTensorCentralizerCoefficientAlgHom K L a b
                    (cyclicTensorCentralizerTwist K L b) *
                cyclicTensorCentralizerRightGenerator K L a b) =
          cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwistProduct K L b m) *
            ((cyclicTensorCentralizerRightGenerator K L a b ^ m *
                cyclicTensorCentralizerCoefficientAlgHom K L a b
                  (cyclicTensorCentralizerTwist K L b)) *
              cyclicTensorCentralizerRightGenerator K L a b) := by
            ac_rfl
        _ = cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwistProduct K L b m) *
            ((cyclicTensorCentralizerCoefficientAlgHom K L a b
                  ((cyclicGaloisGenerator K L ^ m) •
                    cyclicTensorCentralizerTwist K L b) *
                cyclicTensorCentralizerRightGenerator K L a b ^ m) *
              cyclicTensorCentralizerRightGenerator K L a b) := by
            rw [cyclicTensorCentralizerRightGenerator_pow_covariant]
        _ = (cyclicTensorCentralizerCoefficientAlgHom K L a b
                (cyclicTensorCentralizerTwistProduct K L b m) *
              cyclicTensorCentralizerCoefficientAlgHom K L a b
                ((cyclicGaloisGenerator K L ^ m) •
                  cyclicTensorCentralizerTwist K L b)) *
            (cyclicTensorCentralizerRightGenerator K L a b ^ m *
              cyclicTensorCentralizerRightGenerator K L a b) := by
            ac_rfl
        _ = cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwistProduct K L b m *
                ((cyclicGaloisGenerator K L ^ m) •
                  cyclicTensorCentralizerTwist K L b)) *
            cyclicTensorCentralizerRightGenerator K L a b ^ (m + 1) := by
            rw [map_mul, pow_succ]
        _ = cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwistProduct K L b (m + 1)) *
            cyclicTensorCentralizerRightGenerator K L a b ^ (m + 1) := by
            congr 1
            simp [cyclicTensorCentralizerTwistProduct, Finset.prod_range_succ]

theorem cyclicTensorCentralizerTwistProduct_finrank (b : K) :
    cyclicTensorCentralizerTwistProduct K L b (Module.finrank K L) =
      (fun _ : Gal(L/K) => b⁻¹) := by
  apply TransformationFunctions.ext
  intro τ
  unfold cyclicTensorCentralizerTwistProduct
  rw [Finset.prod_apply]
  change (∏ i ∈ Finset.range (Module.finrank K L),
      ((cyclicGaloisGenerator K L ^ i) •
        cyclicTensorCentralizerTwist K L b) τ) = b⁻¹
  rw [← Fin.prod_univ_eq_prod_range]
  exact cyclicTensorCentralizerTwist_prod K L b τ

theorem cyclicTensorCentralizerRightGenerator_pow_finrank (a b : K) :
    cyclicTensorCentralizerRightGenerator K L a b ^ Module.finrank K L =
      algebraMap K
        (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) b := by
  rw [cyclicTensorCentralizerRightGenerator, cyclicTensorProduct_tmul_pow, one_pow,
    cyclicGaloisAlgebraX_pow]
  change (1 : cyclicGaloisAlgebra K L a) ⊗ₜ[K]
      algebraMap K (cyclicGaloisAlgebra K L b) b = _
  rw [show algebraMap K (cyclicGaloisAlgebra K L b) b =
      b • (1 : cyclicGaloisAlgebra K L b) by simp [Algebra.smul_def]]
  rw [TensorProduct.tmul_smul]
  rw [Algebra.TensorProduct.algebraMap_apply]
  apply congrArg (fun z : cyclicGaloisAlgebra K L a =>
    z ⊗ₜ[K] (1 : cyclicGaloisAlgebra K L b))
  simp [Algebra.smul_def]

theorem cyclicTensorCentralizerGenerator_pow_finrank
    (a b : K) (hb : b ≠ 0) :
    cyclicTensorCentralizerGenerator K L a b ^ Module.finrank K L = 1 := by
  rw [cyclicTensorCentralizerGenerator_pow,
    cyclicTensorCentralizerTwistProduct_finrank,
    cyclicTensorCentralizerRightGenerator_pow_finrank]
  change cyclicTensorCentralizerCoefficientAlgHom K L a b
      (algebraMap K (TransformationFunctions K Gal(L/K)) b⁻¹) *
    algebraMap K
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) b = 1
  rw [(cyclicTensorCentralizerCoefficientAlgHom K L a b).commutes]
  rw [← map_mul, inv_mul_cancel₀ hb, map_one]

noncomputable def cyclicTensorCentralizerTwistUnit (b : K) (hb : b ≠ 0) :
    (TransformationFunctions K Gal(L/K))ˣ where
  val := cyclicTensorCentralizerTwist K L b
  inv := by
    classical
    exact fun σ => if σ = 1 then b else 1
  val_inv := by
    apply TransformationFunctions.ext
    intro σ
    classical
    by_cases hσ : σ = 1
    · simp [cyclicTensorCentralizerTwist, hσ, inv_mul_cancel₀ hb]
    · simp [cyclicTensorCentralizerTwist, hσ]
  inv_val := by
    apply TransformationFunctions.ext
    intro σ
    classical
    by_cases hσ : σ = 1
    · simp [cyclicTensorCentralizerTwist, hσ, mul_inv_cancel₀ hb]
    · simp [cyclicTensorCentralizerTwist, hσ]

noncomputable def cyclicTensorCentralizerRightGeneratorUnit (a b : K) (hb : b ≠ 0) :
    (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b)ˣ :=
  Units.map
      (Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom)
      (cyclicGaloisAlgebraXUnit K L b hb)

@[simp]
theorem cyclicTensorCentralizerRightGeneratorUnit_coe (a b : K) (hb : b ≠ 0) :
    (cyclicTensorCentralizerRightGeneratorUnit K L a b hb :
      cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) =
        cyclicTensorCentralizerRightGenerator K L a b := by
  simp [cyclicTensorCentralizerRightGeneratorUnit, cyclicTensorCentralizerRightGenerator,
    cyclicGaloisAlgebraXUnit_coe]

noncomputable def cyclicTensorCentralizerGeneratorUnit (a b : K) (hb : b ≠ 0) :
    (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b)ˣ :=
  Units.map (cyclicTensorCentralizerCoefficientAlgHom K L a b).toRingHom.toMonoidHom
      (cyclicTensorCentralizerTwistUnit K L b hb) *
    cyclicTensorCentralizerRightGeneratorUnit K L a b hb

@[simp]
theorem cyclicTensorCentralizerGeneratorUnit_coe (a b : K) (hb : b ≠ 0) :
    (cyclicTensorCentralizerGeneratorUnit K L a b hb :
      cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) =
        cyclicTensorCentralizerGenerator K L a b := by
  simp [cyclicTensorCentralizerGeneratorUnit, cyclicTensorCentralizerGenerator,
    cyclicTensorCentralizerTwistUnit]

theorem cyclicTensorCentralizerGeneratorUnit_pow_finrank
    (a b : K) (hb : b ≠ 0) :
    cyclicTensorCentralizerGeneratorUnit K L a b hb ^ Module.finrank K L = 1 := by
  apply Units.ext
  simpa using cyclicTensorCentralizerGenerator_pow_finrank K L a b hb

noncomputable def cyclicTensorCentralizerUnitAction (a b : K) (hb : b ≠ 0) :
    Gal(L/K) →*
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b)ˣ :=
  monoidHomOfForallMemZpowers (cyclicGaloisGenerator_spec K L) (by
    rw [cyclicGaloisGenerator_orderOf K L]
    exact orderOf_dvd_of_pow_eq_one
      (cyclicTensorCentralizerGeneratorUnit_pow_finrank K L a b hb))

@[simp]
theorem cyclicTensorCentralizerUnitAction_generator (a b : K) (hb : b ≠ 0) :
    cyclicTensorCentralizerUnitAction K L a b hb (cyclicGaloisGenerator K L) =
      cyclicTensorCentralizerGeneratorUnit K L a b hb := by
  exact monoidHomOfForallMemZpowers_apply_gen _ _

theorem cyclicTensorCentralizerGenerator_covariant
    (a b : K) (f : TransformationFunctions K Gal(L/K)) :
    cyclicTensorCentralizerGenerator K L a b *
        cyclicTensorCentralizerCoefficientAlgHom K L a b f =
      cyclicTensorCentralizerCoefficientAlgHom K L a b
          ((cyclicGaloisGenerator K L) • f) *
        cyclicTensorCentralizerGenerator K L a b := by
  rw [cyclicTensorCentralizerGenerator, mul_assoc, cyclicTensorCentralizerRightGenerator_covariant]
  calc
    cyclicTensorCentralizerCoefficientAlgHom K L a b (cyclicTensorCentralizerTwist K L b) *
          (cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicGaloisGenerator K L • f) *
            cyclicTensorCentralizerRightGenerator K L a b) =
        (cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwist K L b) *
            cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicGaloisGenerator K L • f)) *
          cyclicTensorCentralizerRightGenerator K L a b := by rw [mul_assoc]
    _ = (cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicGaloisGenerator K L • f) *
            cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwist K L b)) *
          cyclicTensorCentralizerRightGenerator K L a b := by
            rw [← map_mul, mul_comm, map_mul]
    _ = cyclicTensorCentralizerCoefficientAlgHom K L a b
            (cyclicGaloisGenerator K L • f) *
          (cyclicTensorCentralizerCoefficientAlgHom K L a b
              (cyclicTensorCentralizerTwist K L b) *
            cyclicTensorCentralizerRightGenerator K L a b) := by rw [mul_assoc]

theorem cyclicTensorCentralizerGenerator_pow_covariant
    (a b : K) (m : ℕ) (f : TransformationFunctions K Gal(L/K)) :
    cyclicTensorCentralizerGenerator K L a b ^ m *
        cyclicTensorCentralizerCoefficientAlgHom K L a b f =
      cyclicTensorCentralizerCoefficientAlgHom K L a b
          ((cyclicGaloisGenerator K L ^ m) • f) *
        cyclicTensorCentralizerGenerator K L a b ^ m := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, mul_assoc, cyclicTensorCentralizerGenerator_covariant]
      rw [← mul_assoc, ih, mul_assoc, ← pow_succ]
      congr 1

@[simp]
theorem cyclicTensorCentralizerUnitAction_pow_coe
    (a b : K) (hb : b ≠ 0) (m : ℕ) :
    ((cyclicTensorCentralizerUnitAction K L a b hb
        (cyclicGaloisGenerator K L ^ m) :
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b)ˣ) :
        cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) =
      cyclicTensorCentralizerGenerator K L a b ^ m := by
  rw [map_pow, cyclicTensorCentralizerUnitAction_generator]
  simp

theorem cyclicTensorCentralizerUnitAction_covariant
    (a b : K) (hb : b ≠ 0) (f : TransformationFunctions K Gal(L/K))
    (σ : Gal(L/K)) :
    cyclicTensorCentralizerCoefficientAlgHom K L a b (σ • f) *
        (cyclicTensorCentralizerUnitAction K L a b hb σ :
          cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) =
      (cyclicTensorCentralizerUnitAction K L a b hb σ :
          cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) *
        cyclicTensorCentralizerCoefficientAlgHom K L a b f := by
  let i := (cyclicGaloisGeneratorFinEquiv K L).symm σ
  have hσ : cyclicGaloisGenerator K L ^ (i : ℕ) = σ :=
    (cyclicGaloisGeneratorFinEquiv K L).apply_symm_apply σ
  rw [← hσ, cyclicTensorCentralizerUnitAction_pow_coe]
  exact (cyclicTensorCentralizerGenerator_pow_covariant K L a b (i : ℕ) f).symm

noncomputable def cyclicTensorCentralizerSkewAlgHom (a b : K) (hb : b ≠ 0) :
    SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K) →ₐ[K]
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  SkewMonoidAlgebra.liftNCAlgHom
    (cyclicTensorCentralizerCoefficientAlgHom K L a b)
    ((Units.coeHom
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b)).comp
        (cyclicTensorCentralizerUnitAction K L a b hb))
    (fun {f} σ => cyclicTensorCentralizerUnitAction_covariant K L a b hb f σ)

@[simp]
theorem cyclicTensorCentralizerSkewAlgHom_single
    (a b : K) (hb : b ≠ 0) (σ : Gal(L/K))
    (f : TransformationFunctions K Gal(L/K)) :
    cyclicTensorCentralizerSkewAlgHom K L a b hb (SkewMonoidAlgebra.single σ f) =
      cyclicTensorCentralizerCoefficientAlgHom K L a b f *
        (cyclicTensorCentralizerUnitAction K L a b hb σ :
          cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := by
  exact SkewMonoidAlgebra.liftNC_single _ _ _ _

theorem cyclicTensorCentralizerSkewAlgHom_injective
    (a b : K) (hb : b ≠ 0) :
    Function.Injective (cyclicTensorCentralizerSkewAlgHom K L a b hb) := by
  classical
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  letI : Nontrivial (cyclicGaloisAlgebra K L b) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L b).symm⟩
  letI : Nontrivial
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := inferInstance
  letI : IsSimpleRing
      (SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    isSimpleRing_transformationSkew K Gal(L/K)
  exact RingHom.injective (cyclicTensorCentralizerSkewAlgHom K L a b hb).toRingHom

theorem cyclicTensorDiagonalGenerator_covariant_tensor
    (a b : K) (t : L ⊗[K] L) :
    cyclicGaloisAlgebraTensorDiagonalGenerator K L a b *
        cyclicGaloisTensorCoefficientAlgHom K L a b t =
      cyclicGaloisTensorCoefficientAlgHom K L a b
          (Algebra.TensorProduct.map (cyclicGaloisGenerator K L).toAlgHom
            (cyclicGaloisGenerator K L).toAlgHom t) *
        cyclicGaloisAlgebraTensorDiagonalGenerator K L a b := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, mul_add, add_mul, hx, hy]
  | tmul x y =>
      simp only [cyclicGaloisAlgebraTensorDiagonalGenerator,
        cyclicGaloisTensorCoefficientAlgHom_tmul,
        Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      apply congrArg₂ (fun u v => u ⊗ₜ[K] v)
      · convert (cyclicAlgebraX_pow_mul_C
            (cyclicGaloisGenerator K L).toRingEquiv
            (Module.finrank K L) (algebraMap K L a) x 1) using 1 <;>
            simp only [pow_one] <;> rfl
      · convert (cyclicAlgebraX_pow_mul_C
            (cyclicGaloisGenerator K L).toRingEquiv
            (Module.finrank K L) (algebraMap K L b) y 1) using 1 <;>
            simp only [pow_one] <;> rfl

theorem cyclicTensorDiagonalGenerator_commute_centralizerCoefficient
    (a b : K) (f : TransformationFunctions K Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b)
      (cyclicTensorCentralizerCoefficientAlgHom K L a b f) := by
  change cyclicGaloisAlgebraTensorDiagonalGenerator K L a b *
      cyclicGaloisTensorCoefficientAlgHom K L a b
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) =
    cyclicGaloisTensorCoefficientAlgHom K L a b
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) *
      cyclicGaloisAlgebraTensorDiagonalGenerator K L a b
  rw [cyclicTensorDiagonalGenerator_covariant_tensor,
    cyclicGaloisTensorFixedCoefficientEmbedding_map_diagonal]

theorem cyclicTensorDiagonalCoefficient_commute_centralizerCoefficient
    (a b : K) (x : L) (f : TransformationFunctions K Gal(L/K)) :
    Commute (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
      (1 : cyclicGaloisAlgebra K L b))
      (cyclicTensorCentralizerCoefficientAlgHom K L a b f) := by
  have hx : cyclicGaloisTensorCoefficientAlgHom K L a b
        (x ⊗ₜ[K] (1 : L)) =
      cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L b) := by
    simpa only [cyclicGaloisTensorCoefficientAlgHom_tmul,
      cyclicAlgebraC_one]
  rw [← hx]
  change Commute
    (cyclicGaloisTensorCoefficientAlgHom K L a b (x ⊗ₜ[K] (1 : L)))
    (cyclicGaloisTensorCoefficientAlgHom K L a b
      (cyclicGaloisTensorFixedCoefficientEmbedding K L f))
  change cyclicGaloisTensorCoefficientAlgHom K L a b (x ⊗ₜ[K] (1 : L)) *
      cyclicGaloisTensorCoefficientAlgHom K L a b
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) =
    cyclicGaloisTensorCoefficientAlgHom K L a b
        (cyclicGaloisTensorFixedCoefficientEmbedding K L f) *
      cyclicGaloisTensorCoefficientAlgHom K L a b (x ⊗ₜ[K] (1 : L))
  rw [← map_mul, mul_comm, map_mul]

theorem cyclicTensorDiagonalCoefficient_commute_rightGenerator
    (a b : K) (x : L) :
    Commute (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
      (1 : cyclicGaloisAlgebra K L b))
      (cyclicTensorCentralizerRightGenerator K L a b) := by
  change (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L b)) *
      ((1 : cyclicGaloisAlgebra K L a) ⊗ₜ[K]
        cyclicGaloisAlgebraX K L b) =
    ((1 : cyclicGaloisAlgebra K L a) ⊗ₜ[K]
        cyclicGaloisAlgebraX K L b) *
      (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
        (1 : cyclicGaloisAlgebra K L b))
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem cyclicTensorDiagonalGenerator_commute_rightGenerator
    (a b : K) :
    Commute (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b)
      (cyclicTensorCentralizerRightGenerator K L a b) := by
  change (cyclicGaloisAlgebraX K L a ⊗ₜ[K]
        cyclicGaloisAlgebraX K L b) *
      ((1 : cyclicGaloisAlgebra K L a) ⊗ₜ[K]
        cyclicGaloisAlgebraX K L b) =
    ((1 : cyclicGaloisAlgebra K L a) ⊗ₜ[K]
        cyclicGaloisAlgebraX K L b) *
      (cyclicGaloisAlgebraX K L a ⊗ₜ[K]
        cyclicGaloisAlgebraX K L b)
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem cyclicTensorDiagonalCoefficient_commute_twistedRightGenerator
    (a b : K) (x : L) :
    Commute (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
      (1 : cyclicGaloisAlgebra K L b))
      (cyclicTensorCentralizerGenerator K L a b) := by
  rw [cyclicTensorCentralizerGenerator]
  exact (cyclicTensorDiagonalCoefficient_commute_centralizerCoefficient K L a b x
    (cyclicTensorCentralizerTwist K L b)).mul_right
      (cyclicTensorDiagonalCoefficient_commute_rightGenerator K L a b x)

theorem cyclicTensorDiagonalGenerator_commute_twistedRightGenerator
    (a b : K) :
    Commute (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b)
      (cyclicTensorCentralizerGenerator K L a b) := by
  rw [cyclicTensorCentralizerGenerator]
  exact (cyclicTensorDiagonalGenerator_commute_centralizerCoefficient K L a b
    (cyclicTensorCentralizerTwist K L b)).mul_right
      (cyclicTensorDiagonalGenerator_commute_rightGenerator K L a b)

theorem cyclicTensorDiagonalCoefficient_commute_unitAction
    (a b : K) (hb : b ≠ 0) (x : L) (σ : Gal(L/K)) :
    Commute (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
      (1 : cyclicGaloisAlgebra K L b))
      (cyclicTensorCentralizerUnitAction K L a b hb σ :
        cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := by
  let i := (cyclicGaloisGeneratorFinEquiv K L).symm σ
  have hσ : cyclicGaloisGenerator K L ^ (i : ℕ) = σ :=
    (cyclicGaloisGeneratorFinEquiv K L).apply_symm_apply σ
  rw [← hσ, cyclicTensorCentralizerUnitAction_pow_coe]
  exact (cyclicTensorDiagonalCoefficient_commute_twistedRightGenerator K L a b x).pow_right _

theorem cyclicTensorDiagonalGenerator_commute_unitAction
    (a b : K) (hb : b ≠ 0) (σ : Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b)
      (cyclicTensorCentralizerUnitAction K L a b hb σ :
        cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := by
  let i := (cyclicGaloisGeneratorFinEquiv K L).symm σ
  have hσ : cyclicGaloisGenerator K L ^ (i : ℕ) = σ :=
    (cyclicGaloisGeneratorFinEquiv K L).apply_symm_apply σ
  rw [← hσ, cyclicTensorCentralizerUnitAction_pow_coe]
  exact (cyclicTensorDiagonalGenerator_commute_twistedRightGenerator K L a b).pow_right _

theorem cyclicTensorDiagonalCoefficient_commute_centralizerSkew
    (a b : K) (hb : b ≠ 0) (x : L)
    (F : SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :
    Commute (cyclicGaloisAlgebraC K L a x ⊗ₜ[K]
      (1 : cyclicGaloisAlgebra K L b))
      (cyclicTensorCentralizerSkewAlgHom K L a b hb F) := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add F H hF hH =>
      rw [map_add]
      exact hF.add_right hH
  | single σ f =>
      rw [cyclicTensorCentralizerSkewAlgHom_single]
      exact (cyclicTensorDiagonalCoefficient_commute_centralizerCoefficient K L a b x f).mul_right
        (cyclicTensorDiagonalCoefficient_commute_unitAction K L a b hb x σ)

theorem cyclicTensorDiagonalGenerator_commute_centralizerSkew
    (a b : K) (hb : b ≠ 0)
    (F : SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTensorDiagonalGenerator K L a b)
      (cyclicTensorCentralizerSkewAlgHom K L a b hb F) := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add F H hF hH =>
      rw [map_add]
      exact hF.add_right hH
  | single σ f =>
      rw [cyclicTensorCentralizerSkewAlgHom_single]
      exact (cyclicTensorDiagonalGenerator_commute_centralizerCoefficient K L a b f).mul_right
        (cyclicTensorDiagonalGenerator_commute_unitAction K L a b hb σ)

theorem cyclicTensorDiagonalAlgHom_commute_centralizerSkew
    (a b : K) (hb : b ≠ 0) (x : cyclicGaloisAlgebra K L (a * b))
    (F : SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :
    Commute (cyclicGaloisAlgebraTensorDiagonalAlgHom K L a b x)
      (cyclicTensorCentralizerSkewAlgHom K L a b hb F) := by
  classical
  obtain ⟨v, rfl⟩ :=
    cyclicGaloisAlgebraNormalFormLinearMap_surjective K L (a * b) x
  rw [cyclicGaloisAlgebraNormalFormLinearMap_apply, map_sum]
  apply Finset.sum_induction
    (fun i : Fin (Module.finrank K L) =>
      cyclicGaloisAlgebraTensorDiagonalAlgHom K L a b
        (cyclicGaloisAlgebraC K L (a * b) (v i) *
          cyclicGaloisAlgebraX K L (a * b) ^ (i : ℕ)))
    (fun z => Commute z (cyclicTensorCentralizerSkewAlgHom K L a b hb F))
  · intro u w hu hw
    exact hu.add_left hw
  · simp
  · intro i _
    rw [map_mul, map_pow]
    change Commute
      (cyclicGaloisAlgebraTensorDiagonalRingHom K L a b
          (cyclicGaloisAlgebraC K L (a * b) (v i)) *
        cyclicGaloisAlgebraTensorDiagonalRingHom K L a b
            (cyclicGaloisAlgebraX K L (a * b)) ^ (i : ℕ))
      (cyclicTensorCentralizerSkewAlgHom K L a b hb F)
    rw [cyclicGaloisAlgebraTensorDiagonalRingHom_C,
      cyclicGaloisAlgebraTensorDiagonalRingHom_X]
    exact (cyclicTensorDiagonalCoefficient_commute_centralizerSkew K L a b hb (v i) F).mul_left
      ((cyclicTensorDiagonalGenerator_commute_centralizerSkew K L a b hb F).pow_left (i : ℕ))

theorem transformationSkew_finrank_eq_card_sq
    (F G : Type) [Field F] [Group G] [Fintype G] [DecidableEq G] :
    Module.finrank F
        (SkewMonoidAlgebra (TransformationFunctions F G) G) =
      Fintype.card G ^ 2 := by
  calc
    Module.finrank F
        (SkewMonoidAlgebra (TransformationFunctions F G) G) =
      Module.finrank F (Module.End F (TransformationFunctions F G)) :=
        (transformationSkewAlgEquiv F G).toLinearEquiv.finrank_eq
    _ = Module.finrank F (TransformationFunctions F G) ^ 2 := by
      rw [Module.finrank_linearMap, pow_two]
    _ = Fintype.card G ^ 2 := by
      congr 1
      rw [Module.finrank_pi_fintype]
      simp

noncomputable def transformationSkewCSA
    (F G : Type) [Field F] [Group G] [Fintype G] [DecidableEq G] : CSA F where
  carrier := SkewMonoidAlgebra (TransformationFunctions F G) G
  isCentral := by
    exact Algebra.IsCentral.of_algEquiv F _ _ (transformationSkewAlgEquiv F G).symm
  isSimple := isSimpleRing_transformationSkew F G
  fin_dim := by
    exact FiniteDimensional.of_injective
      (transformationSkewAlgEquiv F G).toLinearMap
      (transformationSkewAlgEquiv F G).injective

noncomputable def cyclicTensorDiagonalCentralizerProductAlgHom
    (a b : K) (hb : b ≠ 0) :
    (cyclicGaloisAlgebra K L (a * b) ⊗[K]
      SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) →ₐ[K]
        (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  Algebra.TensorProduct.lift
    (cyclicGaloisAlgebraTensorDiagonalAlgHom K L a b)
    (cyclicTensorCentralizerSkewAlgHom K L a b hb)
    (cyclicTensorDiagonalAlgHom_commute_centralizerSkew K L a b hb)

theorem cyclicTensorDiagonalCentralizerProductAlgHom_injective
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb) := by
  classical
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  letI : Nontrivial (cyclicGaloisAlgebra K L b) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L b).symm⟩
  letI : Nontrivial
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := inferInstance
  letI : IsSimpleRing
      (cyclicGaloisAlgebra K L (a * b) ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    tensorProduct_isSimpleRing (cyclicGaloisAlgebraCSA K L (a * b) hab)
      (transformationSkewCSA K Gal(L/K))
  let sourceRing : NonAssocRing
      (cyclicGaloisAlgebra K L (a * b) ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) := inferInstance
  letI : NonAssocSemiring
      (cyclicGaloisAlgebra K L (a * b) ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    sourceRing.toNonAssocSemiring
  let f :
      (cyclicGaloisAlgebra K L (a * b) ⊗[K]
        SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) →+*
      (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
    { toFun := cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb
      map_one' := (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb).map_one
      map_mul' := (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb).map_mul
      map_zero' := (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb).map_zero
      map_add' := (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb).map_add }
  change Function.Injective f
  exact RingHom.injective f

theorem cyclicTensorDiagonalCentralizerProduct_finrank_eq
    (a b : K) :
    Module.finrank K
        (cyclicGaloisAlgebra K L (a * b) ⊗[K]
          SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) =
      Module.finrank K
        (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) := by
  classical
  have hcard : Fintype.card Gal(L/K) = Module.finrank K L := by
    simpa using (Fintype.card_congr (cyclicGaloisGeneratorFinEquiv K L)).symm
  calc
    Module.finrank K
        (cyclicGaloisAlgebra K L (a * b) ⊗[K]
          SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) =
      Module.finrank K (cyclicGaloisAlgebra K L (a * b)) *
        Module.finrank K
          (SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
        Module.finrank_tensorProduct
    _ = Module.finrank K L ^ 2 * Fintype.card Gal(L/K) ^ 2 := by
      rw [cyclicGaloisAlgebra_finrank_eq_square,
        transformationSkew_finrank_eq_card_sq]
    _ = Module.finrank K L ^ 2 * Module.finrank K L ^ 2 := by rw [hcard]
    _ = Module.finrank K (cyclicGaloisAlgebra K L a) *
        Module.finrank K (cyclicGaloisAlgebra K L b) := by
      rw [cyclicGaloisAlgebra_finrank_eq_square,
        cyclicGaloisAlgebra_finrank_eq_square]
    _ = Module.finrank K
        (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
      Module.finrank_tensorProduct.symm

theorem cyclicTensorDiagonalCentralizerProductAlgHom_surjective
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Surjective (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb) := by
  classical
  letI : FiniteDimensional K
      (SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) :=
    (transformationSkewCSA K Gal(L/K)).fin_dim
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (cyclicTensorDiagonalCentralizerProduct_finrank_eq K L a b)).mp
  exact cyclicTensorDiagonalCentralizerProductAlgHom_injective K L a b ha hb

noncomputable def cyclicTensorDiagonalCentralizerProductAlgEquiv
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (cyclicGaloisAlgebra K L (a * b) ⊗[K]
      SkewMonoidAlgebra (TransformationFunctions K Gal(L/K)) Gal(L/K)) ≃ₐ[K]
        (cyclicGaloisAlgebra K L a ⊗[K] cyclicGaloisAlgebra K L b) :=
  AlgEquiv.ofBijective (cyclicTensorDiagonalCentralizerProductAlgHom K L a b hb)
    ⟨cyclicTensorDiagonalCentralizerProductAlgHom_injective K L a b ha hb,
      cyclicTensorDiagonalCentralizerProductAlgHom_surjective K L a b ha hb⟩

noncomputable def transformationSkewMatrixAlgEquiv
    (F G : Type) [Field F] [Group G] [Fintype G] [DecidableEq G] :
    SkewMonoidAlgebra (TransformationFunctions F G) G ≃ₐ[F]
      Matrix (Fin (Module.finrank F (TransformationFunctions F G)))
        (Fin (Module.finrank F (TransformationFunctions F G))) F :=
  (transformationSkewAlgEquiv F G).trans
    (LinearMap.toMatrixAlgEquiv
      (Module.finBasis F (TransformationFunctions F G)))

theorem transformationSkew_brauerClass_eq_split
    (F G : Type) [Field F] [Group G] [Fintype G] [DecidableEq G] :
    brauerClass (transformationSkewCSA F G) = brauerSplitClass F := by
  letI : NeZero (Module.finrank F (TransformationFunctions F G)) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := F)
      (M := TransformationFunctions F G))⟩
  calc
    brauerClass (transformationSkewCSA F G) =
        brauerClass (matrixFinCSA (scalarCSA F)
          (Module.finrank F (TransformationFunctions F G))) :=
      brauerClass_eq_of_algEquiv _ _ (transformationSkewMatrixAlgEquiv F G)
    _ = brauerSplitClass F := brauerClass_matrixFinCSA_scalar_eq _

theorem cyclicGaloisAlgebra_brauerTensorAdd
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    brauerTensorAdd K
        (brauerClass (cyclicGaloisAlgebraCSA K L a ha))
        (brauerClass (cyclicGaloisAlgebraCSA K L b hb)) =
      brauerClass (cyclicGaloisAlgebraCSA K L (a * b) (mul_ne_zero ha hb)) := by
  classical
  calc
    brauerTensorAdd K
        (brauerClass (cyclicGaloisAlgebraCSA K L a ha))
        (brauerClass (cyclicGaloisAlgebraCSA K L b hb)) =
      brauerClass (tensorProductCSA
        (cyclicGaloisAlgebraCSA K L a ha)
        (cyclicGaloisAlgebraCSA K L b hb)) :=
      brauerTensorAdd_brauerClass K _ _
    _ = brauerClass (tensorProductCSA
        (cyclicGaloisAlgebraCSA K L (a * b) (mul_ne_zero ha hb))
        (transformationSkewCSA K Gal(L/K))) :=
      (brauerClass_eq_of_algEquiv _ _
        (cyclicTensorDiagonalCentralizerProductAlgEquiv K L a b ha hb)).symm
    _ = brauerTensorAdd K
        (brauerClass (cyclicGaloisAlgebraCSA K L (a * b) (mul_ne_zero ha hb)))
        (brauerClass (transformationSkewCSA K Gal(L/K))) := rfl
    _ = brauerTensorAdd K
        (brauerClass (cyclicGaloisAlgebraCSA K L (a * b) (mul_ne_zero ha hb)))
        (brauerSplitClass K) := by
      rw [transformationSkew_brauerClass_eq_split]
    _ = brauerClass
        (cyclicGaloisAlgebraCSA K L (a * b) (mul_ne_zero ha hb)) :=
      brauerTensorAdd_split_right K _

theorem cyclicGaloisAlgebra_brauerClass_add
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    brauerClass (cyclicGaloisAlgebraCSA K L a ha) +
        brauerClass (cyclicGaloisAlgebraCSA K L b hb) =
      brauerClass (cyclicGaloisAlgebraCSA K L (a * b) (mul_ne_zero ha hb)) := by
  exact cyclicGaloisAlgebra_brauerTensorAdd K L a b ha hb

end GaloisForLFunctions.HTGeometry.ABHN
