/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebraCompanionMatrix
import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebraLiftGenerator
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraIdealReduction
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2Split
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCohomology
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisCohomology
import GaloisForLFunctions.HTGeometry.ABHN.HasseCentralSimple
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionFunctoriality

/-!
# All-degree cyclic companion coefficient actions

For a cyclic automorphism of order `n + 1`, this file constructs its diagonal action on the
weighted companion matrix module.  The generator commutation relation is proved directly, and
the generator criterion upgrades it to every skew exponent.  This is the universal-property part
of the all-degree cyclic-algebra splitting representation.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative
open scoped TensorProduct

variable {L : Type*} [Field L]

/-- The relative Brauer kernel of a field extension, formed from the already formalized
additive scalar-extension map. -/
noncomputable def scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L] :
    AddSubgroup (BrauerGroup K) :=
  (scalarExtensionBrauerAddHom K L).ker

/-- Membership in the relative Brauer kernel is exactly splitting after scalar extension. -/
theorem mem_scalarExtensionBrauerKernel_iff
    (K L : Type) [Field K] [Field L] [Algebra K L] (x : BrauerGroup K) :
    x ∈ scalarExtensionBrauerKernel K L ↔
      scalarExtensionBrauerMap K L x = brauerSplitClass L := by
  rfl

/-- The coefficient action for the weighted cyclic companion representation: the `i`th diagonal
entry applies the inverse `i`th power of the cyclic automorphism. -/
noncomputable def cyclicCompanionCoefficientMatrixHom
    (σ : L ≃+* L) (n : ℕ) :
    L →+* Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  (Matrix.diagonalRingHom (Fin (n + 1)) L).comp
    (RingHom.pi fun i ↦ (σ.symm ^ (i : ℕ)).toRingHom)

/-- Entrywise formula for the all-degree cyclic companion coefficient action. -/
theorem cyclicCompanionCoefficientMatrixHom_apply
    (σ : L ≃+* L) (n : ℕ) (b : L) (i j : Fin (n + 1)) :
    cyclicCompanionCoefficientMatrixHom σ n b i j =
      if i = j then (σ.symm ^ (i : ℕ)) b else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [cyclicCompanionCoefficientMatrixHom]
  · rw [cyclicCompanionCoefficientMatrixHom]
    simp [hij]

/-- The diagonal coefficient action and weighted companion matrix satisfy the cyclic generator
commutation relation. -/
theorem cyclicCompanionCoefficientMatrix_actions_commute_one
    (σ : L ≃+* L) (n : ℕ) (a b : L) (horder : σ ^ (n + 1) = 1) :
    cyclicCompanionCoefficientMatrixHom σ n (σ b) * cyclicCompanionMatrix n a =
      cyclicCompanionMatrix n a * cyclicCompanionCoefficientMatrixHom σ n b := by
  classical
  change Matrix.diagonal (fun i : Fin (n + 1) ↦ (σ.symm ^ (i : ℕ)) (σ b)) *
      cyclicCompanionMatrix n a =
    cyclicCompanionMatrix n a *
      Matrix.diagonal (fun i : Fin (n + 1) ↦ (σ.symm ^ (i : ℕ)) b)
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext i
  rw [Matrix.mulVec_diagonal, cyclicCompanionMatrix_mulVec,
    cyclicCompanionMatrix_mulVec]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [Matrix.mulVec_diagonal]
    have hpower : σ.symm ^ n = σ := by
      calc
        σ.symm ^ n = (σ ^ n)⁻¹ := inv_pow σ n
        _ = σ := inv_eq_iff_mul_eq_one.mpr (by simpa [pow_succ] using horder)
    simp only [Fin.cons_zero, Fin.val_zero, pow_zero, Fin.val_last]
    rw [show (σ.symm ^ n) b = σ b by rw [hpower]]
    ac_rfl
  · rw [Matrix.mulVec_diagonal]
    simp only [Fin.cons_succ]
    rw [Matrix.mulVec_diagonal]
    simp [pow_succ]

/-- The generator commutation identity supplies the full family of skew-commutation equations
for the cyclic companion coefficient action. -/
theorem cyclicCompanionCoefficientMatrix_actions_commute
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1)
    (m : Multiplicative ℕ) (b : L) :
    cyclicCompanionCoefficientMatrixHom σ n ((cyclicPowerRingAut σ m) b) *
        cyclicPowerMonoidHom (cyclicCompanionMatrix n a) m =
      cyclicPowerMonoidHom (cyclicCompanionMatrix n a) m *
        cyclicCompanionCoefficientMatrixHom σ n b :=
  cyclicAlgebraLift_comm_of_generator σ (cyclicCompanionCoefficientMatrixHom σ n)
    (cyclicCompanionMatrix n a)
    (fun b ↦ cyclicCompanionCoefficientMatrix_actions_commute_one σ n a b horder) m b

/-- The `j`th standard basis vector is the image of the zeroth one under the `j`th companion
power. -/
theorem cyclicCompanionMatrix_pow_mulVec_single_zero
    (n : ℕ) (a x : L) (j : Fin (n + 1)) :
    Matrix.mulVec (cyclicCompanionMatrix n a ^ (j : ℕ)) (Pi.single 0 x) = Pi.single j x := by
  refine Fin.induction ?_ ?_ j
  · ext k
    simp [Matrix.mulVec, Matrix.one_apply, Pi.single_apply]
  · intro i ih
    have ih' : Matrix.mulVec (cyclicCompanionMatrix n a ^ (i : ℕ)) (Pi.single 0 x) =
        Pi.single i.castSucc x := by
      simpa using ih
    rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec, ih']
    exact cyclicCompanionMatrix_mulVec_single_castSucc n a x i

/-- One full weighted companion cycle sends the zeroth basis vector to its `a`-multiple. -/
theorem cyclicCompanionMatrix_pow_succ_mulVec_single_zero
    (n : ℕ) (a x : L) :
    Matrix.mulVec (cyclicCompanionMatrix n a ^ (n + 1)) (Pi.single 0 x) =
      Pi.single 0 (a * x) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec,
    show Matrix.mulVec (cyclicCompanionMatrix n a ^ n) (Pi.single 0 x) =
      Pi.single (Fin.last n) x by
        simpa using cyclicCompanionMatrix_pow_mulVec_single_zero n a x (Fin.last n)]
  exact cyclicCompanionMatrix_mulVec_single_last n a x

/-- One full weighted companion cycle multiplies every standard basis vector by `a`. -/
theorem cyclicCompanionMatrix_pow_succ_mulVec_single
    (n : ℕ) (a x : L) (j : Fin (n + 1)) :
    Matrix.mulVec (cyclicCompanionMatrix n a ^ (n + 1)) (Pi.single j x) =
      Pi.single j (a * x) := by
  rw [← cyclicCompanionMatrix_pow_mulVec_single_zero n a x j]
  calc
    Matrix.mulVec (cyclicCompanionMatrix n a ^ (n + 1))
        (Matrix.mulVec (cyclicCompanionMatrix n a ^ (j : ℕ)) (Pi.single 0 x)) =
        Matrix.mulVec (cyclicCompanionMatrix n a ^ (n + 1) *
          cyclicCompanionMatrix n a ^ (j : ℕ)) (Pi.single 0 x) :=
      Matrix.mulVec_mulVec (Pi.single 0 x) _ _
    _ = Matrix.mulVec (cyclicCompanionMatrix n a ^ (j : ℕ) *
        cyclicCompanionMatrix n a ^ (n + 1)) (Pi.single 0 x) := by
      rw [((Commute.refl (cyclicCompanionMatrix n a)).pow_pow (n + 1) (j : ℕ)).eq]
    _ = Matrix.mulVec (cyclicCompanionMatrix n a ^ (j : ℕ))
        (Matrix.mulVec (cyclicCompanionMatrix n a ^ (n + 1)) (Pi.single 0 x)) :=
      (Matrix.mulVec_mulVec (Pi.single 0 x) _ _).symm
    _ = Pi.single j (a * x) := by
      rw [cyclicCompanionMatrix_pow_succ_mulVec_single_zero,
        cyclicCompanionMatrix_pow_mulVec_single_zero]

/-- The weighted companion matrix satisfies its defining cyclic-algebra relation. -/
theorem cyclicCompanionMatrix_pow_succ
    (n : ℕ) (a : L) :
    cyclicCompanionMatrix n a ^ (n + 1) = a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
  ext i j
  have h := congrFun (cyclicCompanionMatrix_pow_succ_mulVec_single n a 1 j) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h

/-- A coefficient fixed by the cyclic automorphism acts as the corresponding scalar matrix. -/
theorem cyclicCompanionCoefficientMatrixHom_eq_scalar
    (σ : L ≃+* L) (n : ℕ) (a : L) (hfixed : σ a = a) :
    cyclicCompanionCoefficientMatrixHom σ n a =
      a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
  have hfixed_symm : σ.symm a = a := by
    apply σ.injective
    rw [σ.apply_symm_apply, hfixed]
  have hpow : ∀ m : ℕ, (σ.symm ^ m) a = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      change (σ.symm ^ m) (σ.symm a) = a
      rw [hfixed_symm, ih]
  ext i j
  rw [cyclicCompanionCoefficientMatrixHom_apply]
  by_cases hij : i = j
  · subst j
    simp [hpow]
  · simp [hij]

/-- The all-degree weighted companion representation of a cyclic algebra with a fixed parameter.
It realizes both the full skew-commutation family and the defining power relation. -/
noncomputable def cyclicCompanionRepresentation
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    CyclicAlgebra σ (n + 1) a →+* Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  cyclicAlgebraLift σ (n + 1) a (cyclicCompanionCoefficientMatrixHom σ n)
    (cyclicCompanionMatrix n a)
    (cyclicCompanionCoefficientMatrix_actions_commute σ n a horder) (by
      rw [cyclicCompanionMatrix_pow_succ,
        cyclicCompanionCoefficientMatrixHom_eq_scalar σ n a hfixed])

/-- The cyclic companion representation sends coefficients to their Galois-diagonal matrices. -/
theorem cyclicCompanionRepresentation_C
    (σ : L ≃+* L) (n : ℕ) (a b : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    cyclicCompanionRepresentation σ n a horder hfixed (cyclicAlgebraC σ (n + 1) a b) =
      cyclicCompanionCoefficientMatrixHom σ n b :=
  cyclicAlgebraLift_C σ (n + 1) a (cyclicCompanionCoefficientMatrixHom σ n)
    (cyclicCompanionMatrix n a)
    (cyclicCompanionCoefficientMatrix_actions_commute σ n a horder) _ b

/-- The cyclic companion representation sends the cyclic generator to the weighted companion
matrix. -/
theorem cyclicCompanionRepresentation_X
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    cyclicCompanionRepresentation σ n a horder hfixed (cyclicAlgebraX σ (n + 1) a) =
      cyclicCompanionMatrix n a :=
  cyclicAlgebraLift_X σ (n + 1) a (cyclicCompanionCoefficientMatrixHom σ n)
    (cyclicCompanionMatrix n a)
    (cyclicCompanionCoefficientMatrix_actions_commute σ n a horder) _

/-- Transport a raw cyclic algebra across an equality of its cyclic degrees.  Keeping this
transport explicit avoids dependent quotient casts in Galois-specialized representations. -/
noncomputable def cyclicAlgebraDegreeCast
    (σ : L ≃+* L) {d e : ℕ} (a : L) (h : d = e) :
    CyclicAlgebra σ d a →+* CyclicAlgebra σ e a := by
  subst e
  exact RingHom.id _

/-- Degree transport preserves embedded coefficient elements. -/
theorem cyclicAlgebraDegreeCast_C
    (σ : L ≃+* L) {d e : ℕ} (a : L) (h : d = e) (b : L) :
    cyclicAlgebraDegreeCast σ a h (cyclicAlgebraC σ d a b) = cyclicAlgebraC σ e a b := by
  subst e
  rfl

/-- Degree transport preserves the cyclic generator. -/
theorem cyclicAlgebraDegreeCast_X
    (σ : L ≃+* L) {d e : ℕ} (a : L) (h : d = e) :
    cyclicAlgebraDegreeCast σ a h (cyclicAlgebraX σ d a) = cyclicAlgebraX σ e a := by
  subst e
  rfl

/-- Every finite cyclic Galois algebra whose degree is `n + 1` has its canonical weighted
companion representation over the coefficient field. -/
noncomputable def cyclicGaloisAlgebraCompanionRepresentation
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) :
    cyclicGaloisAlgebra K L a →+* Matrix (Fin (n + 1)) (Fin (n + 1)) L := by
  let σ : L ≃+* L := (cyclicGaloisGenerator K L).toRingEquiv
  have horder : (cyclicGaloisGenerator K L).toRingEquiv ^ (n + 1) = 1 := by
    have h := congrArg (fun τ : Gal(L/K) ↦ τ.toRingEquiv)
      (cyclicGaloisGenerator_pow_finrank K L)
    ext x
    simpa [AlgEquiv.coe_pow, hdeg] using DFunLike.congr_fun h x
  exact (cyclicCompanionRepresentation σ n (algebraMap K L a) (by simpa [σ] using horder)
      ((cyclicGaloisGenerator K L).commutes a)).comp
    (cyclicAlgebraDegreeCast σ (algebraMap K L a) hdeg)

/-- The Galois companion representation respects the base-field scalar map. -/
theorem cyclicGaloisAlgebraCompanionRepresentation_algebraMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a c : K) :
    cyclicGaloisAlgebraCompanionRepresentation K L n hdeg a
      (algebraMap K (cyclicGaloisAlgebra K L a) c) =
        c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
  rw [cyclicGaloisAlgebra_algebraMap_apply]
  unfold cyclicGaloisAlgebraCompanionRepresentation
  dsimp
  rw [cyclicAlgebraDegreeCast_C, cyclicCompanionRepresentation_C]
  calc
    cyclicCompanionCoefficientMatrixHom (cyclicGaloisGenerator K L).toRingEquiv n
        (algebraMap K L c) =
        algebraMap K (Matrix (Fin (n + 1)) (Fin (n + 1)) L) c := by
      rw [IsScalarTower.algebraMap_apply K L
        (Matrix (Fin (n + 1)) (Fin (n + 1)) L)]
      simpa only [Algebra.algebraMap_eq_smul_one] using
        cyclicCompanionCoefficientMatrixHom_eq_scalar
          (cyclicGaloisGenerator K L).toRingEquiv n (algebraMap K L c)
          ((cyclicGaloisGenerator K L).commutes c)
    _ = c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
      rw [Algebra.algebraMap_eq_smul_one]

/-- The weighted companion representation is an algebra map over the base field. -/
noncomputable def cyclicGaloisAlgebraCompanionAlgHom
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) :
    cyclicGaloisAlgebra K L a →ₐ[K] Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  AlgHom.mk' (cyclicGaloisAlgebraCompanionRepresentation K L n hdeg a) (by
    intro c x
    rw [Algebra.smul_def, map_mul,
      cyclicGaloisAlgebraCompanionRepresentation_algebraMap]
    simp [Algebra.smul_def])

/-- Scalar extension of the Galois companion representation to its coefficient field. -/
noncomputable def cyclicGaloisAlgebraScalarExtensionCompanionRepresentation
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) :
    L ⊗[K] cyclicGaloisAlgebra K L a →ₐ[L] Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (cyclicGaloisAlgebraCompanionAlgHom K L n hdeg a)
    (fun l x ↦ by
      change algebraMap L (Matrix (Fin (n + 1)) (Fin (n + 1)) L) l * _ =
        _ * algebraMap L (Matrix (Fin (n + 1)) (Fin (n + 1)) L) l
      exact Algebra.commutes l _)

/-- Evaluation of the scalar-extended companion representation on pure tensors. -/
theorem cyclicGaloisAlgebraScalarExtensionCompanionRepresentation_tmul
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K)
    (l : L) (x : cyclicGaloisAlgebra K L a) :
    cyclicGaloisAlgebraScalarExtensionCompanionRepresentation K L n hdeg a (l ⊗ₜ[K] x) =
      (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L)) *
        cyclicGaloisAlgebraCompanionAlgHom K L n hdeg a x := by
  rw [cyclicGaloisAlgebraScalarExtensionCompanionRepresentation,
    Algebra.TensorProduct.lift_tmul]
  change algebraMap L (Matrix (Fin (n + 1)) (Fin (n + 1)) L) l *
      cyclicGaloisAlgebraCompanionAlgHom K L n hdeg a x =
    (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L)) *
      cyclicGaloisAlgebraCompanionAlgHom K L n hdeg a x
  exact congrArg (fun z : Matrix (Fin (n + 1)) (Fin (n + 1)) L ↦
    z * cyclicGaloisAlgebraCompanionAlgHom K L n hdeg a x)
    (Algebra.algebraMap_eq_smul_one l)

/-- The companion representation faithfully embeds the coefficient field in every raw cyclic
algebra satisfying the cyclic power relation. -/
theorem cyclicCompanionRepresentation_C_injective
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    Function.Injective (cyclicAlgebraC σ (n + 1) a) := by
  intro x y hxy
  have hmatrix := congrArg (cyclicCompanionRepresentation σ n a horder hfixed) hxy
  rw [cyclicCompanionRepresentation_C, cyclicCompanionRepresentation_C] at hmatrix
  have hentry := congrArg (fun M => M 0 0) hmatrix
  simpa [cyclicCompanionCoefficientMatrixHom_apply] using hentry

/-- Every raw cyclic algebra satisfying the cyclic power relation is nonzero. -/
theorem cyclicCompanionRepresentation_one_ne_zero
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    (1 : CyclicAlgebra σ (n + 1) a) ≠ 0 := by
  intro hzero
  have hmatrix := congrArg (cyclicCompanionRepresentation σ n a horder hfixed) hzero
  rw [map_one, map_zero] at hmatrix
  exact one_ne_zero hmatrix

/-- The bounded companion normal form: one coefficient for each exponent strictly below the
cyclic degree. -/
noncomputable def cyclicCompanionNormalForm
    (σ : L ≃+* L) (n : ℕ) (a : L) (f : Fin (n + 1) → L) :
    CyclicAlgebra σ (n + 1) a :=
  ∑ i, cyclicAlgebraC σ (n + 1) a (f i) * cyclicAlgebraX σ (n + 1) a ^ (i : ℕ)

/-- Degree-indexed bounded cyclic normal form.  Unlike the successor-indexed companion
notation, this presentation can be used directly at a finite extension degree. -/
noncomputable def cyclicCompanionNormalFormDegree
    (σ : L ≃+* L) (d : ℕ) (a : L) (f : Fin d → L) : CyclicAlgebra σ d a :=
  ∑ i, cyclicAlgebraC σ d a (f i) * cyclicAlgebraX σ d a ^ (i : ℕ)

/-- The degree-indexed normal form agrees definitionally with companion normal form at a
successor degree. -/
theorem cyclicCompanionNormalFormDegree_succ
    (σ : L ≃+* L) (n : ℕ) (a : L) (f : Fin (n + 1) → L) :
    cyclicCompanionNormalFormDegree σ (n + 1) a f = cyclicCompanionNormalForm σ n a f := rfl

/-- Evaluating the companion image of a bounded normal form on the zeroth basis vector recovers
every coefficient, after the invertible diagonal Galois twist. -/
theorem cyclicCompanionRepresentation_normalForm_mulVec_single_zero
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a)
    (f : Fin (n + 1) → L) :
    Matrix.mulVec
      (cyclicCompanionRepresentation σ n a horder hfixed
        (cyclicCompanionNormalForm σ n a f))
      (Pi.single 0 1) =
        fun i : Fin (n + 1) => (σ.symm ^ (i : ℕ)) (f i) := by
  ext j
  rw [cyclicCompanionNormalForm, map_sum]
  rw [Matrix.sum_mulVec]
  rw [Finset.sum_apply]
  simp_rw [map_mul, map_pow, cyclicCompanionRepresentation_C,
    cyclicCompanionRepresentation_X]
  calc
    ∑ i : Fin (n + 1), ((cyclicCompanionCoefficientMatrixHom σ n) (f i) *
      cyclicCompanionMatrix n a ^ (i : ℕ)).mulVec (Pi.single 0 1) j =
        ∑ i : Fin (n + 1), ((cyclicCompanionCoefficientMatrixHom σ n) (f i)).mulVec
          ((cyclicCompanionMatrix n a ^ (i : ℕ)).mulVec (Pi.single 0 1)) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mulVec_mulVec]
    _ = ∑ i : Fin (n + 1), (Pi.single i ((σ.symm ^ (i : ℕ)) (f i))) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [cyclicCompanionMatrix_pow_mulVec_single_zero]
      change (Matrix.diagonal (fun k : Fin (n + 1) ↦
        (σ.symm ^ (k : ℕ)) (f i))).mulVec (Pi.single i 1) j = _
      rw [Matrix.mulVec_diagonal]
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij]
    _ = (σ.symm ^ (j : ℕ)) (f j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · simp

/-- The companion representation separates all bounded cyclic normal forms. -/
theorem cyclicCompanionRepresentation_normalForm_injective
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    Function.Injective (cyclicCompanionNormalForm σ n a) := by
  intro f g hfg
  have himage := congrArg (fun x ↦
    Matrix.mulVec (cyclicCompanionRepresentation σ n a horder hfixed x) (Pi.single 0 1)) hfg
  rw [cyclicCompanionRepresentation_normalForm_mulVec_single_zero,
    cyclicCompanionRepresentation_normalForm_mulVec_single_zero] at himage
  funext i
  exact (σ.symm ^ (i : ℕ)).injective (congrFun himage i)

/-- The zero coefficient vector gives the zero companion normal form. -/
theorem cyclicCompanionNormalForm_zero
    (σ : L ≃+* L) (n : ℕ) (a : L) :
    cyclicCompanionNormalForm σ n a 0 = 0 := by
  classical
  unfold cyclicCompanionNormalForm
  apply Finset.sum_eq_zero
  intro i _
  change cyclicAlgebraC σ (n + 1) a 0 * _ = 0
  rw [← cyclicAlgebraCRingHom_apply, map_zero, zero_mul]

/-- Companion normal form is additive in its coefficient vector. -/
theorem cyclicCompanionNormalForm_add
    (σ : L ≃+* L) (n : ℕ) (a : L) (f g : Fin (n + 1) → L) :
    cyclicCompanionNormalForm σ n a (f + g) =
      cyclicCompanionNormalForm σ n a f + cyclicCompanionNormalForm σ n a g := by
  classical
  unfold cyclicCompanionNormalForm
  simp only [Pi.add_apply]
  simp_rw [← cyclicAlgebraCRingHom_apply L σ (n + 1) a, map_add,
    cyclicAlgebraCRingHom_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

/-- A one-coordinate coefficient vector is its corresponding cyclic normal-form monomial. -/
theorem cyclicCompanionNormalForm_single
    (σ : L ≃+* L) (n : ℕ) (a c : L) (i : Fin (n + 1)) :
    cyclicCompanionNormalForm σ n a (Pi.single i c) =
      cyclicAlgebraC σ (n + 1) a c * cyclicAlgebraX σ (n + 1) a ^ (i : ℕ) := by
  classical
  unfold cyclicCompanionNormalForm
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    change cyclicAlgebraC σ (n + 1) a 0 * _ = 0
    rw [← cyclicAlgebraCRingHom_apply, map_zero, zero_mul]
  · simp

/-- Every raw cyclic-algebra quotient element has a bounded companion normal form. -/
theorem cyclicCompanionNormalForm_surjective
    (σ : L ≃+* L) (n : ℕ) (a : L) :
    Function.Surjective (cyclicCompanionNormalForm σ n a) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using SkewMonoidAlgebra.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      simpa using (cyclicCompanionNormalForm_zero σ n a)
  | add p q hp hq =>
      obtain ⟨fp, hfp⟩ := hp
      obtain ⟨fq, hfq⟩ := hq
      refine ⟨fp + fq, ?_⟩
      rw [cyclicCompanionNormalForm_add, hfp, hfq, map_add]
  | single g c =>
      let i : Fin (n + 1) :=
        ⟨toAdd g % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
      refine ⟨Pi.single i (c * a ^ (toAdd g / (n + 1))), ?_⟩
      rw [cyclicCompanionNormalForm_single]
      change cyclicAlgebraC σ (n + 1) a (c * a ^ (toAdd g / (n + 1))) *
          cyclicAlgebraX σ (n + 1) a ^ (toAdd g % (n + 1)) =
        (Ideal.Quotient.mk (cyclicRelationIdeal σ (n + 1) a)
          (SkewPolynomial.monomial (toAdd g) c) : CyclicAlgebra σ (n + 1) a)
      exact (cyclicAlgebraMonomial_mod_normalForm σ (n + 1) a c (toAdd g)).symm

/-- The additive map sending a coefficient vector to its bounded cyclic normal form. -/
noncomputable def cyclicCompanionNormalFormAddHom
    (σ : L ≃+* L) (n : ℕ) (a : L) :
    (Fin (n + 1) → L) →+ CyclicAlgebra σ (n + 1) a where
  toFun := cyclicCompanionNormalForm σ n a
  map_zero' := cyclicCompanionNormalForm_zero σ n a
  map_add' := cyclicCompanionNormalForm_add σ n a

/-- Bounded coefficient vectors are additive coordinates on every compatible raw cyclic
algebra. -/
noncomputable def cyclicCompanionNormalFormAddEquiv
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    (Fin (n + 1) → L) ≃+ CyclicAlgebra σ (n + 1) a :=
  AddEquiv.ofBijective (cyclicCompanionNormalFormAddHom σ n a)
    ⟨cyclicCompanionRepresentation_normalForm_injective σ n a horder hfixed,
      cyclicCompanionNormalForm_surjective σ n a⟩

/-- The normal-form additive equivalence evaluates to the stated bounded normal form. -/
theorem cyclicCompanionNormalFormAddEquiv_apply
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a)
    (f : Fin (n + 1) → L) :
    cyclicCompanionNormalFormAddEquiv σ n a horder hfixed f =
      cyclicCompanionNormalForm σ n a f := rfl

/-- Bounded cyclic normal forms span every raw cyclic algebra at every positive degree. -/
theorem cyclicCompanionNormalFormDegree_surjective
    (σ : L ≃+* L) (d : ℕ) (hd : d ≠ 0) (a : L) :
    Function.Surjective (cyclicCompanionNormalFormDegree σ d a) := by
  cases d with
  | zero => exact (hd rfl).elim
  | succ n =>
      exact cyclicCompanionNormalForm_surjective σ n a

/-- Under the cyclic relation, degree-indexed normal forms are unique at every positive
degree. -/
theorem cyclicCompanionNormalFormDegree_injective
    (σ : L ≃+* L) (d : ℕ) (hd : d ≠ 0) (a : L) (horder : σ ^ d = 1)
    (hfixed : σ a = a) :
    Function.Injective (cyclicCompanionNormalFormDegree σ d a) := by
  cases d with
  | zero => exact (hd rfl).elim
  | succ n =>
      exact cyclicCompanionRepresentation_normalForm_injective σ n a horder hfixed

/-- The companion image separates bounded normal forms, not merely their quotient classes. -/
theorem cyclicCompanionRepresentation_normalFormImage_injective
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    Function.Injective (fun f : Fin (n + 1) → L ↦
      cyclicCompanionRepresentation σ n a horder hfixed
        (cyclicCompanionNormalForm σ n a f)) := by
  intro f g hfg
  have himage := congrArg (fun M ↦ Matrix.mulVec M (Pi.single 0 1)) hfg
  rw [cyclicCompanionRepresentation_normalForm_mulVec_single_zero,
    cyclicCompanionRepresentation_normalForm_mulVec_single_zero] at himage
  funext i
  exact (σ.symm ^ (i : ℕ)).injective (congrFun himage i)

/-- **Faithful all-degree cyclic companion representation.** Every compatible raw cyclic
algebra embeds into its weighted companion matrix algebra. -/
theorem cyclicCompanionRepresentation_injective
    (σ : L ≃+* L) (n : ℕ) (a : L) (horder : σ ^ (n + 1) = 1) (hfixed : σ a = a) :
    Function.Injective (cyclicCompanionRepresentation σ n a horder hfixed) := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := cyclicCompanionNormalForm_surjective σ n a x
  obtain ⟨g, rfl⟩ := cyclicCompanionNormalForm_surjective σ n a y
  exact congrArg (cyclicCompanionNormalForm σ n a)
    (cyclicCompanionRepresentation_normalFormImage_injective σ n a horder hfixed hxy)

/-- The pre-existing bounded Galois normal-form map is its explicit sum of coefficient
monomials.  This makes the support-reduction API compatible with faithful companion
coordinates. -/
theorem cyclicGaloisAlgebraNormalFormLinearMap_apply
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] (a : K) (v : Fin (Module.finrank K L) → L) :
    cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      ∑ i, cyclicGaloisAlgebraC K L a (v i) * cyclicGaloisAlgebraX K L a ^ (i : ℕ) := by
  classical
  have hv : v = ∑ i : Fin (Module.finrank K L), Pi.single i (v i) := by
    funext i
    simp
  calc
    cyclicGaloisAlgebraNormalFormLinearMap K L a v =
        cyclicGaloisAlgebraNormalFormLinearMap K L a
          (∑ i : Fin (Module.finrank K L), Pi.single i (v i)) :=
      congrArg _ hv
    _ = ∑ i, cyclicGaloisAlgebraC K L a (v i) * cyclicGaloisAlgebraX K L a ^ (i : ℕ) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact cyclicGaloisAlgebraNormalFormLinearMap_single K L a i (v i)

/-- The bounded normal-form coordinates of a finite cyclic Galois algebra are unique.
The proof routes through the degree-indexed faithful companion normal form, so it does not
depend on an equality transport between unrelated `Fin` index types. -/
theorem cyclicGaloisAlgebraNormalFormLinearMap_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    Function.Injective (cyclicGaloisAlgebraNormalFormLinearMap K L a) := by
  let σ : L ≃+* L := (cyclicGaloisGenerator K L).toRingEquiv
  have hdegree : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have horder : σ ^ Module.finrank K L = 1 := by
    have h := congrArg (fun τ : Gal(L/K) ↦ τ.toRingEquiv)
      (cyclicGaloisGenerator_pow_finrank K L)
    ext x
    simpa [σ, AlgEquiv.coe_pow] using DFunLike.congr_fun h x
  have hfixed : σ (algebraMap K L a) = algebraMap K L a := by
    exact (cyclicGaloisGenerator K L).commutes a
  intro v w hvw
  apply cyclicCompanionNormalFormDegree_injective σ (Module.finrank K L) hdegree
    (algebraMap K L a) horder hfixed
  calc
    cyclicCompanionNormalFormDegree σ (Module.finrank K L) (algebraMap K L a) v =
        cyclicGaloisAlgebraNormalFormLinearMap K L a v := by
          exact (cyclicGaloisAlgebraNormalFormLinearMap_apply K L a v).symm
    _ = cyclicGaloisAlgebraNormalFormLinearMap K L a w := hvw
    _ = cyclicCompanionNormalFormDegree σ (Module.finrank K L) (algebraMap K L a) w := by
          exact cyclicGaloisAlgebraNormalFormLinearMap_apply K L a w

/-- Unique normal forms give a linear equivalence between a finite cyclic Galois algebra and
one coefficient-field copy for each cyclic exponent. -/
noncomputable def cyclicGaloisAlgebraNormalFormLinearEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    (Fin (Module.finrank K L) → L) ≃ₗ[K] cyclicGaloisAlgebra K L a :=
  LinearEquiv.ofBijective (cyclicGaloisAlgebraNormalFormLinearMap K L a)
    ⟨cyclicGaloisAlgebraNormalFormLinearMap_injective K L a,
      cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a⟩

/-- The cyclic Galois algebra has exactly the expected square dimension. -/
theorem cyclicGaloisAlgebra_finrank_eq_square
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    Module.finrank K (cyclicGaloisAlgebra K L a) = Module.finrank K L ^ 2 := by
  calc
    Module.finrank K (cyclicGaloisAlgebra K L a) =
        Module.finrank K (Fin (Module.finrank K L) → L) :=
      (cyclicGaloisAlgebraNormalFormLinearEquiv K L a).finrank_eq.symm
    _ = Module.finrank K L ^ 2 := by
      rw [Module.finrank_pi_fintype]
      simp [pow_two]

/-- Scalar extension to the defining cyclic Galois field has the square matrix dimension.
This is the dimension half of the all-degree splitting theorem; surjectivity onto the matrix
algebra remains its separate matrix-unit construction. -/
theorem cyclicGaloisAlgebra_scalarExtension_finrank_eq_matrix
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
      Module.finrank L (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) L) := by
  rw [Module.finrank_tensorProduct, cyclicGaloisAlgebra_finrank_eq_square,
    Module.finrank_matrix]
  simp [pow_two]

/-- Every finite cyclic Galois algebra has nonzero unit, independently of its parameter.
This follows from unique normal-form coordinates. -/
theorem cyclicGaloisAlgebra_one_ne_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    (1 : cyclicGaloisAlgebra K L a) ≠ 0 := by
  let i : Fin (Module.finrank K L) := ⟨0, Module.finrank_pos (R := K) (M := L)⟩
  intro hone
  have hnormal : cyclicGaloisAlgebraNormalFormLinearMap K L a (Pi.single i 1) =
      cyclicGaloisAlgebraNormalFormLinearMap K L a 0 := by
    rw [cyclicGaloisAlgebraNormalFormLinearMap_single, map_zero]
    change cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
        (algebraMap K L a) 1 * cyclicGaloisAlgebraX K L a ^ (i : ℕ) = 0
    rw [cyclicAlgebraC_one, one_mul]
    simpa [i] using hone
  have hcoeff := cyclicGaloisAlgebraNormalFormLinearMap_injective K L a hnormal
  have hentry := congrFun hcoeff i
  simp [i] at hentry

/-- A displayed nonzero normal-form coefficient certifies that its cyclic Galois algebra
element is nonzero. -/
theorem cyclicGaloisAlgebraNormalFormLinearMap_ne_zero_of_coefficient_ne_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (v : Fin (Module.finrank K L) → L) (i : Fin (Module.finrank K L))
    (hvi : v i ≠ 0) : cyclicGaloisAlgebraNormalFormLinearMap K L a v ≠ 0 := by
  intro hzero
  have hv : v = 0 := cyclicGaloisAlgebraNormalFormLinearMap_injective K L a (by
    simpa using hzero)
  exact hvi (congrFun hv i)

/-- **All-degree cyclic simplicity.** A cyclic Galois algebra with nonzero parameter is a
simple ring.  A nonzero two-sided ideal contains a normal form with minimum coefficient support;
a twisted commutator strictly shortens any support of size greater than one, while a one-term
normal form is a unit. -/
theorem isSimpleRing_cyclicGaloisAlgebra_of_nonzero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) : IsSimpleRing (cyclicGaloisAlgebra K L a) := by
  classical
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  rw [← I.one_mem_iff]
  have one_mem_of_isUnit_mem : ∀ {z : cyclicGaloisAlgebra K L a}, IsUnit z → z ∈ I →
      (1 : cyclicGaloisAlgebra K L a) ∈ I := by
    intro z hz hzI
    have hu : (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * z = 1 := by
      calc
        (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * z =
            (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * (hz.unit : cyclicGaloisAlgebra K L a) :=
          congrArg (fun w : cyclicGaloisAlgebra K L a =>
            (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * w) hz.unit_spec.symm
        _ = 1 := Units.inv_mul hz.unit
    rw [← hu]
    exact I.mul_mem_left _ _ hzI
  obtain ⟨x, hxI, hx0 : x ≠ 0⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal
      (cyclicGaloisAlgebra K L a)) < I)
  obtain ⟨u, hu⟩ := cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a x
  have huI : cyclicGaloisAlgebraNormalFormLinearMap K L a u ∈ I := by
    rw [hu]
    exact hxI
  have hu0 : u ≠ 0 := by
    intro huz
    apply hx0
    rw [← hu, huz, map_zero]
  let P : ℕ → Prop := fun m ↦ ∃ v : Fin (Module.finrank K L) → L,
    cyclicGaloisAlgebraNormalFormLinearMap K L a v ∈ I ∧ v ≠ 0 ∧
      (cyclicGaloisAlgebraCoefficientSupport K L v).card = m
  have hP : ∃ m, P m := ⟨(cyclicGaloisAlgebraCoefficientSupport K L u).card,
    u, huI, hu0, rfl⟩
  obtain ⟨v, hvI, hv0, hvcard⟩ := Nat.find_spec hP
  have hsupp : (cyclicGaloisAlgebraCoefficientSupport K L v).Nonempty := by
    by_contra hnone
    apply hv0
    funext i
    by_contra hvi
    exact hnone ⟨i, (mem_cyclicGaloisAlgebraCoefficientSupport K L v i).mpr hvi⟩
  have hcardpos : 0 < (cyclicGaloisAlgebraCoefficientSupport K L v).card :=
    Finset.card_pos.mpr hsupp
  by_cases hcardone : (cyclicGaloisAlgebraCoefficientSupport K L v).card = 1
  · exact one_mem_of_isUnit_mem
      (cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one K L a ha v
        hcardone) hvI
  · have hmore : 1 < (cyclicGaloisAlgebraCoefficientSupport K L v).card := by omega
    obtain ⟨j, hjmem, i, himem, hji⟩ :=
      Finset.one_lt_card.mp hmore
    have hjv : v j ≠ 0 := (mem_cyclicGaloisAlgebraCoefficientSupport K L v j).mp hjmem
    have hiv : v i ≠ 0 := (mem_cyclicGaloisAlgebraCoefficientSupport K L v i).mp himem
    obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i j hji.symm
    let w := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v
    have hwI : cyclicGaloisAlgebraNormalFormLinearMap K L a w ∈ I := by
      rw [← cyclicGaloisAlgebraNormalForm_twistedCommutator]
      exact I.sub_mem (I.mul_mem_right _ _ hvI) (I.mul_mem_left _ _ hvI)
    have hwi : w i ≠ 0 := by
      exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L j i b v hiv hb
    have hw0 : w ≠ 0 := by
      intro hw
      exact hwi (congrFun hw i)
    have hss : cyclicGaloisAlgebraCoefficientSupport K L w ⊂
        cyclicGaloisAlgebraCoefficientSupport K L v :=
      cyclicGaloisAlgebraTwistedCommutatorCoefficients_support_ssubset K L j b v hjv
    have hcardlt : (cyclicGaloisAlgebraCoefficientSupport K L w).card <
        (cyclicGaloisAlgebraCoefficientSupport K L v).card :=
      Finset.card_lt_card hss
    have hwP : P (cyclicGaloisAlgebraCoefficientSupport K L w).card :=
      ⟨w, hwI, hw0, rfl⟩
    have hmin : Nat.find hP ≤ (cyclicGaloisAlgebraCoefficientSupport K L w).card :=
      Nat.find_min' hP hwP
    have hlt : (cyclicGaloisAlgebraCoefficientSupport K L w).card < Nat.find hP := by
      calc
        (cyclicGaloisAlgebraCoefficientSupport K L w).card <
            (cyclicGaloisAlgebraCoefficientSupport K L v).card := hcardlt
        _ = Nat.find hP := hvcard
    exact ((not_le_of_gt hlt) hmin).elim

/-- In a nonzero cyclic Galois algebra, a commuting element has only degree-zero normal-form
coefficient; invariance under the cyclic generator then descends that coefficient to the base
field. -/
theorem cyclicGaloisAlgebra_center_exists_base_of_nonzero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a)
    (hx : ∀ y : cyclicGaloisAlgebra K L a, y * x = x * y) :
    ∃ k : K, x = algebraMap K (cyclicGaloisAlgebra K L a) k := by
    letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
      ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
    obtain ⟨v, hv⟩ := cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a x
    let i0 : Fin (Module.finrank K L) :=
      ⟨0, Module.finrank_pos (R := K) (M := L)⟩
    have hcoeff (i : Fin (Module.finrank K L)) (hi : i ≠ i0) : v i = 0 := by
      by_contra hvi
      obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i i0 hi
      let w := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i0 b v
      have hwzero : cyclicGaloisAlgebraNormalFormLinearMap K L a w = 0 := by
        rw [← cyclicGaloisAlgebraNormalForm_twistedCommutator, hv]
        simpa [i0] using sub_eq_zero.mpr (hx (cyclicGaloisAlgebraC K L a b)).symm
      have hw : w = 0 := cyclicGaloisAlgebraNormalFormLinearMap_injective K L a (by
        simpa using hwzero)
      have hwi : w i ≠ 0 := by
        exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i0 i b v hvi hb
      exact hwi (congrFun hw i)
    have hvform : v = Pi.single i0 (v i0) := by
      funext i
      by_cases hi : i = i0
      · subst i
        simp
      · rw [hcoeff i hi]
        simp [Ne.symm hi]
    have hx0 : x = cyclicGaloisAlgebraC K L a (v i0) := by
      calc
        x = cyclicGaloisAlgebraNormalFormLinearMap K L a v := hv.symm
        _ = cyclicGaloisAlgebraNormalFormLinearMap K L a (Pi.single i0 (v i0)) :=
          congrArg _ hvform
        _ = cyclicGaloisAlgebraC K L a (v i0) := by
          rw [cyclicGaloisAlgebraNormalFormLinearMap_single]
          simp [i0]
    have hX : cyclicGaloisAlgebraX K L a * cyclicGaloisAlgebraC K L a (v i0) =
        cyclicGaloisAlgebraC K L a (v i0) * cyclicGaloisAlgebraX K L a := by
      rw [← hx0]
      exact hx _
    have hdiffEq : cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L (v i0)) *
        cyclicGaloisAlgebraX K L a =
          cyclicGaloisAlgebraC K L a (v i0) * cyclicGaloisAlgebraX K L a := by
      change cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a) (cyclicGaloisGenerator K L (v i0)) *
          cyclicAlgebraX (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
            (algebraMap K L a) =
        cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a) (v i0) *
          cyclicAlgebraX (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
            (algebraMap K L a)
      rw [← show (cyclicGaloisGenerator K L).toRingEquiv (v i0) =
        cyclicGaloisGenerator K L (v i0) from rfl]
      rw [← cyclicAlgebraX_mul_cyclicAlgebraC]
      exact hX
    have hfix : cyclicGaloisGenerator K L (v i0) = v i0 := by
      by_contra hne
      have hzero : cyclicGaloisAlgebraC K L
          a (cyclicGaloisGenerator K L (v i0) - v i0) * cyclicGaloisAlgebraX K L a = 0 := by
        change (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a)
            (cyclicGaloisGenerator K L (v i0) - v i0)) * cyclicGaloisAlgebraX K L a = 0
        rw [map_sub, sub_mul]
        exact sub_eq_zero.mpr hdiffEq
      have hu : IsUnit (cyclicGaloisAlgebraC K L
          a (cyclicGaloisGenerator K L (v i0) - v i0) * cyclicGaloisAlgebraX K L a) := by
        apply IsUnit.mul
        · change IsUnit (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
            (Module.finrank K L) (algebraMap K L a)
              (cyclicGaloisGenerator K L (v i0) - v i0))
          exact IsUnit.map _ (Ne.isUnit (sub_ne_zero.mpr hne))
        · exact cyclicGaloisAlgebraX_isUnit K L a ha
      rw [hzero] at hu
      exact not_isUnit_zero hu
    have hfixed : ∀ sigma : Gal(L/K), sigma (v i0) = v i0 := by
      intro sigma
      let H : Subgroup Gal(L/K) := MulAction.stabilizer Gal(L/K) (v i0)
      have hgen : cyclicGaloisGenerator K L ∈ H := by
        change cyclicGaloisGenerator K L (v i0) = v i0
        exact hfix
      exact MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le.mpr hgen) (cyclicGaloisGenerator_spec K L sigma))
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (v i0)).mpr hfixed
    refine ⟨k, ?_⟩
    rw [hx0, cyclicGaloisAlgebra_algebraMap_apply]
    exact congrArg (cyclicGaloisAlgebraC K L a) hk.symm

/-- **All-degree cyclic centrality.** A nonzero cyclic Galois algebra has precisely its base
field as center. -/
theorem cyclicGaloisAlgebra_isCentral_of_nonzero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) : Algebra.IsCentral K (cyclicGaloisAlgebra K L a) where
  out := by
    intro x hx
    rw [Algebra.mem_bot]
    obtain ⟨k, hk⟩ := cyclicGaloisAlgebra_center_exists_base_of_nonzero K L a ha x
      (Subalgebra.mem_center_iff.mp hx)
    exact ⟨k, hk.symm⟩

/-- The raw cyclic algebra attached to every nonzero finite cyclic Galois parameter is a
finite-dimensional central simple algebra over its base field. -/
noncomputable def cyclicGaloisAlgebraCSA
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) : CSA K where
  carrier := cyclicGaloisAlgebra K L a
  isCentral := cyclicGaloisAlgebra_isCentral_of_nonzero K L a ha
  isSimple := isSimpleRing_cyclicGaloisAlgebra_of_nonzero K L a ha
  fin_dim := cyclicGaloisAlgebra_finiteDimensional K L a

/-- A nonzero cyclic Galois algebra over a number field remains central and simple at every
completion.  This is the direct Hasse central-simplicity application, distinct from ABHN
splitting or reciprocity. -/
theorem numberField_cyclicGaloisAlgebra_isCentral_and_isSimpleRing_at_all_places
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K) :
    Algebra.IsCentral (completion K p)
      (completion K p ⊗[K] cyclicGaloisAlgebra K L a) ∧
    IsSimpleRing (completion K p ⊗[K] cyclicGaloisAlgebra K L a) := by
  exact (numberField_isCentral_and_isSimpleRing_iff_forall_place K).mp
    ⟨cyclicGaloisAlgebra_isCentral_of_nonzero K L a ha,
      isSimpleRing_cyclicGaloisAlgebra_of_nonzero K L a ha⟩ p

/-- A nonzero cyclic Galois algebra over a global function field remains central and simple at
every finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isCentral_and_isSimpleRing_at_all_places
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F) :
    Algebra.IsCentral (rationalFunctionCompletion F p)
      (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) ∧
    IsSimpleRing
      (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) := by
  exact (rationalFunction_isCentral_and_isSimpleRing_iff_forall_place F).mp
    ⟨cyclicGaloisAlgebra_isCentral_of_nonzero (RatFunc F) L a ha,
      isSimpleRing_cyclicGaloisAlgebra_of_nonzero (RatFunc F) L a ha⟩ p

/-- Scalar extension of a nonzero cyclic Galois algebra embeds through its companion
representation.  Simplicity of scalar extension rules out any nonzero kernel. -/
theorem cyclicGaloisAlgebraScalarExtensionCompanionRepresentation_injective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) (ha : a ≠ 0) :
    Function.Injective
      (cyclicGaloisAlgebraScalarExtensionCompanionRepresentation K L n hdeg a) := by
  letI : IsSimpleRing (L ⊗[K] cyclicGaloisAlgebra K L a) :=
    scalarExtension_isSimpleRing (cyclicGaloisAlgebraCSA K L a ha)
  exact RingHom.injective _

/-- The scalar-extended companion representation is onto the full matrix algebra.  Its source
is simple and its source and target have the same finite dimension. -/
theorem cyclicGaloisAlgebraScalarExtensionCompanionRepresentation_surjective
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) (ha : a ≠ 0) :
    Function.Surjective
      (cyclicGaloisAlgebraScalarExtensionCompanionRepresentation K L n hdeg a) := by
  have hinj := cyclicGaloisAlgebraScalarExtensionCompanionRepresentation_injective
    K L n hdeg a ha
  have hfin : Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
      Module.finrank L (Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
    calc
      Module.finrank L (L ⊗[K] cyclicGaloisAlgebra K L a) =
          Module.finrank L
            (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) L) :=
        cyclicGaloisAlgebra_scalarExtension_finrank_eq_matrix K L a
      _ = Module.finrank L (Matrix (Fin (n + 1)) (Fin (n + 1)) L) := by
        rw [hdeg]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj

/-- **All-degree defining-field splitting.** Every nonzero cyclic Galois algebra becomes a
full matrix algebra after scalar extension to its defining cyclic Galois field. -/
noncomputable def cyclicGaloisAlgebraScalarExtensionMatrixAlgEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) (ha : a ≠ 0) :
    L ⊗[K] cyclicGaloisAlgebra K L a ≃ₐ[L] Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  AlgEquiv.ofBijective
    (cyclicGaloisAlgebraScalarExtensionCompanionRepresentation K L n hdeg a)
    ⟨cyclicGaloisAlgebraScalarExtensionCompanionRepresentation_injective K L n hdeg a ha,
      cyclicGaloisAlgebraScalarExtensionCompanionRepresentation_surjective K L n hdeg a ha⟩

/-- The Brauer class of every nonzero cyclic Galois algebra becomes split over its defining
cyclic Galois field. -/
theorem cyclicGaloisAlgebra_scalarExtension_brauerClass_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) (ha : a ≠ 0) :
    scalarExtensionBrauerMap K L (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) =
      brauerSplitClass L := by
  rw [scalarExtensionBrauerMap_brauerClass]
  calc
    brauerClass (scalarExtensionCSA (L := L) (cyclicGaloisAlgebraCSA K L a ha)) =
        brauerClass (matrixFinCSA (scalarCSA L) (n + 1)) :=
      brauerClass_eq_of_algEquiv _ _
        (cyclicGaloisAlgebraScalarExtensionMatrixAlgEquiv K L n hdeg a ha)
    _ = brauerSplitClass L := brauerClass_matrixFinCSA_scalar_eq (n + 1)

/-- A nonzero cyclic Galois Brauer class belongs to the relative kernel of its defining field. -/
theorem cyclicGaloisAlgebra_brauerClass_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) (ha : a ≠ 0) :
    brauerClass (cyclicGaloisAlgebraCSA K L a ha) ∈ scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (cyclicGaloisAlgebra_scalarExtension_brauerClass_eq_split K L n hdeg a ha)

/-- Every scalar extension through the defining cyclic Galois field splits a nonzero cyclic
Galois Brauer class. -/
theorem cyclicGaloisAlgebra_scalarExtension_brauerClass_eq_split_of_scalarTower
    (K L E : Type) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (a : K) (ha : a ≠ 0) :
    scalarExtensionBrauerMap K E (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) =
      brauerSplitClass E := by
  calc
    scalarExtensionBrauerMap K E (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) =
        scalarExtensionBrauerMap L E
          (scalarExtensionBrauerMap K L (brauerClass (cyclicGaloisAlgebraCSA K L a ha))) :=
      (scalarExtensionBrauerMap_comp K L E _).symm
    _ = scalarExtensionBrauerMap L E (brauerSplitClass L) := by
      rw [cyclicGaloisAlgebra_scalarExtension_brauerClass_eq_split K L n hdeg a ha]
    _ = brauerSplitClass E := scalarExtensionBrauerMap_split L E

/-- A nonzero base-unit parameter in any finite cyclic Galois degree determines a central
simple cyclic algebra. -/
noncomputable def cyclicGaloisH2ParameterCSA
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : Additive Kˣ) : CSA K :=
  cyclicGaloisAlgebraCSA K L (a.toMul : K) a.toMul.ne_zero

/-- A selected central simple algebra for every cyclic degree-two Galois cohomology class,
without a restriction on the cyclic extension degree. -/
noncomputable def cyclicGaloisH2ClassCSA
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (z : cyclicGaloisH2 K L) : CSA K :=
  cyclicGaloisH2ParameterCSA K L
    (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
      (cyclicGaloisH2Representative K L z)))

/-- The selected Brauer class of a cyclic degree-two Galois cohomology class in arbitrary
finite cyclic degree.  Tensor-product compatibility is a separate additive step. -/
noncomputable def cyclicGaloisH2BrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    cyclicGaloisH2 K L → BrauerGroup K :=
  fun z ↦ brauerClass (cyclicGaloisH2ClassCSA K L z)

/-- Every selected cyclic degree-two cohomology class lies in the relative Brauer kernel of its
defining cyclic Galois extension.  This is the algebraic splitting input that a local invariant
calculation must eventually identify with its source-side class-field-theory parameter. -/
theorem cyclicGaloisH2BrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K L (cyclicGaloisH2BrauerMap K L z) = brauerSplitClass L := by
  let u : Additive Kˣ := Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
    (cyclicGaloisH2Representative K L z))
  change scalarExtensionBrauerMap K L
    (brauerClass (cyclicGaloisAlgebraCSA K L (u.toMul : K) u.toMul.ne_zero)) =
      brauerSplitClass L
  exact cyclicGaloisAlgebra_scalarExtension_brauerClass_eq_split K L n hdeg
    (u.toMul : K) u.toMul.ne_zero

/-- The selected cyclic `H²` map lands in the defining extension's relative Brauer kernel. -/
theorem cyclicGaloisH2BrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerMap K L z ∈ scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (cyclicGaloisH2BrauerMap_scalarExtension_eq_split K L n hdeg z)

/-- The cyclic `H²` Brauer construction factors as a map into the relative Brauer kernel of its
defining cyclic Galois extension.  No additivity claim is made here: that needs the separate
tensor-product compatibility of cyclic parameters. -/
noncomputable def cyclicGaloisH2RelativeBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) :
    cyclicGaloisH2 K L → scalarExtensionBrauerKernel K L :=
  fun z ↦ ⟨cyclicGaloisH2BrauerMap K L z,
    cyclicGaloisH2BrauerMap_mem_scalarExtensionBrauerKernel K L n hdeg z⟩

/-- Every scalar extension through the defining cyclic Galois field kills every selected cyclic
`H²` Brauer representative. -/
theorem cyclicGaloisH2BrauerMap_scalarExtension_eq_split_of_scalarTower
    (K L E : Type) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K E (cyclicGaloisH2BrauerMap K L z) = brauerSplitClass E := by
  calc
    scalarExtensionBrauerMap K E (cyclicGaloisH2BrauerMap K L z) =
        scalarExtensionBrauerMap L E
          (scalarExtensionBrauerMap K L (cyclicGaloisH2BrauerMap K L z)) :=
      (scalarExtensionBrauerMap_comp K L E _).symm
    _ = scalarExtensionBrauerMap L E (brauerSplitClass L) := by
      rw [cyclicGaloisH2BrauerMap_scalarExtension_eq_split K L n hdeg z]
    _ = brauerSplitClass E := scalarExtensionBrauerMap_split L E

/-- Norm-equivalent cyclic degree-two parameters determine equal Brauer classes in every
finite cyclic degree. -/
theorem cyclicGaloisH2Parameter_brauerClass_eq_of_baseProjection_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a b : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L b) :
    brauerClass (cyclicGaloisH2ParameterCSA K L a) =
      brauerClass (cyclicGaloisH2ParameterCSA K L b) := by
  obtain ⟨e⟩ := cyclicGaloisH2BaseProjection_eq_implies_nonempty_algEquiv K L a b h
  exact brauerClass_eq_of_algEquiv _ _ e

/-- A cyclic base-unit parameter maps to the Brauer representative selected by its degree-two
cohomology class. -/
theorem cyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : Additive Kˣ) (z : cyclicGaloisH2 K L)
    (h : cyclicGaloisH2BaseProjection K L a = z) :
    brauerClass (cyclicGaloisH2ParameterCSA K L a) = cyclicGaloisH2BrauerMap K L z := by
  obtain ⟨e⟩ := cyclicGaloisH2BaseProjection_eq_class_implies_nonempty_algEquiv K L a z h
  exact brauerClass_eq_of_algEquiv _ _ e

/-- A vanishing cyclic base-unit parameter represents the split Brauer class in arbitrary
finite cyclic degree. -/
theorem cyclicGaloisH2Parameter_brauerClass_eq_split_of_baseProjection_eq_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : Additive Kˣ) (h : cyclicGaloisH2BaseProjection K L a = 0) :
    brauerClass (cyclicGaloisH2ParameterCSA K L a) = brauerSplitClass K := by
  calc
    brauerClass (cyclicGaloisH2ParameterCSA K L a) =
        brauerClass (cyclicGaloisH2ZeroCSA K L a h) := by
      exact brauerClass_eq_of_algEquiv _ _ AlgEquiv.refl
    _ = brauerSplitClass K := brauerClass_cyclicGaloisH2ZeroCSA_eq_split K L a h

/-- The zero cyclic degree-two cohomology class selects the split Brauer class in arbitrary
finite cyclic degree. -/
theorem cyclicGaloisH2BrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    cyclicGaloisH2BrauerMap K L 0 = brauerSplitClass K := by
  apply cyclicGaloisH2Parameter_brauerClass_eq_split_of_baseProjection_eq_zero K L
  exact cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection K L 0

/-- Any concrete finite cyclic norm-quotient parameterization supplies a corresponding map to
Brauer classes in the same cyclic degree.  For local fields, an invariant identification may be
plugged into this map once the separate local-class-field-theory bridge is available. -/
noncomputable def cyclicGaloisNormQuotientBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    ZMod n → BrauerGroup K :=
  fun z ↦ cyclicGaloisH2BrauerMap K L
    (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm z))

/-- Every finite norm-quotient parameter selected by a cyclic Galois extension becomes split
after extension to that field. -/
theorem cyclicGaloisNormQuotientBrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : ZMod m) :
    scalarExtensionBrauerMap K L (cyclicGaloisNormQuotientBrauerMap K L m e z) =
      brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (cyclicGaloisH2BrauerMap K L (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm z))) =
      brauerSplitClass L
  exact cyclicGaloisH2BrauerMap_scalarExtension_eq_split K L n hdeg _

/-- Every finite norm-quotient value lands in the defining relative Brauer kernel. -/
theorem cyclicGaloisNormQuotientBrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : ZMod m) :
    cyclicGaloisNormQuotientBrauerMap K L m e z ∈ scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (cyclicGaloisNormQuotientBrauerMap_scalarExtension_eq_split K L m e n hdeg z)

/-- The zero residue class of every finite cyclic norm-quotient parameterization is split. -/
theorem cyclicGaloisNormQuotientBrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    cyclicGaloisNormQuotientBrauerMap K L n e 0 = brauerSplitClass K := by
  change cyclicGaloisH2BrauerMap K L
    (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm 0)) = brauerSplitClass K
  rw [map_zero, map_zero]
  exact cyclicGaloisH2BrauerMap_zero_eq_split K L

/-- A cyclic `H²` invariant with values in `ℤ/nℤ` induces a finite-level Brauer parameter map.
This is the direct interface used by unramified local invariant calculations; it deliberately
does not identify it with the full local Brauer invariant. -/
noncomputable def cyclicGaloisH2InvariantBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) : ZMod n → BrauerGroup K :=
  fun z ↦ cyclicGaloisH2BrauerMap K L (e.symm z)

/-- Every finite cyclic invariant value selected through `H²` becomes split after scalar
extension to the defining cyclic Galois field. -/
theorem cyclicGaloisH2InvariantBrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : ZMod m) :
    scalarExtensionBrauerMap K L (cyclicGaloisH2InvariantBrauerMap K L m e z) =
      brauerSplitClass L := by
  change scalarExtensionBrauerMap K L (cyclicGaloisH2BrauerMap K L (e.symm z)) =
    brauerSplitClass L
  exact cyclicGaloisH2BrauerMap_scalarExtension_eq_split K L n hdeg _

/-- Every finite `H²` invariant value lands in the defining relative Brauer kernel. -/
theorem cyclicGaloisH2InvariantBrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : ZMod m) :
    cyclicGaloisH2InvariantBrauerMap K L m e z ∈ scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (cyclicGaloisH2InvariantBrauerMap_scalarExtension_eq_split K L m e n hdeg z)

/-- A finite cyclic `H²` invariant factors through the defining relative Brauer kernel. -/
noncomputable def cyclicGaloisH2InvariantRelativeBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) :
    ZMod m → scalarExtensionBrauerKernel K L :=
  fun z ↦ ⟨cyclicGaloisH2InvariantBrauerMap K L m e z,
    cyclicGaloisH2InvariantBrauerMap_mem_scalarExtensionBrauerKernel K L m e n hdeg z⟩

/-- The zero invariant value always induces the split Brauer class. -/
theorem cyclicGaloisH2InvariantBrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) :
    cyclicGaloisH2InvariantBrauerMap K L n e 0 = brauerSplitClass K := by
  change cyclicGaloisH2BrauerMap K L (e.symm 0) = brauerSplitClass K
  rw [map_zero]
  exact cyclicGaloisH2BrauerMap_zero_eq_split K L

/-- Finite continuous unit Galois cohomology in degree two maps to the cyclic Brauer
representative through the closed comparison with ordinary cohomology. -/
noncomputable def finiteGaloisContinuousCyclicH2BrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    continuousGaloisUnitCohomology 2 K L → BrauerGroup K :=
  fun z ↦ cyclicGaloisH2BrauerMap K L
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- The continuous finite-Galois cyclic `H²` bridge preserves defining-field splitting. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1)
    (z : continuousGaloisUnitCohomology 2 K L) :
    scalarExtensionBrauerMap K L (finiteGaloisContinuousCyclicH2BrauerMap K L z) =
      brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (cyclicGaloisH2BrauerMap K L (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) =
      brauerSplitClass L
  exact cyclicGaloisH2BrauerMap_scalarExtension_eq_split K L n hdeg _

/-- Every finite continuous cyclic `H²` representative lands in the defining relative Brauer
kernel. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hdeg : Module.finrank K L = n + 1)
    (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCyclicH2BrauerMap K L z ∈ scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (finiteGaloisContinuousCyclicH2BrauerMap_scalarExtension_eq_split K L n hdeg z)

/-- The continuous zero class maps to the split Brauer class. -/
theorem finiteGaloisContinuousCyclicH2BrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    finiteGaloisContinuousCyclicH2BrauerMap K L 0 = brauerSplitClass K := by
  change cyclicGaloisH2BrauerMap K L
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L 0) = brauerSplitClass K
  rw [map_zero]
  exact cyclicGaloisH2BrauerMap_zero_eq_split K L

/-- A finite cyclic continuous-H² invariant valued in `ℤ/nℤ` induces a Brauer parameter map.
This is the precise interface consumed by the unramified nonarchimedean invariant package. -/
noncomputable def finiteGaloisContinuousCyclicH2InvariantBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod n) :
    ZMod n → BrauerGroup K :=
  fun z ↦ finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z)

/-- Every selected finite continuous cyclic invariant value becomes split over its defining
cyclic Galois field. -/
theorem finiteGaloisContinuousCyclicH2InvariantBrauerMap_scalarExtension_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : ZMod m) :
    scalarExtensionBrauerMap K L
      (finiteGaloisContinuousCyclicH2InvariantBrauerMap K L m e z) = brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm z)) = brauerSplitClass L
  exact finiteGaloisContinuousCyclicH2BrauerMap_scalarExtension_eq_split K L n hdeg _

/-- Every selected finite continuous invariant value lies in the defining relative Brauer
kernel. -/
theorem finiteGaloisContinuousCyclicH2InvariantBrauerMap_mem_scalarExtensionBrauerKernel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) (z : ZMod m) :
    finiteGaloisContinuousCyclicH2InvariantBrauerMap K L m e z ∈
      scalarExtensionBrauerKernel K L :=
  (mem_scalarExtensionBrauerKernel_iff K L _).mpr
    (finiteGaloisContinuousCyclicH2InvariantBrauerMap_scalarExtension_eq_split K L m e n hdeg z)

/-- A finite continuous cyclic invariant factors through the defining relative Brauer kernel. -/
noncomputable def finiteGaloisContinuousCyclicH2InvariantRelativeBrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (m : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod m)
    (n : ℕ) (hdeg : Module.finrank K L = n + 1) :
    ZMod m → scalarExtensionBrauerKernel K L :=
  fun z ↦ ⟨finiteGaloisContinuousCyclicH2InvariantBrauerMap K L m e z,
    finiteGaloisContinuousCyclicH2InvariantBrauerMap_mem_scalarExtensionBrauerKernel
      K L m e n hdeg z⟩

/-- The zero continuous invariant value maps to the split Brauer class. -/
theorem finiteGaloisContinuousCyclicH2InvariantBrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod n) :
    finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e 0 = brauerSplitClass K := by
  change finiteGaloisContinuousCyclicH2BrauerMap K L (e.symm 0) = brauerSplitClass K
  rw [map_zero]
  exact finiteGaloisContinuousCyclicH2BrauerMap_zero_eq_split K L

/-- Over a finite coefficient field, every finite-degree cyclic `H²` Brauer representative is
split.  This subsumes the earlier degree-two and degree-three finite-residue statements. -/
theorem finiteField_cyclicGaloisH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [Finite L] [FiniteDimensional K L] [IsGalois K L]
    (z : cyclicGaloisH2 K L) : cyclicGaloisH2BrauerMap K L z = brauerSplitClass K := by
  rw [show z = 0 by exact finiteField_H2_eq_zero z]
  exact cyclicGaloisH2BrauerMap_zero_eq_split K L

/-- Any finite cyclic `H²` invariant over a finite coefficient field has only split Brauer
values. -/
theorem finiteField_cyclicGaloisH2InvariantBrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [Finite L] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) (z : ZMod n) :
    cyclicGaloisH2InvariantBrauerMap K L n e z = brauerSplitClass K := by
  exact finiteField_cyclicGaloisH2BrauerMap_eq_split K L (e.symm z)

/-- Finite continuous cyclic degree-two classes over a finite coefficient field have split
Brauer representatives. -/
theorem finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [Finite L] [FiniteDimensional K L] [IsGalois K L]
    (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCyclicH2BrauerMap K L z = brauerSplitClass K := by
  exact finiteField_cyclicGaloisH2BrauerMap_eq_split K L
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- Every finite continuous cyclic `H²` invariant over a finite coefficient field has split
Brauer values. -/
theorem finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [Finite L] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod n) (z : ZMod n) :
    finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e z = brauerSplitClass K := by
  exact finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_split K L (e.symm z)

end GaloisForLFunctions.HTGeometry.ABHN
