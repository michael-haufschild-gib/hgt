import GaloisForLFunctions.HTGeometry.TorusExteriorComparison
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Differential forms in coordinates

Multiplying an element of an exterior power by a vector on the left raises the degree by one, and
under the identification of the exterior power of the dual with the alternating forms this is the
cofactor expansion of a determinant along its first column: the alternating form of the product is
the alternating sum of the values of the linear form against the form of the original element.  This
is the wedge product with a one-form, and it computes the exterior derivative of a function times an
invariant form.  Every form on a coordinate space is such a sum: the coordinate forms of the sets of
coordinates are a basis of the invariant forms, and the coefficients of a form of class `C^(1 : ℕ)` are
again of class `C^(1 : ℕ)`, so the exterior derivative of any form is the sum of the wedges of the
differentials of its coefficients with the coordinate forms.

* `exteriorConsMul` : multiplication by a vector on the left, one degree up.
* `constantFormOfExterior_consMul` : the cofactor expansion.
* `extDeriv_smul_constantForm` : the exterior derivative of a function times an invariant form.
* `coordForm`, `coordFormBasis`, `constantForm_expansion` : the coordinate forms are a basis.
* `extDeriv_eq_sum_consMul` : the exterior derivative in coordinates.
-/

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module ContinuousAlternatingMap

section ConsMul

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {q : ℕ}

theorem ι_mem_exteriorPower_one (x : M) : ExteriorAlgebra.ι R x ∈ ⋀[R]^(1 : ℕ) M := by
  simpa only [pow_one] using LinearMap.mem_range_self _ x

/-- **Multiplication by a vector on the left**, raising the degree of an exterior power by one. -/
noncomputable def exteriorConsMul (x : M) (y : ⋀[R]^q M) : ⋀[R]^(q + 1) M :=
  ⟨ExteriorAlgebra.ι R x * (y : ExteriorAlgebra R M), by
    have h : ExteriorAlgebra.ι R x * (y : ExteriorAlgebra R M) ∈ ⋀[R]^(1 + q) M :=
      SetLike.mul_mem_graded (ι_mem_exteriorPower_one x) y.2
    rwa [Nat.add_comm 1 q] at h⟩

theorem exteriorConsMul_coe (x : M) (y : ⋀[R]^q M) :
    (exteriorConsMul x y : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R x * (y : ExteriorAlgebra R M) := rfl

/-- Multiplying an exterior product of vectors by one more vector prepends it. -/
theorem exteriorConsMul_ιMulti (x : M) (ψ : Fin q → M) :
    exteriorConsMul x (exteriorPower.ιMulti R q ψ) =
      exteriorPower.ιMulti R (q + 1) (Fin.cons x ψ) := by
  refine Subtype.ext ?_
  rw [exteriorConsMul_coe]
  show ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R q ψ =
    ExteriorAlgebra.ιMulti R (q + 1) (Fin.cons x ψ)
  have htail : Matrix.vecTail (Fin.cons x ψ : Fin (q + 1) → M) = ψ := by
    funext i
    show (Fin.cons x ψ : Fin (q + 1) → M) i.succ = ψ i
    rw [Fin.cons_succ]
  rw [ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, htail]

/-- Multiplication by a vector on the left is additive. -/
theorem exteriorConsMul_add (x : M) (y z : ⋀[R]^q M) :
    exteriorConsMul x (y + z) = exteriorConsMul x y + exteriorConsMul x z := by
  refine Subtype.ext ?_
  rw [exteriorConsMul_coe]
  show ExteriorAlgebra.ι R x * ((y : ExteriorAlgebra R M) + z) =
    (exteriorConsMul x y : ExteriorAlgebra R M) + (exteriorConsMul x z : ExteriorAlgebra R M)
  rw [exteriorConsMul_coe, exteriorConsMul_coe, mul_add]

/-- Multiplication by a vector on the left is homogeneous. -/
theorem exteriorConsMul_smul (c : R) (x : M) (y : ⋀[R]^q M) :
    exteriorConsMul x (c • y) = c • exteriorConsMul x y := by
  refine Subtype.ext ?_
  rw [exteriorConsMul_coe]
  show ExteriorAlgebra.ι R x * (c • (y : ExteriorAlgebra R M)) =
    c • (exteriorConsMul x y : ExteriorAlgebra R M)
  rw [exteriorConsMul_coe, mul_smul_comm]

/-- Multiplication by a vector on the left, as a linear map. -/
noncomputable def exteriorConsMulₗ (x : M) : ⋀[R]^q M →ₗ[R] ⋀[R]^(q + 1) M where
  toFun := exteriorConsMul x
  map_add' := exteriorConsMul_add x
  map_smul' c y := exteriorConsMul_smul c x y

end ConsMul

section CofactorExpansion

variable {𝕜 : Type*} [RCLike 𝕜] {r q n : ℕ}

/-- Evaluation of a continuous alternating form at a tuple, as a linear map in the form. -/
def evalFormₗ (v : Fin n → (Fin r → 𝕜)) : ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 where
  toFun A := A v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalFormₗ_apply (v : Fin n → (Fin r → 𝕜)) (A : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :
    evalFormₗ v A = A v := rfl

/-- **The alternating form of a product with a linear form is the cofactor expansion** of the
determinant along the first column: the alternating sum of the values of the linear form against the
form of the original element. -/
theorem constantFormOfExterior_consMul (φ : Module.Dual 𝕜 (Fin r → 𝕜))
    (y : ⋀[𝕜]^q (Module.Dual 𝕜 (Fin r → 𝕜))) (v : Fin (q + 1) → (Fin r → 𝕜)) :
    constantFormOfExterior 𝕜 r (q + 1) (exteriorConsMul φ y) v =
      ∑ i : Fin (q + 1), (-1 : 𝕜) ^ (i : ℕ) * φ (v i) *
        constantFormOfExterior 𝕜 r q y (Fin.removeNth i v) := by
  classical
  set F : ⋀[𝕜]^q (Module.Dual 𝕜 (Fin r → 𝕜)) →ₗ[𝕜] 𝕜 :=
    (evalFormₗ v).comp
      ((constantFormOfExterior 𝕜 r (q + 1)).toLinearMap.comp (exteriorConsMulₗ φ)) with hF
  set G : ⋀[𝕜]^q (Module.Dual 𝕜 (Fin r → 𝕜)) →ₗ[𝕜] 𝕜 :=
    ∑ i : Fin (q + 1), ((-1 : 𝕜) ^ (i : ℕ) * φ (v i)) •
      ((evalFormₗ (Fin.removeNth i v)).comp
        (constantFormOfExterior 𝕜 r q).toLinearMap) with hG
  have hGapply : ∀ z, G z = ∑ i : Fin (q + 1), (-1 : 𝕜) ^ (i : ℕ) * φ (v i) *
      constantFormOfExterior 𝕜 r q z (Fin.removeNth i v) := by
    intro z
    rw [hG, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    rfl
  have hFapply : ∀ z, F z =
      constantFormOfExterior 𝕜 r (q + 1) (exteriorConsMul φ z) v := fun z => rfl
  have hgen : ∀ z ∈ Set.range (exteriorPower.ιMulti 𝕜 q (M := Module.Dual 𝕜 (Fin r → 𝕜))),
      F z = G z := by
    rintro z ⟨ψ, rfl⟩
    rw [hFapply, hGapply, exteriorConsMul_ιMulti, constantFormOfExterior_ιMulti]
    have hexp := Matrix.det_succ_column_zero
      (A := Matrix.of fun i j => (Fin.cons φ ψ : Fin (q + 1) → Module.Dual 𝕜 (Fin r → 𝕜)) j (v i))
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constantFormOfExterior_ιMulti]
    have hcol : (Matrix.of fun i j =>
        (Fin.cons φ ψ : Fin (q + 1) → Module.Dual 𝕜 (Fin r → 𝕜)) j (v i)) i 0 = φ (v i) := by
      show (Fin.cons φ ψ : Fin (q + 1) → Module.Dual 𝕜 (Fin r → 𝕜)) 0 (v i) = φ (v i)
      rw [Fin.cons_zero]
    have hsub : ((Matrix.of fun i j =>
          (Fin.cons φ ψ : Fin (q + 1) → Module.Dual 𝕜 (Fin r → 𝕜)) j (v i)).submatrix
        i.succAbove Fin.succ) =
        Matrix.of fun a b => ψ b (Fin.removeNth i v a) := by
      ext a b
      show (Fin.cons φ ψ : Fin (q + 1) → Module.Dual 𝕜 (Fin r → 𝕜)) b.succ (v (i.succAbove a)) =
        ψ b (Fin.removeNth i v a)
      rw [Fin.cons_succ]
      rfl
    rw [hcol, hsub]
  have hFG : F = G := LinearMap.ext_on
    (exteriorPower.ιMulti_span 𝕜 q (Module.Dual 𝕜 (Fin r → 𝕜))) hgen
  rw [← hFapply, hFG, hGapply]

theorem zpow_neg_one_smul (i : ℕ) (z : 𝕜) : ((-1 : ℤ) ^ i) • z = (-1 : 𝕜) ^ i * z := by
  rw [zsmul_eq_mul]
  push_cast
  ring

/-- **The exterior derivative of a function times an invariant form** is the wedge of its
differential with that form.  This is the Leibniz rule in the case of a factor of degree zero, and
the computation that turns the differential of a coefficient into a one-form. -/
theorem extDeriv_smul_constantForm {f : (Fin r → 𝕜) → 𝕜} (hf : Differentiable 𝕜 f)
    (y : ⋀[𝕜]^q (Module.Dual 𝕜 (Fin r → 𝕜))) (x : Fin r → 𝕜) :
    extDeriv (fun w => f w • constantFormOfExterior 𝕜 r q y) x =
      constantFormOfExterior 𝕜 r (q + 1)
        (exteriorConsMul ((fderiv 𝕜 f x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) y) := by
  set c := constantFormOfExterior 𝕜 r q y with hc
  have hfd : fderiv 𝕜 (fun w => f w • c) x = (fderiv 𝕜 f x).smulRight c :=
    ((hf x).hasFDerivAt.smul_const c).fderiv
  ext v
  rw [extDeriv, hfd, alternatizeUncurryFin_apply, constantFormOfExterior_consMul]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((-1 : ℤ) ^ (i : ℕ)) • ((((fderiv 𝕜 f x) (v i)) • c) (Fin.removeNth i v)) = _
  show ((-1 : ℤ) ^ (i : ℕ)) • (((fderiv 𝕜 f x) (v i)) * (c (Fin.removeNth i v))) = _
  rw [zpow_neg_one_smul]
  show _ = (-1 : 𝕜) ^ (i : ℕ) * ((fderiv 𝕜 f x) (v i)) * (c (Fin.removeNth i v))
  ring

end CofactorExpansion

section BasisExpansion

variable {𝕜 : Type*} [RCLike 𝕜] {r n : ℕ}

theorem formOfExterior_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ}
    (x : ⋀[R]^m (Module.Dual R M)) (v : Fin m → M) :
    formOfExterior R M m x v = exteriorPower.pairingDual R M m x (exteriorPower.ιMulti R m v) := by
  show (exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual R M m x)) v = _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  rfl

/-- The increasing tuple of standard basis vectors of a set of coordinates. -/
noncomputable def coordTuple (𝕜 : Type*) [RCLike 𝕜] {r n : ℕ}
    (S : Set.powersetCard (Fin r) n) : Fin n → (Fin r → 𝕜) :=
  (Pi.basisFun 𝕜 (Fin r)) ∘ (Set.powersetCard.ofFinEmbEquiv.symm S)

/-- **The invariant form attached to a set of coordinates**: the determinant in those
coordinates. -/
noncomputable def coordForm (𝕜 : Type*) [RCLike 𝕜] (r n : ℕ)
    (S : Set.powersetCard (Fin r) n) : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜 :=
  constantFormOfExterior 𝕜 r n (((Pi.basisFun 𝕜 (Fin r)).dualBasis).exteriorPower n S)

/-- The coordinate forms are dual to the tuples of basis vectors. -/
theorem coordForm_apply_coordTuple (S T : Set.powersetCard (Fin r) n) :
    coordForm 𝕜 r n S (coordTuple 𝕜 T) = if S = T then 1 else 0 := by
  classical
  show formOfExterior 𝕜 (Fin r → 𝕜) n
    (((Pi.basisFun 𝕜 (Fin r)).dualBasis).exteriorPower n S) (coordTuple 𝕜 T) = _
  rw [formOfExterior_apply, pairingDual_dualBasis_exteriorPower]
  have htuple : exteriorPower.ιMulti 𝕜 n (coordTuple 𝕜 T) =
      ((Pi.basisFun 𝕜 (Fin r)).exteriorPower n) T := by
    rw [exteriorPower.basis_apply]
    rfl
  rw [htuple, Module.Basis.dualBasis_apply_self]
  by_cases h : S = T
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun hc => h hc.symm]

/-- **The invariant forms attached to the sets of coordinates form a basis.** -/
noncomputable def coordFormBasis (𝕜 : Type*) [RCLike 𝕜] (r n : ℕ) :
    Module.Basis (Set.powersetCard (Fin r) n) 𝕜 ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :=
  (((Pi.basisFun 𝕜 (Fin r)).dualBasis).exteriorPower n).map (constantFormOfExterior 𝕜 r n)

theorem coordFormBasis_apply (S : Set.powersetCard (Fin r) n) :
    coordFormBasis 𝕜 r n S = coordForm 𝕜 r n S := rfl

/-- **Every invariant form is the sum of its values on the increasing tuples of basis vectors**
times the corresponding coordinate forms. -/
theorem constantForm_expansion (α : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :
    α = ∑ S : Set.powersetCard (Fin r) n, α (coordTuple 𝕜 S) • coordForm 𝕜 r n S := by
  classical
  have hsum := (coordFormBasis 𝕜 r n).sum_repr α
  have hcoeff : ∀ T : Set.powersetCard (Fin r) n,
      (coordFormBasis 𝕜 r n).repr α T = α (coordTuple 𝕜 T) := by
    intro T
    have happ := congrArg (fun A : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜 => A (coordTuple 𝕜 T)) hsum
    rw [ContinuousAlternatingMap.sum_apply] at happ
    have hterm : ∀ S : Set.powersetCard (Fin r) n,
        ((coordFormBasis 𝕜 r n).repr α S • (coordFormBasis 𝕜 r n) S) (coordTuple 𝕜 T) =
          if S = T then (coordFormBasis 𝕜 r n).repr α S else 0 := by
      intro S
      show (coordFormBasis 𝕜 r n).repr α S * ((coordFormBasis 𝕜 r n) S (coordTuple 𝕜 T)) = _
      rw [coordFormBasis_apply, coordForm_apply_coordTuple]
      by_cases h : S = T
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun S _ => hterm S, Finset.sum_ite_eq' Finset.univ T] at happ
    rw [if_pos (Finset.mem_univ T)] at happ
    exact happ
  conv_lhs => rw [← hsum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hcoeff S, coordFormBasis_apply]

/-- Evaluation of an invariant form at a tuple, as a continuous linear map. -/
noncomputable def evalFormL (v : Fin n → (Fin r → 𝕜)) :
    ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n => (Fin r → 𝕜)) 𝕜 v).comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜)

@[simp]
theorem evalFormL_apply (v : Fin n → (Fin r → 𝕜)) (A : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :
    evalFormL v A = A v := rfl

/-- **Every form is the sum of its coefficient functions times the coordinate forms**, and the
coefficients inherit the differentiability of the form. -/
theorem form_expansion (ω : PeriodicFormSpace 𝕜 r n) (x : Fin r → 𝕜) :
    ω x = ∑ S : Set.powersetCard (Fin r) n, (ω x (coordTuple 𝕜 S)) • coordForm 𝕜 r n S :=
  constantForm_expansion (ω x)

theorem form_coeff_differentiable {ω : PeriodicFormSpace 𝕜 r n} (hω : Differentiable 𝕜 ω)
    (S : Set.powersetCard (Fin r) n) :
    Differentiable 𝕜 fun x => ω x (coordTuple 𝕜 S) := fun x =>
  ((evalFormL (coordTuple 𝕜 S)).differentiableAt).comp x (hω x)

/-- The exterior derivative of a finite sum of forms is the sum of the exterior derivatives. -/
theorem extDeriv_finset_sum {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (g : ι → PeriodicFormSpace 𝕜 r n) (hg : ∀ i, Differentiable 𝕜 (g i)) (x : Fin r → 𝕜) :
    extDeriv (fun y => ∑ i ∈ t, g i y) x = ∑ i ∈ t, extDeriv (g i) x := by
  classical
  induction t using Finset.induction with
  | empty =>
      show extDeriv (fun _ : Fin r → 𝕜 => (0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) x = _
      rw [extDeriv_const, Finset.sum_empty]
  | insert a t ha ih =>
      have hpartial : Differentiable 𝕜 fun y : Fin r → 𝕜 => ∑ i ∈ t, g i y := fun y =>
        DifferentiableAt.fun_sum fun i _ => (hg i) y
      have hrw : (fun y : Fin r → 𝕜 => ∑ i ∈ insert a t, g i y) =
          fun y => g a y + ∑ i ∈ t, g i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [hrw, extDeriv_fun_add ((hg a) x) (hpartial x), ih, Finset.sum_insert ha]

/-- **The exterior derivative in coordinates**: expanding a form in the coordinate forms, its
exterior derivative is the sum of the wedges of the differentials of the coefficients with the
corresponding coordinate forms. -/
theorem extDeriv_eq_sum_consMul {ω : PeriodicFormSpace 𝕜 r n} (hω : Differentiable 𝕜 ω)
    (x : Fin r → 𝕜) :
    extDeriv ω x = ∑ S : Set.powersetCard (Fin r) n, constantFormOfExterior 𝕜 r (n + 1)
      (exteriorConsMul
        ((fderiv 𝕜 (fun y => ω y (coordTuple 𝕜 S)) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜))
        (((Pi.basisFun 𝕜 (Fin r)).dualBasis).exteriorPower n S)) := by
  classical
  have hrw : ω = fun y => ∑ S : Set.powersetCard (Fin r) n,
      (ω y (coordTuple 𝕜 S)) • coordForm 𝕜 r n S := by
    funext y
    exact form_expansion ω y
  have hdiff : ∀ S : Set.powersetCard (Fin r) n,
      Differentiable 𝕜 fun y : Fin r → 𝕜 => (ω y (coordTuple 𝕜 S)) • coordForm 𝕜 r n S := by
    intro S y
    exact (form_coeff_differentiable hω S y).smul_const _
  conv_lhs => rw [hrw]
  rw [extDeriv_finset_sum Finset.univ _ hdiff]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact extDeriv_smul_constantForm (form_coeff_differentiable hω S) _ x

end BasisExpansion

end GaloisForLFunctions.HTGeometry
