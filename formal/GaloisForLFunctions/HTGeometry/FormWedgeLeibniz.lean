import GaloisForLFunctions.HTGeometry.ExteriorGradedMul

/-!
# The wedge product of differential forms and the Leibniz rule

Transporting the graded multiplication of the exterior algebra of the dual through the
identification of the exterior powers with the alternating forms gives a wedge product of
differential forms on a coordinate space.  Expanding both factors in the coordinate forms, the
exterior derivative of a product is computed by the product rule for the coefficients, and moving
the differential of the second family of coefficients past the first factor produces the sign
`(-1)^p`.  So the wedge product makes the de Rham complex a differential graded algebra.

* `wedgeForm` : the wedge product of two alternating forms.
* `extDeriv_wedgeForm` : the Leibniz rule.
-/

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section WedgeForm

variable {𝕜 : Type*} [RCLike 𝕜] {r p q n : ℕ}

/-- **The wedge product of two alternating forms** on a coordinate space, transported from the
graded multiplication of the exterior algebra of the dual. -/
noncomputable def wedgeForm (h : p + q = n) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜)
    (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜 :=
  constantFormOfExterior 𝕜 r n
    (exteriorMulOf h ((constantFormOfExterior 𝕜 r p).symm α)
      ((constantFormOfExterior 𝕜 r q).symm β))

/-- The wedge product of the forms of two elements of the exterior powers is the form of their
product. -/
theorem wedgeForm_constantFormOfExterior (h : p + q = n)
    (y : ⋀[𝕜]^p (Module.Dual 𝕜 (Fin r → 𝕜))) (z : ⋀[𝕜]^q (Module.Dual 𝕜 (Fin r → 𝕜))) :
    wedgeForm h (constantFormOfExterior 𝕜 r p y) (constantFormOfExterior 𝕜 r q z) =
      constantFormOfExterior 𝕜 r n (exteriorMulOf h y z) := by
  rw [wedgeForm, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem wedgeForm_add_left (h : p + q = n) (α α' : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜)
    (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h (α + α') β = wedgeForm h α β + wedgeForm h α' β := by
  rw [wedgeForm, map_add, exteriorMulOf_add_left, map_add]
  rfl

theorem wedgeForm_smul_left (h : p + q = n) (c : 𝕜) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜)
    (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h (c • α) β = c • wedgeForm h α β := by
  rw [wedgeForm, map_smul, exteriorMulOf_smul_left, map_smul]
  rfl

theorem wedgeForm_add_right (h : p + q = n) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜)
    (β β' : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h α (β + β') = wedgeForm h α β + wedgeForm h α β' := by
  rw [wedgeForm, map_add, exteriorMulOf_add_right, map_add]
  rfl

theorem wedgeForm_smul_right (h : p + q = n) (c : 𝕜) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜)
    (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h α (c • β) = c • wedgeForm h α β := by
  rw [wedgeForm, map_smul, exteriorMulOf_smul_right, map_smul]
  rfl

/-- The wedge product as a linear map in the left factor. -/
noncomputable def wedgeFormLeftₗ (h : p + q = n) (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    ((Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) →ₗ[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) where
  toFun α := wedgeForm h α β
  map_add' α α' := wedgeForm_add_left h α α' β
  map_smul' c α := wedgeForm_smul_left h c α β

/-- The wedge product as a linear map in the right factor. -/
noncomputable def wedgeFormRightₗ (h : p + q = n) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) :
    ((Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) →ₗ[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) where
  toFun β := wedgeForm h α β
  map_add' β β' := wedgeForm_add_right h α β β'
  map_smul' c β := wedgeForm_smul_right h c α β

theorem wedgeForm_sum_left {ι : Type*} (h : p + q = n) (t : Finset ι)
    (α : ι → (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h (∑ i ∈ t, α i) β = ∑ i ∈ t, wedgeForm h (α i) β :=
  map_sum (wedgeFormLeftₗ h β) α t

theorem wedgeForm_sum_right {ι : Type*} (h : p + q = n) (t : Finset ι)
    (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) (β : ι → (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h α (∑ i ∈ t, β i) = ∑ i ∈ t, wedgeForm h α (β i) :=
  map_sum (wedgeFormRightₗ h α) β t

end WedgeForm

section Leibniz

variable {𝕜 : Type*} [RCLike 𝕜] {r p q n : ℕ}

/-- The element of the exterior power of the dual attached to a set of coordinates. -/
noncomputable def coordExterior (𝕜 : Type*) [RCLike 𝕜] (r m : ℕ)
    (S : Set.powersetCard (Fin r) m) : ⋀[𝕜]^m (Module.Dual 𝕜 (Fin r → 𝕜)) :=
  ((Pi.basisFun 𝕜 (Fin r)).dualBasis).exteriorPower m S

theorem constantFormOfExterior_coordExterior (m : ℕ) (S : Set.powersetCard (Fin r) m) :
    constantFormOfExterior 𝕜 r m (coordExterior 𝕜 r m S) = coordForm 𝕜 r m S := rfl

/-- The expansion of the wedge product of two forms in the coordinate forms. -/
theorem wedgeForm_expansion (h : p + q = n) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜)
    (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h α β =
      ∑ S : Set.powersetCard (Fin r) p, ∑ T : Set.powersetCard (Fin r) q,
        (α (coordTuple 𝕜 S) * β (coordTuple 𝕜 T)) •
          constantFormOfExterior 𝕜 r n
            (exteriorMulOf h (coordExterior 𝕜 r p S) (coordExterior 𝕜 r q T)) := by
  conv_lhs => rw [constantForm_expansion α, constantForm_expansion β]
  rw [wedgeForm_sum_left]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [wedgeForm_smul_left, wedgeForm_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [wedgeForm_smul_right, ← smul_assoc, smul_eq_mul,
    ← constantFormOfExterior_coordExterior p S, ← constantFormOfExterior_coordExterior q T,
    wedgeForm_constantFormOfExterior]

/-- **The Leibniz rule for the exterior derivative.**  Expanding both factors in the coordinate
forms, the product rule for the coefficients produces the two terms, and moving the differential of
the second family of coefficients past the first factor produces the sign `(-1)^p`. -/
theorem extDeriv_wedgeForm (h : p + q = n) {ω : PeriodicFormSpace 𝕜 r p}
    {η : PeriodicFormSpace 𝕜 r q} (hω : Differentiable 𝕜 ω) (hη : Differentiable 𝕜 η)
    (x : Fin r → 𝕜) :
    extDeriv (fun y => wedgeForm h (ω y) (η y)) x =
      wedgeForm (by omega : p + 1 + q = n + 1) (extDeriv ω x) (η x) +
        ((-1 : 𝕜) ^ p) • wedgeForm (by omega : p + (q + 1) = n + 1) (ω x) (extDeriv η x) := by
  classical
  set f : Set.powersetCard (Fin r) p → (Fin r → 𝕜) → 𝕜 :=
    fun S y => ω y (coordTuple 𝕜 S) with hf
  set g : Set.powersetCard (Fin r) q → (Fin r → 𝕜) → 𝕜 :=
    fun T y => η y (coordTuple 𝕜 T) with hg
  have hfdiff : ∀ S, Differentiable 𝕜 (f S) := fun S => form_coeff_differentiable hω S
  have hgdiff : ∀ T, Differentiable 𝕜 (g T) := fun T => form_coeff_differentiable hη T
  set W : Set.powersetCard (Fin r) p → Set.powersetCard (Fin r) q →
      ⋀[𝕜]^n (Module.Dual 𝕜 (Fin r → 𝕜)) :=
    fun S T => exteriorMulOf h (coordExterior 𝕜 r p S) (coordExterior 𝕜 r q T) with hW
  -- the wedge product expanded in the coordinate forms
  have hexp : (fun y => wedgeForm h (ω y) (η y)) =
      fun y => ∑ S : Set.powersetCard (Fin r) p,
        ∑ T : Set.powersetCard (Fin r) q,
          (f S y * g T y) • constantFormOfExterior 𝕜 r n (W S T) := by
    funext y
    exact wedgeForm_expansion h (ω y) (η y)
  have hinnerdiff : ∀ (S : Set.powersetCard (Fin r) p) (T : Set.powersetCard (Fin r) q),
      Differentiable 𝕜 fun y => (f S y * g T y) • constantFormOfExterior 𝕜 r n (W S T) :=
    fun S T y => (((hfdiff S) y).mul ((hgdiff T) y)).smul_const _
  have houterdiff : ∀ S : Set.powersetCard (Fin r) p,
      Differentiable 𝕜 fun y => ∑ T : Set.powersetCard (Fin r) q,
        (f S y * g T y) • constantFormOfExterior 𝕜 r n (W S T) := by
    intro S y
    exact DifferentiableAt.fun_sum fun T _ => (hinnerdiff S T) y
  -- the exterior derivative of the expansion
  have hderiv : extDeriv (fun y => wedgeForm h (ω y) (η y)) x =
      ∑ S : Set.powersetCard (Fin r) p, ∑ T : Set.powersetCard (Fin r) q,
        constantFormOfExterior 𝕜 r (n + 1)
          (exteriorConsMul
            ((fderiv 𝕜 (fun y => f S y * g T y) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) (W S T)) := by
    rw [hexp, extDeriv_finset_sum Finset.univ _ houterdiff]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [extDeriv_finset_sum Finset.univ _ (hinnerdiff S)]
    refine Finset.sum_congr rfl fun T _ => ?_
    exact extDeriv_smul_constantForm (fun y => ((hfdiff S) y).mul ((hgdiff T) y)) (W S T) x
  -- the product rule for the coefficients
  have hprod : ∀ (S : Set.powersetCard (Fin r) p) (T : Set.powersetCard (Fin r) q),
      constantFormOfExterior 𝕜 r (n + 1)
          (exteriorConsMul
            ((fderiv 𝕜 (fun y => f S y * g T y) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) (W S T)) =
        (g T x) • constantFormOfExterior 𝕜 r (n + 1)
            (exteriorConsMul ((fderiv 𝕜 (f S) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) (W S T)) +
          (f S x) • constantFormOfExterior 𝕜 r (n + 1)
            (exteriorConsMul ((fderiv 𝕜 (g T) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) (W S T)) := by
    intro S T
    have hmul : fderiv 𝕜 (fun y => f S y * g T y) x =
        (f S x) • fderiv 𝕜 (g T) x + (g T x) • fderiv 𝕜 (f S) x :=
      fderiv_fun_mul ((hfdiff S) x) ((hgdiff T) x)
    rw [hmul]
    have hcoe : (((f S x) • fderiv 𝕜 (g T) x + (g T x) • fderiv 𝕜 (f S) x :
          (Fin r → 𝕜) →L[𝕜] 𝕜) : (Fin r → 𝕜) →ₗ[𝕜] 𝕜) =
        (f S x) • ((fderiv 𝕜 (g T) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) +
          (g T x) • ((fderiv 𝕜 (f S) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) := rfl
    rw [hcoe, exteriorConsMul_add_left, exteriorConsMul_smul_left, exteriorConsMul_smul_left,
      map_add, map_smul, map_smul]
    abel
  -- the first term of the Leibniz rule
  have hleft : wedgeForm (by omega : p + 1 + q = n + 1) (extDeriv ω x) (η x) =
      ∑ S : Set.powersetCard (Fin r) p, ∑ T : Set.powersetCard (Fin r) q,
        (g T x) • constantFormOfExterior 𝕜 r (n + 1)
          (exteriorConsMul ((fderiv 𝕜 (f S) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) (W S T)) := by
    rw [extDeriv_eq_sum_consMul hω x, wedgeForm_sum_left]
    refine Finset.sum_congr rfl fun S _ => ?_
    conv_lhs => rw [constantForm_expansion (η x)]
    rw [wedgeForm_sum_right]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [wedgeForm_smul_right, ← constantFormOfExterior_coordExterior q T,
      wedgeForm_constantFormOfExterior, hW]
    congr 2
    exact exteriorConsMul_mulOf h (by omega) _ _ _
  -- the second term of the Leibniz rule
  have hright : ((-1 : 𝕜) ^ p) •
        wedgeForm (by omega : p + (q + 1) = n + 1) (ω x) (extDeriv η x) =
      ∑ S : Set.powersetCard (Fin r) p, ∑ T : Set.powersetCard (Fin r) q,
        (f S x) • constantFormOfExterior 𝕜 r (n + 1)
          (exteriorConsMul ((fderiv 𝕜 (g T) x : (Fin r → 𝕜) →ₗ[𝕜] 𝕜)) (W S T)) := by
    rw [extDeriv_eq_sum_consMul hη x]
    conv_lhs => rw [constantForm_expansion (ω x)]
    rw [wedgeForm_sum_left, Finset.smul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [wedgeForm_smul_left, wedgeForm_sum_right, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    have hsign : ((-1 : 𝕜) ^ (p + p)) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [← constantFormOfExterior_coordExterior p S, wedgeForm_constantFormOfExterior, hW,
      mulOf_consMul_right h (by omega), map_smul, smul_comm, smul_smul, mul_assoc, ← pow_add,
      hsign, mul_one]
  rw [hderiv, hleft, hright, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => hprod S T

end Leibniz

end GaloisForLFunctions.HTGeometry
