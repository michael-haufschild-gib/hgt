import GaloisForLFunctions.HTGeometry.CDGATensorAlgebra

/-!
# Functoriality of the tensor product of algebras

A pair of morphisms of commutative differential graded algebras induces one on the tensor product.
Multiplicativity is checked one splitting at a time, where it is the multiplicativity of the two
morphisms and the fact that the Koszul sign depends only on degrees; compatibility with the
differential is inherited from the module-level comparison, the external differential being
`tensorD` of two modules.

* `HTGeometry.tensorAlgMapₗ` : the degreewise map.
* `HTGeometry.tensorCDGAMap` : the induced morphism of tensor products.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {X' : ℕ → Type w} [∀ n, AddCommGroup (X' n)] [∀ n, Module R (X' n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  {Y' : ℕ → Type w} [∀ n, AddCommGroup (Y' n)] [∀ n, Module R (Y' n)]
  {A : CDGAStructure R X} {A' : CDGAStructure R X'}
  {B : CDGAStructure R Y} {B' : CDGAStructure R Y'}

/-- The degreewise map induced on the graded tensor product. -/
noncomputable def tensorAlgMapₗ (φ : CDGAHom A A') (ψ : CDGAHom B B') (n : ℕ) :
    TensorCarrier (R := R) X Y n →ₗ[R] TensorCarrier (R := R) X' Y' n where
  toFun f := fun p => TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2) (f p)
  map_add' f g := by
    funext p
    show TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2) (f p + g p) = _
    rw [map_add]
    rfl
  map_smul' c f := by
    funext p
    show TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2) (c • f p) = _
    rw [map_smul]
    rfl

@[simp] theorem tensorAlgMapₗ_apply (φ : CDGAHom A A') (ψ : CDGAHom B B') (n : ℕ)
    (f : TensorCarrier (R := R) X Y n) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    tensorAlgMapₗ φ ψ n f p = TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2) (f p) := rfl

/-- **The Koszul product is natural.** -/
theorem tensorPairₗ_naturality (φ : CDGAHom A A') (ψ : CDGAHom B B')
    {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (z : TensorProduct R (X a₁) (Y a₂)) (w : TensorProduct R (X b₁) (Y b₂)) :
    TensorProduct.map (φ.mapₗ n₁) (ψ.mapₗ n₂) (tensorPairₗ A B h₁ h₂ z w)
      = tensorPairₗ A' B' h₁ h₂
        (TensorProduct.map (φ.mapₗ a₁) (ψ.mapₗ a₂) z)
        (TensorProduct.map (φ.mapₗ b₁) (ψ.mapₗ b₂) w) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ y₁ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x₂ y₂ =>
          rw [tensorPairₗ_tmul, map_smul, TensorProduct.map_tmul, TensorProduct.map_tmul,
            TensorProduct.map_tmul, tensorPairₗ_tmul]
          show ((-1 : R)) ^ (a₂ * b₁) •
              (φ.toFun n₁ (A.mul h₁ x₁ x₂) ⊗ₜ[R] ψ.toFun n₂ (B.mul h₂ y₁ y₂))
            = ((-1 : R)) ^ (a₂ * b₁) •
              (A'.mul h₁ (φ.toFun a₁ x₁) (φ.toFun b₁ x₂) ⊗ₜ[R]
                B'.mul h₂ (ψ.toFun a₂ y₁) (ψ.toFun b₂ y₂))
          rw [φ.map_mul h₁ x₁ x₂, ψ.map_mul h₂ y₁ y₂]
      | add w w' hw hw' => simp only [map_add, hw, hw']
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- The induced map is multiplicative. -/
theorem tensorAlgMapₗ_mul (φ : CDGAHom A A') (ψ : CDGAHom B B') {a b n : ℕ} (h : a + b = n)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorAlgMapₗ φ ψ n (tensorAlgMul A B h f g)
      = tensorAlgMul A' B' h (tensorAlgMapₗ φ ψ a f) (tensorAlgMapₗ φ ψ b g) := by
  funext p
  show TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2)
      (∑ rs : Splitting a b p, splittingTerm A B f g rs)
    = ∑ rs : Splitting a b p, splittingTerm A' B' (tensorAlgMapₗ φ ψ a f) (tensorAlgMapₗ φ ψ b g) rs
  rw [map_sum]
  refine Finset.sum_congr rfl fun rs _ => ?_
  exact tensorPairₗ_naturality φ ψ rs.2.1 rs.2.2 (f rs.1.1) (g rs.1.2)

/-- The induced map commutes with the external differential. -/
theorem tensorAlgMapₗ_extTensorD (φ : CDGAHom A A') (ψ : CDGAHom B B') (n : ℕ)
    (f : TensorCarrier (R := R) X Y n) :
    tensorAlgMapₗ φ ψ (n + 1) (extTensorD A B n f)
      = extTensorD A' B' n (tensorAlgMapₗ φ ψ n f) := by
  funext p
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
  show TensorProduct.map (φ.mapₗ p₁) (ψ.mapₗ p₂)
      (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n f ⟨(p₁, p₂), hp⟩
        + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n f ⟨(p₁, p₂), hp⟩)
    = tensorDL (CDGAStructure.selfModule A') (zeroActModule (A := A') B') n
        (tensorAlgMapₗ φ ψ n f) ⟨(p₁, p₂), hp⟩
      + tensorDR (CDGAStructure.selfModule A') (zeroActModule (A := A') B') n
        (tensorAlgMapₗ φ ψ n f) ⟨(p₁, p₂), hp⟩
  rw [map_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · cases p₁ with
    | zero => rw [tensorDL_zero, tensorDL_zero, map_zero]
    | succ α =>
        have hq : (α, p₂).1 + (α, p₂).2 = n := by simp only at hp ⊢; omega
        rw [tensorDL_succ, tensorDL_succ]
        show TensorProduct.map (φ.mapₗ (α + 1)) (ψ.mapₗ p₂)
            (TensorProduct.map (A.dₗ α) LinearMap.id (f ⟨(α, p₂), hq⟩))
          = TensorProduct.map (A'.dₗ α) LinearMap.id
            (TensorProduct.map (φ.mapₗ α) (ψ.mapₗ p₂) (f ⟨(α, p₂), hq⟩))
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
          ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
        refine congrArg (fun L : X α →ₗ[R] X' (α + 1) =>
          (TensorProduct.map L (ψ.mapₗ p₂)) (f ⟨(α, p₂), hq⟩)) ?_
        exact LinearMap.ext fun x => φ.map_d α x
  · cases p₂ with
    | zero => rw [tensorDR_zero, tensorDR_zero, map_zero]
    | succ β =>
        have hq : (p₁, β).1 + (p₁, β).2 = n := by simp only at hp ⊢; omega
        rw [tensorDR_succ, tensorDR_succ, map_smul]
        refine congrArg (fun z => ((-1 : R)) ^ p₁ • z) ?_
        show TensorProduct.map (φ.mapₗ p₁) (ψ.mapₗ (β + 1))
            (TensorProduct.map LinearMap.id (B.dₗ β) (f ⟨(p₁, β), hq⟩))
          = TensorProduct.map LinearMap.id (B'.dₗ β)
            (TensorProduct.map (φ.mapₗ p₁) (ψ.mapₗ β) (f ⟨(p₁, β), hq⟩))
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
          ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
        refine congrArg (fun L : Y β →ₗ[R] Y' (β + 1) =>
          (TensorProduct.map (φ.mapₗ p₁) L) (f ⟨(p₁, β), hq⟩)) ?_
        exact LinearMap.ext fun y => ψ.map_d β y

/-- **The tensor product of algebras is functorial.** -/
noncomputable def tensorCDGAMap (φ : CDGAHom A A') (ψ : CDGAHom B B') :
    CDGAHom (tensorCDGA A B) (tensorCDGA A' B') where
  toFun n f := tensorAlgMapₗ φ ψ n f
  map_add n f g := map_add (tensorAlgMapₗ φ ψ n) f g
  map_smul n c f := map_smul (tensorAlgMapₗ φ ψ n) c f
  map_mul h x y := tensorAlgMapₗ_mul φ ψ h x y
  map_d n f := tensorAlgMapₗ_extTensorD φ ψ n f

end GaloisForLFunctions.HTGeometry
