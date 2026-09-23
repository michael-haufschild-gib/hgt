import GaloisForLFunctions.HTGeometry.CDGATensor

/-!
# Tensoring a map of degree one with the identity

A family of linear maps raising the degree by one, tensored with the identity on the second factor,
gives a map of tensor products raising the total degree by one.  On the second factor the same
construction carries the Koszul sign of the degree of the first.  These are the two half-maps of
which the total differential of a tensor product is the special case where the map is a
differential, and they are what a bar differential — the multiplication of two adjacent factors,
which raises the total degree by one after a shift — is built from.

* `HTGeometry.tensorLeftDegOne` : a degree-one map on the left factor.
* `HTGeometry.tensorRightDegOne` : a degree-one map on the right factor, with the Koszul sign.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R]
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]

/-- **A degree-one map on the left factor, tensored with the identity.** -/
def tensorLeftDegOne (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1)) (n : ℕ)
    (F : TensorCarrier (R := R) M N n) : TensorCarrier (R := R) M' N (n + 1) :=
  fun p =>
    match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, b), h⟩ =>
        TensorProduct.map (f a) LinearMap.id (F ⟨(a, b), by omega⟩)

@[simp] theorem tensorLeftDegOne_zero (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1)) (n b : ℕ)
    (F : TensorCarrier (R := R) M N n) (h : (0, b).1 + (0, b).2 = n + 1) :
    tensorLeftDegOne (N := N) f n F ⟨(0, b), h⟩ = 0 := rfl

@[simp] theorem tensorLeftDegOne_succ (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1)) (n a b : ℕ)
    (F : TensorCarrier (R := R) M N n) (h : (a + 1, b).1 + (a + 1, b).2 = n + 1) :
    tensorLeftDegOne (N := N) f n F ⟨(a + 1, b), h⟩
      = TensorProduct.map (f a) LinearMap.id (F ⟨(a, b), by omega⟩) := rfl

theorem tensorLeftDegOne_add (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1)) (n : ℕ)
    (F G : TensorCarrier (R := R) M N n) :
    tensorLeftDegOne (N := N) f n (F + G)
      = tensorLeftDegOne f n F + tensorLeftDegOne f n G := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rw [tensorLeftDegOne_zero]; exact (add_zero (0 : TensorProduct R (M' 0) (N b))).symm
  | succ a' =>
      show TensorProduct.map (f a') LinearMap.id ((F + G) ⟨(a', b), by omega⟩) = _
      rw [tensorCarrier_add_apply, map_add]
      rfl

theorem tensorLeftDegOne_smul (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1)) (n : ℕ) (c : R)
    (F : TensorCarrier (R := R) M N n) :
    tensorLeftDegOne (N := N) f n (c • F) = c • tensorLeftDegOne f n F := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rw [tensorLeftDegOne_zero]; exact (smul_zero c).symm
  | succ a' =>
      show TensorProduct.map (f a') LinearMap.id ((c • F) ⟨(a', b), by omega⟩) = _
      rw [tensorCarrier_smul_apply, map_smul]
      rfl

/-- The degree-one map on the left factor, as a linear map. -/
def tensorLeftDegOneₗ (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1)) (n : ℕ) :
    TensorCarrier (R := R) M N n →ₗ[R] TensorCarrier (R := R) M' N (n + 1) where
  toFun := tensorLeftDegOne f n
  map_add' := tensorLeftDegOne_add f n
  map_smul' := tensorLeftDegOne_smul f n

/-- **A degree-one map on the right factor, tensored with the identity**, with the Koszul sign of
the degree of the left factor. -/
def tensorRightDegOne (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n : ℕ)
    (F : TensorCarrier (R := R) M N n) : TensorCarrier (R := R) M N' (n + 1) :=
  fun p =>
    match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, b + 1), h⟩ =>
        ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g b) (F ⟨(a, b), by omega⟩)

@[simp] theorem tensorRightDegOne_zero (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n a : ℕ)
    (F : TensorCarrier (R := R) M N n) (h : (a, 0).1 + (a, 0).2 = n + 1) :
    tensorRightDegOne (M := M) g n F ⟨(a, 0), h⟩ = 0 := rfl

@[simp] theorem tensorRightDegOne_succ (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n a b : ℕ)
    (F : TensorCarrier (R := R) M N n) (h : (a, b + 1).1 + (a, b + 1).2 = n + 1) :
    tensorRightDegOne (M := M) g n F ⟨(a, b + 1), h⟩
      = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g b) (F ⟨(a, b), by omega⟩) := rfl

theorem tensorRightDegOne_add (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n : ℕ)
    (F G : TensorCarrier (R := R) M N n) :
    tensorRightDegOne (M := M) g n (F + G)
      = tensorRightDegOne g n F + tensorRightDegOne g n G := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rw [tensorRightDegOne_zero]; exact (add_zero (0 : TensorProduct R (M a) (N' 0))).symm
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g b')
        ((F + G) ⟨(a, b'), by omega⟩) = _
      rw [tensorCarrier_add_apply, map_add, smul_add]
      rfl

theorem tensorRightDegOne_smul (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n : ℕ) (c : R)
    (F : TensorCarrier (R := R) M N n) :
    tensorRightDegOne (M := M) g n (c • F) = c • tensorRightDegOne g n F := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rw [tensorRightDegOne_zero]; exact (smul_zero c).symm
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g b')
        ((c • F) ⟨(a, b'), by omega⟩) = _
      rw [tensorCarrier_smul_apply, map_smul, smul_comm]
      rfl

/-- The degree-one map on the right factor, as a linear map. -/
def tensorRightDegOneₗ (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n : ℕ) :
    TensorCarrier (R := R) M N n →ₗ[R] TensorCarrier (R := R) M N' (n + 1) where
  toFun := tensorRightDegOne g n
  map_add' := tensorRightDegOne_add g n
  map_smul' := tensorRightDegOne_smul g n

@[simp] theorem tensorRightDegOneₗ_zero (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n a : ℕ)
    (F : TensorCarrier (R := R) M N n) (h : (a, 0).1 + (a, 0).2 = n + 1) :
    tensorRightDegOneₗ (M := M) g n F ⟨(a, 0), h⟩ = 0 := rfl

@[simp] theorem tensorRightDegOneₗ_succ (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n a b : ℕ)
    (F : TensorCarrier (R := R) M N n) (h : (a, b + 1).1 + (a, b + 1).2 = n + 1) :
    tensorRightDegOneₗ (M := M) g n F ⟨(a, b + 1), h⟩
      = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g b) (F ⟨(a, b), by omega⟩) := rfl

/-- The right-factor construction of the zero family is zero. -/
theorem tensorRightDegOne_zero_map (n : ℕ) (F : TensorCarrier (R := R) M N n) :
    tensorRightDegOne (M := M) (fun b => (0 : N b →ₗ[R] N' (b + 1))) n F = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rw [tensorRightDegOne_zero]; rfl
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (0 : N b' →ₗ[R] N' (b' + 1))
        (F ⟨(a, b'), by omega⟩) = _
      rw [TensorProduct.map_zero_right, LinearMap.zero_apply, smul_zero]
      rfl

/-- The right-factor construction is additive in the family of maps. -/
theorem tensorRightDegOne_add_map (f g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n : ℕ)
    (F : TensorCarrier (R := R) M N n) :
    tensorRightDegOne (M := M) (fun b => f b + g b) n F
      = tensorRightDegOne (M := M) f n F + tensorRightDegOne (M := M) g n F := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rw [tensorRightDegOne_zero]; exact (add_zero (0 : TensorProduct R (M a) (N' 0))).symm
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (f b' + g b')
        (F ⟨(a, b'), by omega⟩) = _
      rw [TensorProduct.map_add_right, LinearMap.add_apply, smul_add]
      rfl

variable {N'' : ℕ → Type w} [∀ n, AddCommGroup (N'' n)] [∀ n, Module R (N'' n)]

/-- **Two degree-one maps on the right factor compose without a sign**: the two Koszul signs are the
same and cancel.  In particular the right-factor construction squares to zero whenever the maps do.
-/
theorem tensorRightDegOne_comp (f : ∀ b : ℕ, N b →ₗ[R] N' (b + 1))
    (g : ∀ b : ℕ, N' b →ₗ[R] N'' (b + 1)) (hgf : ∀ b : ℕ, (g (b + 1)).comp (f b) = 0) (n : ℕ)
    (F : TensorCarrier (R := R) M N n) :
    tensorRightDegOne (M := M) g (n + 1) (tensorRightDegOne (M := M) f n F) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rw [tensorRightDegOne_zero]; rfl
  | succ b' =>
      cases b' with
      | zero =>
          show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g 0)
            (tensorRightDegOne (M := M) f n F ⟨(a, 0), by omega⟩) = _
          rw [tensorRightDegOne_zero, map_zero, smul_zero]
          rfl
      | succ b'' =>
          show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g (b'' + 1))
            (tensorRightDegOne (M := M) f n F ⟨(a, b'' + 1), by omega⟩) = _
          have heven : ((-1 : R)) ^ (a + a) = 1 := Even.neg_one_pow ⟨a, rfl⟩
          rw [tensorRightDegOne_succ, map_smul, smul_smul, ← pow_add, heven,
            one_smul, ← LinearMap.comp_apply,
            ← TensorProduct.map_comp, LinearMap.comp_id, hgf b'',
            TensorProduct.map_zero_right, LinearMap.zero_apply]
          rfl

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R]
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]
  {N'' : ℕ → Type w} [∀ n, AddCommGroup (N'' n)] [∀ n, Module R (N'' n)]

/-- **A degree-one map on the left factor and one on the right anticommute.**  Both compose to the
same map of tensor products, and the two Koszul signs differ by one because the left map raises
exactly the degree the right map's sign reads. -/
theorem tensorLeftDegOne_tensorRightDegOne_add (f : ∀ a : ℕ, M a →ₗ[R] M' (a + 1))
    (g : ∀ b : ℕ, N b →ₗ[R] N' (b + 1)) (n : ℕ) (F : TensorCarrier (R := R) M N n) :
    tensorLeftDegOne (N := N') f (n + 1) (tensorRightDegOne (M := M) g n F)
      + tensorRightDegOne (M := M') g (n + 1) (tensorLeftDegOne (N := N) f n F) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero =>
      cases b with
      | zero => rfl
      | succ b' =>
          show tensorLeftDegOne (N := N') f (n + 1) (tensorRightDegOne (M := M) g n F)
                ⟨(0, b' + 1), h⟩
              + ((-1 : R)) ^ (0 : ℕ) • TensorProduct.map LinearMap.id (g b')
                (tensorLeftDegOne (N := N) f n F ⟨(0, b'), by omega⟩) = 0
          simp only [tensorLeftDegOne_zero, map_zero, smul_zero, add_zero]
  | succ a' =>
      cases b with
      | zero =>
          show TensorProduct.map (f a') LinearMap.id
                (tensorRightDegOne (M := M) g n F ⟨(a', 0), by omega⟩)
              + tensorRightDegOne (M := M') g (n + 1) (tensorLeftDegOne (N := N) f n F)
                ⟨(a' + 1, 0), h⟩ = 0
          simp only [tensorRightDegOne_zero, map_zero, add_zero]
      | succ b' =>
          show TensorProduct.map (f a') LinearMap.id
                (tensorRightDegOne (M := M) g n F ⟨(a', b' + 1), by omega⟩)
              + ((-1 : R)) ^ (a' + 1) • TensorProduct.map LinearMap.id (g b')
                (tensorLeftDegOne (N := N) f n F ⟨(a' + 1, b'), by omega⟩) = 0
          have hswap : ∀ W : TensorProduct R (M a') (N b'),
              TensorProduct.map (f a') (LinearMap.id (R := R) (M := N' (b' + 1)))
                  (TensorProduct.map (LinearMap.id (R := R) (M := M a')) (g b') W)
                = TensorProduct.map (LinearMap.id (R := R) (M := M' (a' + 1))) (g b')
                  (TensorProduct.map (f a') (LinearMap.id (R := R) (M := N b')) W) := by
            intro W
            rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
              ← TensorProduct.map_comp]
            simp only [LinearMap.id_comp, LinearMap.comp_id]
          rw [tensorRightDegOne_succ, tensorLeftDegOne_succ, map_smul, hswap, pow_succ, mul_comm,
            neg_one_mul, neg_smul, add_neg_cancel]

/-- **Two pairs of degree-one maps on the right factor whose composites cancel.**  The Koszul signs
are the same in both orders, so the cancellation of the composites is inherited verbatim. -/
theorem tensorRightDegOne_comp_add {N₁ N₂ : ℕ → Type w} [∀ n, AddCommGroup (N₁ n)]
    [∀ n, Module R (N₁ n)] [∀ n, AddCommGroup (N₂ n)] [∀ n, Module R (N₂ n)]
    (f₁ : ∀ b : ℕ, N b →ₗ[R] N₁ (b + 1)) (g₁ : ∀ b : ℕ, N₁ b →ₗ[R] N'' (b + 1))
    (f₂ : ∀ b : ℕ, N b →ₗ[R] N₂ (b + 1)) (g₂ : ∀ b : ℕ, N₂ b →ₗ[R] N'' (b + 1))
    (hgf : ∀ b : ℕ, (g₁ (b + 1)).comp (f₁ b) + (g₂ (b + 1)).comp (f₂ b) = 0) (n : ℕ)
    (F : TensorCarrier (R := R) M N n) :
    tensorRightDegOne (M := M) g₁ (n + 1) (tensorRightDegOne (M := M) f₁ n F)
      + tensorRightDegOne (M := M) g₂ (n + 1) (tensorRightDegOne (M := M) f₂ n F) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rfl
  | succ b' =>
      cases b' with
      | zero =>
          have h0 : (a, 0).1 + (a, 0).2 = n + 1 := by
            have h' : a + (0 + 1) = n + 1 + 1 := h
            show a + 0 = n + 1
            omega
          show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g₁ 0)
                (tensorRightDegOne (M := M) f₁ n F ⟨(a, 0), h0⟩)
              + ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g₂ 0)
                (tensorRightDegOne (M := M) f₂ n F ⟨(a, 0), h0⟩) = 0
          simp only [tensorRightDegOne_zero, map_zero, smul_zero, add_zero]
      | succ b'' =>
          have h0 : (a, b'' + 1).1 + (a, b'' + 1).2 = n + 1 := by
            have h' : a + (b'' + 1 + 1) = n + 1 + 1 := h
            show a + (b'' + 1) = n + 1
            omega
          show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g₁ (b'' + 1))
                (tensorRightDegOne (M := M) f₁ n F ⟨(a, b'' + 1), h0⟩)
              + ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (g₂ (b'' + 1))
                (tensorRightDegOne (M := M) f₂ n F ⟨(a, b'' + 1), h0⟩) = 0
          have heven : ((-1 : R)) ^ (a + a) = 1 := Even.neg_one_pow ⟨a, rfl⟩
          have hcomp : ∀ W : TensorProduct R (M a) (N b''),
              TensorProduct.map (LinearMap.id (R := R) (M := M a)) (g₁ (b'' + 1))
                  (TensorProduct.map (LinearMap.id (R := R) (M := M a)) (f₁ b'') W)
                + TensorProduct.map (LinearMap.id (R := R) (M := M a)) (g₂ (b'' + 1))
                  (TensorProduct.map (LinearMap.id (R := R) (M := M a)) (f₂ b'') W) = 0 := by
            intro W
            rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
              ← TensorProduct.map_comp, LinearMap.comp_id,
              ← LinearMap.add_apply, ← TensorProduct.map_add_right, hgf b'',
              TensorProduct.map_zero_right, LinearMap.zero_apply]
          rw [tensorRightDegOne_succ, tensorRightDegOne_succ, map_smul, map_smul,
            smul_smul, smul_smul, ← pow_add, heven, one_smul, one_smul]
          exact hcomp _

end GaloisForLFunctions.HTGeometry
