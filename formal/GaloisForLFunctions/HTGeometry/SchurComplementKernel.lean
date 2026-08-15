import Mathlib

/-!
# The Schur complement carries the kernel of a block operator

A block operator on a direct sum `F ⊕ H` whose lower-right block is invertible has the same kernel
as the Schur complement `S = A - B D⁻¹ C` on the first summand: projection to `F` is a linear
isomorphism from the kernel of the block operator onto the kernel of `S`, with explicit inverse
`x ↦ (x, -D⁻¹ C x)`.

Only invertibility of the boundary block is used.  When the first summand is finite free over a
domain the kernel statement becomes a determinant statement: the block operator is injective exactly
when the Schur complement has nonzero determinant — a finite determinant whose every entry carries
the full boundary inverse.
-/

namespace GaloisForLFunctions.HTGeometry

open LinearMap

variable {R F H : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]

/-- The block operator on `F × H` assembled from four blocks. -/
def schurBlockOperator (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H) (D : H →ₗ[R] H) :
    (F × H) →ₗ[R] (F × H) :=
  LinearMap.prod (A.coprod B) (C.coprod D)

@[simp] theorem schurBlockOperator_apply (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H)
    (D : H →ₗ[R] H) (p : F × H) :
    schurBlockOperator A B C D p = (A p.1 + B p.2, C p.1 + D p.2) := rfl

/-- The Schur complement of the boundary block, written with an explicit inverse of that block. -/
def schurComplement (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H) (Dinv : H →ₗ[R] H) :
    F →ₗ[R] F :=
  A - B ∘ₗ Dinv ∘ₗ C

@[simp] theorem schurComplement_apply (A : F →ₗ[R] F) (B : H →ₗ[R] F) (C : F →ₗ[R] H)
    (Dinv : H →ₗ[R] H) (x : F) :
    schurComplement A B C Dinv x = A x - B (Dinv (C x)) := rfl

variable {A : F →ₗ[R] F} {B : H →ₗ[R] F} {C : F →ₗ[R] H} {D Dinv : H →ₗ[R] H}

/-- **Equations (6)–(7).**  A vector is in the kernel of the block operator exactly when its first
component is in the kernel of the Schur complement and its second component is the forced boundary
response. -/
theorem schurBlockOperator_apply_eq_zero_iff (hD : ∀ h, D (Dinv h) = h) (hD' : ∀ h, Dinv (D h) = h)
    (p : F × H) :
    schurBlockOperator A B C D p = 0 ↔
      schurComplement A B C Dinv p.1 = 0 ∧ p.2 = -(Dinv (C p.1)) := by
  constructor
  · intro h
    have h1 : A p.1 + B p.2 = 0 := congrArg Prod.fst h
    have h2 : C p.1 + D p.2 = 0 := congrArg Prod.snd h
    have hsnd : p.2 = -(Dinv (C p.1)) := by
      have hDp : D p.2 = -(C p.1) := by linear_combination (norm := module) h2
      have := congrArg Dinv hDp
      rwa [hD' p.2, map_neg] at this
    refine ⟨?_, hsnd⟩
    have hDinv : Dinv (C p.1) = -p.2 := by rw [hsnd]; simp
    rw [schurComplement_apply, hDinv, map_neg]
    linear_combination (norm := module) h1
  · rintro ⟨h1, h2⟩
    have hfst : A p.1 + B p.2 = 0 := by
      rw [h2, map_neg]
      rw [schurComplement_apply] at h1
      linear_combination (norm := module) h1
    have hsnd : C p.1 + D p.2 = 0 := by
      rw [h2, map_neg, hD]
      simp
    ext
    · simpa using hfst
    · simpa using hsnd

/-- **Equations (3)–(4).**  Projection to the first summand is a linear isomorphism from the kernel
of the block operator onto the kernel of the Schur complement, with inverse `x ↦ (x, -D⁻¹ C x)`. -/
def kerSchurBlockOperatorEquivKerSchur (hD : ∀ h, D (Dinv h) = h) (hD' : ∀ h, Dinv (D h) = h) :
    LinearMap.ker (schurBlockOperator A B C D) ≃ₗ[R] LinearMap.ker (schurComplement A B C Dinv) where
  toFun p := ⟨p.1.1, ((schurBlockOperator_apply_eq_zero_iff hD hD' p.1).1 p.2).1⟩
  map_add' p q := rfl
  map_smul' r p := rfl
  invFun x :=
    ⟨(x.1, -(Dinv (C x.1))),
      (schurBlockOperator_apply_eq_zero_iff hD hD' _).2 ⟨x.2, rfl⟩⟩
  left_inv := by
    rintro ⟨p, hp⟩
    have h := ((schurBlockOperator_apply_eq_zero_iff hD hD' p).1 hp).2
    ext
    · rfl
    · simpa using h.symm
  right_inv := by
    rintro ⟨x, hx⟩
    rfl

/-- The block operator is injective exactly when the Schur complement is. -/
theorem ker_schurBlockOperator_eq_bot_iff (hD : ∀ h, D (Dinv h) = h) (hD' : ∀ h, Dinv (D h) = h) :
    LinearMap.ker (schurBlockOperator A B C D) = ⊥ ↔
      LinearMap.ker (schurComplement A B C Dinv) = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hmem : ((x, -(Dinv (C x))) : F × H) ∈ LinearMap.ker (schurBlockOperator A B C D) :=
      (schurBlockOperator_apply_eq_zero_iff hD hD' _).2 ⟨hx, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact congrArg Prod.fst hmem
  · intro h
    rw [Submodule.eq_bot_iff]
    intro p hp
    obtain ⟨hfst, hsnd⟩ := (schurBlockOperator_apply_eq_zero_iff hD hD' p).1 hp
    rw [Submodule.eq_bot_iff] at h
    have hx : p.1 = 0 := h _ hfst
    have : p.2 = 0 := by rw [hsnd, hx]; simp
    exact Prod.ext hx this

/-- **Equation (5).**  With a finite free first summand over a domain, the block operator is
injective exactly when the Schur complement has nonzero determinant. -/
theorem ker_schurBlockOperator_eq_bot_iff_det_ne_zero [IsDomain R] [Module.Free R F]
    [Module.Finite R F] (hD : ∀ h, D (Dinv h) = h) (hD' : ∀ h, Dinv (D h) = h) :
    LinearMap.ker (schurBlockOperator A B C D) = ⊥ ↔
      LinearMap.det (schurComplement A B C Dinv) ≠ 0 := by
  rw [ker_schurBlockOperator_eq_bot_iff hD hD', Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not]

end GaloisForLFunctions.HTGeometry
