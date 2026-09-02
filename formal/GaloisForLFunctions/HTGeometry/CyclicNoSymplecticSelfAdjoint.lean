import Mathlib

/-!
# No symplectic self-adjoint structure on a cyclic space; doubling is free

Let `K` be an endomorphism of a vector space `V` over a field of characteristic zero, and let `B`
be a bilinear form for which `K` is self-adjoint, `B (K x) y = B x (K y)`.

* If `K` has a cyclic vector `g` (every vector is `p(K) g` for a polynomial `p`), then `B` is
  symmetric: `B (p(K) g) (q(K) g) = B g ((pq)(K) g)` is symmetric in `p, q`.  Consequently an
  alternating such `B` vanishes, and no nondegenerate alternating `K`-self-adjoint form exists on
  a nonzero space with a cyclic vector.  In particular a symplectically self-adjoint endomorphism
  has no cyclic vector, and the canonical analytic model of a divisor at a point, the cyclic module
  `ℂ[z]/(z − w)^m` with multiplication by `z`, carries no symplectic self-adjoint structure,
  whatever the parity of `m`.

* Conversely, given any nondegenerate symmetric `K`-self-adjoint form `S` on `V`, the doubled
  form `ω((x₁,x₂),(y₁,y₂)) = S x₁ y₂ − S x₂ y₁` on `V × V` is nondegenerate, alternating, and
  `K ⊕ K`-self-adjoint.  Doubling any block therefore produces a symplectic realization for free,
  so such realizations of doubled models carry no information about the original block.

* A pairing with values in `{±1}` that is skew, `b x y · b y x = 1`, is symmetric.  Quadratic
  symbols therefore define symmetric, not alternating, forms.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

section Cyclic

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Self-adjointness for `K` propagates to every power of `K`. -/
theorem bilin_pow_comm (B : LinearMap.BilinForm k V) (K : Module.End k V)
    (hK : ∀ x y, B (K x) y = B x (K y)) (n : ℕ) (x y : V) :
    B ((K ^ n) x) y = B x ((K ^ n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hK, ih, ← Module.End.mul_apply,
      ← Module.End.mul_apply, ← pow_succ, ← pow_succ']

/-- Self-adjointness for `K` propagates to every polynomial in `K`. -/
theorem bilin_aeval_comm (B : LinearMap.BilinForm k V) (K : Module.End k V)
    (hK : ∀ x y, B (K x) y = B x (K y)) (p : k[X]) (x y : V) :
    B ((aeval K p) x) y = B x ((aeval K p) y) := by
  rw [aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilin_pow_comm B K hK i]

/-- `g` is a cyclic vector for `K`: every vector is a polynomial in `K` applied to `g`. -/
def IsCyclicVector (K : Module.End k V) (g : V) : Prop :=
  ∀ v : V, ∃ p : k[X], (aeval K p) g = v

/-- **On a space with a cyclic vector every `K`-self-adjoint bilinear form is symmetric.** -/
theorem bilin_symm_of_cyclic (B : LinearMap.BilinForm k V) (K : Module.End k V)
    (hK : ∀ x y, B (K x) y = B x (K y)) {g : V} (hg : IsCyclicVector K g) (x y : V) :
    B x y = B y x := by
  obtain ⟨p, rfl⟩ := hg x
  obtain ⟨q, rfl⟩ := hg y
  calc B ((aeval K p) g) ((aeval K q) g)
      = B g ((aeval K p) ((aeval K q) g)) := bilin_aeval_comm B K hK p _ _
    _ = B g ((aeval K (p * q)) g) := by rw [map_mul, Module.End.mul_apply]
    _ = B g ((aeval K (q * p)) g) := by rw [mul_comm]
    _ = B g ((aeval K q) ((aeval K p) g)) := by rw [map_mul, Module.End.mul_apply]
    _ = B ((aeval K q) g) ((aeval K p) g) := (bilin_aeval_comm B K hK q _ _).symm

/-- An alternating `K`-self-adjoint form on a space with a cyclic vector vanishes. -/
theorem bilin_eq_zero_of_isAlt_of_cyclic [CharZero k] (B : LinearMap.BilinForm k V)
    (K : Module.End k V) (hK : ∀ x y, B (K x) y = B x (K y)) {g : V}
    (hg : IsCyclicVector K g) (halt : B.IsAlt) : B = 0 := by
  ext x y
  have h1 : B x y = B y x := bilin_symm_of_cyclic B K hK hg x y
  have h2 : -B x y = B y x := LinearMap.IsAlt.neg halt x y
  have h3 : (2 : k) * B x y = 0 := by linear_combination h1 - h2
  simpa using (mul_eq_zero.mp h3).resolve_left two_ne_zero

/-- **No symplectic self-adjoint structure on a nonzero space with a cyclic vector.** -/
theorem not_symplectic_selfAdjoint_of_cyclic [CharZero k] [Nontrivial V]
    (B : LinearMap.BilinForm k V) (K : Module.End k V) {g : V} (hg : IsCyclicVector K g) :
    ¬ (B.Nondegenerate ∧ B.IsAlt ∧ ∀ x y, B (K x) y = B x (K y)) := by
  rintro ⟨hnd, halt, hK⟩
  have h0 := bilin_eq_zero_of_isAlt_of_cyclic B K hK hg halt
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hnd.1 v fun w => by simp [h0])

/-- **A symplectically self-adjoint endomorphism has no cyclic vector.** -/
theorem not_isCyclicVector_of_symplectic_selfAdjoint [CharZero k] [Nontrivial V]
    (B : LinearMap.BilinForm k V) (hnd : B.Nondegenerate) (halt : B.IsAlt)
    (K : Module.End k V) (hK : ∀ x y, B (K x) y = B x (K y)) (g : V) :
    ¬ IsCyclicVector K g :=
  fun hg => not_symplectic_selfAdjoint_of_cyclic B K hg ⟨hnd, halt, hK⟩

end Cyclic

section Doubling

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The doubled form `ω((x₁,x₂),(y₁,y₂)) = S x₁ y₂ − S x₂ y₁` on `V × V`. -/
def doubledForm (S : LinearMap.BilinForm k V) : LinearMap.BilinForm k (V × V) :=
  LinearMap.mk₂ k (fun p q => S p.1 q.2 - S p.2 q.1)
    (by
      intro p p' q
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring)
    (by
      intro c p q
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (by
      intro p q q'
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      ring)
    (by
      intro c p q
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]
      ring)

theorem doubledForm_apply (S : LinearMap.BilinForm k V) (p q : V × V) :
    doubledForm S p q = S p.1 q.2 - S p.2 q.1 := by
  rw [doubledForm, LinearMap.mk₂_apply]

/-- The doubled form of a symmetric form is alternating. -/
theorem doubledForm_isAlt (S : LinearMap.BilinForm k V) (hS : ∀ x y, S x y = S y x) :
    (doubledForm S).IsAlt := by
  intro p
  rw [doubledForm_apply, hS p.1 p.2, sub_self]

/-- The doubled form of a nondegenerate form is nondegenerate. -/
theorem doubledForm_nondegenerate (S : LinearMap.BilinForm k V) (hnd : S.Nondegenerate) :
    (doubledForm S).Nondegenerate := by
  refine ⟨fun p hp => ?_, fun q hq => ?_⟩
  · have h1 : p.1 = 0 := by
      refine hnd.1 p.1 fun w => ?_
      have := hp (0, w)
      simpa [doubledForm_apply] using this
    have h2 : p.2 = 0 := by
      refine hnd.1 p.2 fun w => ?_
      have := hp (w, 0)
      simpa [doubledForm_apply] using this
    exact Prod.ext h1 h2
  · have h1 : q.1 = 0 := by
      refine hnd.2 q.1 fun w => ?_
      have := hq (0, w)
      simpa [doubledForm_apply] using this
    have h2 : q.2 = 0 := by
      refine hnd.2 q.2 fun w => ?_
      have := hq (w, 0)
      simpa [doubledForm_apply] using this
    exact Prod.ext h1 h2

/-- The diagonal endomorphism `K ⊕ K` is self-adjoint for the doubled form whenever `K` is
self-adjoint for `S`. -/
theorem doubledForm_selfAdjoint (S : LinearMap.BilinForm k V) (K : Module.End k V)
    (hK : ∀ x y, S (K x) y = S x (K y)) (p q : V × V) :
    doubledForm S (K.prodMap K p) q = doubledForm S p (K.prodMap K q) := by
  simp only [doubledForm_apply, LinearMap.prodMap_apply, hK]

/-- **Doubling is free.**  Any nondegenerate symmetric `K`-self-adjoint form on `V` yields a
nondegenerate alternating form on `V × V` for which `K ⊕ K` is self-adjoint. -/
theorem exists_symplectic_selfAdjoint_doubled (S : LinearMap.BilinForm k V)
    (hnd : S.Nondegenerate) (hS : ∀ x y, S x y = S y x) (K : Module.End k V)
    (hK : ∀ x y, S (K x) y = S x (K y)) :
    ∃ ω : LinearMap.BilinForm k (V × V), ω.Nondegenerate ∧ ω.IsAlt ∧
      ∀ p q, ω (K.prodMap K p) q = ω p (K.prodMap K q) :=
  ⟨doubledForm S, doubledForm_nondegenerate S hnd, doubledForm_isAlt S hS,
    doubledForm_selfAdjoint S K hK⟩

end Doubling

section Sign

/-- A skew pairing with values in `{±1}` is symmetric. -/
theorem symm_of_skew_units {α : Type*} (b : α → α → ℤˣ) (h : ∀ x y, b x y * b y x = 1)
    (x y : α) : b x y = b y x := by
  have h1 : b y x = (b x y)⁻¹ := (inv_eq_of_mul_eq_one_right (h x y)).symm
  have h2 : (b x y)⁻¹ = b x y := by
    rcases Int.units_eq_one_or (b x y) with h | h <;> simp [h]
  rw [h1, h2]

end Sign

end GaloisForLFunctions.HTGeometry
