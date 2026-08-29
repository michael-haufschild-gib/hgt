import GaloisForLFunctions.HTGeometry.GeometricallyReducedCharZero

/-!
# Tensoring with a fraction ring preserves being a domain

Let `k` be a field, `P` a `k`-algebra which is a domain, `Q` a fraction ring of `P`, and `F` a
nontrivial `k`-algebra with `F ⊗[k] P` a domain.  Then `F ⊗[k] Q` is a domain.

This is the purely transcendental step of "reduced stays reduced after base change" in
characteristic zero: for `P` a polynomial ring, `Q` is the field of rational functions, and the
lemma says the base change of a domain along a purely transcendental extension is again a domain.

The proof is denominator clearing.  Every element of `F ⊗[k] Q` becomes an element of the image of
`F ⊗[k] P` after multiplication by `1 ⊗ q` for a single nonzero `q ∈ P`, and that factor is a unit.
So the canonical map into the fraction field of `F ⊗[k] P` is injective, and a subring of a field is
a domain.

* `tensorFractionHom` — the canonical map to the fraction field of `F ⊗[k] P`;
* `exists_denominator_clears` — denominator clearing;
* `isDomain_tensor_of_isFractionRing`.
-/

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {k : Type*} [Field k]
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra k P]
variable {Q : Type*} [CommRing Q] [Algebra k Q] [Algebra P Q] [IsScalarTower k P Q]
  [IsFractionRing P Q]
variable {F : Type*} [CommRing F] [Nontrivial F] [Algebra k F]

/-- The base-change map `F ⊗[k] P → F ⊗[k] Q`. -/
noncomputable def tensorBaseHom : (F ⊗[k] P) →ₐ[k] (F ⊗[k] Q) :=
  Algebra.TensorProduct.map (AlgHom.id k F) (IsScalarTower.toAlgHom k P Q)

@[simp] theorem tensorBaseHom_tmul (a : F) (p : P) :
    (tensorBaseHom (k := k) (P := P) (Q := Q) (F := F)) (a ⊗ₜ[k] p)
      = a ⊗ₜ[k] (algebraMap P Q p) := rfl

/-- **Denominator clearing.**  A single nonzero denominator carries any element of `F ⊗[k] Q` into
the image of `F ⊗[k] P`. -/
theorem exists_denominator_clears (ξ : F ⊗[k] Q) :
    ∃ q : P, q ≠ 0 ∧ ∃ η : F ⊗[k] P,
      ((1 : F) ⊗ₜ[k] (algebraMap P Q q)) * ξ = tensorBaseHom η := by
  classical
  induction ξ using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul a x =>
      obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.mk'_surjective (nonZeroDivisors P) x
      have hq : (q : P) ≠ 0 := nonZeroDivisors.ne_zero q.2
      refine ⟨(q : P), hq, a ⊗ₜ[k] p, ?_⟩
      have hx : (algebraMap P Q (q : P)) * x = algebraMap P Q p := by
        rw [← hpq, mul_comm]
        exact IsLocalization.mk'_spec Q p q
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hx, tensorBaseHom_tmul]
  | add x y hx hy =>
      obtain ⟨q₁, hq₁, η₁, h₁⟩ := hx
      obtain ⟨q₂, hq₂, η₂, h₂⟩ := hy
      refine ⟨q₁ * q₂, mul_ne_zero hq₁ hq₂,
        ((1 : F) ⊗ₜ[k] q₂) * η₁ + ((1 : F) ⊗ₜ[k] q₁) * η₂, ?_⟩
      have hmul : ((1 : F) ⊗ₜ[k] (algebraMap P Q (q₁ * q₂)))
          = ((1 : F) ⊗ₜ[k] (algebraMap P Q q₁)) * ((1 : F) ⊗ₜ[k] (algebraMap P Q q₂)) := by
        rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have hsplit : ((1 : F) ⊗ₜ[k] (algebraMap P Q (q₁ * q₂))) * (x + y)
          = ((1 : F) ⊗ₜ[k] (algebraMap P Q q₂)) *
              (((1 : F) ⊗ₜ[k] (algebraMap P Q q₁)) * x)
            + ((1 : F) ⊗ₜ[k] (algebraMap P Q q₁)) *
              (((1 : F) ⊗ₜ[k] (algebraMap P Q q₂)) * y) := by
        rw [hmul]; ring
      rw [hsplit, h₁, h₂, map_add, map_mul, map_mul, tensorBaseHom_tmul, tensorBaseHom_tmul]

/-- The base-change map is injective, because `P → Q` is and `F` is flat over the field `k`. -/
theorem tensorBaseHom_injective :
    Function.Injective (tensorBaseHom (k := k) (P := P) (Q := Q) (F := F)) := by
  have hPQ : Function.Injective (algebraMap P Q) := IsFractionRing.injective P Q
  have hlin : Function.Injective
      (LinearMap.lTensor F (IsScalarTower.toAlgHom k P Q).toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hPQ
  have hfun : ⇑(tensorBaseHom (k := k) (P := P) (Q := Q) (F := F))
      = ⇑(LinearMap.lTensor F (IsScalarTower.toAlgHom k P Q).toLinearMap) := by
    funext ξ
    induction ξ using TensorProduct.induction_on with
    | zero => simp
    | tmul a p => simp [tensorBaseHom]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hfun]
  exact hlin

/-- **Tensoring with a fraction ring preserves being a domain.** -/
theorem isDomain_tensor_of_isFractionRing [IsDomain (F ⊗[k] P)] : IsDomain (F ⊗[k] Q) := by
  classical
  have hinj := tensorBaseHom_injective (k := k) (P := P) (Q := Q) (F := F)
  have hnontriv : Nontrivial (F ⊗[k] Q) := by
    by_contra hcon
    have hsub : Subsingleton (F ⊗[k] Q) := not_nontrivial_iff_subsingleton.mp hcon
    have : Subsingleton (F ⊗[k] P) := ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    exact (not_subsingleton (F ⊗[k] P)) this
  haveI := hnontriv
  have hunit : ∀ q : P, q ≠ 0 → IsUnit ((1 : F) ⊗ₜ[k] (algebraMap P Q q)) := by
    intro q hq
    obtain ⟨u, hu⟩ := IsUnit.exists_right_inv
      (IsLocalization.map_units (M := nonZeroDivisors P) Q ⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩)
    refine isUnit_iff_exists_inv.mpr ⟨(1 : F) ⊗ₜ[k] u, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, show (algebraMap P Q q) * u = 1 from hu]
    rfl
  haveI : NoZeroDivisors (F ⊗[k] Q) := by
   constructor
   intro ξ ζ hprod
   obtain ⟨q₁, hq₁, η₁, h₁⟩ := exists_denominator_clears (k := k) (P := P) (Q := Q) (F := F) ξ
   obtain ⟨q₂, hq₂, η₂, h₂⟩ := exists_denominator_clears (k := k) (P := P) (Q := Q) (F := F) ζ
   have hmulzero : tensorBaseHom (k := k) (P := P) (Q := Q) (F := F) (η₁ * η₂) = 0 := by
     rw [map_mul, ← h₁, ← h₂]
     calc ((1 : F) ⊗ₜ[k] (algebraMap P Q q₁)) * ξ * (((1 : F) ⊗ₜ[k] (algebraMap P Q q₂)) * ζ)
         = ((1 : F) ⊗ₜ[k] (algebraMap P Q q₁)) * ((1 : F) ⊗ₜ[k] (algebraMap P Q q₂)) * (ξ * ζ) := by
           ring
       _ = 0 := by rw [hprod, mul_zero]
   have hzero : η₁ * η₂ = 0 := hinj (by rw [hmulzero, map_zero])
   rcases mul_eq_zero.mp hzero with h | h
   · left
     have hξ : ((1 : F) ⊗ₜ[k] (algebraMap P Q q₁)) * ξ = 0 := by rw [h₁, h, map_zero]
     obtain ⟨u, hu⟩ := hunit q₁ hq₁
     have := congrArg (fun z => (↑u⁻¹ : F ⊗[k] Q) * z) hξ
     simp only [mul_zero] at this
     rw [← this, ← mul_assoc, ← hu, u.inv_mul, one_mul]
   · right
     have hζ : ((1 : F) ⊗ₜ[k] (algebraMap P Q q₂)) * ζ = 0 := by rw [h₂, h, map_zero]
     obtain ⟨u, hu⟩ := hunit q₂ hq₂
     have := congrArg (fun z => (↑u⁻¹ : F ⊗[k] Q) * z) hζ
     simp only [mul_zero] at this
     rw [← this, ← mul_assoc, ← hu, u.inv_mul, one_mul]

  exact NoZeroDivisors.to_isDomain _

end GaloisForLFunctions.HTGeometry
