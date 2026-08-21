import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The co-Lie module is `e^* Ω¹`

Suzuki defines the Hodge bundle of a group scheme as the pullback of `Ω¹` by the zero section,
`ω_𝒜 = e^* Ω¹_{𝒜/X}`.  For an affine group scheme `Spec A` over `R` with augmentation ideal `I`
this file identifies that with the co-Lie module built in `AffineGroupSchemeCoLie`:

`Ω[A⁄R] / I·Ω[A⁄R]  ≅  I / I²  =  ω_A`,

as `AffineGroupScheme.coLieEquivKaehlerQuotient`.  The maps are `D a ↦ d a` and
`x ↦ [D x]` for `x ∈ I`.

The key structural fact is that the `A`-module structure on `I/I²` is *through the counit*
(`AffineGroupScheme.smul_coLie`), which is what makes `d` an `R`-derivation of `A` into `I/I²` and
so makes it factor through Kähler differentials.
-/

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

open Coalgebra Bialgebra Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

/-- **The `A`-action on the co-Lie module is through the counit.** -/
theorem smul_coLie (a : A) (m : coLie R A) : a • m = (counit a : R) • m := by
  obtain ⟨x, rfl⟩ := (augIdeal R A).toCotangent_surjective m
  rw [← LinearMap.map_smul (augIdeal R A).toCotangent a x,
    ← LinearMap.map_smul_of_tower (augIdeal R A).toCotangent (counit a : R) x]
  refine (Ideal.toCotangent_eq _).mpr ?_
  have hcoe : ((a • x : augIdeal R A) : A) - (((counit a : R) • x : augIdeal R A) : A)
      = (a - algebraMap R A (counit a : R)) * (x : A) := by
    rw [SetLike.val_smul, Submodule.coe_smul_of_tower, smul_eq_mul, Algebra.smul_def]
    ring
  rw [hcoe, pow_two]
  exact Ideal.mul_mem_mul (sub_algebraMap_counit_mem a) x.2

/-- The universal differential as an `R`-derivation of `A` into the co-Lie module. -/
noncomputable def dDerivation : Derivation R A (coLie R A) :=
  Derivation.mk' (d R A) fun a b => by
    rw [d_mul, smul_coLie a (d R A b), smul_coLie b (d R A a)]

@[simp] theorem dDerivation_apply (a : A) : dDerivation (R := R) (A := A) a = d R A a := rfl

/-- The map `Ω[A⁄R] → ω_A` induced by the universal differential at the identity. -/
noncomputable def kaehlerToCoLie : Ω[A⁄R] →ₗ[A] coLie R A :=
  (dDerivation (R := R) (A := A)).liftKaehlerDifferential

@[simp] theorem kaehlerToCoLie_D (a : A) :
    kaehlerToCoLie (KaehlerDifferential.D R A a) = d R A a :=
  Derivation.liftKaehlerDifferential_comp_D _ a

/-- `I · Ω[A⁄R]`, the submodule one quotients by to pull back along the identity section. -/
noncomputable abbrev kaehlerAug : Submodule A (Ω[A⁄R]) :=
  (augIdeal R A) • (⊤ : Submodule A (Ω[A⁄R]))

theorem kaehlerAug_le_ker :
    kaehlerAug (R := R) (A := A) ≤ LinearMap.ker (kaehlerToCoLie (R := R) (A := A)) := by
  intro w hw
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro a ha w _
    rw [LinearMap.mem_ker, map_smul, smul_coLie, mem_augIdeal.mp ha, zero_smul]
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy


theorem smul_D_mem_kaehlerAug {x : A} (hx : x ∈ augIdeal R A) (a : A) :
    x • (KaehlerDifferential.D R A a) ∈ kaehlerAug (R := R) (A := A) :=
  Submodule.smul_mem_smul hx Submodule.mem_top

/-- `x ↦ [D x]` on the augmentation ideal. -/
noncomputable def augToKaehlerQuot :
    (augIdeal R A) →ₗ[A] (Ω[A⁄R] ⧸ kaehlerAug (R := R) (A := A)) where
  toFun x := Submodule.Quotient.mk (KaehlerDifferential.D R A (x : A))
  map_add' x y := by
    show Submodule.Quotient.mk (KaehlerDifferential.D R A ((x : A) + (y : A))) = _
    rw [map_add]
    rfl
  map_smul' a x := by
    show Submodule.Quotient.mk (KaehlerDifferential.D R A (a * (x : A)))
      = a • Submodule.Quotient.mk (KaehlerDifferential.D R A (x : A))
    rw [Derivation.leibniz]
    rw [Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_smul]
    have hz : Submodule.Quotient.mk (p := kaehlerAug (R := R) (A := A))
        ((x : A) • KaehlerDifferential.D R A a) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (smul_D_mem_kaehlerAug x.2 a)
    rw [hz, add_zero]

theorem augToKaehlerQuot_mul (x y : (augIdeal R A)) :
    augToKaehlerQuot (R := R) (A := A) (x * y) = 0 := by
  show Submodule.Quotient.mk (KaehlerDifferential.D R A ((x : A) * (y : A))) = 0
  rw [Derivation.leibniz]
  refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.add_mem _ ?_ ?_)
  · exact smul_D_mem_kaehlerAug x.2 _
  · exact smul_D_mem_kaehlerAug y.2 _

/-- `ω_A → Ω[A⁄R] / I·Ω`. -/
noncomputable def coLieToKaehlerQuot :
    coLie R A →ₗ[A] (Ω[A⁄R] ⧸ kaehlerAug (R := R) (A := A)) :=
  Ideal.Cotangent.lift (augToKaehlerQuot (R := R) (A := A)) augToKaehlerQuot_mul

/-- `Ω[A⁄R] / I·Ω → ω_A`. -/
noncomputable def kaehlerQuotToCoLie :
    (Ω[A⁄R] ⧸ kaehlerAug (R := R) (A := A)) →ₗ[A] coLie R A :=
  Submodule.liftQ _ kaehlerToCoLie kaehlerAug_le_ker

theorem d_coe_augIdeal (x : (augIdeal R A)) : d R A (x : A) = (augIdeal R A).toCotangent x := by
  rw [d_apply]
  congr 1
  apply Subtype.ext
  rw [toAug_coe, mem_augIdeal.mp x.2, map_zero, sub_zero]

theorem kaehlerQuotToCoLie_comp_coLieToKaehlerQuot :
    (kaehlerQuotToCoLie (R := R) (A := A)).comp (coLieToKaehlerQuot (R := R) (A := A))
      = LinearMap.id := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨x, rfl⟩ := (augIdeal R A).toCotangent_surjective m
  show kaehlerQuotToCoLie (coLieToKaehlerQuot ((augIdeal R A).toCotangent x)) = _
  rw [coLieToKaehlerQuot, Ideal.Cotangent.lift_toCotangent]
  show kaehlerToCoLie (KaehlerDifferential.D R A (x : A)) = _
  rw [kaehlerToCoLie_D, d_coe_augIdeal]
  rfl

theorem coLieToKaehlerQuot_comp_kaehlerQuotToCoLie :
    (coLieToKaehlerQuot (R := R) (A := A)).comp (kaehlerQuotToCoLie (R := R) (A := A))
      = LinearMap.id := by
  refine Submodule.linearMap_qext _ ?_
  refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A) ?_
  rintro _ ⟨a, rfl⟩
  show coLieToKaehlerQuot (kaehlerToCoLie (KaehlerDifferential.D R A a))
    = Submodule.Quotient.mk (KaehlerDifferential.D R A a)
  rw [kaehlerToCoLie_D, d_apply, coLieToKaehlerQuot, Ideal.Cotangent.lift_toCotangent]
  show Submodule.Quotient.mk (KaehlerDifferential.D R A (a - algebraMap R A (counit a : R)))
    = Submodule.Quotient.mk (KaehlerDifferential.D R A a)
  rw [map_sub]
  simp

/-- **The co-Lie module is `e^* Ω¹`.** -/
noncomputable def coLieEquivKaehlerQuotient :
    coLie R A ≃ₗ[A] (Ω[A⁄R] ⧸ kaehlerAug (R := R) (A := A)) :=
  LinearEquiv.ofLinear coLieToKaehlerQuot kaehlerQuotToCoLie
    coLieToKaehlerQuot_comp_kaehlerQuotToCoLie kaehlerQuotToCoLie_comp_coLieToKaehlerQuot

end GaloisForLFunctions.HTGeometry.AffineGroupScheme
