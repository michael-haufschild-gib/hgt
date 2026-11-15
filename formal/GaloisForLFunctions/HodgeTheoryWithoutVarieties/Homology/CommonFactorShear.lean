import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology

/-!
# Shearing a two-generator Koszul complex

The complex on `(z a,z b)`, for units `a,b`, is isomorphic to the complex on
`(z,0)`. The shear works over every commutative ring and for every common
factor, including zero divisors. It isolates the closed generator in the
same way as Lemma 3.14 of Kurnosov–Ríos Ortiz,
https://arxiv.org/abs/2611.01210.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
variable {R : Type*} [CommRing R]

/-- A determinant-one change of generators sending `(z a,z b)` to `(z,0)`. -/
def commonFactorShear (a b : Rˣ) : (R × R) ≃ₗ[R] R × R where
  toFun x := (x.1 * (a : R) + x.2 * (b : R), x.2 * (↑a⁻¹ : R))
  invFun x := (x.1 * (↑a⁻¹ : R) - x.2 * (b : R), x.2 * (a : R))
  left_inv x := by
    apply Prod.ext
    · change (x.1 * (a : R) + x.2 * (b : R)) * (↑a⁻¹ : R) -
        x.2 * (↑a⁻¹ : R) * (b : R) = x.1
      calc
        _ = x.1 * ((a : R) * (↑a⁻¹ : R)) := by ring
        _ = x.1 := by simp
    · change x.2 * (↑a⁻¹ : R) * (a : R) = x.2
      simp [mul_assoc]
  right_inv x := by
    apply Prod.ext
    · change (x.1 * (↑a⁻¹ : R) - x.2 * (b : R)) * (a : R) +
        x.2 * (a : R) * (b : R) = x.1
      calc
        _ = x.1 * ((↑a⁻¹ : R) * (a : R)) := by ring
        _ = x.1 := by simp
    · change x.2 * (a : R) * (↑a⁻¹ : R) = x.2
      simp [mul_assoc]
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' c x := by ext <;> dsimp <;> ring

/-- The first differential retains only the first sheared coordinate. -/
theorem commonFactorShear_d1 (z : R) (a b : Rˣ) (x : R × R) :
    commonFactorKoszulD1 z a b x = z * (commonFactorShear a b x).1 := by
  change x.1 * (z * (a : R)) + x.2 * (z * (b : R)) =
    z * (x.1 * (a : R) + x.2 * (b : R))
  ring

/-- The second differential becomes multiplication by `z` in the closed coordinate. -/
theorem commonFactorShear_d2 (z : R) (a b : Rˣ) (t : R) :
    commonFactorShear a b (commonFactorKoszulD2 z a b t) = (0, z * t) := by
  apply Prod.ext
  · change -t * (z * (b : R)) * (a : R) + t * (z * (a : R)) * (b : R) = 0
    ring
  · change t * (z * (a : R)) * (↑a⁻¹ : R) = z * t
    simp [mul_assoc, mul_comm t z]

/-- Scalar annihilator of the common factor. -/
abbrev commonFactorAnnihilator (z : R) :=
  LinearMap.ker (commonFactorScalarMap z : R →ₗ[R] R)

/-- Cycles consist of an annihilator coordinate and an unrestricted coordinate. -/
def commonFactorShearCyclesEquiv (z : R) (a b : Rˣ) :
    commonFactorKoszulCycles z a b ≃ₗ[R] commonFactorAnnihilator z × R where
  toFun x := (⟨(commonFactorShear a b x.val).1, by
    change z * (commonFactorShear a b x.val).1 = 0
    rw [← commonFactorShear_d1]
    exact x.property⟩, (commonFactorShear a b x.val).2)
  invFun x := ⟨(commonFactorShear a b).symm (x.1.val, x.2), by
    change commonFactorKoszulD1 z a b _ = 0
    rw [commonFactorShear_d1, LinearEquiv.apply_symm_apply]
    exact x.1.property⟩
  left_inv x := Subtype.ext ((commonFactorShear a b).symm_apply_apply x.val)
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((commonFactorShear a b).apply_symm_apply (x.1.val, x.2))
    · exact congrArg Prod.snd ((commonFactorShear a b).apply_symm_apply (x.1.val, x.2))
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((commonFactorShear a b).map_add x.val y.val)
    · exact congrArg Prod.snd ((commonFactorShear a b).map_add x.val y.val)
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((commonFactorShear a b).map_smul c x.val)
    · exact congrArg Prod.snd ((commonFactorShear a b).map_smul c x.val)

/-- The quotient coordinate is reduced modulo the common factor. -/
def commonFactorShearProjection (z : R) (a b : Rˣ) :
    commonFactorKoszulCycles z a b →ₗ[R]
      commonFactorAnnihilator z × (R ⧸ (Ideal.span ({z} : Set R) : Submodule R R)) :=
  (LinearMap.prodMap LinearMap.id (Ideal.span ({z} : Set R) : Submodule R R).mkQ).comp
    (commonFactorShearCyclesEquiv z a b).toLinearMap

theorem commonFactorShearProjection_surjective (z : R) (a b : Rˣ) :
    Function.Surjective (commonFactorShearProjection z a b) := by
  rintro ⟨r, q⟩
  obtain ⟨s, hs⟩ := (Ideal.span ({z} : Set R) : Submodule R R).mkQ_surjective q
  refine ⟨(commonFactorShearCyclesEquiv z a b).symm (r, s), ?_⟩
  change (LinearMap.prodMap LinearMap.id (Ideal.span ({z} : Set R) : Submodule R R).mkQ)
    (commonFactorShearCyclesEquiv z a b ((commonFactorShearCyclesEquiv z a b).symm (r, s))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Prod.ext rfl hs

/-- The shear projection kills exactly the original Koszul boundaries. -/
theorem commonFactorShearProjection_ker (z : R) (a b : Rˣ) :
    (commonFactorShearProjection z a b).ker = commonFactorKoszulBoundaries z a b := by
  ext x
  constructor
  · intro hx
    have hr : (commonFactorShear a b x.val).1 = 0 :=
      congrArg (fun y => (y.1 : R)) hx
    have hq : (Submodule.Quotient.mk (commonFactorShear a b x.val).2 :
        R ⧸ (Ideal.span ({z} : Set R) : Submodule R R)) = 0 := congrArg Prod.snd hx
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hm
    refine ⟨t, (commonFactorShear a b).injective ?_⟩
    rw [commonFactorShear_d2]
    exact Prod.ext hr.symm ht.symm
  · rintro ⟨t, ht⟩
    have hs : commonFactorShear a b x.val = (0, z * t) := by
      rw [← ht, commonFactorShear_d2]
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hs
    · change (Submodule.Quotient.mk (commonFactorShear a b x.val).2 :
          R ⧸ (Ideal.span ({z} : Set R) : Submodule R R)) = 0
      rw [congrArg Prod.snd hs]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton.mpr ⟨t, rfl⟩)

/-- Degree-one homology for every common factor, with the annihilator term retained. -/
def commonFactorKoszulH1WithTorsion (z : R) (a b : Rˣ) :
    commonFactorKoszulH1 z a b ≃ₗ[R]
      commonFactorAnnihilator z × (R ⧸ (Ideal.span ({z} : Set R) : Submodule R R)) :=
  (Submodule.quotEquivOfEq _ _ (commonFactorShearProjection_ker z a b).symm).trans
    ((commonFactorShearProjection z a b).quotKerEquivOfSurjective
      (commonFactorShearProjection_surjective z a b))

/-- Degree-two homology is exactly the annihilator of the common factor. -/
theorem commonFactorKoszulH2_eq_annihilator (z : R) (a b : Rˣ) :
    commonFactorKoszulH2 z a b = commonFactorAnnihilator z := by
  ext t
  change commonFactorKoszulD2 z a b t = 0 ↔ z * t = 0
  constructor
  · intro ht
    have hs := congrArg (commonFactorShear a b) ht
    rw [commonFactorShear_d2, map_zero] at hs
    exact congrArg Prod.snd hs
  · intro ht
    apply (commonFactorShear a b).injective
    rw [commonFactorShear_d2, map_zero, ht]
    rfl

#print axioms commonFactorShear_d1
#print axioms commonFactorShear_d2
#print axioms commonFactorKoszulH1WithTorsion
#print axioms commonFactorKoszulH2_eq_annihilator
end GaloisForLFunctions.HodgeTheoryWithoutVarieties
