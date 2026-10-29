import GaloisForLFunctions.HeckeLFunctions.EveryRayResidueAndSignHasAnIntegralRepresentative

/-!
# Finite characters and real parities of Hecke characters

Surjective ray reduction extends the principal ray-class map to the full product
of invertible finite residues and real signs. Restriction to the two factors
separates every Hecke character into a finite character and a product of sign
characters. These components cancel on global units, as their principal ideals
are the unit ideal.
-/

noncomputable section

open NumberField FractionalIdeal
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The ray class of a principal ideal as a function of arbitrary finite residue and real signs. -/
def fullRayResidueClass : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* RayClassGroup 𝔪 :=
  (rayResidueClass 𝔪).comp {
    toFun g := ⟨g, rayHom_surjective 𝔪 g⟩
    map_one' := Subtype.ext rfl
    map_mul' _ _ := Subtype.ext rfl }

theorem fullRayResidueClass_rayHom (α : primeToUnits 𝔪) :
    fullRayResidueClass 𝔪 (rayHom 𝔪 α) = rayClassOfElt 𝔪 α :=
  rayResidueClass_apply 𝔪 α

/-- The character on finite residues and signs induced by a ray class character. -/
def rayResidueCharacter (ψ : HeckeCharacter 𝔪) :
    (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) →* ℂˣ :=
  ψ.comp (fullRayResidueClass 𝔪)

/-- The finite residue component of a Hecke character. -/
def finiteResidueCharacter (ψ : HeckeCharacter 𝔪) : (𝓞 K ⧸ 𝔪.fin)ˣ →* ℂˣ :=
  (rayResidueCharacter 𝔪 ψ).comp
    ((MonoidHom.id ((𝓞 K ⧸ 𝔪.fin)ˣ)).prod
      (1 : (𝓞 K ⧸ 𝔪.fin)ˣ →* (𝔪.inf → ℤˣ)))

/-- The real sign component of a Hecke character. -/
def infiniteSignCharacter (ψ : HeckeCharacter 𝔪) : (𝔪.inf → ℤˣ) →* ℂˣ :=
  (rayResidueCharacter 𝔪 ψ).comp
    ((1 : (𝔪.inf → ℤˣ) →* (𝓞 K ⧸ 𝔪.fin)ˣ).prod
      (MonoidHom.id (𝔪.inf → ℤˣ)))

theorem rayResidueCharacter_eq_mul (ψ : HeckeCharacter 𝔪)
    (g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) :
    rayResidueCharacter 𝔪 ψ g =
      finiteResidueCharacter 𝔪 ψ g.1 * infiniteSignCharacter 𝔪 ψ g.2 := by
  change rayResidueCharacter 𝔪 ψ g =
    rayResidueCharacter 𝔪 ψ (g.1, 1) * rayResidueCharacter 𝔪 ψ (1, g.2)
  rw [← map_mul]
  congr 1
  exact Prod.ext (mul_one _).symm (one_mul _).symm

/-- On principal ideals the finite component and the real sign component multiply to `ψ((α))`. -/
theorem character_rayClassOfElt_eq (ψ : HeckeCharacter 𝔪) (α : primeToUnits 𝔪) :
    ψ (rayClassOfElt 𝔪 α) = finiteResidueCharacter 𝔪 ψ (reduce 𝔪 α) *
      infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 α) := by
  rw [← fullRayResidueClass_rayHom 𝔪 α]
  exact rayResidueCharacter_eq_mul 𝔪 ψ (rayHom 𝔪 α)

/-- A global unit generates the unit fractional ideal. -/
theorem toPrincipalIdeal_globalUnit (u : (𝓞 K)ˣ) :
    toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal, Units.val_one]
  change spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
  rw [← coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit, coeIdeal_top]

/-- Global units are prime to every finite modulus. -/
def globalUnitPrimeTo : (𝓞 K)ˣ →* primeToUnits 𝔪 :=
  (Units.map (algebraMap (𝓞 K) K).toMonoidHom).codRestrict (primeToUnits 𝔪) fun u =>
    (toPrincipalIdeal_mem_idealGroup_iff 𝔪 _).mp (by
      rw [toPrincipalIdeal_globalUnit]
      exact (idealGroup 𝔪).one_mem)

theorem rayClassOfElt_globalUnit (u : (𝓞 K)ˣ) :
    rayClassOfElt 𝔪 (globalUnitPrimeTo 𝔪 u) = 1 := by
  change rayClass 𝔪 _ = 1
  rw [← map_one (rayClass 𝔪)]
  congr 1
  exact Subtype.ext (toPrincipalIdeal_globalUnit u)

/-- The finite and infinite components cancel on every global unit. -/
theorem finite_mul_infinite_globalUnit (ψ : HeckeCharacter 𝔪) (u : (𝓞 K)ˣ) :
    finiteResidueCharacter 𝔪 ψ (reduce 𝔪 (globalUnitPrimeTo 𝔪 u)) *
      infiniteSignCharacter 𝔪 ψ
        (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) = 1 := by
  have h := character_rayClassOfElt_eq 𝔪 ψ (globalUnitPrimeTo 𝔪 u)
  rw [rayClassOfElt_globalUnit, map_one] at h
  exact h.symm

private theorem sign_character_apply (φ : ℤˣ →* ℂˣ) (u : ℤˣ) :
    (φ u : ℂ) = ((u : ℤ) : ℂ) ^ (if (φ (-1) : ℂ) = 1 then 0 else 1 : ℕ) := by
  have hunit : (-1 : ℤˣ) ^ 2 = 1 := by ext; norm_num
  have hsq : (φ (-1) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hunit, map_one, Units.val_one]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]

/-- The parity at a real place: zero for the trivial coordinate character, one for the sign. -/
def heckeParity (ψ : HeckeCharacter 𝔪) (w : 𝔪.inf) : ℕ :=
  if (infiniteSignCharacter 𝔪 ψ (Pi.mulSingle w (-1)) : ℂ) = 1 then 0 else 1

theorem heckeParity_le_one (ψ : HeckeCharacter 𝔪) (w : 𝔪.inf) : heckeParity 𝔪 ψ w ≤ 1 := by
  unfold heckeParity
  split_ifs <;> omega

/-- The infinite component is the product of the coordinate signs raised to their parities. -/
theorem infiniteSignCharacter_eq_prod (ψ : HeckeCharacter 𝔪) (σ : 𝔪.inf → ℤˣ) :
    (infiniteSignCharacter 𝔪 ψ σ : ℂ) =
      ∏ w : 𝔪.inf, ((σ w : ℤ) : ℂ) ^ heckeParity 𝔪 ψ w := by
  change ((Units.coeHom ℂ).comp (infiniteSignCharacter 𝔪 ψ)) σ = _
  conv_lhs => rw [← Finset.univ_prod_mulSingle σ]
  rw [map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h := sign_character_apply ((infiniteSignCharacter 𝔪 ψ).comp
    (MonoidHom.mulSingle (fun _ : 𝔪.inf => ℤˣ) w)) (σ w)
  simpa [MonoidHom.mulSingle, heckeParity, Pi.mulSingle] using h

/-- The finite residue character and the parity factors satisfy the global-unit relation. -/
theorem finite_character_mul_parities_globalUnit (ψ : HeckeCharacter 𝔪) (u : (𝓞 K)ˣ) :
    (finiteResidueCharacter 𝔪 ψ (reduce 𝔪 (globalUnitPrimeTo 𝔪 u)) : ℂ) *
      ∏ w : 𝔪.inf,
        ((signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) w : ℤ) : ℂ) ^
          heckeParity 𝔪 ψ w = 1 := by
  rw [← infiniteSignCharacter_eq_prod]
  simpa only [Units.val_mul, Units.val_one] using
    congrArg (fun z : ℂˣ => (z : ℂ)) (finite_mul_infinite_globalUnit 𝔪 ψ u)

end GaloisForLFunctions.HeckeLFunctions
