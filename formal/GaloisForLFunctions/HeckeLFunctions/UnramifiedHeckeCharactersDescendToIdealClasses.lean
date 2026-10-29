import GaloisForLFunctions.HeckeLFunctions.HeckeThetaAveragesOverTheUnitDomain

/-!
# Unramified Hecke characters descend to ordinary ideal classes

Zero real parity degree and trivial finite weight make the character trivial
on the kernel of the ray-to-ordinary class map. Its proved surjectivity gives
an ordinary class character with the exact original pullback. Nontriviality
is preserved, so the finite ordinary-class character sum vanishes.

For nontrivial finite weight, the finite modulus is not the unit ideal.
The classified physical and dual theta zero modes then both vanish, giving
an entire actual unit-averaged Mellin continuation.
-/

noncomputable section
open NumberField
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Zero coordinate parity degree makes every selected real-place parity zero. -/
theorem heckeParity_eq_zero_of_degree_eq_zero (ψ : HeckeCharacter 𝔪)
    (h : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0) (w : 𝔪.inf) :
    heckeParity 𝔪 ψ w = 0 := by
  have he := congrArg Bool.toNat ((parityDegree_eq_zero_iff _).mp h (Sum.inl w.1))
  simpa only [heckeCoordinateParity, dif_pos w.2, heckeParity_decide,
    Bool.toNat_false] using he

/-- Zero actual parity degree makes the full infinite sign character trivial. -/
theorem infiniteSignCharacter_eq_one_of_degree_eq_zero (ψ : HeckeCharacter 𝔪)
    (h : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0) : infiniteSignCharacter 𝔪 ψ = 1 := by
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  change (infiniteSignCharacter 𝔪 ψ σ : ℂ) = 1
  rw [infiniteSignCharacter_eq_prod]
  simp only [heckeParity_eq_zero_of_degree_eq_zero 𝔪 ψ h, pow_zero, Finset.prod_const_one]

/-- Trivial finite weight restricts to the trivial character on residue units. -/
theorem finiteResidueCharacter_eq_one_of_weight_eq_one (ψ : HeckeCharacter 𝔪)
    (h : finiteHeckeWeight 𝔪 ψ = 1) : finiteResidueCharacter 𝔪 ψ = 1 := by
  apply MonoidHom.ext
  intro u
  apply Units.ext
  change (finiteResidueCharacter 𝔪 ψ u : ℂ) = 1
  rw [← finiteHeckeWeight_unit, h, MulChar.one_apply_coe]

/-- Finite-unit and real-sign triviality force descent to the actual ordinary class group. -/
theorem exists_classCharacter_of_finiteParity_trivial (ψ : HeckeCharacter 𝔪)
    (hf : finiteHeckeWeight 𝔪 ψ = 1)
    (hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0) :
    ∃ φ : ClassGroup (𝓞 K) →* ℂˣ, φ.comp (toClassGroup 𝔪) = ψ := by
  have hfin := finiteResidueCharacter_eq_one_of_weight_eq_one 𝔪 ψ hf
  have hinf := infiniteSignCharacter_eq_one_of_degree_eq_zero 𝔪 ψ hp
  have hk : (toClassGroup 𝔪).ker ≤ ψ.ker := by
    intro c hc
    obtain ⟨α, rfl⟩ := ker_toClassGroup_le 𝔪 c (MonoidHom.mem_ker.mp hc)
    rw [MonoidHom.mem_ker, character_rayClassOfElt_eq, hfin, hinf,
      MonoidHom.one_apply, MonoidHom.one_apply, one_mul]
  let e : {g : RayClassGroup 𝔪 →* ℂˣ // (toClassGroup 𝔪).ker ≤ g.ker} ≃
      (ClassGroup (𝓞 K) →* ℂˣ) :=
    (toClassGroup 𝔪).liftOfSurjective (toClassGroup_surjective 𝔪)
  refine ⟨e ⟨ψ, hk⟩, ?_⟩
  exact congrArg Subtype.val (e.symm_apply_apply ⟨ψ, hk⟩)

/-- A character descending from a nontrivial Hecke character remains nontrivial. -/
theorem classCharacter_ne_one_of_comp (ψ : HeckeCharacter 𝔪) (hψ : ψ ≠ 1)
    (φ : ClassGroup (𝓞 K) →* ℂˣ) (hφ : φ.comp (toClassGroup 𝔪) = ψ) : φ ≠ 1 := by
  intro h
  apply hψ
  rw [← hφ, h]
  ext c
  rfl

local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

/-- Orthogonality cancels the full ordinary-class sum of a nontrivial descended character. -/
theorem sum_classCharacter_eq_zero_of_comp (ψ : HeckeCharacter 𝔪) (hψ : ψ ≠ 1)
    (φ : ClassGroup (𝓞 K) →* ℂˣ) (hφ : φ.comp (toClassGroup 𝔪) = ψ) :
    ∑ c : ClassGroup (𝓞 K), (φ c : ℂ) = 0 := by
  have hn := classCharacter_ne_one_of_comp 𝔪 ψ hψ φ hφ
  change ∑ c, ((Units.coeHom ℂ).comp φ) c = 0
  refine sum_hom_units_eq_zero _ fun h => hn ?_
  ext c
  exact congrArg (· c) h

/-- For the unit finite modulus every finite Hecke weight is trivial. -/
theorem finiteHeckeWeight_eq_one_of_fin_eq_top (ψ : HeckeCharacter 𝔪)
    (hm : 𝔪.fin = ⊤) : finiteHeckeWeight 𝔪 ψ = 1 := by
  have hq (x : 𝓞 K ⧸ 𝔪.fin) : x = 1 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq.mpr
    rw [hm]
    exact Submodule.mem_top
  ext x
  rw [hq x]
  simp only [map_one]

/-- A nontrivial finite weight kills both actual unit-averaged theta zero modes. -/
theorem heckeUnitThetaMellinPair_isStrong_of_finiteWeight_ne_one
    {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
    (ψ : HeckeCharacter 𝔪) (hf : finiteHeckeWeight 𝔪 ψ ≠ 1) :
    IsStrongFEPair (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ) := by
  have hm : 𝔪.fin ≠ ⊤ := fun h => hf (finiteHeckeWeight_eq_one_of_fin_eq_top 𝔪 ψ h)
  constructor
  · change Units.regulator K • heckeThetaConstant 𝔪 ψ = 0
    simp only [heckeThetaConstant, hm, false_and, if_false, smul_zero]
  · change Units.regulator K • heckeDualThetaConstant 𝔪 ψ = 0
    simp only [heckeDualThetaConstant, hf, and_false, if_false, smul_zero]

/-- Nontrivial finite weight makes the actual unit-averaged Mellin continuation entire. -/
theorem differentiable_heckeUnitThetaMellinContinuation_of_finiteWeight_ne_one
    {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
    (ψ : HeckeCharacter 𝔪) (hf : finiteHeckeWeight 𝔪 ψ ≠ 1) :
    Differentiable ℂ (heckeUnitThetaMellinContinuation 𝔪 hb hb0 ψ) :=
  (heckeUnitThetaMellinPair_isStrong_of_finiteWeight_ne_one 𝔪 hb hb0 ψ hf).differentiable_Λ

end GaloisForLFunctions.HeckeLFunctions
