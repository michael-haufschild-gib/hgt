import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayClassNorm
import GaloisForLFunctions.RHTower.Artin.FrobeniusElementsRestrictToASubextension

/-! In an abelian tower, a ray character that factors through the
upper Artin map on relative norms factors through the base Artin map. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

universe u

variable (K E M : Type u) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
  (G H Γ : Type u)
  [CommGroup G] [Fintype G] [MulSemiringAction G E] [IsGaloisGroup G K E]
  [CommGroup H] [Fintype H] [MulSemiringAction H M] [IsGaloisGroup H E M]
  [CommGroup Γ] [Fintype Γ] [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]
  (j : H →* Γ) (hj : ∀ (h : H) (x : M), j h • x = h • x)

private theorem under_prime_to_rational_modulus (c : ℕ) [NeZero c]
    (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ w.asIdeal ∣ (normModulus E c).fin) :
    ¬ (w.under (𝓞 K)).asIdeal ∣ (normModulus K c).fin := by
  rw [dvd_normModulus_fin_iff] at hw ⊢
  intro h
  apply hw
  change algebraMap (𝓞 K) (𝓞 E) (c : 𝓞 K) ∈ w.asIdeal at h
  rwa [map_natCast] at h

include j hj in
theorem exists_artin_factor_of_norm_factor {A : Type*} [Group A] (c : ℕ) [NeZero c]
    (hE : ∀ v, ¬ v.asIdeal ∣ (normModulus K c).fin → IsUnramifiedPrime K E G v)
    (hM : ∀ v, ¬ v.asIdeal ∣ (normModulus K c).fin → IsUnramifiedPrime K M Γ v)
    (hR : rayPrincipal (normModulus K c) ≤ (artinMap K E G).ker)
    (hRM : rayPrincipal (normModulus K c) ≤ (artinMap K M Γ).ker)
    (χ : RayClassGroup (normModulus K c) →* A) (ψ : H →* A)
    (hχ : ∀ J : idealGroup (normModulus E c),
      χ (rayClassNorm K E c (rayClass (normModulus E c) J)) = ψ (artinMap E M H J.val)) :
    ∃ f : Γ →* A, ∀ I : idealGroup (normModulus K c),
      f (artinMap K M Γ I.val) = χ (rayClass (normModulus K c) I) := by
  let m := normModulus K c
  let a := (artinMap K M Γ).comp (idealGroup m).subtype
  let g := χ.comp (rayClass m)
  have ha : Function.Surjective a :=
    MonoidHom.range_eq_top.mp (range_artinMap_comp_subtype K M Γ m hM)
  have hk : a.ker ≤ g.ker := by
    intro I hI
    have hr : artinMap K E G I.val = 1 := by
      rw [← restrictHom_artinMap K E M (G := G) (Γ := Γ)
        (fun v hv => ⟨hE v (fun hd => hv (I.2 v hd)), hM v (fun hd => hv (I.2 v hd))⟩)]
      rw [show artinMap K M Γ I.val = 1 from hI, map_one]
    obtain ⟨J, r, hr, he⟩ := exists_ray_mul_coprimeNorm_of_artin_eq_one K E c G hE hR I hr
    let r' : idealGroup m := ⟨r, rayPrincipal_le m hr⟩
    have hr' : rayClass m r' = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hr)
    have hI' : r' * coprimeIdealNorm K E c J = I := Subtype.ext he
    have hJ : artinMap E M H J.val = 1 := by
      have h := map_artinMap_eq_artinMap_idealNormHom K E M j hj J.val
        (fun w hw => hM _ (under_prime_to_rational_modulus K E c w (fun hd => hw (J.2 w hd))))
      haveI : FaithfulSMul H M := IsGaloisGroup.faithful E
      apply (injective_of_forall_smul_eq j hj)
      have hRI : artinMap K M Γ r = 1 := MonoidHom.mem_ker.mp (hRM hr)
      have he' := map_mul (artinMap K M Γ) r (idealNormHom K E J.val)
      rw [he, hRI] at he'
      have hI1 : artinMap K M Γ I.val = 1 := hI
      calc
        j (artinMap E M H J.val) = artinMap K M Γ (idealNormHom K E J.val) := h
        _ = artinMap K M Γ I.val := (_root_.one_mul _).symm.trans he'.symm
        _ = 1 := hI1
        _ = j 1 := (map_one j).symm
    apply MonoidHom.mem_ker.mpr
    change χ (rayClass m I) = 1
    have hray : rayClass m I = rayClass m (coprimeIdealNorm K E c J) := by
      rw [← hI', map_mul, hr']
      exact _root_.one_mul (rayClass m (coprimeIdealNorm K E c J))
    exact (congrArg χ hray).trans ((hχ J).trans ((congrArg ψ hJ).trans (map_one ψ)))
  let f := a.liftOfSurjective ha ⟨g, hk⟩
  exact ⟨f, fun I =>
    a.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv ha) ⟨g, hk⟩ I⟩

end GlobalTheory.Reciprocity
