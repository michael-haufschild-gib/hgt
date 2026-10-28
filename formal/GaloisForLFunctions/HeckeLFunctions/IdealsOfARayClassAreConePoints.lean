import GaloisForLFunctions.HeckeLFunctions.RayClassesOfPrincipalIdealsAreReadByResidues

/-!
# Ideals of a ray class are cone points

Fix a ray class `c` and an integral ideal `𝔟` prime to `𝔪` in the inverse ideal class of `c`. Then
`𝔞 ↦ 𝔞𝔟` maps the integral ideals of class `c` to principal ideals, and each principal ideal has
exactly `w = #μ_K` generators in the fundamental cone (Mathlib's `integerSetEquiv`). So
`#{𝔞 ∈ c : N𝔞 ≤ x} · w = #{e(γ) ∈ cone : (γ) = 𝔞𝔟, 𝔞 ∈ c, N𝔞 ≤ x}`
(`ncard_rayClassIdeals_mul_torsionOrder`).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal Set
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone NumberField.Units
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The integral ideals of ray class `c` and norm `≤ x`. -/
def rayClassIdeals (c : RayClassGroup 𝔪) (x : ℝ) : Set (Ideal (𝓞 K)) :=
  {I | ∃ hI : I ≠ ⊥, ∃ hm : idealUnit hI ∈ idealGroup 𝔪, rayClass 𝔪 ⟨_, hm⟩ = c ∧
    (Ideal.absNorm I : ℝ) ≤ x}

/-- Counting cone points whose generated ideal satisfies `Q` counts the principal ideals with `Q`,
`w` times. -/
theorem card_integerSet_eq (Q : Ideal (𝓞 K) → Prop) :
    Nat.card {a : integerSet K // Q (Ideal.span {((preimageOfMemIntegerSet a : (𝓞 K)⁰) : 𝓞 K)})} =
      Nat.card {I : {I : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (I : Ideal (𝓞 K))} //
        Q I.1.1} * torsionOrder K := by
  rw [torsionOrder, ← Nat.card_prod]
  refine Nat.card_congr ((Equiv.subtypeEquiv (integerSetEquiv K) fun a => ?_).trans
    Equiv.prodSubtypeFstEquivSubtypeProd)
  rw [integerSetEquiv_apply_fst]

variable {𝔪} {c : RayClassGroup 𝔪} {𝔟 : Ideal (𝓞 K)} (h𝔟0 : 𝔟 ≠ ⊥)

/-- With `[𝔟] = (image of c)⁻¹`, every `𝔞 𝔟`, `𝔞 ∈ c`, is principal. -/
theorem isPrincipal_mul_of_mem (h𝔟c : ClassGroup.mk K (idealUnit h𝔟0) = (toClassGroup 𝔪 c)⁻¹)
    {x : ℝ} {I : Ideal (𝓞 K)} (hI : I ∈ rayClassIdeals 𝔪 c x) :
    Submodule.IsPrincipal (I * 𝔟) := by
  obtain ⟨hI0, hm, hc, -⟩ := hI
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hI0 h𝔟0)),
    ← ClassGroup.mk_mk0 K]
  have h : FractionalIdeal.mk0 K ⟨I * 𝔟, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hI0 h𝔟0)⟩ =
      idealUnit (mul_ne_zero hI0 h𝔟0) := rfl
  rw [h, idealUnit_mul hI0 h𝔟0, map_mul, h𝔟c, ← hc, toClassGroup_rayClass, mul_inv_cancel]

/-- **Ideals of a ray class are cone points**: `#{𝔞 ∈ c : N𝔞 ≤ x} · w` counts the cone points
`e(γ)` with `(γ) = 𝔞𝔟`, `𝔞 ∈ c`, `N𝔞 ≤ x`. -/
theorem ncard_rayClassIdeals_mul_torsionOrder
    (h𝔟c : ClassGroup.mk K (idealUnit h𝔟0) = (toClassGroup 𝔪 c)⁻¹) (x : ℝ) :
    (rayClassIdeals 𝔪 c x).ncard * torsionOrder K =
      {a : mixedSpace K | a ∈ integerSet K ∧ ∃ γ : 𝓞 K, mixedEmbedding K γ = a ∧
        ∃ I ∈ rayClassIdeals 𝔪 c x, Ideal.span {γ} = I * 𝔟}.ncard := by
  set Q : Ideal (𝓞 K) → Prop := fun J => ∃ I ∈ rayClassIdeals 𝔪 c x, J = I * 𝔟 with hQ
  -- the cone points with `Q`
  have h1 : {a : mixedSpace K | a ∈ integerSet K ∧ ∃ γ : 𝓞 K, mixedEmbedding K γ = a ∧
      ∃ I ∈ rayClassIdeals 𝔪 c x, Ideal.span {γ} = I * 𝔟}.ncard =
      Nat.card {a : integerSet K //
        Q (Ideal.span {((preimageOfMemIntegerSet a : (𝓞 K)⁰) : 𝓞 K)})} := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ integerSet K) _).symm.trans
      (Equiv.subtypeEquivRight fun a => ?_))
    constructor
    · rintro ⟨γ, hγ, hQγ⟩
      have : γ = ((preimageOfMemIntegerSet a : (𝓞 K)⁰) : 𝓞 K) := by
        apply RingOfIntegers.coe_injective
        apply mixedEmbedding_injective K
        rw [hγ, mixedEmbedding_preimageOfMemIntegerSet]
      rw [← this]
      exact hQγ
    · intro h
      exact ⟨_, mixedEmbedding_preimageOfMemIntegerSet a, h⟩
  -- the principal ideals with `Q` are the `𝔞𝔟`
  have h2 : Nat.card {I : {I : (Ideal (𝓞 K))⁰ // Submodule.IsPrincipal (I : Ideal (𝓞 K))} //
      Q I.1.1} = (rayClassIdeals 𝔪 c x).ncard := by
    rw [← Nat.card_coe_set_eq]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun I => ⟨⟨⟨I.1 * 𝔟,
      mem_nonZeroDivisors_of_ne_zero (mul_ne_zero I.2.1 h𝔟0)⟩,
      isPrincipal_mul_of_mem h𝔟0 h𝔟c I.2⟩, I.1, I.2, rfl⟩) ⟨fun I J h => ?_, fun J => ?_⟩)
    · have h' : I.1 * 𝔟 = J.1 * 𝔟 := congrArg (fun z => z.1.1.1) h
      exact Subtype.ext (mul_right_cancel₀ h𝔟0 h')
    · obtain ⟨I, hI, hJ⟩ := J.2
      exact ⟨⟨I, hI⟩, Subtype.ext (Subtype.ext (Subtype.ext hJ.symm))⟩
  rw [h1, card_integerSet_eq, h2]

end GaloisForLFunctions.HeckeLFunctions
