import GaloisForLFunctions.RHTower.Artin.ArtinIntegerDescent
import GaloisForLFunctions.RHTower.Artin.ArtinMonomialMultiplicityHasse

/-!
# The integer span of the induced characters inside their span over the algebraic integers

Let `𝔉` be a family of subgroups of a finite group. A virtual character that lies in the span
over the algebraic integers of the characters induced from `𝔉` lies in their integer span
(`mem_inducedSpan_of_mem_inducedSpanInt`).

Write `x = Σ_k a_k v_k` with algebraic integers `a_k` and `v_k` in the integer span
(`exists_integral_combination`). Pairing with a monomial character `μ` is linear, so the
integers `⟨x, μ⟩` are the combinations `Σ_k a_k ⟨v_k, μ⟩` of the integers `⟨v_k, μ⟩`. By the
descent of the coefficients there are integers `m_k` with `⟨x, μ⟩ = Σ_k m_k ⟨v_k, μ⟩` for all
`μ` at once, and a virtual character is determined by its multiplicities against the monomial
characters. So `x = Σ_k m_k v_k`.
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G] [Fintype G]

/-- A member of the span over the algebraic integers is a finite combination, with algebraic
integer coefficients, of members of the integer span. -/
theorem exists_integral_combination {𝔉 : Set (Subgroup G)} {x : G → ℂ}
    (h : x ∈ inducedSpanInt 𝔉) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (v : ι → G → ℂ), (∀ k, IsIntegral ℤ (a k)) ∧
      (∀ k, v k ∈ inducedSpan 𝔉) ∧ x = fun g => ∑ k, a k * v k g := by
  refine AddSubgroup.closure_induction (p := fun x _ => ∃ (ι : Type) (_ : Fintype ι)
    (a : ι → ℂ) (v : ι → G → ℂ), (∀ k, IsIntegral ℤ (a k)) ∧ (∀ k, v k ∈ inducedSpan 𝔉) ∧
      x = fun g => ∑ k, a k * v k g) ?_ ?_ ?_ ?_ h
  · rintro f ⟨a, ha, H, hH, χ, hχ, rfl⟩
    refine ⟨Unit, inferInstance, fun _ => a, fun _ => inducedFunction H χ, fun _ => ha,
      fun _ => AddSubgroup.subset_closure ⟨H, hH, χ, hχ, rfl⟩, ?_⟩
    funext g
    simp
  · exact ⟨Empty, inferInstance, fun k => k.elim, fun k => k.elim, fun k => k.elim,
      fun k => k.elim, by funext g; simp⟩
  · rintro f₁ f₂ _ _ ⟨ι₁, _, a₁, v₁, ha₁, hv₁, rfl⟩ ⟨ι₂, _, a₂, v₂, ha₂, hv₂, rfl⟩
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim a₁ a₂, Sum.elim v₁ v₂, ?_, ?_, ?_⟩
    · rintro (k | k)
      · exact ha₁ k
      · exact ha₂ k
    · rintro (k | k)
      · exact hv₁ k
      · exact hv₂ k
    · funext g
      simp [Fintype.sum_sum_type]
  · rintro f _ ⟨ι, _, a, v, ha, hv, rfl⟩
    refine ⟨ι, inferInstance, fun k => -a k, v, fun k => (ha k).neg, hv, ?_⟩
    funext g
    simp [Finset.sum_neg_distrib]

/-- The pairing with a fixed function is linear in the first variable. -/
theorem characterPairing_sum_mul_left {ι : Type*} [Fintype ι] (a : ι → ℂ) (v : ι → G → ℂ)
    (μ : G → ℂ) :
    characterPairing G (fun g => ∑ k, a k * v k g) μ = ∑ k, a k * characterPairing G (v k) μ := by
  simp only [characterPairing, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun g _ => by ring

/-- **Descent.** A virtual character in the span over the algebraic integers of the characters
induced from a family of subgroups is in their integer span. -/
theorem mem_inducedSpan_of_mem_inducedSpanInt {𝔉 : Set (Subgroup G)} {x : G → ℂ}
    (hx : x ∈ virtualCharacterGroup G) (h : x ∈ inducedSpanInt 𝔉) : x ∈ inducedSpan 𝔉 := by
  obtain ⟨ι, _, a, v, ha, hv, rfl⟩ := exists_integral_combination h
  have hvR : ∀ k, v k ∈ virtualCharacterGroup G := fun k => inducedSpan_le 𝔉 (hv k)
  -- the multiplicities against the monomial characters
  have hpair : ∀ q : Σ H : Subgroup G, LinearCharacter H,
      ((virtualMultiplicity G ⟨_, hx⟩ (monomialVirtualCharacter G q.1 q.2) : ℤ) : ℂ) =
        ∑ k, a k * ((virtualMultiplicity G ⟨v k, hvR k⟩
          (monomialVirtualCharacter G q.1 q.2) : ℤ) : ℂ) := fun q => by
    rw [virtualMultiplicity_cast, characterPairing_sum_mul_left]
    exact Finset.sum_congr rfl fun k _ => by rw [virtualMultiplicity_cast]
  obtain ⟨m, hm⟩ := exists_int_combination a ha
    (fun k (q : Σ H : Subgroup G, LinearCharacter H) =>
      virtualMultiplicity G ⟨v k, hvR k⟩ (monomialVirtualCharacter G q.1 q.2))
    (fun q => virtualMultiplicity G ⟨_, hx⟩ (monomialVirtualCharacter G q.1 q.2)) hpair
  -- the difference has no monomial multiplicity
  have hzero : (⟨_, hx⟩ : VirtualCharacter G) - ∑ k, m k • (⟨v k, hvR k⟩ : VirtualCharacter G) =
      0 := by
    rw [virtualCharacter_eq_zero_monomialMultiplicity_hasse_iff]
    intro H χ
    let L : VirtualCharacter G →+ ℤ := AddMonoidHom.mk'
      (fun θ => virtualMultiplicity G θ (monomialVirtualCharacter G H χ))
      (fun θ η => virtualMultiplicity_add_left G θ η (monomialVirtualCharacter G H χ))
    show L _ = 0
    rw [map_sub, map_sum]
    have h1 := hm ⟨H, χ⟩
    have h2 : ∀ k, L (m k • (⟨v k, hvR k⟩ : VirtualCharacter G)) =
        m k * virtualMultiplicity G ⟨v k, hvR k⟩ (monomialVirtualCharacter G H χ) := fun k => by
      rw [map_zsmul, smul_eq_mul]
      rfl
    rw [Finset.sum_congr rfl fun k _ => h2 k]
    exact sub_eq_zero.mpr h1
  have hval := congrArg (fun θ : VirtualCharacter G => θ.val) (sub_eq_zero.mp hzero)
  have hx' : (fun g => ∑ k, a k * v k g) = ∑ k, m k • v k := by
    simpa using hval
  rw [hx']
  exact AddSubgroup.sum_mem _ fun k _ => AddSubgroup.zsmul_mem _ (hv k) _

end GaloisForLFunctions
