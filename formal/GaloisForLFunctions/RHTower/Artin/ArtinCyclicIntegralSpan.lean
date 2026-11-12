import GaloisForLFunctions.RHTower.Artin.ArtinIntegralInducedSpan
import GaloisForLFunctions.RHTower.Artin.ArtinCyclicInductionIdentity
import GaloisForLFunctions.RHTower.Artin.ArtinFiniteAbelianFourier

/-!
# Class functions with values in `|G|·𝓞` are induced from cyclic subgroups

Let `𝓞` be the algebraic integers of `ℂ` and `𝔉` a family of subgroups of a finite group `G`
that contains the cyclic subgroups. A class function `f` whose values lie in `|G|·𝓞` is in the
`𝓞`-span of the characters induced from `𝔉` (`mem_inducedSpanInt_of_card_mul`).

* By Artin's identity and the projection formula, `f = Σ_C Ind(θ_C · (f/|G|)|_C)`, the sum over
  the cyclic subgroups.
* A function `φ` on a cyclic group `C` with values in `|C|·𝓞` is an `𝓞`-combination of linear
  characters: its Fourier coefficients `(1/|C|) Σ_c φ(c) χ(c⁻¹)` are algebraic integers, since
  the values of a linear character are roots of unity
  (`inducedFunction_mem_inducedSpanInt_of_cyclic`).
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G]

/-- The values of a linear character of a finite group are algebraic integers. -/
theorem isIntegral_linearCharacter {H : Type*} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H) :
    IsIntegral ℤ ((χ h : ℂˣ) : ℂ) := by
  refine IsIntegral.of_pow (n := Nat.card H) Nat.card_pos ?_
  have e : ((χ h : ℂˣ) : ℂ) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  rw [e]
  exact isIntegral_one

/-- A linear character is a character. -/
theorem linearCharacter_mem_fdCharacterSet {H : Type u} [Group H] (χ : LinearCharacter H) :
    (fun h => ((χ h : ℂˣ) : ℂ)) ∈ fdCharacterSet H := by
  have h := representation_character_mem_fdCharacterSet H (linearCharacterRepresentation χ)
  have e : (linearCharacterRepresentation χ).character = fun h => ((χ h : ℂˣ) : ℂ) :=
    funext fun h => linearCharacterRepresentation_character χ h
  rwa [e] at h

theorem extendByZero_sum (H : Subgroup G) {ι : Type*} (s : Finset ι) (F : ι → H → ℂ) (x : G) :
    extendByZero H (fun h => ∑ i ∈ s, F i h) x = ∑ i ∈ s, extendByZero H (F i) x := by
  by_cases hx : x ∈ H
  · simp only [extendByZero_of_mem H _ hx]
  · simp only [extendByZero_of_notMem H _ hx, Finset.sum_const_zero]

/-- The linear characters of a finite abelian group, as a finite type. -/
noncomputable local instance finiteLinearCharacterOfComm {A : Type u} [CommGroup A] [Finite A] :
    Finite (LinearCharacter A) :=
  RHTower.deningerCharacterGroup_finite

noncomputable local instance fintypeLinearCharacterOfComm {A : Type u} [CommGroup A]
    [Finite A] : Fintype (LinearCharacter A) :=
  Fintype.ofFinite _

variable [Fintype G]

/-- Induction commutes with finite sums. -/
theorem inducedFunction_sum (H : Subgroup G) {ι : Type*} (s : Finset ι) (F : ι → H → ℂ) :
    inducedFunction H (fun h => ∑ i ∈ s, F i h) = fun g => ∑ i ∈ s, inducedFunction H (F i) g := by
  funext g
  simp only [inducedFunction, extendByZero_sum]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- **A function on a cyclic subgroup with values in `|C|·𝓞` induces into the `𝓞`-span.** -/
theorem inducedFunction_mem_inducedSpanInt_of_cyclic {𝔉 : Set (Subgroup G)} (g₀ : G)
    (hC : Subgroup.zpowers g₀ ∈ 𝔉) (φ : Subgroup.zpowers g₀ → ℂ)
    (hφ : ∀ c, ∃ a : ℂ, IsIntegral ℤ a ∧ φ c = (Nat.card (Subgroup.zpowers g₀) : ℂ) * a) :
    inducedFunction (Subgroup.zpowers g₀) φ ∈ inducedSpanInt 𝔉 := by
  letI : CommGroup (Subgroup.zpowers g₀) := IsCyclic.commGroup
  choose a ha hφa using hφ
  have hcard : (Nat.card (Subgroup.zpowers g₀) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- the Fourier coefficients are algebraic integers
  have hcoeff : ∀ χ : LinearCharacter (Subgroup.zpowers g₀),
      IsIntegral ℤ (characterPairing (Subgroup.zpowers g₀) (RHTower.deningerCharacterFn χ) φ) := by
    intro χ
    have e : characterPairing (Subgroup.zpowers g₀) (RHTower.deningerCharacterFn χ) φ =
        ∑ c : Subgroup.zpowers g₀, a c * RHTower.deningerCharacterFn χ c⁻¹ := by
      rw [characterPairing, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hφa c]
      field_simp
    rw [e]
    exact IsIntegral.sum _ fun c _ => (ha c).mul (isIntegral_linearCharacter χ c⁻¹)
  have hfourier := finiteAbelian_fourier_reconstruction φ
  have hφsum : φ = fun c => ∑ χ : LinearCharacter (Subgroup.zpowers g₀),
      characterPairing (Subgroup.zpowers g₀) (RHTower.deningerCharacterFn χ) φ *
        RHTower.deningerCharacterFn χ c := by
    funext c
    conv_lhs => rw [← hfourier]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hφsum, inducedFunction_sum]
  have hterm : ∀ χ : LinearCharacter (Subgroup.zpowers g₀),
      (fun g => inducedFunction (Subgroup.zpowers g₀) (fun c =>
        characterPairing (Subgroup.zpowers g₀) (RHTower.deningerCharacterFn χ) φ *
          RHTower.deningerCharacterFn χ c) g) ∈ inducedSpanInt 𝔉 := fun χ => by
    rw [inducedFunction_smul]
    exact AddSubgroup.subset_closure ⟨_, hcoeff χ, _, hC, _,
      linearCharacter_mem_fdCharacterSet χ, rfl⟩
  have hsum := AddSubgroup.sum_mem (inducedSpanInt 𝔉) fun χ (_ : χ ∈ Finset.univ) => hterm χ
  convert hsum using 1
  funext g
  rw [Finset.sum_apply]

/-- **A class function with values in `|G|·𝓞` is in the `𝓞`-span of the characters induced from
the cyclic subgroups.** -/
theorem mem_inducedSpanInt_of_card_mul {𝔉 : Set (Subgroup G)}
    (h𝔉 : ∀ g : G, Subgroup.zpowers g ∈ 𝔉) {f : G → ℂ}
    (hclass : ∀ x g : G, f (x * g * x⁻¹) = f g)
    (hint : ∀ g : G, ∃ a : ℂ, IsIntegral ℤ a ∧ f g = (Nat.card G : ℂ) * a) :
    f ∈ inducedSpanInt 𝔉 := by
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  choose a ha hfa using hint
  -- `a = f/|G|` is a class function
  have haclass : ∀ x g : G, a (x * g * x⁻¹) = a g := fun x g =>
    mul_left_cancel₀ hG (by rw [← hfa, ← hfa, hclass])
  -- Artin's identity and the projection formula
  have hf : f = fun x => ∑ C ∈ cyclicSubgroups G,
      inducedFunction C (fun c : C => generatorWeight C c * a c) x := by
    funext x
    simp only [inducedFunction_mul_restrict _ _ a haclass]
    rw [← Finset.sum_mul, sum_inducedFunction_generatorWeight, hfa]
  rw [hf]
  have hsum := AddSubgroup.sum_mem (inducedSpanInt 𝔉) (f := fun C : Subgroup G =>
    inducedFunction C (fun c : C => generatorWeight C c * a c))
    (t := cyclicSubgroups G) fun C hC => by
      obtain ⟨g₀, -, rfl⟩ := Finset.mem_image.mp hC
      refine inducedFunction_mem_inducedSpanInt_of_cyclic g₀ (h𝔉 g₀) _ fun c => ?_
      by_cases hgen : Subgroup.zpowers (c : G) = Subgroup.zpowers g₀
      · exact ⟨a c, ha c, by rw [generatorWeight, if_pos hgen]⟩
      · exact ⟨0, isIntegral_zero, by rw [generatorWeight, if_neg hgen, zero_mul, mul_zero]⟩
  convert hsum using 1
  funext x
  rw [Finset.sum_apply]

end GaloisForLFunctions
