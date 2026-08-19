import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Primality survives a denominator-clearing extension

A subalgebra `T` of a field that contains the image of an injective ring map, inverts one element
of that image, and consists of elements that become images after clearing a power of it, is a
localization in all the ways that matter for divisor theory: every prime of the source that does
not divide the inverted element remains prime in `T`.

This is the elementary substitute for the localization API, stated so that it applies directly to
a concrete subalgebra of a function field.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E R R₀ : Type*} [Field E] [CommRing R] [CommRing R₀] [Algebra R₀ E]

/-- **Primality survives a denominator-clearing extension.**

If a subalgebra `T` of a field contains the image of an injective ring map `φ`, inverts `φ W`, and
every element of `T` becomes an image after clearing a power of `φ W`, then every prime of the
source not dividing `W` stays prime in `T`. -/
theorem prime_subtype_of_clearing (φ : R →+* E) (hφ : Function.Injective φ)
    (T : Subalgebra R₀ E) (hAT : ∀ r, φ r ∈ T)
    {W : R} {v : E} (hv : v ∈ T) (hvW : v * φ W = 1)
    (hclear : ∀ t : T, ∃ N : ℕ, ∃ f : R, (φ W) ^ N * (t : E) = φ f)
    {S : R} (hS : Prime S) (hSnonunit : ¬ IsUnit (⟨φ S, hAT S⟩ : T)) :
    Prime (⟨φ S, hAT S⟩ : T) := by
  have hSW : ¬ (S ∣ W) := by
    rintro ⟨g, rfl⟩
    have hone : (⟨φ S, hAT S⟩ : T) * (⟨v * φ g, T.mul_mem hv (hAT g)⟩ : T) = 1 := by
      apply Subtype.ext
      show φ S * (v * φ g) = 1
      rw [map_mul] at hvW
      calc φ S * (v * φ g) = v * (φ S * φ g) := by ring
        _ = 1 := hvW
    exact hSnonunit ⟨⟨_, _, hone, (mul_comm _ _).trans hone⟩, rfl⟩
  refine ⟨?_, hSnonunit, ?_⟩
  · intro hzero
    exact hS.ne_zero (hφ (by simpa using congrArg Subtype.val hzero))
  · rintro a b ⟨c, hc⟩
    have hcE : (a : E) * (b : E) = φ S * (c : E) := congrArg Subtype.val hc
    obtain ⟨Na, fa, hfa⟩ := hclear a
    obtain ⟨Nb, fb, hfb⟩ := hclear b
    obtain ⟨Nc, fc, hfc⟩ := hclear c
    have hkey : φ (W ^ Nc * (fa * fb)) = φ (S * (W ^ (Na + Nb) * fc)) := by
      have h1 : φ (W ^ Nc * (fa * fb))
          = (φ W) ^ Nc * (((φ W) ^ Na * (a : E)) * ((φ W) ^ Nb * (b : E))) := by
        rw [map_mul, map_mul, map_pow, hfa, hfb]
      have h2 : φ (S * (W ^ (Na + Nb) * fc))
          = φ S * ((φ W) ^ (Na + Nb) * ((φ W) ^ Nc * (c : E))) := by
        rw [map_mul, map_mul, map_pow, hfc]
      rw [h1, h2, pow_add]
      calc (φ W) ^ Nc * (((φ W) ^ Na * (a : E)) * ((φ W) ^ Nb * (b : E)))
          = ((φ W) ^ Na * (φ W) ^ Nb) * ((φ W) ^ Nc * ((a : E) * (b : E))) := by ring
        _ = ((φ W) ^ Na * (φ W) ^ Nb) * ((φ W) ^ Nc * (φ S * (c : E))) := by rw [hcE]
        _ = φ S * ((φ W) ^ Na * (φ W) ^ Nb * ((φ W) ^ Nc * (c : E))) := by ring
    have hdvd2 : S ∣ fa * fb := by
      have hdvd : S ∣ W ^ Nc * (fa * fb) := ⟨W ^ (Na + Nb) * fc, hφ hkey⟩
      rcases hS.dvd_mul.mp hdvd with h | h
      · exact absurd (hS.dvd_of_dvd_pow h) hSW
      · exact h
    have hsplit : ∀ (N : ℕ) (t : T) (f g : R), (φ W) ^ N * (t : E) = φ f → f = S * g →
        (⟨φ S, hAT S⟩ : T) ∣ t := by
      intro N t f g hf hfg
      refine ⟨⟨v ^ N * φ g, T.mul_mem (T.pow_mem hv N) (hAT g)⟩, ?_⟩
      apply Subtype.ext
      show (t : E) = φ S * (v ^ N * φ g)
      have hvN : v ^ N * (φ W) ^ N = 1 := by rw [← mul_pow, hvW, one_pow]
      calc (t : E) = v ^ N * ((φ W) ^ N * (t : E)) := by
            rw [← mul_assoc, hvN, one_mul]
        _ = v ^ N * φ f := by rw [hf]
        _ = φ S * (v ^ N * φ g) := by rw [hfg, map_mul]; ring
    rcases hS.dvd_mul.mp hdvd2 with h | h
    · obtain ⟨g, hg⟩ := h
      exact Or.inl (hsplit Na a fa g hfa hg)
    · obtain ⟨g, hg⟩ := h
      exact Or.inr (hsplit Nb b fb g hfb hg)

end GaloisForLFunctions.HTGeometry
