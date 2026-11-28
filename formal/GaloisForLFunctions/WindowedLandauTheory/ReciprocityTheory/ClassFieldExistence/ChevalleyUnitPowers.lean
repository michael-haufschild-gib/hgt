import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ChevalleyPrimePowerUnits
import Mathlib.Data.Nat.Factorization.Basic

/-! Chevalley's congruence theorem for global units. A modulus prime
to a prescribed integer forces its principal units to be n-th powers. -/

noncomputable section

open NumberField

namespace GlobalTheory.Reciprocity

private theorem combine_coprime_unit_powers (E : Type) [Field E] [NumberField E] (b m₁ m₂ : ℕ) (hcop : m₁.Coprime m₂)
    (h₁ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, v ^ m₁ = u)
    (h₂ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, v ^ m₂ = u) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 →
      ∃ v : (𝓞 E)ˣ, v ^ (m₁ * m₂) = u := by
  obtain ⟨a₁, ha₁, hc₁, hu₁⟩ := h₁
  obtain ⟨a₂, ha₂, hc₂, hu₂⟩ := h₂
  refine ⟨a₁ * a₂, Nat.mul_pos ha₁ ha₂, Nat.Coprime.mul hc₁ hc₂, ?_⟩
  intro u hu
  have hd₁ : (a₁ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₂ : 𝓞 E), by push_cast; ring⟩ hu
  have hd₂ : (a₂ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₁ : 𝓞 E), by push_cast; ring⟩ hu
  obtain ⟨v₁, hv₁⟩ := hu₁ u hd₁
  obtain ⟨v₂, hv₂⟩ := hu₂ u hd₂
  set s := Nat.gcdA m₁ m₂
  set t := Nat.gcdB m₁ m₂
  have hg : ((1 : ℕ) : ℤ) = (m₁ : ℤ) * s + (m₂ : ℤ) * t := by
    rw [← hcop.gcd_eq_one]; exact Nat.gcd_eq_gcd_ab m₁ m₂
  have key : u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := by
    rw [← hg]; simp
  have e1 : u ^ ((m₁ : ℤ) * s) = v₂ ^ (s * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [← hv₂]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have e2 : u ^ ((m₂ : ℤ) * t) = v₁ ^ (t * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [← hv₁]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  refine ⟨v₂ ^ s * v₁ ^ t, ?_⟩
  symm
  calc u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := key
    _ = u ^ ((m₁ : ℤ) * s) * u ^ ((m₂ : ℤ) * t) := zpow_add _ _ _
    _ = (v₂ ^ s * v₁ ^ t) ^ (m₁ * m₂) := by
      rw [e1, e2, zpow_mul, zpow_mul, ← mul_zpow, zpow_natCast]

theorem exists_coprime_congruence_for_unit_powers (E : Type) [Field E] [NumberField E]
    (n b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (c : 𝓞 E) ∣ u.val - 1 →
      ∃ z : (𝓞 E)ˣ, z ^ n = u := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p r hp _ => exact exists_coprime_congruence_for_primePower_units E p r b hp hb
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | one => exact ⟨1, one_pos, Nat.coprime_one_left b, fun u _ => ⟨u, pow_one u⟩⟩
  | coprime m n hm hn hcop ih₁ ih₂ =>
      exact combine_coprime_unit_powers E b m n hcop (ih₁ (by omega)) (ih₂ (by omega))

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_coprime_congruence_for_unit_powers
