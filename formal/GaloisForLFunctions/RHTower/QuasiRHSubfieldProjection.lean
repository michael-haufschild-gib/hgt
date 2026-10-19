import GaloisForLFunctions.RHTower.QuasiRHSubfieldMoment
import Mathlib.Tactic.LinearCombination

/-!
# Affine-line projections of finite-field character packets

In a quadratic extension, a nonprincipal character trivial on the base-field
units has an exact two-valued line average. Averaging an arbitrary shift packet
therefore measures its occupancy on that affine line.
-/

noncomputable section

namespace RHTower.QuasiRHShiftCorrelation

open Finset
open scoped Classical

variable {F K : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]

private theorem quadraticAffine_bijective (hcard : Nat.card K = Nat.card F ^ 2)
    (x : K) (hx : x ∉ Set.range (algebraMap F K)) :
    Function.Bijective (fun p : F × F => algebraMap F K p.1 * x - algebraMap F K p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨b, a⟩ ⟨d, c⟩ h
    dsimp at h
    have hbd : b = d := by
      by_contra hbd
      have hden : algebraMap F K b - algebraMap F K d ≠ 0 :=
        sub_ne_zero.mpr (fun he => hbd ((algebraMap F K).injective he))
      apply hx
      refine ⟨(a - c) / (b - d), ?_⟩
      rw [map_div₀, map_sub, map_sub]
      apply (div_eq_iff hden).mpr
      linear_combination -h
    subst d
    have hac : a = c := by
      apply (algebraMap F K).injective
      linear_combination -h
    exact Prod.ext rfl hac
  · simpa only [Fintype.card_eq_nat_card, Nat.card_prod, pow_two] using hcard.symm

/-- The full subfield line has value `r-1` on that line and `-1` elsewhere. -/
theorem subfield_coset_character_sum (χ : MulChar K ℂ) (hnonprincipal : χ ≠ 1)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1)
    (hcard : Nat.card K = Nat.card F ^ 2) (x : K) :
    ∑ a : F, χ (x - algebraMap F K a) =
      (if x ∈ Set.range (algebraMap F K) then (Fintype.card F : ℂ) else 0) - 1 := by
  by_cases hx : x ∈ Set.range (algebraMap F K)
  · rw [if_pos hx]
    obtain ⟨u, rfl⟩ := hx
    have hp := subfield_shiftPacket χ hχ (univ : Finset F) u
    rw [sum_image (fun a _ b _ h => (algebraMap F K).injective h)] at hp
    simpa using hp
  · rw [if_neg hx, zero_sub]
    let L : ℂ := ∑ a : F, χ (x - algebraMap F K a)
    let e := Equiv.ofBijective _ (quadraticAffine_bijective hcard x hx)
    have hrow (b : F) :
        (∑ a : F, χ (algebraMap F K b * x - algebraMap F K a)) =
          if b = 0 then (Fintype.card F : ℂ) - 1 else L := by
      by_cases hb : b = 0
      · subst b
        rw [if_pos rfl]
        have hp (a : F) : χ (algebraMap F K 0 * x - algebraMap F K a) =
            1 - if a = 0 then 1 else 0 := by
          by_cases ha : a = 0
          · simp [ha, MulChar.map_zero]
          · rw [map_zero, zero_mul, zero_sub, ← map_neg,
              hχ (-a) (neg_ne_zero.mpr ha), if_neg ha, sub_zero]
        simp_rw [hp, sum_sub_distrib]
        simp
      · rw [if_neg hb]
        have hbe : algebraMap F K b ≠ 0 := by
          intro h
          exact hb ((algebraMap F K).injective (by simpa using h))
        have hp (a : F) :
            χ (algebraMap F K b * x - algebraMap F K a) =
              χ (x - algebraMap F K (a / b)) := by
          have he : algebraMap F K b * x - algebraMap F K a =
              algebraMap F K b * (x - algebraMap F K (a / b)) := by
            rw [map_div₀]
            field_simp [hbe]
          rw [he, map_mul, hχ b hb, one_mul]
        simp_rw [hp]
        exact Equiv.sum_comp (Equiv.divRight₀ b hb) (fun a => χ (x - algebraMap F K a))
    have hs := e.sum_comp (fun y => χ y)
    change (∑ p : F × F, χ (algebraMap F K p.1 * x - algebraMap F K p.2)) =
      ∑ y : K, χ y at hs
    rw [Fintype.sum_prod_type, MulChar.sum_eq_zero_of_ne_one hnonprincipal] at hs
    simp_rw [hrow] at hs
    have hsplit (b : F) :
        (if b = 0 then (Fintype.card F : ℂ) - 1 else L) =
          L + if b = 0 then (Fintype.card F : ℂ) - 1 - L else 0 := by
      split_ifs <;> ring
    simp_rw [hsplit, sum_add_distrib] at hs
    simp only [sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, if_true] at hs
    have hc : (Fintype.card F : ℂ) - 1 ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (ne_of_gt (Fintype.one_lt_card (α := F)))
    have hprod : ((Fintype.card F : ℂ) - 1) * (L + 1) = 0 := by
      linear_combination hs
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hprod).resolve_left hc)

/-- Scaling the subfield line retains the character phase and its exact constant correction. -/
theorem subfield_affineLine_character_sum (χ : MulChar K ℂ) (hnonprincipal : χ ≠ 1)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1)
    (hcard : Nat.card K = Nat.card F ^ 2) (u : K) (hu : u ≠ 0) (x : K) :
    ∑ a : F, χ (x - u * algebraMap F K a) =
      χ u * ((if x / u ∈ Set.range (algebraMap F K)
        then (Fintype.card F : ℂ) else 0) - 1) := by
  have hp (a : F) : χ (x - u * algebraMap F K a) =
      χ u * χ (x / u - algebraMap F K a) := by
    rw [← map_mul]
    congr 1
    field_simp
  simp_rw [hp, ← mul_sum]
  rw [subfield_coset_character_sum χ hnonprincipal hχ hcard]

/-- Averaging a shift packet on an affine line reads off its exact occupancy imbalance. -/
theorem subfield_affineLine_packet_sum (χ : MulChar K ℂ) (hnonprincipal : χ ≠ 1)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1)
    (hcard : Nat.card K = Nat.card F ^ 2) (u : K) (hu : u ≠ 0)
    (x : K) (S : Finset K) :
    ∑ a : F, ∑ h ∈ S, χ (x - u * algebraMap F K a - h) =
      χ u * ((Fintype.card F : ℂ) *
        (S.filter (fun h => (x - h) / u ∈ Set.range (algebraMap F K))).card - S.card) := by
  rw [sum_comm]
  have hp (h : K) :
      (∑ a : F, χ (x - u * algebraMap F K a - h)) =
        χ u * ((if (x - h) / u ∈ Set.range (algebraMap F K)
          then (Fintype.card F : ℂ) else 0) - 1) := by
    convert subfield_affineLine_character_sum χ hnonprincipal hχ hcard u hu (x - h)
      using 1
    apply sum_congr rfl
    intro a _
    congr 1
    ring
  simp_rw [hp, ← mul_sum, sum_sub_distrib]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  ring

end RHTower.QuasiRHShiftCorrelation
