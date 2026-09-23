import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCaseThreeTwo

/-!
# CASE 3.2 of Grynkiewicz's STEP 3

`case32_false` shows that for `t ≥ 3` a maximal Dyson witness cannot have fewer than `t` points in
its small part, once `#A ≥ #B ≥ 2t + 1`, `B` meets at least two cosets of `S(T · B)`, and the weak
Pollard bound fails.

The proof feeds `#T ≤ #A − #B + t − 1` (from `qubal` and `card_dysonFull_add_card_le`) into
Lemma 2.1 at `k = t − 1`.  Whichever of the two terms of Lemma 2.1 is the minimum, the resulting
inequality is impossible: the first gives `(#A − 2t)(#B − 2t) ≤ 0`, the second reduces — after
`case32_denominator` rewrites the denominator as `#A·#B − (#B − t + 1)²` — to the cubic
inequality `case32_key`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **CASE 3.2 of Grynkiewicz's STEP 3.**  For `t ≥ 3`, a maximal Dyson witness with fewer than
`t` points in its small part is impossible once `#A ≥ #B ≥ 2t + 1`, `B` is spread over at least
two cosets of `S(T · B)`, and the weak Pollard bound fails. -/
theorem case32_false {A B : Finset G} {x₀ : G} {t : ℕ}
    (ht : 3 ≤ t) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) (hBbig : 2 * t + 1 ≤ B.card)
    (hkle : (dysonSmall A B x₀).card + 1 ≤ t)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B x₀).card)
    (hspread : ∀ c : G, ¬ (B ⊆ c • mulStab (dysonFull A B * B)))
    (hTne : (dysonFull A B).Nonempty)
    (hweakfail : repSum A B t + 2 * t ^ (2 : ℕ) + 1 ≤ t * A.card + t * B.card) :
    False := by
  classical
  -- the `#T` bound
  have hqub := qubal hmax hkle hspread
  have hTbound := card_dysonFull_add_card_le t hTne hB hqub
  -- Lemma 2.1 with `k = t - 1`
  have hk : ∀ x : G, x ∉ dysonFull A B → rep A B⁻¹ x ≤ t - 1 := by
    intro x hx
    have := rep_inv_le_of_notMem_dysonFull hmax hx
    omega
  have hk1 : 1 ≤ t - 1 := by omega
  have hkB : t - 1 ≤ B.card := by omega
  have hlem := repSum_ge_min_of_rep_inv_le (T := dysonFull A B) (k := t - 1) (t := t)
    (by omega) hA hB hk1 hkB hk
  have httcast : (((t - 1 : ℕ)) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [httcast] at hlem
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have httpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hbbig : 2 * (t : ℝ) + 1 ≤ (B.card : ℝ) := by exact_mod_cast hBbig
  have hba : (B.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hBA
  have hapos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hA
  have hTpos : (0 : ℝ) ≤ ((dysonFull A B).card : ℝ) := Nat.cast_nonneg _
  have hTle : ((dysonFull A B).card : ℝ) ≤ (A.card : ℝ) - (B.card : ℝ) + (t : ℝ) - 1 := by
    have h2 : (((dysonFull A B).card : ℕ) : ℝ) + (B.card : ℝ) + 1 ≤ (A.card : ℝ) + (t : ℝ) := by
      exact_mod_cast hTbound
    linarith
  have hsum : ((repSum A B t : ℕ) : ℝ)
      ≤ (t : ℝ) * ((A.card : ℝ) + (B.card : ℝ) - 2 * (t : ℝ)) := by
    have h2 : ((repSum A B t : ℕ) : ℝ) + 2 * (t : ℝ) ^ (2 : ℕ) + 1
        ≤ (t : ℝ) * (A.card : ℝ) + (t : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hweakfail
    nlinarith [h2]
  rcases min_cases ((t : ℝ) * ((A.card : ℝ) * (B.card : ℝ))
        / ((t : ℝ) + Real.sqrt ((t : ℝ) * ((t : ℝ) - 1))))
      ((t : ℝ) * (A.card : ℝ) ^ (2 : ℕ) * (B.card : ℝ)
        / (((t : ℝ) - 1) * (A.card : ℝ)
            + ((dysonFull A B).card : ℝ) * ((B.card : ℝ) - ((t : ℝ) - 1))))
      with ⟨hmin, _⟩ | ⟨hmin, _⟩
  · rw [hmin] at hlem
    have hchain : (A.card : ℝ) * (B.card : ℝ) / 2
        ≤ (t : ℝ) * ((A.card : ℝ) + (B.card : ℝ) - 2 * (t : ℝ)) := by
      calc (A.card : ℝ) * (B.card : ℝ) / 2
          ≤ (t : ℝ) * ((A.card : ℝ) * (B.card : ℝ))
              / ((t : ℝ) + Real.sqrt ((t : ℝ) * ((t : ℝ) - 1))) :=
            half_le_first_term ht1 (M := (A.card : ℝ) * (B.card : ℝ)) (by positivity)
        _ ≤ ((repSum A B t : ℕ) : ℝ) := hlem
        _ ≤ _ := hsum
    exact case32_first_branch hbbig hba hchain
  · rw [hmin] at hlem
    have hdenpos : (0 : ℝ) < ((t : ℝ) - 1) * (A.card : ℝ)
        + ((dysonFull A B).card : ℝ) * ((B.card : ℝ) - ((t : ℝ) - 1)) := by
      have h3 : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      nlinarith [hTpos, hapos, hbbig, h3]
    have hkey : (A.card : ℝ) ^ (2 : ℕ) * (B.card : ℝ)
        ≤ ((A.card : ℝ) + (B.card : ℝ) - 2 * (t : ℝ))
          * (((t : ℝ) - 1) * (A.card : ℝ)
             + ((dysonFull A B).card : ℝ) * ((B.card : ℝ) - ((t : ℝ) - 1))) := by
      rw [div_le_iff₀ hdenpos] at hlem
      nlinarith [hlem, hsum, httpos, hdenpos]
    have hden : ((t : ℝ) - 1) * (A.card : ℝ)
        + ((dysonFull A B).card : ℝ) * ((B.card : ℝ) - ((t : ℝ) - 1))
        ≤ (A.card : ℝ) * (B.card : ℝ) - ((B.card : ℝ) - (t : ℝ) + 1) ^ (2 : ℕ) := by
      nlinarith [hTle, hbbig, ht1]
    have habpos : (0 : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) - 2 * (t : ℝ) := by linarith
    have hfin : (A.card : ℝ) ^ (2 : ℕ) * (B.card : ℝ)
        ≤ ((A.card : ℝ) + (B.card : ℝ) - 2 * (t : ℝ))
          * ((A.card : ℝ) * (B.card : ℝ) - ((B.card : ℝ) - (t : ℝ) + 1) ^ (2 : ℕ)) :=
      le_trans hkey (mul_le_mul_of_nonneg_left hden habpos)
    have hcase := case32_key ht1 hbbig hba
    nlinarith [hfin, hcase]

end GaloisForLFunctions.HTGeometry.AddComb
