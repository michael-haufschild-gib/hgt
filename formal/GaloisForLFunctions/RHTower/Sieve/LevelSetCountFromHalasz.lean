import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryLogPolyBlock

/-!
# The level-set count straight from Halász–Montgomery

A spaced family of frequencies on which a block polynomial exceeds a threshold `V` contributes at
least `#S · V²` to the Halász–Montgomery sum, so the inequality bounds `#S` as soon as `V²` beats
the *diagonal* term `(1 + 214√T + 1536 N/√U)·‖c‖²`.

This is the level-set count with **no restriction on the level beyond that threshold**.  It is the
form the block-product estimate consumes through its opaque count hypothesis, and it reaches the
levels near the `L²` size of the coefficient vector, which is where a rarity statement has content.

* `card_le_levelSet_blockPoly`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The level-set count from the Halász–Montgomery inequality.**  Stated multiplicatively, so no
positivity of the denominator is needed to state it. -/
theorem card_le_levelSet_blockPoly (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (sigma : ℝ)
    {S : Finset ℝ} {delta U T V Kmax : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hKmax : ((S.card : ℕ) : ℝ) ≤ Kmax) (hKmax1 : 1 ≤ Kmax)
    (hlevel : ∀ t ∈ S, V ≤ ‖blockPoly N c sigma t‖) :
    ((S.card : ℕ) : ℝ) * (V ^ (2 : ℕ) - (1 + 214 * Real.sqrt T
          + 1536 * ((N : ℝ) / Real.sqrt U)) * ‖blockCoeff N c sigma‖ ^ (2 : ℕ))
      ≤ ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log Kmax))
          * ‖blockCoeff N c sigma‖ ^ (2 : ℕ) := by
  set D : ℝ := 1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U) with hD
  set A : ℝ := ‖blockCoeff N c sigma‖ ^ (2 : ℕ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hHM := halaszMontgomery_blockPoly_real_finset_sigma N hN c sigma hdelta hU hT hsep
    hspread hnear hlamT
  have hlow : ((S.card : ℕ) : ℝ) * V ^ (2 : ℕ) ≤ ∑ t ∈ S, ‖blockPoly N c sigma t‖ ^ (2 : ℕ) := by
    have hterm : ∀ t ∈ S, V ^ (2 : ℕ) ≤ ‖blockPoly N c sigma t‖ ^ (2 : ℕ) := by
      intro t ht
      exact pow_le_pow_left₀ hV (hlevel t ht) 2
    calc ((S.card : ℕ) : ℝ) * V ^ (2 : ℕ) = ∑ _t ∈ S, V ^ (2 : ℕ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ S, ‖blockPoly N c sigma t‖ ^ (2 : ℕ) := Finset.sum_le_sum hterm
  have hlogle : Real.log ((S.card : ℕ) : ℝ) ≤ Real.log Kmax := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hKmax1
    · exact Real.log_le_log (by exact_mod_cast hpos) hKmax
  have hcard0 : (0 : ℝ) ≤ ((S.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hchain : ((S.card : ℕ) : ℝ) * V ^ (2 : ℕ)
      ≤ ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log Kmax)
          + ((S.card : ℕ) : ℝ) * D) * A := by
    refine le_trans hlow (le_trans hHM ?_)
    refine mul_le_mul_of_nonneg_right ?_ hA0
    have hmono : (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log ((S.card : ℕ) : ℝ))
        ≤ (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log Kmax) := by
      refine mul_le_mul_of_nonneg_left (by linarith [hlogle]) ?_
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      positivity
    linarith
  nlinarith [hchain, hA0, hcard0]


/-- **The level-set count in explicit form.**  Once the level beats twice the diagonal term, the
count is the classical `N‖a‖²/V²` up to the Kuzmin–Landau logarithm and a factor two. -/
theorem card_le_levelSet_blockPoly_of_threshold (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (sigma : ℝ)
    {S : Finset ℝ} {delta U T V Kmax : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T) (hV : 0 < V)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hKmax : ((S.card : ℕ) : ℝ) ≤ Kmax) (hKmax1 : 1 ≤ Kmax)
    (hlevel : ∀ t ∈ S, V ≤ ‖blockPoly N c sigma t‖)
    (hthresh : 2 * ((1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))
        * ‖blockCoeff N c sigma‖ ^ (2 : ℕ)) ≤ V ^ (2 : ℕ)) :
    ((S.card : ℕ) : ℝ)
      ≤ 2 * (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log Kmax))
          * ‖blockCoeff N c sigma‖ ^ (2 : ℕ)) / V ^ (2 : ℕ) := by
  have hmain := card_le_levelSet_blockPoly N hN c sigma hdelta hU hT hV.le hsep hspread hnear
    hlamT hKmax hKmax1 hlevel
  have hhalf : V ^ (2 : ℕ) / 2 ≤ V ^ (2 : ℕ) - (1 + 214 * Real.sqrt T
      + 1536 * ((N : ℝ) / Real.sqrt U)) * ‖blockCoeff N c sigma‖ ^ (2 : ℕ) := by linarith
  have hcard0 : (0 : ℝ) ≤ ((S.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hstep : ((S.card : ℕ) : ℝ) * (V ^ (2 : ℕ) / 2)
      ≤ ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log Kmax))
          * ‖blockCoeff N c sigma‖ ^ (2 : ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left hhalf hcard0) hmain
  have hV2 : (0 : ℝ) < V ^ (2 : ℕ) := by positivity
  rw [le_div_iff₀ hV2]
  linarith

end

end RHTower.Sieve
