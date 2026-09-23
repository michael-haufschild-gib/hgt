import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareGeneric
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail
import GaloisForLFunctions.RHTower.Sieve.GallagherAffineMeanSquare

/-!
# The dyadic mean square with the far tail paid dyadically

`dyadicMeanSquare_le_largeValues` pays the frequencies beyond `W` by the *global* size
`M₂ = sup_w ‖logPoly a s w‖²`, which for a polynomial of length `M` is `M²`.  That is a factor `M`
worse than the truth: the Gallagher weight decays quadratically, so cutting the far range into
dyadic annuli and paying each by the mean value theorem replaces `M₂` by the coefficients' `ℓ²`
mass.  `gallagher_split_integral_dyadic` does exactly this, under an affine majorant

```text
∫_{|w| ≤ T} ‖logPoly a s w‖² ≤ α·T + β        (T ≥ W) ,
```

and costs `2δ²(αW + β) + 4α/(π²W) + 4β/(3π²W²)`.  Running the generic chain of
`LinearMeanSquareGeneric` over that budget gives

```text
dyadicMeanSquare f ℓ A B ≤ A(1+ε)^{K'} · K' ·
    blockCostG ℓ ε ( 2 log(1+ℓ/A)²(αW + β) + 4α/(π²W) + 4β/(3π²W²) ) .
```

The `ℓ¹` coefficient mass has disappeared from the whole route: every frequency, near and far, is
paid by a mean square.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The dyadic mean square, with all frequencies paid by mean squares.** -/
theorem dyadicMeanSquare_le_dyadicTail (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {ℓ A B M K' : ℕ} {ε α β W : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε) (hW : 0 < W)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hG : ∀ T : ℝ, W ≤ T →
      (∫ w in Set.Icc (-T) T, ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
        ≤ α * T + β) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K')
          * ((K' : ℝ) * blockCostG (ℓ : ℝ) ε
              (2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ (2 : ℕ) * (α * W + β)
                + (4 * α / (Real.pi ^ (2 : ℕ) * W) + 4 * β / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ))))) := by
  have hpi := Real.pi_pos
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hlogA : 0 ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (ℓ : ℝ) / (A : ℝ) := by positivity
    linarith
  have hmass : (0 : ℝ) ≤ α * W + β := by positivity
  set G : ℝ := 2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ (2 : ℕ) * (α * W + β)
      + (4 * α / (Real.pi ^ (2 : ℕ) * W) + 4 * β / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ))) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    have h1 : (0 : ℝ) ≤ 2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ (2 : ℕ) * (α * W + β) :=
      mul_nonneg (by positivity) hmass
    have h2 : (0 : ℝ) ≤ 4 * α / (Real.pi ^ (2 : ℕ) * W) := by positivity
    have h3 : (0 : ℝ) ≤ 4 * β / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ)) := by positivity
    linarith
  refine dyadicMeanSquare_le_gen f hf hℓ hA hAB hε hG0 hM hcover ?_
  intro Y' hY' E
  have hY'0 : (0 : ℝ) < Y' := lt_of_lt_of_le hA0 hY'
  have hδ0 : 0 < Real.log (1 + (ℓ : ℝ) / Y') := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < (ℓ : ℝ) / Y' := by positivity
    linarith
  -- the set integral is at most the whole-line one
  have hint := integrable_normSq_logWindowSum (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M)
    (Real.log (1 + (ℓ : ℝ) / Y'))
  have hnn : 0 ≤ᵐ[volume] fun u : ℝ =>
      ‖logWindowSum (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M)
        (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun u => by positivity
  refine le_trans (setIntegral_le_integral hint hnn) ?_
  refine le_trans (gallagher_split_integral_dyadic (fun n => ((f n : ℝ) : ℂ))
    (Finset.Icc 1 M) hδ0 hW hG) ?_
  -- and the width is largest at the base point
  have hmono : Real.log (1 + (ℓ : ℝ) / Y') ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have : (ℓ : ℝ) / Y' ≤ (ℓ : ℝ) / (A : ℝ) := div_le_div_of_nonneg_left hℓ0.le hA0 hY'
    linarith
  have hsq : Real.log (1 + (ℓ : ℝ) / Y') ^ (2 : ℕ) ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hδ0.le hmono 2
  rw [hGdef]
  have hmul := mul_le_mul_of_nonneg_right hsq hmass
  linarith

/-- **The unconditional baseline.**  With no arithmetic input at all — only the mean value theorem's
affine majorant `α = (5π/2)M`, `β = (5e/2)M² + (5/4)M` — the dyadic mean square of any unit-bounded
weight is already bounded.  Every arithmetic estimate for `logPoly` is measured against this. -/
theorem dyadicMeanSquare_le_meanValue (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {ℓ A B M K' : ℕ} {ε W : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε) (hW : 0 < W)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K') :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K')
          * ((K' : ℝ) * blockCostG (ℓ : ℝ) ε
              (2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ (2 : ℕ)
                    * ((5 * Real.pi / 2) * (M : ℝ) * W
                        + ((5 * Real.exp 1 / 2) * (M : ℝ) ^ (2 : ℕ) + (5 / 4) * (M : ℝ)))
                + (4 * ((5 * Real.pi / 2) * (M : ℝ)) / (Real.pi ^ (2 : ℕ) * W)
                    + 4 * ((5 * Real.exp 1 / 2) * (M : ℝ) ^ (2 : ℕ) + (5 / 4) * (M : ℝ))
                        / (3 * Real.pi ^ (2 : ℕ) * W ^ (2 : ℕ))))) := by
  have hpi := Real.pi_pos
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  refine dyadicMeanSquare_le_dyadicTail f hf hℓ hA hAB hε hW (by positivity) (by positivity)
    hM hcover ?_
  intro T hT
  have hT0 : (0 : ℝ) ≤ T := le_trans hW.le hT
  refine le_trans (integral_Icc_normSq_logPoly_le_affine_majorant
    (fun n => ((f n : ℝ) : ℂ)) M hT0) ?_
  -- the two coefficient masses are at most `M` and `M²`
  have hnorm : ∀ m : Fin M, ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ) ≤ 1 := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [hf ((m : ℕ) + 1), abs_nonneg (f ((m : ℕ) + 1))]
  have hS : (∑ m : Fin M, ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ)) ≤ (M : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun m _ => hnorm m) ?_
    simp
  have hS0 : (0 : ℝ) ≤ ∑ m : Fin M, ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hS1 : (∑ m : Fin M, (((m : ℕ) : ℝ) + 1) * ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ))
      ≤ (M : ℝ) ^ (2 : ℕ) := by
    have hterm : ∀ m : Fin M, (((m : ℕ) : ℝ) + 1) * ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ)
        ≤ (M : ℝ) := by
      intro m
      have hm : (((m : ℕ) : ℝ) + 1) ≤ (M : ℝ) := by
        have : (m : ℕ) + 1 ≤ M := m.2
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ (((m : ℕ) : ℝ) + 1) := by positivity
      nlinarith [hnorm m, h0, hm, sq_nonneg ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖]
    refine le_trans (Finset.sum_le_sum fun m _ => hterm m) ?_
    simp [Finset.sum_const, Finset.card_univ]
    nlinarith [hM0]
  have hS10 : (0 : ℝ) ≤ ∑ m : Fin M, (((m : ℕ) : ℝ) + 1) * ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep1 : (5 * Real.pi / 2) * (∑ m : Fin M, ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ)) * T
      ≤ (5 * Real.pi / 2) * (M : ℝ) * T := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ) ≤ 5 * Real.pi / 2)
    nlinarith [this, hT0]
  have hstep2 : (5 * Real.exp 1 / 2)
      * (∑ m : Fin M, (((m : ℕ) : ℝ) + 1) * ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ))
      ≤ (5 * Real.exp 1 / 2) * (M : ℝ) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hstep3 : (5 / 4 : ℝ) * (∑ m : Fin M, ‖((f ((m : ℕ) + 1) : ℝ) : ℂ)‖ ^ (2 : ℕ))
      ≤ (5 / 4 : ℝ) * (M : ℝ) :=
    mul_le_mul_of_nonneg_left hS (by norm_num)
  linarith

end RHTower.Sieve

end
