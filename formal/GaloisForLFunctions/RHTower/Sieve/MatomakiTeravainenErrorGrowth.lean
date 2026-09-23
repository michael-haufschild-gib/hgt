import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenErrorLayers

/-!
# Mean-square accumulation for Matomäki--Teräväinen equation (2.16)

Successive source-error layers have coefficient cost `K^j`, hence square cost `K^(2j)`.
The exponent in (2.16) is the cumulative sum `∑_{0≤j≤J} 2j`.  This file proves the exact
finite mean-square induction, including a depth-independent constant.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Literal natural exponent in equation (2.16). -/
def mtIterationErrorExponent (J : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (J + 1), 2 * j

@[simp] theorem mtIterationErrorExponent_zero : mtIterationErrorExponent 0 = 0 := by
  simp [mtIterationErrorExponent]

theorem mtIterationErrorExponent_succ (J : ℕ) :
    mtIterationErrorExponent (J + 1) =
      mtIterationErrorExponent J + 2 * (J + 1) := by
  simp [mtIterationErrorExponent, Finset.sum_range_succ]

/-- Squared norm of a pointwise sum costs at most twice the two squared norms. -/
theorem norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖ ^ (2 : ℕ) ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
  have hnorm := norm_add_le x y
  have hxy : 0 ≤ ‖x‖ + ‖y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    ‖x + y‖ ^ (2 : ℕ) ≤ (‖x‖ + ‖y‖) ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) hxy).2 hnorm
    _ ≤ 2 * ‖x‖ ^ (2 : ℕ) + 2 * ‖y‖ ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Finite `L²` triangle inequality with the elementary factor `2`. -/
theorem sum_norm_add_sq_le_two (S : Finset ℕ) (f g : ℕ → ℂ) :
    ∑ n ∈ S, ‖f n + g n‖ ^ (2 : ℕ) ≤
      2 * (∑ n ∈ S, ‖f n‖ ^ (2 : ℕ)) +
        2 * (∑ n ∈ S, ‖g n‖ ^ (2 : ℕ)) := by
  calc
    ∑ n ∈ S, ‖f n + g n‖ ^ (2 : ℕ) ≤
        ∑ n ∈ S, (2 * ‖f n‖ ^ (2 : ℕ) + 2 * ‖g n‖ ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_add_sq_le_two (f n) (g n)
    _ = 2 * (∑ n ∈ S, ‖f n‖ ^ (2 : ℕ)) +
        2 * (∑ n ∈ S, ‖g n‖ ^ (2 : ℕ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Exact scalar absorption that keeps the implicit constant independent of iteration depth. -/
theorem mtIterationError_scalar_absorption
    {C Kreal : ℝ} {S r : ℕ} (hC : 0 ≤ C) (hK : 2 ≤ Kreal) (hr : 1 ≤ r) :
    2 * (8 * C * Kreal ^ S) + 2 * (C * Kreal ^ (2 * r)) ≤
      8 * C * Kreal ^ (S + 2 * r) := by
  have hKone : 1 ≤ Kreal := by linarith
  have hKS : 1 ≤ Kreal ^ S := by
    simpa using pow_le_pow_right₀ hKone (Nat.zero_le S)
  have hKsq : 4 ≤ Kreal ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (Kreal - 2)]
  have hpowMono : Kreal ^ (2 : ℕ) ≤ Kreal ^ (2 * r) :=
    pow_le_pow_right₀ hKone (by omega)
  have hKr : 4 ≤ Kreal ^ (2 * r) := hKsq.trans hpowMono
  have hscalar :
      16 * Kreal ^ S + 2 * Kreal ^ (2 * r) ≤
        8 * Kreal ^ S * Kreal ^ (2 * r) := by
    have hprod :
        0 ≤ (Kreal ^ S - 1) * (Kreal ^ (2 * r) - 4) :=
      mul_nonneg (sub_nonneg.mpr hKS) (sub_nonneg.mpr hKr)
    nlinarith
  rw [pow_add]
  calc
    2 * (8 * C * Kreal ^ S) + 2 * (C * Kreal ^ (2 * r)) =
        C * (16 * Kreal ^ S + 2 * Kreal ^ (2 * r)) := by ring
    _ ≤ C * (8 * Kreal ^ S * Kreal ^ (2 * r)) :=
      mul_le_mul_of_nonneg_left hscalar hC
    _ = 8 * C * (Kreal ^ S * Kreal ^ (2 * r)) := by ring

/-- Equation (2.16)'s finite induction.  A layer-`j` square bound `C K^(2j)` accumulates with
the source exponent `∑_{0≤j≤J}2j` and one absolute constant `8`. -/
theorem sum_norm_sq_sum_layers_le_iterationExponent
    (S : Finset ℕ) (errorLayer : ℕ → ℕ → ℂ)
    (C : ℝ) (K : ℕ) (hC : 0 ≤ C) (hK : 2 ≤ K)
    (J : ℕ)
    (hlayer : ∀ j ≤ J,
      ∑ n ∈ S, ‖errorLayer j n‖ ^ (2 : ℕ) ≤ C * (K : ℝ) ^ (2 * j)) :
    ∑ n ∈ S, ‖∑ j ∈ Finset.range (J + 1), errorLayer j n‖ ^ (2 : ℕ) ≤
      8 * C * (K : ℝ) ^ mtIterationErrorExponent J := by
  induction J with
  | zero =>
      have hzero : ∑ n ∈ S, ‖errorLayer 0 n‖ ^ (2 : ℕ) ≤ C := by
        simpa using hlayer 0 (by omega)
      have hC8 : C ≤ 8 * C := by nlinarith
      simpa [mtIterationErrorExponent] using hzero.trans hC8
  | succ J ih =>
      have hprevious := ih (fun j hj => hlayer j (hj.trans (Nat.le_succ J)))
      have hnew := hlayer (J + 1) (by omega)
      rw [mtIterationErrorExponent_succ]
      calc
        ∑ n ∈ S, ‖∑ j ∈ Finset.range (J + 2), errorLayer j n‖ ^ (2 : ℕ) =
            ∑ n ∈ S,
              ‖(∑ j ∈ Finset.range (J + 1), errorLayer j n) +
                errorLayer (J + 1) n‖ ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_range_succ]
        _ ≤ 2 * (∑ n ∈ S,
              ‖∑ j ∈ Finset.range (J + 1), errorLayer j n‖ ^ (2 : ℕ)) +
            2 * (∑ n ∈ S, ‖errorLayer (J + 1) n‖ ^ (2 : ℕ)) :=
          sum_norm_add_sq_le_two S _ _
        _ ≤ 2 * (8 * C * (K : ℝ) ^ mtIterationErrorExponent J) +
            2 * (C * (K : ℝ) ^ (2 * (J + 1))) := by
          gcongr
        _ ≤ 8 * C *
            (K : ℝ) ^ (mtIterationErrorExponent J + 2 * (J + 1)) := by
          exact mtIterationError_scalar_absorption hC (by exact_mod_cast hK) (by omega)

/-- Direct application to the exact accumulated source-error arithmetic function. -/
theorem MTFiniteIterationSourceData.sum_norm_sq_accumulatedError_le
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (S : Finset ℕ)
    (C : ℝ) (K : ℕ) (hC : 0 ≤ C) (hK : 2 ≤ K)
    (J : ℕ) (j : Fin (t + 1))
    (hlayer : ∀ layer ≤ J,
      ∑ n ∈ S, ‖mtSignedSourceErrorLayerAF data a layer j n‖ ^ (2 : ℕ) ≤
        C * (K : ℝ) ^ (2 * layer)) :
    ∑ n ∈ S, ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ (2 : ℕ) ≤
      8 * C * (K : ℝ) ^ mtIterationErrorExponent J := by
  rw [mtAccumulatedSourceErrorAF_eq_sum_signedLayers]
  simp only [arithmeticFunction_finset_sum_apply]
  exact sum_norm_sq_sum_layers_le_iterationExponent S
    (fun layer n => mtSignedSourceErrorLayerAF data a layer j n)
    C K hC hK J hlayer

end

end RHTower.Sieve
