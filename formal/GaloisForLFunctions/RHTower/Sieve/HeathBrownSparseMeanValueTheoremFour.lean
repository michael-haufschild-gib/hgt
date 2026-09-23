import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueTheoremFourAlgebra

/-!
# Heath--Brown sparse mean value, Theorem 4(iii)

Exact explicit-constant form of the published estimate.  Sparse phases and dense coefficients are
arbitrary in their source ranges.  Canonical second-scale selection, all rounding, divisor loss,
and exponent absorption are discharged internally.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- Explicit `eta`-dependent constant in Heath--Brown's Theorem 4(iii). -/
def heathBrownTheoremFourCoefficient (eta : ℝ) : ℝ :=
  heathBrownTheoremFourUniversalCoefficient *
    (divisorBoundConst (eta / 4) ^ (2 : ℕ) * (3 : ℝ) ^ eta)

/-- Heath--Brown's sparse mean-value estimate, Theorem 4(iii), with an explicit constant.

This is the coefficient-faithful form: sparse phases are arbitrary circle values, dense
coefficients are arbitrary values in `[0,1]`, and the only assumptions are the theorem's support,
height, and positive-exponent conditions. -/
theorem integral_Icc_normSq_heathBrown_factors_le_theoremFour
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ)) ≤
      95 * Real.pi / 2 * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        heathBrownTheoremFourCoefficient eta * (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
            (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)) := by
  by_cases hA0 : A.card = 0
  · have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
    subst A
    simp [heathBrownSparseFactor]
  by_cases hN0 : N = 0
  · subst N
    have hBe : B = ∅ := by
      ext n
      constructor
      · intro hn
        exfalso
        have hnle := hB n hn
        have hnpos : 1 ≤ (n : ℕ) := n.pos
        omega
      · intro hn
        simp at hn
    subst B
    simp [heathBrownDenseFactor, heta.ne']
  let K : ℕ := heathBrownSecondScale (T : ℝ) (A.card : ℝ)
  let D : ℝ := heathBrownSquareDivisorScale K (eta / 4)
  let L : ℝ :=
    (divisorBoundConst (eta / 4) ^ (2 : ℕ) * (3 : ℝ) ^ eta) *
      (((N : ℝ) * (T : ℝ)) ^ eta)
  have hN : 1 ≤ N := by omega
  have hR : 0 < (A.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hA0
  have hRT : (A.card : ℝ) ≤ (T : ℝ) :=
    cast_card_le_height_of_pnat_support A T.property.le hA
  have hK : 1 ≤ K := one_le_heathBrownSecondScale (by linarith)
  have hKpos : 0 < K := by omega
  have hdiv : K * K / K = K := Nat.mul_div_right K hKpos
  have hheight : (T : ℝ) ≤ (K : ℝ) ^ (3 : ℕ) :=
    height_le_heathBrownSecondScale_cube T.property.le
  have hmixed :
      (T : ℝ) * (A.card : ℝ) ^ (2 : ℕ) / (K : ℝ) ≤
        (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) :=
    heathBrown_height_mul_card_sq_div_secondScale_le_mixed (by linarith) hR
  have hcross :
      (K : ℝ) * (A.card : ℝ) * Real.sqrt ((T : ℝ) * (A.card : ℝ)) ≤
        3 * ((A.card : ℝ) * (T : ℝ) +
          (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)) :=
    heathBrownSecondScale_mul_card_sqrt_le (by linarith) hR
  have hD2 : D ^ (2 : ℕ) ≤ L := by
    exact heathBrownSquareDivisorScale_secondScale_sq_le
      (by linarith) (Nat.cast_nonneg _) hRT hN heta
  have hDone : 1 ≤ D := by
    exact one_le_heathBrownSquareDivisorScale hK (by positivity)
  have hL : 1 ≤ L := le_trans (by nlinarith : (1 : ℝ) ≤ D ^ (2 : ℕ)) hD2
  have hbase := integral_Icc_normSq_heathBrown_factors_le_selectedSecondScale
    A B eps q T hT hA hB (eta := eta / 4) (by positivity)
  dsimp only at hbase
  have hKdef : heathBrownSecondScale (T : ℝ) (A.card : ℝ) = K := rfl
  rw [hKdef] at hbase
  have hDdef : heathBrownSquareDivisorScale K (eta / 4) = D := rfl
  rw [hDdef] at hbase
  have hraw :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ)) ≤
        95 * Real.pi / 2 * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
          15 * Real.pi / 2 * (N : ℝ) *
            ((T : ℝ) * (A.card : ℝ) ^ (2 : ℕ) / (K : ℝ)) +
          (25 * Real.pi / 2) * ((N : ℝ) / (K : ℝ)) *
            Real.sqrt
              (heathBrownMeanSquareCoefficient * (T : ℝ) * (A.card : ℝ) * D ^ (2 : ℕ) *
                (2 *
                    (75 * Real.pi / 2 * (K : ℝ) ^ (4 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
                      5 * Real.pi / 2 * (T : ℝ) * (2 * (K : ℝ) + 1) *
                        (A.card : ℝ) ^ (2 : ℕ)) +
                  (25 * Real.pi / 4 * ((K : ℝ) + 1)) ^ (2 : ℕ) *
                    (heathBrownMeanSquareCoefficient * (T : ℝ) *
                      (A.card : ℝ) * D ^ (2 : ℕ)))) := by
    calc
      _ ≤ _ := hbase
      _ = _ := by
        simp only [hdiv, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        dsimp only [heathBrownMeanSquareCoefficient, heathBrownHalfHeight]
        field_simp
        ring
  have hscalar := heathBrown_twoStep_scalar_absorption
    (T := (T : ℝ)) (R := (A.card : ℝ)) (N := (N : ℝ)) (K := (K : ℝ))
    (D := D) (L := L) hT hR (Nat.cast_nonneg N)
      (by exact_mod_cast hK) hheight hmixed hcross hD2 hL
  dsimp only at hscalar
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ)) ≤
      95 * Real.pi / 2 * (N : ℝ) ^ (2 : ℕ) * (A.card : ℝ) ^ (2 : ℕ) +
        heathBrownTheoremFourUniversalCoefficient * L *
          ((N : ℝ) * (A.card : ℝ) * (T : ℝ) +
            (N : ℝ) * (A.card : ℝ) ^ (7 / 4 : ℝ) *
              (T : ℝ) ^ (3 / 4 : ℝ)) := hraw.trans hscalar
    _ = _ := by
      dsimp only [L, heathBrownTheoremFourCoefficient]
      ring

end

end RHTower.Sieve
