import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSelfBound

/-!
# Integer square-root scale in the Heath--Brown sparse mean value

This file selects the first paper scale without a real-to-natural rounding premise and simplifies
the exact one-step self-bound at that scale.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- Quotient by the natural square root loses at most two. -/
theorem heathBrown_natDiv_sqrt_le_add_two (N : ℕ) (hN : 1 ≤ N) :
    N / N.sqrt ≤ N.sqrt + 2 := by
  have hK : 0 < N.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hlt := Nat.lt_succ_sqrt N
  apply Nat.div_le_of_le_mul
  nlinarith

/-- The square of the natural square root stays below its argument. -/
theorem heathBrown_sqrt_mul_sqrt_le (N : ℕ) : N.sqrt * N.sqrt ≤ N := by
  exact Nat.le_sqrt.mp le_rfl

/-- First Heath--Brown branch with the exact integer square-root scale selected. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_le_sqrtScale
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    {X : ℝ} (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X)
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) :
    let I : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
      ‖heathBrownSparseFactor A (fun _ => 1) t *
        heathBrownDenseFactor (heathBrownPositiveInterval N hN)
          heathBrownDenseUnitWeight t‖ ^ 2
    let k : ℝ :=
      ((5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
        (heathBrownSquareDivisorScale N.sqrt eta ^ 2 * (25 * Real.pi / 8) *
          (25 * Real.pi / 8))
    I ≤ 75 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
      5 * Real.pi * (T : ℝ) * ((2 * N.sqrt + 5 : ℕ) : ℝ) * (A.card : ℝ) ^ 2 +
      ((25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ)) ^ 2 * k := by
  dsimp only
  let I : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight t‖ ^ 2
  let k : ℝ :=
    ((5 * Real.pi * Real.exp 1 * X +
        (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
      (heathBrownSquareDivisorScale N.sqrt eta ^ 2 * (25 * Real.pi / 8) *
        (25 * Real.pi / 8))
  have hK : 1 ≤ N.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hKsq : N.sqrt * N.sqrt ≤ N := heathBrown_sqrt_mul_sqrt_le N
  have hbase := integral_Icc_normSq_heathBrown_fullUnit_le_oneStepSelfBound
    A T hT hA hK hN hKsq heta
  dsimp only at hbase
  have hq := heathBrown_natDiv_sqrt_le_add_two N hN
  have hq1 : ((N / N.sqrt + 1 : ℕ) : ℝ) ≤ ((N.sqrt + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : N / N.sqrt + 1 ≤ N.sqrt + 3)
  have hq2 : ((2 * (N / N.sqrt) + 1 : ℕ) : ℝ) ≤
      ((2 * N.sqrt + 5 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * (N / N.sqrt) + 1 ≤ 2 * N.sqrt + 5)
  have hMS : 0 ≤
      (5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ) :=
    heathBrownSparseMeanSquareEnvelope_nonneg A hA
      (heathBrownHalfHeight T).property.le
  have hk0 : 0 ≤ k := by
    dsimp only [k]
    positivity
  have hclean : I ≤
      75 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        5 * Real.pi * (T : ℝ) * ((2 * (N / N.sqrt) + 1 : ℕ) : ℝ) *
          (A.card : ℝ) ^ 2 +
        ((25 * Real.pi / 4) * ((N / N.sqrt + 1 : ℕ) : ℝ)) ^ 2 * k := by
    calc
      I ≤ 2 * ((5 * Real.pi / 2) * (T : ℝ) *
          (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            ((2 * (N / N.sqrt) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)) +
          ((5 * Real.pi / 2) * (T : ℝ) *
            (((N / N.sqrt + 1 : ℕ) : ℝ) * (5 / (2 * (T : ℝ))))) ^ 2 * k := by
        simpa only [I, k] using hbase
      _ = 75 * Real.pi * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
          5 * Real.pi * (T : ℝ) * ((2 * (N / N.sqrt) + 1 : ℕ) : ℝ) *
            (A.card : ℝ) ^ 2 +
          ((25 * Real.pi / 4) * ((N / N.sqrt + 1 : ℕ) : ℝ)) ^ 2 * k := by
        have hT0 : (T : ℝ) ≠ 0 := ne_of_gt T.property
        field_simp
        ring
  have hterm2 :
      5 * Real.pi * (T : ℝ) * ((2 * (N / N.sqrt) + 1 : ℕ) : ℝ) *
          (A.card : ℝ) ^ 2 ≤
        5 * Real.pi * (T : ℝ) * ((2 * N.sqrt + 5 : ℕ) : ℝ) *
          (A.card : ℝ) ^ 2 := by
    gcongr
  have hbsmall : 0 ≤ (25 * Real.pi / 4) * ((N / N.sqrt + 1 : ℕ) : ℝ) := by positivity
  have hbbig : 0 ≤ (25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ) := by positivity
  have hb : (25 * Real.pi / 4) * ((N / N.sqrt + 1 : ℕ) : ℝ) ≤
      (25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ) := by gcongr
  have hterm3 :
      ((25 * Real.pi / 4) * ((N / N.sqrt + 1 : ℕ) : ℝ)) ^ 2 * k ≤
        ((25 * Real.pi / 4) * ((N.sqrt + 3 : ℕ) : ℝ)) ^ 2 * k := by
    gcongr
  exact hclean.trans (add_le_add (add_le_add_right hterm2 _) hterm3)

end RHTower.Sieve
