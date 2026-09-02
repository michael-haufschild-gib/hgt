import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridModulusBilinear

/-!
# One-sided signed Kloosterman hybrid modulus form

One residue vector is fixed while the other is the additive Dirichlet vector at physical height.
This specialization admits an unconditional integrated baseline from the existing hybrid large
sieve, while retaining the signed modulus sum on the left.
-/

open Complex MeasureTheory Set Finset

namespace RHTower.Sieve

noncomputable section

/-- Signed modulus sum pairing one additive hybrid vector with a fixed residue vector. -/
def kloostermanHybridModulusLinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ)
    (a : ℕ → ℕ → ℂ) (b : (q : ℕ) → ZMod (q + 1) → ℂ) (t : ℝ) : ℂ :=
  ∑ q ∈ Q, w q *
    ∑ n : ZMod (q + 1), b q n * kloostermanHybridTransform q N (a q) n t

/-- Identification with the generic signed modulus bilinear form. -/
theorem kloostermanHybridModulusLinear_eq
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ)
    (a : ℕ → ℕ → ℂ) (b : (q : ℕ) → ZMod (q + 1) → ℂ) (t : ℝ) :
    kloostermanHybridModulusLinear Q w N a b t =
      kloostermanModulusBilinear Q w
        (fun q d => additiveHybridDirichletPoly q N (a q) d t) b := by
  unfold kloostermanHybridModulusLinear kloostermanModulusBilinear
    kloostermanBilinear kloostermanHybridTransform
  rfl

/-- The one-sided signed hybrid form is continuous in physical height. -/
theorem continuous_kloostermanHybridModulusLinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ)
    (a : ℕ → ℕ → ℂ) (b : (q : ℕ) → ZMod (q + 1) → ℂ) :
    Continuous (kloostermanHybridModulusLinear Q w N a b) := by
  unfold kloostermanHybridModulusLinear
  apply continuous_finsetSum
  intro q _hq
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro n _hn
  exact continuous_const.mul
    (continuous_kloostermanHybridTransform q N (a q) n)

/-- Pointwise direct-sum baseline with all square roots evaluated. -/
theorem norm_kloostermanHybridModulusLinear_sq_le_baseline
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ)
    (a : ℕ → ℕ → ℂ) (b : (q : ℕ) → ZMod (q + 1) → ℂ) (t : ℝ) :
    ‖kloostermanHybridModulusLinear Q w N a b t‖ ^ 2 ≤
      (∑ q ∈ Q, ‖w q‖ ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 *
        ∑ d : ZMod (q + 1),
          ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ 2) *
      ∑ q ∈ Q, ∑ n : ZMod (q + 1), ‖b q n‖ ^ 2 := by
  rw [kloostermanHybridModulusLinear_eq]
  have hbase := norm_kloostermanModulusBilinear_sq_le_baseline Q w
    (fun q d => additiveHybridDirichletPoly q N (a q) d t) b
  have ha : ∀ q : ℕ, 0 ≤ ∑ d : ZMod (q + 1),
      ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ 2 := fun q =>
    Finset.sum_nonneg fun d _ => sq_nonneg _
  have hb : ∀ q : ℕ, 0 ≤ ∑ n : ZMod (q + 1), ‖b q n‖ ^ 2 := fun q =>
    Finset.sum_nonneg fun n _ => sq_nonneg _
  simpa only [mul_pow, Real.sq_sqrt (ha _), Real.sq_sqrt (hb _), mul_assoc] using hbase

/-- Integrated one-sided baseline from the physical-height additive hybrid large sieve.  This is
the exact non-spectral cost against which a future modulus-average theorem must improve. -/
theorem integral_normSq_kloostermanHybridModulusLinear_le_baseline
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ)
    (a : ℕ → ℕ → ℂ) (b : (q : ℕ) → ZMod (q + 1) → ℂ)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T,
        ‖kloostermanHybridModulusLinear Q w N a b t‖ ^ 2) ≤
      (∑ q ∈ Q, ∑ n : ZMod (q + 1), ‖b q n‖ ^ 2) *
        ∑ q ∈ Q, ‖w q‖ ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 *
          ((5 * Real.pi * Real.exp 1 * (N : ℝ) +
              5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
            ∑ m ∈ Finset.Icc 1 N, ‖a q m‖ ^ 2) := by
  let I : Set ℝ := Set.Icc (-T) T
  let B : ℝ := ∑ q ∈ Q, ∑ n : ZMod (q + 1), ‖b q n‖ ^ 2
  let E : ℝ → ℝ := fun t =>
    ∑ q ∈ Q, ‖w q‖ ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 *
      ∑ d : ZMod (q + 1), ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg fun q _ =>
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hleft : Integrable
      (fun t => ‖kloostermanHybridModulusLinear Q w N a b t‖ ^ 2)
      (volume.restrict I) :=
    ((continuous_kloostermanHybridModulusLinear Q w N a b).norm.pow 2).integrableOn_Icc
  have hright : Integrable (fun t => B * E t) (volume.restrict I) := by
    apply Continuous.integrableOn_Icc
    apply continuous_const.mul
    dsimp only [E]
    apply continuous_finsetSum
    intro q _hq
    apply continuous_const.mul
    apply continuous_finsetSum
    intro d _hd
    exact (continuous_additiveHybridDirichletPoly q N (a q) d).norm.pow 2
  have hpoint : ∀ t : ℝ,
      ‖kloostermanHybridModulusLinear Q w N a b t‖ ^ 2 ≤ B * E t := by
    intro t
    have hbase := norm_kloostermanHybridModulusLinear_sq_le_baseline Q w N a b t
    simpa only [B, E, mul_comm] using hbase
  have hmono :
      (∫ t in I, ‖kloostermanHybridModulusLinear Q w N a b t‖ ^ 2) ≤
        ∫ t in I, B * E t :=
    MeasureTheory.integral_mono hleft hright hpoint
  have hEint :
      (∫ t in I, E t) =
        ∑ q ∈ Q, ‖w q‖ ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 *
          ∑ d : ZMod (q + 1),
            (∫ t in I, ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ 2) := by
    dsimp only [E]
    rw [MeasureTheory.integral_finsetSum Q]
    · apply Finset.sum_congr rfl
      intro q _hq
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finsetSum Finset.univ]
      intro d _hd
      exact (continuous_additiveHybridDirichletPoly q N (a q) d).norm.pow 2 |>.integrableOn_Icc
    · intro q _hq
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro d _hd
      exact (continuous_additiveHybridDirichletPoly q N (a q) d).norm.pow 2 |>.integrableOn_Icc
  calc
    (∫ t in I, ‖kloostermanHybridModulusLinear Q w N a b t‖ ^ 2) ≤
        ∫ t in I, B * E t := hmono
    _ = B * ∑ q ∈ Q, ‖w q‖ ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 *
          ∑ d : ZMod (q + 1),
            (∫ t in I, ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ 2) := by
      rw [MeasureTheory.integral_const_mul, hEint]
    _ ≤ B * ∑ q ∈ Q, ‖w q‖ ^ 2 * ((q + 1 : ℕ) : ℝ) ^ 2 *
          ((5 * Real.pi * Real.exp 1 * (N : ℝ) +
              5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
            ∑ m ∈ Finset.Icc 1 N, ‖a q m‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro q _hq
      apply mul_le_mul_of_nonneg_left
      · exact sum_integral_additiveHybridDirichletPoly_le_length q N (a q) hT
      · positivity
    _ = _ := by rfl

end

end RHTower.Sieve
