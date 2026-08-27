import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC2Coefficient
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3PaperScale

/-!
# Matomäki--Teräväinen `c₂,n` endpoint estimate at paper scale

Both endpoint spill families lie in one literal `(1+δ_A)`-width prime interval, with the first
allowed to begin at `z₀/(1+δ_A)`.  Their combined reciprocal mass is at most `4δ_A`.  The exact
bounded-coefficient error then has the source weighted first moment with final
`(log X)^(-3A)` saving.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Literal `d₃(n)|c₂,n|` mean before fixed-polylog absorption. -/
theorem eventually_sum_ternaryWeighted_norm_mtC2_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (level : ℕ → ℕ)
        (aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) level n‖ ≤
        B * ((2 : ℝ) ^ 3 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
            (4 * mtPaperWidth A X)) := by
  filter_upwards [eventually_sum_inv_primesIco_relaxedPaperCutoff A] with X hmassX
  intro α level aLower bLower aUpper bUpper Y B hY
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand hB hα
  have hLowerMass := hmassX hLowerCut hLowerOrder hLowerBand
  have hUpperMass := hmassX hUpperCut hUpperOrder hUpperBand
  have hmean := sum_ternaryDivisorCount_mul_norm_mtC2Coefficient_le
    α (primesIco aLower bLower) (primesIco aUpper bUpper) level Y hY
    (fun q hq => (mem_primesIco.mp hq).2.2)
    (fun q hq => (mem_primesIco.mp hq).2.2) hB hα
  have hfactor0 : 0 ≤ (2 : ℝ) ^ 3 * (Y : ℝ) *
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) := by
    have hlog : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    positivity
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtC2Coefficient α (primesIco aLower bLower)
            (primesIco aUpper bUpper) level n‖ ≤
      B * ((2 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          ((∑ q ∈ primesIco aLower bLower, 1 / (q : ℝ)) +
            ∑ q ∈ primesIco aUpper bUpper, 1 / (q : ℝ))) := hmean
    _ ≤ B * ((2 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (4 * mtPaperWidth A X)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply mul_le_mul_of_nonneg_left _ hfactor0
      linarith

/-- Exact source-scale `d₃(n)|c₂,n|` capstone with final `(log X)^(-3A)` saving. -/
theorem eventually_sum_ternaryWeighted_norm_mtC2_le_log_rpow (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (level : ℕ → ℕ)
        (aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) *
            ‖mtC2Coefficient α (primesIco aLower bLower)
              (primesIco aUpper bUpper) level n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_ternaryWeighted_norm_mtC2_paperWidth A,
    eventually_mtC3_polylog_absorption A hA,
    Filter.eventually_ge_atTop 1] with X hmeanX habsorbX hX
  intro α level aLower bLower aUpper bUpper Y B hY hYX
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand hB hα
  have hmean := hmeanX α level aLower bLower aUpper bUpper Y B hY
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand hB hα
  have hscalar := habsorbX Y 1 hY hYX (by omega : 1 ≤ (1 : ℕ)) (by exact_mod_cast hX)
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hwidth : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg (Real.log_nonneg hX) _
  have hcompare :
      (2 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (4 * mtPaperWidth A X) ≤
        (4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ)) := by
    norm_num [Real.log_one]
    have hbase : 0 ≤ 1 + Real.log (Y : ℝ) := by linarith
    have hpoly : 0 ≤ (1 + Real.log (Y : ℝ)) ^ 7 := pow_nonneg hbase _
    nlinarith [mul_nonneg hpoly hwidth]
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) *
          ‖mtC2Coefficient α (primesIco aLower bLower)
            (primesIco aUpper bUpper) level n‖ ≤
      B * ((2 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (4 * mtPaperWidth A X)) := hmean
    _ ≤ B * (Y : ℝ) *
        ((4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ))) := by
      have hBY : 0 ≤ B * (Y : ℝ) := mul_nonneg hB (Nat.cast_nonneg _)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hcompare hBY)
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (show
        (4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ)) ≤
            (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) by
          simpa only [Nat.cast_one] using hscalar)
        (mul_nonneg hB (Nat.cast_nonneg _))

end

end RHTower.Sieve
