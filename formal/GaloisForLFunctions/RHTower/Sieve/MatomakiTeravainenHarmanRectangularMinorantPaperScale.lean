import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangularMinorant
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3PaperScale

/-!
# Paper-scale rectangularization error

The pair and triple bad-cell moments have maximal logarithmic degree fifteen.  The complete prime
source costs one further harmonic logarithm, so the literal width `(log X)^(-10A)` absorbs the
rectangularization error into `(log X)^(-2A)` for the paper range `A ≥ 5`.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- The two explicit rectangularization budgets fit inside the paper's squared-error saving. -/
theorem eventually_mtHarmanRectangularizationBudgets_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (Y D : ℕ) (P : Finset ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ D → (D : ℝ) ≤ X →
      (∀ q ∈ P, 1 ≤ q) → (∀ q ∈ P, q ≤ D) →
      2 * mtHarmanPairRectangularizationBudget A X Y P +
          2 * mtHarmanTripleRectangularizationBudget A X Y P ≤
        (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  have hαβ : (16 : ℝ) - ((10 * A : ℕ) : ℝ) < -((2 * A : ℕ) : ℝ) := by
    have hAR : (5 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    push_cast
    linarith
  have hkey := eventually_const_mul_rpow_polylog_le_rpow
    (C := (73856 : ℝ) * (5 : ℝ) ^ 15)
    (α := (16 : ℝ) - ((10 * A : ℕ) : ℝ))
    (β := -((2 * A : ℕ) : ℝ)) 0 hαβ
  have hkeyX := Real.tendsto_log_atTop.eventually hkey
  filter_upwards [hkeyX, Filter.eventually_ge_atTop (Real.exp 1)] with X hkeyX hX
  intro Y D P hY hYX hD hDX hPpos hPupper
  have hL1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hL : 0 < Real.log X := zero_lt_one.trans_le hL1
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (Nat.zero_lt_one.trans_le hY)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.zero_lt_one.trans_le hD)
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlogY : Real.log (Y : ℝ) ≤ Real.log 4 + Real.log X := by
    have hmono := Real.log_le_log hYpos hYX
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne'] at hmono
    exact hmono
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hYscale : 1 + Real.log (Y : ℝ) ≤ 5 * Real.log X := by linarith
  have hYbase0 : 0 ≤ 1 + Real.log (Y : ℝ) := by
    have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    linarith
  have hYbase1 : 1 ≤ 1 + Real.log (Y : ℝ) := by
    have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    linarith
  have hP : ∑ q ∈ P, 1 / (q : ℝ) ≤ 1 + Real.log D :=
    sum_inv_finset_le_one_add_log P D hPpos hPupper
  have hlogD : Real.log (D : ℝ) ≤ Real.log X := Real.log_le_log hDpos hDX
  have hDscale : 1 + Real.log (D : ℝ) ≤ 2 * Real.log X := by linarith
  have hP0 : 0 ≤ ∑ q ∈ P, 1 / (q : ℝ) := by
    apply Finset.sum_nonneg
    intro q hq
    positivity
  have hδ0 : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg hL.le _
  have hpair :
      2 * mtHarmanPairRectangularizationBudget A X Y P ≤
        2112 * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 15 *
          mtPaperWidth A X * ∑ q ∈ P, 1 / (q : ℝ) := by
    have heq : 2 * mtHarmanPairRectangularizationBudget A X Y P =
        2112 * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 3 *
          mtPaperWidth A X * ∑ q ∈ P, 1 / (q : ℝ) := by
      unfold mtHarmanPairRectangularizationBudget
      norm_num
      ring
    rw [heq]
    have hpow : (1 + Real.log (Y : ℝ)) ^ 3 ≤
        (1 + Real.log (Y : ℝ)) ^ 15 := by
      exact pow_le_pow_right₀ hYbase1 (by omega)
    gcongr
  have htriple :
      2 * mtHarmanTripleRectangularizationBudget A X Y P =
        34816 * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 15 *
          mtPaperWidth A X * ∑ q ∈ P, 1 / (q : ℝ) := by
    unfold mtHarmanTripleRectangularizationBudget
    norm_num
    ring
  have hbudget :
      2 * mtHarmanPairRectangularizationBudget A X Y P +
          2 * mtHarmanTripleRectangularizationBudget A X Y P ≤
        36928 * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 15 *
          mtPaperWidth A X * ∑ q ∈ P, 1 / (q : ℝ) := by
    rw [htriple]
    linarith
  have hPscale : ∑ q ∈ P, 1 / (q : ℝ) ≤ 2 * Real.log X :=
    hP.trans hDscale
  calc
    2 * mtHarmanPairRectangularizationBudget A X Y P +
        2 * mtHarmanTripleRectangularizationBudget A X Y P ≤
      36928 * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ 15 *
        mtPaperWidth A X * ∑ q ∈ P, 1 / (q : ℝ) := hbudget
    _ ≤ 36928 * (Y : ℝ) * (5 * Real.log X) ^ 15 *
        mtPaperWidth A X * (2 * Real.log X) := by gcongr
    _ = (Y : ℝ) * ((73856 : ℝ) * (5 : ℝ) ^ 15 *
        (Real.log X) ^ ((16 : ℝ) - ((10 * A : ℕ) : ℝ))) := by
      rw [mtPaperWidth]
      rw [show (5 * Real.log X) ^ 15 = (5 : ℝ) ^ 15 * (Real.log X) ^ 15 by ring]
      have hpow : (Real.log X) ^ 15 *
          (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) * Real.log X =
          (Real.log X) ^ ((16 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
        have hfirst : (Real.log X) ^ 15 *
            (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) =
            (Real.log X) ^ ((15 : ℝ) + (-((10 * A : ℕ) : ℝ))) := by
          simpa using (Real.rpow_add hL (15 : ℝ) (-((10 * A : ℕ) : ℝ))).symm
        have hsecond :
            (Real.log X) ^ ((15 : ℝ) + (-((10 * A : ℕ) : ℝ))) * Real.log X =
            (Real.log X) ^ (((15 : ℝ) + (-((10 * A : ℕ) : ℝ))) + 1) := by
          simpa using (Real.rpow_add hL
            ((15 : ℝ) + (-((10 * A : ℕ) : ℝ))) (1 : ℝ)).symm
        rw [hfirst, hsecond]
        congr 1
        push_cast
        ring
      rw [← hpow]
      ring
    _ ≤ (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
      gcongr
      simpa using hkeyX

/-- Final actual-source mean square for the literal bad-cell rectangularization error. -/
theorem eventually_sum_normSq_mtHarmanRectangularMinorantError_actualSource_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (z D Y E : ℕ),
      mtLowerCutoffNat X ≤ z → z ≤ D → (D : ℝ) ≤ X → 1 ≤ Y →
      (Y : ℝ) ≤ 4 * X →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X)
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanRectangularMinorantError
            (t := D - mtLowerCutoffNat X) endpoint z D E n‖ ^ 2 ≤
        (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_normSq_mtHarmanRectangularMinorantError_actualSource_le A,
    eventually_mtHarmanRectangularizationBudgets_le_log_rpow A hA,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hraw habsorb hX
  intro z D Y E hz hD hDX hY hYX
  have hDNat : 1 ≤ D := by
    have hz0 : 1 ≤ mtLowerCutoffNat X := by
      rw [mtLowerCutoffNat]
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    exact hz0.trans (hz.trans hD)
  have hraw' := hraw z D Y E hz hD hDX hY
  exact hraw'.trans (habsorb Y D (primesIco (mtLowerCutoffNat X) D)
    hY hYX hDNat hDX
    (fun q hq => (mem_primesIco.mp hq).2.2.pos)
    (fun q hq => (mem_primesIco.mp hq).2.1.le))

end

end RHTower.Sieve
