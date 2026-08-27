import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC3Coefficient
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRelaxedPaperScale
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Matomäki--Teräväinen `c₃,n` estimate at the literal paper scale

This file discharges the remaining analytic factors in the source's `c₃,n` estimate.  Lower-prime
fibres cost `2δ_A`, outer primes cost one harmonic factor, and the fixed divisor loss costs seven
logarithmic powers.  Since `δ_A = (log X)^(-10A)`, all factors are absorbed into the source target
`(log X)^(-3A)` for `A ≥ 2` (hence for the paper's `A ≥ 5`).
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Literal `d₃(n)|c₃,n|` mean at paper width, before outer-mass absorption. -/
theorem eventually_sum_ternaryWeighted_norm_mtC3_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) (Y : ℕ) (B : ℝ),
      1 ≤ Y →
      (∀ q ∈ S, q.Prime) →
      (∀ q ∈ S,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ S, lower q ≤ q) →
      (∀ q ∈ S, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
        B * ((4 : ℝ) ^ 3 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
            (2 * mtPaperWidth A X) * ∑ q ∈ S, 1 / (q : ℝ)) := by
  filter_upwards [eventually_lowerC3FibreMass_paperWidth A] with X hmassX
  intro α S lower Y B hY hprime hlowerCut hlower hband hB hα
  exact sum_ternaryDivisorCount_mul_norm_mtC3Coefficient_le
    α S lower Y hY hprime hlower hB hα (hmassX S lower hlowerCut hlower hband)

/-- Reciprocal mass of any finite positive family below `N` is at most `1 + log N`. -/
theorem sum_inv_finset_le_one_add_log
    (S : Finset ℕ) (N : ℕ) (hpos : ∀ q ∈ S, 1 ≤ q) (hupper : ∀ q ∈ S, q ≤ N) :
    ∑ q ∈ S, 1 / (q : ℝ) ≤ 1 + Real.log N := by
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨hpos q hq, hupper q hq⟩
  calc
    ∑ q ∈ S, 1 / (q : ℝ) ≤ ∑ q ∈ Finset.Icc 1 N, 1 / (q : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hqS hq => by
        rw [Finset.mem_Icc] at hqS
        positivity)
    _ ≤ 1 + Real.log N := sum_Icc_one_div_le_one_add_log N

/-- The fixed `c₃,n` polylogarithm and outer harmonic mass are absorbed by `δ_A`. -/
theorem eventually_mtC3_polylog_absorption (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (Y N : ℕ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (N : ℝ)) ≤
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  have hαβ : (8 : ℝ) - ((10 * A : ℕ) : ℝ) < -((3 * A : ℕ) : ℝ) := by
    have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    push_cast
    linarith
  have hkey := eventually_const_mul_rpow_polylog_le_rpow
    (C := (4 : ℝ) ^ 4 * (5 : ℝ) ^ 7) (α := (8 : ℝ) - ((10 * A : ℕ) : ℝ))
      (β := -((3 * A : ℕ) : ℝ)) 0 hαβ
  have hkeyX := Real.tendsto_log_atTop.eventually hkey
  filter_upwards [hkeyX, Filter.eventually_ge_atTop (Real.exp 1)] with X hkeyX hX
  intro Y N hY hYX hN hNX
  have hL1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hL : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
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
  have hNlog : Real.log (N : ℝ) ≤ Real.log X := Real.log_le_log hNpos hNX
  have hNscale : 1 + Real.log (N : ℝ) ≤ 2 * Real.log X := by linarith
  have hδ0 : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg hL.le _
  have hrough :
      (4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (N : ℝ)) ≤
        (4 : ℝ) ^ 3 * (5 * Real.log X) ^ 7 *
          (2 * mtPaperWidth A X) * (2 * Real.log X) := by
    norm_num
    gcongr
  calc
    (4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
        (2 * mtPaperWidth A X) * (1 + Real.log (N : ℝ)) ≤
      (4 : ℝ) ^ 3 * (5 * Real.log X) ^ 7 *
        (2 * mtPaperWidth A X) * (2 * Real.log X) := hrough
    _ = ((4 : ℝ) ^ 4 * (5 : ℝ) ^ 7) *
        (Real.log X) ^ ((8 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
      rw [mtPaperWidth]
      rw [show (5 * Real.log X) ^ 7 = (5 : ℝ) ^ 7 * (Real.log X) ^ 7 by ring]
      have hpow : (Real.log X) ^ 7 *
          (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) * Real.log X =
          (Real.log X) ^ ((8 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
        have hfirst : (Real.log X) ^ 7 *
            (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) =
            (Real.log X) ^ ((7 : ℝ) + (-((10 * A : ℕ) : ℝ))) := by
          simpa using (Real.rpow_add hL (7 : ℝ) (-((10 * A : ℕ) : ℝ))).symm
        have hsecond : (Real.log X) ^ ((7 : ℝ) + (-((10 * A : ℕ) : ℝ))) *
            Real.log X =
            (Real.log X) ^ (((7 : ℝ) + (-((10 * A : ℕ) : ℝ))) + 1) := by
          simpa using (Real.rpow_add hL
            ((7 : ℝ) + (-((10 * A : ℕ) : ℝ))) (1 : ℝ)).symm
        calc
          (Real.log X) ^ 7 * (Real.log X) ^ (-((10 * A : ℕ) : ℝ)) * Real.log X =
            (Real.log X) ^ ((7 : ℝ) + (-((10 * A : ℕ) : ℝ))) *
              Real.log X := congrArg (fun x => x * Real.log X) hfirst
          _ = (Real.log X) ^
              (((7 : ℝ) + (-((10 * A : ℕ) : ℝ))) + 1) := hsecond
          _ = (Real.log X) ^ ((8 : ℝ) - ((10 * A : ℕ) : ℝ)) := by
            congr 1
            push_cast
            ring
      rw [← hpow]
      ring
    _ ≤ (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      simpa using hkeyX

/-- Exact source-scale `d₃(n)|c₃,n|` capstone with final `(log X)^(-3A)` saving. -/
theorem eventually_sum_ternaryWeighted_norm_mtC3_le_log_rpow (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) (Y N : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (∀ q ∈ S, q.Prime) → (∀ q ∈ S, q ≤ N) →
      (∀ q ∈ S,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ S, lower q ≤ q) →
      (∀ q ∈ S, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → (∀ m, ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_ternaryWeighted_norm_mtC3_paperWidth A,
    eventually_mtC3_polylog_absorption A hA] with X hmeanX habsorbX
  intro α S lower Y N B hY hYX hN hNX hprime hupper hlowerCut hlower hband hB hα
  have hmean := hmeanX α S lower Y B hY hprime hlowerCut hlower hband hB hα
  have houter : ∑ q ∈ S, 1 / (q : ℝ) ≤ 1 + Real.log N :=
    sum_inv_finset_le_one_add_log S N (fun q hq => (hprime q hq).pos) hupper
  have hscalar := habsorbX Y N hY hYX hN hNX
  have hfactor0 : 0 ≤ (4 : ℝ) ^ 3 * (Y : ℝ) *
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) * (2 * mtPaperWidth A X) := by
    have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
    have hwidth : 0 ≤ mtPaperWidth A X := by
      rw [mtPaperWidth]
      have hX1 : (1 : ℝ) ≤ X := (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)).trans hNX
      exact Real.rpow_nonneg (Real.log_nonneg hX1) _
    positivity
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        (ternaryDivisorCount n : ℝ) * ‖mtC3Coefficient α S lower n‖ ≤
      B * ((4 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * ∑ q ∈ S, 1 / (q : ℝ)) := hmean
    _ ≤ B * ((4 : ℝ) ^ 3 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left houter hfactor0) hB
    _ = B * (Y : ℝ) *
        ((4 : ℝ) ^ 3 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 3 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) := by ring
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hscalar (mul_nonneg hB (Nat.cast_nonneg Y))

end

end RHTower.Sieve
