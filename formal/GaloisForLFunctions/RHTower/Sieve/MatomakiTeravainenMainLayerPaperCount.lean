import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerChains

/-!
# Paper-scale count for Matomäki--Teräväinen main pieces

The source counts every recursion depth together with every surviving block chain.  This file keeps
that exact depth-indexed sum.  For the repaired aligned schedule its cardinality is eventually at
most `exp ((log log X)^(5 : ℕ))`, matching Proposition 2.2's stated family budget.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- Exact count of all active block chains through a prescribed terminal depth. -/
theorem sum_card_mtActiveBlockChains_le {t : ℕ}
    (block : Fin t → Finset ℕ) (maxDepth : ℕ) (j : Fin (t + 1)) :
    ∑ depth ∈ Finset.range (maxDepth + 1),
        (mtActiveBlockChains block depth j).card ≤
      (maxDepth + 1) * ((mtActiveBlockIndices block).card + 1) ^ maxDepth := by
  calc
    _ ≤ ∑ _depth ∈ Finset.range (maxDepth + 1),
        ((mtActiveBlockIndices block).card + 1) ^ maxDepth := by
      apply Finset.sum_le_sum
      intro depth hdepth
      have hdepthMax : depth ≤ maxDepth := Nat.le_of_lt_succ (Finset.mem_range.mp hdepth)
      calc
        (mtActiveBlockChains block depth j).card ≤
            (mtActiveBlockIndices block).card ^ depth :=
          card_mtActiveBlockChains_le_pow block depth j
        _ ≤ ((mtActiveBlockIndices block).card + 1) ^ depth :=
          Nat.pow_le_pow_left (Nat.le_add_right _ _) depth
        _ ≤ ((mtActiveBlockIndices block).card + 1) ^ maxDepth :=
          Nat.pow_le_pow_right (by omega) hdepthMax
    _ = (maxDepth + 1) * ((mtActiveBlockIndices block).card + 1) ^ maxDepth := by
      simp [Finset.sum_const]

/-- One more active-block slot is eventually below a quarter-square exponential in `log log X`. -/
theorem eventually_cast_card_mtPaperAlignedActiveBlockIndices_add_one_le_exp_quarter_sq
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ z₁ : ℕ,
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      (((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
        (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card + 1 : ℕ) : ℝ) ≤
          Real.exp ((Real.log (Real.log X)) ^ (2 : ℕ) / 4) := by
  have hlarge := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (4 * (((10 * A + 2 : ℕ) : ℝ)) + 6)
  filter_upwards [eventually_cast_card_mtPaperAlignedActiveBlockIndices_le_six_mul_log_pow A,
    hlarge, Filter.eventually_ge_atTop (Real.exp 1)] with X hcard hll hX
  intro z₁ hz hzX
  change 4 * (((10 * A + 2 : ℕ) : ℝ)) + 6 ≤ Real.log (Real.log X) at hll
  let u := Real.log (Real.log X)
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hlogXOne : (1 : ℝ) ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hlogX : 0 < Real.log X := by
    exact zero_lt_one.trans_le hlogXOne
  have hlogXEq : Real.log X = Real.exp u := by
    dsimp [u]
    exact (Real.exp_log hlogX).symm
  have hlogXSeven : (7 : ℝ) ≤ Real.log X := by
    rw [hlogXEq]
    calc
      (7 : ℝ) ≤ u + 1 := by
        dsimp [u] at hll ⊢
        linarith
      _ ≤ Real.exp u := Real.add_one_le_exp u
  have hexponent : ((10 * A + 2 : ℕ) : ℝ) * u ≤ u ^ (2 : ℕ) / 4 := by
    have huLower : 4 * (((10 * A + 2 : ℕ) : ℝ)) ≤ u := by
      dsimp [u] at hll ⊢
      linarith
    have := mul_le_mul_of_nonneg_right huLower hu
    nlinarith
  have hactive := hcard z₁ hz hzX
  calc
    (((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
        (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card + 1 : ℕ) : ℝ) =
        ((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
          (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card : ℝ) + 1 := by push_cast; ring
    _ ≤ 6 * (Real.log X) ^ (10 * A + 1) + 1 := by gcongr
    _ ≤ 7 * (Real.log X) ^ (10 * A + 1) := by
      have : (1 : ℝ) ≤ (Real.log X) ^ (10 * A + 1) := one_le_pow₀ hlogXOne
      nlinarith
    _ ≤ (Real.log X) ^ (10 * A + 2) := by
      have hpowNonneg : 0 ≤ (Real.log X) ^ (10 * A + 1) := pow_nonneg hlogX.le _
      calc
        7 * (Real.log X) ^ (10 * A + 1) ≤
            Real.log X * (Real.log X) ^ (10 * A + 1) :=
          mul_le_mul_of_nonneg_right hlogXSeven hpowNonneg
        _ = (Real.log X) ^ (10 * A + 2) := by rw [pow_succ]; ring
    _ = Real.exp (((10 * A + 2 : ℕ) : ℝ) * u) := by
      rw [hlogXEq, Real.exp_nat_mul]
    _ ≤ Real.exp (u ^ (2 : ℕ) / 4) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp ((Real.log (Real.log X)) ^ (2 : ℕ) / 4) := rfl

/-- Abstract conversion from cubic depth and quarter-square block growth to the source fifth-power
exponential budget. -/
theorem cast_sum_card_mtActiveBlockChains_le_exp_fifth_of_bounds
    {t maxDepth : ℕ} (block : Fin t → Finset ℕ) (j : Fin (t + 1))
    {u : ℝ} (hu : 2 ≤ u)
    (hdepth : (maxDepth : ℝ) ≤ 2 * u ^ (3 : ℕ))
    (hblock : (((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ≤
      Real.exp (u ^ (2 : ℕ) / 4)) :
    ((∑ depth ∈ Finset.range (maxDepth + 1),
        (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
      Real.exp (u ^ (5 : ℕ)) := by
  have hsumNat := sum_card_mtActiveBlockChains_le block maxDepth j
  have hsumReal :
      ((∑ depth ∈ Finset.range (maxDepth + 1),
          (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
        ((maxDepth : ℝ) + 1) *
          ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) := by
    exact_mod_cast hsumNat
  have hu0 : 0 ≤ u := by linarith
  have huCube0 : 0 ≤ u ^ (3 : ℕ) := pow_nonneg hu0 3
  have huFifth0 : 0 ≤ u ^ (5 : ℕ) := pow_nonneg hu0 5
  have harg : (maxDepth : ℝ) * (u ^ (2 : ℕ) / 4) ≤ u ^ (5 : ℕ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hdepth
      (div_nonneg (sq_nonneg u) (by norm_num : (0 : ℝ) ≤ 4))
    calc
      (maxDepth : ℝ) * (u ^ (2 : ℕ) / 4) ≤ (2 * u ^ (3 : ℕ)) * (u ^ (2 : ℕ) / 4) := hmul
      _ = u ^ (5 : ℕ) / 2 := by ring
  have hpow :
      ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) ≤
        Real.exp (u ^ (5 : ℕ) / 2) := by
    calc
      ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) ≤
          (Real.exp (u ^ (2 : ℕ) / 4)) ^ maxDepth :=
        pow_le_pow_left₀ (by positivity) hblock maxDepth
      _ = Real.exp ((maxDepth : ℝ) * (u ^ (2 : ℕ) / 4)) :=
        (Real.exp_nat_mul (u ^ (2 : ℕ) / 4) maxDepth).symm
      _ ≤ Real.exp (u ^ (5 : ℕ) / 2) := Real.exp_le_exp.mpr harg
  have hcubic : 2 * u ^ (3 : ℕ) ≤ u ^ (5 : ℕ) / 2 := by
    have huSq : (4 : ℝ) ≤ u ^ (2 : ℕ) := by nlinarith [sq_nonneg (u - 2)]
    have hmul := mul_le_mul_of_nonneg_right huSq huCube0
    nlinarith
  have hfactor : (maxDepth : ℝ) + 1 ≤ Real.exp (u ^ (5 : ℕ) / 2) := by
    calc
      (maxDepth : ℝ) + 1 ≤ u ^ (5 : ℕ) / 2 + 1 := by linarith
      _ ≤ Real.exp (u ^ (5 : ℕ) / 2) := Real.add_one_le_exp _
  calc
    ((∑ depth ∈ Finset.range (maxDepth + 1),
        (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
        ((maxDepth : ℝ) + 1) *
          ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) := hsumReal
    _ ≤ Real.exp (u ^ (5 : ℕ) / 2) *
        ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) :=
      mul_le_mul_of_nonneg_right hfactor (pow_nonneg (by positivity) _)
    _ ≤ Real.exp (u ^ (5 : ℕ) / 2) * Real.exp (u ^ (5 : ℕ) / 2) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (u ^ (5 : ℕ)) := by rw [← Real.exp_add]; congr 1; ring

/-- Proposition 2.2's exact depth-and-chain family count for the repaired aligned iteration. -/
theorem eventually_sum_card_mtActiveBlockChains_paperAligned_le_exp_log_log_fifth
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y z₁ : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ∀ j : Fin (z₁ - mtLowerCutoffNat X + 1),
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains
              (mtAdjacentPrimeBlock
                (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
              depth j).card : ℕ) : ℝ) ≤
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := by
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2
  filter_upwards [eventually_mtLogDepth_le_two_mul_log_log_cube,
    eventually_cast_card_mtPaperAlignedActiveBlockIndices_add_one_le_exp_quarter_sq A,
    hll] with X hdepth hblock hllX
  intro Y z₁ hY hYX hz hzX j
  apply cast_sum_card_mtActiveBlockChains_le_exp_fifth_of_bounds
      (block := mtAdjacentPrimeBlock
        (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
      (j := j) (u := Real.log (Real.log X)) hllX
  · exact hdepth Y hY hYX
  · rw [mtActiveBlockIndices_paperAligned]
    exact hblock z₁ hz hzX

/-- Stronger block envelope reserving half of Proposition 2.2's fifth-power exponent for the
outer `q₁,q₂,e,k` partitions. -/
theorem eventually_cast_card_mtPaperAlignedActiveBlockIndices_add_one_le_exp_eighth_sq
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ z₁ : ℕ,
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      (((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
        (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card + 1 : ℕ) : ℝ) ≤
          Real.exp ((Real.log (Real.log X)) ^ (2 : ℕ) / 8) := by
  have hlarge := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (8 * (((10 * A + 2 : ℕ) : ℝ)) + 6)
  filter_upwards [eventually_cast_card_mtPaperAlignedActiveBlockIndices_le_six_mul_log_pow A,
    hlarge, Filter.eventually_ge_atTop (Real.exp 1)] with X hcard hll hX
  intro z₁ hz hzX
  change 8 * (((10 * A + 2 : ℕ) : ℝ)) + 6 ≤ Real.log (Real.log X) at hll
  let u := Real.log (Real.log X)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hlogXOne : (1 : ℝ) ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hlogX : 0 < Real.log X := zero_lt_one.trans_le hlogXOne
  have hlogXEq : Real.log X = Real.exp u := by
    dsimp [u]
    exact (Real.exp_log hlogX).symm
  have hlogXSeven : (7 : ℝ) ≤ Real.log X := by
    rw [hlogXEq]
    calc
      (7 : ℝ) ≤ u + 1 := by dsimp [u] at hll ⊢; linarith
      _ ≤ Real.exp u := Real.add_one_le_exp u
  have hexponent : ((10 * A + 2 : ℕ) : ℝ) * u ≤ u ^ (2 : ℕ) / 8 := by
    have huLower : 8 * (((10 * A + 2 : ℕ) : ℝ)) ≤ u := by
      dsimp [u] at hll ⊢
      linarith
    have := mul_le_mul_of_nonneg_right huLower hu
    nlinarith
  have hactive := hcard z₁ hz hzX
  calc
    (((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
        (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card + 1 : ℕ) : ℝ) =
        ((mtPaperAlignedActiveBlockIndices (z₁ - mtLowerCutoffNat X)
          (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)).card : ℝ) + 1 := by push_cast; ring
    _ ≤ 6 * (Real.log X) ^ (10 * A + 1) + 1 := by gcongr
    _ ≤ 7 * (Real.log X) ^ (10 * A + 1) := by
      have : (1 : ℝ) ≤ (Real.log X) ^ (10 * A + 1) := one_le_pow₀ hlogXOne
      nlinarith
    _ ≤ (Real.log X) ^ (10 * A + 2) := by
      have hpowNonneg : 0 ≤ (Real.log X) ^ (10 * A + 1) := pow_nonneg hlogX.le _
      calc
        7 * (Real.log X) ^ (10 * A + 1) ≤
            Real.log X * (Real.log X) ^ (10 * A + 1) :=
          mul_le_mul_of_nonneg_right hlogXSeven hpowNonneg
        _ = (Real.log X) ^ (10 * A + 2) := by rw [pow_succ]; ring
    _ = Real.exp (((10 * A + 2 : ℕ) : ℝ) * u) := by
      rw [hlogXEq, Real.exp_nat_mul]
    _ ≤ Real.exp (u ^ (2 : ℕ) / 8) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp ((Real.log (Real.log X)) ^ (2 : ℕ) / 8) := rfl

/-- Cubic depth plus the eighth-square block envelope costs only half the fifth-power budget. -/
theorem cast_sum_card_mtActiveBlockChains_le_exp_half_fifth_of_bounds
    {t maxDepth : ℕ} (block : Fin t → Finset ℕ) (j : Fin (t + 1))
    {u : ℝ} (hu : 3 ≤ u)
    (hdepth : (maxDepth : ℝ) ≤ 2 * u ^ (3 : ℕ))
    (hblock : (((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ≤
      Real.exp (u ^ (2 : ℕ) / 8)) :
    ((∑ depth ∈ Finset.range (maxDepth + 1),
        (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
      Real.exp (u ^ (5 : ℕ) / 2) := by
  have hsumNat := sum_card_mtActiveBlockChains_le block maxDepth j
  have hsumReal :
      ((∑ depth ∈ Finset.range (maxDepth + 1),
          (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
        ((maxDepth : ℝ) + 1) *
          ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) := by
    exact_mod_cast hsumNat
  have hu0 : 0 ≤ u := by linarith
  have huCube0 : 0 ≤ u ^ (3 : ℕ) := pow_nonneg hu0 3
  have harg : (maxDepth : ℝ) * (u ^ (2 : ℕ) / 8) ≤ u ^ (5 : ℕ) / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hdepth
      (div_nonneg (sq_nonneg u) (by norm_num : (0 : ℝ) ≤ 8))
    calc
      (maxDepth : ℝ) * (u ^ (2 : ℕ) / 8) ≤ (2 * u ^ (3 : ℕ)) * (u ^ (2 : ℕ) / 8) := hmul
      _ = u ^ (5 : ℕ) / 4 := by ring
  have hpow :
      ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) ≤
        Real.exp (u ^ (5 : ℕ) / 4) := by
    calc
      ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) ≤
          (Real.exp (u ^ (2 : ℕ) / 8)) ^ maxDepth :=
        pow_le_pow_left₀ (by positivity) hblock maxDepth
      _ = Real.exp ((maxDepth : ℝ) * (u ^ (2 : ℕ) / 8)) :=
        (Real.exp_nat_mul (u ^ (2 : ℕ) / 8) maxDepth).symm
      _ ≤ Real.exp (u ^ (5 : ℕ) / 4) := Real.exp_le_exp.mpr harg
  have hcubic : 2 * u ^ (3 : ℕ) ≤ u ^ (5 : ℕ) / 4 := by
    have huSq : (8 : ℝ) ≤ u ^ (2 : ℕ) := by nlinarith [sq_nonneg (u - 3)]
    have hmul := mul_le_mul_of_nonneg_right huSq huCube0
    nlinarith
  have hfactor : (maxDepth : ℝ) + 1 ≤ Real.exp (u ^ (5 : ℕ) / 4) := by
    calc
      (maxDepth : ℝ) + 1 ≤ u ^ (5 : ℕ) / 4 + 1 := by linarith
      _ ≤ Real.exp (u ^ (5 : ℕ) / 4) := Real.add_one_le_exp _
  calc
    ((∑ depth ∈ Finset.range (maxDepth + 1),
        (mtActiveBlockChains block depth j).card : ℕ) : ℝ) ≤
        ((maxDepth : ℝ) + 1) *
          ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) := hsumReal
    _ ≤ Real.exp (u ^ (5 : ℕ) / 4) *
        ((((mtActiveBlockIndices block).card + 1 : ℕ) : ℝ) ^ maxDepth) :=
      mul_le_mul_of_nonneg_right hfactor (pow_nonneg (by positivity) _)
    _ ≤ Real.exp (u ^ (5 : ℕ) / 4) * Real.exp (u ^ (5 : ℕ) / 4) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (u ^ (5 : ℕ) / 2) := by rw [← Real.exp_add]; congr 1; ring

/-- Repaired main-chain family uses only half of Proposition 2.2's stated exponent. -/
theorem eventually_sum_card_mtActiveBlockChains_paperAligned_le_exp_half_log_log_fifth
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y z₁ : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ∀ j : Fin (z₁ - mtLowerCutoffNat X + 1),
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains
              (mtAdjacentPrimeBlock
                (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
              depth j).card : ℕ) : ℝ) ≤
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := by
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  filter_upwards [eventually_mtLogDepth_le_two_mul_log_log_cube,
    eventually_cast_card_mtPaperAlignedActiveBlockIndices_add_one_le_exp_eighth_sq A,
    hll] with X hdepth hblock hllX
  intro Y z₁ hY hYX hz hzX j
  apply cast_sum_card_mtActiveBlockChains_le_exp_half_fifth_of_bounds
      (block := mtAdjacentPrimeBlock
        (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
      (j := j) (u := Real.log (Real.log X)) hllX
  · exact hdepth Y hY hYX
  · rw [mtActiveBlockIndices_paperAligned]
    exact hblock z₁ hz hzX

/-- Every fixed outer polylogarithmic partition fits inside the half-budget reserved above. -/
theorem eventually_const_mul_log_pow_le_exp_half_log_log_fifth
    (C : ℝ) (K : ℕ) (_hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in Filter.atTop,
      C * (Real.log X) ^ K ≤
        Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := by
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (2 * (K + 1) + 2 : ℝ)
  have hlogC := Real.tendsto_log_atTop.eventually_ge_atTop (max C 1)
  filter_upwards [hll, hlogC] with X hllX hlogX
  change (2 * (K + 1) + 2 : ℝ) ≤ Real.log (Real.log X) at hllX
  have hlogOne : (1 : ℝ) ≤ Real.log X := (le_max_right C 1).trans hlogX
  have hlogC' : C ≤ Real.log X := (le_max_left C 1).trans hlogX
  let u := Real.log (Real.log X)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  have hlogEq : Real.log X = Real.exp u := by
    dsimp [u]
    exact (Real.exp_log hlogPos).symm
  have hexponent : (((K + 1 : ℕ) : ℝ)) * u ≤ u ^ (5 : ℕ) / 2 := by
    have huLower : 2 * (((K + 1 : ℕ) : ℝ)) ≤ u := by
      dsimp [u] at hllX ⊢
      push_cast at hllX ⊢
      linarith
    have huOne : (1 : ℝ) ≤ u := by
      dsimp [u] at hllX ⊢
      linarith
    have hu4 : u ≤ u ^ (4 : ℕ) := by
      have hu3 : (1 : ℝ) ≤ u ^ (3 : ℕ) := one_le_pow₀ huOne
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right huLower hu
    nlinarith
  calc
    C * (Real.log X) ^ K ≤ Real.log X * (Real.log X) ^ K :=
      mul_le_mul_of_nonneg_right hlogC' (pow_nonneg hlogPos.le _)
    _ = (Real.log X) ^ (K + 1) := by rw [pow_succ]; ring
    _ = Real.exp ((((K + 1 : ℕ) : ℝ)) * u) := by
      rw [hlogEq, Real.exp_nat_mul]
    _ ≤ Real.exp (u ^ (5 : ℕ) / 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := rfl

/-- Main-chain count times any fixed outer polylogarithmic partition has Proposition 2.2's exact
`exp((log log X)^(5 : ℕ))` budget. -/
theorem eventually_outer_mul_sum_card_mtActiveBlockChains_paperAligned_le_exp_log_log_fifth
    (A K : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y z₁ : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ∀ j : Fin (z₁ - mtLowerCutoffNat X + 1),
        C * (Real.log X) ^ K *
          ((∑ depth ∈ Finset.range
              (Nat.floor (Real.log (Y : ℝ) /
                Real.log (mtLowerCutoffNat X : ℝ)) + 1),
              (mtActiveBlockChains
                (mtAdjacentPrimeBlock
                  (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                depth j).card : ℕ) : ℝ) ≤
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := by
  filter_upwards [eventually_const_mul_log_pow_le_exp_half_log_log_fifth C K hC,
    eventually_sum_card_mtActiveBlockChains_paperAligned_le_exp_half_log_log_fifth A]
    with X houter hchains
  intro Y z₁ hY hYX hz hzX j
  calc
    C * (Real.log X) ^ K *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains
              (mtAdjacentPrimeBlock
                (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
              depth j).card : ℕ) : ℝ) ≤
        Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) *
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := by
      calc
        C * (Real.log X) ^ K *
            ((∑ depth ∈ Finset.range
                (Nat.floor (Real.log (Y : ℝ) /
                  Real.log (mtLowerCutoffNat X : ℝ)) + 1),
                (mtActiveBlockChains
                  (mtAdjacentPrimeBlock
                    (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                  depth j).card : ℕ) : ℝ) ≤
            Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) *
              ((∑ depth ∈ Finset.range
                  (Nat.floor (Real.log (Y : ℝ) /
                    Real.log (mtLowerCutoffNat X : ℝ)) + 1),
                  (mtActiveBlockChains
                    (mtAdjacentPrimeBlock
                      (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                    depth j).card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right houter (by positivity)
        _ ≤ Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) *
            Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) :=
          mul_le_mul_of_nonneg_left (hchains Y z₁ hY hYX hz hzX j) (Real.exp_pos _).le
    _ = Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Exact count budget for `r` independent outer paper-width grid choices times every repaired
main-layer chain. -/
theorem eventually_grid_pow_mul_sum_card_mtActiveBlockChains_paperAligned_le_exp_log_log_fifth
    (A r : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ Y z₁ : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X →
      ∀ j : Fin (z₁ - mtLowerCutoffNat X + 1),
        (((adicIndex (mtPaperWidth A X) 1 X + 1) ^ r : ℕ) : ℝ) *
          ((∑ depth ∈ Finset.range
              (Nat.floor (Real.log (Y : ℝ) /
                Real.log (mtLowerCutoffNat X : ℝ)) + 1),
              (mtActiveBlockChains
                (mtAdjacentPrimeBlock
                  (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                depth j).card : ℕ) : ℝ) ≤
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := by
  filter_upwards [eventually_cast_adicIndex_paperWidth_one_add_one_pow_le_log_pow A r,
    eventually_outer_mul_sum_card_mtActiveBlockChains_paperAligned_le_exp_log_log_fifth
      A (r * (10 * A + 1)) ((3 : ℝ) ^ r) (by positivity)]
    with X hgrid htotal
  intro Y z₁ hY hYX hz hzX j
  calc
    (((adicIndex (mtPaperWidth A X) 1 X + 1) ^ r : ℕ) : ℝ) *
        ((∑ depth ∈ Finset.range
            (Nat.floor (Real.log (Y : ℝ) /
              Real.log (mtLowerCutoffNat X : ℝ)) + 1),
            (mtActiveBlockChains
              (mtAdjacentPrimeBlock
                (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
              depth j).card : ℕ) : ℝ) ≤
        (3 : ℝ) ^ r * (Real.log X) ^ (r * (10 * A + 1)) *
          ((∑ depth ∈ Finset.range
              (Nat.floor (Real.log (Y : ℝ) /
                Real.log (mtLowerCutoffNat X : ℝ)) + 1),
              (mtActiveBlockChains
                (mtAdjacentPrimeBlock
                  (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)))
                depth j).card : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hgrid (by positivity)
    _ ≤ Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := htotal Y z₁ hY hYX hz hzX j

end

end RHTower.Sieve
