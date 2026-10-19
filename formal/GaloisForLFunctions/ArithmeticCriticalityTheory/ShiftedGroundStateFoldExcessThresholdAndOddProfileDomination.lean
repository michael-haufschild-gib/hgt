import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOddProfileCoordinates

/-!
# Dual-Threshold Fold-Excess Annihilation and Odd-Profile Monotone Domination

In `ShiftedGroundStateOriginFailure`, the shifted ground state `ω_a` fails the raw folded
supersolution inequality `C_a(x) ≤ sinh(a/2) sinh(x/2)` near `x = 0` for every `a > 0`
because the prime `n = 2` contribution to the raw collar mass `C_a(x)` remains strictly
positive as `x → 0⁺`.

In `ShiftedGroundStateMonotoneFoldDomination`, restricting to even profiles `u` that are
nonnegative and nonincreasing on `[0, ∞)` replaces `C_a(x)` by the fold-excess weight
`W_a(x) = foldExcessWeight a x` against the source `2 sinh(a/2) sinh(x/2)`.

This module establishes three structural results for `W_a(x)` and its odd-profile form:

1. **Dual-Threshold Shift & Prime-Power Annihilation (`foldExcessDensity_eq_zero_of_le_max`,
   `foldExcessDensity_eq_zero_of_le_two_thirds`):**
   Combining the half-collar cutoff (`t ≤ 2x`) with the monotonicity window (`x + t ≤ a`)
   shows that `foldExcessDensity a t x = 0` whenever `t ≤ max (2 * x) (a - x)`.
   Since `(1/3)(2x) + (2/3)(a - x) = (2/3)a`, every `x ∈ ℝ` satisfies
   `(2 / 3) * a ≤ max (2 * x) (a - x)`. Consequently, **every** jump `t ≤ (2 / 3) * a` —
   and every prime-power atom `n` with `log n ≤ (2 / 3) * a` — is identically annihilated
   from `foldExcessWeight a x` across the entire half-line `x ≥ 0`. In particular, for
   `a ≥ (3 / 2) * log 2`, the prime `n = 2` (which caused the origin failure of `C_a(x)`)
   contributes zero to `W_a(x)` for all `x ≥ 0`.

2. **Support-Localized Weight Criterion
   (`markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_support_weight_le`):**
   The pointwise domination `W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` only needs to hold on the
   active support `{x > 0 | u x ≠ 0}` of the monotone profile `u`.

3. **Odd-Profile Monotone Fold Domination (`markovEnergy_oddProfileTest_ge_of_antitone`,
   `markovEnergy_oddProfileTest_nonneg_of_antitone_of_support_weight_le`):**
   Transfers the monotone fold-excess lower bound and support-localized positivity criterion
   into the odd-profile test coordinates `oddProfileTest a w`.
-/

open MeasureTheory Set Filter Topology Complex
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ## 1. Dual-Threshold Shift & Prime-Power Annihilation in `foldExcessDensity` -/

/-- Convex-combination lower bound: for every `a, x ∈ ℝ`, the dual threshold
`max (2 * x) (a - x)` is at least `(2 / 3) * a` (achieved at `x = a / 3`). -/
theorem two_thirds_mul_le_max_two_mul_sub (a x : ℝ) :
    2 / 3 * a ≤ max (2 * x) (a - x) := by
  rcases le_total (2 * x) (a - x) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

/-- **Dual-Threshold Vanishing Law:** For `x ≥ 0`, the fold-excess density vanishes
whenever `t ≤ max (2 * x) (a - x)`, uniting the half-collar cutoff `t ≤ 2 * x` and the
peak-monotonicity window `x + t ≤ a`. -/
theorem foldExcessDensity_eq_zero_of_le_max {a t x : ℝ} (hx : 0 ≤ x)
    (ht : t ≤ max (2 * x) (a - x)) :
    foldExcessDensity a t x = 0 := by
  rcases le_or_gt t (2 * x) with h2x | h2x
  · exact foldExcessDensity_of_le h2x
  · have hsub : t ≤ a - x := by
      rcases le_max_iff.mp ht with h | h
      · linarith
      · exact h
    exact foldExcessDensity_eq_zero_of_add_le hx (by linarith) (by linarith)

/-- **Uniform Shift Annihilation below `(2 / 3) * a`:**
Every shift `t ≤ (2 / 3) * a` has `foldExcessDensity a t x = 0` for **all** `x ≥ 0`. -/
theorem foldExcessDensity_eq_zero_of_le_two_thirds {a t x : ℝ} (hx : 0 ≤ x)
    (ht : t ≤ 2 / 3 * a) :
    foldExcessDensity a t x = 0 :=
  foldExcessDensity_eq_zero_of_le_max hx (ht.trans (two_thirds_mul_le_max_two_mul_sub a x))

/-- Any prime-power term with `log n ≤ max (2 * x) (a - x)` vanishes in `foldExcessWeight a x`. -/
theorem vonMangoldt_foldExcess_eq_zero_of_log_le_max {a x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hn : Real.log n ≤ max (2 * x) (a - x)) :
    vonMangoldtAtom n * foldExcessDensity a (Real.log n) x = 0 := by
  rw [foldExcessDensity_eq_zero_of_le_max hx hn, mul_zero]

/-- **Global Prime-Power Annihilation below `(2 / 3) * a`:**
Every prime power `n` with `log n ≤ (2 / 3) * a` contributes zero to `foldExcessWeight a x`
for **every** `x ≥ 0`. -/
theorem vonMangoldt_foldExcess_eq_zero_of_log_le_two_thirds {a x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hn : Real.log n ≤ 2 / 3 * a) :
    vonMangoldtAtom n * foldExcessDensity a (Real.log n) x = 0 := by
  rw [foldExcessDensity_eq_zero_of_le_two_thirds hx hn, mul_zero]

/-- **Prime-2 Origin Obstruction Removal:**
When `a ≥ (3 / 2) * log 2`, the prime `n = 2` (which causes `ShiftedGroundStateOriginFailure`
in the raw collar mass `shiftedCollarMass a x`) is identically annihilated in
`foldExcessWeight a x` across the entire half-line `x ≥ 0`. -/
theorem prime_two_foldExcess_eq_zero_of_three_halves_log_two_le {a x : ℝ}
    (ha : 3 / 2 * Real.log 2 ≤ a) (hx : 0 ≤ x) :
    vonMangoldtAtom 2 * foldExcessDensity a (Real.log 2) x = 0 := by
  apply vonMangoldt_foldExcess_eq_zero_of_log_le_two_thirds hx
  linarith

/-! ## 2. Global Bounds on `foldExcessWeight` -/

/-- The fold-excess weight `W_a(x)` is everywhere nonnegative. -/
theorem foldExcessWeight_nonneg (a x : ℝ) : 0 ≤ foldExcessWeight a x := by
  unfold foldExcessWeight
  refine add_nonneg ?_ ?_
  · exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (foldExcessDensity_nonneg a t x)
  · exact tsum_nonneg fun n =>
      mul_nonneg (vonMangoldtAtom_nonneg n) (foldExcessDensity_nonneg a _ x)

theorem measurable_foldExcessDensity_left (a x : ℝ) :
    Measurable fun t => foldExcessDensity a t x :=
  (measurable_foldExcessDensity_uncurry a).comp (measurable_id.prodMk measurable_const)

theorem integrableOn_archLevy_foldExcessDensity {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t => archLevyDensity t * foldExcessDensity a t x) (Ioi 0) := by
  refine (integrableOn_archLevy_max_shiftDifference ha hx).mono'
    (measurable_archLevyDensity.mul (measurable_foldExcessDensity_left a x)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 := (mem_Ioi.mp ht).le
  have hL := (archLevyDensity_pos (mem_Ioi.mp ht)).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL,
    abs_of_nonneg (foldExcessDensity_nonneg a t x)]
  exact mul_le_mul_of_nonneg_left (foldExcessDensity_le_max ha.le ht0 hx.le) hL

/-- For `a > 0` and `x > 0`, the fold-excess weight is bounded above by the raw reflected
collar mass `shiftedCollarMass a x`. -/
theorem foldExcessWeight_le_shiftedCollarMass {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    foldExcessWeight a x ≤ shiftedCollarMass a x := by
  unfold foldExcessWeight shiftedCollarMass
  refine add_le_add ?_ ?_
  · refine setIntegral_mono_on (integrableOn_archLevy_foldExcessDensity ha hx)
      (integrableOn_archLevy_max_shiftDifference ha hx) measurableSet_Ioi fun t ht => ?_
    exact mul_le_mul_of_nonneg_left
      (foldExcessDensity_le_max ha.le (mem_Ioi.mp ht).le hx.le)
      (archLevyDensity_pos (mem_Ioi.mp ht)).le
  · refine Summable.tsum_le_tsum (fun n => ?_)
      (summable_atom_mul_foldExcessDensity ha.le hx.le)
      (summable_atom_max_shiftDifference a x)
    exact mul_le_mul_of_nonneg_left
      (foldExcessDensity_le_max ha.le (Real.log_natCast_nonneg n) hx.le)
      (vonMangoldtAtom_nonneg n)

/-! ## 3. Support-Localized Weight Criterion & Odd-Profile Monotone Domination -/

/-- **Support-Localized Weight Criterion:**
To guarantee `0 ≤ markovEnergy (Φ(ω_a u))` for an even, nonnegative, nonincreasing profile
`u ∈ C²_c(ℝ)`, the weight bound `W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` only needs to hold at
points `x > 0` where `u x ≠ 0`. -/
theorem markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_support_weight_le
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hnn : ∀ x, 0 ≤ u x) (hanti : AntitoneOn u (Ici 0))
    (hW : ∀ x, 0 < x → u x ≠ 0 →
      foldExcessWeight a x ≤ 2 * Real.sinh (a / 2) * Real.sinh (x / 2)) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  refine le_trans ?_ (markovEnergy_phiDoob_shiftedGroundState_ge_of_antitone ha hu huc heven hnn hanti)
  have hI1 := integrableOn_sq_mul_shiftDifference_mul_foldExcessWeight ha hu.continuous huc
  have hI2 : IntegrableOn (fun x => (2 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) *
      u x ^ 2) (Ioi 0) :=
    integrableOn_continuous_mul_sq ((continuous_const.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))) hu.continuous huc _
  have hI2' : IntegrableOn (fun x => 2 * Real.sinh (a / 2) *
      (u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) :=
    hI2.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have hmono : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * foldExcessWeight a x) ≤
      ∫ x in Ioi (0 : ℝ), 2 * Real.sinh (a / 2) *
        (u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) := by
    refine setIntegral_mono_on hI1 hI2' measurableSet_Ioi fun x hx => ?_
    by_cases hux : u x = 0
    · simp [hux]
    · have hm0 := shiftDifference_nonneg_of_nonneg ha.le (mem_Ioi.mp hx).le
      calc u x ^ 2 * shiftDifference a x * foldExcessWeight a x
          ≤ u x ^ 2 * shiftDifference a x * (2 * Real.sinh (a / 2) * Real.sinh (x / 2)) :=
            mul_le_mul_of_nonneg_left (hW x (mem_Ioi.mp hx) hux) (mul_nonneg (sq_nonneg _) hm0)
        _ = _ := by ring
  rw [integral_const_mul] at hmono
  linarith

/-- **Monotone Fold-Domination Lower Bound in Odd-Profile Coordinates:**
For `a > 0` and any even `w ∈ C²_c(ℝ)` that is nonnegative and nonincreasing on `[0, ∞)`,
```
2 ∫_{x>0} oddProfile a x · sinh(x/2) · w(x)²
  − (1 / sinh(a/2)) ∫_{x>0} oddProfile a x · foldExcessWeight a x · w(x)²
  ≤ markovEnergy (oddProfileTest a w).
``` -/
theorem markovEnergy_oddProfileTest_ge_of_antitone {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hnn : ∀ x, 0 ≤ w x) (hanti : AntitoneOn w (Ici 0)) :
    2 * (∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) -
        1 / Real.sinh (a / 2) *
          (∫ x in Ioi (0 : ℝ), oddProfile a x * foldExcessWeight a x * w x ^ 2) ≤
      markovEnergy (fun x => (oddProfileTest a w x : ℂ)) := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  rw [oddProfileTest_eq_smul_phiDoob ha, markovEnergy_real_smul]
  have hge := markovEnergy_phiDoob_shiftedGroundState_ge_of_antitone ha hw hwc heven hnn hanti
  have hI1 : (∫ x in Ioi (0 : ℝ), w x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      2 * Real.sinh (a / 2) *
        ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [shiftDifference_eq_two_sinh_mul_oddProfile ha.ne']
    ring
  have hI2 : (∫ x in Ioi (0 : ℝ), w x ^ 2 * shiftDifference a x * foldExcessWeight a x) =
      2 * Real.sinh (a / 2) *
        ∫ x in Ioi (0 : ℝ), oddProfile a x * foldExcessWeight a x * w x ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [shiftDifference_eq_two_sinh_mul_oddProfile ha.ne']
    ring
  have hmul := mul_le_mul_of_nonneg_left hge (sq_nonneg (1 / (2 * Real.sinh (a / 2))))
  rw [hI1, hI2] at hmul
  refine le_trans ?_ hmul
  apply le_of_eq
  field_simp
  ring

/-- **Support-Localized Odd-Profile Positivity Criterion:**
For `a > 0` and any even `w ∈ C²_c(ℝ)` that is nonnegative and nonincreasing on `[0, ∞)`,
if `foldExcessWeight a x ≤ 2 * Real.sinh (a / 2) * Real.sinh (x / 2)` for all `x > 0` in the
active support `w x ≠ 0`, then `0 ≤ markovEnergy (oddProfileTest a w)`. -/
theorem markovEnergy_oddProfileTest_nonneg_of_antitone_of_support_weight_le
    {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hnn : ∀ x, 0 ≤ w x) (hanti : AntitoneOn w (Ici 0))
    (hW : ∀ x, 0 < x → w x ≠ 0 →
      foldExcessWeight a x ≤ 2 * Real.sinh (a / 2) * Real.sinh (x / 2)) :
    0 ≤ markovEnergy (fun x => (oddProfileTest a w x : ℂ)) := by
  rw [oddProfileTest_eq_smul_phiDoob ha, markovEnergy_real_smul]
  exact mul_nonneg (sq_nonneg _)
    (markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_support_weight_le
      ha hw hwc heven hnn hanti hW)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
