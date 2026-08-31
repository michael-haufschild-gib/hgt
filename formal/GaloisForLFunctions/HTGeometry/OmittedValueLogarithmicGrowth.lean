import GaloisForLFunctions.HTGeometry.OmittedValueCharacteristicBound
import GaloisForLFunctions.HTGeometry.LogSelfBoundArithmetic
import GaloisForLFunctions.HTGeometry.BorelGrowthExponent

/-!
# Logarithmic growth of a function omitting two values

The quantitative bound of `OmittedValueCharacteristicBound` relates `T(r)` to `T(R)` for any
`R > r`.  Choosing `R = r + T(r)^{-1/2}` and applying the Borel growth lemma at exponent `1/2` makes
`T(R) ≤ 2T(r)` and `2R/(R−r)² = 2R·T(r)`, and the bound collapses to a self-referential logarithmic
inequality `T ≤ A + 6 log(T+1) + B`, which forces `T = O(log r)`.

The Borel lemma is used in its *window* form: a good radius inside `[s, s + borelWindow]`, not merely
cofinally.  A cofinal good set would bound `T(s)` by `A log r + B` for some unrelated `r ≥ s`, which
is no bound at all; a good radius within a fixed distance of `s` gives `T(s) = O(log s)`.

Monotonicity of the characteristic — mathlib's `characteristic_monotoneOn` — is what lets the Borel
lemma apply and what transports the bound from the good radius back to `s`.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real Set

/-- The shifted characteristic, monotone on all of `ℝ` and at least one. -/
noncomputable def charPlusOne (F : ℂ → ℂ) (x : ℝ) : ℝ := characteristic F ⊤ (max x 1) + 1

theorem monotone_charPlusOne {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Monotone (charPlusOne F) := by
  intro p q hpq
  have hmono := ValueDistribution.characteristic_monotoneOn
    (f := F) (fun z => (hF.analyticAt z).meromorphicAt)
  have hp : max p 1 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hq : max q 1 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hle : max p 1 ≤ max q 1 := max_le_max hpq le_rfl
  have := hmono hp hq hle
  rw [charPlusOne, charPlusOne]
  linarith

theorem one_le_charPlusOne {F : ℂ → ℂ} (hF : Differentiable ℂ F) (x : ℝ) :
    1 ≤ charPlusOne F x := by
  have := characteristic_nonneg_of_entire hF (max x 1)
  rw [charPlusOne]
  linarith

theorem charPlusOne_eq {F : ℂ → ℂ} {x : ℝ} (hx : 1 ≤ x) :
    charPlusOne F x = characteristic F ⊤ x + 1 := by
  rw [charPlusOne, max_eq_left hx]

set_option maxHeartbeats 2000000 in
/-- **The characteristic of a function omitting two values is `O(log r)`.**  The Borel growth lemma
at exponent `1/2` supplies, inside every window, a radius where the shifted characteristic does not
double; there the quantitative bound collapses to a logarithm. -/
theorem exists_characteristic_le_log_of_omits_two {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hF' : ∀ z, deriv F z ≠ 0) {K : ℝ}
    (hfmt : ∀ r : ℝ, r ≠ 0 → ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    ∃ A B : ℝ, 1 ≤ A ∧ ∀ s : ℝ, 1 ≤ s → characteristic F ⊤ s ≤ 6 * Real.log (s + A) + B := by
  classical
  set W : ℝ := Nevanlinna.borelWindow (1 / 2) with hW
  have hW1 : 1 ≤ W := Nevanlinna.one_le_borelWindow _
  set Cbig : ℝ := 2 * (Real.posLog ‖a₁‖ + Real.log 2) + 2 * (Real.posLog ‖a₂‖ + Real.log 2)
    + |Real.log ‖F 0 - a₁‖| + |Real.log ‖F 0 - a₂‖| with hCbigdef
  have hCbig0 : 0 ≤ Cbig := by
    have h1 := Real.posLog_nonneg (x := ‖a₁‖)
    have h2 := Real.posLog_nonneg (x := ‖a₂‖)
    have h3 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h4 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₁‖| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₂‖| := abs_nonneg _
    rw [hCbigdef]
    linarith
  set Csmall : ℝ := (2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
      + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
    - Real.log ‖deriv F 0‖ + (Real.posLog ‖a₁‖ + Real.log 2) with hCsmalldef
  set D : ℝ := 4 + Cbig with hD
  have hD4 : (4 : ℝ) ≤ D := by rw [hD]; linarith
  set B' : ℝ := max (6 * Real.log 2 + Csmall) 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨max 6 (W + 1), 6 * Real.log (2 * D) + 2 * B' + 1156, le_max_of_le_left (by norm_num), ?_⟩
  intro s hs
  -- a Borel-good radius inside the window `[s, s + W]`
  obtain ⟨x, hxmem, hxborel⟩ :=
    Nevanlinna.exists_mem_Icc_lt_two_mul_rpow_window (monotone_charPlusOne hF)
      (one_le_charPlusOne hF) (by norm_num : (0:ℝ) < 1/2) s
  have hxs : s ≤ x := hxmem.1
  have hxW : x ≤ s + W := hxmem.2
  have hx1 : (1 : ℝ) ≤ x := le_trans hs hxs
  have hx0 : (0 : ℝ) < x := by linarith
  set T₀ : ℝ := characteristic F ⊤ x with hT₀
  have hT₀0 : 0 ≤ T₀ := characteristic_nonneg_of_entire hF x
  have hTx : charPlusOne F x = T₀ + 1 := charPlusOne_eq hx1
  set step : ℝ := (charPlusOne F x) ^ (-(1/2 : ℝ)) with hstep
  have hstep0 : 0 < step := Real.rpow_pos_of_pos (by linarith [one_le_charPlusOne hF x]) _
  have hstep1 : step ≤ 1 := by
    rw [hstep]
    refine Real.rpow_le_one_of_one_le_of_nonpos (one_le_charPlusOne hF x) (by norm_num)
  set R : ℝ := x + step with hR
  have hxR : x < R := by rw [hR]; linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; linarith
  have hRx1 : R ≤ x + 1 := by rw [hR]; linarith
  -- the Borel step
  have hcharR : characteristic F ⊤ R ≤ 2 * T₀ + 1 := by
    have h := hxborel
    rw [hTx] at h
    have hR' : charPlusOne F R = characteristic F ⊤ R + 1 := charPlusOne_eq hR1
    rw [hR'] at h
    linarith
  -- the main quantitative inequality at `(x, R)`
  have hmain := characteristic_le_log_of_omits_two hF hane h₁ h₂ hF'
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1) hx0 hxR hR1 (hfmt x (ne_of_gt hx0))
  rw [← hCbigdef, ← hCsmalldef, ← hT₀] at hmain
  -- the window factor
  have hstepsq : (R - x) ^ 2 = (T₀ + 1)⁻¹ := by
    have hxx : R - x = step := by rw [hR]; ring
    rw [hxx, hstep, hTx, ← Real.rpow_natCast ((T₀ + 1) ^ (-(1/2 : ℝ))) 2,
      ← Real.rpow_mul (by linarith)]
    norm_num
    rw [Real.rpow_neg_one]
  have hT1pos : (0 : ℝ) < T₀ + 1 := by linarith
  have hfactor : 2 * R / (R - x) ^ 2 = 2 * R * (T₀ + 1) := by
    rw [hstepsq]
    field_simp
  -- collapse the inner quantity
  set y : ℝ := 2 * R / (R - x) ^ 2 * (2 * characteristic F ⊤ R + Cbig) with hy
  have hy0 : 0 ≤ y := by
    have h1 : 0 ≤ characteristic F ⊤ R := characteristic_nonneg_of_entire hF R
    have h2 : (0 : ℝ) < 2 * R / (R - x) ^ 2 := by
      rw [hfactor]
      positivity
    rw [hy]
    have : (0 : ℝ) ≤ 2 * characteristic F ⊤ R + Cbig := by linarith
    positivity
  have hyle : y ≤ 2 * D * (x + 1) * (T₀ + 1) ^ 2 := by
    rw [hy, hfactor]
    have hinner : 2 * characteristic F ⊤ R + Cbig ≤ D * (T₀ + 1) := by
      rw [hD]
      nlinarith [hcharR, hCbig0, hT₀0]
    have hRle : 2 * R * (T₀ + 1) ≤ 2 * (x + 1) * (T₀ + 1) := by nlinarith [hRx1, hT1pos]
    have hinner0 : (0 : ℝ) ≤ 2 * characteristic F ⊤ R + Cbig := by
      have := characteristic_nonneg_of_entire hF R
      linarith
    calc 2 * R * (T₀ + 1) * (2 * characteristic F ⊤ R + Cbig)
        ≤ 2 * (x + 1) * (T₀ + 1) * (2 * characteristic F ⊤ R + Cbig) :=
          mul_le_mul_of_nonneg_right hRle hinner0
      _ ≤ 2 * (x + 1) * (T₀ + 1) * (D * (T₀ + 1)) := by
          refine mul_le_mul_of_nonneg_left hinner ?_
          nlinarith [hx1, hT1pos]
      _ = 2 * D * (x + 1) * (T₀ + 1) ^ 2 := by ring
  have hbig1 : (1 : ℝ) ≤ 2 * D * (x + 1) * (T₀ + 1) ^ 2 := by
    have hq1 : (1:ℝ) ≤ (T₀ + 1) ^ 2 := by nlinarith [hT₀0]
    have hq2 : (2:ℝ) ≤ x + 1 := by linarith
    have h2 : (16 : ℝ) ≤ 2 * D * (x + 1) := by nlinarith [hD4, hq2]
    nlinarith [h2, hq1]
  have hposlog : Real.posLog y ≤ Real.log (2 * D) + Real.log (x + 1) + 2 * Real.log (T₀ + 1) := by
    have hmono : Real.posLog y ≤ Real.posLog (2 * D * (x + 1) * (T₀ + 1) ^ 2) :=
      Real.posLog_le_posLog hy0 hyle
    have heq : Real.posLog (2 * D * (x + 1) * (T₀ + 1) ^ 2)
        = Real.log (2 * D * (x + 1) * (T₀ + 1) ^ 2) := by
      refine Real.posLog_eq_log ?_
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * D * (x + 1) * (T₀ + 1) ^ 2)]
      exact hbig1
    rw [heq] at hmono
    have hsplit : Real.log (2 * D * (x + 1) * (T₀ + 1) ^ 2)
        = Real.log (2 * D) + Real.log (x + 1) + 2 * Real.log (T₀ + 1) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
      push_cast
      ring
    linarith [hmono, hsplit]
  have hlogy : Real.log (1 + y ^ ((1:ℝ)/2))
      ≤ Real.log 2 + (1/2) * (Real.log (2 * D) + Real.log (x + 1) + 2 * Real.log (T₀ + 1)) := by
    refine le_trans (log_one_add_rpow_le hy0 (by norm_num)) ?_
    linarith [hposlog]
  -- feed into the self-bound collapse
  have hself : T₀ ≤ (3 * Real.log (2 * D) + 3 * Real.log (x + 1))
      + 6 * Real.log (T₀ + 1) + B' := by
    have hval : (3 : ℝ) / (1/2) = 6 := by norm_num
    rw [hval] at hmain
    have hBle : 6 * Real.log 2 + Csmall ≤ B' := le_max_left _ _
    linarith [hmain, hlogy, hBle]
  have hAB0 : (0 : ℝ) ≤ (3 * Real.log (2 * D) + 3 * Real.log (x + 1)) + B' := by
    have h1 : (0 : ℝ) ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    linarith
  have hfinal := le_of_le_add_six_log hT₀0 hAB0 hself
  -- transport back to `s`
  have hmonos : characteristic F ⊤ s ≤ T₀ := by
    have hmono := ValueDistribution.characteristic_monotoneOn
      (f := F) (fun z => (hF.analyticAt z).meromorphicAt)
    exact hmono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr hx0) hxs
  have hlogx : Real.log (x + 1) ≤ Real.log (s + max 6 (W + 1)) := by
    refine Real.log_le_log (by linarith) ?_
    have : W + 1 ≤ max 6 (W + 1) := le_max_right _ _
    linarith
  linarith [hfinal, hmonos, hlogx]

end GaloisForLFunctions.HTGeometry
