import GaloisForLFunctions.RHTower.ZetaRigidOrdinateLorentzSum
import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationLeadingOrder

/-!
# The anti-crystal law for the zeros of ζ

**Theorem** (`not_rigidOrdinates`). For no `h > 0` and no index `N₀` are the ordered positive
ordinates of the zeros of `ζ` `h`-rigid from `N₀` on. In other words, they cannot from some point
on increase strictly with consecutive gaps `g, g'` obeying `g' ≤ g e^{(g+g')/h}` and
`g ≤ g' e^{(g+g')/h}`.

So the zeros of ζ are never, from some height on, a slowly modulated lattice at a fixed scale `h`.
The theorem is unconditional. Strict increase alone would already put all zeros above `γ_{N₀}` on
the critical line (`RigidOrdinates.re_eq_half`).

**Proof.**
* Rigidity bounds Montgomery's Lorentzian zero sum `S(T^α, t)` uniformly on `[T^{3/4}, T]`
  (`RigidOrdinates.exists_norm_lorentzZeroSumAll_le`). Below `T^{3/4}` the trivial bound
  `16√x · lorentzMass t` suffices. Hence `∫_0^T |S|² = O(T) + o(T log T)`.
* The truncation identity `∫_0^T |S|² = (π/2) F(T^α, T) + o(T log T)`
  (`integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le`, `tendsto_truncation_error_div`)
  and the unconditional pair-correlation asymptotic `F(T^α, T) ~ (T/2π) α log T`
  (`tendsto_montgomeryForm_div_leadingOrder`) give `∫_0^T |S|² ≥ (T/8) α log T` eventually.
  This is a contradiction.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The trivial bound `‖S(x,t)‖ ≤ 16√x · lorentzMass t`. -/
theorem norm_lorentzZeroSumAll_le_mass {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ‖lorentzZeroSumAll x t‖ ≤ 16 * Real.sqrt x * lorentzMass t := by
  refine (norm_tsum_le_tsum_norm (summable_norm_zeroSumTerm hx t)).trans ?_
  rw [lorentzMass, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (norm_zeroSumTerm_le hx t) (summable_norm_zeroSumTerm hx t)
    ((summable_lorentzMassTerm t).mul_left _)

/-- The low-height contribution is `o(T log T)`: eventually
`T^{3/4} (128 T^{α/2}(C + log(T + 4)))² ≤ (1/100)(T/4) α log T`. -/
theorem eventually_lowHeight_le {α : ℝ} (hα0 : 0 < α) (hα8 : α ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, T ^ (3 / 4 : ℝ) *
      (128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4))) ^ 2 ≤
        1 / 100 * ((T / 4) * (α * Real.log T)) := by
  have hC := xiLineTwoLogDerivConstant_nonneg
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop (xiLineTwoLogDerivConstant + 2)
  have e2 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 16 by norm_num)).eventually_ge_atTop
    (65536 * 16 * 400 / α)
  filter_upwards [e1, e2, eventually_ge_atTop (4 : ℝ)] with T h1 h2 hT4
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hL
  have hL0 : 0 < L := by linarith
  -- `C + log(T + 4) ≤ 2L`
  have hlog4 : xiLineTwoLogDerivConstant + Real.log (T + 4) ≤ 2 * L := by
    have h5 : Real.log (T + 4) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h5
    have := Real.log_two_lt_d9; linarith
  have hK0 : 0 ≤ xiLineTwoLogDerivConstant + Real.log (T + 4) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 4 by linarith); linarith
  -- `(√(T^α))² = T^α ≤ T^{1/8}`
  have hsq : Real.sqrt (T ^ α) ^ 2 = T ^ α := Real.sq_sqrt (Real.rpow_nonneg hT0.le _)
  have hTα : T ^ α ≤ T ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hα8
  -- `L ≤ 16 T^{1/16}`
  have hLle : L ≤ 16 * T ^ (1 / 16 : ℝ) := by
    have := Real.log_le_rpow_div hT0.le (show (0 : ℝ) < 1 / 16 by norm_num)
    linarith [show T ^ (1 / 16 : ℝ) / (1 / 16) = 16 * T ^ (1 / 16 : ℝ) by ring]
  have hsplit : T = T ^ (3 / 4 : ℝ) * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ) * T ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]; norm_num
  have hp1 : 0 ≤ T ^ (3 / 4 : ℝ) := Real.rpow_nonneg hT0.le _
  have hp2 : 0 ≤ T ^ (1 / 8 : ℝ) := Real.rpow_nonneg hT0.le _
  have hp3 : 0 ≤ T ^ (1 / 16 : ℝ) := Real.rpow_nonneg hT0.le _
  calc T ^ (3 / 4 : ℝ) *
        (128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4))) ^ 2
      = T ^ (3 / 4 : ℝ) * (16384 * T ^ α *
          (xiLineTwoLogDerivConstant + Real.log (T + 4)) ^ 2) := by rw [mul_pow, mul_pow, hsq]; ring
    _ ≤ T ^ (3 / 4 : ℝ) * (16384 * T ^ (1 / 8 : ℝ) * (2 * L) ^ 2) := by gcongr
    _ = 65536 * (T ^ (3 / 4 : ℝ) * T ^ (1 / 8 : ℝ)) * L * L := by ring
    _ ≤ 65536 * (T ^ (3 / 4 : ℝ) * T ^ (1 / 8 : ℝ)) * (16 * T ^ (1 / 16 : ℝ)) * L := by gcongr
    _ = (65536 * 16) * (T ^ (3 / 4 : ℝ) * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ)) * L := by ring
    _ ≤ (α / 400 * T ^ (1 / 16 : ℝ)) * (T ^ (3 / 4 : ℝ) * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ)) * L := by
        have hK : (65536 * 16 : ℝ) ≤ α / 400 * T ^ (1 / 16 : ℝ) := by
          rw [div_le_iff₀ hα0] at h2
          linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) hL0.le
    _ = 1 / 100 * ((T ^ (3 / 4 : ℝ) * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ) * T ^ (1 / 16 : ℝ)) / 4 *
          (α * L)) := by ring
    _ = 1 / 100 * ((T / 4) * (α * L)) := by rw [← hsplit]

/-- **The anti-crystal law.** The ordered ordinates of the zeros of `ζ` are never `h`-rigid. -/
theorem not_rigidOrdinates {h : ℝ} (hh : 0 < h) (N₀ : ℕ) : ¬ RigidOrdinates h N₀ := by
  intro H
  obtain ⟨α, hα0, hα8, C, hev⟩ := H.exists_norm_lorentzZeroSumAll_le hh
  have hα1 : α < 1 := by linarith
  have hM := tendsto_montgomeryForm_div_leadingOrder hα0 hα1
  have hTr := tendsto_truncation_error_div hα0 hα1 xiLineTwoLogDerivConstant
    xiLineTwoLogDerivConstant_nonneg
  have e1 := hM.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have e2 := hTr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  have e3 := eventually_lowHeight_le hα0 hα8
  have e4 := Real.tendsto_log_atTop.eventually_ge_atTop (400 * C ^ 2 / α + 1)
  obtain ⟨T, hTev, hT1, hT2, hT3, hT4, hT16⟩ :=
    (hev.and (e1.and (e2.and (e3.and (e4.and (eventually_ge_atTop (16 : ℝ))))))).exists
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hN0 : 0 < (T / 4) * (α * L) := by positivity
  have hx1 : 1 ≤ T ^ α := Real.one_le_rpow (by linarith) hα0.le
  set Q := T ^ (3 / 4 : ℝ) with hQ
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hT0.le _
  have hQT : Q ≤ T := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  -- the Montgomery lower bound
  have hF : (1 / 2 : ℝ) * ((T / (2 * Real.pi)) * (α * L)) <
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    have hden : 0 < (T / (2 * Real.pi)) * (α * L) := by positivity
    rwa [lt_div_iff₀ hden] at hT1
  -- the truncation bound
  have htrunc := integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le hx1 hT0.le
  have hT2' : 131072 * T ^ α * ((xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) ^ 2 *
      (3 * Real.log (1 + T) + 2) + 64) < 1 / 100 * ((T / 4) * (α * L)) := by
    rwa [div_lt_iff₀ hN0] at hT2
  have htr : |(∫ t in Icc 0 T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) - Real.pi / 2 *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re| <
      1 / 100 * ((T / 4) * (α * L)) := by
    refine lt_of_le_of_lt htrunc ?_
    unfold truncationLog
    exact hT2'
  -- the upper bound on `∫_0^T |S|²`
  have hint := integrableOn_normSq_lorentzZeroSumAll hx1 T
  have hi1 : IntervalIntegrable (fun t => ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) volume 0 Q :=
    (hint.mono_set (by rw [uIcc_of_le hQ0]; exact Icc_subset_Icc le_rfl hQT)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) volume Q T :=
    (hint.mono_set (by rw [uIcc_of_le hQT]; exact Icc_subset_Icc hQ0 le_rfl)).intervalIntegrable
  have hsplitI : (∫ t in Icc 0 T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) =
      (∫ t in (0 : ℝ)..Q, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) +
        ∫ t in Q..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 := by
    rw [setIntegral_Icc_normSq_lorentzZeroSumAll hT0.le,
      intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  -- low heights
  set A := 128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4)) with hA
  have hlow : (∫ t in (0 : ℝ)..Q, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) ≤ A ^ 2 * Q := by
    have hb : ∀ t ∈ uIoc 0 Q, ‖‖lorentzZeroSumAll (T ^ α) t‖ ^ 2‖ ≤ A ^ 2 := by
      intro t ht
      rw [uIoc_of_le hQ0] at ht
      have ht0 : 0 ≤ t := ht.1.le
      have htT : t ≤ T := le_trans ht.2 hQT
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := norm_lorentzZeroSumAll_le_mass hx1 t
      have h2 := lorentzMass_le_log t
      rw [abs_of_nonneg ht0] at h2
      have h3 : Real.log (t + 4) ≤ Real.log (T + 4) := Real.log_le_log (by linarith) (by linarith)
      have hS : ‖lorentzZeroSumAll (T ^ α) t‖ ≤ A := by
        refine h1.trans ?_
        rw [hA]
        calc 16 * Real.sqrt (T ^ α) * lorentzMass t
            ≤ 16 * Real.sqrt (T ^ α) * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) := by
              gcongr; rw [abs_of_nonneg ht0]; exact h2
          _ ≤ 16 * Real.sqrt (T ^ α) * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4))) := by
              rw [abs_of_nonneg ht0]; gcongr
          _ = 128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4)) := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) hS 2
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hQ0] at this
    exact (le_abs_self _).trans this
  -- high heights
  have hhigh : (∫ t in Q..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) ≤ C ^ 2 * T := by
    have hb : ∀ t ∈ uIoc Q T, ‖‖lorentzZeroSumAll (T ^ α) t‖ ^ 2‖ ≤ C ^ 2 := by
      intro t ht
      rw [uIoc_of_le hQT] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hS := hTev t ⟨ht.1.le, ht.2⟩
      exact pow_le_pow_left₀ (norm_nonneg _) hS 2
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ T - Q by linarith)] at this
    have h1 := (le_abs_self _).trans this
    have h2 : C ^ 2 * (T - Q) ≤ C ^ 2 * T := by nlinarith [sq_nonneg C]
    linarith
  -- `C² T ≤ (1/100)(T/4) α L`
  have hC2 : C ^ 2 * T ≤ 1 / 100 * ((T / 4) * (α * L)) := by
    have : 400 * C ^ 2 / α ≤ L := by linarith
    rw [div_le_iff₀ hα0] at this
    nlinarith
  have hlow' : A ^ 2 * Q ≤ 1 / 100 * ((T / 4) * (α * L)) := by
    have := hT3; rw [hA]; linarith [show Q * A ^ 2 = A ^ 2 * Q by ring]
  -- contradiction
  rw [hsplitI] at htr
  have hpi : Real.pi / 2 * ((1 / 2 : ℝ) * ((T / (2 * Real.pi)) * (α * L))) = (T / 8) * (α * L) := by
    field_simp; ring
  have hFpi : (T / 8) * (α * L) < Real.pi / 2 *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    rw [← hpi]
    exact mul_lt_mul_of_pos_left hF (by positivity)
  have habs := (abs_lt.mp htr).1
  nlinarith

end

end RHTower
