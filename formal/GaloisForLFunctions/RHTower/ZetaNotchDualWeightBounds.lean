import GaloisForLFunctions.RHTower.ZetaNotchDualOscillationBound
import GaloisForLFunctions.RHTower.ZetaNotchDiagonalSum
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# Pointwise bounds for the critical dual weight and the two diagonal main terms

* Dual line: `‖W_t(Y)‖ ≤ C₁ (1+|t|)²/Y` (`exists_norm_critDualWeight_le`).
* Right line after the residue shift, for `t ≥ 1`:
  `‖W_t(Y) − 1‖ ≤ C₂ Y^{1/4} t^{−1/2}` (`exists_norm_critDualWeight_sub_one_le`).

Hence `z ↦ W_t(z t²)` is a cutoff in the sense of `diagSum`. The two diagonal sums of the product
approximate functional equation at scale `x = L` satisfy:

* direct: `‖Σ j^{−1} V(N j²/L) − ½ log(L/N)‖ ≤ C` for `N ≤ L` (`exists_norm_directDiag_sub_le`);
* dual: `‖Σ j^{−1} W_t(N j² L) − ½ log(t²/(NL))‖ ≤ C` for `N ≤ t²/L`, `t ≥ 1`
  (`exists_norm_dualDiag_sub_le`).

Their sum is `log(t/N)` up to `O(1)`. This is the classical diagonal of the twisted second moment.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-- **Dual-line pointwise bound.** -/
theorem exists_norm_critDualWeight_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) {Y : ℝ}, 0 < Y → ‖critDualWeight t Y‖ ≤ C * (1 + |t|) ^ 2 / Y := by
  set I₂ : ℝ := ∫ v : ℝ, (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ))) with hI₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun v => by positivity
  refine ⟨(1 / (2 * Real.pi)) * Real.exp 1 * I₂, by positivity, fun t {Y} hY => ?_⟩
  rw [critDualWeight_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hmaj : Integrable (fun v : ℝ => ((1 + |t|) ^ 2 * (Y⁻¹ * Real.exp 1)) *
      ((1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ))))) :=
    (integrable_one_add_abs_pow_mul_exp_neg_sq 2).const_mul _
  have hb := norm_integral_le_of_norm_le (f := fun v : ℝ =>
      critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) hmaj
    (Filter.Eventually.of_forall fun v => norm_critDualIntegrand_one_le hY t v)
  rw [integral_const_mul] at hb
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * ((1 + |t|) ^ 2 * (Y⁻¹ * Real.exp 1) * I₂) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / (2 * Real.pi) * Real.exp 1 * I₂ * (1 + |t|) ^ 2 / Y := by
        field_simp

theorem exp_neg_sq_div_eight_le {t : ℝ} (ht : 1 ≤ t) : Real.exp (-(t ^ 2) / 8) ≤ 8 / Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  have h1 : Real.exp (-(t ^ 2) / 8) ≤ Real.exp (-(t / 8)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h2 : Real.exp (-(t / 8)) ≤ 8 / t := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have := Real.add_one_le_exp (t / 8)
    rw [inv_div]
    linarith
  have h3 : 8 / t ≤ 8 / Real.sqrt t := by
    apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr ht0)
    have hs : Real.sqrt t ≤ t := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    exact hs
  linarith

/-- **Right-line pointwise bound**: `‖W_t(Y) − 1‖ ≤ C Y^{1/4} t^{−1/2}` for `t ≥ 1`. -/
theorem exists_norm_critDualWeight_sub_one_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t Y : ℝ}, 1 ≤ t → 0 < Y →
      ‖critDualWeight t Y - 1‖ ≤ C * Y ^ rightAbscissa / Real.sqrt t := by
  obtain ⟨K', hK', hb⟩ := exists_norm_critDualIntegrand_neg_le rightAbscissa_pos
    rightAbscissa_lt_half
  set C : ℝ := (1 / (2 * Real.pi)) * K' * (Real.sqrt 2 * Real.sqrt Real.pi +
    8 * Real.sqrt (4 * Real.pi)) with hCdef
  refine ⟨C, by positivity, fun {t Y} ht hY => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [critDualWeight_eq_one_add_at_neg rightAbscissa_pos rightAbscissa_lt_half hY t,
    add_sub_cancel_left]
  unfold critDualWeightAt
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  set S : Set ℝ := {v : ℝ | |v| ≤ t / 2} with hS
  have hSmeas : MeasurableSet Sᶜ :=
    (isClosed_le continuous_abs continuous_const).measurableSet.compl
  have hδ := rightAbscissa_pos
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  -- the envelope
  set g : ℝ → ℝ := fun v => K' * Y ^ rightAbscissa *
    (Real.sqrt 2 / Real.sqrt t * Real.exp (-(v ^ (2 : ℕ))) +
      Sᶜ.indicator (fun v => (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ)))) v) with hg
  have hgint : Integrable g := by
    have h1 := (integrable_one_add_abs_pow_mul_exp_neg_sq 0).const_mul (Real.sqrt 2 / Real.sqrt t)
    have h2 := (integrable_one_add_abs_pow_mul_exp_neg_sq 0).indicator hSmeas
    have h1' : Integrable (fun v : ℝ => Real.sqrt 2 / Real.sqrt t * Real.exp (-(v ^ (2 : ℕ)))) := by
      simpa using h1
    exact (h1'.add h2).const_mul _
  have hpt : ∀ v : ℝ, ‖critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ g v := by
    intro v
    refine (hb hY t v).trans ?_
    simp only [hg]
    have hden : 1 / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa) ≤
        Real.sqrt 2 / Real.sqrt t + Sᶜ.indicator (fun _ => (1 : ℝ)) v := by
      have hd1 : 1 ≤ (max 1 |t - v|) ^ rightAbscissa := Real.one_le_rpow (le_max_left _ _) hδ.le
      have hd2 : 1 ≤ (max 1 |-t - v|) ^ rightAbscissa := Real.one_le_rpow (le_max_left _ _) hδ.le
      by_cases hv : |v| ≤ t / 2
      · have hnot : v ∉ Sᶜ := by simp [hS, hv]
        rw [indicator_of_notMem hnot, add_zero]
        have h1 : t / 2 ≤ max 1 |t - v| := by
          refine le_trans ?_ (le_max_right _ _)
          have := abs_sub_abs_le_abs_sub t v
          rw [abs_of_pos ht0] at this
          linarith
        have h2 : t / 2 ≤ max 1 |-t - v| := by
          refine le_trans ?_ (le_max_right _ _)
          have := abs_sub_abs_le_abs_sub (-t) v
          rw [abs_neg, abs_of_pos ht0] at this
          linarith
        have hp1 : (t / 2) ^ rightAbscissa ≤ (max 1 |t - v|) ^ rightAbscissa :=
          Real.rpow_le_rpow (by linarith) h1 hδ.le
        have hp2 : (t / 2) ^ rightAbscissa ≤ (max 1 |-t - v|) ^ rightAbscissa :=
          Real.rpow_le_rpow (by linarith) h2 hδ.le
        have hq : (t / 2) ^ rightAbscissa * (t / 2) ^ rightAbscissa = Real.sqrt (t / 2) := by
          rw [← Real.rpow_add (by linarith), show rightAbscissa + rightAbscissa = 1 / 2 by
            unfold rightAbscissa; norm_num, ← Real.sqrt_eq_rpow]
        have hq0 : 0 < (t / 2) ^ rightAbscissa := Real.rpow_pos_of_pos (by linarith) _
        calc 1 / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa)
            ≤ 1 / ((t / 2) ^ rightAbscissa * (t / 2) ^ rightAbscissa) := by
              apply one_div_le_one_div_of_le (by positivity)
              exact mul_le_mul hp1 hp2 hq0.le (by linarith)
          _ = Real.sqrt 2 / Real.sqrt t := by
              rw [hq, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
              field_simp
      · have hmem : v ∈ Sᶜ := by simp [hS, hv]
        rw [indicator_of_mem hmem]
        have : 1 / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        have : 0 ≤ Real.sqrt 2 / Real.sqrt t := by positivity
        linarith
    have hind : Sᶜ.indicator (fun _ => (1 : ℝ)) v * Real.exp (-(v ^ (2 : ℕ))) =
        Sᶜ.indicator (fun v => (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ)))) v := by
      by_cases hv : v ∈ Sᶜ
      · rw [indicator_of_mem hv, indicator_of_mem hv, pow_zero]
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul]
    rw [← hind]
    calc K' * Y ^ rightAbscissa / ((max 1 |t - v|) ^ rightAbscissa * (max 1 |-t - v|) ^ rightAbscissa)
          * Real.exp (-(v ^ (2 : ℕ)))
        = K' * Y ^ rightAbscissa * (1 / ((max 1 |t - v|) ^ rightAbscissa *
            (max 1 |-t - v|) ^ rightAbscissa)) * Real.exp (-(v ^ (2 : ℕ))) := by ring
      _ ≤ K' * Y ^ rightAbscissa * (Real.sqrt 2 / Real.sqrt t +
            Sᶜ.indicator (fun _ => (1 : ℝ)) v) * Real.exp (-(v ^ (2 : ℕ))) := by
          gcongr
      _ = _ := by ring
  have hbound := norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hgval : ∫ v, g v ≤ K' * Y ^ rightAbscissa * (Real.sqrt 2 / Real.sqrt t * Real.sqrt Real.pi +
      Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(t / 2) ^ 2 / 2) * Real.sqrt (4 * Real.pi)) := by
    have htail := integral_one_add_abs_pow_mul_exp_neg_sq_compl_le 0 (V := t / 2) (by linarith)
    have hgauss : ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) = Real.sqrt Real.pi := by
      have := integral_gaussian 1
      simpa using this
    have hsplit : ∫ v, g v = K' * Y ^ rightAbscissa * (Real.sqrt 2 / Real.sqrt t *
        Real.sqrt Real.pi + ∫ v in Sᶜ, (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ)))) := by
      simp only [hg]
      rw [integral_const_mul, integral_add, integral_const_mul, integral_indicator hSmeas, hgauss]
      · exact ((integrable_one_add_abs_pow_mul_exp_neg_sq 0).const_mul
          (Real.sqrt 2 / Real.sqrt t)).congr (Filter.Eventually.of_forall fun v => by simp)
      · exact (integrable_one_add_abs_pow_mul_exp_neg_sq 0).indicator hSmeas
    rw [hsplit]
    have htail' : ∫ v in Sᶜ, (1 + |v|) ^ 0 * Real.exp (-(v ^ (2 : ℕ))) ≤
        Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(t / 2) ^ 2 / 2) * Real.sqrt (4 * Real.pi) := by
      simpa using htail
    gcongr
  have hexp : Real.exp (-(t / 2) ^ 2 / 2) = Real.exp (-(t ^ 2) / 8) := by
    congr 1; ring
  rw [hexp] at hgval
  have he := exp_neg_sq_div_eight_le ht
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, critCarrier t (-(((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)) *
        smoothAFEMellinIntegrand Y (((-rightAbscissa : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * (K' * Y ^ rightAbscissa * (Real.sqrt 2 / Real.sqrt t *
          Real.sqrt Real.pi + Real.exp ((0 : ℝ) ^ 2) * Real.exp (-(t ^ 2) / 8) *
            Real.sqrt (4 * Real.pi))) :=
        mul_le_mul_of_nonneg_left (hbound.trans hgval) (by positivity)
    _ ≤ 1 / (2 * Real.pi) * (K' * Y ^ rightAbscissa * (Real.sqrt 2 / Real.sqrt t *
          Real.sqrt Real.pi + 1 * (8 / Real.sqrt t) * Real.sqrt (4 * Real.pi))) := by
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, Real.exp_zero]
        gcongr
    _ = C * Y ^ rightAbscissa / Real.sqrt t := by
        rw [hCdef]
        field_simp

/-! ## The two diagonal main terms -/

/-- **Direct diagonal**: `Σ j^{−1} V(N j²/L) = ½ log(L/N) + O(1)` for `0 < N ≤ L`. -/
theorem exists_norm_directDiag_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N L : ℝ}, 0 < N → N ≤ L →
      ‖diagSum smoothAFECutoff N L - ((Real.log (L / N) / 2 : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  obtain ⟨K₂, hK₂, h₂⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1 / 4) (by norm_num)
  refine ⟨1 + 4 * max K₁ K₂, by positivity, fun {N L} hN hNL => ?_⟩
  apply norm_diagSum_sub_half_log_le (le_trans hK₁ (le_max_left _ _)) _ _ hN hNL
  · intro y hy
    refine (h₁ hy).trans ?_
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (le_max_left _ _) hy.le
  · intro y hy
    exact (h₂ hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

theorem direct_diagSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N L : ℝ}, 0 < N → 0 < L → ‖diagSum smoothAFECutoff N L‖ ≤ C * (L / N) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  refine ⟨2 * K₁, by positivity, fun {N L} hN hL => ?_⟩
  have h := norm_diagSum_le_of_lt (φ := smoothAFECutoff) hK₁ (fun y hy => by
    refine (h₁ hy).trans (le_of_eq ?_)
    rw [Real.rpow_neg_one, div_eq_mul_inv]) hN hL
  exact h

/-- The dual cutoff at height `t`: `z ↦ W_t(z t²)`. -/
def dualCutoff (t : ℝ) (z : ℝ) : ℂ := critDualWeight t (z * t ^ 2)

theorem exists_dualCutoff_bounds :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {t : ℝ}, 1 ≤ t →
      (∀ z > 0, ‖dualCutoff t z‖ ≤ A / z) ∧
        (∀ z > 0, ‖dualCutoff t z - 1‖ ≤ A * z ^ (1 / 4 : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_critDualWeight_le
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_critDualWeight_sub_one_le
  refine ⟨max (4 * C₁) C₂, by positivity, fun {t} ht => ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
  · have ht0 : 0 < t := by linarith
    have hY : 0 < z * t ^ 2 := by positivity
    refine (h₁ t hY).trans ?_
    have habs : (1 + |t|) ^ 2 ≤ 4 * t ^ 2 := by
      rw [abs_of_pos ht0]; nlinarith
    calc C₁ * (1 + |t|) ^ 2 / (z * t ^ 2) ≤ C₁ * (4 * t ^ 2) / (z * t ^ 2) := by gcongr
      _ = 4 * C₁ / z := by field_simp
      _ ≤ max (4 * C₁) C₂ / z := div_le_div_of_nonneg_right (le_max_left _ _) hz.le
  · have ht0 : 0 < t := by linarith
    have hY : 0 < z * t ^ 2 := by positivity
    refine (h₂ ht hY).trans ?_
    have hr : (z * t ^ 2) ^ rightAbscissa = z ^ (1 / 4 : ℝ) * Real.sqrt t := by
      rw [Real.mul_rpow hz.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
        Real.sqrt_eq_rpow]
      unfold rightAbscissa
      norm_num
    rw [hr]
    have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    calc C₂ * (z ^ (1 / 4 : ℝ) * Real.sqrt t) / Real.sqrt t = C₂ * z ^ (1 / 4 : ℝ) := by
          field_simp
      _ ≤ max (4 * C₁) C₂ * z ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem dualCutoff_arg {t N L : ℝ} (ht : t ≠ 0) (hL : 0 < L) (j : ℝ) :
    dualCutoff t (N * j ^ 2 / (t ^ 2 / L)) = critDualWeight t (N * j ^ 2 * L) := by
  unfold dualCutoff
  congr 1
  field_simp

/-- **Dual diagonal**: `Σ j^{−1} W_t(N j² L) = ½ log(t²/(NL)) + O(1)` for `0 < N ≤ t²/L`,
`t ≥ 1`. -/
theorem exists_norm_dualDiag_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t N L : ℝ}, 1 ≤ t → 0 < L → 0 < N → N ≤ t ^ 2 / L →
      ‖diagSum (dualCutoff t) N (t ^ 2 / L) - ((Real.log (t ^ 2 / L / N) / 2 : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨A, hA, hb⟩ := exists_dualCutoff_bounds
  refine ⟨1 + 4 * A, by positivity, fun {t N L} ht hL hN hNX => ?_⟩
  exact norm_diagSum_sub_half_log_le hA (hb ht).1 (hb ht).2 hN hNX

theorem dual_diagSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t N L : ℝ}, 1 ≤ t → 0 < L → 0 < N →
      ‖diagSum (dualCutoff t) N (t ^ 2 / L)‖ ≤ C * (t ^ 2 / L / N) := by
  obtain ⟨A, hA, hb⟩ := exists_dualCutoff_bounds
  refine ⟨2 * A, by positivity, fun {t N L} ht hL hN => ?_⟩
  have ht0 : 0 < t := by linarith
  exact norm_diagSum_le_of_lt hA (hb ht).1 hN (by positivity)

end RHTower.ZetaNotch
