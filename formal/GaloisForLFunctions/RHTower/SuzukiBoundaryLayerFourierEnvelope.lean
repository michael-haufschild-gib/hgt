import GaloisForLFunctions.RHTower.SuzukiHlogDenseFormCore
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower


def testEnvelope (n : ℕ) (M ξ : ℝ) : ℝ :=
  Real.log (3 + |ξ|) *
    min (2 / ((n : ℝ) + 1)) (|M| / |ξ|) ^ 2

def testDom (M ξ : ℝ) : ℝ :=
  (64 * (1 + M ^ 2)) * (1 + |ξ|) ^ (-(3 / 2 : ℝ))

theorem log_three_add_le_four_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log (3 + x) ≤ 4 * x ^ (1 / 2 : ℝ) := by
  have hlog := Real.log_le_rpow_div (show 0 ≤ 3 + x by linarith) (show 0 < (1 / 2 : ℝ) by norm_num)
  have hbase : 3 + x ≤ 4 * x := by linarith
  have hrpow : (3 + x) ^ (1 / 2 : ℝ) ≤ (4 * x) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hbase (by norm_num)
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hfour : (4 * x) ^ (1 / 2 : ℝ) = 2 * x ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hx0]
    norm_num [← Real.rpow_natCast]
  rw [div_eq_mul_inv] at hlog
  norm_num at hlog
  nlinarith

theorem testDom_integrable (M : ℝ) : Integrable (testDom M) := by
  unfold testDom
  exact (integrable_one_add_norm (E := ℝ) (μ := volume)
    (show (Module.finrank ℝ ℝ : ℝ) < (3 / 2 : ℝ) by norm_num)).const_mul _

theorem rpow_two_three_halves_le_four :
    (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem one_fourth_le_one_add_rpow_neg_three_halves {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 / 4 : ℝ) ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have hpow : (1 + x) ^ (3 / 2 : ℝ) ≤ 4 := by
    exact (Real.rpow_le_rpow (by positivity) (by linarith)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans rpow_two_three_halves_le_four
  rw [Real.rpow_neg (by positivity)]
  rw [show (1 / 4 : ℝ) = 1 / (4 : ℝ) by norm_num]
  have hden : 0 < (1 + x) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [show ((1 + x) ^ (3 / 2 : ℝ))⁻¹ =
    1 * ((1 + x) ^ (3 / 2 : ℝ))⁻¹ by simp, le_mul_inv_iff₀ hden]
  nlinarith

theorem one_fourth_mul_x_rpow_le_one_add_rpow_neg_three_halves {x : ℝ}
    (hx : 1 ≤ x) :
    (1 / 4 : ℝ) * x ^ (-(3 / 2 : ℝ)) ≤
      (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hbase : 1 + x ≤ 2 * x := by linarith
  have hpow : (1 + x) ^ (3 / 2 : ℝ) ≤ 4 * x ^ (3 / 2 : ℝ) := by
    calc
      (1 + x) ^ (3 / 2 : ℝ) ≤ (2 * x) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = 2 ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) := by rw [Real.mul_rpow (by norm_num) hx0]
      _ ≤ 4 * x ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right rpow_two_three_halves_le_four (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  have hp : 0 < x ^ (3 / 2 : ℝ) := by positivity
  have hq : 0 < (1 + x) ^ (3 / 2 : ℝ) := by positivity
  rw [show ((1 + x) ^ (3 / 2 : ℝ))⁻¹ =
    1 * ((1 + x) ^ (3 / 2 : ℝ))⁻¹ by simp, le_mul_inv_iff₀ hq]
  calc
    1 / 4 * (x ^ (3 / 2 : ℝ))⁻¹ * (1 + x) ^ (3 / 2 : ℝ)
        ≤ 1 / 4 * (x ^ (3 / 2 : ℝ))⁻¹ * (4 * x ^ (3 / 2 : ℝ)) := by
          gcongr
    _ = 1 := by field_simp

theorem sqrt_mul_div_sq_eq_rpow_neg_three_halves {x : ℝ} (hx : 0 < x) (M : ℝ) :
    x ^ (1 / 2 : ℝ) * (|M| / x) ^ 2 =
      M ^ 2 * x ^ (-(3 / 2 : ℝ)) := by
  have hs : x ^ (1 / 2 : ℝ) = √x := by rw [Real.sqrt_eq_rpow]
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx
  have hs_sq : (√x) ^ 2 = x := Real.sq_sqrt hx.le
  have hthree : x ^ (3 / 2 : ℝ) = x * √x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx, Real.rpow_one, hs]
  rw [Real.rpow_neg hx.le, hthree, hs]
  rw [div_pow, sq_abs]
  field_simp
  nlinarith

theorem norm_testEnvelope_le_testDom (n : ℕ) (M ξ : ℝ) :
    ‖testEnvelope n M ξ‖ ≤ testDom M ξ := by
  let x : ℝ := |ξ|
  have hx0 : 0 ≤ x := abs_nonneg ξ
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hsmall0 : 0 ≤ 2 / ((n : ℝ) + 1) := div_nonneg (by norm_num) (by positivity)
  have hsmall2 : 2 / ((n : ℝ) + 1) ≤ 2 := by
    exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have htail0 : 0 ≤ |M| / x := div_nonneg (abs_nonneg M) hx0
  have hmin0 : 0 ≤ min (2 / ((n : ℝ) + 1)) (|M| / x) := le_min hsmall0 htail0
  have hlog0 : 0 ≤ Real.log (3 + x) := Real.log_nonneg (by linarith)
  have henv0 : 0 ≤ testEnvelope n M ξ := by
    unfold testEnvelope
    simpa [x] using mul_nonneg hlog0 (sq_nonneg (min (2 / ((n : ℝ) + 1)) (|M| / x)))
  rw [Real.norm_eq_abs, abs_of_nonneg henv0]
  change testEnvelope n M ξ ≤ testDom M ξ
  unfold testEnvelope testDom
  change Real.log (3 + x) * min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2 ≤
    64 * (1 + M ^ 2) * (1 + x) ^ (-(3 / 2 : ℝ))
  rcases le_or_gt x 1 with hx1 | hx1
  · have hlog : Real.log (3 + x) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 3 + x by linarith)
      nlinarith
    have hmin : min (2 / ((n : ℝ) + 1)) (|M| / x) ≤ 2 :=
      (min_le_left _ _).trans hsmall2
    have hsq : min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2 ≤ 4 := by nlinarith
    have hleft : Real.log (3 + x) *
        min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2 ≤ 16 := by nlinarith
    have hbracket := one_fourth_le_one_add_rpow_neg_three_halves hx0 hx1
    have hM : 0 ≤ M ^ 2 := sq_nonneg M
    calc
      Real.log (3 + x) * min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2 ≤ 16 := hleft
      _ ≤ 64 * (1 + M ^ 2) * (1 + x) ^ (-(3 / 2 : ℝ)) := by nlinarith
  · have hx : 1 ≤ x := hx1.le
    have hxpos : 0 < x := lt_trans zero_lt_one hx1
    have hmin : min (2 / ((n : ℝ) + 1)) (|M| / x) ≤ |M| / x := min_le_right _ _
    have hsq : min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2 ≤ (|M| / x) ^ 2 := by
      nlinarith
    have hlog := log_three_add_le_four_sqrt hx
    have htailnonneg : 0 ≤ (|M| / x) ^ 2 := sq_nonneg _
    have hleft : Real.log (3 + x) *
        min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2 ≤
        4 * M ^ 2 * x ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.log (3 + x) * min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2
            ≤ Real.log (3 + x) * (|M| / x) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq hlog0
        _ ≤ (4 * x ^ (1 / 2 : ℝ)) * (|M| / x) ^ 2 :=
              mul_le_mul_of_nonneg_right hlog htailnonneg
        _ = 4 * M ^ 2 * x ^ (-(3 / 2 : ℝ)) := by
              rw [mul_assoc, sqrt_mul_div_sq_eq_rpow_neg_three_halves hxpos M]
              ring
    have hbracket := one_fourth_mul_x_rpow_le_one_add_rpow_neg_three_halves hx
    have hxpow0 : 0 ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx0 _
    have hM : 0 ≤ M ^ 2 := sq_nonneg M
    calc
      Real.log (3 + x) * min (2 / ((n : ℝ) + 1)) (|M| / x) ^ 2
          ≤ 4 * M ^ 2 * x ^ (-(3 / 2 : ℝ)) := hleft
      _ ≤ 64 * (1 + M ^ 2) * (1 + x) ^ (-(3 / 2 : ℝ)) := by nlinarith

theorem measurable_testEnvelope (n : ℕ) (M : ℝ) : Measurable (testEnvelope n M) := by
  unfold testEnvelope
  fun_prop

theorem tendsto_testEnvelope_pointwise (M ξ : ℝ) :
    Tendsto (fun n : ℕ => testEnvelope n M ξ) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
          Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * 0)))
  have htail : 0 ≤ |M| / |ξ| := div_nonneg (abs_nonneg M) (abs_nonneg ξ)
  have hmin : Tendsto
      (fun n : ℕ => min (2 / ((n : ℝ) + 1)) (|M| / |ξ|)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => |M| / |ξ|) atTop (𝓝 (|M| / |ξ|)) :=
      tendsto_const_nhds
    simpa only [min_eq_left htail] using hsmall.min hconst
  unfold testEnvelope
  convert tendsto_const_nhds.mul (hmin.pow 2) using 1 <;> simp

/-- Suzuki's boundary-layer envelope has vanishing logarithmically weighted energy.  This is the
analytic core of source equations (3.3)--(3.4): simultaneous `2ε` and `M / |ξ|` Fourier bounds
force the full weighted energy to zero. -/
theorem tendsto_integral_testEnvelope (M : ℝ) :
    Tendsto (fun n : ℕ => ∫ ξ : ℝ, testEnvelope n M ξ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (testDom M)
    (fun n => (measurable_testEnvelope n M).aestronglyMeasurable)
    (testDom_integrable M)
    (fun n => ae_of_all _ fun ξ => norm_testEnvelope_le_testDom n M ξ)
    (ae_of_all _ fun ξ => tendsto_testEnvelope_pointwise M ξ)
  simpa using h

end RHTower

