import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicLowFrequency
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerSubpowerSchedule
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.HTGeometry.ReciprocalLogPowerTailGeneral
import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics

namespace RHTower.Sieve

open Finset Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- Polylogarithmic central disc, large enough to start all high-frequency estimates. -/
def menonHarmonicCentralRadius (x : ℝ) : ℝ := (Real.log x) ^ (2000 : ℕ)

theorem menonHarmonicCentralRadius_nonneg (x : ℝ) :
    0 ≤ menonHarmonicCentralRadius x := by
  rw [menonHarmonicCentralRadius]
  positivity

private theorem tendsto_menonHarmonicSourceLower_atTop :
    Tendsto (fun x : ℝ => ((⌈x⌉₊ - 1 : ℕ) : ℝ)) atTop atTop := by
  refine Filter.tendsto_atTop_mono' atTop ?_
    (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) tendsto_id)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceilOne : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.2 (by linarith)
  have hcast : (((⌈x⌉₊ - 1 : ℕ) : ℝ)) = (⌈x⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceilOne]
    norm_num
  rw [hcast]
  simp only [id_eq]
  linarith

private theorem eventually_sqrt_log_le_log_sourceLower :
    ∀ᶠ x : ℝ in atTop,
      Real.sqrt (Real.log x) ≤ Real.log (((⌈x⌉₊ - 1 : ℕ) : ℝ)) := by
  filter_upwards [eventually_ge_atTop (Real.exp 4)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  have hx4 : 4 ≤ x := by
    have he : (4 : ℝ) < Real.exp 4 := by
      have := Real.add_one_lt_exp (by norm_num : (4 : ℝ) ≠ 0)
      linarith
    linarith
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceilOne : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.2 hx0
  have hcast : (((⌈x⌉₊ - 1 : ℕ) : ℝ)) = (⌈x⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceilOne]
    norm_num
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrtSq : (Real.sqrt x) ^ 2 = x := (Real.sq_sqrt hx0.le)
  have hsqrtLe : Real.sqrt x ≤ x - 1 := by nlinarith
  have hsource : Real.sqrt x ≤ (((⌈x⌉₊ - 1 : ℕ) : ℝ)) := by
    rw [hcast]
    linarith
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlog := Real.log_le_log hsqrtPos hsource
  rw [Real.log_sqrt hx0.le] at hlog
  have hlogx : 4 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 4) hx
    simpa using this
  have hsqrtLog : Real.sqrt (Real.log x) ≤ Real.log x / 2 := by
    have hs0 := Real.sqrt_nonneg (Real.log x)
    have hsSq := Real.sq_sqrt (by linarith : 0 ≤ Real.log x)
    nlinarith
  exact hsqrtLog.trans hlog

private theorem eventually_menonHarmonicCentral_contour_admissible (K₀ : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      K₀ ≤ contourParam (⌈x⌉₊ : ℝ) ∧
      5 + 4 * (2 * Real.pi * menonHarmonicCentralRadius x) ≤
        ((contourParam (⌈x⌉₊ : ℝ) : ℕ) : ℝ) := by
  have hceilTop : Tendsto (fun x : ℝ => (⌈x⌉₊ : ℝ)) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards with x
    exact Nat.le_ceil x
  have hK := (tendsto_contourParam.comp hceilTop).eventually_ge_atTop K₀
  have hdomRaw : ∀ᶠ x : ℝ in atTop,
      (5 + 8 * Real.pi) * (Real.log x) ^ (2000 : ℝ) ≤
        Real.exp (1 * (Real.log x) ^ ((1 : ℝ) / 10)) :=
    Real.tendsto_log_atTop.eventually
      (eventually_mul_rpow_le_exp_rpow (5 + 8 * Real.pi)
        (c := (1 : ℝ)) (δ := (1 / 10 : ℝ)) (p := (2000 : ℝ))
        (by positivity) (by norm_num))
  have hdom : ∀ᶠ x : ℝ in atTop,
      (5 + 8 * Real.pi) * (Real.log x) ^ (2000 : ℝ) ≤
        Real.exp ((Real.log x) ^ ((1 : ℝ) / 10)) := by
    simpa only [one_mul] using hdomRaw
  filter_upwards [hK, hdom, eventually_ge_atTop (Real.exp 1)] with x hKx hdomx hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    simpa using this
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hpow1 : 1 ≤ (Real.log x) ^ (2000 : ℕ) := one_le_pow₀ hlog
  have hleft : 5 + 4 * (2 * Real.pi * menonHarmonicCentralRadius x) ≤
      (5 + 8 * Real.pi) * (Real.log x) ^ (2000 : ℝ) := by
    have hpEq : Real.log x ^ (2000 : ℕ) = Real.log x ^ (2000 : ℝ) :=
      (Real.rpow_natCast _ 2000).symm
    rw [menonHarmonicCentralRadius, hpEq]
    have hpow1' : 1 ≤ Real.log x ^ (2000 : ℝ) := by
      rw [← hpEq]
      exact hpow1
    have h5 : (5 : ℝ) ≤ 5 * Real.log x ^ (2000 : ℝ) :=
      calc
        (5 : ℝ) = 5 * 1 := by ring
        _ ≤ 5 * Real.log x ^ (2000 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow1' (by norm_num)
    calc
      5 + 4 * (2 * Real.pi * Real.log x ^ (2000 : ℝ)) =
          5 + 8 * Real.pi * Real.log x ^ (2000 : ℝ) := by ring
      _ ≤ 5 * Real.log x ^ (2000 : ℝ) +
            8 * Real.pi * Real.log x ^ (2000 : ℝ) :=
        by simpa only [add_comm] using
          add_le_add_right h5 (8 * Real.pi * Real.log x ^ (2000 : ℝ))
      _ = (5 + 8 * Real.pi) * Real.log x ^ (2000 : ℝ) := by ring
  have hlogCeil : Real.log x ≤ Real.log (⌈x⌉₊ : ℝ) :=
    Real.log_le_log hx0 (Nat.le_ceil x)
  have hrpow : (Real.log x) ^ ((1 : ℝ) / 10) ≤
      (Real.log (⌈x⌉₊ : ℝ)) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlog0 hlogCeil (by norm_num)
  have hKx' : K₀ ≤ contourParam (⌈x⌉₊ : ℝ) := by
    have hKcast : (K₀ : ℝ) ≤ (contourParam (⌈x⌉₊ : ℝ) : ℝ) := by
      simpa only [Function.comp_apply] using hKx
    exact_mod_cast hKcast
  refine ⟨hKx', hleft.trans (hdomx.trans ?_)⟩
  exact (Real.exp_le_exp.2 hrpow).trans contourParam_ge

/-- Menon's exact harmonic source shell has negligible central-disc energy. -/
theorem eventually_integral_central_normSq_menonFinalRangeShell_le_log_rpow_neg :
    ∀ᶠ x : ℝ in atTop,
      (∫ w in Set.Icc (-menonHarmonicCentralRadius x) (menonHarmonicCentralRadius x),
          ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ 2) ≤
        (Real.log x) ^ (-(80 : ℝ)) := by
  obtain ⟨K₀, N₁, hdisc⟩ :=
    exists_setIntegral_disc_normSq_logPoly_harmonicMoebiusC_Icc_le
  have hN := tendsto_menonHarmonicSourceLower_atTop.eventually_ge_atTop N₁
  have hcont := eventually_menonHarmonicCentral_contour_admissible K₀
  have hrel := tendsto_menonHarmonicSourceLower_atTop.eventually
    (eventually_relMoebiusSharp_le_log_rpow_neg (4000 : ℝ))
  have hlogLower := eventually_sqrt_log_le_log_sourceLower
  filter_upwards [hN, hcont, hrel, hlogLower,
    eventually_ge_atTop (Real.exp 4)] with x hNx hcontx hrelx hlogLowerx hx
  let a : ℕ := ⌈x⌉₊
  let b : ℕ := menonFinalRangeTopNat x
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  have hx1 : 1 < x := lt_of_lt_of_le
    (by simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (by norm_num : (0 : ℝ) < 4)) hx
  have ha : 1 ≤ a := by
    simp only [a]
    exact Nat.one_le_ceil_iff.2 hx0
  have hab : a ≤ b := by
    simp only [a, b, menonFinalRangeTopNat]
    apply Nat.le_floor
    have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
    linarith
  have hbase := hdisc a b (menonHarmonicCentralRadius x) ha hab
    (menonHarmonicCentralRadius_nonneg x) hNx hcontx.1 hcontx.2
  have hshell : menonFinalRangeShell x = Finset.Icc a b := by
    rfl
  rw [hshell]
  refine hbase.trans ?_
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hceil : x ≤ (a : ℝ) := by
    simp only [a]
    exact Nat.le_ceil x
  have hb : (b : ℝ) ≤ 3 * x := by
    simp only [b, menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have haminus : (((a - 1 : ℕ) : ℝ)) ≤ (a : ℝ) := by exact_mod_cast (Nat.sub_le a 1)
  have hfactor : ((((a - 1 : ℕ) : ℝ) + (b : ℝ)) /
      (a : ℝ)) ≤ 4 := by
    rw [div_le_iff₀ haR]
    nlinarith
  have hsource0 : 0 < (((a - 1 : ℕ) : ℝ)) := by
    have hlarge : (2 : ℝ) < x := lt_of_lt_of_le
      (by nlinarith [Real.exp_pos 4, Real.add_one_lt_exp (by norm_num : (4 : ℝ) ≠ 0)]) hx
    have haTwo : 2 ≤ a := by
      have hceilA : x ≤ (a : ℝ) := by
        simp only [a]
        exact Nat.le_ceil x
      have haReal : (1 : ℝ) < (a : ℝ) := lt_trans (by norm_num) (hlarge.trans_le hceilA)
      exact_mod_cast haReal
    exact_mod_cast (by omega : 0 < a - 1)
  have hrel0 := relMoebiusSharp_nonneg hsource0
  have hU : (((((a - 1 : ℕ) : ℝ) + (b : ℝ)) *
      relMoebiusSharp (((a - 1 : ℕ) : ℝ))) / (a : ℝ)) ≤
      4 * relMoebiusSharp (((a - 1 : ℕ) : ℝ)) := by
    calc
      ((((a - 1 : ℕ) : ℝ) + (b : ℝ)) *
          relMoebiusSharp (((a - 1 : ℕ) : ℝ))) / (a : ℝ) =
          ((((a - 1 : ℕ) : ℝ) + (b : ℝ)) / (a : ℝ)) *
            relMoebiusSharp (((a - 1 : ℕ) : ℝ)) := by ring
      _ ≤ 4 * relMoebiusSharp (((a - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactor hrel0
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlogx
  have hneg : (Real.log (((a - 1 : ℕ) : ℝ))) ^ (-(4000 : ℝ)) ≤
      (Real.sqrt (Real.log x)) ^ (-(4000 : ℝ)) := by
    rw [Real.rpow_neg (lt_of_lt_of_le hsqrtLogPos hlogLowerx).le,
      Real.rpow_neg hsqrtLogPos.le]
    simpa [one_div] using one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hsqrtLogPos (4000 : ℝ))
      (Real.rpow_le_rpow hsqrtLogPos.le hlogLowerx (by norm_num))
  have hsqrtPow : (Real.sqrt (Real.log x)) ^ (-(4000 : ℝ)) =
      (Real.log x) ^ (-(2000 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogx.le]
    congr 1
    ring
  have hrelFinal : relMoebiusSharp (((a - 1 : ℕ) : ℝ)) ≤
      (Real.log x) ^ (-(2000 : ℝ)) := by
    exact hrelx.trans (hneg.trans_eq hsqrtPow)
  have hpowLog0 : 0 ≤ (Real.log x) ^ (-(2000 : ℝ)) := Real.rpow_nonneg hlogx.le _
  have hUsq : (((((a - 1 : ℕ) : ℝ) + (b : ℝ)) *
        relMoebiusSharp (((a - 1 : ℕ) : ℝ))) / (a : ℝ)) ^ 2 ≤
      (4 * (Real.log x) ^ (-(2000 : ℝ))) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (hU.trans
      (mul_le_mul_of_nonneg_left hrelFinal (by norm_num))) 2
  have hrad : menonHarmonicCentralRadius x = (Real.log x) ^ (2000 : ℝ) := by
    rw [menonHarmonicCentralRadius]
    exact (Real.rpow_natCast _ 2000).symm
  rw [hrad]
  calc
    (((((a - 1 : ℕ) : ℝ) + (b : ℝ)) *
          relMoebiusSharp (((a - 1 : ℕ) : ℝ))) / (a : ℝ)) ^ 2 *
        (2 * (Real.log x) ^ (2000 : ℝ))
      ≤ (4 * (Real.log x) ^ (-(2000 : ℝ))) ^ 2 *
          (2 * (Real.log x) ^ (2000 : ℝ)) :=
        mul_le_mul_of_nonneg_right hUsq (by positivity)
    _ = 32 * (Real.log x) ^ (-(2000 : ℝ)) := by
      calc
        (4 * (Real.log x) ^ (-(2000 : ℝ))) ^ 2 *
            (2 * (Real.log x) ^ (2000 : ℝ)) =
            32 * (((Real.log x) ^ (-(2000 : ℝ)) *
              (Real.log x) ^ (-(2000 : ℝ))) *
                (Real.log x) ^ (2000 : ℝ)) := by ring
        _ = 32 * (Real.log x) ^ (-(2000 : ℝ)) := by
          rw [← Real.rpow_add hlogx, ← Real.rpow_add hlogx]
          norm_num
    _ ≤ (Real.log x) ^ (-(80 : ℝ)) := by
      have hlog4 : 4 ≤ Real.log x := by
        have := Real.log_le_log (Real.exp_pos 4) hx
        simpa using this
      have hpow1920 : 32 ≤ (Real.log x) ^ (1920 : ℝ) := by
        have hbase : (2 : ℝ) ≤ Real.log x := by linarith
        calc
          (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
          _ ≤ (Real.log x) ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hbase 5
          _ ≤ (Real.log x) ^ (1920 : ℕ) := by
            exact pow_le_pow_right₀ (by linarith) (by omega)
          _ = (Real.log x) ^ (1920 : ℝ) := (Real.rpow_natCast _ 1920).symm
      calc
        32 * (Real.log x) ^ (-(2000 : ℝ)) ≤
            (Real.log x) ^ (1920 : ℝ) * (Real.log x) ^ (-(2000 : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow1920 (Real.rpow_nonneg hlogx.le _)
        _ = (Real.log x) ^ (-(80 : ℝ)) := by
          rw [← Real.rpow_add hlogx]
          norm_num

end

end RHTower.Sieve
