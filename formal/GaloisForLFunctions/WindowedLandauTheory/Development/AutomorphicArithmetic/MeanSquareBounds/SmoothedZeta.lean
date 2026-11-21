import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound
import GaloisForLFunctions.RHTower.PowerLagLandauSeries
import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheExplicitFormulaForACharacter
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic
import GaloisForLFunctions.WindowedLandauTheory.ZeroFreeRegion.NativeZeroFreeRegion

/-! The centered principal Cesàro sum from the smoothed zeta explicit formula. -/

open Complex Finset RHTower WindowedLandauTheory.HC
open ArithmeticFunction (vonMangoldt)

namespace QH

private theorem zeta_smoothed_identity {y : ℝ} (hy : 1 < y) :
    (An.G y : ℂ) = lagZeroSum y + (Real.log (2 * Real.pi) : ℂ) - trivialZeroSeries y := by
  have hψ : Chebyshev.psi y = ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
    simp [Icc_one_eq_Ioc_zero]
  have hsum : (∑ n ∈ Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0) =
      y * (∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / (n : ℝ)) - Chebyshev.psi y := by
    rw [hψ, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn₁
    have hny := (show (n : ℝ) ≤ ⌊y⌋₊ by exact_mod_cast hn₂).trans (Nat.floor_le (by linarith))
    rw [max_eq_left (sub_nonneg.mpr ((le_div_iff₀ hn₀).mpr (by simpa using hny)))]
    simp only [An.abelian₂]
    ring
  rw [An.G, hsum, lagZeroSum, lag_explicit_formula hy]
  push_cast
  ring

theorem smoothed_zeta_bound : ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ y : ℝ, Real.exp 1 ≤ y →
    ‖(An.G y : ℂ)‖ ≤ K * y * Real.exp (-k * Real.sqrt (Real.log y)) := by
  obtain ⟨c, hc, hz⟩ := WindowedLandauTheory.ZF.zeroFreeRegion
  let M := ∑' q : XiZeroCopy, ‖lagWeight q‖ * Real.sqrt (2 + |zeroOrdinate q|)
  let L := |Real.log (2 * Real.pi)|
  let k := min c (1 / 2)
  have hk : 0 < k := lt_min hc (by norm_num)
  have hM : 0 ≤ M := tsum_nonneg fun _ => by positivity
  refine ⟨M + L + 2, k, by positivity, hk, fun y hy => ?_⟩
  have hy₀ : 0 < y := (Real.exp_pos _).trans_le hy
  have hy₁ : 1 < y := (Real.one_lt_exp_iff.mpr one_pos).trans_le hy
  set v := Real.log y with hv
  have hv₁ : 1 ≤ v := (Real.le_log_iff_exp_le hy₀).mpr hy
  set s := Real.sqrt v with hs
  have hs₁ : 1 ≤ s := Real.one_le_sqrt.mpr hv₁
  have hs₀ : 0 < s := zero_lt_one.trans_le hs₁
  have hss : s * s = v := Real.mul_self_sqrt (zero_le_one.trans hv₁)
  set A := Real.exp (-k * s) with hA
  have hA₀ : 0 < A := Real.exp_pos _
  have hA₁ : 1 ≤ y * A := by
    have hys : y = Real.exp v := (Real.exp_log hy₀).symm
    rw [hys, hA, ← Real.exp_add]
    apply Real.one_le_exp
    have hks : k * s ≤ s := mul_le_of_le_one_left hs₀.le ((min_le_right _ _).trans (by norm_num))
    have hsv : s ≤ v := by rw [← hss]; exact le_mul_of_one_le_right hs₀.le hs₁
    linarith only [hks, hsv]
  have hterm (q : XiZeroCopy) :
      ‖(y : ℂ) ^ ((q.1 : ℂ) - 1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
        A * (‖lagWeight q‖ * Real.sqrt (2 + |zeroOrdinate q|)) := by
    let ρ : ℂ := q.1
    have hρ₁ := xiZeroCopy_re_lt_one q
    have hρ : ρ ≠ 1 := fun e => by rw [show (q.1 : ℂ) = ρ from rfl, e, Complex.one_re] at hρ₁; exact (lt_irrefl _ hρ₁)
    have hzero := riemannZeta_eq_zero_of_xiZeroCopy q
    have hg : ρ.re < 1 - c / Real.log (|ρ.im| + 2) := lt_of_not_ge fun h => hz ρ hρ h hzero
    have hγ : 0 < Real.log (2 + |ρ.im|) := Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hcq : y ^ (ρ.re - 1) ≤ A * Real.sqrt (2 + |ρ.im|) := by
      rcases le_or_gt (Real.log (2 + |ρ.im|)) s with hl | hl
      · have hcs : c / s ≤ c / Real.log (2 + |ρ.im|) := div_le_div_of_nonneg_left hc.le hγ hl
        have hkv : k * s ≤ (c / s) * v := by
          calc k * s ≤ c * s := mul_le_mul_of_nonneg_right (min_le_left _ _) hs₀.le
            _ = (c / s) * v := by rw [← hss]; field_simp [hs₀.ne']
        have hude : y ^ (ρ.re - 1) ≤ A := by
          rw [Real.rpow_def_of_pos hy₀, hA]
          apply Real.exp_le_exp.mpr
          have h := mul_le_mul_of_nonneg_left hcs (zero_le_one.trans hv₁)
          rw [add_comm 2] at h
          have hh := mul_le_mul_of_nonneg_left hg.le (zero_le_one.trans hv₁)
          linarith only [hh, h, hkv]
        have hone : 1 ≤ Real.sqrt (2 + |ρ.im|) := Real.one_le_sqrt.mpr (by linarith [abs_nonneg ρ.im])
        exact hude.trans (le_mul_of_one_le_right hA₀.le hone)
      · have hv' : y ^ (ρ.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy₁.le (sub_nonpos.mpr hρ₁.le)
        have hpos : 0 < 2 + |ρ.im| := by positivity
        have hroot : Real.sqrt (2 + |ρ.im|) = Real.exp (Real.log (2 + |ρ.im|) / 2) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
          congr 1
          ring
        have hks : k * s ≤ s / 2 := by
          linarith only [mul_le_mul_of_nonneg_right (min_le_right c (1 / 2)) hs₀.le]
        rw [hroot, hA, ← Real.exp_add]
        exact hv'.trans (Real.one_le_exp (by linarith only [hl.le, hks]))
    rw [div_eq_mul_one_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy₀, Complex.sub_re, Complex.one_re]
    change y ^ (ρ.re - 1) * ‖lagWeight q‖ ≤ A * (‖lagWeight q‖ * Real.sqrt (2 + |ρ.im|))
    rw [mul_left_comm A, mul_comm (y ^ (ρ.re - 1))]
    exact mul_le_mul_of_nonneg_left hcq (norm_nonneg _)
  have hsZ := summable_lagWeight_mul_sqrt.mul_left A
  have hn := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsZ
  have hZ : ‖lagZeroSum y / (y : ℂ)‖ ≤ A * M := by
    rw [lagZeroSum_div_eq hy₁.le, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hterm hsZ)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hy₀.le, div_le_iff₀ hy₀] at hZ
  have htriv : ‖trivialZeroSeries y‖ ≤ 2 := by
    have hs := (summable_trivialZeroSeriesTerm hy₁.le).norm
    have hb : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
      exact_mod_cast (summable_nat_add_iff 1).mpr h
    refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum (norm_trivialZeroSeriesTerm_le hy₁.le) hb).trans ?_)
    exact GaloisForLFunctions.ShortIntervalPrimesInProgressions.efD_le_two
  rw [zeta_smoothed_identity hy₁]
  have hL : ‖(Real.log (2 * Real.pi) : ℂ)‖ = L := by rw [Complex.norm_real, Real.norm_eq_abs]
  calc ‖lagZeroSum y + (Real.log (2 * Real.pi) : ℂ) - trivialZeroSeries y‖
      ≤ ‖lagZeroSum y‖ + ‖(Real.log (2 * Real.pi) : ℂ)‖ + ‖trivialZeroSeries y‖ :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (A * M) * y + L + 2 := by rw [hL]; linarith only [hZ, htriv]
    _ ≤ (M + L + 2) * y * A := by
      have h := le_mul_of_one_le_right (show 0 ≤ L + 2 by positivity) hA₁
      linarith only [h]

end QH
