import GaloisForLFunctions.BezoutValuationIncidence.UniformCancellationInTheUndampedVaughanConvolution
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicEnergyFromPrefixCancellation
import GaloisForLFunctions.BezoutValuationIncidence.TheExtremeVaughanCutoffReadsItsHarmonicSum
import GaloisForLFunctions.RHTower.MertensPowerBoundsControlMobiusHarmonicSums
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
Uniform power cancellation in the actual undamped Vaughan convolution is
equivalent to a fixed zero-free strip. Balancing cutoff rounding and the
Mertens tail transfers every gain below the explicit ratio η/(2+η).
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- At the unit/full cutoff pair the undamped convolution prefix is exactly one. -/
theorem pmUndampedVaughanConvolutionPrefix_one_full {n : ℕ} (hn : 1 ≤ n) :
    pmUndampedVaughanConvolutionPrefix 1 n n = 1 := by
  rw [pmUndampedVaughanConvolutionPrefix_eq_rectangle]
  have hm : moebiusReal 1 = 1 := by simp [moebiusReal]
  simp only [Icc_self, sum_singleton, hm, one_mul, Nat.one_mul]
  simpa only [moebiusReal] using moebius_floor_summatory n hn

/-- Balancing floor rounding and the Mertens tail transfers every gain below `η/(2+η)`. -/
theorem exists_uniform_pmUndampedVaughan_power_of_mertens_power {η κ B : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hκη : κ < η / (2 + η)) (hB : 0 ≤ B)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ B * (n : ℝ) ^ (1 - η)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          C * (n : ℝ) ^ (1 - κ) := by
  let a : ℝ := 1 / (2 + η)
  let BH : ℝ := B * (1 + 1 / η)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hBH : 0 ≤ BH := by dsimp only [BH]; positivity
  have hopt : a * η = η / (2 + η) := by dsimp only [a]; ring
  have hbalance : 1 - 2 * a = a * η := by
    dsimp only [a]
    field_simp [(show (2 : ℝ) + η ≠ 0 by positivity)] <;> ring
  have hκtail : 0 < a * η - κ := sub_pos.mpr (by rw [hopt]; exact hκη)
  have hκhead : 2 * a ≤ 1 - κ := by linarith only [hκtail, hbalance]
  have ha1 : a ≤ 1 := by linarith only [hκhead, hκ]
  have hH (n : ℕ) (hn : 1 ≤ n) :
      |deningerHarmonicPartial n| ≤ BH * (n : ℝ) ^ (-η) := by
    apply abs_deningerHarmonicPartial_le_of_mertens_power hη hB
      (fun k hk => ?_) hn
    rw [← sum_Icc_moebiusReal_eq_mertensM]
    exact hM k hk
  let D : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ a⌋₊
  have hDlim : Tendsto D atTop atTop := tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogPower : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (a * η - κ) := by
    have h := eventually_log_pow_le_sqrt_rpow 2
      (β := 2 * (a * η - κ)) (by positivity)
    simpa only [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _),
      show 2 * (a * η - κ) * (1 / 2 : ℝ) = a * η - κ by ring] using h
  refine ⟨2 + 2 ^ η * (11 * B + BH), by positivity, ?_⟩
  filter_upwards [hDlim.eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1,
    hlogPower, eventually_ge_atTop 1] with n hD1 hlog1 hlogPower hn U V
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD0 : (0 : ℝ) < D n := by exact_mod_cast hD1
  have hDn : D n ≤ n := by
    apply Nat.floor_le_of_le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 ha1
  have hlogD : a * Real.log (n : ℝ) - Real.log 2 ≤ Real.log (D n : ℝ) :=
    CubicGamma.log_floor_rpow_ge hn1 ha.le
  have hDpower : (D n : ℝ) ^ (-η) ≤ (2 : ℝ) ^ η * (n : ℝ) ^ (-a * η) := by
    rw [Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hn0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_right hlogD (neg_nonpos.mpr hη.le)
    exact h.trans_eq (by ring)
  have hMtail (x : ℕ) (hx : D n ≤ x) :
      |∑ d ∈ Icc 1 x, moebiusReal d| ≤ (B * (D n : ℝ) ^ (-η)) * x := by
    have hx1 : 1 ≤ x := hD1.trans hx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    calc
      _ ≤ B * (x : ℝ) ^ (1 - η) := hM x hx1
      _ = (B * (x : ℝ) ^ (-η)) * x := by
        rw [show 1 - η = -η + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hD0
          (by exact_mod_cast hx) (neg_nonpos.mpr hη.le)) hB) hx0.le
  have hHtail (x : ℕ) (hx : D n ≤ x) :
      |deningerHarmonicPartial x| ≤ BH * (D n : ℝ) ^ (-η) :=
    (hH x (hD1.trans hx)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hD0 (by exact_mod_cast hx) (neg_nonpos.mpr hη.le)) hBH)
  have hfinite := abs_pmUndampedVaughanConvolutionPrefix_sub_mean_le_uniform
    (by positivity : 0 ≤ B * (D n : ℝ) ^ (-η))
    (by positivity : 0 ≤ BH * (D n : ℝ) ^ (-η)) hDn hMtail hHtail U V
  have hhead : (D n : ℝ) ^ 2 + D n ≤ 2 * (n : ℝ) ^ (1 - κ) := by
    have hfloor : (D n : ℝ) ≤ (n : ℝ) ^ a := Nat.floor_le (Real.rpow_nonneg hn0.le _)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (D n)) hfloor 2
    have heq : ((n : ℝ) ^ a) ^ 2 = (n : ℝ) ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      norm_num [mul_comm]
    rw [heq] at hsq
    have hsingle := hfloor.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [ha] : a ≤ 2 * a))
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hκhead
    linarith only [hsq, hsingle, hpow]
  have hHarmonic : (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by
    have hs := Sieve.sum_Icc_one_div_le_one_add_log n
    have hh : (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      linarith only [hs, hlog1]
    have hnH : 0 ≤ ∑ k ∈ Icc 1 n, 1 / (k : ℝ) := sum_nonneg fun k _ => by positivity
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using pow_le_pow_left₀ hnH hh 2
  have hlog2 : 1 ≤ Real.log (n : ℝ) ^ 2 := one_le_pow₀ hlog1
  have htail0 : 3 * (B * (D n : ℝ) ^ (-η)) * n +
      2 * (B * (D n : ℝ) ^ (-η)) * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 +
        (BH * (D n : ℝ) ^ (-η)) * n ≤
          (11 * B + BH) * (D n : ℝ) ^ (-η) * n * Real.log (n : ℝ) ^ 2 := by
    have hfirst := mul_le_mul_of_nonneg_left hlog2
      (by positivity : 0 ≤ 3 * B * (D n : ℝ) ^ (-η) * n)
    have hmiddle := mul_le_mul_of_nonneg_left hHarmonic
      (by positivity : 0 ≤ 2 * B * (D n : ℝ) ^ (-η) * n)
    have hlast := mul_le_mul_of_nonneg_left hlog2
      (by positivity : 0 ≤ BH * (D n : ℝ) ^ (-η) * n)
    nlinarith only [hfirst, hmiddle, hlast]
  have hpowerProduct : (n : ℝ) ^ (-a * η) * n * (n : ℝ) ^ (a * η - κ) =
      (n : ℝ) ^ (1 - κ) := by
    calc
      _ = ((n : ℝ) ^ (-a * η) * (n : ℝ) ^ (1 : ℝ)) * (n : ℝ) ^ (a * η - κ) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
        congr 1
        ring
  have htail : (11 * B + BH) * (D n : ℝ) ^ (-η) * n * Real.log (n : ℝ) ^ 2 ≤
      (2 ^ η * (11 * B + BH)) * (n : ℝ) ^ (1 - κ) := by
    calc
      _ ≤ (11 * B + BH) * ((2 : ℝ) ^ η * (n : ℝ) ^ (-a * η)) * n *
          (n : ℝ) ^ (a * η - κ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDpower (by positivity)) hn0.le)
          hlogPower (sq_nonneg _) (by positivity)
      _ = (2 ^ η * (11 * B + BH)) *
          ((n : ℝ) ^ (-a * η) * n * (n : ℝ) ^ (a * η - κ)) := by ring
      _ = _ := by rw [hpowerProduct]
  have htotal := add_le_add hhead (htail0.trans htail)
  refine hfinite.trans ?_
  convert htotal using 1 <;> ring

/-- An eventual uniform power bound already forces a strip through the unit/full cutoff pair. -/
theorem zetaZeroAbscissa_lt_one_of_uniform_pmUndampedVaughan_power {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (h : ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          C * (n : ℝ) ^ (1 - δ)) : zetaZeroAbscissa < 1 := by
  let η : ℝ := min δ (1 / 2)
  have hη : 0 < η := lt_min hδ (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηδ : η ≤ δ := min_le_left _ _
  have hHone : deningerHarmonicPartial 1 = 1 := by
    rw [deningerHarmonicPartial_eq_sum_Icc]
    simp
  have hevent : ∀ᶠ n : ℕ in atTop,
      |deningerHarmonicPartial n| ≤ (1 + C) * (n : ℝ) ^ (-η) := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have herror := hn 1 n
    rw [pmUndampedVaughanConvolutionPrefix_one_full hn1, hHone, mul_one] at herror
    have htriangle : (n : ℝ) * |deningerHarmonicPartial n| ≤
        1 + |1 - (n : ℝ) * deningerHarmonicPartial n| := by
      have ht := abs_sub (1 : ℝ) (1 - (n : ℝ) * deningerHarmonicPartial n)
      rw [show (1 : ℝ) - (1 - (n : ℝ) * deningerHarmonicPartial n) =
        (n : ℝ) * deningerHarmonicPartial n by ring,
        abs_mul, abs_of_pos hn0, abs_one] at ht
      exact ht
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1r
      (by linarith only [hηδ] : 1 - δ ≤ 1 - η)
    have hone : 1 ≤ (n : ℝ) ^ (1 - η) := Real.one_le_rpow hn1r (sub_pos.mpr hη1).le
    have hlarge : (n : ℝ) * |deningerHarmonicPartial n| ≤ (1 + C) * (n : ℝ) ^ (1 - η) :=
      (htriangle.trans (add_le_add le_rfl herror)).trans
        ((add_le_add hone (mul_le_mul_of_nonneg_left hpow hC)).trans_eq (by ring))
    have hdiv : |deningerHarmonicPartial n| ≤
        ((1 + C) * (n : ℝ) ^ (1 - η)) / n :=
      (le_div_iff₀ hn0).mpr (by simpa only [mul_comm] using hlarge)
    refine hdiv.trans_eq ?_
    rw [show 1 - η = -η + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    field_simp [hn0.ne']
  have hlinear (_a : Unit) (n : ℕ) (hn : 1 ≤ n) :
      |deningerHarmonicPartial n| ≤ (1 : ℝ) * n := by
    simpa only [one_mul] using (abs_deningerHarmonicPartial_le_one n).trans
      (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have hevent' : ∀ᶠ n : ℕ in atTop, ∀ _a : Unit,
      |deningerHarmonicPartial n| ≤ (1 + C) * (n : ℝ) ^ (1 - (1 + η)) := by
    filter_upwards [hevent] with n hn _a
    simpa only [show 1 - (1 + η) = -η by ring] using hn
  obtain ⟨K, hK, hglobal⟩ := exists_uniform_rpow_bound_of_eventually
    (f := fun _a : Unit => deningerHarmonicPartial) (ε := 1 + η)
    (by positivity) (by norm_num) (by positivity) hlinear hevent'
  apply zetaZeroAbscissa_lt_one_of_harmonic_power hη hη1 hK
  intro n hn
  simpa only [show 1 - (1 + η) = -η by ring] using hglobal () n hn

/-- Uniform power cancellation in the actual undamped Vaughan mean error is exactly a fixed strip. -/
theorem zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power :
    zetaZeroAbscissa < 1 ↔ ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
        |pmUndampedVaughanConvolutionPrefix U V n -
          (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
            C * (n : ℝ) ^ (1 - η) := by
  constructor
  · intro hΘ
    obtain ⟨B, β, hB, _hβ0, hβ1, hM⟩ := zetaZeroAbscissa_lt_one_iff_moebius_rate.mp hΘ
    let η : ℝ := 1 - β
    let κ : ℝ := (η / (2 + η)) / 2
    have hη : 0 < η := sub_pos.mpr hβ1
    have hgain : 0 < η / (2 + η) := by positivity
    have hκ : 0 < κ := half_pos hgain
    have hκη : κ < η / (2 + η) := half_lt_self hgain
    have hM' (n : ℕ) (hn : 1 ≤ n) :
        |∑ d ∈ Icc 1 n, moebiusReal d| ≤ B * (n : ℝ) ^ (1 - η) := by
      simpa only [η, show 1 - (1 - β) = β by ring] using hM n hn
    obtain ⟨C, hC, hbound⟩ := exists_uniform_pmUndampedVaughan_power_of_mertens_power hη hκ hκη hB hM'
    exact ⟨κ, C, hκ, hC, hbound⟩
  · rintro ⟨δ, C, hδ, hC, h⟩
    exact zetaZeroAbscissa_lt_one_of_uniform_pmUndampedVaughan_power hδ hC h

#print axioms pmUndampedVaughanConvolutionPrefix_one_full
#print axioms exists_uniform_pmUndampedVaughan_power_of_mertens_power
#print axioms zetaZeroAbscissa_lt_one_of_uniform_pmUndampedVaughan_power
#print axioms zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power
end GaloisForLFunctions.BezoutValuationIncidence
