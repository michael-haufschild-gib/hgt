import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMoebiusProducerHasARate
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheSharpReadingOfTheRate
import GaloisForLFunctions.RHTower.MertensPowerBoundsControlMobiusHarmonicSums
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureRH

/-!
# The rate is the Mertens level

A function `δ` is a **Mertens level** when, for all large `T`, `|M(y)| ≤ δ(T) y` on `y ≥ T` and
`|m(T)| ≤ δ(T)`, with `δ(T)` not too small. A Mertens level gives integer producers: at alphabet size
`K`, taking `T = ⌊K^{1/4}⌋`, there is a producer of rate at most
`8 δ(T) (3 + 6 log T)(1 + 4 log T)`.

Together with the sharp reading this closes the question of the rate at the level of exponents:

**polynomial rates exist if and only if `ζ` has a zero-free strip.**

So a stencil past a given rate is a zero-free region past that rate, and conversely.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- `mertens` is the corpus Mertens function. -/
theorem mertens_eq_mertensM (y : ℕ) : mertens y = RHTower.Sieve.mertensM y := by
  rw [mertens, RHTower.Sieve.mertensM]
  have hrange : range (y + 1) = insert 0 (Ioc 0 y) := by
    ext b
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hrange, sum_insert (by simp)]
  simp

/-- `mobiusHarmonic` is the corpus harmonic partial sum. -/
theorem mobiusHarmonic_eq_deninger (T : ℕ) :
    mobiusHarmonic T = RHTower.deningerHarmonicPartial T := by
  rw [mobiusHarmonic, RHTower.deningerHarmonicPartial]
  have hrange : range (T + 1) = insert 0 (Icc 1 T) := by
    ext b
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp)]
  simp

/-- A Mertens level: for all large `T`, the Mertens function and the harmonic sum are at most `δ(T)`,
and `δ(T)` is neither too small nor too large. -/
def IsMertensLevel (δ : ℕ → ℝ) : Prop :=
  ∀ᶠ T : ℕ in atTop, 0 < δ T ∧ δ T ≤ 1 ∧ 1 / (T : ℝ) ≤ δ T ∧
    (∀ y, T ≤ y → |mertens y| ≤ δ T * y) ∧ |mobiusHarmonic T| ≤ δ T ∧
    δ T * (3 + 6 * Real.log T) ≤ 1 / 2

/-- The cutoff at alphabet size `K`. -/
def levelCutoff (K : ℕ) : ℕ := ⌊(K : ℝ) ^ (1 / 4 : ℝ)⌋₊

theorem tendsto_levelCutoff : Tendsto levelCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)

theorem levelCutoff_pow_le (K : ℕ) : (levelCutoff K : ℝ) ^ 4 ≤ K := by
  have h0 : (0 : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have h1 : (levelCutoff K : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le h0
  calc ((levelCutoff K : ℕ) : ℝ) ^ 4 ≤ ((K : ℝ) ^ (1 / 4 : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 4
    _ = (K : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg K)]
        norm_num

/-- The cutoff is at least half of `K^{1/4}` once it is positive. -/
theorem half_rpow_le_levelCutoff {K : ℕ} (h1 : 1 ≤ levelCutoff K) :
    (K : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ levelCutoff K := by
  have hlt : (K : ℝ) ^ (1 / 4 : ℝ) < (levelCutoff K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hT : (1 : ℝ) ≤ levelCutoff K := by exact_mod_cast h1
  linarith

/-- **A Mertens level gives producers.** At alphabet size `K`, with `T = ⌊K^{1/4}⌋`, there is an integer
producer on an alphabet in `[1, K]` of rate at most `8 δ(T) (3 + 6 log T)(1 + 4 log T)`. -/
theorem eventually_producer_of_level {δ : ℕ → ℝ} (h : IsMertensLevel δ) :
    ∀ᶠ K : ℕ in atTop, ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
      rate c m B ≤ 8 * (δ (levelCutoff K) * (3 + 6 * Real.log (levelCutoff K))) *
        (1 + 4 * Real.log (levelCutoff K)) := by
  filter_upwards [tendsto_levelCutoff.eventually h, tendsto_levelCutoff.eventually_ge_atTop 2]
    with K hK hT2
  obtain ⟨hδ0, hδ1, hδT, hM, hm, hsm⟩ := hK
  set T := levelCutoff K with hT
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by linarith)
  -- `1/δ ≤ T` bounds both logarithms.
  have hinv : 1 / δ T ≤ T := by
    rw [div_le_iff₀ hδ0]
    rw [div_le_iff₀ hT0] at hδT
    linarith
  have hT2δ : (T : ℝ) ^ 2 / δ T ≤ (T : ℝ) ^ 3 := by
    calc (T : ℝ) ^ 2 / δ T = (T : ℝ) ^ 2 * (1 / δ T) := by ring
      _ ≤ (T : ℝ) ^ 2 * T := by gcongr
      _ = _ := by ring
  have hT3δ : (T : ℝ) ^ 3 / δ T ≤ (T : ℝ) ^ 4 := by
    calc (T : ℝ) ^ 3 / δ T = (T : ℝ) ^ 3 * (1 / δ T) := by ring
      _ ≤ (T : ℝ) ^ 3 * T := by gcongr
      _ = _ := by ring
  have hlog2 : Real.log ((T : ℝ) ^ 2 / δ T) ≤ 3 * Real.log T := by
    have := Real.log_le_log (by positivity) hT2δ
    rwa [Real.log_pow] at this
  have hlog3 : Real.log ((T : ℝ) ^ 3 / δ T) ≤ 4 * Real.log T := by
    have := Real.log_le_log (by positivity) hT3δ
    rwa [Real.log_pow] at this
  have hsmall : δ T * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ T)) ≤ 1 / 2 := by
    refine le_trans ?_ hsm
    exact mul_le_mul_of_nonneg_left (by linarith) hδ0.le
  obtain ⟨c, m, B, hP, hal, hr⟩ := exists_moebius_producer_of_level hT2 hδ0 hδ1 hM hm hsmall
  refine ⟨c, m, B, hP, fun k hk => ?_, hr.trans ?_⟩
  · have hle : (T : ℝ) ^ 3 / δ T ≤ K := hT3δ.trans (levelCutoff_pow_le K)
    exact (hal k hk).trans (Nat.floor_le_of_le hle)
  · have h0 : 0 ≤ Real.log ((T : ℝ) ^ 2 / δ T) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hδ0]
      nlinarith
    have h1 : 0 ≤ Real.log ((T : ℝ) ^ 3 / δ T) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hδ0]
      have : (T : ℝ) ^ 3 ≥ 1 := one_le_pow₀ (by linarith)
      nlinarith
    have hA : δ T * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ T)) ≤ δ T * (3 + 6 * Real.log T) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    have hA0 : 0 ≤ δ T * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ T)) := by positivity
    calc _ = 8 * (δ T * (3 + 2 * Real.log ((T : ℝ) ^ 2 / δ T))) *
          (1 + Real.log ((T : ℝ) ^ 3 / δ T)) := rfl
      _ ≤ 8 * (δ T * (3 + 6 * Real.log T)) * (1 + 4 * Real.log T) := by
          refine mul_le_mul (by linarith) (by linarith) (by linarith) ?_
          have : 0 ≤ δ T * (3 + 6 * Real.log T) := by positivity
          linarith

/-- `HasRate` is monotone in the rate. -/
theorem HasRate.mono {f g : ℕ → ℝ} (h : HasRate f) (hfg : ∀ᶠ K in atTop, f K ≤ g K) :
    HasRate g := by
  filter_upwards [h, hfg] with K hK hK'
  obtain ⟨c, m, B, hP, ha, hr⟩ := hK
  exact ⟨c, m, B, hP, ha, hr.trans hK'⟩

/-- **A power bound on the Mertens function is a Mertens level.** -/
theorem isMertensLevel_of_power {C σ : ℝ} (hC : 0 ≤ C) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hM : ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ C * (n : ℝ) ^ (1 - σ)) :
    IsMertensLevel fun T => (C + 1) * (1 + 1 / σ) * (T : ℝ) ^ (-σ) := by
  set A : ℝ := (C + 1) * (1 + 1 / σ) with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ C + 1 := by linarith
    have h2 : 1 ≤ 1 + 1 / σ := by
      have : 0 ≤ 1 / σ := by positivity
      linarith
    calc 1 = 1 * 1 := by ring
      _ ≤ A := mul_le_mul h1 h2 zero_le_one (by linarith)
  have hAC : C ≤ A := by
    have h2 : 1 ≤ 1 + 1 / σ := by
      have : 0 ≤ 1 / σ := by positivity
      linarith
    calc C ≤ (C + 1) * 1 := by linarith
      _ ≤ A := mul_le_mul_of_nonneg_left h2 (by linarith)
  have hlim : Tendsto (fun x : ℝ => (3 + Real.log x) * x ^ (-σ)) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_neg_atTop hσ0
    have h2 := (isLittleO_log_rpow_atTop hσ0).tendsto_div_nhds_zero
    have h3 := (h1.const_mul 3).add h2
    rw [mul_zero, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le]
    field_simp
  have hlimN : Tendsto (fun T : ℕ => 6 * A * ((3 + Real.log (T : ℝ)) * (T : ℝ) ^ (-σ))) atTop (𝓝 0) := by
    have := (hlim.comp tendsto_natCast_atTop_atTop).const_mul (6 * A)
    simpa using this
  have hpow0 : Tendsto (fun T : ℕ => A * (T : ℝ) ^ (-σ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hσ0).comp tendsto_natCast_atTop_atTop).const_mul A
    simpa using this
  filter_upwards [hlimN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hpow0.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with T hT1 hT2 hT3
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT3
  have hT0 : (0 : ℝ) < T := by linarith
  have hTσ : 0 < (T : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hT0 _
  have hA0 : 0 < A := by linarith
  have hlog : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hTR
  refine ⟨by positivity, hT2.le, ?_, ?_, ?_, ?_⟩
  · -- `1/T ≤ A T^{-σ}` since `σ ≤ 1`.
    have h : (T : ℝ) ^ (-1 : ℝ) ≤ (T : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le hTR (by linarith)
    rw [Real.rpow_neg_one, ← one_div] at h
    nlinarith
  · intro y hy
    have hy1 : 1 ≤ y := hT3.trans hy
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy1
    rw [mertens_eq_mertensM]
    refine (hM y hy1).trans ?_
    have hsplit : (y : ℝ) ^ (1 - σ) = (y : ℝ) * (y : ℝ) ^ (-σ) := by
      rw [sub_eq_add_neg, Real.rpow_add hyR, Real.rpow_one]
    have hmono : (y : ℝ) ^ (-σ) ≤ (T : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hT0 (by exact_mod_cast hy) (by linarith)
    have hy0 : (0 : ℝ) ≤ y := hyR.le
    rw [hsplit]
    calc C * ((y : ℝ) * (y : ℝ) ^ (-σ)) ≤ A * ((y : ℝ) * (T : ℝ) ^ (-σ)) := by gcongr
      _ = _ := by ring
  · rw [mobiusHarmonic_eq_deninger]
    exact (RHTower.abs_deningerHarmonicPartial_le_of_mertens_power hσ0 hC hM hT3).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hTσ.le)
  · have hlogge : 3 + 6 * Real.log (T : ℝ) ≤ 6 * (3 + Real.log (T : ℝ)) := by linarith
    calc A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T)
        ≤ A * (T : ℝ) ^ (-σ) * (6 * (3 + Real.log (T : ℝ))) :=
          mul_le_mul_of_nonneg_left hlogge (by positivity)
      _ = 6 * A * ((3 + Real.log (T : ℝ)) * (T : ℝ) ^ (-σ)) := by ring
      _ ≤ 1 / 2 := hT1.le

/-- **A power bound on the Mertens function gives a polynomial rate.** -/
theorem hasRate_of_power {C σ : ℝ} (hC : 0 ≤ C) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hM : ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ C * (n : ℝ) ^ (1 - σ)) :
    HasRate fun K => (K : ℝ) ^ (-(σ / 16)) := by
  have hlevel := isMertensLevel_of_power hC hσ0 hσ1 hM
  set A : ℝ := (C + 1) * (1 + 1 / σ) with hA
  have hσ2 : 0 < σ / 2 := by linarith
  -- The polylogarithm against `T^{-σ/2}`.
  have hlim : Tendsto (fun x : ℝ => 8 * A * ((3 + 6 * Real.log x) * (1 + 4 * Real.log x)) *
      x ^ (-(σ / 2))) atTop (𝓝 0) := by
    have hbig : (fun x : ℝ => (3 + 6 * Real.log x) * (1 + 4 * Real.log x)) =o[atTop]
        fun x : ℝ => x ^ (σ / 2) := by
      have h1 : (fun x : ℝ => (3 : ℝ) + 6 * Real.log x) =o[atTop] fun x : ℝ => x ^ (σ / 4) := by
        refine Asymptotics.IsLittleO.add ?_ ((isLittleO_log_rpow_atTop (by linarith)).const_mul_left 6)
        exact (Asymptotics.isLittleO_const_left.mpr (Or.inr
          (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by linarith)))))
      have h2 : (fun x : ℝ => (1 : ℝ) + 4 * Real.log x) =o[atTop] fun x : ℝ => x ^ (σ / 4) := by
        refine Asymptotics.IsLittleO.add ?_ ((isLittleO_log_rpow_atTop (by linarith)).const_mul_left 4)
        exact (Asymptotics.isLittleO_const_left.mpr (Or.inr
          (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by linarith)))))
      refine (h1.mul h2).congr' (EventuallyEq.refl _ _) ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have := hbig.tendsto_div_nhds_zero.const_mul (8 * A)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le]
    field_simp
  have hev := (hlim.comp ((tendsto_natCast_atTop_atTop).comp tendsto_levelCutoff)).eventually
    (gt_mem_nhds zero_lt_one)
  have hK2 : ∀ᶠ K : ℕ in atTop, (2 : ℝ) ≤ (K : ℝ) ^ (σ / 16) :=
    (((tendsto_rpow_atTop (by linarith : 0 < σ / 16))).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [eventually_producer_of_level hlevel, hev,
    tendsto_levelCutoff.eventually_ge_atTop 1, hK2, eventually_ge_atTop 1] with K hK hK1 hT1 hK3 hK4
  obtain ⟨c, m, B, hP, ha, hr⟩ := hK
  refine ⟨c, m, B, hP, ha, hr.trans ?_⟩
  set T := levelCutoff K with hT
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hT0 : (0 : ℝ) < T := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK4
  simp only [Function.comp] at hK1
  have hsplit : (T : ℝ) ^ (-σ) = (T : ℝ) ^ (-(σ / 2)) * (T : ℝ) ^ (-(σ / 2)) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have hQ0 : 0 < (T : ℝ) ^ (-(σ / 2)) := Real.rpow_pos_of_pos hT0 _
  have hbound : 8 * (A * (T : ℝ) ^ (-σ) * (3 + 6 * Real.log T)) * (1 + 4 * Real.log T) ≤
      (T : ℝ) ^ (-(σ / 2)) := by
    rw [hsplit]
    have heq : 8 * (A * ((T : ℝ) ^ (-(σ / 2)) * (T : ℝ) ^ (-(σ / 2))) * (3 + 6 * Real.log T)) *
        (1 + 4 * Real.log T) = (8 * A * ((3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ))) *
          (T : ℝ) ^ (-(σ / 2))) * (T : ℝ) ^ (-(σ / 2)) := by ring
    rw [heq]
    calc _ ≤ 1 * (T : ℝ) ^ (-(σ / 2)) := mul_le_mul_of_nonneg_right hK1.le hQ0.le
      _ = _ := one_mul _
  refine hbound.trans ?_
  -- `T ≥ K^{1/4}/2`.
  have hlow := half_rpow_le_levelCutoff hT1
  have hstep : (T : ℝ) ^ (-(σ / 2)) ≤ ((K : ℝ) ^ (1 / 4 : ℝ) / 2) ^ (-(σ / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
  refine hstep.trans ?_
  have hval : ((K : ℝ) ^ (1 / 4 : ℝ) / 2) ^ (-(σ / 2)) = (2 : ℝ) ^ (σ / 2) * (K : ℝ) ^ (-(σ / 8)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hK0.le, Real.rpow_neg (by norm_num)]
    have hexp : (1 / 4 : ℝ) * -(σ / 2) = -(σ / 8) := by ring
    rw [hexp]
    field_simp
  rw [hval]
  have h2pow : (2 : ℝ) ^ (σ / 2) ≤ 2 := by
    calc (2 : ℝ) ^ (σ / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hK8 : (K : ℝ) ^ (-(σ / 8)) = (K : ℝ) ^ (-(σ / 16)) * (K : ℝ) ^ (-(σ / 16)) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  have hK16 : (K : ℝ) ^ (-(σ / 16)) * (K : ℝ) ^ (σ / 16) = 1 := by
    rw [← Real.rpow_add hK0]
    simp
  have hK16pos : 0 < (K : ℝ) ^ (-(σ / 16)) := Real.rpow_pos_of_pos hK0 _
  have h2le : 2 * (K : ℝ) ^ (-(σ / 16)) ≤ 1 := by
    calc 2 * (K : ℝ) ^ (-(σ / 16)) ≤ (K : ℝ) ^ (σ / 16) * (K : ℝ) ^ (-(σ / 16)) :=
          mul_le_mul_of_nonneg_right hK3 hK16pos.le
      _ = 1 := by rw [mul_comm]; exact hK16
  rw [hK8]
  calc (2 : ℝ) ^ (σ / 2) * ((K : ℝ) ^ (-(σ / 16)) * (K : ℝ) ^ (-(σ / 16)))
      ≤ 2 * ((K : ℝ) ^ (-(σ / 16)) * (K : ℝ) ^ (-(σ / 16))) := by gcongr
    _ = (2 * (K : ℝ) ^ (-(σ / 16))) * (K : ℝ) ^ (-(σ / 16)) := by ring
    _ ≤ 1 * (K : ℝ) ^ (-(σ / 16)) := mul_le_mul_of_nonneg_right h2le hK16pos.le
    _ = _ := one_mul _

/-- **The exact theorem of the rate.** Polynomial rates exist if and only if `ζ` has a zero-free
strip: `A(K) − 1 ≤ K^{-a}` for some `a > 0` is the quasi-Riemann hypothesis. -/
theorem exists_hasRate_rpow_iff :
    (∃ a : ℝ, 0 < a ∧ HasRate fun K => (K : ℝ) ^ (-a)) ↔
      ∃ Θ : ℝ, Θ < 1 ∧ ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0 := by
  constructor
  · rintro ⟨a, ha, h⟩
    have ha' : 0 < min a 1 := lt_min ha one_pos
    have hmono : HasRate fun K => (K : ℝ) ^ (-(min a 1)) := by
      refine h.mono ?_
      filter_upwards [eventually_ge_atTop 1] with K hK
      have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
      exact Real.rpow_le_rpow_of_exponent_le hKR (by linarith [min_le_left a 1])
    refine ⟨1 - 2 * min a 1 / 3, by linarith, fun s hs hz => ?_⟩
    have := re_le_of_hasRate_rpow_sharp ha' (min_le_right a 1) hmono hz
    linarith
  · rintro ⟨Θ₀, hΘ₀, hzf⟩
    set Θ : ℝ := max Θ₀ (1 / 2) with hΘ
    have hΘ1 : Θ < 1 := max_lt hΘ₀ (by norm_num)
    have hΘh : 1 / 2 ≤ Θ := le_max_right _ _
    have hzf' : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz =>
      hzf z (lt_of_le_of_lt (le_max_left _ _) hz)
    set σ : ℝ := (1 - Θ) / 2 with hσ
    have hσ0 : 0 < σ := by rw [hσ]; linarith
    have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
    obtain ⟨C, hC, hbd⟩ := RHTower.mobiusMertens_subpower_of_zeroFree hΘh hΘ1.le hzf' σ hσ0
    have hexp : Θ + σ = 1 - σ := by rw [hσ]; ring
    have hM : ∀ n : ℕ, 1 ≤ n → |RHTower.Sieve.mertensM n| ≤ (C * 2) * (n : ℝ) ^ (1 - σ) := by
      intro n hn
      have hb := hbd n
      rw [RHTower.mobiusMertensPartialSum_eq_sieveMertensM, Complex.norm_real, Real.norm_eq_abs,
        hexp] at hb
      refine hb.trans ?_
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h0 : (0 : ℝ) ≤ 1 - σ := by rw [hσ]; linarith
      have h1 : ((n : ℝ) + 1) ^ (1 - σ) ≤ (2 * (n : ℝ)) ^ (1 - σ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) h0
      have h2 : (2 * (n : ℝ)) ^ (1 - σ) = (2 : ℝ) ^ (1 - σ) * (n : ℝ) ^ (1 - σ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      have h3 : (2 : ℝ) ^ (1 - σ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hnp : 0 ≤ (n : ℝ) ^ (1 - σ) := by positivity
      calc C * ((n : ℝ) + 1) ^ (1 - σ) ≤ C * ((2 : ℝ) ^ (1 - σ) * (n : ℝ) ^ (1 - σ)) := by
            rw [← h2]
            exact mul_le_mul_of_nonneg_left h1 hC
        _ ≤ C * (2 * (n : ℝ) ^ (1 - σ)) := by gcongr
        _ = _ := by ring
    exact ⟨σ / 16, by positivity, hasRate_of_power (by positivity) hσ0 hσ1 hM⟩

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
