import GaloisForLFunctions.RHTower.Sieve.MultiPiBound

/-!
# The side conditions of the marker family, eventually

Everything the family needs — that the marker base is large, that its logarithm beats a fixed
constant, that the sifting bound exceeds three, and that the sieve remainder is beaten by the level
— follows from the single fact that the marker base grows.
-/

namespace RHTower.Sieve

open Filter Asymptotics

noncomputable section

/-- The marker base grows. -/
theorem tendsto_multiBase (K₀ : ℕ) :
    Tendsto (fun v : ℕ => ((multiBase K₀ v : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_multiScale K₀)
  filter_upwards [(tendsto_multiScale K₀).eventually_ge_atTop 3] with v hv
  have h3 : 3 ≤ multiScale K₀ v := by exact_mod_cast hv
  have hW1 : 1 ≤ multiFactor K₀ v := by
    have := two_le_multiFactor (K₀ := K₀) (v := v) h3
    omega
  have : multiScale K₀ v ≤ multiBase K₀ v := by
    rw [multiBase]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact_mod_cast this

/-- **The sifting bound exceeds three, eventually.** -/
theorem eventually_three_le_multiSift (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop, 3 ≤ multiSift K₀ v := by
  have hev : ∀ᶠ y : ℝ in atTop, (3 : ℝ) ^ (144 : ℕ) ≤ y := eventually_ge_atTop _
  filter_upwards [(tendsto_multiBase K₀).eventually hev,
    (tendsto_multiBase K₀).eventually_gt_atTop 0] with v hv hv0
  rw [multiSift]
  refine Nat.le_floor ?_
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [hcast]
  have hkey : ((3 : ℝ) ^ (144 : ℕ)) ^ ((1 : ℝ) / 144)
      ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 144) :=
    Real.rpow_le_rpow (by positivity) hv (by norm_num)
  refine le_trans (le_of_eq ?_) hkey
  rw [← Real.rpow_natCast (3 : ℝ) 144, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **The logarithm of the base beats any constant, eventually.** -/
theorem eventually_log_multiBase_ge (K₀ : ℕ) (c : ℝ) :
    ∀ᶠ v : ℕ in atTop, c ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
  have hev : ∀ᶠ y : ℝ in atTop, c ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop c
  exact (tendsto_multiBase K₀).eventually hev

/-- **The sieve remainder is beaten by the level, eventually.** -/
theorem eventually_multi_remainder (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop,
      8 * 4 ^ (K₀ + 1) * (Real.log ((multiBase K₀ v : ℕ) : ℝ)) ^ 2
        ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
  have hlo : (fun y : ℝ => Real.log y ^ (2 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((1 : ℝ) / 4) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  have hc : (0 : ℝ) < 1 / (8 * 4 ^ (K₀ + 1)) := by positivity
  have hbd := hlo.def hc
  have hev : ∀ᶠ y : ℝ in atTop,
      8 * 4 ^ (K₀ + 1) * (Real.log y) ^ 2 ≤ y ^ ((1 : ℝ) / 4) := by
    filter_upwards [hbd, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
    have hy0 : (0 : ℝ) < y := by linarith
    have hpow : Real.log y ^ (2 : ℝ) = (Real.log y) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg
      (Real.rpow_nonneg hy0.le _)] at hy
    have hK : (0 : ℝ) < 8 * 4 ^ (K₀ + 1) := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hK] at hy
    linarith [hy]
  exact (tendsto_multiBase K₀).eventually hev

/-- **All the side conditions of the pair budget, eventually.** -/
theorem eventually_multiPi_le (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop, multiPi K₀ v ≤ multiPiConst K₀ * ((multiScale K₀ v : ℕ) : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [(tendsto_multiBase K₀).eventually_ge_atTop 2,
    (tendsto_multiScale K₀).eventually_ge_atTop 3,
    eventually_log_multiBase_ge K₀ (288 * Real.log 2),
    eventually_three_le_multiSift K₀, eventually_multi_remainder K₀]
    with v hM2 hm3 hbig hs3 hrem
  have hM2' : 2 ≤ multiBase K₀ v := by exact_mod_cast hM2
  have hm3' : 3 ≤ multiScale K₀ v := by exact_mod_cast hm3
  have hW1 : 1 ≤ multiFactor K₀ v := by
    have := two_le_multiFactor (K₀ := K₀) (v := v) hm3'
    omega
  exact multiPi_le hM2' hW1 hbig hs3 hrem

end

end RHTower.Sieve
