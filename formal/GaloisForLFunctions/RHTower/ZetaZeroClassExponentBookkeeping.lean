import GaloisForLFunctions.RHTower.ZetaZeroClassLargeValueCounts
import GaloisForLFunctions.RHTower.ZetaZeroDensityExponentLemmas

/-!
# Bookkeeping for a detection class at height `T`

At height `T ≥ 2^{400}` with the density parameters `y = ⌊T^{1/40}⌋`, `N = ⌈T^{61/50}⌉`:

* the number of dyadic blocks is `J ≤ 3(1 + log T)`;
* a block `2^j` that carries a nonzero large value satisfies `T^{1/50} ≤ 2^j ≤ T^{4/3}`, because
  its coefficients vanish below the mollifier length and the support ends at `Ny ≤ 2T^{1.245}`;
* for `1 ≤ ℓ ≤ 34` and `(2^j)^ℓ ≤ T^{4/3}`, `1 + log (2^{j+1})^ℓ ≤ 36(1 + log T)`, and the mass of
  the `ℓ`-th power is at most `2^{34} X^{1-2σ} (36(1 + log T))^{2^{136}}` with `X = (2^j)^ℓ`.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve

theorem densityParameters_upper {T : ℝ} (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T) :
    ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ) ≤ 2 * T ^ (249 / 200 : ℝ) := by
  obtain ⟨_, hyT, _, hN2, _⟩ := densityParameters hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  push_cast
  calc (densityBlockLength T : ℝ) * densityMollifierLength T
      ≤ (2 * T ^ (61 / 50 : ℝ)) * T ^ (1 / 40 : ℝ) :=
        mul_le_mul hN2 hyT (Nat.cast_nonneg _) (by positivity)
    _ = 2 * T ^ (249 / 200 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hT0]
        norm_num

/-- **The number of dyadic blocks is logarithmic.** -/
theorem detBlockCount_le_log {T : ℝ} (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T) :
    (detBlockCount (densityBlockLength T) (densityMollifierLength T) : ℝ)
      ≤ 3 * (1 + Real.log T) := by
  obtain ⟨_, _, _, _, hNy⟩ := densityParameters hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT
  set m := densityBlockLength T * densityMollifierLength T with hm
  have hm0 : m ≠ 0 := by omega
  have hpow : ((2 : ℝ) ^ Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hm0
  have hlog2 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hmup := densityParameters_upper hT
  have hlogm : Real.log m ≤ Real.log 2 + (249 / 200) * Real.log T := by
    have := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0) hmup
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hT0 _).ne', Real.log_rpow hT0] at this
    exact this
  have hl2 : (0.69 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
  have hl2' : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hN : (Nat.log 2 m : ℝ) ≤ 2 + 2 * Real.log T := by
    have h1 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ 1 + (249 / 200) * Real.log T := by linarith
    have h2 : (Nat.log 2 m : ℝ) * 0.69 ≤ (Nat.log 2 m : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
    nlinarith
  unfold detBlockCount
  push_cast
  linarith

/-- **A block with a large value starts above the mollifier length.** -/
theorem block_bounds_of_large {T : ℝ} (hT : (2 : ℝ) ^ (400 : ℕ) ≤ T) {j i : ℕ} {σ' t V : ℝ}
    (hV : 0 < V)
    (hbig : V ≤ ‖dpoly (classCoeff (densityBlockLength T) (densityMollifierLength T)
      (Real.log (densityBlockLength T * densityMollifierLength T : ℕ)) i σ')
      (detDyadicBlock (densityBlockLength T) (densityMollifierLength T) j) t‖) :
    T ^ (1 / 50 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧ ((2 ^ j : ℕ) : ℝ) ≤ T ^ (4 / 3 : ℝ) := by
  have hT120 : (2 : ℝ) ^ (120 : ℕ) ≤ T :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hT
  obtain ⟨hy1, hyT, hN1, hN2, hNy⟩ := densityParameters hT120
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  set N := densityBlockLength T
  set y := densityMollifierLength T
  -- some coefficient of the block is nonzero
  have hne : ∃ k ∈ detDyadicBlock N y j,
      classCoeff N y (Real.log (N * y : ℕ)) i σ' k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : dpoly (classCoeff N y (Real.log (N * y : ℕ)) i σ') (detDyadicBlock N y j) t = 0 := by
      unfold dpoly
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [cterm, hcon k hk]
      simp
    rw [hzero, norm_zero] at hbig
    linarith
  obtain ⟨k, hk, hkne⟩ := hne
  have hks := mem_detSupport_le (Finset.mem_filter.mp hk).1
  have hkb := mem_detDyadicBlock_bounds hk
  have hN : 1 ≤ N := by
    have := hNy
    by_contra h
    have h0 : N = 0 := by omega
    rw [h0] at this
    simp at this
  -- the coefficient vanishes up to `y`
  have hky : y < k := by
    by_contra h
    push Not at h
    have hyN : y ≤ N := by
      have h1 : ((y : ℕ) : ℝ) ≤ N := by
        calc ((y : ℕ) : ℝ) ≤ T ^ (1 / 40 : ℝ) := hyT
          _ ≤ T ^ (61 / 50 : ℝ) := Real.rpow_le_rpow_of_exponent_le
              (le_trans (one_le_pow₀ (by norm_num)) hT) (by norm_num)
          _ ≤ N := hN1
      exact_mod_cast h1
    apply hkne
    rw [classCoeff, detCoeff_eq_zero_of_le hks.1 (le_trans h hyN) h]
    ring
  constructor
  · -- `2^j > y/2 ≥ T^{1/50}`
    have hk2 : k < 2 * 2 ^ j := by rw [← pow_succ']; exact hkb.2
    have hy2 : (y : ℝ) + 1 ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast (by omega : y + 1 ≤ 2 * 2 ^ j)
    have hyfloor : T ^ (1 / 40 : ℝ) < (y : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (T ^ (1 / 40 : ℝ))
      simpa [y, densityMollifierLength] using this
    have hkey : 2 * T ^ (1 / 50 : ℝ) ≤ T ^ (1 / 40 : ℝ) := by
      have hsplit : T ^ (1 / 40 : ℝ) = T ^ (1 / 200 : ℝ) * T ^ (1 / 50 : ℝ) := by
        rw [← Real.rpow_add hT0]
        norm_num
      have h2 : (2 : ℝ) ≤ T ^ (1 / 200 : ℝ) := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (400 : ℕ)) ^ (1 / 400 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              norm_num
          _ ≤ T ^ (1 / 400 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
          _ ≤ T ^ (1 / 200 : ℝ) := Real.rpow_le_rpow_of_exponent_le
              (le_trans (one_le_pow₀ (by norm_num)) hT) (by norm_num)
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)
    linarith
  · -- `2^j ≤ k ≤ Ny ≤ 2T^{1.245} ≤ T^{4/3}`
    have hup := densityParameters_upper hT120
    have hkNy : ((2 ^ j : ℕ) : ℝ) ≤ ((N * y : ℕ) : ℝ) := by
      exact_mod_cast le_trans hkb.1 hks.2
    refine le_trans hkNy (le_trans hup ?_)
    have hsplit : T ^ (4 / 3 : ℝ) = T ^ (53 / 600 : ℝ) * T ^ (249 / 200 : ℝ) := by
      rw [← Real.rpow_add hT0]
      norm_num
    have h2 : (2 : ℝ) ≤ T ^ (53 / 600 : ℝ) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (400 : ℕ)) ^ (1 / 400 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ T ^ (1 / 400 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
        _ ≤ T ^ (53 / 600 : ℝ) := Real.rpow_le_rpow_of_exponent_le
            (le_trans (one_le_pow₀ (by norm_num)) hT) (by norm_num)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)

/-- The logarithm of the raised length is at most `36(1 + log T)` in the window. -/
theorem one_add_log_raised_le {T : ℝ} (hT : 1 ≤ T) {j ℓ : ℕ} (hℓ : ℓ ≤ 34)
    (hX : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (4 / 3 : ℝ)) :
    1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 36 * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * (((2 ^ j : ℕ) : ℝ)) ^ ℓ := by
    push_cast
    ring
  have hXpos : 0 < (((2 ^ j : ℕ) : ℝ)) ^ ℓ := by positivity
  rw [hcast, Real.log_mul (by positivity) hXpos.ne', Real.log_pow]
  have h1 : (ℓ : ℝ) * Real.log 2 ≤ 34 := by
    have : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    have hℓR : (ℓ : ℝ) ≤ 34 := by exact_mod_cast hℓ
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  have h2 : Real.log ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ≤ (4 / 3) * Real.log T := by
    have := Real.log_le_log hXpos hX
    rwa [Real.log_rpow hT0] at this
  linarith

/-- **The mass of a raised class polynomial in the window.** -/
theorem classPowerMass_le {T : ℝ} (hT : 1 ≤ T) {j ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 34) {σ : ℝ}
    (hX : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (4 / 3 : ℝ)) :
    classPowerMass j ℓ σ ≤ 2 ^ 34 * ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ (1 - 2 * σ)
        * (36 * (1 + Real.log T)) ^ (2 ^ 136) := by
  have hlog := one_add_log_raised_le hT hℓ hX
  set X := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hX0 : 0 < X := by linarith
  have hΛ1 : 1 ≤ 36 * (1 + Real.log T) := by
    have := Real.log_nonneg hT
    linarith
  have hlogL0 : 1 ≤ 1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    have : 0 ≤ Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_pow _ _ (by positivity))
    linarith
  have hcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have h2l : (2 : ℝ) ^ ℓ ≤ 2 ^ 34 := pow_le_pow_right₀ (by norm_num) hℓ
  have hexp : 2 ^ (4 * ℓ) - 1 ≤ 2 ^ 136 := by
    have : 2 ^ (4 * ℓ) ≤ 2 ^ 136 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpolylog : (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) ^ (2 ^ (4 * ℓ) - 1)
      ≤ (36 * (1 + Real.log T)) ^ (2 ^ 136) :=
    le_trans (pow_le_pow_left₀ (by linarith) hlog _) (pow_le_pow_right₀ hΛ1 hexp)
  unfold classPowerMass
  rw [← hXdef, hcast]
  have hXpow : X ^ (-2 * σ) * (2 ^ ℓ * X) = 2 ^ ℓ * X ^ (1 - 2 * σ) := by
    rw [show (1 - 2 * σ) = (-2 * σ) + 1 by ring, Real.rpow_add hX0, Real.rpow_one]
    ring
  rw [hXpow]
  have hXnn : 0 ≤ X ^ (1 - 2 * σ) := Real.rpow_nonneg hX0.le _
  calc 2 ^ ℓ * X ^ (1 - 2 * σ) * (1 + Real.log (2 ^ ℓ * X)) ^ (2 ^ (4 * ℓ) - 1)
      ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * (36 * (1 + Real.log T)) ^ (2 ^ 136) := by
        rw [← hcast]
        gcongr

end

end RHTower
