import GaloisForLFunctions.PrimeExponentialSums.LogarithmicPrimeMomentsOnDyadicWindows
import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic

/-!
# Square mass of pointwise envelopes on prime powers

On Y < p ≤ 2Y the square mass of p^(kθ) log p is asymptotic to
((2^a−1)/a) Y^a log Y, where a=1+2kθ. Relative to the prime-power
cutoff X=(2Y)^k, its power exponent is 1/k+2θ. At θ=5/14 the
pointwise estimate in Lemma 2.3 of arXiv:2610.18928 thus allows excess
at both squares and cubes.
-/

noncomputable section
open Filter Topology Finset RHTower
namespace GaloisForLFunctions.PrimeExponentialSums.PrimeMoments

private theorem shell_eq (a Y : ℝ) (hY : 2 ≤ Y) :
    moment (fun t => t^(a-1)*Real.log t) 0 Y =
      primeRpowLogSumIoc a (2*Y) - primeRpowLogSumIoc a Y := by
  let f (p : ℕ) := if p.Prime then (p:ℝ)^(a-1)*Real.log p else 0
  have h₁ : 2 ≤ ⌊Y⌋₊ := (Nat.le_floor_iff (by linarith only [hY])).2 (by exact_mod_cast hY)
  have h₂ := Nat.floor_mono (show Y≤2*Y by linarith only [hY])
  have h := Finset.sum_Ioc_consecutive f h₁ h₂
  change _ = (∑ p ∈ Ioc 2 ⌊2*Y⌋₊, f p) - ∑ p ∈ Ioc 2 ⌊Y⌋₊, f p
  rw [← h,add_sub_cancel_left]
  unfold moment primeCountSum
  simp only [f,← sum_filter,pow_zero,mul_one]
  apply sum_congr rfl
  intro p hp
  obtain ⟨_,hy,_⟩ := mem_shell_of_mem_filter (by linarith only [hY] : 0≤Y) hp
  have hp₁ : 1≤(p:ℝ) := by linarith only [hy,hY]
  exact abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hp₁) _) (Real.log_nonneg hp₁))

/-- Power-weighted prime logarithms on a multiplicative window, with the exact constant. -/
theorem rpow_log_window (a : ℝ) (ha : 0<a) (j : ℕ) :
    Tendsto (fun Y => moment (fun t => t^(a-1)*Real.log t) j Y / (Y^a*Real.log Y^j))
      atTop (𝓝 (((2:ℝ)^a-1)/a)) := by
  let scale (Y : ℝ) : NNReal := (Real.toNNReal (Y^a))⁻¹
  have h := tendsto_primeRpowLogSumIoc ha
  have h₂ := h.comp (RHTower.tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num))
  have raw := (h₂.const_mul ((2:ℝ)^a)).sub h
  have ht : Tendsto (fun Y => (scale Y:ℝ)*moment (fun t => t^(a-1)*Real.log t) 0 Y)
      atTop (𝓝 (((2:ℝ)^a-1)/a)) := by
    rw [show (2:ℝ)^a*(1/a)-1/a=(2^a-1)/a by ring] at raw
    refine raw.congr' ?_
    filter_upwards [eventually_ge_atTop (2:ℝ)] with Y hY
    have hy : 0<Y := by linarith only [hY]
    change 2^a*(primeRpowLogSumIoc a (2*Y)/(2*Y)^a) - primeRpowLogSumIoc a Y/Y^a = _
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hy.le,shell_eq a Y hY]
    simp only [scale,NNReal.coe_inv,Real.coe_toNNReal _ (Real.rpow_nonneg hy.le _)]
    field_simp [(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) a).ne',
      (Real.rpow_pos_of_pos hy a).ne']
    <;> ring
  apply ((transfer_limit _ j scale _).2 ht).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y hy
  simp only [scale,NNReal.coe_inv,Real.coe_toNNReal _ (Real.rpow_nonneg hy.le _)]
  ring

/-- Square of the pointwise envelope, summed over primes in the base window. -/
def envelope (θ : ℝ) (k : ℕ) (Y : ℝ) :=
  primeCountSum (fun t => (t^((k:ℝ)*θ)*Real.log t)^2) Y (2*Y)

private theorem envelope_eq (θ : ℝ) (k : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    envelope θ k Y = moment (fun t => t^((1+2*k*θ)-1)*Real.log t) 1 Y := by
  unfold envelope primeCountSum moment
  apply sum_congr rfl
  intro p hp
  obtain ⟨_,hy,_⟩ := mem_shell_of_mem_filter (zero_le_one.trans hY) hp
  have hp₀ := one_pos.trans_le (hY.trans hy.le)
  have hl := Real.log_nonneg (hY.trans hy.le)
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hp₀.le _) hl),pow_one,mul_pow,
    ← Real.rpow_mul_natCast hp₀.le]
  rw [show (k:ℝ)*θ*(2:ℕ)=(1+2*k*θ)-1 by push_cast; ring]
  ring

/-- Exact square mass for any degree and any exponent with a positive cumulative power. -/
theorem envelope_asymptotic (θ : ℝ) (k : ℕ) (ha : 0<1+2*k*θ) :
    let a := 1+2*k*θ
    Tendsto (fun Y => envelope θ k Y/(Y^a*Real.log Y)) atTop (𝓝 (((2:ℝ)^a-1)/a)) := by
  apply (rpow_log_window (1+2*k*θ) ha 1).congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Y hy
  rw [envelope_eq θ k Y hy,pow_one]

/-- When 1+2kθ>k the square mass of the allowed envelope exceeds every
constant times X log X with X=(2Y)^k. -/
theorem excess (θ : ℝ) (k : ℕ) (hk : 0<k) (ha : (k:ℝ)<1+2*k*θ) :
    Tendsto (fun Y : ℝ => envelope θ k Y/((2*Y)^k*Real.log ((2*Y)^k))) atTop atTop := by
  let a : ℝ := 1+2*k*θ
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have ha' : 0<a := hk'.trans ha
  have hc : 0<((2:ℝ)^a-1)/a := div_pos (sub_pos.mpr (Real.one_lt_rpow (by norm_num) ha')) ha'
  have hl := tendsto_log_shift_ratio (Real.log 2)
  have scale := ((envelope_asymptotic θ k ha').mul hl).div_const ((2:ℝ)^k*k)
  rw [mul_one] at scale
  have hpos : 0<(((2:ℝ)^a-1)/a)/(2^k*k) := div_pos hc (by positivity)
  have grow := Filter.Tendsto.pos_mul_atTop hpos scale (tendsto_rpow_atTop (sub_pos.mpr ha))
  refine grow.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with Y hY
  have hy := one_pos.trans hY
  have hlY := (Real.log_pos hY).ne'
  have hl₂ := (Real.log_pos (show 1<2*Y by linarith only [hY])).ne'
  change (envelope θ k Y/(Y^a*Real.log Y)*(Real.log Y/(Real.log Y+Real.log 2))/
    (2^k*k))*Y^(a-(k:ℝ)) = _
  rw [Real.rpow_sub hy,Real.rpow_natCast,Real.log_pow,Real.log_mul two_ne_zero hy.ne',mul_pow]
  rw [Real.log_mul two_ne_zero hy.ne'] at hl₂
  rw [add_comm (Real.log Y) (Real.log 2)]
  field_simp [(Real.rpow_pos_of_pos hy a).ne',hlY,hl₂,hk'.ne',hy.ne']
  <;> ring

/-- Squares and cubes both exceed X log X at the exponent 5/14. -/
theorem square_and_cube_excess :
    Tendsto (fun Y : ℝ => envelope (5/14) 2 Y/((2*Y)^2*Real.log ((2*Y)^2))) atTop atTop ∧
    Tendsto (fun Y : ℝ => envelope (5/14) 3 Y/((2*Y)^3*Real.log ((2*Y)^3))) atTop atTop :=
  ⟨excess _ _ (by norm_num) (by norm_num),excess _ _ (by norm_num) (by norm_num)⟩

/-- Bases whose k-th power lies below the integer cutoff. -/
def bases (N k : ℕ) := (Nat.primesLE N).filter fun p => p^k ≤ N

private theorem fourth_root_bound {N k : ℕ} (hk : 4≤k) :
    ((bases N k).card:ℝ) ≤ (N:ℝ)^(1/4:ℝ) := by
  have hroot := Real.rpow_nonneg (Nat.cast_nonneg N) (1/4:ℝ)
  have hs : bases N k ⊆ Ioc 0 ⌊(N:ℝ)^(1/4:ℝ)⌋₊ := by
    intro p hp
    obtain ⟨hm,hpk⟩ := mem_filter.mp hp
    have hprime := (Nat.mem_primesLE.mp hm).2
    have h₄ := (Nat.pow_le_pow_right hprime.pos hk).trans hpk
    have h := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg p) 4)
      (by exact_mod_cast h₄ : (p:ℝ)^4≤N) (by norm_num : (0:ℝ)≤1/4)
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p),show (4:ℕ)*(1/4:ℝ)=1 by norm_num,
      Real.rpow_one] at h
    exact mem_Ioc.mpr ⟨hprime.pos,(Nat.le_floor_iff hroot).2 h⟩
  have hc := card_le_card hs
  rw [Nat.card_Ioc,Nat.sub_zero] at hc
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hroot)

private theorem degree_bound (N k : ℕ) (hk : 4≤k) :
    (∑ p ∈ bases N k, ((p:ℝ)^((k:ℝ)*(5/14:ℝ))*Real.log p)^2) ≤
      (N:ℝ)^(27/28:ℝ)*(Real.log N)^2 := by
  let B := (N:ℝ)^(5/7:ℝ)*(Real.log N)^2
  have hB : 0≤B := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
  calc
    _ ≤ ∑ _p ∈ bases N k, B := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hm,hpk⟩ := mem_filter.mp hp
      obtain ⟨hN,hprime⟩ := Nat.mem_primesLE.mp hm
      have hp₁ : (1:ℝ)≤p := by exact_mod_cast hprime.one_lt.le
      rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg p),
        show (k:ℝ)*(5/14:ℝ)*(2:ℕ)=k*(5/7:ℝ) by push_cast; ring,
        Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      apply mul_le_mul (Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg p) k)
        (by exact_mod_cast hpk) (by norm_num)) _ (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact pow_le_pow_left₀ (Real.log_nonneg hp₁)
        (Real.log_le_log (zero_lt_one.trans_le hp₁) (by exact_mod_cast hN)) 2
    _ ≤ (N:ℝ)^(1/4:ℝ)*B := by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (fourth_root_bound hk) hB
    _ = _ := by
      unfold B
      rw [← mul_assoc,← Real.rpow_add_of_nonneg (Nat.cast_nonneg N) (by norm_num) (by norm_num)]
      norm_num

/-- The whole tail from fourth powers on has power 27/28, with an
explicit logarithmic factor counting the possible exponents. -/
theorem fourth_power_tail (N : ℕ) :
    (∑ k ∈ Icc 4 (Nat.log 2 N), ∑ p ∈ bases N k,
      ((p:ℝ)^((k:ℝ)*(5/14:ℝ))*Real.log p)^2) ≤
      (Nat.log 2 N:ℝ)*((N:ℝ)^(27/28:ℝ)*(Real.log N)^2) := by
  calc
    _ ≤ ∑ _k ∈ Icc 4 (Nat.log 2 N), (N:ℝ)^(27/28:ℝ)*(Real.log N)^2 :=
      sum_le_sum fun k hk => degree_bound N k (mem_Icc.mp hk).1
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul,Nat.card_Icc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show Nat.log 2 N+1-4≤Nat.log 2 N by omega))
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (sq_nonneg _))

end GaloisForLFunctions.PrimeExponentialSums.PrimeMoments

#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.rpow_log_window
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.envelope_asymptotic
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.excess
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.square_and_cube_excess
#print axioms GaloisForLFunctions.PrimeExponentialSums.PrimeMoments.fourth_power_tail
