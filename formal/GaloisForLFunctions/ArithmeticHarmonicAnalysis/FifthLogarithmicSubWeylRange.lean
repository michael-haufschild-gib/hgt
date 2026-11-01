import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FifthLogarithmicWeylWindow
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma

/-! # The sub-Weyl exponent on the fifth-derivative interval

A ceiling window balances the two leading differencing terms. Direct
logarithmic comparisons control every secondary term on
`T^(97/200) ≤ N ≤ T^(101/200)`.
-/

noncomputable section
open RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Every contribution to the squared prefix bound is controlled by
`N*T^(33/100)` on the fifth-derivative interval. -/
theorem fifthRange_numeric {N H : ℕ} {T x : ℝ} (hN0 : (0 : ℝ) < N) (hT0 : 0 < T)
    (hx : x = (N : ℝ) ^ (36 / 41 : ℝ) * T ^ (-(11 / 41) : ℝ)) (hHx : x ≤ H) (hHx2 : (H : ℝ) ≤ 2 * x)
    (F1 : 97 * Real.log T ≤ 200 * Real.log (N : ℝ))
    (F2 : 200 * Real.log (N : ℝ) ≤ 101 * Real.log T)
    (hlT9 : 9 * Real.log 2 ≤ Real.log T) :
    (H : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 24 * N * fifthDiffLogQ T N H
      ≤ 10 ^ 26 * (1 * (N : ℝ) ^ (1 : ℝ) * T ^ (33 / 100 : ℝ)) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl70 : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num)
  have hlogT : 0 ≤ Real.log T := by linarith only [hlT9, hl2]
  have hlogN : 0 ≤ Real.log (N : ℝ) := by linarith only [F1, hlogT]
  have hx0 : 0 < x := by rw [hx]; positivity
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le hx0 hHx
  obtain ⟨M, hM⟩ : ∃ M, M = 1 * (N : ℝ) ^ (1 : ℝ) * T ^ (33 / 100 : ℝ) := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by rw [hM]; positivity
  -- `TH ≤ Y = 2N^{36/41}T^{30/41}`
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 * (N : ℝ) ^ (36 / 41 : ℝ) * T ^ (30 / 41 : ℝ) := ⟨_, rfl⟩
  have hTH : T * H ≤ Y := by
    have e : T * (2 * x) = Y := by
      rw [hx, hY]
      have : T * T ^ (-(11 / 41) : ℝ) = T ^ (30 / 41 : ℝ) := by
        rw [← Real.rpow_one_add' hT0.le (by norm_num)]; norm_num
      calc T * (2 * ((N : ℝ) ^ (36 / 41 : ℝ) * T ^ (-(11 / 41) : ℝ)))
          = 2 * (N : ℝ) ^ (36 / 41 : ℝ) * (T * T ^ (-(11 / 41) : ℝ)) := by ring
        _ = _ := by rw [this]
    rw [← e]; exact mul_le_mul_of_nonneg_left hHx2 hT0.le
  have hTH0 : 0 ≤ T * H := by positivity
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hlY : Real.log Y = Real.log 2 + 36 / 41 * Real.log (N : ℝ) + 30 / 41 * Real.log T := by
    rw [hY]; exact log_mono_eq two_pos hN0 hT0 _ _
  have hlM : Real.log M = 1 * Real.log (N : ℝ) + 33 / 100 * Real.log T := by
    rw [hM, log_mono_eq one_pos hN0 hT0, Real.log_one]; ring
  have hlc : ∀ c : ℝ, 0 < c → Real.log (c * M) = Real.log c + Real.log M := fun c hc =>
    Real.log_mul hc.ne' hM0.ne'
  -- the eight terms
  have t1 : (H : ℝ) ^ 2 ≤ 4 * M := by
    have h1 : (H : ℝ) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ hH0.le hHx2 2
    have h2' : x ^ 2 ≤ M := by
      refine le_of_log_le_log (by positivity) hM0 ?_
      rw [Real.log_pow, hx, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0,
        Real.log_rpow hT0, hlM]
      push_cast
      linarith only [F2, hlogT]
    nlinarith only [h1, h2']
  have t2 : 4 * (N : ℝ) ^ 2 / H ≤ 4 * M := by
    rw [div_le_iff₀ hH0]
    have e : (N : ℝ) ^ 2 ≤ M * x := by
      refine le_of_log_le_log (by positivity) (by positivity) ?_
      rw [Real.log_pow, Real.log_mul hM0.ne' hx0.ne', hlM, hx,
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow hT0]
      push_cast
      linarith only [F2, hlogT]
    have hm := mul_le_mul_of_nonneg_left hHx hM0.le
    linarith only [e, hm]
  have q1 : (N : ℝ) * ((T * H) ^ (11 / 30 : ℝ) * (N : ℝ) ^ (-(1 / 5) : ℝ)) ≤ 2 * M := by
    have h1 : (T * H) ^ (11 / 30 : ℝ) ≤ Y ^ (11 / 30 : ℝ) :=
      Real.rpow_le_rpow hTH0 hTH (by norm_num)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity))
      hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hY0, Real.log_rpow hN0, hlY, hlc 2 two_pos, hlM]
    linarith only [F2, hlogT, hl2]
  have q2 : (N : ℝ) * ((T * H) ^ (5 / 8 : ℝ) * (N : ℝ) ^ (-(13 / 16) : ℝ)) ≤ 2 * M := by
    have h1 : (T * H) ^ (5 / 8 : ℝ) ≤ Y ^ (5 / 8 : ℝ) :=
      Real.rpow_le_rpow hTH0 hTH (by norm_num)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity))
      hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hY0, Real.log_rpow hN0, hlY, hlc 2 two_pos, hlM]
    linarith only [F1, hlogT, hl2]
  have q3 : (N : ℝ) * (T * H / (N : ℝ) ^ 2) ≤ 2 * M := by
    have h1 : T * H / (N : ℝ) ^ 2 ≤ Y / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hTH (by positivity)
    refine (mul_le_mul_of_nonneg_left h1 hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_div hY0.ne' (by positivity), Real.log_pow,
      hlY, hlc 2 two_pos, hlM]
    push_cast
    linarith only [F1, hlogT, hl2]
  have q4 : (N : ℝ) * ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) ≤ 7 * M := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_div (by positivity) hT0.ne', Real.log_pow, hlc 7 (by norm_num), hlM]
    push_cast
    linarith only [F2, hlogT, hl70]
  have q5 : (N : ℝ) * ((T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ)) ≤ 2 * M := by
    have h1 : (T * H) ^ (2 / 5 : ℝ) ≤ Y ^ (2 / 5 : ℝ) :=
      Real.rpow_le_rpow hTH0 hTH (by norm_num)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity))
      hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hY0, Real.log_rpow hN0, hlY, hlc 2 two_pos, hlM]
    linarith only [hlogT, hlogN, hl2]
  have q6 : (N : ℝ) * (N : ℝ) ^ (5 / 8 : ℝ) ≤ 7 * M := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_rpow hN0, hlc 7 (by norm_num), hlM]
    linarith only [F2, hlogT, hl70]
  have hQ : (N : ℝ) * fifthDiffLogQ T N H ≤ 22 * M := by
    have e : (N : ℝ) * fifthDiffLogQ T N H = (N : ℝ) * ((T * H) ^ (11 / 30 : ℝ) * (N : ℝ) ^ (-(1 / 5) : ℝ))
          + (N : ℝ) * ((T * H) ^ (5 / 8 : ℝ) * (N : ℝ) ^ (-(13 / 16) : ℝ))
          + (N : ℝ) * (T * H / (N : ℝ) ^ 2) + (N : ℝ) * ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ)
          + (N : ℝ) * ((T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ))
          + (N : ℝ) * (N : ℝ) ^ (5 / 8 : ℝ) := by rw [fifthDiffLogQ]; ring
    rw [e]
    linarith only [q1, q2, q3, q4, q5, q6]
  have e : 4 * 10 ^ 24 * (N : ℝ) * fifthDiffLogQ T N H = 4 * 10 ^ 24 * ((N : ℝ) * fifthDiffLogQ T N H) := by
    ring
  rw [e]
  have h3 := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 24)
  linarith only [t1, t2, h3, hM0]

/-- The actual logarithmic prefix has exponent `33/200` after its critical weight. -/
theorem norm_prefix_le_fifthRange {t : ℝ} (ht : 512 ≤ t / (2 * Real.pi))
    {N L : ℕ} (hN : 3 ≤ N) (hL : L ≤ N)
    (F1 : 97 * Real.log (t / (2 * Real.pi)) ≤ 200 * Real.log (N : ℝ))
    (F2 : 200 * Real.log (N : ℝ) ≤ 101 * Real.log (t / (2 * Real.pi))) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * (t / (2 * Real.pi)) ^ (33 / 200 : ℝ) := by
  obtain ⟨T, hTd⟩ : ∃ T, T = t / (2 * Real.pi) := ⟨_, rfl⟩
  rw [← hTd] at ht F1 F2 ⊢
  have hT0 : 0 < T := by linarith only [ht]
  have ht0 : 0 < t := by
    have hq : 0 < t / (2 * Real.pi) := hTd ▸ hT0
    rcases div_pos_iff.mp hq with h | h
    · exact h.1
    · have hp := Real.pi_pos
      linarith only [h.2, hp]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlT9 : 9 * Real.log 2 ≤ Real.log T := by
    have he : (512 : ℝ) = 2 ^ 9 := by norm_num
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 512) ht
    rw [he, Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    exact hm
  have hlogT : 0 ≤ Real.log T := by linarith only [hlT9, hl2]
  have hlogN : 0 ≤ Real.log (N : ℝ) := by linarith only [F1, hlogT]
  obtain ⟨x, hx⟩ : ∃ x, x = (N : ℝ) ^ (36 / 41 : ℝ) * T ^ (-(11 / 41) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hlx : Real.log x = 36 / 41 * Real.log (N : ℝ) - 11 / 41 * Real.log T := by
    rw [hx, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow hT0]
    ring
  have hx1 : 1 ≤ x := by
    apply le_of_log_le_log one_pos hx0
    rw [Real.log_one, hlx]
    linarith only [F1, hlogT]
  have h4x : 4 * x ≤ N := by
    apply le_of_log_le_log (by positivity) hN0
    rw [Real.log_mul (by norm_num) hx0.ne', hlx,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlT9, hlogN, hl2]
  obtain ⟨H, hHd⟩ : ∃ H : ℕ, H = ⌈x⌉₊ := ⟨_, rfl⟩
  have hHx : x ≤ H := by rw [hHd]; exact Nat.le_ceil x
  have hHx2 : (H : ℝ) ≤ 2 * x := by
    have hc : (H : ℝ) < x + 1 := by rw [hHd]; exact Nat.ceil_lt_add_one hx0.le
    linarith only [hc, hx1]
  have hH1 : 1 ≤ H := by exact_mod_cast hx1.trans hHx
  have hHN : 2 * H ≤ N := by
    have hr : 2 * (H : ℝ) ≤ N := by linarith only [hHx2, h4x]
    exact_mod_cast hr
  have hw := norm_prefix_sq_le_fifthWeyl ht0 hN hL hH1 hHN
  rw [← hTd] at hw
  have hn := fifthRange_numeric hN0 hT0 hx hHx hHx2 F1 F2 hlT9
  have hpN : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpT : (T ^ (33 / 200 : ℝ)) ^ 2 = T ^ (33 / 100 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  have hs : (10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (33 / 200 : ℝ)) ^ 2 =
      10 ^ 26 * (1 * (N : ℝ) ^ (1 : ℝ) * T ^ (33 / 100 : ℝ)) := by
    rw [mul_pow, mul_pow, hpN, hpT, Real.rpow_one]
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ((hw.trans hn).trans_eq hs.symm)

/-- Every critical-line partial block in the fifth-derivative interval has the improved exponent. -/
theorem norm_criticalBlock_le_fifthRange {t : ℝ} (ht : 512 ≤ t / (2 * Real.pi))
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) (hM : M ≤ 2 * N)
    (F1 : 97 * Real.log (t / (2 * Real.pi)) ≤ 200 * Real.log (N : ℝ))
    (F2 : 200 * Real.log (N : ℝ) ≤ 101 * Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ))‖ ≤
      10 ^ 13 * (t / (2 * Real.pi)) ^ (33 / 200 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := RHTower.Sieve.dirichlet_block_sigma_bound (σ := 1 / 2) (by norm_num)
    t N M (by omega) hNM
    (10 ^ 13 * (N : ℝ) ^ (1 / 2 : ℝ) * (t / (2 * Real.pi)) ^ (33 / 200 : ℝ))
    (fun m hm1 hm2 => by
      rw [Finset.sum_Ico_eq_sum_range]
      exact norm_prefix_le_fifthRange ht hN (by omega) F1 F2)
  have he : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hN0]
    norm_num
  refine hp.trans_eq ?_
  calc _ = (10 ^ 13 * (t / (2 * Real.pi)) ^ (33 / 200 : ℝ)) *
      ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ)) := by ring
    _ = _ := by rw [he, mul_one]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.fifthRange_numeric

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_prefix_le_fifthRange

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_criticalBlock_le_fifthRange
