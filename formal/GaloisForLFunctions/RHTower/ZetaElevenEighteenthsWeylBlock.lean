import GaloisForLFunctions.RHTower.ZetaWeylCorrelationBound
import GaloisForLFunctions.RHTower.Sieve.LogPhaseBlock
import GaloisForLFunctions.RHTower.Sieve.WeylDifferencing

/-!
# The `A·B·A²B` block: Weyl differencing, then `B`, then the fourth-derivative test

For the Dirichlet prefix `P = Σ_{j<L} (N + j)^{−it}`, `L ≤ N`, and a Weyl window `H ≤ N/2`, with
`T = t/2π` (`norm_prefix_sq_le_weyl`):

  `‖P‖² ≤ H² + 4N²/H + 4·10¹⁰ N Q`,
  `Q = (TH)^{2/7} + (TH)^{13/28}N^{−1/2} + TH/N² + (N³/T)^{1/2} + (TH)^{2/5}N^{−2/5} + N^{2/3}`.

**Proof.**  `weyl_vdc` reduces `‖P‖²` to the correlations `Σ_n e(−T(log(N + n + h) − log(N + n)))`,
`1 ≤ h < H`.  Each is bounded by `10¹⁰ Q` (`norm_sum_diffLog_le`):
* if `(Th)³ ≥ 5N⁷`, by the `B` regime (`norm_sum_diffLog_le_B`), every term being monotone in
  `X = Th ∈ [T, TH]`;
* otherwise by the second-derivative test (`norm_sum_diffLog_le_second`),
  `50((X/N)^{1/2} + (N³/X)^{1/2})`, with `(X/N)^{1/2} ≤ 2N^{2/3}` since `X³ < 5N⁷`.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The second-derivative regime -/

/-- **The differenced sum in the second-derivative regime.**  For `X = Th ≤ N³`,
`‖Σ_{n<L} e(T(log(N + n + h) − log(N + n)))‖ ≤ 50((X/N)^{1/2} + (N³/X)^{1/2})`. -/
theorem norm_sum_diffLog_le_second {T : ℝ} (hT : 0 < T) {N L h : ℕ} (hN : 2 ≤ N) (hh : 1 ≤ h)
    (h2h : 2 * h ≤ N) (hL : L ≤ N) (hX : T * h ≤ (N : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log ((N : ℝ) + n + h)
        - Real.log ((N : ℝ) + n))) : ℝ) : ℂ) * I)‖
      ≤ 50 * ((T * h / N) ^ (1 / 2 : ℝ) + ((N : ℝ) ^ 3 / (T * h)) ^ (1 / 2 : ℝ)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = N := ⟨_, rfl⟩
  obtain ⟨hR, hhR⟩ : ∃ r : ℝ, r = h := ⟨_, rfl⟩
  rw [← hn, ← hhR]
  rw [← hn, ← hhR] at hX
  have hn2 : 2 ≤ n := by rw [hn]; exact_mod_cast hN
  have hn0 : 0 < n := by linarith
  have hR1 : 1 ≤ hR := by rw [hhR]; exact_mod_cast hh
  have hR0 : 0 < hR := by linarith
  have hRn : 2 * hR ≤ n := by rw [hn, hhR]; exact_mod_cast h2h
  obtain ⟨X, hXd⟩ : ∃ X, X = T * hR := ⟨_, rfl⟩
  rw [← hXd]
  rw [← hXd] at hX
  have hX0 : 0 < X := by rw [hXd]; positivity
  have hRHS : 0 ≤ 50 * ((X / n) ^ (1 / 2 : ℝ) + (n ^ 3 / X) ^ (1 / 2 : ℝ)) := by positivity
  rcases Nat.eq_zero_or_pos L with rfl | hL1
  · simpa using hRHS
  -- the curvature window
  obtain ⟨lam, hlam⟩ : ∃ l, l = 16 * X / (125 * n ^ 3) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one (by positivity)]; nlinarith [pow_pos hn0 3]
  have hspan : ∀ x ∈ Set.Icc n (n + ((L - 1 : ℕ) : ℝ)), 0 < x ∧ n ≤ x ∧ x ≤ 2 * n := by
    intro x hx
    have hL' : ((L - 1 : ℕ) : ℝ) ≤ n := by
      rw [hn]; exact_mod_cast (show L - 1 ≤ N by omega)
    exact ⟨by linarith [hx.1], hx.1, by linarith [hx.2]⟩
  have h2 := RHTower.Sieve.second_derivative_test' (diffPhase T hR 0) (diffPhase1 T hR 0)
    (diffPhase2 T hR) n L hL1 (lam := lam) (hgrow := 125 / 8) hlam0 hlam1
    (fun x hx => hasDerivAt_diffPhase (hspan x hx).1 hR0.le)
    (fun x hx => hasDerivAt_diffPhase1 (hspan x hx).1 hR0.le)
    (fun x hx => by
      obtain ⟨hx0, _, hx2⟩ := hspan x hx
      refine le_trans ?_ (diffPhase2_ge hT.le hx0 hR0.le)
      have e1 : (x + hR) ^ 3 ≤ (5 / 2 * n) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      rw [hlam, mul_assoc 2 T hR, ← hXd]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hn0 3])
    (fun x hx => by
      obtain ⟨hx0, hx1, _⟩ := hspan x hx
      refine (diffPhase2_le hT.le hx0 hR0.le).trans ?_
      have e1 : n ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hn0.le hx1 3
      have e : 125 / 8 * lam = 2 * X / n ^ 3 := by rw [hlam]; field_simp; ring
      rw [e, mul_assoc 2 T hR, ← hXd]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) e1)
  have hsum : ∑ i ∈ Finset.range L,
      Complex.exp (((2 * Real.pi * diffPhase T hR 0 (n + i) : ℝ) : ℂ) * I)
      = ∑ i ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log (n + i + hR)
        - Real.log (n + i))) : ℝ) : ℂ) * I) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [diffPhase, zero_mul, add_zero]
  rw [hsum] at h2
  refine h2.trans ?_
  have hLn : (L : ℝ) ≤ n := by rw [hn]; exact_mod_cast hL
  have hsq0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  -- `125 n √λ = √(2000 X/n)` and `12/√λ = √(1125 n³/X)`
  have e1 : 125 * n * Real.sqrt lam = Real.sqrt 2000 * Real.sqrt (X / n) := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [show 125 * n * Real.sqrt lam = Real.sqrt ((125 * n) ^ 2 * lam) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    congr 1
    rw [hlam]; field_simp; ring
  have e2 : 12 / Real.sqrt lam = Real.sqrt 1125 * Real.sqrt (n ^ 3 / X) := by
    rw [← Real.sqrt_mul (by norm_num), div_eq_iff hsq0.ne']
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (12 : ℝ) = Real.sqrt 144 by
      rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    congr 1
    rw [hlam]; field_simp; ring
  have hs1 : Real.sqrt 2000 ≤ 45 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2 : Real.sqrt 1125 ≤ 34 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hA : 8 * (L : ℝ) * (125 / 8) * Real.sqrt lam ≤ 45 * (X / n) ^ (1 / 2 : ℝ) := by
    have : 8 * (L : ℝ) * (125 / 8) * Real.sqrt lam ≤ 125 * n * Real.sqrt lam := by
      have := mul_le_mul_of_nonneg_right hLn hsq0.le
      nlinarith
    rw [e1, ← Real.sqrt_eq_rpow] at *
    have := mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg (X / n))
    linarith
  have hB : 12 / Real.sqrt lam ≤ 34 * (n ^ 3 / X) ^ (1 / 2 : ℝ) := by
    rw [e2, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg _)
  have hpos1 : 0 ≤ (X / n) ^ (1 / 2 : ℝ) := by positivity
  have hpos2 : 0 ≤ (n ^ 3 / X) ^ (1 / 2 : ℝ) := by positivity
  linarith

/-! ## Every shift -/

/-- The common bound `Q` for all Weyl shifts `h ≤ H`. -/
def diffLogQ (T : ℝ) (N H : ℕ) : ℝ :=
  (T * H) ^ (2 / 7 : ℝ) + (T * H) ^ (13 / 28 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ) + T * H / (N : ℝ) ^ 2
    + ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) + (T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ)
    + (N : ℝ) ^ (2 / 3 : ℝ)

theorem diffLogQ_nonneg {T : ℝ} (hT : 0 ≤ T) (N H : ℕ) : 0 ≤ diffLogQ T N H := by
  unfold diffLogQ; positivity

/-- `(X/N)^{1/2} ≤ 2N^{2/3}` when `X³ ≤ 5N⁷`. -/
theorem sqrt_ratio_le_of_cube_le {X n : ℝ} (hX : 0 ≤ X) (hn : 0 < n) (h : X ^ 3 ≤ 5 * n ^ 7) :
    (X / n) ^ (1 / 2 : ℝ) ≤ 2 * n ^ (2 / 3 : ℝ) := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (6 : ℕ) ≠ 0)).mp ?_
  have e1 : ((X / n) ^ (1 / 2 : ℝ)) ^ (6 : ℕ) = (X / n) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (2 * n ^ (2 / 3 : ℝ)) ^ (6 : ℕ) = 64 * n ^ 4 := by
    rw [mul_pow, ← Real.rpow_natCast (n ^ (2 / 3 : ℝ)), ← Real.rpow_mul hn.le]; norm_num
  rw [e1, e2, div_pow, div_le_iff₀ (by positivity)]
  nlinarith [pow_pos hn 7]

/-- **Every Weyl shift.**  For `3 ≤ N`, `1 ≤ h ≤ H`, `2h ≤ N`, `L ≤ N`:
`‖Σ_{n<L} e(T(log(N + n + h) − log(N + n)))‖ ≤ 10¹⁰ Q`. -/
theorem norm_sum_diffLog_le {T : ℝ} (hT : 0 < T) {N L h H : ℕ} (hN : 3 ≤ N) (hh : 1 ≤ h)
    (hhH : h ≤ H) (h2h : 2 * h ≤ N) (hL : L ≤ N) :
    ‖∑ n ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log ((N : ℝ) + n + h)
        - Real.log ((N : ℝ) + n))) : ℝ) : ℂ) * I)‖ ≤ 10 ^ 10 * diffLogQ T N H := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hXY : T * h ≤ T * H := mul_le_mul_of_nonneg_left (by exact_mod_cast hhH) hT.le
  have hTX : T ≤ T * h := by nlinarith
  have hX0 : 0 < T * h := by positivity
  have hsqrt : ((N : ℝ) ^ 3 / (T * h)) ^ (1 / 2 : ℝ) ≤ ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left (by positivity) hT hTX) (by norm_num)
  have hQ := diffLogQ_nonneg hT.le N H
  by_cases hB : 5 * (N : ℝ) ^ 7 ≤ (T * h) ^ 3
  · refine (norm_sum_diffLog_le_B hT (by omega) hh h2h hL hB).trans ?_
    have m1 : (T * h) ^ (2 / 7 : ℝ) ≤ (T * H) ^ (2 / 7 : ℝ) :=
      Real.rpow_le_rpow hX0.le hXY (by norm_num)
    have m2 : (T * h) ^ (13 / 28 : ℝ) ≤ (T * H) ^ (13 / 28 : ℝ) :=
      Real.rpow_le_rpow hX0.le hXY (by norm_num)
    have m3 : T * h / (N : ℝ) ^ 2 ≤ T * H / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hXY (by positivity)
    have m5 : (T * h) ^ (2 / 5 : ℝ) ≤ (T * H) ^ (2 / 5 : ℝ) :=
      Real.rpow_le_rpow hX0.le hXY (by norm_num)
    have hN1 : 0 ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    have hN2 : 0 ≤ (N : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
    have hN3 : 0 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by positivity
    have m2' := mul_le_mul_of_nonneg_right m2 hN1
    have m5' := mul_le_mul_of_nonneg_right m5 hN2
    unfold diffLogQ
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    linarith
  · push Not at hB
    have hXN : T * h ≤ (N : ℝ) ^ 3 := by
      have h9 : (T * h) ^ 3 ≤ ((N : ℝ) ^ 3) ^ 3 := by
        have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
        have hN2 : (9 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        have h7 : (0 : ℝ) ≤ (N : ℝ) ^ 7 := by positivity
        calc (T * h) ^ 3 ≤ 5 * (N : ℝ) ^ 7 := hB.le
          _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 7 := by nlinarith
          _ = ((N : ℝ) ^ 3) ^ 3 := by ring
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h9
    refine (norm_sum_diffLog_le_second hT (by omega) hh h2h hL hXN).trans ?_
    have hr := sqrt_ratio_le_of_cube_le hX0.le hn0 hB.le
    unfold diffLogQ
    have : 0 ≤ (T * H) ^ (2 / 7 : ℝ) + (T * H) ^ (13 / 28 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ)
        + T * H / (N : ℝ) ^ 2 + (T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
    have hN3 : 0 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by positivity
    have hs0 : 0 ≤ ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) := by positivity
    linarith

/-! ## The Weyl assembly -/

theorem norm_natCast_cpow_neg_I_mul_le {t : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rw [RHTower.Sieve.natCast_cpow_neg_I_mul t n hn, Complex.norm_exp_ofReal_mul_I]

/-- **The Weyl-windowed prefix bound.**  See the module docstring. -/
theorem norm_prefix_sq_le_weyl {t : ℝ} (ht : 0 < t) {N L H : ℕ} (hN : 3 ≤ N) (hL : L ≤ N)
    (hH1 : 1 ≤ H) (hHN : 2 * H ≤ N) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ (H : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 / H
        + 4 * 10 ^ 10 * N * diffLogQ (t / (2 * Real.pi)) N H := by
  have hT : 0 < t / (2 * Real.pi) := by positivity
  have hQ := diffLogQ_nonneg hT.le N H
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  set a : ℕ → ℂ := fun j => ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ))) with ha
  have hanorm : ∀ j, ‖a j‖ ≤ 1 := fun j => norm_natCast_cpow_neg_I_mul_le (by omega)
  have hextra : 0 ≤ 4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 10 * N * diffLogQ (t / (2 * Real.pi)) N H := by
    positivity
  by_cases hLH : L < H
  · have hP : ‖∑ j ∈ Finset.range L, a j‖ ≤ H := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => hanorm j).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast hLH.le
    have : ‖∑ j ∈ Finset.range L, a j‖ ^ 2 ≤ (H : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hP 2
    linarith
  push Not at hLH
  have hW := RHTower.Sieve.weyl_vdc a hanorm L H hH1 hLH
  -- each correlation
  have hcorr : ∀ h ∈ Finset.Icc 1 (H - 1),
      ‖RHTower.Sieve.weylCorr a L h‖ ≤ 10 ^ 10 * diffLogQ (t / (2 * Real.pi)) N H := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have e : RHTower.Sieve.weylCorr a L h = ∑ n ∈ Finset.range (L - h),
        Complex.exp (((-(2 * Real.pi * (t / (2 * Real.pi) * (Real.log ((N : ℝ) + n + h)
          - Real.log ((N : ℝ) + n))))) : ℝ) * I) := by
      unfold RHTower.Sieve.weylCorr
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [ha]
      rw [RHTower.Sieve.natCast_cpow_neg_I_mul t _ (by omega),
        RHTower.Sieve.natCast_cpow_neg_I_mul t _ (by omega), ← Complex.exp_conj, map_mul,
        Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
      congr 1
      simp only [RHTower.Sieve.logPhase]
      push_cast
      field_simp
      ring
    rw [e, norm_sum_cexp_neg (Finset.range (L - h)) (fun n => 2 * Real.pi * (t / (2 * Real.pi)
      * (Real.log ((N : ℝ) + n + h) - Real.log ((N : ℝ) + n))))]
    exact norm_sum_diffLog_le hT hN hh.1 (by omega) (by omega) (by omega)
  have hsum : ∑ h ∈ Finset.Icc 1 (H - 1), ‖RHTower.Sieve.weylCorr a L h‖
      ≤ H * (10 ^ 10 * diffLogQ (t / (2 * Real.pi)) N H) := by
    refine (Finset.sum_le_sum hcorr).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : H + 1 - 1 - 1 ≤ H := by omega
    exact_mod_cast this
  have hLN : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hmain : (H : ℝ) * ‖∑ n ∈ Finset.range L, a n‖ ^ 2
      ≤ 4 * N * (N + H * (10 ^ 10 * diffLogQ (t / (2 * Real.pi)) N H)) := by
    refine hW.trans ?_
    have h1 : (L : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖RHTower.Sieve.weylCorr a L h‖
        ≤ N + H * (10 ^ 10 * diffLogQ (t / (2 * Real.pi)) N H) := by linarith
    have h2 : 0 ≤ (L : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖RHTower.Sieve.weylCorr a L h‖ := by
      positivity
    have := mul_le_mul (mul_le_mul_of_nonneg_left hLN (by norm_num : (0 : ℝ) ≤ 4)) h1 h2
      (by positivity)
    linarith
  have hdiv : ‖∑ n ∈ Finset.range L, a n‖ ^ 2
      ≤ 4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 10 * N * diffLogQ (t / (2 * Real.pi)) N H := by
    rw [← mul_le_mul_iff_of_pos_left hH0]
    calc (H : ℝ) * ‖∑ n ∈ Finset.range L, a n‖ ^ 2
        ≤ 4 * N * (N + H * (10 ^ 10 * diffLogQ (t / (2 * Real.pi)) N H)) := hmain
      _ = H * (4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 10 * N * diffLogQ (t / (2 * Real.pi)) N H) := by
        field_simp
  have : (0 : ℝ) ≤ (H : ℝ) ^ 2 := by positivity
  linarith

/-! ## The prefix bound on `t^{5/13} ≤ N ≤ t^{1/2}` -/

/-- `log (c N^a T^b) = log c + a log N + b log T`. -/
theorem log_mono_eq {c N T : ℝ} (hc : 0 < c) (hN : 0 < N) (hT : 0 < T) (a b : ℝ) :
    Real.log (c * N ^ a * T ^ b) = Real.log c + a * Real.log N + b * Real.log T := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hc.ne' (by positivity),
    Real.log_rpow hN, Real.log_rpow hT]

theorem le_of_log_le_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : Real.log x ≤ Real.log y) :
    x ≤ y := (Real.log_le_log_iff hx hy).mp h

/-- The canonical monomials of the block exponents, compared through their logarithms. -/
theorem mono_le_of_log {c c' N T a b a' b' : ℝ} (hc : 0 < c) (hc' : 0 < c') (hN : 0 < N)
    (hT : 0 < T)
    (h : Real.log c + a * Real.log N + b * Real.log T
      ≤ Real.log c' + a' * Real.log N + b' * Real.log T) :
    c * N ^ a * T ^ b ≤ c' * N ^ a' * T ^ b' := by
  refine le_of_log_le_log (by positivity) (by positivity) ?_
  rw [log_mono_eq hc hN hT, log_mono_eq hc' hN hT]
  exact h

/-- **The bookkeeping of the `B` range.**  With `x = N^{7/9}T^{−2/9} ≤ H ≤ 2x`,
`5 log T ≤ 13 log N` and `2 log N ≤ log 7 + log T`, every term of `norm_prefix_sq_le_weyl` is a
multiple of `N^{11/9}T^{2/9}`. -/
theorem BRange_numeric {N H : ℕ} {T x : ℝ} (hN0 : (0 : ℝ) < N) (hT0 : 0 < T)
    (hx : x = (N : ℝ) ^ (7 / 9 : ℝ) * T ^ (-(2 / 9) : ℝ)) (hHx : x ≤ H) (hHx2 : (H : ℝ) ≤ 2 * x)
    (F1 : 5 * Real.log T ≤ 13 * Real.log (N : ℝ))
    (F2 : 2 * Real.log (N : ℝ) ≤ Real.log 7 + Real.log T)
    (hlT9 : 9 * Real.log 2 ≤ Real.log T) (hl7 : Real.log 7 ≤ 6) (hl70 : 0 < Real.log 7)
    (hl2 : 0.69 < Real.log 2) :
    (H : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 / H + 4 * 10 ^ 10 * N * diffLogQ T N H
      ≤ 10 ^ 12 * (1 * (N : ℝ) ^ (11 / 9 : ℝ) * T ^ (2 / 9 : ℝ)) := by
  have hx0 : 0 < x := by rw [hx]; positivity
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le hx0 hHx
  obtain ⟨M, hM⟩ : ∃ M, M = 1 * (N : ℝ) ^ (11 / 9 : ℝ) * T ^ (2 / 9 : ℝ) := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by rw [hM]; positivity
  -- `TH ≤ Y = 2N^{7/9}T^{7/9}`
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 * (N : ℝ) ^ (7 / 9 : ℝ) * T ^ (7 / 9 : ℝ) := ⟨_, rfl⟩
  have hTH : T * H ≤ Y := by
    have e : T * (2 * x) = Y := by
      rw [hx, hY]
      have : T * T ^ (-(2 / 9) : ℝ) = T ^ (7 / 9 : ℝ) := by
        rw [← Real.rpow_one_add' hT0.le (by norm_num)]; norm_num
      calc T * (2 * ((N : ℝ) ^ (7 / 9 : ℝ) * T ^ (-(2 / 9) : ℝ)))
          = 2 * (N : ℝ) ^ (7 / 9 : ℝ) * (T * T ^ (-(2 / 9) : ℝ)) := by ring
        _ = _ := by rw [this]
    rw [← e]; exact mul_le_mul_of_nonneg_left hHx2 hT0.le
  have hTH0 : 0 ≤ T * H := by positivity
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hlY : Real.log Y = Real.log 2 + 7 / 9 * Real.log (N : ℝ) + 7 / 9 * Real.log T := by
    rw [hY]; exact log_mono_eq two_pos hN0 hT0 _ _
  have hlM : Real.log M = 11 / 9 * Real.log (N : ℝ) + 2 / 9 * Real.log T := by
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
      linarith
    nlinarith
  have t2 : 4 * (N : ℝ) ^ 2 / H ≤ 4 * M := by
    rw [div_le_iff₀ hH0]
    have e : (N : ℝ) ^ 2 ≤ M * x := by
      refine le_of_log_le_log (by positivity) (by positivity) ?_
      rw [Real.log_pow, Real.log_mul hM0.ne' hx0.ne', hlM, hx,
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow hT0]
      push_cast
      linarith
    nlinarith
  have q1 : (N : ℝ) * (T * H) ^ (2 / 7 : ℝ) ≤ 2 * M := by
    refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hTH0 hTH (by norm_num))
      hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_rpow hY0, hlY, hlc 2 two_pos, hlM]
    linarith
  have q2 : (N : ℝ) * ((T * H) ^ (13 / 28 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ)) ≤ 2 * M := by
    have h1 : (T * H) ^ (13 / 28 : ℝ) ≤ Y ^ (13 / 28 : ℝ) :=
      Real.rpow_le_rpow hTH0 hTH (by norm_num)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity))
      hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hY0, Real.log_rpow hN0, hlY, hlc 2 two_pos, hlM]
    linarith
  have q3 : (N : ℝ) * (T * H / (N : ℝ) ^ 2) ≤ 2 * M := by
    have h1 : T * H / (N : ℝ) ^ 2 ≤ Y / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hTH (by positivity)
    refine (mul_le_mul_of_nonneg_left h1 hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_div hY0.ne' (by positivity), Real.log_pow,
      hlY, hlc 2 two_pos, hlM]
    push_cast
    linarith
  have q4 : (N : ℝ) * ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ) ≤ 7 * M := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_div (by positivity) hT0.ne', Real.log_pow, hlc 7 (by norm_num), hlM]
    push_cast
    linarith
  have q5 : (N : ℝ) * ((T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ)) ≤ 2 * M := by
    have h1 : (T * H) ^ (2 / 5 : ℝ) ≤ Y ^ (2 / 5 : ℝ) :=
      Real.rpow_le_rpow hTH0 hTH (by norm_num)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity))
      hN0.le).trans ?_
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hY0, Real.log_rpow hN0, hlY, hlc 2 two_pos, hlM]
    linarith
  have q6 : (N : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) ≤ 7 * M := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_rpow hN0, hlc 7 (by norm_num), hlM]
    linarith
  have hQ : (N : ℝ) * diffLogQ T N H ≤ 22 * M := by
    have e : (N : ℝ) * diffLogQ T N H = (N : ℝ) * (T * H) ^ (2 / 7 : ℝ)
          + (N : ℝ) * ((T * H) ^ (13 / 28 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ))
          + (N : ℝ) * (T * H / (N : ℝ) ^ 2) + (N : ℝ) * ((N : ℝ) ^ 3 / T) ^ (1 / 2 : ℝ)
          + (N : ℝ) * ((T * H) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ))
          + (N : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by rw [diffLogQ]; ring
    rw [e]
    linarith
  have e : 4 * 10 ^ 10 * (N : ℝ) * diffLogQ T N H = 4 * 10 ^ 10 * ((N : ℝ) * diffLogQ T N H) := by
    ring
  rw [e]
  have h3 := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 4 * 10 ^ 10)
  linarith only [t1, t2, h3, hM0]

/-- **The `B`-range prefix bound.**  For `t ≥ 1024π`, `t⁵ ≤ N¹³`, `N² ≤ t` and `L ≤ N`,
`‖Σ_{j<L} (N + j)^{−it}‖ ≤ 10⁶ N^{11/18} t^{1/9}`, via `norm_prefix_sq_le_weyl` with
`H = ⌈N^{7/9}T^{−2/9}⌉`, `T = t/2π`. -/
theorem norm_prefix_le_BRange {t : ℝ} (ht : 1024 * Real.pi ≤ t) {N L : ℕ}
    (h5 : t ^ 5 ≤ (N : ℝ) ^ 13) (h2 : (N : ℝ) ^ 2 ≤ t) (hL : L ≤ N) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 10 ^ 6 * (N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ) := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have ht0 : 0 < t := by linarith
  obtain ⟨T, hTd⟩ : ∃ T, T = t / (2 * Real.pi) := ⟨_, rfl⟩
  have hT512 : 512 ≤ T := by rw [hTd, le_div_iff₀ (by positivity)]; linarith
  have hT0 : 0 < T := by linarith
  have hTt : T ≤ t := by rw [hTd, div_le_iff₀ (by positivity)]; nlinarith
  have htT : t ≤ 7 * T := by rw [hTd]; field_simp; nlinarith
  -- `N ≥ 4`
  have hN4 : (4 : ℝ) ≤ N := by
    by_contra hlt
    push Not at hlt
    have h1 : (N : ℝ) ^ 13 ≤ 4 ^ 13 := pow_le_pow_left₀ (by positivity) hlt.le 13
    have h2' : (3000 : ℝ) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    norm_num at h1 h2'
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN3 : 3 ≤ N := by exact_mod_cast (show (3 : ℝ) ≤ N by linarith)
  -- logarithmic facts
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl7 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7); linarith
  have hl70 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have hlN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hlT9 : 9 * Real.log 2 ≤ Real.log T := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  have F1 : 5 * Real.log T ≤ 13 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity) ((pow_le_pow_left₀ hT0.le hTt 5).trans h5)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have F2 : 2 * Real.log (N : ℝ) ≤ Real.log 7 + Real.log T := by
    have h := Real.log_le_log (by positivity) (h2.trans htT)
    rw [Real.log_pow, Real.log_mul (by norm_num) hT0.ne'] at h
    push_cast at h
    linarith
  -- the Weyl window
  obtain ⟨x, hx⟩ : ∃ x, x = (N : ℝ) ^ (7 / 9 : ℝ) * T ^ (-(2 / 9) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : 1 ≤ x := by
    refine (Real.log_nonneg_iff hx0).mp ?_
    rw [hx, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow hT0]
    linarith
  have hx4 : x ≤ N / 4 := by
    refine le_of_log_le_log hx0 (by positivity) ?_
    rw [hx, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow hT0,
      Real.log_div hN0.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  obtain ⟨H, hH⟩ : ∃ H : ℕ, H = ⌈x⌉₊ := ⟨_, rfl⟩
  have hHx : x ≤ H := by rw [hH]; exact Nat.le_ceil x
  have hHx2 : (H : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one hx0.le; rw [← hH] at this; linarith
  have hH1 : 1 ≤ H := by exact_mod_cast (show (1 : ℝ) ≤ H by linarith)
  have hHN : 2 * H ≤ N := by
    have : (2 * H : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hW := norm_prefix_sq_le_weyl ht0 hN3 hL hH1 hHN
  rw [← hTd] at hW
  have hnum := BRange_numeric hN0 hT0 hx hHx hHx2 F1 F2 hlT9 hl7 hl70 hl2
  have hsq := hW.trans hnum
  -- square root
  have hMt : 1 * (N : ℝ) ^ (11 / 9 : ℝ) * T ^ (2 / 9 : ℝ)
      ≤ ((N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ)) ^ 2 := by
    have e : ((N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ)) ^ 2
        = (N : ℝ) ^ (11 / 9 : ℝ) * t ^ (2 / 9 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul hN0.le,
        ← Real.rpow_mul ht0.le]
      norm_num
    rw [e, one_mul]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT0.le hTt (by norm_num)) (by positivity)
  have hfin : ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2
      ≤ (10 ^ 6 * (N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ)) ^ 2 := by
    have e : (10 ^ 6 * (N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ)) ^ 2
        = 10 ^ 12 * ((N : ℝ) ^ (11 / 18 : ℝ) * t ^ (1 / 9 : ℝ)) ^ 2 := by ring
    rw [e]
    exact hsq.trans (mul_le_mul_of_nonneg_left hMt (by positivity))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hfin

end

end RHTower
