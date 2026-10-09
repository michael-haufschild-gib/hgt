import GaloisForLFunctions.RHTower.WeilLogShiftTwoEdgeLower
import GaloisForLFunctions.RHTower.WeilLogShiftRecoveryRowBounds
import GaloisForLFunctions.RHTower.WeilLogShiftBoundedRecoveryNoGo

/-!
# Lower envelopes for the first recovery subdiagonal

The adjacent column has twice the diagonal overlap width. Keeping its two
facing smooth factors gives an exponential lower rate pi + 20/9, up to a
quadratic prefactor. Every larger exponential rate absorbs that prefactor.
-/

open Filter Topology Set Real

noncomputable section

namespace RHTower

open WeilExcess

/-- On the first subdiagonal, the origin and positive-shift cutoff terms vanish. -/
theorem weilLogShiftRecoveryWeight_subdiagonal (n : ℕ) (hn : 2 ≤ n) :
    weilLogShiftRecoveryWeight (n + 1) n =
      2 * truncatedRiemannAutocorr (weilLogShiftRecoveryCutoff (n + 1))
        (log n - log 2) / sqrt n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : log (n + 1 + 1 : ℕ) ≤ log (n : ℝ) + log 2 := by
    rw [← log_mul hnpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    apply log_le_log (by positivity)
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith only [hnr]
  have hbound : 2 * weilLogShiftRecoveryCutoff (n + 1) ≤ log n := by
    dsimp only [weilLogShiftRecoveryCutoff]
    linarith only [hlog]
  have hc : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have h0 := truncatedRiemannAutocorr_eq_zero
    (hbound.trans (le_abs_self (log (n : ℝ))))
  have hp := truncatedRiemannAutocorr_eq_zero
    ((show 2 * weilLogShiftRecoveryCutoff (n + 1) ≤ log n + log 2 by
      linarith only [hbound, hc]).trans (le_abs_self _))
  simp only [weilLogShiftRecoveryWeight, h0, hp, mul_zero, zero_add, sub_zero]

/-- A shrinking central interval retains an explicit quadratic-prefactor
lower envelope along the first subdiagonal. -/
theorem exists_weilLogShiftRecoveryWeight_subdiagonal_polynomial_lower :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      (A / ((n : ℝ) + 1) ^ 2) * exp (-((π + 20 / 9) * ((n : ℝ) + 1))) ≤
        weilLogShiftRecoveryWeight (n + 1) n := by
  let c := π * (exp 2 - 1) / 20
  let A := (2 * π ^ 2) ^ 2 / 20 * exp (-c)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hcut : ∀ᶠ n : ℕ in atTop, 2 ≤ weilLogShiftRecoveryCutoff (n + 1) :=
    (tendsto_weilLogShiftRecoveryCutoff.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 2
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcut, eventually_ge_atTop (18 : ℕ)] with n hL hn
  let N : ℝ := n + 1
  let L := weilLogShiftRecoveryCutoff (n + 1)
  let z := log (n : ℝ) - log 2
  let d := 1 / (20 * N)
  let a := 9 / (10 * N)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp only [N]; positivity
  have hN19 : 19 ≤ N := by dsimp only [N]; linarith only [hnr]
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have ha : 0 < a := by dsimp only [a]; positivity
  have hz : 0 ≤ z := sub_nonneg.mpr
    (log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n by omega)))
  have hwidth : 1 / ((n : ℝ) + 2) ≤ L - z / 2 := by
    have h := log_le_sub_one_of_pos (div_pos hnpos hn2)
    rw [log_div hnpos.ne' hn2.ne'] at h
    have heq : (n : ℝ) / ((n : ℝ) + 2) - 1 = -2 / ((n : ℝ) + 2) := by
      field_simp [hn2.ne']; ring
    rw [heq] at h
    dsimp only [L, z, weilLogShiftRecoveryCutoff]
    push_cast
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    ring_nf at h ⊢
    linarith only [h]
  have hwidth' : 19 / (20 * N) ≤ 1 / ((n : ℝ) + 2) := by
    apply (div_le_div_iff₀ (show 0 < 20 * N by positivity) hn2).mpr
    dsimp only [N]
    linarith only [hnr]
  have hda : d + a = 19 / (20 * N) := by
    dsimp only [d, a]
    field_simp [hN.ne']; ring
  have hmargin : z / 2 + d + a ≤ L := by linarith only [hwidth, hwidth', hda]
  have hd1 : d ≤ 1 := by
    dsimp only [d]
    apply (div_le_iff₀ (show 0 < 20 * N by positivity)).mpr
    linarith only [hN19]
  have hplateau : 1 ≤ L + z / 2 - d := by
    change 2 ≤ L at hL
    linarith only [hL, hz, hd1]
  have hcentral := truncatedRiemannAutocorr_central_lower_exp_two_edges hd hz ha hmargin hplateau
  have hchord : exp (2 * d) ≤ 1 + (exp 2 - 1) * d := by
    have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (2 : ℝ))
      (show 0 ≤ 1 - d by linarith only [hd1]) hd.le (show 1 - d + d = 1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
    rw [mul_comm d 2] at h
    nlinarith only [h]
  have hexp : exp z = (n : ℝ) / 2 := by
    dsimp only [z]
    rw [exp_sub, exp_log hnpos, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hnd : (n : ℝ) * d ≤ 1 / 20 := by
    dsimp only [d]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (show 0 < 20 * N by positivity)).mpr
    dsimp only [N]
    linarith
  have hExp2 : 0 ≤ exp (2 : ℝ) - 1 := sub_nonneg.mpr
    (one_le_exp_iff.mpr (by norm_num))
  have hscale : 2 * π * exp (z + 2 * d) ≤ π * N + c := by
    rw [exp_add, hexp]
    have h₁ := mul_le_mul_of_nonneg_left hchord (Nat.cast_nonneg (α := ℝ) n)
    have h₂ := mul_le_mul_of_nonneg_left hnd hExp2
    have h₃ : (n : ℝ) * exp (2 * d) ≤ N + (exp 2 - 1) / 20 := by
      dsimp only [N]
      nlinarith only [h₁, h₂]
    have h₄ := mul_le_mul_of_nonneg_left h₃ pi_pos.le
    dsimp only [c]
    nlinarith only [h₄]
  have haexp : 2 / a = (20 / 9) * N := by
    dsimp only [a]
    field_simp [hN.ne']; ring
  have hkernel : (d * (2 * π ^ 2) ^ 2 / 2) * exp (-c) *
      exp (-((π + 20 / 9) * N)) ≤ truncatedRiemannAutocorr L z := by
    calc
      _ = (d * (2 * π ^ 2) ^ 2 / 2) * exp (-c - (π + 20 / 9) * N) := by
        rw [sub_eq_add_neg, exp_add]
        ring
      _ ≤ (d * (2 * π ^ 2) ^ 2 / 2) * exp (-2 / a - 2 * π * exp (z + 2 * d)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply exp_le_exp.mpr
        rw [neg_div, haexp]
        linarith only [hscale]
      _ ≤ _ := hcentral
  have hsqrt : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hnpos
  have hsqrtN : sqrt (n : ℝ) ≤ N := by
    have hs := sqrt_le_self_iff.mpr (Or.inr (show (1 : ℝ) ≤ n by linarith only [hnr]))
    dsimp only [N]
    linarith only [hs]
  rw [weilLogShiftRecoveryWeight_subdiagonal n (by omega)]
  change (A / N ^ 2) * exp (-((π + 20 / 9) * N)) ≤
    2 * truncatedRiemannAutocorr L z / sqrt n
  calc
    _ = (2 * ((d * (2 * π ^ 2) ^ 2 / 2) * exp (-c) *
        exp (-((π + 20 / 9) * N)))) / N := by
      dsimp only [A, d]
      field_simp [hN.ne']
    _ ≤ (2 * ((d * (2 * π ^ 2) ^ 2 / 2) * exp (-c) *
        exp (-((π + 20 / 9) * N)))) / sqrt n :=
      div_le_div_of_nonneg_left (by positivity) hsqrt hsqrtN
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkernel (by norm_num)) hsqrt.le

/-- Every rate strictly above pi+20/9 absorbs the quadratic prefactor. -/
theorem exists_weilLogShiftRecoveryWeight_subdiagonal_exponential_lower {b : ℝ}
    (hb : π + 20 / 9 < b) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      D * exp (-(b * ((n : ℝ) + 1))) ≤ weilLogShiftRecoveryWeight (n + 1) n := by
  obtain ⟨A, hA, hlower⟩ := exists_weilLogShiftRecoveryWeight_subdiagonal_polynomial_lower
  let g := b - (π + 20 / 9)
  have hg : 0 < g := sub_pos.mpr hb
  have hx : Tendsto (fun n : ℕ => g * ((n : ℝ) + 1)) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h.const_mul_atTop hg
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
      exp (-(g * ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hx).const_mul (1 / g ^ 2)
    convert h using 1
    · funext n
      dsimp only [Function.comp_def]
      field_simp [hg.ne']
    · simp only [mul_zero]
  refine ⟨A, hA, ?_⟩
  filter_upwards [hlower, (tendsto_order.mp hlim).2 1 (by norm_num)] with n hn hs
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hsmall : exp (-(g * ((n : ℝ) + 1))) ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    nlinarith only [hs]
  calc
    _ = A * (exp (-(g * ((n : ℝ) + 1))) *
        exp (-((π + 20 / 9) * ((n : ℝ) + 1)))) := by
      rw [← exp_add]
      congr 2
      dsimp only [g]
      ring
    _ ≤ A * ((1 / ((n : ℝ) + 1) ^ 2) *
        exp (-((π + 20 / 9) * ((n : ℝ) + 1)))) := by gcongr
    _ = (A / ((n : ℝ) + 1) ^ 2) * exp (-((π + 20 / 9) * ((n : ℝ) + 1))) := by ring
    _ ≤ _ := hn

/-- Eventually, the adjacent coefficient exceeds twice exp(n+1) times the
diagonal coefficient. This comparison is unconditional on the native mesh. -/
theorem eventually_weilLogShiftRecoveryWeight_subdiagonal_amplifies :
    ∀ᶠ n : ℕ in atTop,
      2 * exp ((n : ℝ) + 1) * weilLogShiftRecoveryWeight (n + 1) (n + 1) ≤
        weilLogShiftRecoveryWeight (n + 1) n := by
  let a := 99 * π / 100
  let b := π + 9 / 4
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hapi : a < π := by dsimp only [a]; linarith only [pi_pos]
  obtain ⟨C, hC, hupper⟩ := exists_weilLogShiftRecoveryWeight_row_exponential_bound ha0 hapi
  obtain ⟨D, hD, hlower⟩ := exists_weilLogShiftRecoveryWeight_subdiagonal_exponential_lower
    (b := b) (by dsimp only [b]; linarith)
  let g := a + 3 - b
  have hg : 0 < g := by dsimp only [g, a, b]; linarith only [pi_lt_four]
  have hx : Tendsto (fun n : ℕ => g * ((n : ℝ) + 1)) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h.const_mul_atTop hg
  have hlim : Tendsto (fun n : ℕ => (2 * C / D) * exp (-(g * ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (tendsto_exp_neg_atTop_nhds_zero.comp hx).const_mul (2 * C / D)
  filter_upwards [hlower, (tendsto_order.mp hlim).2 1 (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with n hn hs hn2
  have hdiag : weilLogShiftRecoveryWeight (n + 1) (n + 1) ≤
      C * exp (-((a + 4) * ((n : ℝ) + 1))) := by
    have h := hupper (n + 1) (n + 1) (by omega) le_rfl
    have heq : -a * (n + 1 : ℕ) - 4 * (n + 1 : ℕ) /
        (((n + 1 : ℕ) : ℝ) + 1 - (n + 1 : ℕ)) = -((a + 4) * ((n : ℝ) + 1)) := by
      push_cast
      ring
    rw [heq] at h
    exact (le_abs_self _).trans h
  have hsmall : 2 * C * exp (-(g * ((n : ℝ) + 1))) ≤ D := by
    have hdiv : (2 * C * exp (-(g * ((n : ℝ) + 1)))) / D ≤ 1 := by
      calc
        _ = (2 * C / D) * exp (-(g * ((n : ℝ) + 1))) := by ring
        _ ≤ _ := hs.le
    simpa only [one_mul] using (div_le_iff₀ hD).mp hdiv
  calc
    _ ≤ 2 * exp ((n : ℝ) + 1) * (C * exp (-((a + 4) * ((n : ℝ) + 1)))) :=
      mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = (2 * C * exp (-(g * ((n : ℝ) + 1)))) * exp (-(b * ((n : ℝ) + 1))) := by
      have heq : exp ((n : ℝ) + 1) * exp (-((a + 4) * ((n : ℝ) + 1))) =
          exp (-(g * ((n : ℝ) + 1))) * exp (-(b * ((n : ℝ) + 1))) := by
        rw [← exp_add, ← exp_add]
        congr 1
        dsimp only [g]
        ring
      calc
        _ = (2 * C) * (exp ((n : ℝ) + 1) * exp (-((a + 4) * ((n : ℝ) + 1)))) := by ring
        _ = _ := by rw [heq]; ring
    _ ≤ D * exp (-(b * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right hsmall (exp_pos _).le
    _ ≤ _ := hn

/-- Beyond a common threshold, each older entry, damped by the accumulated
column-growth factor, costs at most one row-length share of half the adjacent
entry. Summing this estimate will control the whole older tail. -/
theorem exists_weilLogShiftRecoveryWeight_tail_dominance_threshold :
    ∃ J : ℕ, 625 ≤ J ∧ ∀ n j : ℕ, J ≤ n → J ≤ j → j + 1 ≤ n →
      ((n : ℝ) + 1) * |weilLogShiftRecoveryWeight (n + 1) j| *
        exp (-((j : ℝ) + 1) * ((n : ℝ) - j)) ≤
          weilLogShiftRecoveryWeight (n + 1) n / 2 := by
  let a := 99 * π / 100
  let b := π + 9 / 4
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have hapi : a < π := by dsimp only [a]; linarith only [pi_pos]
  obtain ⟨C, hC, hupper⟩ := exists_weilLogShiftRecoveryWeight_row_exponential_bound ha0 hapi
  obtain ⟨D, hD, hlower⟩ := exists_weilLogShiftRecoveryWeight_subdiagonal_exponential_lower
    (b := b) (by dsimp only [b]; linarith)
  have hx : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / 100) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert h.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 100) using 1
    funext n
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * C *
      exp (-((n : ℝ) + 1) / 100)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx).const_mul (100 * C)
    convert h using 1
    · funext n
      simp only [Function.comp_def, pow_one, neg_div]
      ring
    · simp only [mul_zero]
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlower.and ((tendsto_order.mp hlim).2 (D / 2) (by positivity)))
  refine ⟨max 625 N, le_max_left _ _, fun n j hn hj hjn => ?_⟩
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hlo, hsmall⟩ := hN n hnN
  have hj625 : 625 ≤ j := (le_max_left _ _).trans hj
  have hjR : (625 : ℝ) ≤ j := by exact_mod_cast hj625
  have hjnR : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
  have hgap := weilLogShiftRecovery_tail_exponent_gap
    (n := (n : ℝ) + 1) (j := j) (by linarith only [hjnR]) hjR
  have hrow := hupper (n + 1) j (by omega) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hrow
  have hterm : |weilLogShiftRecoveryWeight (n + 1) j| *
      exp (-((j : ℝ) + 1) * ((n : ℝ) - j)) ≤
        C * exp (-(b * ((n : ℝ) + 1)) - ((n : ℝ) + 1) / 100) := by
    calc
      _ ≤ (C * exp (-a * j - 4 * j / ((n : ℝ) + 1 + 1 - j))) *
          exp (-((j : ℝ) + 1) * ((n : ℝ) - j)) :=
        mul_le_mul_of_nonneg_right hrow (exp_pos _).le
      _ = C * exp ((-a * j - 4 * j / ((n : ℝ) + 1 + 1 - j)) +
          (-((j : ℝ) + 1) * ((n : ℝ) - j))) := by rw [exp_add]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply exp_le_exp.mpr
        dsimp only [a, b]
        nlinarith only [hgap]
  calc
    _ = ((n : ℝ) + 1) * (|weilLogShiftRecoveryWeight (n + 1) j| *
        exp (-((j : ℝ) + 1) * ((n : ℝ) - j))) := by ring
    _ ≤ ((n : ℝ) + 1) * (C * exp (-(b * ((n : ℝ) + 1)) - ((n : ℝ) + 1) / 100)) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (((n : ℝ) + 1) * C * exp (-((n : ℝ) + 1) / 100)) *
        exp (-(b * ((n : ℝ) + 1))) := by
      rw [sub_eq_add_neg, exp_add, neg_div]
      ring
    _ ≤ (D / 2) * exp (-(b * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right hsmall.le (exp_pos _).le
    _ ≤ _ := by linarith only [hlo]

end RHTower
