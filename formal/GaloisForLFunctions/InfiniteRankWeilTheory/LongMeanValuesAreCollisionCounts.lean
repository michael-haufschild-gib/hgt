import Mathlib

/-!
# Long mean values are collision counts

The mean-value theorem `∫_0^T |Σ_{n≤N} a_n n^{−it}|² dt = Σ|a_n|²(T + O(n))` has a main term only
while the length `N` is below the height `T`. Beyond the height the off-diagonal pairs `m ≠ n` with
`|log(n/m)| ≲ 1/T` — the **collisions** — take over. With the Fejér weight the statement is an
identity at every length.

* `fejerMean_eq`: for real coefficients,
  `∫_0^T (1 − t/T) |Σ_n a_n n^{−it}|² dt = Σ_{m,n} a_m a_n κ_T(log n − log m)`, with the Fejér kernel
  `κ_T(λ) = (1 − cos λT)/(Tλ²)`, `κ_T(0) = T/2` (`integral_fejerWeight_cos`). The mean value of a
  Dirichlet polynomial of any length is exactly a smoothed collision form.
* `fejerKernel_nonneg`, `fejerKernel_le_half`, `fejerKernel_le_inv_sq`,
  `two_div_pi_sq_mul_le_fejerKernel`: `0 ≤ κ_T ≤ T/2`, `κ_T(λ) ≤ 2/(Tλ²)`, and `κ_T(λ) ≥ 2T/π²` on
  the collision range `|λ| ≤ π/T`.
* `collisionCount_le_fejerMean`: for nonnegative coefficients the mean value dominates `2T/π²` times
  the collision count at scale `π/T`.
* `fejerMean_one_ge`: for `a = 1` on `[1, N]` the mean value is at least `TN(N+1)/(π²(T+1))` at every
  height `T`, against a diagonal `TN/2`: beyond the height the collisions dominate.
* `primeCollisions_le_fejerMean`: for prime coefficients the collision count is a count of prime
  pairs `p, p'` with `|log(p'/p)| ≤ π/T`. A main term for the long mean value of the prime polynomial
  is therefore a binary statement about primes in short multiplicative ranges.
-/

open Real Finset intervalIntegral

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The Dirichlet polynomial `Σ_{n∈S} a_n n^{−it}` with real coefficients. -/
def realDirPoly (S : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (a n : ℂ) * Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * Complex.I)

/-- `|D(t)|² = Σ_{m,n} a_m a_n cos(t(log n − log m))` for real coefficients. -/
theorem norm_sq_realDirPoly (S : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    ‖realDirPoly S a t‖ ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S, a m * a n * Real.cos (t * (Real.log n - Real.log m)) := by
  have hre : (realDirPoly S a t).re = ∑ n ∈ S, a n * Real.cos (t * Real.log n) := by
    simp only [realDirPoly, Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (realDirPoly S a t).im = -∑ n ∈ S, a n * Real.sin (t * Real.log n) := by
    simp only [realDirPoly, Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him, neg_mul_neg, Finset.sum_mul_sum,
    Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show t * (Real.log n - Real.log m) = t * Real.log n - t * Real.log m by ring, Real.cos_sub]
  ring

/-- The Fejér kernel `κ_T(λ) = (1 − cos λT)/(Tλ²)`, `κ_T(0) = T/2`. -/
def fejerKernel (T lam : ℝ) : ℝ := if lam = 0 then T / 2 else (1 - Real.cos (lam * T)) / (T * lam ^ 2)

/-- `∫_0^T (1 − t/T) cos(λt) dt = κ_T(λ)`. -/
theorem integral_fejerWeight_cos {T : ℝ} (hT : 0 < T) (lam : ℝ) :
    ∫ t in (0 : ℝ)..T, (1 - t / T) * Real.cos (t * lam) = fejerKernel T lam := by
  by_cases hl : lam = 0
  · subst hl
    simp only [mul_zero, Real.cos_zero, mul_one, fejerKernel, if_true]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (by exact (continuous_id.div_const T).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
    field_simp
    ring
  · rw [fejerKernel, if_neg hl]
    set F : ℝ → ℝ := fun t => (1 - t / T) * Real.sin (t * lam) / lam -
      Real.cos (t * lam) / (T * lam ^ 2) with hF
    have hderiv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F ((1 - t / T) * Real.cos (t * lam)) t := by
      intro t _
      have h1 : HasDerivAt (fun t => 1 - t / T) (-(1 / T)) t := by
        simpa using ((hasDerivAt_id t).div_const T).const_sub 1
      have h2 : HasDerivAt (fun t => Real.sin (t * lam)) (Real.cos (t * lam) * lam) t := by
        simpa using (Real.hasDerivAt_sin (t * lam)).comp t ((hasDerivAt_id t).mul_const lam)
      have h3 : HasDerivAt (fun t => Real.cos (t * lam)) (-Real.sin (t * lam) * lam) t := by
        simpa using (Real.hasDerivAt_cos (t * lam)).comp t ((hasDerivAt_id t).mul_const lam)
      have := ((h1.mul h2).div_const lam).sub (h3.div_const (T * lam ^ 2))
      convert this using 1
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by exact (by fun_prop : Continuous fun t : ℝ => (1 - t / T) * Real.cos (t * lam)).intervalIntegrable _ _)]
    simp only [hF, div_self hT.ne', sub_self, zero_mul, zero_div, zero_sub, mul_zero, Real.sin_zero,
      Real.cos_zero, zero_div]
    field_simp
    ring

/-- The Fejér mean value `∫_0^T (1 − t/T) |D(t)|² dt`. -/
def fejerMean (S : Finset ℕ) (a : ℕ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (1 - t / T) * ‖realDirPoly S a t‖ ^ 2

/-- **The mean value of a Dirichlet polynomial of any length is a collision form.** -/
theorem fejerMean_eq (S : Finset ℕ) (a : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    fejerMean S a T =
      ∑ m ∈ S, ∑ n ∈ S, a m * a n * fejerKernel T (Real.log n - Real.log m) := by
  unfold fejerMean
  simp_rw [norm_sq_realDirPoly, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun m _ => ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum fun n _ => ?_]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [← integral_fejerWeight_cos hT, ← intervalIntegral.integral_const_mul]
      congr 1
      ext t
      ring
    · exact (by fun_prop : Continuous fun t : ℝ => (1 - t / T) *
        (a m * a n * Real.cos (t * (Real.log n - Real.log m)))).intervalIntegrable _ _
  · exact (continuous_finset_sum _ fun n _ => by fun_prop).intervalIntegrable _ _

/-! ### The Fejér kernel -/

theorem one_sub_cos_eq (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

theorem fejerKernel_nonneg {T : ℝ} (hT : 0 < T) (lam : ℝ) : 0 ≤ fejerKernel T lam := by
  unfold fejerKernel
  split_ifs with h
  · linarith
  · exact div_nonneg (by linarith [Real.cos_le_one (lam * T)]) (by positivity)

theorem fejerKernel_le_half {T : ℝ} (hT : 0 < T) (lam : ℝ) : fejerKernel T lam ≤ T / 2 := by
  unfold fejerKernel
  split_ifs with h
  · exact le_rfl
  · have hl : 0 < lam ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    have := Real.one_sub_sq_div_two_le_cos (x := lam * T)
    nlinarith

theorem fejerKernel_le_inv_sq {T : ℝ} (hT : 0 < T) {lam : ℝ} (hl : lam ≠ 0) :
    fejerKernel T lam ≤ 2 / (T * lam ^ 2) := by
  rw [fejerKernel, if_neg hl]
  exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos (lam * T)]) (by positivity)

/-- On the collision range `|λ| ≤ π/T` the Fejér kernel is at least `2T/π²`. -/
theorem two_div_pi_sq_mul_le_fejerKernel {T : ℝ} (hT : 0 < T) {lam : ℝ}
    (hl : |lam| ≤ Real.pi / T) : 2 * T / Real.pi ^ 2 ≤ fejerKernel T lam := by
  unfold fejerKernel
  split_ifs with h0
  · have : (2 : ℝ) / Real.pi ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_gt_three]
    calc 2 * T / Real.pi ^ 2 = T * (2 / Real.pi ^ 2) := by ring
      _ ≤ T * (1 / 2) := mul_le_mul_of_nonneg_left this hT.le
      _ = T / 2 := by ring
  · set x := |lam * T| / 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have hxpi : x ≤ Real.pi / 2 := by
      rw [hx, abs_mul, abs_of_pos hT]
      have : |lam| * T ≤ Real.pi := by rwa [le_div_iff₀ hT] at hl
      linarith
    have hjordan := Real.mul_le_sin hx0 hxpi
    have hsin : Real.sin ((lam * T) / 2) ^ 2 = Real.sin x ^ 2 := by
      rcases le_or_gt 0 (lam * T) with hpos | hneg
      · rw [hx, abs_of_nonneg hpos]
      · rw [hx, abs_of_neg hneg, show -(lam * T) / 2 = -((lam * T) / 2) by ring, Real.sin_neg,
          neg_sq]
    have hl2 : 0 < lam ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity), one_sub_cos_eq, hsin]
    have hxsq : x ^ 2 = lam ^ 2 * T ^ 2 / 4 := by
      rw [hx, div_pow, sq_abs]; ring
    have hpi := Real.pi_pos
    have hsq : (2 / Real.pi * x) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ (by positivity) hjordan 2
    have : (2 / Real.pi * x) ^ 2 = lam ^ 2 * T ^ 2 / Real.pi ^ 2 := by
      rw [mul_pow, hxsq, div_pow]; field_simp; ring
    rw [this] at hsq
    have : 2 * T / Real.pi ^ 2 * (T * lam ^ 2) = 2 * (lam ^ 2 * T ^ 2 / Real.pi ^ 2) := by ring
    rw [this]
    linarith

/-! ### Collisions -/

/-- The collision count `Σ_{|log n − log m| ≤ η} a_m a_n`. -/
def collisionCount (S : Finset ℕ) (a : ℕ → ℝ) (η : ℝ) : ℝ :=
  ∑ m ∈ S, ∑ n ∈ S with |Real.log n - Real.log m| ≤ η, a m * a n

/-- **Collisions bound the mean value from below.** For nonnegative coefficients,
`(2T/π²) · (collision count at scale π/T) ≤ ∫_0^T (1 − t/T)|D(t)|² dt`. -/
theorem collisionCount_le_fejerMean (S : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ n ∈ S, 0 ≤ a n)
    {T : ℝ} (hT : 0 < T) :
    2 * T / Real.pi ^ 2 * collisionCount S a (Real.pi / T) ≤ fejerMean S a T := by
  rw [fejerMean_eq S a hT, collisionCount, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun n hn => ?_
  have hmn : 0 ≤ a m * a n := mul_nonneg (ha m hm) (ha n hn)
  split_ifs with h
  · calc 2 * T / Real.pi ^ 2 * (a m * a n) = a m * a n * (2 * T / Real.pi ^ 2) := by ring
      _ ≤ a m * a n * fejerKernel T (Real.log n - Real.log m) :=
          mul_le_mul_of_nonneg_left (two_div_pi_sq_mul_le_fejerKernel hT h) hmn
  · exact mul_nonneg hmn (fejerKernel_nonneg hT _)

/-- Each `n ≤ N` collides with at least `n/(T+1)` integers `m ≤ n` at scale `1/T`. -/
theorem le_card_collisions {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / (T + 1) ≤
      ((Finset.Icc 1 n).filter fun m => |Real.log n - Real.log m| ≤ 1 / T).card := by
  set x : ℝ := (n : ℝ) / (T + 1) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxn : x < n := by
    rw [hxdef, div_lt_iff₀ (by linarith)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hsub : (Finset.range (⌊x⌋₊ + 1)).image (fun j => n - j) ⊆
      (Finset.Icc 1 n).filter fun m => |Real.log n - Real.log m| ≤ 1 / T := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
    have hjx : (j : ℝ) ≤ x := by
      have := Finset.mem_range.1 hj
      exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 this)).trans (Nat.floor_le hx0)
    have hjn : j < n := by exact_mod_cast hjx.trans_lt hxn
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    have hm0 : (0 : ℝ) < (n - j : ℕ) := by exact_mod_cast (show 0 < n - j by omega)
    have hcast : ((n - j : ℕ) : ℝ) = n - j := by push_cast [hjn.le]; ring
    have hle : Real.log (n - j : ℕ) ≤ Real.log n :=
      Real.log_le_log hm0 (by exact_mod_cast Nat.sub_le n j)
    rw [abs_of_nonneg (by linarith)]
    -- `log n − log m ≤ (n − m)/m ≤ 1/T` since `n − m ≤ x` and `m ≥ n − x = nT/(T+1)`
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / (n - j : ℕ) by positivity)
    rw [Real.log_div (by positivity) hm0.ne'] at hlog
    have hmlow : (n : ℝ) * T / (T + 1) ≤ ((n - j : ℕ) : ℝ) := by
      rw [hcast]
      have : (n : ℝ) * T / (T + 1) = n - x := by rw [hxdef]; field_simp; ring
      linarith
    have hfrac : (n : ℝ) / ((n - j : ℕ) : ℝ) - 1 ≤ 1 / T := by
      rw [div_sub_one hm0.ne', div_le_div_iff₀ hm0 hT, hcast]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (j : ℝ) * T ≤ n * T / (T + 1) := by
        calc (j : ℝ) * T ≤ x * T := mul_le_mul_of_nonneg_right hjx hT.le
          _ = n * T / (T + 1) := by rw [hxdef]; ring
      have h2 : n * T / (T + 1) ≤ (n : ℝ) - j := by rw [← hcast]; exact hmlow
      nlinarith
    linarith
  calc x ≤ (⌊x⌋₊ + 1 : ℕ) := by push_cast; exact (Nat.lt_floor_add_one x).le
    _ = ((Finset.range (⌊x⌋₊ + 1)).image (fun j => n - j)).card := by
        rw [Finset.card_image_of_injOn (fun j hj k hk h => by
          have := Finset.mem_range.1 hj
          have := Finset.mem_range.1 hk
          have hjx : (j : ℝ) < n := lt_of_le_of_lt
            ((Nat.cast_le.2 (Nat.lt_succ_iff.1 ‹j < _›)).trans (Nat.floor_le hx0)) hxn
          have hkx : (k : ℝ) < n := lt_of_le_of_lt
            ((Nat.cast_le.2 (Nat.lt_succ_iff.1 ‹k < _›)).trans (Nat.floor_le hx0)) hxn
          have : j < n := by exact_mod_cast hjx
          have : k < n := by exact_mod_cast hkx
          simp only at h
          omega), Finset.card_range]
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- **Beyond the height the collisions dominate.** For `a = 1` on `[1, N]` and every `T > 0`,
`∫_0^T (1 − t/T)|Σ_{n≤N} n^{−it}|² dt ≥ T N(N+1)/(π²(T+1))`, while the diagonal is `TN/2`. -/
theorem fejerMean_one_ge (N : ℕ) {T : ℝ} (hT : 0 < T) :
    T * (N * (N + 1)) / (Real.pi ^ 2 * (T + 1)) ≤ fejerMean (Finset.Icc 1 N) (fun _ => 1) T := by
  refine le_trans ?_ (collisionCount_le_fejerMean _ (fun _ _ => zero_le_one) hT)
  have hpiT : 1 / T ≤ Real.pi / T := div_le_div_of_nonneg_right (by linarith [Real.pi_gt_three])
    hT.le
  have hcount : (N * (N + 1) : ℝ) / (2 * (T + 1)) ≤ collisionCount (Finset.Icc 1 N) (fun _ => 1)
      (Real.pi / T) := by
    unfold collisionCount
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul]
    have hsum : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) / (T + 1) = (N * (N + 1) : ℝ) / (2 * (T + 1)) := by
      rw [← Finset.sum_div]
      have : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) = N * (N + 1) / 2 := by
        induction N with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring
      rw [this]; field_simp
    rw [← hsum, Finset.sum_comm' (t' := Finset.Icc 1 N)
      (s' := fun n => (Finset.Icc 1 N).filter fun m => |Real.log n - Real.log m| ≤ Real.pi / T)]
    · refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
      refine (le_card_collisions hT hn1).trans ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      refine Nat.cast_le.2 (Finset.card_le_card fun m hm => ?_)
      obtain ⟨hmI, hml⟩ := Finset.mem_filter.1 hm
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hmI).1,
        (Finset.mem_Icc.1 hmI).2.trans hnN⟩, ?_⟩
      exact hml.trans hpiT
    · intro m n
      constructor
      · rintro ⟨hm, hn⟩
        exact ⟨Finset.mem_filter.1 hn |>.1, Finset.mem_filter.2 ⟨hm, by
          rw [abs_sub_comm]; exact (Finset.mem_filter.1 hn).2⟩⟩
      · rintro ⟨hn, hm⟩
        exact ⟨(Finset.mem_filter.1 hm).1, Finset.mem_filter.2 ⟨hn, by
          rw [abs_sub_comm]; exact (Finset.mem_filter.1 hm).2⟩⟩
  calc T * (N * (N + 1)) / (Real.pi ^ 2 * (T + 1))
      = 2 * T / Real.pi ^ 2 * ((N * (N + 1) : ℝ) / (2 * (T + 1))) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by positivity)

/-- **Prime collisions.** For the indicator of the primes in `S`, the number of ordered prime pairs
`p, p' ∈ S` with `|log p' − log p| ≤ π/T` is at most `π²/(2T)` times the mean value. -/
theorem primeCollisions_le_fejerMean (S : Finset ℕ) {T : ℝ} (hT : 0 < T) :
    (((S.filter Nat.Prime) ×ˢ (S.filter Nat.Prime)).filter
        fun pq => |Real.log pq.2 - Real.log pq.1| ≤ Real.pi / T).card ≤
      Real.pi ^ 2 / (2 * T) *
        fejerMean S (fun n => if n.Prime then 1 else 0) T := by
  have h := collisionCount_le_fejerMean S (a := fun n => if n.Prime then 1 else 0)
    (fun n _ => by split_ifs <;> norm_num) hT
  have hcount : collisionCount S (fun n => if n.Prime then (1 : ℝ) else 0) (Real.pi / T) =
      (((S.filter Nat.Prime) ×ˢ (S.filter Nat.Prime)).filter
        fun pq => |Real.log pq.2 - Real.log pq.1| ≤ Real.pi / T).card := by
    unfold collisionCount
    rw [Finset.card_filter, Finset.sum_product]
    push_cast
    refine Finset.sum_congr ?_ ?_ |>.trans ?_
    · exact S
    · rfl
    · intro m _; rfl
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : n.Prime <;> by_cases hl : |Real.log n - Real.log m| ≤ Real.pi / T <;>
        simp [hm, hn, hl]
    · simp [hm]
  rw [hcount] at h
  have hpi : 0 < Real.pi ^ 2 / (2 * T) := by positivity
  calc _ = Real.pi ^ 2 / (2 * T) * (2 * T / Real.pi ^ 2 * _) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hpi.le

end GaloisForLFunctions.InfiniteRankWeilTheory
