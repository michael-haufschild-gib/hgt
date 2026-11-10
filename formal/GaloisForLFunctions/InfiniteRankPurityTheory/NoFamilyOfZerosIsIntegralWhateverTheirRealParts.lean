import GaloisForLFunctions.InfiniteRankPurityTheory.OnTheFlowTheWeightFiltrationNeedsNoChainCondition
import GaloisForLFunctions.InfiniteRankPurityTheory.NoTraceClassFamilyOfZerosIsIntegral

/-!
# No family of zeros is integral, whatever their real parts

Kronecker's theorem over `ℤ` needs the weights to have no ascending chain, and the Wolff module
shows that for general modules this cannot be dropped. For locally finite modules in the strip it
can: integrality at the integers reaches the whole flow, and on the flow no chain condition is
needed.

**Theorem** (`mergedWeight_eq_zero_of_integral_locallyFinite`). Let a module have finitely many
modes in every disc, weights in `0 < Re ρ ≤ 1`, trace class of order two, and integer traces at all
large integers. Then it carries no weight at any mode other than `1`.

**Proof.** The second difference of the trace tends to zero and is an integer, so the trace is a
polynomial `c₀ + c₁ n` at large integers. The dilated combination `t(qx) − q t(x)` is the trace of
the module with weights `b_i (q^{ρ_i} − q)` and kills the linear term. Its derivative is bounded on
the flow because the derived module has weights `≤ 0`, so between consecutive integers it moves by a
bounded amount: it is bounded on the whole flow. On the flow the growth of the trace bounds the
weights of a locally finite module, so `(q^{ρ_j} − q)` times the weight at `ρ_j` vanishes for
`q = 2, 3`, and `2^ρ = 2`, `3^ρ = 3` force `ρ = 1`.

**Corollary** (`eq_zero_of_integral_trace_of_distinct_xi_zeros`). A family of distinct zeros of `ξ`
with weights of trace class of order two and integer traces at all large integers has all weights
zero. Nothing is assumed about the real parts of the zeros.
-/

open Filter Topology Complex Set

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

variable {ι : Type*}

/-- The trace moves by a bounded amount between nearby points of the flow when the weights are
`≤ 1`: `‖t(y) − t(a)‖ ≤ (Σ ‖b_i ρ_i‖) (y − a)` for `1 < a ≤ y`. -/
theorem norm_frobTrace_sub_le {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖))
    (hA : ∀ i, (ρ i).re ≤ 1) {a y : ℝ} (ha : 1 < a) (hay : a ≤ y) :
    ‖frobTrace b ρ y - frobTrace b ρ a‖ ≤ (∑' i, ‖b i * ρ i‖) * (y - a) := by
  have hbρ : Summable fun i => ‖b i * ρ i‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hb
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (ρ i)]) (norm_nonneg _)
  have hA' : ∀ i, (ρ i - 1).re ≤ 0 := fun i => by
    simp only [sub_re, one_re]
    linarith [hA i]
  have hder : ∀ z ∈ Icc a y, HasDerivWithinAt (frobTrace b ρ)
      (frobTrace (fun i => b i * ρ i) (fun i => ρ i - 1) z) (Icc a y) z := fun z hz =>
    (hasDerivAt_frobTrace hb hA (lt_of_lt_of_le ha hz.1)).hasDerivWithinAt
  have hbound : ∀ z ∈ Ico a y,
      ‖frobTrace (fun i => b i * ρ i) (fun i => ρ i - 1) z‖ ≤ ∑' i, ‖b i * ρ i‖ := by
    intro z hz
    have h := norm_frobTrace_le hbρ hA' (le_of_lt (lt_of_lt_of_le ha hz.1))
    rwa [Real.rpow_zero, mul_one] at h
  exact norm_image_sub_le_of_norm_deriv_le_segment' hder hbound y (right_mem_Icc.mpr hay)

/-- The dilated combination `t(qx) − q t(x)` is the trace of the module with weights
`b_i (q^{ρ_i} − q)`. -/
theorem frobTrace_dilate_sub {b ρ : ι → ℂ} (hb : Summable fun i => ‖b i‖)
    (hA : ∀ i, (ρ i).re ≤ 1) (q : ℕ) (hq : 1 ≤ q) {x : ℝ} (hx : 1 ≤ x) :
    frobTrace (fun i => b i * ((q : ℂ) ^ ρ i - q)) ρ x =
      frobTrace b ρ ((q : ℝ) * x) - q * frobTrace b ρ x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hqx : (1 : ℝ) ≤ (q : ℝ) * x := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hs1 := summable_frobTerm hb hA hqx
  have hs2 := (summable_frobTerm hb hA hx).mul_left (q : ℂ)
  have hd := dilate_cpow q 1 hx0
  simp only [pow_one] at hd
  rw [frobTrace, frobTrace, frobTrace, ← tsum_mul_left, ← hs1.tsum_sub hs2]
  refine tsum_congr fun i => ?_
  rw [hd]
  ring

/-- **Kronecker for locally finite modules in the strip, without a chain condition.** Finitely many
modes in every disc, weights in `0 < Re ρ ≤ 1`, trace class of order two, integer traces at all
large integers: no weight is carried at a mode other than `1`. -/
theorem mergedWeight_eq_zero_of_integral_locallyFinite {b ρ : ι → ℂ}
    (hpos : ∀ i, 0 < (ρ i).re) (hA : ∀ i, (ρ i).re ≤ 1)
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ 2) (hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite)
    {n₁ : ℕ} (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) {j : ι} (hj : ρ j ≠ 1) :
    (∑' i, if ρ i = ρ j then b i else 0) = 0 := by
  classical
  have hb1 : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) :=
    summable_order_one (m := 1) (by simpa using hb)
  have hb0 : Summable fun i => ‖b i‖ := summable_of_order hb
  -- the trace is `c₀ + c₁ n` at large integers
  obtain ⟨n₀, P, hP, hval⟩ := exists_polynomial_of_integral_trace (m := 2) hA (by norm_num) hb hint
  have hPeval : ∀ x : ℂ, P.eval x = P.coeff 0 + P.coeff 1 * x := by
    intro x
    rw [← sum_range_coeff_eq_eval P hP x, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max n₀ 2 := ⟨_, rfl⟩
  have hN0 : n₀ ≤ N := by rw [hN]; exact le_max_left _ _
  have hN2 : 2 ≤ N := by rw [hN]; exact le_max_right _ _
  -- for each `q` the dilated combination is bounded on the flow
  have hbounded : ∀ q : ℕ, 1 ≤ q → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖frobTrace (fun i => b i * ((q : ℂ) ^ ρ i - q)) ρ x‖ ≤ C * x ^ (0 : ℝ) := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑' i, ‖b i * ρ i‖ := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by
      rw [hK]
      exact tsum_nonneg fun _ => norm_nonneg _
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' i, ‖b i‖ := ⟨_, rfl⟩
    have hW0 : 0 ≤ W := by
      rw [hW]
      exact tsum_nonneg fun _ => norm_nonneg _
    refine ⟨(q : ℝ) * K + q * K + ‖(P.coeff 0 : ℂ) * (1 - q)‖ + (W * (q * N) + q * (W * N)),
      fun x hx => ?_⟩
    rw [Real.rpow_zero, mul_one, frobTrace_dilate_sub hb0 hA q hq hx]
    rcases le_or_gt (N : ℝ) x with hxN | hxN
    · -- beyond `N`: compare with the integer part
      obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊x⌋₊ := ⟨_, rfl⟩
      have hnx : (n : ℝ) ≤ x := by
        rw [hn]
        exact Nat.floor_le (by linarith)
      have hxn : x < (n : ℝ) + 1 := by
        rw [hn]
        exact Nat.lt_floor_add_one x
      have hNn : N ≤ n := by
        rw [hn]
        exact Nat.le_floor hxN
      have hn1 : (1 : ℝ) < n := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hN2.trans hNn
        linarith
      have hqn1 : (1 : ℝ) < (q : ℝ) * n := by nlinarith
      have h1 := norm_frobTrace_sub_le hb1 hA hqn1
        (mul_le_mul_of_nonneg_left hnx (by linarith) : (q : ℝ) * n ≤ q * x)
      have h2 := norm_frobTrace_sub_le hb1 hA hn1 hnx
      rw [← hK] at h1 h2
      -- at the integers the combination is `c₀ (1 − q)`
      have hint1 : frobTrace b ρ ((q : ℝ) * n) - q * frobTrace b ρ n =
          P.coeff 0 * (1 - q) := by
        have e1 : frobTrace b ρ ((q : ℝ) * n) = P.eval ((q * n : ℕ) : ℂ) := by
          rw [← hval (q * n) (hN0.trans (hNn.trans (Nat.le_mul_of_pos_left n hq)))]
          push_cast
          rfl
        rw [e1, hval n (hN0.trans hNn), hPeval, hPeval]
        push_cast
        ring
      have hsplit : frobTrace b ρ ((q : ℝ) * x) - q * frobTrace b ρ x =
          (frobTrace b ρ ((q : ℝ) * x) - frobTrace b ρ ((q : ℝ) * n)) -
            q * (frobTrace b ρ x - frobTrace b ρ n) + P.coeff 0 * (1 - q) := by
        rw [← hint1]
        ring
      rw [hsplit]
      have hq0 : ‖(q : ℂ)‖ = q := by simp
      have ha : ‖frobTrace b ρ ((q : ℝ) * x) - frobTrace b ρ ((q : ℝ) * n)‖ ≤ q * K := by
        refine h1.trans ?_
        have : (q : ℝ) * x - q * n ≤ q := by nlinarith
        calc K * ((q : ℝ) * x - q * n) ≤ K * q := mul_le_mul_of_nonneg_left this hK0
          _ = q * K := mul_comm _ _
      have hb' : ‖(q : ℂ) * (frobTrace b ρ x - frobTrace b ρ n)‖ ≤ q * K := by
        rw [norm_mul, hq0]
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by linarith)
        calc K * (x - n) ≤ K * 1 := mul_le_mul_of_nonneg_left (by linarith) hK0
          _ = K := mul_one K
      have hrest : 0 ≤ W * (q * N) + q * (W * N) := by positivity
      calc _ ≤ ‖frobTrace b ρ ((q : ℝ) * x) - frobTrace b ρ ((q : ℝ) * n)‖ +
            ‖(q : ℂ) * (frobTrace b ρ x - frobTrace b ρ n)‖ + ‖(P.coeff 0 : ℂ) * (1 - q)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ (q : ℝ) * K + q * K + ‖(P.coeff 0 : ℂ) * (1 - q)‖ +
            (W * (q * N) + q * (W * N)) := by linarith
    · -- below `N`: the crude bound
      have hqx : (1 : ℝ) ≤ (q : ℝ) * x := by nlinarith
      have h1 := norm_frobTrace_le hb0 hA hqx
      have h2 := norm_frobTrace_le hb0 hA hx
      rw [Real.rpow_one, ← hW] at h1 h2
      have hq0 : ‖(q : ℂ)‖ = q := by simp
      have ha : ‖frobTrace b ρ ((q : ℝ) * x)‖ ≤ W * (q * N) :=
        h1.trans (mul_le_mul_of_nonneg_left (by nlinarith) hW0)
      have hb' : ‖(q : ℂ) * frobTrace b ρ x‖ ≤ q * (W * N) := by
        rw [norm_mul, hq0]
        exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hxN.le hW0))
          (by linarith)
      have hrest : 0 ≤ (q : ℝ) * K + q * K + ‖(P.coeff 0 : ℂ) * (1 - q)‖ := by positivity
      calc _ ≤ ‖frobTrace b ρ ((q : ℝ) * x)‖ + ‖(q : ℂ) * frobTrace b ρ x‖ := norm_sub_le _ _
        _ ≤ (q : ℝ) * K + q * K + ‖(P.coeff 0 : ℂ) * (1 - q)‖ +
            (W * (q * N) + q * (W * N)) := by linarith
  -- on the flow the dilated module carries no weight in `Re > 0`
  have hkill : ∀ q : ℕ, 1 ≤ q →
      ((q : ℂ) ^ ρ j - q) * (∑' i, if ρ i = ρ j then b i else 0) = 0 := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hsum : Summable fun i => ‖b i * ((q : ℂ) ^ ρ i - q)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
        (hb0.mul_right ((q : ℝ) + q))
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : ‖(q : ℂ) ^ ρ i‖ ≤ q := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega)]
        calc (q : ℝ) ^ (ρ i).re ≤ (q : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hq1 (hA i)
          _ = q := Real.rpow_one _
      calc ‖(q : ℂ) ^ ρ i - q‖ ≤ ‖(q : ℂ) ^ ρ i‖ + ‖(q : ℂ)‖ := norm_sub_le _ _
        _ ≤ (q : ℝ) + q := by
            have : ‖(q : ℂ)‖ = q := by simp
            linarith
    obtain ⟨C, hC⟩ := hbounded q hq
    have h := mergedWeight_eq_zero_of_flow_bound hsum hA hfin hC (hpos j)
    have hrel : (∑' i, if ρ i = ρ j then b i * ((q : ℂ) ^ ρ i - q) else 0) =
        ((q : ℂ) ^ ρ j - q) * ∑' i, if ρ i = ρ j then b i else 0 := by
      rw [← tsum_mul_left]
      refine tsum_congr fun i => ?_
      by_cases hi : ρ i = ρ j
      · rw [if_pos hi, if_pos hi, hi, mul_comm]
      · rw [if_neg hi, if_neg hi, mul_zero]
    rw [← hrel]
    exact h
  by_contra hne
  have h2 := (mul_eq_zero.mp (hkill 2 (by norm_num))).resolve_right hne
  have h3 := (mul_eq_zero.mp (hkill 3 (by norm_num))).resolve_right hne
  apply hj
  refine cpow_two_three_injective ?_ ?_
  · rw [Complex.cpow_one]
    have := sub_eq_zero.mp h2
    simpa using this
  · rw [Complex.cpow_one]
    have := sub_eq_zero.mp h3
    simpa using this

/-- The zeros of `ξ` in a disc are finite in number. -/
theorem finite_xi_zeros_norm_le (B : ℝ) : {s : ℂ | xi s = 0 ∧ ‖s‖ ≤ B}.Finite := by
  refine ((finite_xiZeroCopy_band 0 (abs_nonneg B)).image fun q : XiZeroCopy => (q.1 : ℂ)).subset
    ?_
  rintro s ⟨hs, hsB⟩
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hs
  refine ⟨q, ?_, hq⟩
  show |(q.1 : ℂ).im - 0| ≤ |B|
  rw [sub_zero, hq]
  exact (Complex.abs_im_le_norm s).trans (hsB.trans (le_abs_self B))

/-- **No family of zeros is integral, whatever their real parts.** A family of distinct zeros of
`ξ` with weights of trace class of order two and integer traces at all large integers has all
weights zero. -/
theorem eq_zero_of_integral_trace_of_distinct_xi_zeros {b ρ : ι → ℂ}
    (hρ : Function.Injective ρ) (hzero : ∀ i, xi (ρ i) = 0)
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ 2) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) : ∀ i, b i = 0 := by
  intro j
  have hfin : ∀ B : ℝ, {i | ‖ρ i‖ ≤ B}.Finite := by
    intro B
    refine ((finite_xi_zeros_norm_le B).preimage hρ.injOn).subset fun i hi => ?_
    exact ⟨hzero i, hi⟩
  have hj : ρ j ≠ 1 := fun h => by
    have h1 := hzero j
    rw [h, xi_one] at h1
    norm_num at h1
  have h := mergedWeight_eq_zero_of_integral_locallyFinite
    (fun i => re_pos_of_xi_eq_zero (hzero i))
    (fun i => (re_lt_one_of_xi_eq_zero (hzero i)).le) hb hfin hint hj
  rwa [tsum_eq_single j (fun i hi => by rw [if_neg fun h' => hi (hρ h')]), if_pos rfl] at h

end GaloisForLFunctions.InfiniteRankPurityTheory
