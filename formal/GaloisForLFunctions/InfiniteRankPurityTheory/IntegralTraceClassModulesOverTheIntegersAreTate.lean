import GaloisForLFunctions.InfiniteRankPurityTheory.TwoFrobeniiDetermineATraceClassModule
import GaloisForLFunctions.InfiniteRankPurityTheory.BoundedIntegralTracesOfOneFrobeniusAreTorsion

/-!
# Integral trace-class Frobenius modules over `ℤ` are Tate

Kronecker's theorem for the whole Frobenius system of `ℤ`. A Frobenius module over `ℤ` has modes
`ρ_i`, weights `b_i`, and traces `t(n) = Σ_i b_i n^{ρ_i}`; it is of **trace class of order `m`** when
`Σ ‖b_i‖ (1 + ‖ρ_i‖)^m < ∞`.

**Theorem** (`tate_of_integral_trace`). Let the modes be distinct with weights `Re ρ_i ≤ A < m`, the
set of weights without infinite ascending chain, the module of trace class of order `m`, and let
`t(n) ∈ ℤ` for all large `n`. Then every visible mode is one of `0, 1, …, m − 1`: the module is a sum
of Tate twists and `t` is a polynomial. The rank is not assumed finite.

**Proof.**
- `d/dx Σ b_i x^{ρ_i} = Σ b_i ρ_i x^{ρ_i − 1}`: a derivative lowers every weight by one and costs one
  order (`hasDerivAt_frobTrace`).
- The `m`-th forward difference is an `m`-fold mean of the `m`-th derivative, so
  `‖Δ^m t(x)‖ ≤ K x^{A − m}` (`exists_norm_fwdDiff_iter_frobTrace_le`).
- `Δ^m t(n)` is an integer tending to zero, hence zero for `n ≥ n₀`; by Newton's formula `t` agrees
  with a polynomial of degree `< m` on `n ≥ n₀`.
- The dilation operator `Π_{k<m} (S_p − p^k)`, `S_p f(x) = f(p x)`, kills polynomials of degree `< m`
  and multiplies the weight of the mode `ρ` by `Π_{k<m} (p^ρ − p^k)` (`tateDilation_polynomial`,
  `tateDilation_frobTrace`).
- Two Frobenii determine a trace-class module, so `b_i Π_{k<m}(p^{ρ_i} − p^k) = 0` for `p = 2, 3`;
  `2^ρ = 2^k` and `3^ρ = 3^{k'}` force `ρ = k`.

With the duality `ρ ↔ 1 − ρ` only the modes `0` and `1` survive (`tate_of_integral_trace_dual`), and
no visible mode lies in the open strip `0 < Re ρ < 1` (`not_visible_in_open_strip`). The zero motive
of an arithmetic object is therefore never of trace class of an order exceeding its weight; for `ζ`
already `Σ 1/‖ρ‖ = ∞`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-! ### Size of the trace -/

theorem norm_ofReal_cpow_le {x A : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re ≤ A) :
    ‖(x : ℂ) ^ ρ‖ ≤ x ^ A := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx hρ

theorem norm_frobTerm_le {b ρ : ι → ℂ} {A : ℝ} (hA : ∀ i, (ρ i).re ≤ A) {x : ℝ} (hx : 1 ≤ x)
    (i : ι) : ‖b i * (x : ℂ) ^ ρ i‖ ≤ ‖b i‖ * x ^ A := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_ofReal_cpow_le hx (hA i)) (norm_nonneg _)

theorem summable_frobTerm {b ρ : ι → ℂ} {A : ℝ} (hb : Summable fun i => ‖b i‖)
    (hA : ∀ i, (ρ i).re ≤ A) {x : ℝ} (hx : 1 ≤ x) : Summable fun i => b i * (x : ℂ) ^ ρ i :=
  Summable.of_norm_bounded (hb.mul_right (x ^ A)) (norm_frobTerm_le hA hx)

theorem norm_frobTrace_le {b ρ : ι → ℂ} {A : ℝ} (hb : Summable fun i => ‖b i‖)
    (hA : ∀ i, (ρ i).re ≤ A) {x : ℝ} (hx : 1 ≤ x) :
    ‖frobTrace b ρ x‖ ≤ (∑' i, ‖b i‖) * x ^ A := by
  rw [frobTrace, ← tsum_mul_right]
  exact tsum_of_norm_bounded (hb.mul_right (x ^ A)).hasSum (norm_frobTerm_le hA hx)

/-! ### Orders -/

theorem one_le_one_add_norm_pow (ρ : ℂ) (m : ℕ) : 1 ≤ (1 + ‖ρ‖) ^ m :=
  one_le_pow₀ (by linarith [norm_nonneg ρ])

/-- Trace class of order `m` is trace class. -/
theorem summable_of_order {b ρ : ι → ℂ} {m : ℕ}
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) : Summable fun i => ‖b i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => le_mul_of_one_le_right (norm_nonneg _) (one_le_one_add_norm_pow _ _)) hb

/-- Trace class of order `m + 1` is trace class of order one. -/
theorem summable_order_one {b ρ : ι → ℂ} {m : ℕ}
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ (m + 1)) :
    Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) := by
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (norm_nonneg _) (by linarith [norm_nonneg (ρ i)])) (fun i => ?_) hb
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [pow_succ]
  exact le_mul_of_one_le_left (by linarith [norm_nonneg (ρ i)]) (one_le_one_add_norm_pow _ _)

/-- The derived module `(b ρ, ρ − 1)` has one order less. -/
theorem summable_order_deriv {b ρ : ι → ℂ} {m : ℕ}
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ (m + 1)) :
    Summable fun i => ‖b i * ρ i‖ * (1 + ‖ρ i - 1‖) ^ m := by
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [norm_nonneg (ρ i - 1)]) _))
    (fun i => ?_) (hb.mul_left ((2 : ℝ) ^ m))
  have h0 := norm_nonneg (ρ i)
  have h1 : 1 + ‖ρ i - 1‖ ≤ 2 * (1 + ‖ρ i‖) := by
    have : ‖ρ i - 1‖ ≤ ‖ρ i‖ + 1 := by
      calc ‖ρ i - 1‖ ≤ ‖ρ i‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖ρ i‖ + 1 := by rw [norm_one]
    linarith
  have h2 : (1 + ‖ρ i - 1‖) ^ m ≤ (2 : ℝ) ^ m * (1 + ‖ρ i‖) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [norm_nonneg (ρ i - 1)]) h1 m
  calc ‖b i * ρ i‖ * (1 + ‖ρ i - 1‖) ^ m
      ≤ (‖b i‖ * (1 + ‖ρ i‖)) * ((2 : ℝ) ^ m * (1 + ‖ρ i‖) ^ m) := by
        rw [norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)) h2
          (pow_nonneg (by linarith [norm_nonneg (ρ i - 1)]) _)
          (mul_nonneg (norm_nonneg _) (by linarith))
    _ = (2 : ℝ) ^ m * (‖b i‖ * (1 + ‖ρ i‖) ^ (m + 1)) := by ring

/-! ### The derivative lowers the weights by one -/

theorem hasDerivAt_ofReal_cpow (ρ : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ ρ) (ρ * (y : ℂ) ^ (ρ - 1)) y := by
  have h := ((hasDerivAt_id (y : ℂ)).cpow_const (c := ρ)
    (Complex.ofReal_mem_slitPlane.mpr hy)).comp_ofReal
  simpa using h

/-- `d/dx Σ b_i x^{ρ_i} = Σ b_i ρ_i x^{ρ_i − 1}` for `x > 1`. -/
theorem hasDerivAt_frobTrace {b ρ : ι → ℂ} {A : ℝ}
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖)) (hA : ∀ i, (ρ i).re ≤ A) {x : ℝ}
    (hx : 1 < x) :
    HasDerivAt (frobTrace b ρ) (frobTrace (fun i => b i * ρ i) (fun i => ρ i - 1) x) x := by
  have hb0 : Summable fun i => ‖b i‖ := by
    have := summable_of_order (b := b) (ρ := ρ) (m := 1) (by simpa using hb)
    exact this
  set M : ℝ := (x + 1) ^ |A - 1| with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg (by linarith) _
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℂ)
    (u := fun i => ‖b i‖ * (1 + ‖ρ i‖) * M)
    (g := fun i (y : ℝ) => b i * (y : ℂ) ^ ρ i)
    (g' := fun i (y : ℝ) => b i * ρ i * (y : ℂ) ^ (ρ i - 1))
    (t := Set.Ioo 1 (x + 1)) (y₀ := x) (y := x) (hb.mul_right M) isOpen_Ioo isPreconnected_Ioo
    ?_ ?_ ⟨hx, by linarith⟩ (summable_frobTerm hb0 hA hx.le) ⟨hx, by linarith⟩
  · exact hmain
  · intro i y hy
    have h := (hasDerivAt_ofReal_cpow (ρ i) (by linarith [hy.1] : (0 : ℝ) < y)).const_mul (b i)
    exact h.congr_deriv (mul_assoc _ _ _).symm
  · intro i y hy
    have hy1 : (1 : ℝ) ≤ y := hy.1.le
    have hpow : ‖(y : ℂ) ^ (ρ i - 1)‖ ≤ M := by
      have h1 : (ρ i - 1).re ≤ |A - 1| := by
        simp only [Complex.sub_re, Complex.one_re]
        exact (sub_le_sub_right (hA i) 1).trans (le_abs_self _)
      calc ‖(y : ℂ) ^ (ρ i - 1)‖ ≤ y ^ |A - 1| := norm_ofReal_cpow_le hy1 h1
        _ ≤ (x + 1) ^ |A - 1| := Real.rpow_le_rpow (by linarith) hy.2.le (abs_nonneg _)
    rw [norm_mul, norm_mul]
    have h0 := norm_nonneg (ρ i)
    calc ‖b i‖ * ‖ρ i‖ * ‖(y : ℂ) ^ (ρ i - 1)‖ ≤ ‖b i‖ * (1 + ‖ρ i‖) * M := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)) hpow
            (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by linarith))

/-! ### Forward differences -/

/-- Forward differences of any step `h ≥ 0` commute with differentiation. -/
theorem hasDerivAt_fwdDiff_iter {h : ℝ} (hh : 0 ≤ h) (m : ℕ) : ∀ {f f' : ℝ → ℂ},
    (∀ y : ℝ, 1 < y → HasDerivAt f (f' y) y) →
    ∀ y : ℝ, 1 < y → HasDerivAt ((fwdDiff h)^[m] f) ((fwdDiff h)^[m] f' y) y := by
  induction m with
  | zero =>
    intro f f' hf y hy
    simpa using hf y hy
  | succ m ih =>
    intro f f' hf y hy
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih (f := fwdDiff h f) (f' := fwdDiff h f') (fun z hz => ?_) y hy
    have h1 : HasDerivAt (fun z => f (z + h)) (f' (z + h)) z :=
      HasDerivAt.comp_add_const z h (hf (z + h) (by linarith))
    exact h1.sub (hf z hz)

/-- **The `m`-th forward difference of the trace is `O(x^{A − m})`**, for every step `h ≥ 0`. -/
theorem exists_norm_fwdDiff_iter_frobTrace_le {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    ∀ (b ρ : ι → ℂ) (A : ℝ),
    (∀ i, (ρ i).re ≤ A) → A ≤ m → Summable (fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 < x →
      ‖(fwdDiff h)^[m] (frobTrace b ρ) x‖ ≤ K * x ^ (A - m) := by
  induction m with
  | zero =>
    intro b ρ A hA _ hb
    have hb' : Summable fun i => ‖b i‖ := by simpa using hb
    refine ⟨∑' i, ‖b i‖, tsum_nonneg fun _ => norm_nonneg _, fun x hx => ?_⟩
    simpa using norm_frobTrace_le hb' hA hx.le
  | succ m ih =>
    intro b ρ A hA hAm hb
    have hAm' : A ≤ (m : ℝ) + 1 := by exact_mod_cast hAm
    have hb1 := summable_order_one hb
    obtain ⟨K, hK0, hK⟩ := ih (fun i => b i * ρ i) (fun i => ρ i - 1) (A - 1)
      (fun i => by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [hA i])
      (by linarith) (summable_order_deriv hb)
    refine ⟨K * h, mul_nonneg hK0 hh, fun x hx => ?_⟩
    rw [Function.iterate_succ_apply']
    set g := (fwdDiff h)^[m] (frobTrace b ρ) with hg
    set g' := (fwdDiff h)^[m] (frobTrace (fun i => b i * ρ i) (fun i => ρ i - 1)) with hg'
    have hder : ∀ y : ℝ, 1 < y → HasDerivAt g (g' y) y :=
      hasDerivAt_fwdDiff_iter hh m fun y hy => hasDerivAt_frobTrace hb1 hA hy
    have hexp : A - 1 - (m : ℝ) = A - ((m + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hbound : ∀ y ∈ Set.Ico x (x + h), ‖g' y‖ ≤ K * x ^ (A - ((m + 1 : ℕ) : ℝ)) := by
      intro y hy
      have hy1 : 1 < y := lt_of_lt_of_le hx hy.1
      calc ‖g' y‖ ≤ K * y ^ (A - 1 - m) := hK y hy1
        _ ≤ K * x ^ (A - 1 - m) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0
            exact Real.rpow_le_rpow_of_nonpos (by linarith) hy.1 (by linarith)
        _ = K * x ^ (A - ((m + 1 : ℕ) : ℝ)) := by rw [hexp]
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g') (a := x)
      (b := x + h) (fun y hy => (hder y (lt_of_lt_of_le hx hy.1)).hasDerivWithinAt) hbound
      (x + h) (Set.right_mem_Icc.mpr (by linarith))
    have hval : fwdDiff h g x = g (x + h) - g x := rfl
    rw [hval]
    calc ‖g (x + h) - g x‖ ≤ K * x ^ (A - ((m + 1 : ℕ) : ℝ)) * (x + h - x) := hmvt
      _ = K * h * x ^ (A - ((m + 1 : ℕ) : ℝ)) := by ring

/-! ### Integrality -/

/-- Forward differences of an integer-valued function are integer-valued. -/
theorem exists_int_fwdDiff_iter {f : ℝ → ℂ} {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, f n = k) (m : ℕ) {n : ℕ} (hn : n₁ ≤ n) :
    ∃ k : ℤ, (fwdDiff (1 : ℝ))^[m] f n = k := by
  choose! F hF using hint
  refine ⟨∑ k ∈ range (m + 1), ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ)) * F (n + k), ?_⟩
  rw [fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcast : ((n : ℝ) + k • (1 : ℝ)) = ((n + k : ℕ) : ℝ) := by
    simp
  rw [hcast, hF (n + k) (by omega), zsmul_eq_mul]
  push_cast
  ring

/-- **The `m`-th difference of an integral trace vanishes eventually.** -/
theorem fwdDiff_iter_eventually_zero {b ρ : ι → ℂ} {A : ℝ} {m : ℕ} (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) :
    ∃ n₀ : ℕ, n₁ ≤ n₀ ∧ 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → (fwdDiff (1 : ℝ))^[m] (frobTrace b ρ) n = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_fwdDiff_iter_frobTrace_le zero_le_one m b ρ A hA hAm.le hb
  have hneg : 0 < (m : ℝ) - A := by linarith
  have htend : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (A - m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-((m : ℝ) - A))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hneg
    have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul K
    simpa [neg_sub] using h2
  have hev : ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ (A - m) < 1 := htend.eventually (gt_mem_nhds one_pos)
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp hev
  refine ⟨max (max n₁ 2) n₂, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnn : n₂ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨k, hk⟩ := exists_int_fwdDiff_iter hint m hn1
  have hx : (1 : ℝ) < n := by exact_mod_cast hn2
  have hlt : ‖(k : ℂ) - ((0 : ℤ) : ℂ)‖ < 1 := by
    rw [← hk]
    simpa using lt_of_le_of_lt (hK n hx) (hn₂ n hnn)
  rw [hk, int_eq_of_norm_sub_lt_one hlt]
  simp

/-! ### Newton's formula: the trace is a polynomial on `n ≥ n₀` -/

/-- A function on `ℝ` whose `m`-th forward difference vanishes at all integers `n ≥ n₀` agrees there
with a polynomial all of whose coefficients of index `≥ m` vanish. -/
theorem exists_polynomial_of_fwdDiff_iter_zero {f : ℝ → ℂ} {m n₀ : ℕ}
    (h0 : ∀ n : ℕ, n₀ ≤ n → (fwdDiff (1 : ℝ))^[m] f n = 0) :
    ∃ P : Polynomial ℂ, (∀ i, m ≤ i → P.coeff i = 0) ∧
      ∀ n : ℕ, n₀ ≤ n → f n = P.eval (n : ℂ) := by
  -- higher differences vanish at `n₀`
  have hhigh : ∀ k : ℕ, m ≤ k → (fwdDiff (1 : ℝ))^[k] f n₀ = 0 := by
    intro k hk
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, Function.iterate_add_apply, fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hcast : ((n₀ : ℝ) + j • (1 : ℝ)) = ((n₀ + j : ℕ) : ℝ) := by simp
    rw [hcast, h0 (n₀ + j) (by omega), smul_zero]
  set d : ℕ → ℂ := fun k => (fwdDiff (1 : ℝ))^[k] f n₀ with hd
  -- Newton's formula
  have hnewton : ∀ j : ℕ, f ((n₀ + j : ℕ) : ℝ) = ∑ k ∈ range m, (j.choose k : ℂ) * d k := by
    intro j
    have hcast : ((n₀ + j : ℕ) : ℝ) = (n₀ : ℝ) + j • (1 : ℝ) := by simp
    rw [hcast, shift_eq_sum_fwdDiff_iter (1 : ℝ) f j (n₀ : ℝ)]
    have hterm : ∀ k, j.choose k • (fwdDiff (1 : ℝ))^[k] f n₀ = (j.choose k : ℂ) * d k := by
      intro k
      rw [nsmul_eq_mul]
    simp_rw [hterm]
    have hA : ∑ k ∈ range (j + 1), (j.choose k : ℂ) * d k =
        ∑ k ∈ range (max (j + 1) m), (j.choose k : ℂ) * d k := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _)) fun k _ hk => ?_
      have hjk : j < k := by
        have := Finset.mem_range.not.mp hk
        omega
      rw [Nat.choose_eq_zero_of_lt hjk]
      simp
    have hB : ∑ k ∈ range m, (j.choose k : ℂ) * d k =
        ∑ k ∈ range (max (j + 1) m), (j.choose k : ℂ) * d k := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) fun k _ hk => ?_
      have hmk : m ≤ k := by
        have := Finset.mem_range.not.mp hk
        omega
      rw [hd]
      simp only
      rw [hhigh k hmk, mul_zero]
    rw [hA, hB]
  -- the Newton polynomial in the variable `j`
  set Q : Polynomial ℂ :=
    ∑ k ∈ range m, Polynomial.C (d k / (k.factorial : ℂ)) * descPochhammer ℂ k with hQ
  have hQeval : ∀ j : ℕ, Q.eval (j : ℂ) = ∑ k ∈ range m, (j.choose k : ℂ) * d k := by
    intro j
    rw [hQ, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  have hQcoeff : ∀ i, m ≤ i → Q.coeff i = 0 := by
    intro i hi
    rw [hQ, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [descPochhammer_natDegree]
    exact lt_of_lt_of_le (Finset.mem_range.mp hk) hi
  -- shift the variable
  refine ⟨Q.comp (Polynomial.X - Polynomial.C (n₀ : ℂ)), ?_, ?_⟩
  · intro i hi
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have hQ0 : Q = 0 := by
        rw [hQ, hm]
        simp
      rw [hQ0]
      simp
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hdeg : Q.natDegree ≤ m - 1 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        exact hQcoeff N (by omega)
      calc (Q.comp (Polynomial.X - Polynomial.C (n₀ : ℂ))).natDegree
          ≤ Q.natDegree * (Polynomial.X - Polynomial.C (n₀ : ℂ)).natDegree :=
            Polynomial.natDegree_comp_le
        _ = Q.natDegree := by rw [Polynomial.natDegree_X_sub_C, mul_one]
        _ ≤ m - 1 := hdeg
        _ < i := by omega
  · intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [hnewton j, ← hQeval j, Polynomial.eval_comp]
    congr 1
    simp

/-- **The `m`-th difference of a trace of order `m` with weights below `m` tends to zero**, with
no integrality assumed. A function on the integers whose `m`-th differences do not tend to zero is not
such a trace. -/
theorem tendsto_fwdDiff_iter_frobTrace_zero {b ρ : ι → ℂ} {A : ℝ} {m : ℕ}
    (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) :
    Tendsto (fun n : ℕ => (fwdDiff (1 : ℝ))^[m] (frobTrace b ρ) n) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_fwdDiff_iter_frobTrace_le zero_le_one m b ρ A hA hAm.le hb
  have hneg : 0 < (m : ℝ) - A := by linarith
  have htend : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (A - m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-((m : ℝ) - A))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hneg
    have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul K
    simpa [neg_sub] using h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
    (Eventually.of_forall fun n => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact hK n (by exact_mod_cast hn)

/-- **An integral trace is eventually a polynomial.** A trace of order `m` with weights below `m`
that is an integer at all large integers agrees there with a polynomial without coefficients of index
`≥ m`. Neither distinct modes nor a chain condition on the weights is needed. -/
theorem exists_polynomial_of_integral_trace {b ρ : ι → ℂ} {A : ℝ} {m : ℕ}
    (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m)
    {n₁ : ℕ} (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) :
    ∃ (n₀ : ℕ) (P : Polynomial ℂ), (∀ i, m ≤ i → P.coeff i = 0) ∧
      ∀ n : ℕ, n₀ ≤ n → frobTrace b ρ n = P.eval (n : ℂ) := by
  obtain ⟨n₀, -, -, hzero⟩ := fwdDiff_iter_eventually_zero hA hAm hb hint
  obtain ⟨P, hP, hval⟩ := exists_polynomial_of_fwdDiff_iter_zero hzero
  exact ⟨n₀, P, hP, hval⟩

/-! ### The dilation operator -/

/-- `E_{p,m}(X) = Π_{k<m} (X − p^k)`. -/
noncomputable def tatePoly (p m : ℕ) : Polynomial ℂ :=
  ∏ k ∈ range m, (Polynomial.X - Polynomial.C ((p : ℂ) ^ k))

theorem tatePoly_eval_eq_zero_iff {p m : ℕ} {z : ℂ} :
    (tatePoly p m).eval z = 0 ↔ ∃ k, k < m ∧ z = (p : ℂ) ^ k := by
  rw [tatePoly, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    refine ⟨k, Finset.mem_range.mp hk, ?_⟩
    simpa [sub_eq_zero] using h
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mpr hk, by simp [h]⟩

/-- The dilation operator `Π_{k<m} (S_p − p^k)`, where `S_p f(x) = f(p x)`. -/
noncomputable def tateDilation (p m : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ l ∈ range ((tatePoly p m).natDegree + 1), (tatePoly p m).coeff l * f ((p : ℝ) ^ l * x)

/-- The dilation operator kills polynomials of degree `< m`. -/
theorem tateDilation_polynomial {p m : ℕ} {P : Polynomial ℂ}
    (hP : ∀ i, m ≤ i → P.coeff i = 0) (x : ℝ) :
    tateDilation p m (fun y => P.eval (y : ℂ)) x = 0 := by
  have hstep : tateDilation p m (fun y => P.eval (y : ℂ)) x =
      ∑ i ∈ range (P.natDegree + 1),
        P.coeff i * (x : ℂ) ^ i * (tatePoly p m).eval ((p : ℂ) ^ i) := by
    rw [tateDilation]
    simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  rw [hstep]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i < m
  · rw [tatePoly_eval_eq_zero_iff.mpr ⟨i, hi, rfl⟩, mul_zero]
  · rw [hP i (not_lt.mp hi)]
    ring

/-- `(p^l x)^ρ = (p^ρ)^l x^ρ` for `x ≥ 0`. -/
theorem dilate_cpow (p l : ℕ) {x : ℝ} (hx : 0 ≤ x) (ρ : ℂ) :
    ((((p : ℝ) ^ l * x : ℝ)) : ℂ) ^ ρ = ((p : ℂ) ^ ρ) ^ l * (x : ℂ) ^ ρ := by
  have hpl : (0 : ℝ) ≤ (p : ℝ) ^ l := pow_nonneg (Nat.cast_nonneg p) l
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hpl hx, ← natCast_pow_cpow]
  congr 2
  push_cast
  rfl

/-- The dilation operator multiplies the weight of the mode `ρ` by `Π_{k<m} (p^ρ − p^k)`. -/
theorem tateDilation_frobTrace {b ρ : ι → ℂ} {A : ℝ} (hb : Summable fun i => ‖b i‖)
    (hA : ∀ i, (ρ i).re ≤ A) {p : ℕ} (hp : 1 ≤ p) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    tateDilation p m (frobTrace b ρ) x =
      frobTrace (fun i => b i * (tatePoly p m).eval ((p : ℂ) ^ ρ i)) ρ x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hsum : ∀ l ∈ range ((tatePoly p m).natDegree + 1),
      Summable fun i => (tatePoly p m).coeff l * (b i * (((p : ℝ) ^ l * x : ℝ) : ℂ) ^ ρ i) := by
    intro l _
    have hpl : (1 : ℝ) ≤ (p : ℝ) ^ l * x := by
      have h1 : (1 : ℝ) ≤ (p : ℝ) ^ l := one_le_pow₀ (by exact_mod_cast hp)
      nlinarith
    exact (summable_frobTerm hb hA hpl).mul_left _
  rw [tateDilation, frobTrace]
  simp_rw [frobTrace, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun i => ?_
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dilate_cpow p l hx0]
  ring

/-- A bound for `Π_{k<m} (z − p^k)` on a disc. -/
theorem exists_norm_tatePoly_eval_le (p m : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖(tatePoly p m).eval z‖ ≤ C := by
  refine ⟨∑ l ∈ range ((tatePoly p m).natDegree + 1), ‖(tatePoly p m).coeff l‖ * |R| ^ l,
    Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg _) _),
    fun z hz => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hz.trans (le_abs_self R)) l) (norm_nonneg _)

/-! ### Kronecker's theorem over `ℤ` -/

/-- At one prime: the visible modes satisfy `p^ρ = p^k` for some `k < m`. -/
theorem exists_cpow_eq_pow_of_integral_trace {b ρ : ι → ℂ} {A : ℝ} {m : ℕ}
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) {p : ℕ} (hp : 1 ≤ p) :
    ∀ i, b i ≠ 0 → ∃ k, k < m ∧ (p : ℂ) ^ ρ i = (p : ℂ) ^ k := by
  have hb0 : Summable fun i => ‖b i‖ := summable_of_order hb
  obtain ⟨n₀, -, hn₀2, hzero⟩ := fwdDiff_iter_eventually_zero hA hAm hb hint
  obtain ⟨P, hPcoeff, hP⟩ := exists_polynomial_of_fwdDiff_iter_zero hzero
  -- the dilated trace vanishes at all `n ≥ n₀`
  have hdil : ∀ n : ℕ, n₀ ≤ n → tateDilation p m (frobTrace b ρ) n = 0 := by
    intro n hn
    rw [← tateDilation_polynomial (p := p) hPcoeff (n : ℝ)]
    rw [tateDilation, tateDilation]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hcast : ((p : ℝ) ^ l * (n : ℝ)) = ((p ^ l * n : ℕ) : ℝ) := by push_cast; rfl
    have hge : n₀ ≤ p ^ l * n := by
      calc n₀ ≤ n := hn
        _ = 1 * n := (one_mul n).symm
        _ ≤ p ^ l * n := Nat.mul_le_mul_right n (Nat.one_le_pow _ _ hp)
    rw [hcast, hP _ hge, Complex.ofReal_natCast]
  -- its weights
  obtain ⟨C, hC0, hC⟩ := exists_norm_tatePoly_eval_le p m ((p : ℝ) ^ A)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hmode : ∀ i, ‖(p : ℂ) ^ ρ i‖ ≤ (p : ℝ) ^ A := by
    intro i
    have := norm_ofReal_cpow_le hpR (hA i)
    simpa using this
  have hcs : Summable fun i => ‖b i * (tatePoly p m).eval ((p : ℂ) ^ ρ i)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (hb0.mul_right C)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _ (hmode i)) (norm_nonneg _)
  have hvan : ∀ n : ℕ, n₀ ≤ n →
      frobTrace (fun i => b i * (tatePoly p m).eval ((p : ℂ) ^ ρ i)) ρ n = 0 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    rw [← tateDilation_frobTrace hb0 hA hp m hn1]
    exact hdil n hn
  have hall := eq_zero_of_frobTrace_eventually_zero hcs hρ hwf hvan
  intro i hbi
  have := hall i
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hbi
  · exact tatePoly_eval_eq_zero_iff.mp h

/-- **Kronecker's theorem over `ℤ`: integral trace-class Frobenius modules are Tate.** Distinct
modes of weights `≤ A < m`, weights without infinite ascending chain, trace class of order `m`,
integer traces at all large integers: every visible mode is one of `0, 1, …, m − 1`. -/
theorem tate_of_integral_trace {b ρ : ι → ℂ} {A : ℝ} {m : ℕ}
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) :
    ∀ i, b i ≠ 0 → ∃ k : ℕ, k < m ∧ ρ i = k := by
  intro i hbi
  obtain ⟨k, hkm, h2⟩ := exists_cpow_eq_pow_of_integral_trace hρ hwf hA hAm hb hint
    (p := 2) (by norm_num) i hbi
  obtain ⟨k', -, h3⟩ := exists_cpow_eq_pow_of_integral_trace hρ hwf hA hAm hb hint
    (p := 3) (by norm_num) i hbi
  simp only [Nat.cast_ofNat] at h2 h3
  -- the weight is `k = k'`
  have hre2 : (ρ i).re = k := by
    have h := congrArg norm h2
    rw [norm_two_cpow, norm_pow, Complex.norm_ofNat] at h
    have hlog := congrArg Real.log h
    rw [Real.log_rpow (by norm_num), Real.log_pow] at hlog
    have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_right_cancel₀ hl.ne' hlog
  have hre3 : (ρ i).re = k' := by
    have h := congrArg norm h3
    rw [norm_three_cpow, norm_pow, Complex.norm_ofNat] at h
    have hlog := congrArg Real.log h
    rw [Real.log_rpow (by norm_num), Real.log_pow] at hlog
    have hl : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    exact mul_right_cancel₀ hl.ne' hlog
  have hkk : k' = k := by
    have : (k' : ℝ) = k := by rw [← hre2, ← hre3]
    exact_mod_cast this
  rw [hkk] at h3
  refine ⟨k, hkm, cpow_two_three_injective ?_ ?_⟩
  · rw [h2, Complex.cpow_natCast]
  · rw [h3, Complex.cpow_natCast]

/-- **Traces in a discrete group `ℤ c`.** The same conclusion when the traces at all large
integers are integer multiples of one number `c ≠ 0`, for instance of `log p` for one prime `p`. The
traces of `ζ` lie in `Σ_p ℤ log p`, which is dense in `ℝ`. -/
theorem tate_of_trace_in_zmultiples {b ρ : ι → ℂ} {A : ℝ} {m : ℕ}
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) {c : ℂ} (hc : c ≠ 0) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k * c) :
    ∀ i, b i ≠ 0 → ∃ k : ℕ, k < m ∧ ρ i = k := by
  have hscale : ∀ x : ℝ, frobTrace (fun i => b i / c) ρ x = frobTrace b ρ x / c := by
    intro x
    rw [frobTrace, frobTrace, ← tsum_div_const]
    refine tsum_congr fun i => ?_
    ring
  have hb' : Summable fun i => ‖b i / c‖ * (1 + ‖ρ i‖) ^ m := by
    have h := hb.mul_left ‖c‖⁻¹
    refine h.congr fun i => ?_
    rw [norm_div, div_eq_mul_inv]
    ring
  have hint' : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace (fun i => b i / c) ρ n = k := by
    intro n hn
    obtain ⟨k, hk⟩ := hint n hn
    exact ⟨k, by rw [hscale, hk, mul_div_assoc, div_self hc, mul_one]⟩
  intro i hbi
  exact tate_of_integral_trace hρ hwf hA hAm hb' hint' i (div_ne_zero hbi hc)

/-- **With the duality `ρ ↔ 1 − ρ` only `0` and `1` survive.** If the visible modes are closed
under `ρ ↦ 1 − ρ`, the visible modes of an integral trace-class module are among `0` and `1`. -/
theorem tate_of_integral_trace_dual {b ρ : ι → ℂ} {A : ℝ} {m : ℕ}
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖) ^ m) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k)
    (hdual : ∀ i, b i ≠ 0 → ∃ j, b j ≠ 0 ∧ ρ j = 1 - ρ i) :
    ∀ i, b i ≠ 0 → ρ i = 0 ∨ ρ i = 1 := by
  intro i hbi
  obtain ⟨k, -, hk⟩ := tate_of_integral_trace hρ hwf hA hAm hb hint i hbi
  obtain ⟨j, hbj, hj⟩ := hdual i hbi
  obtain ⟨l, -, hl⟩ := tate_of_integral_trace hρ hwf hA hAm hb hint j hbj
  rw [hl, hk] at hj
  have hkl : l + k = 1 := by
    have : ((l + k : ℕ) : ℂ) = 1 := by
      push_cast
      linear_combination hj
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · left
    rw [hk, h0]
    simp
  · right
    have : k = 1 := by omega
    rw [hk, this]
    simp

/-- **No integral trace-class module lives in the open strip.** A visible mode of an integral
trace-class module of order one with all weights `≤ A < 1` is the mode `0`; in particular none has
`0 < Re ρ`. -/
theorem not_visible_in_open_strip {b ρ : ι → ℂ} {A : ℝ}
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hA1 : A < 1) (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖)) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) :
    ∀ i, b i ≠ 0 → ρ i = 0 := by
  intro i hbi
  obtain ⟨k, hk1, hk⟩ := tate_of_integral_trace (m := 1) hρ hwf hA (by simpa using hA1)
    (by simpa using hb) hint i hbi
  have : k = 0 := by omega
  rw [hk, this]
  simp

end GaloisForLFunctions.InfiniteRankPurityTheory
