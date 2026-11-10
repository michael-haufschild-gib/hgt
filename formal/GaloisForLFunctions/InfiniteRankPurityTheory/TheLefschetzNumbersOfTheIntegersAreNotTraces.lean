import GaloisForLFunctions.InfiniteRankPurityTheory.IntegralTraceClassModulesOverTheIntegersAreTate
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta
import GaloisForLFunctions.RHTower.XiHadamardFinitePart
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour

/-!
# The Lefschetz numbers of the integers are not traces

The weight filtration of a Frobenius module is its filtration by the growth of the traces as soon as
the module is of trace class. This module determines which arithmetic sequences are traces at all.

A module `(b, ρ)` is of **trace class of order `m` at the Frobenius `q`** when
`Σ ‖b_i‖ q^{Re ρ_i} (1 + ‖ρ_i‖)^m < ∞` (`TraceClassAt`). At `q = 1` this says that the weighted rank
is finite; at `q ≥ 2` it allows infinitely many modes of weight tending to `−∞`, each with a weight
of size one, such as the trivial zeros. Dilation by `q` turns the trace at `qx` into the trace of the
module `(b_i q^{ρ_i}, ρ_i)` at `x` (`frobTrace_dilate`), so the calculus of traces applies.

* `tendsto_fwdDiff_iter_frobTrace_of_traceClassAt`: the `m`-th difference of a trace of order `m`
  with weights below `m` tends to zero. A trace is smooth at infinity.
* `exists_polynomial_of_integral_trace_at`, `tate_of_integral_trace_at`,
  `tate_of_integral_trace_dual_at`: Kronecker over `ℤ` at any Frobenius: an integral trace is
  eventually a polynomial, with distinct modes and weights without ascending chain the module is a
  sum of Tate twists, and with the duality `ρ ↔ 1 − ρ` only the modes `0` and `1` remain.
* `IsTrace m f`: `f` agrees at all large integers with the trace of a module of trace class of order
  `m` at some Frobenius, with weights below `m`. Traces are closed under differences and dilations
  (`IsTrace.sub`, `IsTrace.dilate`).
* `not_isTrace_of_primePower_support`, `not_isTrace_vonMangoldt`: a sequence supported on the prime
  powers that does not tend to zero along the powers of one prime is not a trace of any order: along
  `n = p^a` the `m`-th difference of `n ↦ f(pn)` is `± f(p^{a+1})`. So the Lefschetz numbers `Λ(n)` of
  the scaling flow are not a trace, and no constituent with an Euler product is of trace class.
* `not_isTrace_of_two_jumps`, `not_isTrace_mertens`, `not_isTrace_primeCounting`: an integer sequence
  whose consecutive differences take two values infinitely often is not a trace of any order; so the
  Mertens function, which is the defect of the orientation cover, and the prime counting function
  are not traces.
* `lagModule_traceClassAt_zero`, `lagModule_not_traceClassAt_one`: with the lag weights
  `1/(ρ(1−ρ))` the zeros of `ξ` form a module of trace class of order zero at every Frobenius and of
  order one at none.

So the zero motive carries the growth filtration of order zero and no calculus of traces: an
explicit formula for `Λ`, for the Mertens function or for the prime counting function cannot
converge in trace class of any order, at any Frobenius, with any modes.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

variable {ι : Type*}

/-! ### Trace class at a Frobenius -/

/-- The module `(b, ρ)` is of trace class of order `m` at the Frobenius `q`:
`Σ ‖b_i‖ q^{Re ρ_i} (1 + ‖ρ_i‖)^m < ∞`. -/
def TraceClassAt (q m : ℕ) (b ρ : ι → ℂ) : Prop :=
  Summable fun i => ‖b i‖ * (q : ℝ) ^ (ρ i).re * (1 + ‖ρ i‖) ^ m

theorem norm_mul_natCast_cpow {q : ℕ} (hq : 1 ≤ q) (b ρ : ℂ) :
    ‖b * (q : ℂ) ^ ρ‖ = ‖b‖ * (q : ℝ) ^ ρ.re := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]

/-- Trace class at `q` is trace class of the dilated module `(b_i q^{ρ_i}, ρ_i)`. -/
theorem TraceClassAt.dilated {q m : ℕ} (hq : 1 ≤ q) {b ρ : ι → ℂ} (hb : TraceClassAt q m b ρ) :
    Summable fun i => ‖b i * (q : ℂ) ^ ρ i‖ * (1 + ‖ρ i‖) ^ m := by
  have h : Summable fun i => ‖b i‖ * (q : ℝ) ^ (ρ i).re * (1 + ‖ρ i‖) ^ m := hb
  simpa only [norm_mul_natCast_cpow hq] using h

/-- **Dilation.** The trace at `q x` is the trace of the module `(b_i q^{ρ_i}, ρ_i)` at `x`. -/
theorem frobTrace_dilate (b ρ : ι → ℂ) (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    frobTrace b ρ ((q : ℝ) * x) = frobTrace (fun i => b i * (q : ℂ) ^ ρ i) ρ x := by
  rw [frobTrace, frobTrace]
  refine tsum_congr fun i => ?_
  have h := dilate_cpow q 1 hx (ρ i)
  rw [pow_one, pow_one] at h
  rw [h, mul_assoc]

/-- Trace class at `q` is trace class at every multiple of `q` when the weights are bounded above. -/
theorem TraceClassAt.mul_right {q m : ℕ} {b ρ : ι → ℂ} {A : ℝ} (hA : ∀ i, (ρ i).re ≤ A)
    (hb : TraceClassAt q m b ρ) {r : ℕ} (hr : 1 ≤ r) : TraceClassAt (q * r) m b ρ := by
  have hterm : ∀ i, 0 ≤ ‖b i‖ * ((q * r : ℕ) : ℝ) ^ (ρ i).re * (1 + ‖ρ i‖) ^ m := fun i =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (by linarith [norm_nonneg (ρ i)]) _)
  refine Summable.of_nonneg_of_le hterm (fun i => ?_) (hb.mul_left ((r : ℝ) ^ |A|))
  have h1 : ((q * r : ℕ) : ℝ) ^ (ρ i).re = (q : ℝ) ^ (ρ i).re * (r : ℝ) ^ (ρ i).re := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg r)
  have h2 : (r : ℝ) ^ (ρ i).re ≤ (r : ℝ) ^ |A| :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hr) ((hA i).trans (le_abs_self A))
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ (ρ i).re := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp0 : (0 : ℝ) ≤ (1 + ‖ρ i‖) ^ m := pow_nonneg (by linarith [norm_nonneg (ρ i)]) _
  rw [h1]
  calc ‖b i‖ * ((q : ℝ) ^ (ρ i).re * (r : ℝ) ^ (ρ i).re) * (1 + ‖ρ i‖) ^ m
      ≤ ‖b i‖ * ((q : ℝ) ^ (ρ i).re * (r : ℝ) ^ |A|) * (1 + ‖ρ i‖) ^ m :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hq0) (norm_nonneg _)) hp0
    _ = (r : ℝ) ^ |A| * (‖b i‖ * (q : ℝ) ^ (ρ i).re * (1 + ‖ρ i‖) ^ m) := by ring

/-- The trace converges absolutely at every `x ≥ q`. -/
theorem TraceClassAt.summable_term {q m : ℕ} (hq : 1 ≤ q) {b ρ : ι → ℂ} {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) (hb : TraceClassAt q m b ρ) {x : ℝ} (hx : (q : ℝ) ≤ x) :
    Summable fun i => b i * (x : ℂ) ^ ρ i := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hy : (1 : ℝ) ≤ x / q := (one_le_div hq0).mpr hx
  have h := summable_frobTerm (summable_of_order (hb.dilated hq)) hA hy
  refine h.congr fun i => ?_
  have hd := dilate_cpow q 1 (by positivity : (0 : ℝ) ≤ x / q) (ρ i)
  rw [pow_one, pow_one, mul_div_cancel₀ x hq0.ne'] at hd
  rw [hd, mul_assoc]

/-- **A trace is smooth at infinity.** The `m`-th difference of the trace of a module of trace class
of order `m` at `q`, with weights below `m`, tends to zero. -/
theorem tendsto_fwdDiff_iter_frobTrace_of_traceClassAt {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ}
    (hq : 1 ≤ q) (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m) (hb : TraceClassAt q m b ρ) :
    Tendsto (fun n : ℕ => (fwdDiff (1 : ℝ))^[m] (frobTrace b ρ) n) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨K, hK0, hK⟩ := exists_norm_fwdDiff_iter_frobTrace_le (h := (q : ℝ)⁻¹)
    (inv_nonneg.mpr hq0.le) m (fun i => b i * (q : ℂ) ^ ρ i) ρ A hA hAm.le (hb.dilated hq)
  -- a difference of step `1` at `x` is a difference of step `1/q` of the dilated trace at `x/q`
  have hrel : ∀ x : ℝ, 0 ≤ x → (fwdDiff (1 : ℝ))^[m] (frobTrace b ρ) x =
      (fwdDiff (q : ℝ)⁻¹)^[m] (frobTrace (fun i => b i * (q : ℂ) ^ ρ i) ρ) (x / q) := by
    intro x hx
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun k _ => ?_
    have harg : x + k • (1 : ℝ) = (q : ℝ) * (x / q + k • (q : ℝ)⁻¹) := by
      simp only [nsmul_eq_mul, mul_one]
      field_simp
    have hnn : (0 : ℝ) ≤ x / q + k • (q : ℝ)⁻¹ :=
      add_nonneg (div_nonneg hx hq0.le) (nsmul_nonneg (inv_nonneg.mpr hq0.le) k)
    rw [harg, frobTrace_dilate b ρ q hnn]
  have hneg : 0 < (m : ℝ) - A := by linarith
  have htend : Tendsto (fun n : ℕ => K * ((n : ℝ) / q) ^ (A - m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-((m : ℝ) - A))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hneg
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / q) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const hq0
    have h3 := (h1.comp h2).const_mul K
    simpa [neg_sub] using h3
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
    (Eventually.of_forall fun n => norm_nonneg _) ?_
  filter_upwards [eventually_gt_atTop q] with n hn
  rw [hrel n (Nat.cast_nonneg n)]
  exact hK _ ((one_lt_div hq0).mpr (by exact_mod_cast hn))

/-- **An integral trace is eventually a polynomial**, at any Frobenius. -/
theorem exists_polynomial_of_integral_trace_at {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ} (hq : 1 ≤ q)
    (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m) (hb : TraceClassAt q m b ρ) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) :
    ∃ (n₀ : ℕ) (P : Polynomial ℂ), (∀ i, m ≤ i → P.coeff i = 0) ∧
      ∀ n : ℕ, n₀ ≤ n → frobTrace b ρ n = P.eval (n : ℂ) := by
  have htend := (tendsto_fwdDiff_iter_frobTrace_of_traceClassAt hq hA hAm hb).norm
  rw [norm_zero] at htend
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds one_pos))
  have hzero : ∀ n : ℕ, max n₁ n₂ ≤ n → (fwdDiff (1 : ℝ))^[m] (frobTrace b ρ) n = 0 := by
    intro n hn
    obtain ⟨k, hk⟩ := exists_int_fwdDiff_iter hint m (le_trans (le_max_left _ _) hn)
    have hlt : ‖(k : ℂ) - ((0 : ℤ) : ℂ)‖ < 1 := by
      rw [← hk]
      simpa using hn₂ n (le_trans (le_max_right _ _) hn)
    rw [hk, int_eq_of_norm_sub_lt_one hlt]
    simp
  obtain ⟨P, hP, hval⟩ := exists_polynomial_of_fwdDiff_iter_zero hzero
  exact ⟨_, P, hP, hval⟩

/-- **Kronecker over `ℤ` at any Frobenius.** A module of trace class of order `m` at `q`, with
distinct modes, weights below `m` without ascending chain and integer traces at all large integers,
is a sum of Tate twists `0, …, m − 1`. -/
theorem tate_of_integral_trace_at {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ} (hq : 1 ≤ q)
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : TraceClassAt q m b ρ) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) :
    ∀ i, b i ≠ 0 → ∃ k : ℕ, k < m ∧ ρ i = k := by
  intro i hbi
  have hint' : ∀ n : ℕ, n₁ ≤ n →
      ∃ k : ℤ, frobTrace (fun i => b i * (q : ℂ) ^ ρ i) ρ n = k := by
    intro n hn
    obtain ⟨k, hk⟩ := hint (q * n) (hn.trans (Nat.le_mul_of_pos_left n hq))
    refine ⟨k, ?_⟩
    rw [← frobTrace_dilate b ρ q (Nat.cast_nonneg n), ← hk]
    push_cast
    rfl
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  exact tate_of_integral_trace hρ hwf hA hAm (hb.dilated hq) hint' i
    (mul_ne_zero hbi (by simp [Complex.cpow_eq_zero_iff, hq0]))

/-- **Kronecker with the duality at any Frobenius.** If moreover the visible modes are closed
under `ρ ↦ 1 − ρ`, they are among `0` and `1`. -/
theorem tate_of_integral_trace_dual_at {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ} (hq : 1 ≤ q)
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A)
    (hAm : A < m) (hb : TraceClassAt q m b ρ) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k)
    (hdual : ∀ i, b i ≠ 0 → ∃ j, b j ≠ 0 ∧ ρ j = 1 - ρ i) :
    ∀ i, b i ≠ 0 → ρ i = 0 ∨ ρ i = 1 := by
  intro i hbi
  obtain ⟨k, -, hk⟩ := tate_of_integral_trace_at hq hρ hwf hA hAm hb hint i hbi
  obtain ⟨j, hbj, hj⟩ := hdual i hbi
  obtain ⟨l, -, hl⟩ := tate_of_integral_trace_at hq hρ hwf hA hAm hb hint j hbj
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

/-! ### Sequences that are traces -/

/-- `f` agrees at all large integers with the trace of a Frobenius module of trace class of order
`m` at some Frobenius, with weights below `m`. -/
def IsTrace (m : ℕ) (f : ℕ → ℂ) : Prop :=
  ∃ (ι : Type) (b ρ : ι → ℂ) (A : ℝ) (q : ℕ), 1 ≤ q ∧ (∀ i, (ρ i).re ≤ A) ∧ A < m ∧
    TraceClassAt q m b ρ ∧ ∀ᶠ n : ℕ in atTop, f n = frobTrace b ρ n

/-- The `m`-th difference of a trace of order `m` tends to zero. -/
theorem IsTrace.tendsto_fwdDiff {m : ℕ} {f : ℕ → ℂ} (hf : IsTrace m f) :
    Tendsto (fun n : ℕ => (fwdDiff (1 : ℕ))^[m] f n) atTop (𝓝 0) := by
  obtain ⟨ι, b, ρ, A, q, hq, hA, hAm, hb, hfe⟩ := hf
  refine (tendsto_fwdDiff_iter_frobTrace_of_traceClassAt hq hA hAm hb).congr' ?_
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hfe
  filter_upwards [eventually_ge_atTop n₀] with n hn
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcast : ((n : ℝ) + k • (1 : ℝ)) = ((n + k • 1 : ℕ) : ℝ) := by simp
  rw [hcast, ← hn₀ (n + k • 1) (hn.trans (Nat.le_add_right _ _))]

/-- Traces are closed under dilation of the argument. -/
theorem IsTrace.dilate {m : ℕ} {f : ℕ → ℂ} (hf : IsTrace m f) {Q : ℕ} (hQ : 1 ≤ Q) :
    IsTrace m fun n => f (Q * n) := by
  obtain ⟨ι, b, ρ, A, q, hq, hA, hAm, hb, hfe⟩ := hf
  refine ⟨ι, fun i => b i * (Q : ℂ) ^ ρ i, ρ, A, q, hq, hA, hAm, ?_, ?_⟩
  · refine (hb.mul_right hA hQ).congr fun i => ?_
    rw [norm_mul_natCast_cpow hQ]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg Q)]
    ring
  · have hmul : Tendsto (fun n : ℕ => Q * n) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hQ) tendsto_id
    filter_upwards [hmul.eventually hfe] with n hn
    rw [hn, ← frobTrace_dilate b ρ Q (Nat.cast_nonneg n)]
    push_cast
    rfl

/-- Traces are closed under differences. -/
theorem IsTrace.sub {m : ℕ} {f g : ℕ → ℂ} (hf : IsTrace m f) (hg : IsTrace m g) :
    IsTrace m fun n => f n - g n := by
  obtain ⟨ι, b, ρ, A, q, hq, hA, hAm, hb, hfe⟩ := hf
  obtain ⟨κ, c, σ, B, r, hr, hB, hBm, hc, hge⟩ := hg
  have hb' : TraceClassAt (q * r) m b ρ := hb.mul_right hA hr
  have hc' : TraceClassAt (q * r) m c σ := by
    rw [mul_comm]
    exact hc.mul_right hB hq
  have hqr : 1 ≤ q * r := Nat.mul_pos hq hr
  refine ⟨ι ⊕ κ, Sum.elim b fun j => -c j, Sum.elim ρ σ, max A B, q * r, hqr, ?_, max_lt hAm hBm,
    ?_, ?_⟩
  · rintro (i | j)
    · exact (hA i).trans (le_max_left _ _)
    · exact (hB j).trans (le_max_right _ _)
  · refine Summable.sum _ ?_ ?_
    · simpa only [TraceClassAt, Function.comp_def, Sum.elim_inl] using hb'
    · simpa only [TraceClassAt, Function.comp_def, Sum.elim_inr, norm_neg] using hc'
  · filter_upwards [hfe, hge, eventually_ge_atTop (q * r)] with n h1 h2 hn
    have hx : ((q * r : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have s1 := (hb'.summable_term hqr hA hx).hasSum
    have s2 := ((hc'.summable_term hqr hB hx).neg).hasSum
    have hsum : HasSum (fun t : ι ⊕ κ => Sum.elim b (fun j => -c j) t *
        ((n : ℝ) : ℂ) ^ Sum.elim ρ σ t)
        ((∑' i, b i * ((n : ℝ) : ℂ) ^ ρ i) + ∑' j, -(c j * ((n : ℝ) : ℂ) ^ σ j)) := by
      refine HasSum.sum ?_ ?_
      · simpa only [Function.comp_def, Sum.elim_inl] using s1
      · simpa only [Function.comp_def, Sum.elim_inr, neg_mul] using s2
    rw [h1, h2]
    show frobTrace b ρ n - frobTrace c σ n = frobTrace _ _ n
    rw [frobTrace, frobTrace, frobTrace, hsum.tsum_eq, tsum_neg]
    ring

/-- An integer-valued trace is eventually a polynomial. -/
theorem IsTrace.eventually_polynomial {m : ℕ} {f : ℕ → ℤ} (hf : IsTrace m fun n => (f n : ℂ)) :
    ∃ (n₀ : ℕ) (P : Polynomial ℂ), ∀ n : ℕ, n₀ ≤ n → (f n : ℂ) = P.eval (n : ℂ) := by
  obtain ⟨ι, b, ρ, A, q, hq, hA, hAm, hb, hfe⟩ := hf
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hfe
  obtain ⟨n₀, P, -, hP⟩ := exists_polynomial_of_integral_trace_at hq hA hAm hb (n₁ := n₁)
    fun n hn => ⟨f n, (hn₁ n hn).symm⟩
  exact ⟨max n₀ n₁, P, fun n hn => (hn₁ n (le_trans (le_max_right _ _) hn)).trans
    (hP n (le_trans (le_max_left _ _) hn))⟩

/-! ### Arithmetic sequences -/

/-- **An integer sequence with two recurring jumps is not a trace.** A polynomial whose
differences take two values infinitely often does not exist. -/
theorem not_isTrace_of_two_jumps {f : ℕ → ℤ} {a b : ℤ} (hab : a ≠ b)
    (ha : ∃ᶠ n in atTop, f (n + 1) - f n = a) (hb : ∃ᶠ n in atTop, f (n + 1) - f n = b)
    (m : ℕ) : ¬ IsTrace m fun n => (f n : ℂ) := by
  intro hf
  obtain ⟨n₀, P, hP⟩ := hf.eventually_polynomial
  set Q : Polynomial ℂ := P.comp (Polynomial.X + 1) - P with hQ
  have hQeval : ∀ n : ℕ, n₀ ≤ n → Q.eval (n : ℂ) = ((f (n + 1) - f n : ℤ) : ℂ) := by
    intro n hn
    have h1 := hP (n + 1) (by omega)
    rw [hQ, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
    push_cast at h1 ⊢
    rw [← h1, ← hP n hn]
  have key : ∀ c : ℤ, (∃ᶠ n in atTop, f (n + 1) - f n = c) → Q = Polynomial.C (c : ℂ) := by
    intro c hc
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : {n : ℕ | n₀ ≤ n ∧ f (n + 1) - f n = c}.Infinite := by
      rw [← Nat.frequently_atTop_iff_infinite]
      exact (hc.and_eventually (eventually_ge_atTop n₀)).mono fun n h => ⟨h.2, h.1⟩
    refine (hinf.image Nat.cast_injective.injOn).mono ?_
    rintro _ ⟨n, ⟨hn, hc'⟩, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.eval_C]
    rw [hQeval n hn, hc']
  have h2 := key b hb
  rw [key a ha] at h2
  exact hab (by exact_mod_cast Polynomial.C_injective h2)

/-- `p (p^a + k)` is not a prime power for a prime `p` and `0 < k < p^a`. -/
theorem not_isPrimePow_prime_mul_add {p a k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hk : k < p ^ a) :
    ¬ IsPrimePow (p * (p ^ a + k)) := by
  rw [isPrimePow_nat_iff]
  rintro ⟨q, j, hq, hj, hqj⟩
  have hpq : p ∣ q := by
    have : p ∣ q ^ j := hqj ▸ dvd_mul_right p _
    exact hp.dvd_of_dvd_pow this
  have hqp : q = p := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).symm
  rw [hqp] at hqj
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [pow_succ, mul_comm] at hqj
  have hval : p ^ i = p ^ a + k := Nat.eq_of_mul_eq_mul_left hp.pos hqj
  have hlow : p ^ a < p ^ i := by omega
  have hupp : p ^ i < p ^ (a + 1) := by
    rw [pow_succ, hval]
    have h2 : 2 ≤ p := hp.two_le
    nlinarith
  have h1 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlow
  have h2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hupp
  omega

/-- **A sequence with an Euler product is not a trace.** If `f` vanishes off the prime powers and
`f(p^k)` does not tend to zero along the powers of one prime `p`, then `f` is not a trace of any
order: along `n = p^a` the `m`-th difference of `n ↦ f(pn)` is `± f(p^{a+1})`. -/
theorem not_isTrace_of_primePower_support {f : ℕ → ℂ} (h0 : ∀ n, ¬ IsPrimePow n → f n = 0)
    {p : ℕ} (hp : p.Prime) (hlim : ¬ Tendsto (fun k : ℕ => f (p ^ k)) atTop (𝓝 0)) (m : ℕ) :
    ¬ IsTrace m f := by
  intro hf
  have htend := (hf.dilate (Q := p) hp.one_lt.le).tendsto_fwdDiff
  have hsub := htend.comp (tendsto_pow_atTop_atTop_of_one_lt hp.one_lt)
  have hev : ∀ᶠ a : ℕ in atTop, ((fun n : ℕ => (fwdDiff (1 : ℕ))^[m]
      (fun n : ℕ => f (p * n)) n) ∘ fun a : ℕ => p ^ a) a = (-1 : ℂ) ^ m * f (p ^ (a + 1)) := by
    filter_upwards [eventually_gt_atTop m] with a ha
    have hma : m < p ^ a := lt_trans ha (Nat.lt_pow_self hp.one_lt)
    simp only [Function.comp_apply]
    rw [fwdDiff_iter_eq_sum_shift, Finset.sum_eq_single 0]
    · have hval : p * (p ^ a + 0 • 1) = p ^ (a + 1) := by
        rw [pow_succ]
        simp [mul_comm]
      rw [hval, zsmul_eq_mul]
      simp
    · intro k hk hk0
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hnot := not_isPrimePow_prime_mul_add (a := a) hp (Nat.pos_of_ne_zero hk0)
        (lt_of_le_of_lt hkm hma)
      have hzero : f (p * (p ^ a + k • 1)) = 0 := h0 _ (by simpa using hnot)
      rw [hzero, smul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
  have h1 : Tendsto (fun a : ℕ => (-1 : ℂ) ^ m * f (p ^ (a + 1))) atTop (𝓝 0) :=
    hsub.congr' hev
  have hsq : ∀ a : ℕ, (-1 : ℂ) ^ m * ((-1 : ℂ) ^ m * f (p ^ (a + 1))) = f (p ^ (a + 1)) := by
    intro a
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have h2 : Tendsto (fun a : ℕ => f (p ^ (a + 1))) atTop (𝓝 0) := by
    have h3 := h1.const_mul ((-1 : ℂ) ^ m)
    simpa only [hsq, mul_zero] using h3
  exact hlim ((tendsto_add_atTop_iff_nat 1).mp h2)

/-- **The Lefschetz numbers `Λ(n)` are not a trace of any order**: `Λ` is supported on the prime
powers and `Λ(2^k) = log 2`. -/
theorem not_isTrace_vonMangoldt (m : ℕ) :
    ¬ IsTrace m fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
  refine not_isTrace_of_primePower_support (fun n hn => ?_) Nat.prime_two (fun h => ?_) m
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp
  · have hconst : ∀ᶠ k : ℕ in atTop,
        ((ArithmeticFunction.vonMangoldt (2 ^ k) : ℝ) : ℂ) = (Real.log 2 : ℂ) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have h' : Tendsto (fun _ : ℕ => (Real.log 2 : ℂ)) atTop (𝓝 0) := h.congr' hconst
    have hval := tendsto_nhds_unique h' tendsto_const_nhds
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact hlog.ne (by exact_mod_cast hval)

/-- **The Mertens function is not a trace of any order.** Its jumps are `μ(n)`, which is `0` at the
multiples of `4` and `−1` at the primes. -/
theorem not_isTrace_mertens (m : ℕ) :
    ¬ IsTrace m fun N : ℕ =>
      ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  have hjump : ∀ n : ℕ, (∑ k ∈ Finset.Icc 1 (n + 1), ArithmeticFunction.moebius k) -
      ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k = ArithmeticFunction.moebius (n + 1) := by
    intro n
    rw [Finset.sum_Icc_succ_top (by omega)]
    ring
  refine not_isTrace_of_two_jumps (a := 0) (b := -1) (by norm_num) ?_ ?_ m
  · refine Filter.frequently_atTop.mpr fun N => ⟨4 * (N + 1) - 1, by omega, ?_⟩
    rw [hjump]
    have h4 : 4 * (N + 1) - 1 + 1 = 4 * (N + 1) := by omega
    rw [h4]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    have := hsq 2 ⟨N + 1, by ring⟩
    simp at this
  · refine Filter.frequently_atTop.mpr fun N => ?_
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (N + 1)
    refine ⟨p - 1, by omega, ?_⟩
    rw [hjump]
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1, ArithmeticFunction.moebius_apply_prime hprime]

/-- **The prime counting function is not a trace of any order.** -/
theorem not_isTrace_primeCounting (m : ℕ) :
    ¬ IsTrace m fun N : ℕ => ((Nat.primeCounting N : ℤ) : ℂ) := by
  have hjump : ∀ n : ℕ, (Nat.primeCounting (n + 1) : ℤ) - Nat.primeCounting n =
      if (n + 1).Prime then 1 else 0 := by
    intro n
    rw [Nat.primeCounting, Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
    push_cast
    split_ifs <;> ring
  refine not_isTrace_of_two_jumps (a := 0) (b := 1) (by norm_num) ?_ ?_ m
  · refine Filter.frequently_atTop.mpr fun N => ⟨4 * (N + 1) - 1, by omega, ?_⟩
    rw [hjump]
    have h4 : 4 * (N + 1) - 1 + 1 = 4 * (N + 1) := by omega
    have h22 : 4 * (N + 1) = 2 * (2 * (N + 1)) := by ring
    rw [h4, if_neg]
    rw [h22]
    exact Nat.not_prime_mul (by norm_num) (by omega)
  · refine Filter.frequently_atTop.mpr fun N => ?_
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (N + 1)
    refine ⟨p - 1, by omega, ?_⟩
    rw [hjump]
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1, if_pos hprime]

/-! ### The zero motive with its lag weights -/

open GaloisForLFunctions.InfiniteRankWeilTheory renaming lagWeight → lagW,
  summable_norm_lagWeight → summable_norm_lagW

/-- With the lag weights the zeros form a module of trace class of order zero at every Frobenius. -/
theorem lagModule_traceClassAt_zero {q : ℕ} (hq : 1 ≤ q) :
    TraceClassAt q 0 lagW fun z : XiZeroCopy => (z.1 : ℂ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    (summable_norm_lagW.mul_right (q : ℝ))
  rw [pow_zero, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (z.1 : ℂ).re ≤ 1 := (re_lt_one_of_xi_eq_zero (xi_xiZeroCopy_eq_zero z)).le
  calc (q : ℝ) ^ (z.1 : ℂ).re ≤ (q : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 hre
    _ = q := Real.rpow_one _

/-- **The zero motive has no order above zero.** With the lag weights the zeros are of trace class
of order one at no Frobenius: `Σ 1/‖ρ‖ = ∞`. -/
theorem lagModule_not_traceClassAt_one {q : ℕ} (hq : 1 ≤ q) :
    ¬ TraceClassAt q 1 lagW fun z : XiZeroCopy => (z.1 : ℂ) := by
  intro h
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine XiAtlasFinitePart.not_summable_norm_inv_xiZero
    (Summable.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => ?_) h)
  set w : ℂ := (z.1 : ℂ) with hw
  have hz : xi w = 0 := xi_xiZeroCopy_eq_zero z
  have hre0 : 0 < w.re := re_pos_of_xi_eq_zero hz
  have hre1 : w.re < 1 := re_lt_one_of_xi_eq_zero hz
  have hw0 : w ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre0; exact lt_irrefl _ hre0
  have h1w : 1 - w ≠ 0 := fun h0 => by
    have : w.re = 1 := by
      have := congrArg Complex.re (sub_eq_zero.mp h0)
      simpa using this.symm
    linarith
  have hn0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hn1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr h1w
  have htri : ‖1 - w‖ ≤ 1 + ‖w‖ := by
    calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ := by rw [norm_one]
  have hqpow : (1 : ℝ) ≤ (q : ℝ) ^ w.re := Real.one_le_rpow hq1 hre0.le
  show ‖(XiAtlasFinitePart.xiZero z)⁻¹‖ ≤ ‖lagW z‖ * (q : ℝ) ^ w.re * (1 + ‖w‖) ^ 1
  have hlag : ‖lagW z‖ = 1 / (‖w‖ * ‖1 - w‖) := by
    rw [GaloisForLFunctions.InfiniteRankWeilTheory.lagWeight, norm_div, norm_one, norm_mul]
  rw [XiAtlasFinitePart.xiZero, norm_inv, hlag, pow_one]
  have hbase : ‖w‖⁻¹ ≤ 1 / (‖w‖ * ‖1 - w‖) * (1 + ‖w‖) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (mul_pos hn0 hn1), inv_mul_eq_div,
      mul_comm ‖w‖, mul_div_assoc, div_self hn0.ne', mul_one]
    exact htri
  calc ‖w‖⁻¹ ≤ 1 / (‖w‖ * ‖1 - w‖) * (1 + ‖w‖) := hbase
    _ ≤ 1 / (‖w‖ * ‖1 - w‖) * (q : ℝ) ^ w.re * (1 + ‖w‖) := by
        have hpos : 0 ≤ 1 / (‖w‖ * ‖1 - w‖) := by positivity
        nlinarith [mul_nonneg hpos (by linarith : (0 : ℝ) ≤ 1 + ‖w‖)]

end GaloisForLFunctions.InfiniteRankPurityTheory
