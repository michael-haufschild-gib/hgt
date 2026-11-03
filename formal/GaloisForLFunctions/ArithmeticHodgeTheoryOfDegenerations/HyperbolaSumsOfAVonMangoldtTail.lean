import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Hyperbola sums of a von Mangoldt tail

Let `δ : ℕ → ℂ` tend to `0` with increments `‖δ(k+1) − δ(k)‖ ≤ C Λ(k+1)/(k+1)`, as the tail of a
convergent twisted series `Σ χ(m)Λ(m)/m` does. Read along the hyperbola `n ↦ ⌊N/n⌋`:

* **Block oscillation** (`tendsto_sum_blockOsc_div`): with `osc_n` the oscillation of `δ` on the
  block `⌊N/(n+1)⌋ ≤ k ≤ ⌊N/n⌋`, `Σ_{n ≤ N} osc_n/n → 0`. For `n ≤ K` the block lies far out, where
  `δ` is small; for `n > K`, `1/n < 2m/N` on the block, and the blocks tile `(0, N/(K+1)]`, so
  Chebyshev's `ψ(x) ≤ (log 4 + 4)x` bounds the tail by `2C(log 4 + 4)/(K+1)`.
* **Mean-zero periodic weights** (`tendsto_sum_periodic_mul_hyperbola`):
  `Σ_{n ≤ N} v(n) δ(⌊N/n⌋)/n → 0` for every periodic `v` of mean zero (summation by parts).
* **Constant weight** (`tendsto_sum_hyperbola_sub_integral`):
  `Σ_{n ≤ N} δ(⌊N/n⌋)/n − ∫_0^{log N} δ(⌊e^u⌋) du → 0`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticFunction (vonMangoldt)

/-- Increments of a von Mangoldt tail: `‖δ(k+1) − δ(k)‖ ≤ C Λ(k+1)/(k+1)`. -/
def HasVonMangoldtIncrements (δ : ℕ → ℂ) (C : ℝ) : Prop :=
  ∀ k : ℕ, ‖δ (k + 1) - δ k‖ ≤ C * (vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ))

variable {δ : ℕ → ℂ} {C : ℝ}

theorem vonMangoldt_div_nonneg (m : ℕ) : 0 ≤ vonMangoldt m / (m : ℝ) :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg m)

/-- Across a block: `‖δ(b) − δ(a)‖ ≤ C Σ_{a < m ≤ b} Λ(m)/m`. -/
theorem norm_sub_le_sum_Ioc (hinc : HasVonMangoldtIncrements δ C) {a b : ℕ} (hab : a ≤ b) :
    ‖δ b - δ a‖ ≤ C * ∑ m ∈ Ioc a b, vonMangoldt m / (m : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, mul_add]
    have h := norm_add_le (δ (b + 1) - δ b) (δ b - δ a)
    rw [sub_add_sub_cancel] at h
    have := hinc b
    push_cast at this ⊢
    linarith

/-! ### Block oscillation -/

/-- The oscillation of `δ` on the block `⌊N/(n+1)⌋ ≤ k ≤ ⌊N/n⌋` against its right end. -/
def blockOsc (δ : ℕ → ℂ) (N n : ℕ) : ℝ :=
  (((Icc (N / (n + 1)) (N / n)).sup fun k => ‖δ k - δ (N / n)‖₊ : NNReal) : ℝ)

theorem blockOsc_nonneg (N n : ℕ) : 0 ≤ blockOsc δ N n := NNReal.coe_nonneg _

theorem norm_sub_le_blockOsc {N n k : ℕ} (hk : k ∈ Icc (N / (n + 1)) (N / n)) :
    ‖δ k - δ (N / n)‖ ≤ blockOsc δ N n := by
  unfold blockOsc
  have := Finset.le_sup (f := fun k => ‖δ k - δ (N / n)‖₊) hk
  exact_mod_cast this

theorem blockOsc_le {N n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k ∈ Icc (N / (n + 1)) (N / n), ‖δ k - δ (N / n)‖ ≤ c) : blockOsc δ N n ≤ c := by
  unfold blockOsc
  have hs : (Icc (N / (n + 1)) (N / n)).sup (fun k => ‖δ k - δ (N / n)‖₊) ≤ c.toNNReal :=
    Finset.sup_le fun k hk => by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc, coe_nnnorm]
      exact h k hk
  have := NNReal.coe_le_coe.mpr hs
  rwa [Real.coe_toNNReal _ hc] at this

/-- The oscillation is bounded by the von Mangoldt mass of the block. -/
theorem blockOsc_le_sum (hC : 0 ≤ C) (hinc : HasVonMangoldtIncrements δ C) (N n : ℕ) :
    blockOsc δ N n ≤ C * ∑ m ∈ Ioc (N / (n + 1)) (N / n), vonMangoldt m / (m : ℝ) := by
  refine blockOsc_le (mul_nonneg hC (sum_nonneg fun m _ => vonMangoldt_div_nonneg m))
    fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [norm_sub_rev]
  refine (norm_sub_le_sum_Ioc hinc hk.2).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left hk.1)
    fun m _ _ => vonMangoldt_div_nonneg m

/-- Far out the oscillation is small. -/
theorem blockOsc_le_two_mul {N n M₀ : ℕ} {η : ℝ} (hη : 0 ≤ η) (hM : ∀ k, M₀ ≤ k → ‖δ k‖ ≤ η)
    (hN : M₀ ≤ N / (n + 1)) : blockOsc δ N n ≤ 2 * η := by
  refine blockOsc_le (by linarith) fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have h1 := hM k (hN.trans hk.1)
  have h2 := hM (N / n) (hN.trans (hk.1.trans hk.2))
  linarith [norm_sub_le (δ k) (δ (N / n))]

/-- On the block, `1/n < 2m/N`: `(1/n) Σ Λ(m)/m ≤ (2/N) Σ Λ(m)`. -/
theorem sum_block_div_le {N n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) :
    (∑ m ∈ Ioc (N / (n + 1)) (N / n), vonMangoldt m / (m : ℝ)) / n ≤
      2 / N * ∑ m ∈ Ioc (N / (n + 1)) (N / n), vonMangoldt m := by
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mem_Ioc] at hm
  have ha : N / (n + 1) + 1 ≤ m := hm.1
  have hlt : N < m * (n + 1) :=
    calc N < (n + 1) * (N / (n + 1) + 1) := Nat.lt_mul_div_succ N (Nat.succ_pos n)
      _ ≤ (n + 1) * m := Nat.mul_le_mul_left _ ha
      _ = m * (n + 1) := mul_comm _ _
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) ha
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ 2 * m * n := by
    have : N ≤ 2 * m * n := by nlinarith
    exact_mod_cast this
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := m)
  rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hN0]
  nlinarith

/-- Telescoping over consecutive differences. -/
theorem sum_Ioc_sub_succ (T : ℕ → ℝ) {K L : ℕ} (hKL : K ≤ L) :
    ∑ n ∈ Ioc K L, (T n - T (n + 1)) = T (K + 1) - T (L + 1) := by
  induction L, hKL using Nat.le_induction with
  | base => simp
  | succ L hKL ih => rw [Finset.sum_Ioc_succ_top hKL, ih]; ring

theorem Icc_one_eq_Ioc_zero (M : ℕ) : Icc 1 M = Ioc 0 M := by
  ext; simp; omega

/-- **Block oscillation is summable against `1/n`**: `Σ_{n ≤ N} osc_n/n → 0`. -/
theorem tendsto_sum_blockOsc_div (hC : 0 ≤ C) (hinc : HasVonMangoldtIncrements δ C)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, blockOsc δ N n / n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set A : ℝ := 2 * C * (Real.log 4 + 4) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * A / ε)
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hKε : A / (K + 1) < ε / 2 := by
    rw [div_lt_iff₀ hK1]
    have h1 : 2 * A < ε * K := by rw [div_lt_iff₀ hε] at hK; linarith
    nlinarith
  set η : ℝ := ε / (4 * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp hδ η hη0
  have hM : ∀ k, M₀ ≤ k → ‖δ k‖ ≤ η := fun k hk => by
    have := hM₀ k hk
    rw [dist_zero_right] at this
    exact this.le
  refine ⟨(M₀ + 1) * (K + 1), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hN
  have hKN : K ≤ N := le_trans (by nlinarith) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hfar : M₀ + 1 ≤ N / (K + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos K)).mpr hN
  have hnn : 0 ≤ ∑ n ∈ Icc 1 N, blockOsc δ N n / n :=
    sum_nonneg fun n _ => div_nonneg (blockOsc_nonneg N n) (Nat.cast_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn, Icc_one_eq_Ioc_zero,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le K) hKN]
  -- the head: `n ≤ K`
  have hhead : ∑ n ∈ Ioc 0 K, blockOsc δ N n / n ≤ K * (2 * η) := by
    have hb : ∀ n ∈ Ioc 0 K, blockOsc δ N n / n ≤ 2 * η := fun n hn => by
      rw [Finset.mem_Ioc] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hfar' : M₀ ≤ N / (n + 1) :=
        (Nat.le_succ M₀).trans (hfar.trans (Nat.div_le_div_left (by omega) (by omega)))
      exact (div_le_self (blockOsc_nonneg N n) hn1).trans (blockOsc_le_two_mul hη0.le hM hfar')
    have := Finset.sum_le_sum hb
    rwa [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at this
  have hhead' : (K : ℝ) * (2 * η) < ε / 2 := by
    rw [hη]
    have : (K : ℝ) * (2 * (ε / (4 * (K + 1)))) = ε / 2 * (K / (K + 1)) := by field_simp; ring
    rw [this]
    have : (K : ℝ) / (K + 1) < 1 := by rw [div_lt_one hK1]; linarith
    nlinarith
  -- the tail: `n > K`
  set T : ℕ → ℝ := fun n => ∑ m ∈ Ioc 0 (N / n), vonMangoldt m with hT
  have hblock : ∀ n, 1 ≤ n → ∑ m ∈ Ioc (N / (n + 1)) (N / n), vonMangoldt m = T n - T (n + 1) :=
    fun n hn => by
      have := Finset.sum_Ioc_consecutive (fun m => vonMangoldt m) (Nat.zero_le (N / (n + 1)))
        (Nat.div_le_div_left (Nat.le_succ n) hn)
      simp only [hT]
      linarith
  have htail : ∑ n ∈ Ioc K N, blockOsc δ N n / n ≤ A / (K + 1) := by
    have hb : ∀ n ∈ Ioc K N, blockOsc δ N n / n ≤ 2 * C / N * (T n - T (n + 1)) := fun n hn => by
      rw [Finset.mem_Ioc] at hn
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have h1 := div_le_div_of_nonneg_right (blockOsc_le_sum hC hinc N n) hn0.le
      rw [mul_div_assoc] at h1
      have h2 := mul_le_mul_of_nonneg_left (sum_block_div_le hn1 hN1) hC
      rw [hblock n hn1] at h2
      calc blockOsc δ N n / n ≤ C * ((∑ m ∈ Ioc (N / (n + 1)) (N / n),
            vonMangoldt m / (m : ℝ)) / n) := h1
        _ ≤ C * (2 / N * (T n - T (n + 1))) := h2
        _ = 2 * C / N * (T n - T (n + 1)) := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum, sum_Ioc_sub_succ T hKN]
    have hTN : 0 ≤ T (N + 1) := sum_nonneg fun m _ => ArithmeticFunction.vonMangoldt_nonneg
    have hTK : T (K + 1) ≤ (Real.log 4 + 4) * (N / (K + 1) : ℝ) := by
      have hpsi : T (K + 1) = Chebyshev.psi ((N / (K + 1) : ℕ) : ℝ) := by
        simp only [hT, Chebyshev.psi, Nat.floor_natCast]
      rw [hpsi]
      refine (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := Nat.cast_div_le (m := N) (n := K + 1) (α := ℝ)
      push_cast at this
      exact this
    have h2C : 0 ≤ 2 * C / N := by positivity
    calc 2 * C / N * (T (K + 1) - T (N + 1)) ≤ 2 * C / N * T (K + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) h2C
      _ ≤ 2 * C / N * ((Real.log 4 + 4) * (N / (K + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hTK h2C
      _ = A / (K + 1) := by rw [hA]; field_simp
  linarith

/-! ### Dominated hyperbola sums -/

theorem exists_norm_le_of_tendsto (hδ : Tendsto δ atTop (𝓝 0)) : ∃ B, ∀ k, ‖δ k‖ ≤ B := by
  obtain ⟨B, hB⟩ := hδ.norm.bddAbove_range
  exact ⟨B, fun k => hB ⟨k, rfl⟩⟩

/-- `Σ_{1 ≤ n ≤ N} ‖δ(⌊N/(n + s)⌋)‖ w(n) → 0` for summable `w ≥ 0` (Tannery). -/
theorem tendsto_sum_norm_hyperbola_mul {w : ℕ → ℝ} (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n)
    (s : ℕ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ‖δ (N / (n + s))‖ * w n) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := exists_norm_le_of_tendsto hδ
  set F : ℕ → ℕ → ℝ := fun N n => if n ∈ Icc 1 N then ‖δ (N / (n + s))‖ * w n else 0 with hF
  have hsum : ∀ N, ∑ n ∈ Icc 1 N, ‖δ (N / (n + s))‖ * w n = ∑' n, F N n := fun N => by
    rw [tsum_eq_sum (s := Icc 1 N) fun n hn => by simp only [hF, if_neg hn]]
    exact Finset.sum_congr rfl fun n hn => by simp only [hF, if_pos hn]
  simp only [hsum]
  have hab : ∀ n, Tendsto (fun N => F N n) atTop (𝓝 0) := fun n => by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact tendsto_const_nhds.congr fun N => by simp [hF]
    · have hdiv : Tendsto (fun N : ℕ => N / (n + s)) atTop atTop :=
        Nat.tendsto_div_const_atTop (by omega)
      have hlim := ((hδ.comp hdiv).norm.mul_const (w n))
      rw [norm_zero, zero_mul] at hlim
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop n] with N hN
      simp only [hF, Function.comp_apply, if_pos (Finset.mem_Icc.mpr ⟨hn, hN⟩)]
  have hbd : ∀ N n, ‖F N n‖ ≤ B * w n := fun N n => by
    simp only [hF]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw0 n))]
      exact mul_le_mul_of_nonneg_right (hB _) (hw0 n)
    · rw [norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hB 0)) (hw0 n)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := F) (g := fun _ => (0 : ℝ))
    (bound := fun n => B * w n) (hw.mul_left B) hab (Eventually.of_forall hbd)
  simpa using h

/-- The weight `1/(n(n+1))` is summable. -/
theorem summable_inv_mul_succ : Summable fun n : ℕ => 1 / ((n : ℝ) * (n + 1)) := by
  refine (Real.summable_one_div_nat_pow.mpr one_lt_two).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith

/-! ### Summation by parts -/

theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    ∑ i ∈ range N, g (i + 1) = ∑ n ∈ Icc 1 N, g n := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem norm_sum_range_mul_le (f g : ℕ → ℂ) (M : ℕ) {B : ℝ}
    (hB : ∀ k ≤ M, ‖∑ i ∈ range (k + 1), g i‖ ≤ B) :
    ‖∑ i ∈ range (M + 1), f i * g i‖ ≤ B * (‖f M‖ + ∑ i ∈ range M, ‖f (i + 1) - f i‖) := by
  have h := Finset.sum_range_by_parts f g (M + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB M le_rfl) (norm_nonneg _)
  · rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB i (by simp at hi; omega)) (norm_nonneg _)

theorem sum_range_shift_periodic {v : ℕ → ℂ} {q : ℕ} (hper : ∀ n, v (n + q) = v n) (a : ℕ) :
    ∑ j ∈ range q, v (a + j) = ∑ j ∈ range q, v j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := Finset.sum_range_succ' (fun j => v (a + j)) q
    have h2 := Finset.sum_range_succ (fun j => v (a + j)) q
    simp only [add_zero] at h1
    rw [hper a] at h2
    have e : ∀ j, v (a + (j + 1)) = v (a + 1 + j) := fun j => by rw [add_assoc, add_comm 1 j]
    simp_rw [e] at h1
    rw [← ih]
    linear_combination h2 - h1

/-- The partial sums of a periodic sequence of mean zero are bounded by `Σ_{r < q} ‖v(r)‖`. -/
theorem norm_sum_range_periodic_le {v : ℕ → ℂ} {q : ℕ} (hq : 0 < q) (hper : ∀ n, v (n + q) = v n)
    (hmean : ∑ r ∈ range q, v r = 0) (n : ℕ) :
    ‖∑ j ∈ range n, v j‖ ≤ ∑ r ∈ range q, ‖v r‖ := by
  have hmul : ∀ m r : ℕ, ∑ j ∈ range (q * m + r), v j = ∑ j ∈ range r, v j := fun m r => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show q * (m + 1) + r = (q * m + r) + q by ring, Finset.sum_range_add, ih,
        sum_range_shift_periodic hper, hmean, add_zero]
  rw [← Nat.div_add_mod n q, hmul]
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.mod_lt _ hq).le)
    fun _ _ _ => norm_nonneg _

/-! ### Mean-zero periodic weights -/

/-- **Mean-zero periodic weights**: `Σ_{n ≤ N} v(n) δ(⌊N/n⌋)/n → 0`. -/
theorem tendsto_sum_periodic_mul_hyperbola {v : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hper : ∀ n, v (n + q) = v n) (hmean : ∑ r ∈ range q, v r = 0)
    (hC : 0 ≤ C) (hinc : HasVonMangoldtIncrements δ C) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, v n / n * δ (N / n)) atTop (𝓝 0) := by
  set Bv : ℝ := ∑ r ∈ range q, ‖v r‖
  have hBv : 0 ≤ Bv := sum_nonneg fun _ _ => norm_nonneg _
  -- partial sums of the shifted weight
  have hpart : ∀ k, ‖∑ i ∈ range (k + 1), v (i + 1)‖ ≤ 2 * Bv := fun k => by
    have e : ∑ i ∈ range (k + 1), v (i + 1) = ∑ j ∈ range (k + 2), v j - v 0 := by
      rw [Finset.sum_range_succ' (fun j => v j) (k + 1)]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_sum_range_periodic_le hq hper hmean (k + 2)
    have h2 : ‖v 0‖ ≤ Bv :=
      Finset.single_le_sum (f := fun r => ‖v r‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hq)
    linarith
  -- the bound
  have hosc := tendsto_sum_blockOsc_div hC hinc hδ
  have hdom := tendsto_sum_norm_hyperbola_mul summable_inv_mul_succ
    (fun n => by positivity) 1 hδ
  obtain ⟨B, hB⟩ := exists_norm_le_of_tendsto hδ
  have hlast : Tendsto (fun N : ℕ => B / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat B
  have hmaj := ((hlast.add (hosc.add hdom)).const_mul (2 * Bv))
  simp only [add_zero, mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hN0 : (0 : ℝ) < (M + 1 : ℕ) := by exact_mod_cast Nat.succ_pos M
  set f : ℕ → ℂ := fun i => δ ((M + 1) / (i + 1)) / ((i + 1 : ℕ) : ℂ) with hf
  have hre : ∑ n ∈ Icc 1 (M + 1), v n / n * δ ((M + 1) / n) =
      ∑ i ∈ range (M + 1), f i * v (i + 1) := by
    rw [← sum_range_succ_eq_sum_Icc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf]
    ring
  rw [hre]
  refine (norm_sum_range_mul_le f (fun i => v (i + 1)) M fun k _ => hpart k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine add_le_add ?_ ?_
  · -- the last term `δ(1)/N`
    rw [hf]
    simp only
    rw [Nat.div_self (Nat.succ_pos M), norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hB 1) hN0.le
  · -- consecutive differences
    have hdiff : ∀ i ∈ range M, ‖f (i + 1) - f i‖ ≤
        blockOsc δ (M + 1) (i + 1) / ((i + 1 : ℕ) : ℝ) +
          ‖δ ((M + 1) / (i + 1 + 1))‖ * (1 / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1))) :=
      fun i _ => by
        have hA : ((i + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
        have hB2 : ((i + 1 + 1 : ℕ) : ℂ) = ((i + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
        have hA' : ((i + 1 : ℕ) : ℂ) + 1 ≠ 0 := by
          rw [← hB2]; exact_mod_cast Nat.succ_ne_zero (i + 1)
        have hn0 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
        have e : f (i + 1) - f i =
            (δ ((M + 1) / (i + 1 + 1)) - δ ((M + 1) / (i + 1))) / ((i + 1 : ℕ) : ℂ) -
              δ ((M + 1) / (i + 1 + 1)) * (1 / (((i + 1 : ℕ) : ℂ) * (((i + 1 : ℕ) : ℂ) + 1))) := by
          simp only [hf]
          rw [hB2]
          field_simp
          ring
        rw [e]
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_div, Complex.norm_natCast]
          refine div_le_div_of_nonneg_right (norm_sub_le_blockOsc ?_) hn0.le
          rw [Finset.mem_Icc]
          exact ⟨le_rfl, Nat.div_le_div_left (Nat.le_succ (i + 1)) (Nat.succ_pos i)⟩
        · rw [norm_mul]
          refine le_of_eq ?_
          congr 1
          rw [norm_div, norm_one, norm_mul, Complex.norm_natCast, ← hB2, Complex.norm_natCast]
          push_cast
          ring
    refine (Finset.sum_le_sum hdiff).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← sum_range_succ_eq_sum_Icc (fun n => blockOsc δ (M + 1) n / (n : ℝ))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M))
        fun i _ _ => div_nonneg (blockOsc_nonneg _ _) (Nat.cast_nonneg _)
    · rw [← sum_range_succ_eq_sum_Icc (fun n => ‖δ ((M + 1) / (n + 1))‖ *
        (1 / ((n : ℝ) * ((n : ℝ) + 1))))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M))
        fun i _ _ => mul_nonneg (norm_nonneg _) (by positivity)

/-! ### Constant weight: the hyperbola sum against its integral -/

theorem measurable_hyperbolaIntegrand (δ : ℕ → ℂ) (x : ℝ) :
    Measurable fun y : ℝ => δ ⌊Real.exp (x - y)⌋₊ :=
  measurable_from_nat.comp
    (Nat.measurable_floor.comp (Real.measurable_exp.comp (measurable_const.sub measurable_id)))

/-- One block of the integral: on `[log n, log(n+1)]` the integrand stays in the block `n`. -/
theorem norm_integral_block_sub_le {N n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hint : IntervalIntegrable (fun y : ℝ => δ ⌊Real.exp (Real.log N - y)⌋₊) volume
      (Real.log n) (Real.log ((n + 1 : ℕ) : ℝ))) :
    ‖(∫ y in Real.log n..Real.log ((n + 1 : ℕ) : ℝ), δ ⌊Real.exp (Real.log N - y)⌋₊) -
        δ (N / n) / (n : ℂ)‖ ≤
      blockOsc δ N n / n + ‖δ (N / n)‖ * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  set a := Real.log n
  set b := Real.log ((n + 1 : ℕ) : ℝ)
  have hab : a ≤ b := Real.log_le_log hn0 (by rw [hn1]; linarith)
  -- `1/(n+1) ≤ b − a ≤ 1/n`
  have hq : (0 : ℝ) < (n + 1) / n := by positivity
  have hba : b - a = Real.log ((n + 1) / n) := by
    show Real.log ((n + 1 : ℕ) : ℝ) - Real.log n = _
    rw [Real.log_div (by positivity) hn0.ne', hn1]
  have hup : b - a ≤ 1 / n := by
    rw [hba]
    have := Real.log_le_sub_one_of_pos hq
    have e : (n + 1 : ℝ) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have hlo : 1 / (n + 1) ≤ b - a := by
    rw [hba]
    have := Real.one_sub_inv_le_log_of_pos hq
    have e : 1 - ((n + 1 : ℝ) / n)⁻¹ = 1 / (n + 1) := by field_simp; ring
    linarith
  set c := δ (N / n)
  have hI : ‖(∫ y in a..b, δ ⌊Real.exp (Real.log N - y)⌋₊) - (b - a) • c‖ ≤
      blockOsc δ N n * (b - a) := by
    rw [← intervalIntegral.integral_const, ← intervalIntegral.integral_sub hint intervalIntegrable_const]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_).trans
      (le_of_eq (by rw [abs_of_nonneg (by linarith)]))
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at hy
    have hey1 : (n : ℝ) < Real.exp y := by
      have := Real.exp_lt_exp.mpr hy.1; rwa [Real.exp_log hn0] at this
    have hey2 : Real.exp y ≤ n + 1 := by
      have := Real.exp_le_exp.mpr hy.2; rwa [Real.exp_log (by positivity), hn1] at this
    have hey0 : 0 < Real.exp y := Real.exp_pos y
    have hx : Real.exp (Real.log N - y) = N / Real.exp y := by
      rw [Real.exp_sub, Real.exp_log hN0]
    refine norm_sub_le_blockOsc ?_
    rw [Finset.mem_Icc, hx]
    constructor
    · refine Nat.le_floor ?_
      refine (Nat.cast_div_le (m := N) (n := n + 1)).trans ?_
      push_cast
      exact div_le_div_of_nonneg_left hN0.le hey0 hey2
    · rw [← Nat.floor_div_eq_div (K := ℝ) N n]
      exact Nat.floor_le_floor (div_le_div_of_nonneg_left hN0.le hn0 hey1.le)
  have hsm : ‖(b - a) • c - c / (n : ℂ)‖ ≤ ‖c‖ * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    have e : (b - a) • c - c / (n : ℂ) = (((b - a) - 1 / n : ℝ) : ℂ) * c := by
      rw [Complex.real_smul]; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have e2 : 1 / (n : ℝ) - 1 / (n + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by field_simp; ring
    linarith
  calc ‖(∫ y in a..b, δ ⌊Real.exp (Real.log N - y)⌋₊) - c / (n : ℂ)‖
      = ‖((∫ y in a..b, δ ⌊Real.exp (Real.log N - y)⌋₊) - (b - a) • c) +
          ((b - a) • c - c / (n : ℂ))‖ := by congr 1; abel
    _ ≤ blockOsc δ N n * (b - a) + ‖c‖ * (1 / ((n : ℝ) * ((n : ℝ) + 1))) :=
        (norm_add_le _ _).trans (add_le_add hI hsm)
    _ ≤ blockOsc δ N n / n + ‖c‖ * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        have := mul_le_mul_of_nonneg_left hup (blockOsc_nonneg (δ := δ) N n)
        rw [mul_one_div] at this
        linarith

/-- **Constant weight**: `Σ_{n ≤ N} δ(⌊N/n⌋)/n − ∫_0^{log N} δ(⌊e^u⌋) du → 0`. -/
theorem tendsto_sum_hyperbola_sub_integral (hC : 0 ≤ C) (hinc : HasVonMangoldtIncrements δ C)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, δ (N / n) / n -
      ∫ u in (0 : ℝ)..Real.log N, δ ⌊Real.exp u⌋₊) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := exists_norm_le_of_tendsto hδ
  have hosc := tendsto_sum_blockOsc_div hC hinc hδ
  have hdom := tendsto_sum_norm_hyperbola_mul summable_inv_mul_succ
    (fun n => by positivity) 0 hδ
  simp only [add_zero] at hdom
  have hlast : Tendsto (fun N : ℕ => B / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat B
  have hmaj := hosc.add (hdom.add hlast)
  simp only [add_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set L : ℝ := Real.log ((M + 1 : ℕ) : ℝ) with hL
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => δ ⌊Real.exp (L - y)⌋₊) volume a b :=
    fun a b => (intervalIntegrable_const (c := B)).mono_fun'
      (measurable_hyperbolaIntegrand δ L).aestronglyMeasurable (ae_of_all _ fun y => hB _)
  have hint_eq : ∫ u in (0 : ℝ)..L, δ ⌊Real.exp u⌋₊ = ∫ y in (0 : ℝ)..L, δ ⌊Real.exp (L - y)⌋₊ := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => δ ⌊Real.exp u⌋₊) L]
    simp
  have hsplit : ∫ y in (0 : ℝ)..L, δ ⌊Real.exp (L - y)⌋₊ =
      ∑ i ∈ range M, ∫ y in Real.log ((i + 1 : ℕ) : ℝ)..Real.log ((i + 1 + 1 : ℕ) : ℝ),
        δ ⌊Real.exp (L - y)⌋₊ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i => Real.log ((i + 1 : ℕ) : ℝ)) fun k _ => hint _ _]
    simp [hL]
  rw [hint_eq, hsplit, ← sum_range_succ_eq_sum_Icc (fun n => δ ((M + 1) / n) / (n : ℂ)),
    Finset.sum_range_succ, Nat.div_self (Nat.succ_pos M)]
  have hdiff : ∑ i ∈ range M, δ ((M + 1) / (i + 1)) / ((i + 1 : ℕ) : ℂ) +
      δ 1 / ((M + 1 : ℕ) : ℂ) - ∑ i ∈ range M, ∫ y in Real.log ((i + 1 : ℕ) : ℝ)..Real.log
        ((i + 1 + 1 : ℕ) : ℝ), δ ⌊Real.exp (L - y)⌋₊ =
      -∑ i ∈ range M, ((∫ y in Real.log ((i + 1 : ℕ) : ℝ)..Real.log ((i + 1 + 1 : ℕ) : ℝ),
        δ ⌊Real.exp (L - y)⌋₊) - δ ((M + 1) / (i + 1)) / ((i + 1 : ℕ) : ℂ)) +
        δ 1 / ((M + 1 : ℕ) : ℂ) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have hN0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos M
  have hpieces : ‖∑ i ∈ range M, ((∫ y in Real.log ((i + 1 : ℕ) : ℝ)..Real.log
        ((i + 1 + 1 : ℕ) : ℝ), δ ⌊Real.exp (L - y)⌋₊) - δ ((M + 1) / (i + 1)) / ((i + 1 : ℕ) : ℂ))‖ ≤
      ∑ n ∈ Icc 1 (M + 1), blockOsc δ (M + 1) n / n +
        ∑ n ∈ Icc 1 (M + 1), ‖δ ((M + 1) / n)‖ * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i ∈ range M, ‖(∫ y in Real.log ((i + 1 : ℕ) : ℝ)..Real.log ((i + 1 + 1 : ℕ) : ℝ),
        δ ⌊Real.exp (L - y)⌋₊) - δ ((M + 1) / (i + 1)) / ((i + 1 : ℕ) : ℂ)‖ ≤
        blockOsc δ (M + 1) (i + 1) / ((i + 1 : ℕ) : ℝ) + ‖δ ((M + 1) / (i + 1))‖ *
          (1 / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1))) := fun i _ =>
      norm_integral_block_sub_le (Nat.succ_pos i) (Nat.succ_pos M) (hint _ _)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← sum_range_succ_eq_sum_Icc (fun n => blockOsc δ (M + 1) n / (n : ℝ))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M))
        fun i _ _ => div_nonneg (blockOsc_nonneg _ _) (Nat.cast_nonneg _)
    · rw [← sum_range_succ_eq_sum_Icc (fun n => ‖δ ((M + 1) / n)‖ *
        (1 / ((n : ℝ) * ((n : ℝ) + 1))))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ M))
        fun i _ _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hlastb : ‖δ 1 / ((M + 1 : ℕ) : ℂ)‖ ≤ B / ((M + 1 : ℕ) : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hB 1) hN0.le
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
