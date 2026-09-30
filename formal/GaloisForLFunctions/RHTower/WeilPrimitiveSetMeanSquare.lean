import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Weil positivity bounds the weights in mean square on primitive sets

A finite set `S ⊆ [2, N]` is *primitive* if no element is a proper multiple of another.

**Theorem** (`exists_sum_sq_div_le_of_primitive`). There is an absolute constant `C₀` such that
every Weil-positive weight system `lam` (with the archimedean term of `ζ`) satisfies

`Σ_{n ∈ S} lam(n)²/n ≤ (log N + C₀)²`

for every `N ≥ 1` and every primitive `S ⊆ [2, N]`.

**Corollaries.**
- `sum_sq_Ioc_le` (dyadic mean square): `Σ_{N < n ≤ 2N} lam(n)² ≤ 2N (log 2N + C₀)²`.
- `summable_abs_div_rpow_of_weilPositive`: `Σ_n |lam(n)| n^{−σ} < ∞` for every `σ > 1`.

So every Weil-positive system is `Λ`-size in dyadic mean square up to a logarithm, and its
Dirichlet series converges absolutely on `Re s > 1`. The only size bound known before was the
pointwise box `|lam(n)| ≤ √n (log n + C)`.

**Proof.** Take the star resonator `c = δ₁ + t Σ_{n ∈ S} lam(n) n^{−1/2} δ_n`. Its multiplicative
autocorrelation meets an atom `n ≥ 2` only through the pair `(n, 1)`: a product `n m` with
`m ∈ S` is never in `S`, by primitivity. The multiplicative Toeplitz bound of Weil positivity
therefore reads `2t Q ≤ (log N + C₀)(1 + t² Q)` with `Q = Σ_S lam(n)²/n`, and `t = (log N + C₀)/Q`
gives `Q ≤ (log N + C₀)²`. The interval `(N, 2N]` is primitive. Absolute convergence follows by
AM–GM on dyadic blocks.
-/

noncomputable section

open Complex Finset Filter Topology
open scoped Real ComplexConjugate

namespace RHTower.WeilMeanSquare

/-- No element of `S` is a proper multiple of another element of `S`. -/
def IsPrimitiveSet (S : Finset ℕ) : Prop := ∀ m ∈ S, ∀ m' ∈ S, ∀ k, 2 ≤ k → m ≠ k * m'

/-- **The primitive-set mean-square law.** -/
theorem exists_sum_sq_div_le_of_primitive {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → 0 ≤ Real.log N + C₀ ∧
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S →
        ∑ n ∈ S, lam n ^ 2 / n ≤ (Real.log N + C₀) ^ 2 := by
  obtain ⟨C₀, hC⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun N hN => ?_⟩
  -- the resonator `c = δ₁ + t Σ_S lam(n) n^{-1/2} δ_n`
  have key : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S → ∀ t : ℝ,
      2 * t * ∑ n ∈ S, lam n ^ 2 / n ≤
        (Real.log N + C₀) * (1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n) := by
    intro S hS hprim t
    set c : ℕ → ℂ := fun m => if m = 1 then 1 else if m ∈ S then
      ((t * lam m / Real.sqrt m : ℝ) : ℂ) else 0 with hc
    have hcN : ∀ m, N < m → c m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h => by have := (Finset.mem_Icc.mp (hS h)).2; omega
      simp [hc, h1, h2]
    have h := hC N hN c hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
          if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n * m) * conj (c m) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S
      · simp [hc, hn1, hnS]
      · simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 = 1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), Finset.mul_sum]
      · congr 1
        · simp [hc]
        · refine Finset.sum_congr rfl fun n hn => ?_
          have hn2 := (Finset.mem_Icc.mp (hS hn)).1
          have hn1 : n ≠ 1 := by omega
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          simp only [hc, hn1, hn, if_false, if_true, Complex.norm_real, Real.norm_eq_abs, sq_abs,
            div_pow, mul_pow, Real.sq_sqrt hn0.le]
          ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re = t * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at h
    linarith
  -- the constant is nonnegative: take `S = ∅`
  have hB : 0 ≤ Real.log N + C₀ := by
    have := key ∅ (Finset.empty_subset _) (fun m hm => absurd hm (Finset.notMem_empty m)) 0
    simpa using this
  refine ⟨hB, fun S hS hprim => ?_⟩
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
  set B := Real.log N + C₀ with hBdef
  rcases hQ0.lt_or_eq with hQpos | hQzero
  · have h := key S hS hprim (B / Q)
    rw [← hQ] at h
    have e : 2 * (B / Q) * Q = 2 * B := by field_simp
    have e2 : B * (1 + (B / Q) ^ 2 * Q) = B + B ^ 3 / Q := by field_simp
    rw [e, e2] at h
    have h3 : B ≤ B ^ 3 / Q := by linarith
    rcases hB.lt_or_eq with hBpos | hBzero
    · rw [le_div_iff₀ hQpos] at h3
      nlinarith
    · have h1 := key S hS hprim 1
      rw [← hQ, ← hBzero] at h1
      nlinarith
  · rw [← hQzero]; positivity

/-- **Dyadic mean square.** `Σ_{N < n ≤ 2N} lam(n)² ≤ 2N (log 2N + C₀)²`. -/
theorem exists_sum_sq_Ioc_le {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N → 0 ≤ Real.log (2 * N : ℕ) + C₀ ∧
      ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + C₀) ^ 2 := by
  obtain ⟨C₀, hC⟩ := exists_sum_sq_div_le_of_primitive hW
  refine ⟨C₀, fun N hN => ?_⟩
  obtain ⟨hB, h⟩ := hC (2 * N) (by omega)
  refine ⟨hB, ?_⟩
  have hsub : Finset.Ioc N (2 * N) ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hprim : IsPrimitiveSet (Finset.Ioc N (2 * N)) := by
    intro m hm m' hm' k hk heq
    rw [Finset.mem_Ioc] at hm hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := h _ hsub hprim
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  calc ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        rw [Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn.2)
    _ ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + C₀) ^ 2 := mul_le_mul_of_nonneg_left hQ h2N.le

/-! ## Absolute convergence on `Re s > 1` -/

/-- **Dyadic `ℓ¹` bound.** `Σ_{N < n ≤ 2N} |lam(n)| ≤ (3/2) N (L + 1)` whenever
`Σ_{N < n ≤ 2N} lam(n)² ≤ 2N L²` and `L ≥ 0`, by `2|x| ≤ x²/(L+1) + (L+1)`. -/
theorem sum_abs_Ioc_le_of_sum_sq {lam : ℕ → ℝ} {N : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤ (2 * N : ℕ) * L ^ 2) :
    ∑ n ∈ Finset.Ioc N (2 * N), |lam n| ≤ 3 / 2 * N * (L + 1) := by
  have hL1 : 0 < L + 1 := by linarith
  have hpt : ∀ n, 2 * |lam n| ≤ lam n ^ 2 / (L + 1) + (L + 1) := by
    intro n
    have h0 : 0 ≤ (|lam n| - (L + 1)) ^ 2 := sq_nonneg _
    rw [div_add' _ _ _ hL1.ne', le_div_iff₀ hL1]
    nlinarith [sq_abs (lam n)]
  have hcard : ((Finset.Ioc N (2 * N)).card : ℝ) = N := by
    rw [Nat.card_Ioc, show 2 * N - N = N by omega]
  have hsum := Finset.sum_le_sum fun n (_ : n ∈ Finset.Ioc N (2 * N)) => hpt n
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
    nsmul_eq_mul, hcard] at hsum
  have h2 : (∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2) / (L + 1) ≤ 2 * N * (L + 1) := by
    rw [div_le_iff₀ hL1]
    push_cast at h
    nlinarith [sq_nonneg L, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

theorem sum_range_succ_eq_Ioc (f : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1), f n = f 0 + f 1 + ∑ n ∈ Finset.Ioc 1 m, f n := by
  induction m, hm using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]
  | succ k hk ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top hk]
    ring

/-- **Weil-positive weights converge absolutely on `Re s > 1`.** -/
theorem summable_abs_div_rpow_of_weilPositive {lam : ℕ → ℝ} (hW : WeilPositive lam) {σ : ℝ}
    (hσ : 1 < σ) : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  obtain ⟨C₀, hC⟩ := exists_sum_sq_Ioc_le hW
  set r : ℝ := (2 : ℝ) ^ (1 - σ) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set b : ℕ → ℝ := fun j => 3 / 2 * r ^ j * ((j + 1) * Real.log 2 + |C₀| + 1) with hb
  have hbs : Summable b := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left
      (3 / 2 * Real.log 2)
    have h2 := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (3 / 2 * (Real.log 2 + |C₀| + 1))
    refine (h1.add h2).congr fun j => ?_
    simp only [hb, pow_one]; ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    simp only [hb]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  set f : ℕ → ℝ := fun n => |lam n| / (n : ℝ) ^ σ with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  -- the block bound
  have hblock : ∀ j : ℕ, ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n ≤ b j := by
    intro j
    set N : ℕ := 2 ^ j with hN
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2N : 2 ^ (j + 1) = 2 * N := by rw [pow_succ, mul_comm]
    rw [h2N]
    obtain ⟨hL, hsq⟩ := hC N hN1
    have habs := sum_abs_Ioc_le_of_sum_sq hL hsq
    have hNσ : ∀ n ∈ Finset.Ioc N (2 * N), f n ≤ |lam n| / (N : ℝ) ^ σ := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      simp only [hf]
      refine div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos hN0 _)
        (Real.rpow_le_rpow hN0.le (by exact_mod_cast hn.1.le) (by linarith))
    calc ∑ n ∈ Finset.Ioc N (2 * N), f n
        ≤ ∑ n ∈ Finset.Ioc N (2 * N), |lam n| / (N : ℝ) ^ σ := Finset.sum_le_sum hNσ
      _ = (∑ n ∈ Finset.Ioc N (2 * N), |lam n|) / (N : ℝ) ^ σ := by rw [Finset.sum_div]
      _ ≤ 3 / 2 * N * (Real.log (2 * N : ℕ) + C₀ + 1) / (N : ℝ) ^ σ :=
          div_le_div_of_nonneg_right habs (Real.rpow_nonneg hN0.le _)
      _ ≤ b j := by
          have hNr : (N : ℝ) / (N : ℝ) ^ σ = r ^ j := by
            have e1 : (N : ℝ) = (2 : ℝ) ^ (j : ℝ) := by
              rw [hN, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
            have e2 : (N : ℝ) ^ σ = (2 : ℝ) ^ ((j : ℝ) * σ) := by
              rw [e1, ← Real.rpow_mul (by norm_num)]
            have e3 : r ^ j = (2 : ℝ) ^ ((1 - σ) * (j : ℝ)) := by
              rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            rw [e2, e3, e1, ← Real.rpow_sub (by norm_num)]
            congr 1; ring
          have hlog : Real.log (2 * N : ℕ) = (j + 1) * Real.log 2 := by
            rw [← h2N, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; ring
          rw [hlog]
          have e : 3 / 2 * (N : ℝ) * ((j + 1) * Real.log 2 + C₀ + 1) / (N : ℝ) ^ σ =
              3 / 2 * ((N : ℝ) / (N : ℝ) ^ σ) * ((j + 1) * Real.log 2 + C₀ + 1) := by ring
          rw [e, hNr]
          simp only [hb]
          have hrj : 0 ≤ r ^ j := pow_nonneg hr0 j
          have hC : C₀ ≤ |C₀| := le_abs_self C₀
          nlinarith
  -- dyadic decomposition of `(1, 2^J]`
  have hdyad : ∀ J : ℕ, ∑ n ∈ Finset.Ioc 1 (2 ^ J), f n ≤ ∑ j ∈ Finset.range J, b j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive f (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ J)), Finset.sum_range_succ]
      exact add_le_add ih (hblock J)
  refine summable_of_sum_range_le (c := f 0 + f 1 + ∑' j, b j) hf0 fun T => ?_
  have hT : T ≤ 2 ^ T := (Nat.lt_two_pow_self).le
  calc ∑ n ∈ Finset.range T, f n ≤ ∑ n ∈ Finset.range (2 ^ T + 1), f n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun n _ _ => hf0 n)
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc 1 (2 ^ T), f n :=
        sum_range_succ_eq_Ioc f (2 ^ T) Nat.one_le_two_pow
    _ ≤ f 0 + f 1 + ∑' j, b j := by
        have := (hdyad T).trans (hbs.sum_le_tsum _ fun j _ => hb0 j)
        linarith

/-! ## Full-cone corollaries -/

/-- Full-cone Weil-positive weights converge absolutely on `Re s > 1`: this is the summability
field of `HerglotzWeilPositive`, which therefore holds automatically on the Weil cone. -/
theorem summable_abs_div_rpow_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
  summable_abs_div_rpow_of_weilPositive (weilPositive_of_weilPositiveFull hW) hσ

/-- **Prime mean square.** `Σ_{p ≤ N} lam(p)²/p ≤ (log N + C₀)²`; `Λ` has `(½ + o(1)) log² N`. -/
theorem exists_sum_sq_prime_div_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, lam p ^ 2 / p ≤ (Real.log N + C₀) ^ 2 := by
  obtain ⟨C₀, hC⟩ := exists_sum_sq_div_le_of_primitive (weilPositive_of_weilPositiveFull hW)
  refine ⟨C₀, fun N hN => (hC N hN).2 _ (Finset.filter_subset _ _) ?_⟩
  intro m hm m' hm' k hk heq
  rw [Finset.mem_filter] at hm hm'
  have hm'2 := hm'.2.two_le
  exact Nat.not_prime_mul (by omega) (by omega) (heq ▸ hm.2)

/-- **Dyadic mean square on the Weil cone.** -/
theorem exists_sum_sq_Ioc_le_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C₀ : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + C₀) ^ 2 := by
  obtain ⟨C₀, hC⟩ := exists_sum_sq_Ioc_le (weilPositive_of_weilPositiveFull hW)
  exact ⟨C₀, fun N hN => (hC N hN).2⟩

end RHTower.WeilMeanSquare
