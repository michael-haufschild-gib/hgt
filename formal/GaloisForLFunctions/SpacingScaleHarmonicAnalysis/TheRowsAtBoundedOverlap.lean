import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeEntersThroughNonRatioLags
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime

/-!
# The rows at bounded overlap

At every width the prime form of an atomic test splits into the ratio lags, which see the bump
only through `‖g‖²`, and the non-ratio lags, which carry the overlap.

* **The overlap identity** (`primeSum_atomicTest_eq_ratio_add`): for a bump supported in `[0, w]`,
  `primeSum f_x = ‖g‖² P_N(x) + NR_w(x)`, where `P_N` is the atomic Weil prime form and
  `NR_w(x) = Σ_k Λ_k Σ_{m,n} x_m x_n (non-ratio terms)` is the non-ratio lag form. Below the spacing
  `NR_w = 0`; beyond it this is the only new term.
* **The non-ratio rows** (`abs_nonRatioForm_le`): by a Schur test with weights `n^{−1/2}`,
  `|NR_w(x)| ≤ ‖g‖² Σ_m x_m² ρ_w(m)`, `ρ_w(m) = 2(log 4 + 4)e^{3w/2}(e^w − 1)N +
  2e^{w/2} m (e^w − 1)(log m + w)`. Up the tower a window of width `w` around `km` holds at most
  `2km(e^w − 1)` other atoms (`up_row_le`, Chebyshev); down the tower the pairs `kn = ℓ ≠ m` near `m`
  are divisors of `ℓ`, and `Σ_{d∣ℓ} Λ(d) = log ℓ` (`down_row_le`, `sum_sum_vonMangoldt_le`).
* **At overlap ratio `K`** (`nonRatioRow_le_of_ratio`): `ρ_w(m) ≤ 2(log 4 + 4)e^{5/2}K +
  2e^{3/2}K(m/N)(log m + 1)` — the same shape `K (m/N) log N` as the archimedean cross-kernel row
  and as the saving `(m/4N) log m` of the tilted rows.
* **The prime form at ratio `K` as row sums** (`primeSum_atomicTest_le_rows`):
  `primeSum f_x ≤ ‖g‖² Σ_m x_m² (log N + 2(log 4 + 4) − (m/4N) log m + ρ_w(m))`.

So the coefficient-size method sees bounded overlap as a competition of three rows of the same
shape `(m/N) log N`: the tilt saving `1/4`, the archimedean cross kernel `≍ K`, and the non-ratio
lags `≍ 2e^{3/2}K`. It closes only while their constants do; past that, positivity must read the
signs of the non-ratio lags — the gauge.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics ArithmeticEffectivityTheory

variable {g : ℝ → ℝ} {w : ℝ}

/-- The ratio lag count of order `k`: `Σ_{m,n} x_m x_n ([m = kn] + [n = km])`. -/
def ratioLag (N k : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
    ((if m = k * n then 1 else 0) + (if n = k * m then 1 else 0))

/-- The non-ratio lag form of order `k`: the lag form with its ratio terms removed. -/
def nonRatioLag (g : ℝ → ℝ) (N k : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
    ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
      (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))))

/-- The **non-ratio lag form** `NR_w(x) = Σ_k Λ_k · nonRatioLag_k(x)`. -/
def nonRatioForm (g : ℝ → ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, vonMangoldtAtom k * nonRatioLag g N k x

theorem bumpCorr_zero (g : ℝ → ℝ) : bumpCorr g 0 = ∫ u, g u ^ 2 := by
  unfold bumpCorr
  simp [sq]

/-- A lag form is its ratio part, read at `‖g‖²`, plus its non-ratio part. -/
theorem lagForm_eq_ratio_add {N k : ℕ} (hk : 1 ≤ k) (x : ℕ → ℝ) :
    lagForm g N k x = (∫ u, g u ^ 2) * ratioLag N k x + nonRatioLag g N k x := by
  unfold lagForm ratioLag nonRatioLag
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hm1 := (mem_Icc.mp hm).1
  have hn1 := (mem_Icc.mp hn).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e1 : m = k * n → -Real.log k - (Real.log n - Real.log m) = 0 := fun h => by
    rw [h]; push_cast; rw [Real.log_mul hk0.ne' hn0.ne']; ring
  have e2 : n = k * m → Real.log k - (Real.log n - Real.log m) = 0 := fun h => by
    rw [h]; push_cast; rw [Real.log_mul hk0.ne' hm0.ne']; ring
  by_cases h1 : m = k * n <;> by_cases h2 : n = k * m
  · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, e1 h1, e2 h2, bumpCorr_zero]; ring
  · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, e1 h1, bumpCorr_zero]; ring
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, e2 h2, bumpCorr_zero]; ring
  · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring

/-- Ratio lags of order `k > N` do not occur. -/
theorem ratioLag_eq_zero {N k : ℕ} (hk : N < k) (x : ℕ → ℝ) : ratioLag N k x = 0 := by
  unfold ratioLag
  refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
  have hm1 := (mem_Icc.mp hm)
  have hn1 := (mem_Icc.mp hn)
  have h1 : m ≠ k * n := fun h => by nlinarith
  have h2 : n ≠ k * m := fun h => by nlinarith
  rw [if_neg h1, if_neg h2]; ring

/-- `Σ_k Λ_k [n = km] = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n`, `m ≠ n`. -/
theorem sum_vonMangoldtAtom_ratio {N m n : ℕ} (hm : 1 ≤ m) (hn : n ≤ N) :
    ∑ k ∈ range (N + 1), vonMangoldtAtom k * (if n = k * m then 1 else 0) =
      if m ∣ n ∧ m ≠ n then ArithmeticFunction.vonMangoldt (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)
        else 0 := by
  by_cases hdiv : m ∣ n
  · obtain ⟨q, rfl⟩ := hdiv
    have hq : ∀ k, (m * q = k * m ↔ k = q) := fun k => by
      constructor
      · intro h; nlinarith [Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) (by linarith : k * m = q * m)]
      · intro h; rw [h]; ring
    simp_rw [hq, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' (range (N + 1)) q, if_pos (mem_range.mpr (by nlinarith)),
      Nat.mul_div_cancel_left q (by omega)]
    unfold vonMangoldtAtom
    by_cases hq2 : 2 ≤ q
    · rw [if_pos hq2, if_pos ⟨dvd_mul_right m q, by nlinarith⟩]
    · rw [if_neg hq2]
      rcases (show q = 0 ∨ q = 1 by omega) with h | h
      · subst h; simp
      · subst h; simp
  · have hne : ∀ k, n ≠ k * m := fun k h => hdiv ⟨k, by rw [h]; ring⟩
    simp [hne, hdiv]

/-- The ratio lags, weighted by `Λ_k`, are the atomic Weil prime form. -/
theorem tsum_ratioLag (N : ℕ) (x : ℕ → ℝ) :
    ∑' k : ℕ, vonMangoldtAtom k * ratioLag N k x = atomicWeilForm N x := by
  rw [tsum_eq_sum (s := range (N + 1)) fun k hk => by
    rw [ratioLag_eq_zero (by simpa using hk), mul_zero]]
  unfold ratioLag atomicWeilForm
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n hn => ?_
  have hm1 := (mem_Icc.mp hm)
  have hn1 := (mem_Icc.mp hn)
  have e : ∀ k, vonMangoldtAtom k * (x m * x n * ((if m = k * n then 1 else 0) +
      (if n = k * m then 1 else 0))) = x m * x n * (vonMangoldtAtom k * (if m = k * n then 1 else 0) +
        vonMangoldtAtom k * (if n = k * m then 1 else 0)) := fun k => by ring
  simp_rw [e]
  rw [← mul_sum, sum_add_distrib, sum_vonMangoldtAtom_ratio hn1.1 hm1.2,
    sum_vonMangoldtAtom_ratio hm1.1 hn1.2, weilPrimeKernel_eq_add, add_comm]

/-- **The overlap identity**: for a bump supported in `[0, w]`, at every width,
`primeSum f_x = ‖g‖² P_N(x) + NR_w(x)`. -/
theorem primeSum_atomicTest_eq_ratio_add (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    primeSum (atomicTest N x g) = (∫ u, g u ^ 2) * atomicWeilForm N x + nonRatioForm g N x := by
  rw [primeSum_atomicTest_eq_lags hg hgc]
  have hterm : ∀ k, vonMangoldtAtom k * lagForm g N k x =
      (∫ u, g u ^ 2) * (vonMangoldtAtom k * ratioLag N k x) +
        vonMangoldtAtom k * nonRatioLag g N k x := fun k => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [vonMangoldtAtom]
    · rw [lagForm_eq_ratio_add hk]; ring
  have hs1 : Summable fun k => (∫ u, g u ^ 2) * (vonMangoldtAtom k * ratioLag N k x) :=
    summable_of_ne_finset_zero (s := range (N + 1)) fun k hk => by
      rw [ratioLag_eq_zero (by simpa using hk), mul_zero, mul_zero]
  have hs2 : Summable fun k => vonMangoldtAtom k * nonRatioLag g N k x := by
    have := (summable_lagForm hgsupp hw N x vonMangoldtAtom).sub hs1
    refine this.congr fun k => ?_
    rw [hterm k]; ring
  rw [tsum_congr hterm, hs1.tsum_add hs2, tsum_mul_left, tsum_ratioLag]
  rfl

/-! ### Counting near a point -/

/-- At most `2d` naturals other than `c` lie within `d` of `c`. -/
theorem card_near_le (S : Finset ℕ) (c : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    ((S.filter fun n => n ≠ c ∧ |(n : ℝ) - c| ≤ d).card : ℝ) ≤ 2 * d := by
  set D := ⌊d⌋₊
  have hsub : (S.filter fun n => n ≠ c ∧ |(n : ℝ) - c| ≤ d) ⊆ (Icc (c - D) (c + D)).erase c := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨-, hne, hle⟩ := hn
    refine mem_erase.mpr ⟨hne, mem_Icc.mpr ⟨?_, ?_⟩⟩
    · have : (c : ℝ) - n ≤ d := by linarith [abs_le.mp hle]
      have h2 : c - n ≤ D := by
        rcases le_or_gt n c with h | h
        · have : ((c - n : ℕ) : ℝ) ≤ d := by rw [Nat.cast_sub h]; exact this
          exact Nat.le_floor this
        · omega
      omega
    · have : (n : ℝ) - c ≤ d := (abs_le.mp hle).2
      have h2 : n - c ≤ D := by
        rcases le_or_gt c n with h | h
        · have : ((n - c : ℕ) : ℝ) ≤ d := by rw [Nat.cast_sub h]; exact this
          exact Nat.le_floor this
        · omega
      omega
  have hc : c ∈ Icc (c - D) (c + D) := mem_Icc.mpr ⟨Nat.sub_le c D, Nat.le_add_right c D⟩
  have hcard : ((Icc (c - D) (c + D)).erase c).card ≤ 2 * D := by
    rw [card_erase_of_mem hc, Nat.card_Icc]
    omega
  have hD : (D : ℝ) ≤ d := Nat.floor_le hd
  calc ((S.filter fun n => n ≠ c ∧ |(n : ℝ) - c| ≤ d).card : ℝ)
      ≤ (((Icc (c - D) (c + D)).erase c).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ((2 * D : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * d := by push_cast; linarith

/-- A log-window of half-width `w ≥ 0` around `c > 0` lies within `c(e^w − 1)` of `c`. -/
theorem abs_sub_le_of_abs_log_le {y c w : ℝ} (hy : 0 < y) (hc : 0 < c)
    (h : |Real.log y - Real.log c| ≤ w) : |y - c| ≤ c * (Real.exp w - 1) := by
  rw [abs_le] at h ⊢
  have h1 : y ≤ c * Real.exp w := by
    have : Real.log y ≤ Real.log c + w := by linarith
    rw [← Real.exp_le_exp, Real.exp_log hy, Real.exp_add, Real.exp_log hc] at this
    exact this
  have h2 : c * Real.exp (-w) ≤ y := by
    have : Real.log c - w ≤ Real.log y := by linarith
    rw [← Real.exp_le_exp, Real.exp_log hy, Real.exp_sub, Real.exp_log hc] at this
    rwa [Real.exp_neg, ← div_eq_mul_inv]
  have h3 : 1 - Real.exp (-w) ≤ Real.exp w - 1 := by
    have := Real.add_one_le_exp w
    have := Real.add_one_le_exp (-w)
    have hm : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos w, Real.exp_pos (-w)]
  constructor <;> nlinarith

/-! ### The non-ratio rows -/

/-- The up window: `n ≠ km` and `log(n/m)` within `w` of `log k`. -/
def upWin (w : ℝ) (k m n : ℕ) : Prop :=
  n ≠ k * m ∧ |Real.log k - (Real.log n - Real.log m)| ≤ w

/-- The up-window indicator. -/
def upInd (w : ℝ) (k m n : ℕ) : ℝ := by
  classical exact if upWin w k m n then 1 else 0

theorem upInd_nonneg (w : ℝ) (k m n : ℕ) : 0 ≤ upInd w k m n := by
  unfold upInd; split_ifs <;> norm_num

/-- One non-ratio term is at most `‖g‖²` times its window indicator. -/
theorem abs_nonRatio_term_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (k m n : ℕ) :
    |(if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))| ≤
      (∫ u, g u ^ 2) * upInd w k m n := by
  unfold upInd upWin
  by_cases h1 : n = k * m
  · rw [if_pos h1, abs_zero]
    exact mul_nonneg (integral_nonneg fun u => sq_nonneg _) (by split_ifs <;> norm_num)
  rw [if_neg h1]
  by_cases h2 : |Real.log k - (Real.log n - Real.log m)| ≤ w
  · rw [if_pos ⟨h1, h2⟩, mul_one]; exact abs_bumpCorr_le hg hgc _
  · rw [if_neg (fun h => h2 h.2), mul_zero, bumpCorr_eq_zero hgsupp (not_le.mp h2), abs_zero]

/-- The down terms are the up terms with `m` and `n` exchanged. -/
theorem nonRatio_down_eq (k m n : ℕ) :
    (if m = k * n then (0 : ℝ) else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) =
      if m = k * n then 0 else bumpCorr g (-(Real.log k - (Real.log m - Real.log n))) := by
  congr 2; ring

theorem bumpCorr_neg (t : ℝ) : bumpCorr g (-t) = bumpCorr g t := by
  unfold bumpCorr
  have h := integral_add_right_eq_self (μ := volume) (fun v => g v * g (v + -t)) t
  simp only [add_neg_cancel_right] at h
  rw [← h]
  congr 1
  funext v
  ring

/-- **The non-ratio lag of order `k` by its windows**:
`|nonRatioLag_k(x)| ≤ ‖g‖² Σ_{m,n} |x_m||x_n| (1_up(k,m,n) + 1_up(k,n,m))`. -/
theorem abs_nonRatioLag_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N k : ℕ) (x : ℕ → ℝ) :
    |nonRatioLag g N k x| ≤ (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      |x m| * |x n| * (upInd w k m n + upInd w k n m) := by
  unfold nonRatioLag
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  have h1 := abs_nonRatio_term_le hg hgc hgsupp k m n
  have h2 := abs_nonRatio_term_le hg hgc hgsupp (w := w) k n m
  rw [nonRatio_down_eq, bumpCorr_neg] at *
  rw [abs_mul, abs_mul]
  have hxx : 0 ≤ |x m| * |x n| := by positivity
  calc |x m| * |x n| * |(if m = k * n then 0 else
          bumpCorr g (Real.log k - (Real.log m - Real.log n))) +
        (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))|
      ≤ |x m| * |x n| * ((∫ u, g u ^ 2) * upInd w k n m + (∫ u, g u ^ 2) * upInd w k m n) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h2 h1)) hxx
    _ = (∫ u, g u ^ 2) * (|x m| * |x n| * (upInd w k m n + upInd w k n m)) := by ring

/-- **Weighted Schur step**: for a symmetric nonnegative kernel `V`,
`Σ_{m,n} |x_m||x_n| V(m,n) ≤ Σ_m x_m² Σ_n √(m/n) V(m,n)`. -/
theorem sum_abs_mul_le_schur (N : ℕ) (x : ℕ → ℝ) (V : ℕ → ℕ → ℝ)
    (hV : ∀ m n, 0 ≤ V m n) (hsym : ∀ m n, V m n = V n m) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n ≤
      ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n := by
  have hpair : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, |x m| * |x n| * V m n ≤
      (x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) +
        x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V n m)) / 2 := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    set a := Real.sqrt ((m : ℝ) / n)
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hinv : Real.sqrt ((n : ℝ) / m) = a⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    rw [hinv, ← hsym m n]
    have hV0 := hV m n
    have key : 2 * (|x m| * |x n|) ≤ x m ^ 2 * a + x n ^ 2 * a⁻¹ := by
      have key' : 2 * (|x m| * |x n|) * a ≤ (|x m| ^ 2 * a + |x n| ^ 2 * a⁻¹) * a := by
        rw [add_mul, mul_assoc (|x n| ^ 2), inv_mul_cancel₀ ha.ne', mul_one]
        nlinarith [sq_nonneg (|x m| * a - |x n|)]
      have := le_of_mul_le_mul_right key' ha
      rwa [sq_abs, sq_abs] at this
    nlinarith
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n
      ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) +
          x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V n m)) / 2 :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    _ = ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n := by
        simp_rw [add_div, sum_add_distrib]
        rw [sum_comm (f := fun (m n : ℕ) => x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V n m) / 2),
          ← two_mul, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        ring

/-- In the up window, `n ≥ km e^{−w}`, so `√(m/n) ≤ e^{w/2}/√k`, and `|n − km| ≤ km(e^w − 1)`. -/
theorem upWin_bounds {k m n : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : |Real.log k - (Real.log n - Real.log m)| ≤ w) :
    Real.sqrt ((m : ℝ) / n) ≤ Real.exp (w / 2) / Real.sqrt k ∧
      |(n : ℝ) - (k * m : ℕ)| ≤ (k * m : ℕ) * (Real.exp w - 1) ∧
        (k : ℝ) * m * Real.exp (-w) ≤ n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkm : Real.log ((k * m : ℕ) : ℝ) = Real.log k + Real.log m := by
    push_cast; exact Real.log_mul hk0.ne' hm0.ne'
  have hlog : |Real.log n - Real.log ((k * m : ℕ) : ℝ)| ≤ w := by
    rw [hkm, abs_sub_comm]; convert h using 2; ring
  have hlow : (k : ℝ) * m * Real.exp (-w) ≤ n := by
    have : Real.log ((k * m : ℕ) : ℝ) - w ≤ Real.log n := by linarith [abs_le.mp hlog]
    rw [← Real.exp_le_exp, Real.exp_sub, Real.exp_log hn0, Real.exp_log (by positivity)] at this
    push_cast at this
    rwa [Real.exp_neg, ← div_eq_mul_inv]
  refine ⟨?_, abs_sub_le_of_abs_log_le hn0 (by positivity) hlog, hlow⟩
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hk0), ← Real.sqrt_mul (by positivity),
    show Real.exp (w / 2) = Real.sqrt (Real.exp w) by
      rw [← Real.exp_half]]
  refine Real.sqrt_le_sqrt ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
  have he : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos w, Real.exp_pos (-w)]

/-- In the down window, `kn ≥ m e^{−w}`, so `√(m/n) ≤ e^{w/2}√k`, and `|kn − m| ≤ m(e^w − 1)`. -/
theorem downWin_bounds {k m n : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : |Real.log k - (Real.log m - Real.log n)| ≤ w) :
    Real.sqrt ((m : ℝ) / n) ≤ Real.exp (w / 2) * Real.sqrt k ∧
      |((k * n : ℕ) : ℝ) - m| ≤ m * (Real.exp w - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : Real.log ((k * n : ℕ) : ℝ) = Real.log k + Real.log n := by
    push_cast; exact Real.log_mul hk0.ne' hn0.ne'
  have hlog : |Real.log ((k * n : ℕ) : ℝ) - Real.log m| ≤ w := by
    rw [hkn]; convert h using 2; ring
  refine ⟨?_, abs_sub_le_of_abs_log_le (by positivity) hm0 hlog⟩
  have hlow : (m : ℝ) * Real.exp (-w) ≤ k * n := by
    have : Real.log m - w ≤ Real.log ((k * n : ℕ) : ℝ) := by linarith [abs_le.mp hlog]
    rw [← Real.exp_le_exp, Real.exp_sub, Real.exp_log hm0, Real.exp_log (by positivity)] at this
    push_cast at this
    rwa [Real.exp_neg, ← div_eq_mul_inv]
  rw [show Real.exp (w / 2) = Real.sqrt (Real.exp w) by rw [← Real.exp_half],
    ← Real.sqrt_mul (Real.exp_pos w).le]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hn0]
  have he : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos w, Real.exp_pos (-w)]

/-- **Reindexing by the product**: `Σ_{k,n} Λ(k) [Q(kn)] ≤ Σ_{ℓ, Q(ℓ)} log ℓ`, since the pairs
with `kn = ℓ` are divisors of `ℓ` and `Σ_{d ∣ ℓ} Λ(d) = log ℓ`. -/
theorem sum_sum_vonMangoldt_le (A B : Finset ℕ) (hA : ∀ k ∈ A, 1 ≤ k) (hB : ∀ n ∈ B, 1 ≤ n)
    (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ k ∈ A, ∑ n ∈ B, (if Q (k * n) then ArithmeticFunction.vonMangoldt k else 0) ≤
      ∑ ℓ ∈ ((A ×ˢ B).image fun p => p.1 * p.2).filter Q, Real.log ℓ := by
  rw [← sum_product' (f := fun k n => if Q (k * n) then ArithmeticFunction.vonMangoldt k else 0),
    ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2)
      (t := (A ×ˢ B).image fun p => p.1 * p.2) fun p hp => mem_image_of_mem _ hp, sum_filter]
  refine sum_le_sum fun ℓ hℓ => ?_
  split_ifs with hQ
  · -- the fiber of `ℓ` injects into its divisors
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hℓ
    have hℓ0 : p₀.1 * p₀.2 ≠ 0 := Nat.mul_ne_zero (by have := hA _ (mem_product.mp hp₀).1; omega)
      (by have := hB _ (mem_product.mp hp₀).2; omega)
    rw [← ArithmeticFunction.vonMangoldt_sum]
    have hfib : ∀ p ∈ (A ×ˢ B).filter (fun p => p.1 * p.2 = p₀.1 * p₀.2),
        (if Q (p.1 * p.2) then ArithmeticFunction.vonMangoldt p.1 else 0) =
          ArithmeticFunction.vonMangoldt p.1 := fun p hp => by
      rw [(mem_filter.mp hp).2, if_pos hQ]
    rw [sum_congr rfl hfib]
    have hinj : Set.InjOn Prod.fst ((A ×ˢ B).filter (fun p => p.1 * p.2 = p₀.1 * p₀.2) : Set (ℕ × ℕ)) := by
      intro p hp q hq hpq
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have h1 : 1 ≤ p.1 := hA _ (mem_product.mp (mem_filter.mp hp).1).1
      have h2 : p.2 = q.2 := by
        rw [hpq] at hp'
        exact Nat.eq_of_mul_eq_mul_left (by rw [← hpq]; omega) (hp'.trans hq'.symm)
      exact Prod.ext hpq h2
    rw [← sum_image (f := fun d => ArithmeticFunction.vonMangoldt d) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg
    intro d hd
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
    refine Nat.mem_divisors.mpr ⟨⟨p.2, ?_⟩, hℓ0⟩
    exact (mem_filter.mp hp).2.symm
  · refine le_of_eq (sum_eq_zero fun p hp => ?_)
    rw [(mem_filter.mp hp).2, if_neg hQ]

theorem vonMangoldtAtom_eq_zero_of_lt_two {k : ℕ} (hk : k < 2) : vonMangoldtAtom k = 0 := by
  unfold vonMangoldtAtom; rw [if_neg (by omega)]

theorem vonMangoldtAtom_eq {k : ℕ} (hk : 2 ≤ k) :
    vonMangoldtAtom k = ArithmeticFunction.vonMangoldt k / Real.sqrt k := by
  unfold vonMangoldtAtom; rw [if_pos hk]

/-- **The up rows**: `Σ_k Λ_k Σ_n √(m/n) 1_up(k, m, n) ≤ 2(log 4 + 4) e^{3w/2}(e^w − 1) N`. -/
theorem up_row_le (hw : 0 ≤ w) {m N : ℕ} (hm : 1 ≤ m) (K : ℕ) :
    ∑ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n ≤
      2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hew : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  set k₁ := ⌊(N : ℝ) * Real.exp w / m⌋₊
  -- one order `k`
  have hk : ∀ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) *
      upInd w k m n ≤ (if k ∈ Icc 1 k₁ then ArithmeticFunction.vonMangoldt k else 0) *
        (2 * m * (Real.exp w - 1) * Real.exp (w / 2)) := by
    intro k _
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
      split_ifs <;> [exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity);
        simp]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    -- the inner sum runs over the window
    have hinner : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n ≤
        ∑ n ∈ (Icc 1 N).filter (fun n => n ≠ k * m ∧ |(n : ℝ) - (k * m : ℕ)| ≤
          (k * m : ℕ) * (Real.exp w - 1)), Real.exp (w / 2) / Real.sqrt k := by
      rw [sum_filter]
      refine sum_le_sum fun n hn => ?_
      have hn1 := (mem_Icc.mp hn).1
      unfold upInd upWin
      split_ifs with h1 h2
      · rw [mul_one]; exact (upWin_bounds (by omega) hm hn1 h1.2).1
      · exact absurd ⟨h1.1, (upWin_bounds (by omega) hm hn1 h1.2).2.1⟩ h2
      · rw [mul_zero]; positivity
      · rw [mul_zero]
    rw [sum_const, nsmul_eq_mul] at hinner
    have hcard := card_near_le (Icc 1 N) (k * m) (show (0 : ℝ) ≤ (k * m : ℕ) * (Real.exp w - 1) by
      positivity)
    by_cases hkK : k ∈ Icc 1 k₁
    · rw [if_pos hkK, vonMangoldtAtom_eq hk2]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := k)
      calc ArithmeticFunction.vonMangoldt k / Real.sqrt k * ∑ n ∈ Icc 1 N,
            Real.sqrt ((m : ℝ) / n) * upInd w k m n
          ≤ ArithmeticFunction.vonMangoldt k / Real.sqrt k *
              (2 * ((k * m : ℕ) * (Real.exp w - 1)) * (Real.exp (w / 2) / Real.sqrt k)) := by
            refine mul_le_mul_of_nonneg_left (hinner.trans ?_) (by positivity)
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = ArithmeticFunction.vonMangoldt k * (2 * m * (Real.exp w - 1) * Real.exp (w / 2)) := by
            push_cast
            have : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
            field_simp
            rw [Real.sq_sqrt hk0.le]
    · -- beyond `k₁` the window misses `[1, N]`
      rw [if_neg hkK, zero_mul]
      have hbig : (N : ℝ) * Real.exp w / m < k := by
        have : k₁ < k := by
          by_contra hle
          exact hkK (mem_Icc.mpr ⟨by omega, by omega⟩)
        exact (Nat.lt_of_floor_lt this)
      have hzero : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n = 0 := by
        refine sum_eq_zero fun n hn => ?_
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        unfold upInd upWin
        split_ifs with h1
        · exfalso
          have hle := (upWin_bounds (by omega) hm hn1 h1.2).2.2
          have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
          rw [div_lt_iff₀ hm0] at hbig
          have he : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos w, Real.exp_pos (-w)]
        · rw [mul_zero]
      rw [hzero, mul_zero]
  refine (sum_le_sum hk).trans ?_
  rw [← sum_mul, ← sum_filter]
  have hsub : (range K).filter (fun k => k ∈ Icc 1 k₁) ⊆ Icc 1 k₁ :=
    fun k hk => (mem_filter.mp hk).2
  have hΛ : ∑ k ∈ (range K).filter (fun k => k ∈ Icc 1 k₁), ArithmeticFunction.vonMangoldt k ≤
      (Real.log 4 + 4) * k₁ :=
    (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => ArithmeticFunction.vonMangoldt_nonneg).trans
      (sum_vonMangoldt_Icc_le k₁)
  have hk₁ : (k₁ : ℝ) ≤ N * Real.exp w / m := Nat.floor_le (by positivity)
  have hc : 0 ≤ 2 * m * (Real.exp w - 1) * Real.exp (w / 2) := by positivity
  calc (∑ k ∈ (range K).filter (fun k => k ∈ Icc 1 k₁), ArithmeticFunction.vonMangoldt k) *
        (2 * m * (Real.exp w - 1) * Real.exp (w / 2))
      ≤ (Real.log 4 + 4) * (N * Real.exp w / m) * (2 * m * (Real.exp w - 1) * Real.exp (w / 2)) := by
        refine mul_le_mul_of_nonneg_right (hΛ.trans ?_) hc
        exact mul_le_mul_of_nonneg_left hk₁ (by positivity)
    _ = 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N := by
        rw [show 3 * w / 2 = w + w / 2 by ring, Real.exp_add]
        field_simp

/-- **The down rows**: `Σ_k Λ_k Σ_n √(m/n) 1_up(k, n, m) ≤ 2 e^{w/2} m (e^w − 1)(log m + w)`. -/
theorem down_row_le (hw : 0 ≤ w) {m N : ℕ} (hm : 1 ≤ m) (K : ℕ) :
    ∑ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k n m ≤
      2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hew : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  set d := (m : ℝ) * (Real.exp w - 1)
  have hd : 0 ≤ d := by positivity
  set Q : ℕ → Prop := fun ℓ => ℓ ≠ m ∧ |(ℓ : ℝ) - m| ≤ d
  -- each order `k` is at most `e^{w/2}` times the weighted pair count
  have hk : ∀ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) *
      upInd w k n m ≤ Real.exp (w / 2) * ∑ n ∈ Icc 1 N,
        (if Q (k * n) then ArithmeticFunction.vonMangoldt k else 0) := by
    intro k _
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun n _ => by
        split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl])
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    rw [vonMangoldtAtom_eq hk2, mul_sum, mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn1 := (mem_Icc.mp hn).1
    unfold upInd upWin
    by_cases h1 : m ≠ k * n ∧ |Real.log k - (Real.log m - Real.log n)| ≤ w
    · obtain ⟨hb1, hb2⟩ := downWin_bounds (by omega) hm hn1 h1.2
      have hQ : Q (k * n) := ⟨fun h => h1.1 h.symm, hb2⟩
      rw [if_pos h1, if_pos hQ, mul_one]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := k)
      calc ArithmeticFunction.vonMangoldt k / Real.sqrt k * Real.sqrt ((m : ℝ) / n)
          ≤ ArithmeticFunction.vonMangoldt k / Real.sqrt k * (Real.exp (w / 2) * Real.sqrt k) :=
            mul_le_mul_of_nonneg_left hb1 (by positivity)
        _ = Real.exp (w / 2) * ArithmeticFunction.vonMangoldt k := by field_simp
    · rw [if_neg h1, mul_zero, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (by
        split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl])
  refine (sum_le_sum hk).trans ?_
  rw [← mul_sum]
  -- the order `0` contributes nothing; reindex by `ℓ = kn`
  have hpos : ∑ k ∈ (range K).filter (fun k => 1 ≤ k), ∑ n ∈ Icc 1 N,
      (if Q (k * n) then ArithmeticFunction.vonMangoldt k else 0) =
      ∑ k ∈ range K, ∑ n ∈ Icc 1 N, (if Q (k * n) then ArithmeticFunction.vonMangoldt k else 0) := by
    refine sum_filter_of_ne fun k _ hne => ?_
    by_contra h0
    have : k = 0 := by omega
    subst this
    exact hne (sum_eq_zero fun n _ => by simp)
  rw [← hpos]
  have hre := sum_sum_vonMangoldt_le ((range K).filter (fun k => 1 ≤ k)) (Icc 1 N)
    (fun k hk => (mem_filter.mp hk).2) (fun n hn => (mem_Icc.mp hn).1) Q
  set L := (((range K).filter (fun k => 1 ≤ k)) ×ˢ Icc 1 N).image (fun p : ℕ × ℕ => p.1 * p.2)
  -- every `ℓ` in the window has `log ℓ ≤ log m + w`, and there are at most `2d` of them
  have hlog : ∀ ℓ ∈ L.filter Q, Real.log ℓ ≤ Real.log m + w := by
    intro ℓ hℓ
    obtain ⟨hℓL, -, hℓd⟩ := mem_filter.mp hℓ
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hℓL
    have h1 : 1 ≤ p.1 := (mem_filter.mp (mem_product.mp hp).1).2
    have h2 : 1 ≤ p.2 := (mem_Icc.mp (mem_product.mp hp).2).1
    have hpos' : (0 : ℝ) < ((p.1 * p.2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega) (by omega)
    have hup : ((p.1 * p.2 : ℕ) : ℝ) ≤ m * Real.exp w := by
      have := (abs_le.mp hℓd).2
      simp only [d] at this
      linarith
    calc Real.log ((p.1 * p.2 : ℕ) : ℝ) ≤ Real.log (m * Real.exp w) := Real.log_le_log hpos' hup
      _ = Real.log m + w := by rw [Real.log_mul hm0.ne' (Real.exp_pos w).ne', Real.log_exp]
  have hcard : ((L.filter Q).card : ℝ) ≤ 2 * d := card_near_le L m hd
  have hlogm : 0 ≤ Real.log m + w := by
    have := Real.log_natCast_nonneg m; linarith
  calc Real.exp (w / 2) * ∑ k ∈ (range K).filter (fun k => 1 ≤ k), ∑ n ∈ Icc 1 N,
        (if Q (k * n) then ArithmeticFunction.vonMangoldt k else 0)
      ≤ Real.exp (w / 2) * ∑ ℓ ∈ L.filter Q, Real.log ℓ :=
        mul_le_mul_of_nonneg_left hre (Real.exp_pos _).le
    _ ≤ Real.exp (w / 2) * ((L.filter Q).card * (Real.log m + w)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := sum_le_card_nsmul (L.filter Q) (fun ℓ => Real.log ℓ) (Real.log m + w) hlog
        rwa [nsmul_eq_mul] at this
    _ ≤ Real.exp (w / 2) * (2 * d * (Real.log m + w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hlogm) (Real.exp_pos _).le
    _ = 2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w) := by
        simp only [d]; ring

/-- The row bound of the non-ratio lag form at the atom `m`. -/
def nonRatioRow (w : ℝ) (N m : ℕ) : ℝ :=
  2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N +
    2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w)

theorem nonRatioLag_eq_zero_of_log_lt (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N k : ℕ} (hk : Real.log N + w < Real.log k) (x : ℕ → ℝ) : nonRatioLag g N k x = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [nonRatioLag]
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    simp at hk
    linarith
  have hkN : N < k := by
    by_contra h
    have : Real.log k ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast (not_lt.mp h))
    linarith
  have h := lagForm_eq_ratio_add (g := g) (N := N) hk1 x
  rw [lagForm_eq_zero_of_log_lt hgsupp hw hk, ratioLag_eq_zero hkN, mul_zero, zero_add] at h
  exact h.symm

/-- **The non-ratio rows**: for a bump supported in `[0, w]`,
`|NR_w(x)| ≤ ‖g‖² Σ_m x_m² (2(log 4 + 4) e^{3w/2}(e^w − 1) N + 2e^{w/2} m (e^w − 1)(log m + w))`.
At overlap ratio `K`, `w ≤ K/N`, the rows are `O(K) + O(K (m/N) log N)`. -/
theorem abs_nonRatioForm_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤ (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow w N m := by
  set K := ⌈(N : ℝ) * Real.exp w⌉₊ + 1
  set G := ∫ u, g u ^ 2
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  -- finitely many orders
  have hfin : nonRatioForm g N x = ∑ k ∈ range K, vonMangoldtAtom k * nonRatioLag g N k x := by
    unfold nonRatioForm
    refine tsum_eq_sum fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [nonRatioLag]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hbig : (N : ℝ) * Real.exp w < k := by
      have := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have h2 : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2
      linarith
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [nonRatioLag_eq_zero_of_log_lt hgsupp hw hlog, mul_zero]
  set V : ℕ → ℕ → ℝ := fun m n => ∑ k ∈ range K, vonMangoldtAtom k * (upInd w k m n + upInd w k n m)
  have hV0 : ∀ m n, 0 ≤ V m n := fun m n => sum_nonneg fun k _ =>
    mul_nonneg (vonMangoldtAtom_nonneg' k) (add_nonneg (upInd_nonneg _ _ _ _) (upInd_nonneg _ _ _ _))
  have hVsym : ∀ m n, V m n = V n m := fun m n => sum_congr rfl fun k _ => by ring
  -- each order by its windows, then Schur
  have h1 : |nonRatioForm g N x| ≤ G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n := by
    rw [hfin]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range K, |vonMangoldtAtom k * nonRatioLag g N k x|
        ≤ ∑ k ∈ range K, vonMangoldtAtom k * (G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
            |x m| * |x n| * (upInd w k m n + upInd w k n m)) := by
          refine sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
          exact mul_le_mul_of_nonneg_left (abs_nonRatioLag_le hg hgc hgsupp N k x)
            (vonMangoldtAtom_nonneg' k)
      _ = G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n := by
          simp only [V, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun m _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun n _ => ?_
          refine sum_congr rfl fun k _ => ?_
          ring
  have h2 := sum_abs_mul_le_schur N x V hV0 hVsym
  have h3 : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n ≤ nonRatioRow w N m := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    have e : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n =
        (∑ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n) +
        ∑ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k n m := by
      simp only [V, mul_sum, ← sum_add_distrib]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => sum_congr rfl fun n _ => by ring
    rw [e]
    exact add_le_add (up_row_le hw hm1 K) (down_row_le hw hm1 K)
  calc |nonRatioForm g N x| ≤ G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n := h1
    _ ≤ G * ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n :=
        mul_le_mul_of_nonneg_left h2 hG
    _ ≤ G * ∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow w N m :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun m hm =>
          mul_le_mul_of_nonneg_left (h3 m hm) (sq_nonneg _)) hG

/-- **The prime form at bounded overlap as row sums**: for a bump supported in `[0, w]`,
`primeSum f_x ≤ ‖g‖² Σ_m x_m² (log N + 2(log 4 + 4) − (m/4N) log m + nonRatioRow_w(N, m))` — the
tilted rows of the ratio lags plus the non-ratio rows. -/
theorem primeSum_atomicTest_le_rows (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    primeSum (atomicTest N x g) ≤ (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, x m ^ 2 *
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m + nonRatioRow w N m) := by
  rw [primeSum_atomicTest_eq_ratio_add hg hgc hgsupp hw]
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hP := atomicWeilForm_le_tilted N x
  have hNR := (le_abs_self _).trans (abs_nonRatioForm_le hg hgc hgsupp hw N x)
  have hsplit : ∑ m ∈ Icc 1 N, x m ^ 2 *
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m + nonRatioRow w N m) =
      ∑ m ∈ Icc 1 N, x m ^ 2 * (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) +
        ∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow w N m := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun m _ => by ring
  rw [hsplit, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_left hP hG) hNR

/-- `e^w − 1 ≤ w e^w`. -/
theorem exp_sub_one_le_mul_exp {w : ℝ} : Real.exp w - 1 ≤ w * Real.exp w := by
  have h := Real.add_one_le_exp (-w)
  have he : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos w, Real.exp_pos (-w)]

/-- **The non-ratio rows at overlap ratio `K`**: for `0 ≤ w ≤ K/N`, `w ≤ 1`,
`nonRatioRow ≤ 2(log 4 + 4) e^{5/2} K + 2 e^{3/2} K (m/N)(log m + 1)`: a constant times the ratio
up the tower, the ratio times the relative position `m/N` times `log m` down it. -/
theorem nonRatioRow_le_of_ratio {K : ℝ} {N m : ℕ} (hN : 1 ≤ N) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hwK : w ≤ K / N) (hm : 1 ≤ m) :
    nonRatioRow w N m ≤ 2 * (Real.log 4 + 4) * Real.exp (5 / 2) * K +
      2 * Real.exp (3 / 2) * K * ((m : ℝ) / N) * (Real.log m + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hNw : (N : ℝ) * w ≤ K := by have := (le_div_iff₀ hN0).mp hwK; linarith
  have hK : 0 ≤ K := le_trans (mul_nonneg hN0.le hw0) hNw
  have hew := exp_sub_one_le_mul_exp (w := w)
  have hew0 : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have e1 : Real.exp (3 * w / 2) * Real.exp w ≤ Real.exp (5 / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (w / 2) * Real.exp w ≤ Real.exp (3 / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hup : (Real.exp w - 1) * N ≤ K * Real.exp w := by nlinarith [Real.exp_pos w]
  have hdown : (Real.exp w - 1) * m ≤ K * Real.exp w * ((m : ℝ) / N) := by
    have : (Real.exp w - 1) ≤ K / N * Real.exp w := by
      calc Real.exp w - 1 ≤ w * Real.exp w := hew
        _ ≤ K / N * Real.exp w := mul_le_mul_of_nonneg_right hwK (Real.exp_pos w).le
    calc (Real.exp w - 1) * m ≤ K / N * Real.exp w * m := mul_le_mul_of_nonneg_right this hm0.le
      _ = K * Real.exp w * ((m : ℝ) / N) := by ring
  unfold nonRatioRow
  have hc : 0 ≤ 2 * (Real.log 4 + 4) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have t1 : 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N ≤
      2 * (Real.log 4 + 4) * Real.exp (5 / 2) * K := by
    calc 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N
        = 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * ((Real.exp w - 1) * N) := by ring
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (K * Real.exp w) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 2 * (Real.log 4 + 4) * K * (Real.exp (3 * w / 2) * Real.exp w) := by ring
      _ ≤ 2 * (Real.log 4 + 4) * K * Real.exp (5 / 2) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = _ := by ring
  have t2 : 2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w) ≤
      2 * Real.exp (3 / 2) * K * ((m : ℝ) / N) * (Real.log m + 1) := by
    calc 2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w)
        = 2 * Real.exp (w / 2) * ((Real.exp w - 1) * m) * (Real.log m + w) := by ring
      _ ≤ 2 * Real.exp (w / 2) * (K * Real.exp w * ((m : ℝ) / N)) * (Real.log m + 1) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hdown (by positivity)) (by linarith)
            (by positivity) (by positivity)
      _ = 2 * K * ((m : ℝ) / N) * (Real.log m + 1) * (Real.exp (w / 2) * Real.exp w) := by ring
      _ ≤ 2 * K * ((m : ℝ) / N) * (Real.log m + 1) * Real.exp (3 / 2) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
