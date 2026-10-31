import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticResidualBudgetIsUniformInTheHorizon
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# Bombieri–Vinogradov Level of Distribution for Full Prime Matrix Residuals

Unconditional collective `L²` bound across all normalized Ramanujan conductor modes
`1 ≤ m ≤ M` whenever `M * M ≤ N` (arbitrary level of distribution `0 < θ < 1 / 2`):
```
∑_{m=1}^M ‖P_N v_m - (log N - E_arith(m)) v_m‖² ≤ C_p M log N.
```
Each prime-matrix residual splits into a Mertens/floor profile and a prime-tower
tail correction. On `1 ≤ n ≤ M`, `N / n ≥ √N` supplies `O(1 / (log N)²)` Mertens decay
while the divisor-totient packet bound `∑_{m=1}^M c̃_m(n)² ≤ n (1 + log M)⁴` cancels `1 / n`.
On `M < n ≤ N`, period-`m` grouping transfers each conductor's squared mass to the
summable Wiener log-Lorentzian kernel at cost `O(1)` per conductor. For the prime-tower
tail, quotients `N / n ≥ m` decay at `O((log m)² / m)` while quotients `1 ≤ y = N / n < m`
satisfy a complete-period Cauchy–Schwarz fiber bound of cost `O((log m)²)` per conductor.
-/

noncomputable section

open Finset Filter Topology ArithmeticFunction
open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory ArithmeticEffectivityTheory BezoutValuationIncidence
  SuccessorShellArithmetic

/-! ## Section 1: Periodic interval sums on positive integers -/

private theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ t, 0 ≤ f x) :
    (∑ x ∈ s ∪ t, f x) ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have heq : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have hdisj : Disjoint s (t \ s) := by
    rw [Finset.disjoint_left]; intro x hxs hxt; exact (mem_sdiff.mp hxt).2 hxs
  rw [heq, sum_union hdisj]
  exact add_le_add le_rfl
    (sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_sdiff.mp hx).1) fun x hx _ => hf x hx)

private theorem sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) {f : β → ℝ}
    (hf : ∀ a ∈ s, ∀ x ∈ t a, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have h1 : (∑ x ∈ t a ∪ s.biUnion t, f x) ≤
        (∑ x ∈ t a, f x) + ∑ x ∈ s.biUnion t, f x :=
      sum_union_le_of_nonneg fun x hx => by
        obtain ⟨b, hb, hxb⟩ := mem_biUnion.mp hx
        exact hf b (mem_insert_of_mem hb) x hxb
    exact h1.trans (add_le_add le_rfl (ih fun b hb => hf b (mem_insert_of_mem hb)))

private theorem periodic_add_mul {α : Type*} {f : ℕ → α} {m : ℕ}
    (hf : Function.Periodic f m) (k x : ℕ) : f (x + k * m) = f x := by
  simpa only [Nat.cast_id] using hf.nat_mul k x

/-- Shifting a complete period preserves the sum of an `m`-periodic sequence. -/
theorem sum_Ico_periodic_eq {f : ℕ → ℝ} {m : ℕ} (hm : 0 < m) (hf : Function.Periodic f m)
    (a : ℕ) : (∑ n ∈ Ico a (a + m), f n) = ∑ r ∈ range m, f r := by
  induction a with
  | zero => refine sum_congr (by ext x; simp) fun _ _ => rfl
  | succ a ih =>
    have h1 : Ico a (a + m) = insert a (Ico (a + 1) (a + m)) := by
      ext x; simp only [mem_insert, mem_Ico]; omega
    have h2 : Ico (a + 1) (a + 1 + m) = insert (a + m) (Ico (a + 1) (a + m)) := by
      ext x; simp only [mem_insert, mem_Ico]; omega
    have hnot1 : a ∉ Ico (a + 1) (a + m) := by simp
    have hnot2 : a + m ∉ Ico (a + 1) (a + m) := by simp
    have hs1 : (∑ x ∈ Ico a (a + m), f x) = f a + ∑ x ∈ Ico (a + 1) (a + m), f x := by
      rw [h1, sum_insert hnot1]
    have hs2 : (∑ x ∈ Ico (a + 1) (a + 1 + m), f x) =
        f (a + m) + ∑ x ∈ Ico (a + 1) (a + m), f x := by
      rw [h2, sum_insert hnot2]
    have hper : f (a + m) = f a := hf a
    linarith only [hs1, hs2, hper, ih]

/-- Half-open interval version `(a, a + m]` of complete-period invariance. -/
theorem sum_Ioc_periodic_eq {f : ℕ → ℝ} {m : ℕ} (hm : 0 < m) (hf : Function.Periodic f m)
    (a : ℕ) : (∑ n ∈ Ioc a (a + m), f n) = ∑ r ∈ range m, f r := by
  have heq : Ioc a (a + m) = Ico (a + 1) (a + 1 + m) := by
    ext x; simp only [mem_Ioc, mem_Ico]; omega
  rw [heq, sum_Ico_periodic_eq hm hf (a + 1)]

/-- Any interval `(a, b]` of nonnegative values invariant under `+ m` on positive integers
is bounded by `((b - a) / m + 1)` complete periods `[1, m]`. -/
theorem sum_Ioc_le_mul_sum_Icc_of_periodic_pos {f : ℕ → ℝ} {m : ℕ} (hm : 0 < m)
    (hnonneg : ∀ n, 1 ≤ n → 0 ≤ f n)
    (hper : ∀ n, 1 ≤ n → f (n + m) = f n) (a b : ℕ) :
    (∑ n ∈ Ioc a b, f n) ≤ (((b - a) / m + 1 : ℕ) : ℝ) * ∑ n ∈ Icc 1 m, f n := by
  have hshift : ∀ k n : ℕ, 1 ≤ n → f (n + k * m) = f n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [Nat.succ_mul, ← Nat.add_assoc, hper (n + k * m) (by omega), ih n hn]
  let g : ℕ → ℝ := fun n => f (n % m + m)
  have hg_per : Function.Periodic g m := by
    intro n
    dsimp only [g]
    rw [Nat.add_mod_right]
  have hfg : ∀ n : ℕ, 1 ≤ n → f n = g n := by
    intro n hn
    dsimp only [g]
    by_cases hmod : n % m = 0
    · have hdvd : m ∣ n := Nat.dvd_of_mod_eq_zero hmod
      have hq1 : 1 ≤ n / m := Nat.div_pos (Nat.le_of_dvd hn hdvd) hm
      have hdecomp : n = m + (n / m - 1) * m := by
        have hmul := Nat.div_mul_cancel hdvd
        have hsub : n / m - 1 + 1 = n / m := by omega
        rw [← hsub, Nat.succ_mul, Nat.add_comm] at hmul
        exact hmul.symm
      rw [hmod, Nat.zero_add]
      conv_lhs => rw [hdecomp]
      exact hshift (n / m - 1) m hm
    · have hr1 : 1 ≤ n % m := Nat.pos_of_ne_zero hmod
      have hdecomp : n = n % m + (n / m) * m := by
        have h := (Nat.div_add_mod n m).symm
        linarith [Nat.mul_comm m (n / m)]
      have h1 : f n = f (n % m) := by
        conv_lhs => rw [hdecomp]
        exact hshift (n / m) (n % m) hr1
      rw [h1, (hper (n % m) hr1).symm]
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => hnonneg (n % m + m) (by omega)
  have hIcc : (∑ r ∈ range m, g r) = ∑ n ∈ Icc 1 m, f n := by
    have h0 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
    rw [← sum_Ioc_periodic_eq hm hg_per 0, h0]
    exact sum_congr rfl fun n hn => (hfg n (mem_Ioc.mp hn).1).symm
  let K := (b - a) / m + 1
  have hcover : Ioc a b ⊆ (range K).biUnion (fun k => Ioc (a + k * m) (a + k * m + m)) := by
    intro n hn
    obtain ⟨hna, hnb⟩ := mem_Ioc.mp hn
    let k := (n - a - 1) / m
    refine mem_biUnion.mpr ⟨k, mem_range.mpr ?_, mem_Ioc.mpr ?_⟩
    · have hle : (n - a - 1) / m ≤ (b - a) / m := Nat.div_le_div_right (by omega)
      omega
    · have hdiv := Nat.div_add_mod (n - a - 1) m
      have hmod := Nat.mod_lt (n - a - 1) hm
      have hkm : k * m = m * ((n - a - 1) / m) := Nat.mul_comm _ _
      omega
  calc
    (∑ n ∈ Ioc a b, f n) = ∑ n ∈ Ioc a b, g n :=
      sum_congr rfl fun n hn => hfg n (by have := (mem_Ioc.mp hn).1; omega)
    _ ≤ ∑ n ∈ (range K).biUnion (fun k => Ioc (a + k * m) (a + k * m + m)), g n :=
      sum_le_sum_of_subset_of_nonneg hcover fun n _ _ => hg_nonneg n
    _ ≤ ∑ k ∈ range K, ∑ n ∈ Ioc (a + k * m) (a + k * m + m), g n :=
      sum_biUnion_le_of_nonneg _ _ fun _ _ n _ => hg_nonneg n
    _ = ∑ _k ∈ range K, ∑ n ∈ Icc 1 m, f n := by
      refine sum_congr rfl fun k _ => ?_
      rw [sum_Ioc_periodic_eq hm hg_per (a + k * m), hIcc]
    _ = (K : ℝ) * ∑ n ∈ Icc 1 m, f n := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Complete-period quadratic mass of `normalizedRamanujanMode m` on `(a, a + m]`. -/
theorem sum_Ioc_normalizedRamanujanMode_sq {m : ℕ} (hm : 0 < m) (a : ℕ) :
    (∑ n ∈ Ioc a (a + m), normalizedRamanujanMode m n ^ 2) = (m : ℝ) := by
  have hper : Function.Periodic (fun n => normalizedRamanujanMode m n ^ 2) m :=
    fun n => by dsimp only; rw [normalizedRamanujanMode_periodic hm n]
  rw [sum_Ioc_periodic_eq hm hper a]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  exact (div_eq_iff hmR).mp (periodMean_normalizedRamanujanMode_sq hm) |>.trans (one_mul _)

/-- Prefix quadratic mass bound `∑_{n=1}^N c̃_m(n)^2 ≤ 2 N` for `1 ≤ m ≤ N`. -/
theorem sum_Icc_normalizedRamanujanMode_sq_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n ^ 2) ≤ 2 * (N : ℝ) := by
  have h0 : Icc 1 N = Ioc 0 N := by ext x; simp only [mem_Icc, mem_Ioc]; omega
  have hIcc : (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2) = (m : ℝ) := by
    have h1 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
    rw [h1, sum_Ioc_normalizedRamanujanMode_sq hm 0]
  rw [h0]
  calc
    (∑ n ∈ Ioc 0 N, normalizedRamanujanMode m n ^ 2) ≤
        (((N - 0) / m + 1 : ℕ) : ℝ) * ∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2 :=
      sum_Ioc_le_mul_sum_Icc_of_periodic_pos hm (fun _ _ => sq_nonneg _)
        (fun n _ => by rw [normalizedRamanujanMode_periodic hm n]) 0 N
    _ = ((N / m : ℕ) : ℝ) * m + m := by
      rw [Nat.sub_zero, hIcc]; push_cast; ring
    _ ≤ (N : ℝ) + N := by
      have hdiv : ((N / m : ℕ) : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
      have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
      linarith only [hdiv, hmNR]
    _ = 2 * (N : ℝ) := by ring

/-! ## Section 2: Mertens and floor contribution (`0 < θ < 1/2`) -/

private theorem wiener_lorentzian_sum_le {N : ℕ} (hN : 0 < N) :
    (∑ j ∈ Icc 1 N, 1 / (j : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹) ≤
        1 + 2 * Real.pi ^ 2 := by
  have hcheby : chebyWith 1 (fun _ : ℕ => (1 : ℂ)) := fun _ => by simp [cumsum]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum : Summable (fun j : ℕ => 1 / (j : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹) := by
    simpa only [norm_one, one_div] using
      limiting_fourier_lim1_aux ⟨1, hcheby⟩ hN0 1 zero_le_one
  have hfull : (∑' j : ℕ, 1 / (j : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹) ≤
        1 + 2 * Real.pi ^ 2 := by
    simpa only [norm_one, one_mul] using bound_sum_log' hcheby hN1
  exact (Summable.sum_le_tsum (Icc 1 N) (fun j _ => by positivity) hsum).trans hfull

/-- Companion-block log-Lorentzian comparison when `j < n ≤ 3 * j` and `n ≤ N`. -/
private theorem companion_block_kernel_comparison {N n j : ℕ}
    (hj0 : 0 < j) (hjn : j ≤ n) (hn3j : n ≤ 3 * j) (hnN : n ≤ N) :
    1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2 ≤
      2 * (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := by
  have hn0 : 0 < n := hj0.trans_le hjn
  have hN0 : 0 < N := hn0.trans_le hnN
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hy : 1 ≤ N / n := Nat.div_pos hnN hn0
  have hyR : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hy
  have hNy : (N : ℝ) ≤ 2 * ((N / n : ℕ) : ℝ) * n := by
    have hmod := Nat.mod_lt N hn0
    have hid := Nat.mod_add_div N n
    have hlt : N < (N / n + 1) * n := by nlinarith only [hmod, hid]
    have hle : N ≤ 2 * (N / n) * n := by nlinarith only [hlt, hy]
    exact_mod_cast hle
  have hn3jR : (n : ℝ) ≤ 3 * j := by exact_mod_cast hn3j
  have hquot6 : (N : ℝ) / j ≤ 6 * ((N / n : ℕ) : ℝ) := by
    rw [div_le_iff₀ hjR]
    nlinarith only [hNy, hn3jR, hyR]
  have hjNR : (j : ℝ) ≤ N := by exact_mod_cast hjn.trans hnN
  have hlog_neg : Real.log ((j : ℝ) / N) ≤ 0 :=
    Real.log_nonpos (div_nonneg hjR.le hNR.le) ((div_le_one hNR).mpr hjNR)
  have hlog_abs : |Real.log ((j : ℝ) / N)| = Real.log ((N : ℝ) / j) := by
    rw [abs_of_nonpos hlog_neg, Real.log_div hjR.ne' hNR.ne', Real.log_div hNR.ne' hjR.ne']
    ring
  have hlog6 : Real.log 6 ≤ 5 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hlog_ub : Real.log ((N : ℝ) / j) ≤ 5 + Real.log ((N / n : ℕ) : ℝ) := by
    have h1 := Real.log_le_log (div_pos hNR hjR) hquot6
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    linarith only [h1, hlog6]
  have hpi : (6 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hlog_y : 0 ≤ Real.log ((N / n : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hscaled : |1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)| ≤
      1 + Real.log ((N / n : ℕ) : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), hlog_abs,
      one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith only [hlog_ub, hpi, hlog_y]
  have hsq := mul_self_le_mul_self (abs_nonneg _) hscaled
  rw [← sq, sq_abs, ← sq] at hsq
  nlinarith only [hsq, hlog_y]

/-- Uniform `O(1)` bound per conductor `m` on the Mertens residual sum over `n ∈ (m, N]`. -/
private theorem sum_Ioc_mertens_ramanujan_sq_le {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hMert : ∀ y : ℕ, 0 < y → primeMertensRemainderProfile y ≤ C₀ / (1 + Real.log y))
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (∑ n ∈ Ioc m N,
      primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / (n : ℝ)) ≤
      C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) := by
  have hN0 : 0 < N := hm.trans_le hmN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let f : ℕ → ℝ := fun n =>
    primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / (n : ℝ)
  have hf0 : ∀ n, 0 ≤ f n := fun n => by dsimp only [f]; positivity
  -- Split `(m, N]` into `(m, min (2m) N]` and `(2m, N]`.
  have hsplit_sub : Ioc m N ⊆ Ioc m (min (2 * m) N) ∪ Ioc (2 * m) N := by
    intro n hn
    simp only [mem_union, mem_Ioc, le_min_iff] at hn ⊢
    omega
  -- First block `(m, min (2m) N]`: bounded by `C₀^2`.
  have hblock1 : (∑ n ∈ Ioc m (min (2 * m) N), f n) ≤ C₀ ^ 2 := by
    have hpt : ∀ n ∈ Ioc m (min (2 * m) N),
        f n ≤ (C₀ ^ 2 / m) * normalizedRamanujanMode m n ^ 2 := by
      intro n hn
      obtain ⟨hmn, hnmin⟩ := mem_Ioc.mp hn
      have hnN : n ≤ N := le_trans hnmin (min_le_right _ _)
      have hn0 : 0 < n := hm.trans hmn
      have hy : 0 < N / n := Nat.div_pos hnN hn0
      have hlog : 0 ≤ Real.log ((N / n : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have hp : primeMertensRemainderProfile (N / n) ≤ C₀ :=
        (hMert (N / n) hy).trans (div_le_self hC₀.le (by linarith only [hlog]))
      have hpsq : primeMertensRemainderProfile (N / n) ^ 2 ≤ C₀ ^ 2 := by
        have h := mul_self_le_mul_self (by unfold primeMertensRemainderProfile; positivity) hp
        simpa only [← sq] using h
      have hn_ge : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
      dsimp only [f]
      calc
        primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / n ≤
            C₀ ^ 2 * normalizedRamanujanMode m n ^ 2 / m := by
          refine (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpsq (sq_nonneg _)) (Nat.cast_nonneg n)).trans ?_
          exact div_le_div_of_nonneg_left (by positivity) hmR hn_ge
        _ = (C₀ ^ 2 / m) * normalizedRamanujanMode m n ^ 2 := by ring
    have hsub : Ioc m (min (2 * m) N) ⊆ Ioc m (m + m) := by
      intro n hn
      simp only [mem_Ioc, le_min_iff] at hn ⊢
      omega
    calc
      (∑ n ∈ Ioc m (min (2 * m) N), f n) ≤
          ∑ n ∈ Ioc m (min (2 * m) N), (C₀ ^ 2 / m) * normalizedRamanujanMode m n ^ 2 :=
        sum_le_sum hpt
      _ ≤ ∑ n ∈ Ioc m (m + m), (C₀ ^ 2 / m) * normalizedRamanujanMode m n ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (C₀ ^ 2 / m) * ∑ n ∈ Ioc m (m + m), normalizedRamanujanMode m n ^ 2 :=
        (mul_sum _ _ _).symm
      _ = C₀ ^ 2 := by rw [sum_Ioc_normalizedRamanujanMode_sq hm m]; field_simp [hmR.ne']
  -- Remaining blocks `(2m, N]` covered by `k ∈ Icc 2 (N / m)` with companion `J_k = ((k-1)m, km]`.
  let wL : ℕ → ℝ := fun j =>
    1 / (j : ℝ) * (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹
  have hwL0 : ∀ j, 0 ≤ wL j := fun j => by dsimp only [wL]; positivity
  have hcover : Ioc (2 * m) N ⊆
      (Icc 2 (N / m)).biUnion (fun k => Ioc (k * m) (min ((k + 1) * m) N)) := by
    intro n hn
    obtain ⟨hn2m, hnN⟩ := mem_Ioc.mp hn
    let k := (n - 1) / m
    have hk2 : 2 ≤ k := (Nat.le_div_iff_mul_le hm).mpr (by omega)
    have hkN : k ≤ N / m := Nat.div_le_div_right (by omega)
    have hdiv := Nat.div_add_mod (n - 1) m
    have hmod := Nat.mod_lt (n - 1) hm
    have hkm : k * m = m * ((n - 1) / m) := Nat.mul_comm _ _
    have hsucc : (k + 1) * m = k * m + m := Nat.succ_mul k m
    exact mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨hk2, hkN⟩,
      mem_Ioc.mpr ⟨by omega, le_min (by omega) hnN⟩⟩
  have hblock_k : ∀ k ∈ Icc 2 (N / m),
      (∑ n ∈ Ioc (k * m) (min ((k + 1) * m) N), f n) ≤
        2 * C₀ ^ 2 * ∑ j ∈ Ioc ((k - 1) * m) (k * m), wL j := by
    intro k hk
    obtain ⟨hk2, hkNm⟩ := mem_Icc.mp hk
    let B_k := Ioc (k * m) (min ((k + 1) * m) N)
    let J_k := Ioc ((k - 1) * m) (k * m)
    have hJk_card : (J_k.card : ℝ) = m := by
      have heq : J_k = Ioc ((k - 1) * m) ((k - 1) * m + m) := by
        dsimp only [J_k]
        congr 1
        rw [← Nat.succ_mul]
        congr 1
        omega
      rw [heq, Nat.card_Ioc]
      exact_mod_cast Nat.add_sub_cancel_left _ _
    -- For every `j ∈ J_k`, bound the `B_k` sum by `2 * C₀^2 * m * wL j`.
    have hfor_j : ∀ j ∈ J_k, (∑ n ∈ B_k, f n) ≤ (m : ℝ) * (2 * C₀ ^ 2 * wL j) := by
      intro j hj
      obtain ⟨hj_lo, hj_hi⟩ := mem_Ioc.mp hj
      have hj0 : 0 < j := by omega
      have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
      have hpt : ∀ n ∈ B_k, f n ≤ (2 * C₀ ^ 2 * wL j) * normalizedRamanujanMode m n ^ 2 := by
        intro n hn
        obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
        have hnN : n ≤ N := le_trans hn_hi (min_le_right _ _)
        have hn_up : n ≤ (k + 1) * m := le_trans hn_hi (min_le_left _ _)
        have hn0 : 0 < n := hj0.trans (hj_hi.trans_lt hn_lo)
        have hy : 0 < N / n := Nat.div_pos hnN hn0
        have hn3j : n ≤ 3 * j := by
          have hk3 : k + 1 ≤ 3 * (k - 1) := by omega
          have hmul : (k + 1) * m ≤ 3 * ((k - 1) * m) := by
            rw [← Nat.mul_assoc]
            exact Nat.mul_le_mul_right m hk3
          omega
        have hcomp := companion_block_kernel_comparison hj0 (hj_hi.trans hn_lo.le) hn3j hnN
        have hden : 0 < 1 + Real.log ((N / n : ℕ) : ℝ) :=
          by linarith [Real.log_natCast_nonneg (N / n)]
        have hkpos : 0 < 1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2 := by positivity
        have hp := hMert (N / n) hy
        have hpsq : primeMertensRemainderProfile (N / n) ^ 2 ≤
            (C₀ / (1 + Real.log ((N / n : ℕ) : ℝ))) ^ 2 := by
          have h := mul_self_le_mul_self (by unfold primeMertensRemainderProfile; positivity) hp
          simpa only [← sq] using h
        have hratio : (C₀ / (1 + Real.log ((N / n : ℕ) : ℝ))) ^ 2 ≤
            2 * C₀ ^ 2 * (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹ := by
          rw [div_pow, ← div_eq_mul_inv, div_le_div_iff₀ (sq_pos_of_pos hden) hkpos]
          nlinarith only [mul_le_mul_of_nonneg_left hcomp (sq_nonneg C₀)]
        have hinv_n : 1 / (n : ℝ) ≤ 1 / (j : ℝ) :=
          one_div_le_one_div_of_le hjR (by exact_mod_cast hj_hi.trans hn_lo.le)
        dsimp only [f, wL]
        calc
          primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / n =
              (primeMertensRemainderProfile (N / n) ^ 2 * (1 / (n : ℝ))) *
                normalizedRamanujanMode m n ^ 2 := by ring
          _ ≤ ((2 * C₀ ^ 2 * (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹) *
                (1 / (j : ℝ))) * normalizedRamanujanMode m n ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hpsq.trans hratio) hinv_n (by positivity) (by positivity))
              (sq_nonneg _)
          _ = (2 * C₀ ^ 2 * (1 / (j : ℝ) *
                (1 + (1 / (2 * Real.pi) * Real.log ((j : ℝ) / N)) ^ 2)⁻¹)) *
                normalizedRamanujanMode m n ^ 2 := by ring
      have hBk_sub : B_k ⊆ Ioc (k * m) (k * m + m) := by
        intro n hn
        obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨h1, (le_trans h2 (min_le_left _ _)).trans_eq (Nat.succ_mul k m)⟩
      calc
        (∑ n ∈ B_k, f n) ≤
            ∑ n ∈ B_k, (2 * C₀ ^ 2 * wL j) * normalizedRamanujanMode m n ^ 2 := sum_le_sum hpt
        _ ≤ ∑ n ∈ Ioc (k * m) (k * m + m), (2 * C₀ ^ 2 * wL j) * normalizedRamanujanMode m n ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hBk_sub fun _ _ _ => by positivity
        _ = (2 * C₀ ^ 2 * wL j) * ∑ n ∈ Ioc (k * m) (k * m + m), normalizedRamanujanMode m n ^ 2 :=
          (mul_sum _ _ _).symm
        _ = (m : ℝ) * (2 * C₀ ^ 2 * wL j) := by
          rw [sum_Ioc_normalizedRamanujanMode_sq hm (k * m), mul_comm]
    -- Average over `j ∈ J_k` and cancel `m > 0`.
    have havg := sum_le_sum hfor_j
    rw [sum_const, nsmul_eq_mul, hJk_card, ← mul_sum, ← mul_sum] at havg
    exact le_of_mul_le_mul_left havg hmR
  -- Pairwise disjointness of `J_k` inside `Icc 1 N`.
  have hdisj : Set.PairwiseDisjoint (↑(Icc 2 (N / m)) : Set ℕ)
      (fun k => Ioc ((k - 1) * m) (k * m)) := by
    intro k₁ hk₁ k₂ hk₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    obtain ⟨h1a, h1b⟩ := mem_Ioc.mp hj₁
    obtain ⟨h2a, h2b⟩ := mem_Ioc.mp hj₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk_le : k₁ ≤ k₂ - 1 := by omega
      have hmul := Nat.mul_le_mul_right m hk_le
      omega
    · have hk_le : k₂ ≤ k₁ - 1 := by omega
      have hmul := Nat.mul_le_mul_right m hk_le
      omega
  have hJk_sub : (Icc 2 (N / m)).biUnion (fun k => Ioc ((k - 1) * m) (k * m)) ⊆ Icc 1 N := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := mem_biUnion.mp hj
    obtain ⟨hk2, hkN⟩ := mem_Icc.mp hk
    obtain ⟨hj1, hj2⟩ := mem_Ioc.mp hjk
    have hkm : k * m ≤ N := (Nat.mul_le_mul_right m hkN).trans (Nat.div_mul_le_self N m)
    have h1m : 1 ≤ (k - 1) * m + 1 := by omega
    exact mem_Icc.mpr ⟨by omega, hj2.trans hkm⟩
  have hblocks2 : (∑ n ∈ Ioc (2 * m) N, f n) ≤ 2 * C₀ ^ 2 * (1 + 2 * Real.pi ^ 2) := by
    calc
      (∑ n ∈ Ioc (2 * m) N, f n) ≤
          ∑ n ∈ (Icc 2 (N / m)).biUnion (fun k => Ioc (k * m) (min ((k + 1) * m) N)), f n :=
        sum_le_sum_of_subset_of_nonneg hcover fun n _ _ => hf0 n
      _ ≤ ∑ k ∈ Icc 2 (N / m), ∑ n ∈ Ioc (k * m) (min ((k + 1) * m) N), f n :=
        sum_biUnion_le_of_nonneg _ _ fun _ _ n _ => hf0 n
      _ ≤ ∑ k ∈ Icc 2 (N / m), 2 * C₀ ^ 2 * ∑ j ∈ Ioc ((k - 1) * m) (k * m), wL j :=
        sum_le_sum hblock_k
      _ = 2 * C₀ ^ 2 * ∑ k ∈ Icc 2 (N / m), ∑ j ∈ Ioc ((k - 1) * m) (k * m), wL j :=
        (mul_sum _ _ _).symm
      _ = 2 * C₀ ^ 2 * ∑ j ∈ (Icc 2 (N / m)).biUnion (fun k => Ioc ((k - 1) * m) (k * m)), wL j := by
        rw [sum_biUnion hdisj]
      _ ≤ 2 * C₀ ^ 2 * ∑ j ∈ Icc 1 N, wL j :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hJk_sub fun j _ _ => hwL0 j) (by positivity)
      _ ≤ 2 * C₀ ^ 2 * (1 + 2 * Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left (wiener_lorentzian_sum_le hN0) (by positivity)
  calc
    (∑ n ∈ Ioc m N, f n) ≤ ∑ n ∈ Ioc m (min (2 * m) N) ∪ Ioc (2 * m) N, f n :=
      sum_le_sum_of_subset_of_nonneg hsplit_sub fun n _ _ => hf0 n
    _ ≤ (∑ n ∈ Ioc m (min (2 * m) N), f n) + ∑ n ∈ Ioc (2 * m) N, f n :=
      sum_union_le_of_nonneg fun n _ => hf0 n
    _ ≤ C₀ ^ 2 + 2 * C₀ ^ 2 * (1 + 2 * Real.pi ^ 2) := add_le_add hblock1 hblocks2
    _ = C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) := by ring

/-- Collective Mertens/floor bound across `1 ≤ m ≤ M` for `M * M ≤ N` and `1 ≤ log N`. -/
private theorem sum_mertens_levelOfDistribution_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 1 ≤ Real.log N →
      (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / (n : ℝ)) ≤
        C₁ * M * (Real.log N) ^ 2 := by
  obtain ⟨C₀, hC₀, hMert⟩ := exists_primeMertensRemainder_log_envelope
  refine ⟨C₀ ^ 2 * (27 + 4 * Real.pi ^ 2), by positivity, ?_⟩
  intro M N hM hMN hlogN
  have hMN_le : M ≤ N := (Nat.le_mul_self M).trans hMN
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  let f : ℕ → ℕ → ℝ := fun m n =>
    primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / (n : ℝ)
  -- Split `Icc 1 N = Icc 1 M ∪ Ioc M N`.
  have hunion : Icc 1 N = Icc 1 M ∪ Ioc M N := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 M) (Ioc M N) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2; simp only [mem_Icc, mem_Ioc] at hn1 hn2; omega
  have hsplit : (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, f m n) =
      (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 M, f m n) + ∑ m ∈ Icc 1 M, ∑ n ∈ Ioc M N, f m n := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [hunion, sum_union hdisj]
  -- Small `n ∈ Icc 1 M`: swap sums, use `N / n ≥ n` (`M * M ≤ N`) and `sum_normalizedRamanujanMode_sq_le`.
  have hlogM : 1 + Real.log M ≤ (3 / 2) * Real.log N := by
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hNR : (0 : ℝ) < N := by exact_mod_cast (hM.trans hMN_le)
    have hsq : (M : ℝ) ^ 2 ≤ N := by
      rw [sq]
      exact_mod_cast hMN
    have h2 : 2 * Real.log M ≤ Real.log N := by
      have h := Real.log_le_log (sq_pos_of_pos hMR) hsq
      rw [Real.log_pow, Nat.cast_ofNat] at h
      exact h
    linarith only [h2, hlogN]
  have hlogM4 : (1 + Real.log M) ^ 4 ≤ 6 * (Real.log N) ^ 4 := by
    calc
      (1 + Real.log M) ^ 4 ≤ ((3 / 2) * Real.log N) ^ 4 :=
        pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg M]) hlogM 4
      _ = (81 / 16) * (Real.log N) ^ 4 := by ring
      _ ≤ 6 * (Real.log N) ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hLN0.le 4)
  have hsmall : (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 M, f m n) ≤
      24 * C₀ ^ 2 * M * (Real.log N) ^ 2 := by
    rw [sum_comm]
    have hpt : ∀ n ∈ Icc 1 M, (∑ m ∈ Icc 1 M, f m n) ≤ 24 * C₀ ^ 2 * (Real.log N) ^ 2 := by
      intro n hn
      obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
      have hnN : n ≤ N := hnM.trans hMN_le
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hy : 0 < N / n := Nat.div_pos hnN hn1
      have hnn : n ≤ N / n :=
        (Nat.le_div_iff_mul_le hn1).mpr ((Nat.mul_le_mul hnM hnM).trans hMN)
      have hlog_nn : Real.log n ≤ Real.log ((N / n : ℕ) : ℝ) :=
        Real.log_le_log hnR (by exact_mod_cast hnn)
      have hr := roundoff_le hn1 hnN
      have hy1 : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hy
      have hinv_y : 1 / ((N / n : ℕ) : ℝ) ≤ 1 := div_le_self zero_le_one hy1
      have hden_lb : Real.log N / 2 ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
        linarith only [hr.2, hinv_y, hlog_nn]
      have hp : primeMertensRemainderProfile (N / n) ≤ 2 * C₀ / Real.log N := by
        calc
          primeMertensRemainderProfile (N / n) ≤ C₀ / (1 + Real.log ((N / n : ℕ) : ℝ)) :=
            hMert (N / n) hy
          _ ≤ C₀ / (Real.log N / 2) :=
            div_le_div_of_nonneg_left hC₀.le (half_pos hLN0) hden_lb
          _ = 2 * C₀ / Real.log N := by ring
      have hpsq : primeMertensRemainderProfile (N / n) ^ 2 ≤ 4 * C₀ ^ 2 / (Real.log N) ^ 2 := by
        have h := mul_self_le_mul_self (by unfold primeMertensRemainderProfile; positivity) hp
        rw [← sq, ← sq, div_pow] at h
        exact h.trans_eq (by ring)
      have hfactor : (∑ m ∈ Icc 1 M, f m n) =
          (primeMertensRemainderProfile (N / n) ^ 2 / n) *
            ∑ m ∈ Icc 1 M, normalizedRamanujanMode m n ^ 2 := by
        dsimp only [f]
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by ring
      rw [hfactor]
      calc
        (primeMertensRemainderProfile (N / n) ^ 2 / n) *
            ∑ m ∈ Icc 1 M, normalizedRamanujanMode m n ^ 2 ≤
            (primeMertensRemainderProfile (N / n) ^ 2 / n) * ((n : ℝ) * (1 + Real.log M) ^ 4) :=
          mul_le_mul_of_nonneg_left (sum_normalizedRamanujanMode_sq_le M hn1) (by positivity)
        _ = primeMertensRemainderProfile (N / n) ^ 2 * (1 + Real.log M) ^ 4 := by
          field_simp [hnR.ne']
        _ ≤ (4 * C₀ ^ 2 / (Real.log N) ^ 2) * (6 * (Real.log N) ^ 4) :=
          mul_le_mul hpsq hlogM4 (by positivity) (by positivity)
        _ = 24 * C₀ ^ 2 * (Real.log N) ^ 2 := by field_simp [hLN0.ne']; ring
    calc
      (∑ n ∈ Icc 1 M, ∑ m ∈ Icc 1 M, f m n) ≤
          ∑ _n ∈ Icc 1 M, 24 * C₀ ^ 2 * (Real.log N) ^ 2 := sum_le_sum hpt
      _ = 24 * C₀ ^ 2 * M * (Real.log N) ^ 2 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  -- Large `n ∈ Ioc M N ⊆ Ioc m N`: `O(1)` per conductor `m`.
  have hlarge : (∑ m ∈ Icc 1 M, ∑ n ∈ Ioc M N, f m n) ≤
      C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) * M * (Real.log N) ^ 2 := by
    have hpt : ∀ m ∈ Icc 1 M, (∑ n ∈ Ioc M N, f m n) ≤ C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) := by
      intro m hmI
      obtain ⟨hm1, hmM⟩ := mem_Icc.mp hmI
      have hsub : Ioc M N ⊆ Ioc m N := fun n hn =>
        mem_Ioc.mpr ⟨hmM.trans_lt (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2⟩
      exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by dsimp only [f]; positivity).trans
        (sum_Ioc_mertens_ramanujan_sq_le hC₀ hMert hm1 (hmM.trans hMN_le))
    have hL2 : 1 ≤ (Real.log N) ^ 2 := by nlinarith only [hlogN]
    calc
      (∑ m ∈ Icc 1 M, ∑ n ∈ Ioc M N, f m n) ≤
          ∑ _m ∈ Icc 1 M, C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) := sum_le_sum hpt
      _ = C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) * M * 1 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      _ ≤ C₀ ^ 2 * (3 + 4 * Real.pi ^ 2) * M * (Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
  rw [hsplit]
  linarith only [hsmall, hlarge]

/-! ## Section 3: Prime-tower tail correction across all conductors `1 ≤ m ≤ M` -/

/-- Normalized prime-row correction at complementary quotient `y`. -/
private def normalizedPrimeCorrection (m y n : ℕ) : ℝ :=
  poleProfileCorrection (normalizedRamanujanMode m) y n +
    (Real.log m + tameDifferent m) * normalizedRamanujanMode m n

/-- Finite tail partial sums converge to `-normalizedPrimeCorrection m y n` for `m, n ≥ 1`. -/
private theorem tendsto_tail_normalizedPrimeCorrection {m : ℕ} (hm : 0 < m)
    {n : ℕ} (hn : 0 < n) (y : ℕ) :
    Tendsto (fun T : ℕ =>
      -(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ)))
      atTop (𝓝 (normalizedPrimeCorrection m y n)) := by
  have hg : normalizedRamanujanMode m =
      fun j => ramanujanLagCoefficient m j / Real.sqrt (m.totient : ℝ) :=
    funext (normalizedRamanujanMode_eq_coefficient hm)
  have hid : normalizedPrimeCorrection m y n =
      ((∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) +
        (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n +
          ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) := by
    unfold normalizedPrimeCorrection
    rw [hg, poleProfileCorrection_div, poleProfileCorrection_eq_divisor_jumps]
    change ((_ + ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) + _) = _
    unfold ramanujanUpCorrectionTerm
    ring
  have hs := (hasSum_ramanujan_correction m hm n hn).tendsto_sum_nat
  have hshift := (tendsto_add_atTop_iff_nat 1).mpr hs
  have hlim := (hshift.const_sub (∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t)).div_const
    (Real.sqrt (m.totient : ℝ))
  have htarget :
      ((∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) -
        (-(Real.log m + tameDifferent m) * ramanujanLagCoefficient m n -
          ramanujanDownCorrection m n)) / Real.sqrt (m.totient : ℝ) =
      normalizedPrimeCorrection m y n := by
    rw [hid]
    ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop y] with T hT
  have hrng : range (T + 1) = insert 0 (Icc 1 y ∪ Ioc y T) := by
    ext t; simp only [mem_range, mem_insert, mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 y) (Ioc y T) := by
    rw [Finset.disjoint_left]; intro t ht1 ht2; simp only [mem_Icc, mem_Ioc] at ht1 ht2; omega
  have hnot0 : (0 : ℕ) ∉ Icc 1 y ∪ Ioc y T := by simp
  have hsum_split : (∑ t ∈ range (T + 1), ramanujanUpCorrectionTerm m n t) =
      (∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) +
        ∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t := by
    rw [hrng, sum_insert hnot0, sum_union hdisj]
    simp [ramanujanUpCorrectionTerm]
  rw [hsum_split, ← sum_div]
  ring

/-- On positive integers `n ≥ 1`, `normalizedPrimeCorrection m y` is `m`-periodic. -/
private theorem normalizedPrimeCorrection_periodic_pos {m : ℕ} (hm : 0 < m) (y : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    normalizedPrimeCorrection m y (n + m) = normalizedPrimeCorrection m y n := by
  have hper_lag : Function.Periodic (ramanujanLagCoefficient m) m := by
    intro x
    have hφ : Real.sqrt (m.totient : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm)).ne'
    have h1 := normalizedRamanujanMode_periodic hm x
    rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm] at h1
    exact (div_left_inj' hφ).mp h1
  have hterm : ∀ t : ℕ, ramanujanUpCorrectionTerm m (n + m) t = ramanujanUpCorrectionTerm m n t := by
    intro t
    unfold ramanujanUpCorrectionTerm
    have hmul : (n + m) * t = n * t + t * m := by ring
    rw [hmul, periodic_add_mul hper_lag t (n * t), hper_lag n]
  have h1 := tendsto_tail_normalizedPrimeCorrection hm (by omega : 0 < n + m) y
  have h2 := tendsto_tail_normalizedPrimeCorrection hm hn y
  simp_rw [hterm] at h1
  exact tendsto_nhds_unique h1 h2

/-- Modular multiplication fiber bound: for `0 < m` and any `t, z`, at most `gcd(m, t)`
residues `r ∈ range m` satisfy `(r * t) % m = z`. -/
private theorem card_filter_mul_mod_le_gcd {m : ℕ} (hm : 0 < m) (t z : ℕ) :
    ((range m).filter (fun r => (r * t) % m = z)).card ≤ Nat.gcd m t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [Nat.gcd_zero_right]
    exact (card_filter_le _ _).trans_eq (card_range m)
  let F := (range m).filter (fun r => (r * t) % m = z)
  by_cases hne : F.Nonempty
  · let r₀ := F.min' hne
    have hr₀_mem : r₀ ∈ F := Finset.min'_mem F hne
    have hr₀_mod : (r₀ * t) % m = z := (mem_filter.mp hr₀_mem).2
    let g := Nat.gcd m t
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left t hm
    let m' := m / g
    let t' := t / g
    have hm_eq : m' * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m t)
    have ht_eq : t' * g = t := Nat.div_mul_cancel (Nat.gcd_dvd_right m t)
    have hm'0 : 0 < m' := Nat.div_pos (Nat.gcd_le_left t hm) hg0
    have hcop : m'.Coprime t' := Nat.coprime_div_gcd_div_gcd hg0
    have hdvd_diff : ∀ r ∈ F, m' ∣ r - r₀ := by
      intro r hr
      have hle : r₀ ≤ r := Finset.min'_le F r hr
      have hr_mod : (r * t) % m = z := (mem_filter.mp hr).2
      have hdiv1 := Nat.div_add_mod (r * t) m
      have hdiv0 := Nat.div_add_mod (r₀ * t) m
      rw [hr_mod] at hdiv1
      rw [hr₀_mod] at hdiv0
      have hsub : (r - r₀) * t = m * (r * t / m - r₀ * t / m) := by
        rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
        have hle_mul : r₀ * t ≤ r * t := Nat.mul_le_mul_right t hle
        have hle_div : m * (r₀ * t / m) ≤ m * (r * t / m) :=
          Nat.mul_le_mul_left m (Nat.div_le_div_right hle_mul)
        omega
      have hmdvd : m ∣ (r - r₀) * t := ⟨r * t / m - r₀ * t / m, hsub⟩
      have hgdvd : m' * g ∣ ((r - r₀) * t') * g := by
        rw [hm_eq, Nat.mul_assoc, ht_eq]
        exact hmdvd
      exact hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_right hg0 hgdvd)
    refine (Finset.card_le_card_of_injOn (fun r => (r - r₀) / m') ?_ ?_).trans_eq (card_range g)
    · intro r hr
      have hlt : r - r₀ < m' * g := by
        have hrm : r < m := mem_range.mp (mem_filter.mp hr).1
        omega
      exact mem_range.mpr (Nat.div_lt_of_lt_mul hlt)
    · intro r₁ hr₁ r₂ hr₂ heq
      have hle₁ : r₀ ≤ r₁ := Finset.min'_le F r₁ hr₁
      have hle₂ : r₀ ≤ r₂ := Finset.min'_le F r₂ hr₂
      have hd₁ := Nat.div_mul_cancel (hdvd_diff r₁ hr₁)
      have hd₂ := Nat.div_mul_cancel (hdvd_diff r₂ hr₂)
      dsimp only at heq
      have hsub_eq : r₁ - r₀ = r₂ - r₀ := by rw [← hd₁, ← hd₂, heq]
      omega
  · change F.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, card_empty]
    exact Nat.zero_le _

/-- Period quadratic mass under lag dilation: `∑_{n=1}^m c̃_m(n * t)^2 ≤ gcd(m, t) * m`. -/
private theorem sum_Icc_normalizedRamanujanMode_mul_sq_le {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (∑ n ∈ Icc 1 m, normalizedRamanujanMode m (n * t) ^ 2) ≤ (Nat.gcd m t : ℝ) * m := by
  have hper_base := normalizedRamanujanMode_periodic hm
  have hper : Function.Periodic (fun n => normalizedRamanujanMode m (n * t) ^ 2) m := by
    intro n
    dsimp only
    rw [show (n + m) * t = n * t + t * m by ring, periodic_add_mul hper_base t (n * t)]
  have h0 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
  rw [h0, sum_Ioc_periodic_eq hm hper 0]
  have hmod_eq : ∀ r : ℕ, normalizedRamanujanMode m (r * t) =
      normalizedRamanujanMode m ((r * t) % m) := by
    intro r
    conv_lhs => rw [← Nat.mod_add_div (r * t) m, Nat.mul_comm m _,
      periodic_add_mul hper_base (r * t / m) (r * t % m)]
  have hmaps : ∀ r ∈ range m, (r * t) % m ∈ range m :=
    fun r _ => mem_range.mpr (Nat.mod_lt _ hm)
  calc
    (∑ r ∈ range m, normalizedRamanujanMode m (r * t) ^ 2) =
        ∑ r ∈ range m, normalizedRamanujanMode m ((r * t) % m) ^ 2 :=
      sum_congr rfl fun r _ => by rw [hmod_eq r]
    _ = ∑ z ∈ range m, ∑ r ∈ (range m).filter (fun r => (r * t) % m = z),
          normalizedRamanujanMode m ((r * t) % m) ^ 2 :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ z ∈ range m, (((range m).filter (fun r => (r * t) % m = z)).card : ℝ) *
          normalizedRamanujanMode m z ^ 2 := by
      refine sum_congr rfl fun z _ => ?_
      rw [sum_congr rfl (fun r hr => by rw [(mem_filter.mp hr).2]), sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ range m, (Nat.gcd m t : ℝ) * normalizedRamanujanMode m z ^ 2 := by
      refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact_mod_cast card_filter_mul_mod_le_gcd hm t z
    _ = (Nat.gcd m t : ℝ) * ∑ z ∈ range m, normalizedRamanujanMode m z ^ 2 := (mul_sum _ _ _).symm
    _ = (Nat.gcd m t : ℝ) * m := by
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hmean := (div_eq_iff hmR).mp (periodMean_normalizedRamanujanMode_sq hm)
      rw [hmean, one_mul]

/-- Prime-tower `gcd`-weighted Mangoldt sum bound:
`∑_{p ∈ m.primeFactors} ∑_{t ∈ (y, T]} localMangoldtMass p t * gcd(m, t) ≤ 2 log m`. -/
private theorem sum_primeFactors_localMangoldtMass_mul_gcd_le {m : ℕ} (hm : 0 < m) (y T : ℕ) :
    (∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
      2 * Real.log m := by
  have hfor_p : ∀ p ∈ m.primeFactors,
      (∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
        2 * (m.factorization p : ℝ) * Real.log p := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith only [hp2]
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith only [hp2])
    let a := m.factorization p
    have ha1 : 1 ≤ a :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (m.support_factorization ▸ hp_mem))
    have hndvd : ¬ p ^ (a + 1) ∣ m := Nat.pow_succ_factorization_not_dvd hm.ne' hp
    -- Nonzero summands in `Ioc y T` have the form `t = p ^ (k + 1)` with `k ∈ range T`.
    let S := (Ioc y T).filter (fun t => localMangoldtMass p t ≠ 0)
    have hrestrict : (∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) =
        ∑ t ∈ S, localMangoldtMass p t * (Nat.gcd m t : ℝ) := by
      symm
      refine sum_subset (filter_subset _ _) fun t _ htS => ?_
      have hz : localMangoldtMass p t = 0 := by
        by_contra hne
        exact htS (mem_filter.mpr ⟨‹_›, hne⟩)
      rw [hz, zero_mul]
    have hS_sub : S ⊆ (range T).image (fun k => p ^ (k + 1)) := by
      intro t ht
      obtain ⟨htI, hne⟩ := mem_filter.mp ht
      have hpdvd : p ∣ t := by
        unfold localMangoldtMass at hne
        by_contra hnd
        rw [if_neg hnd] at hne
        exact hne rfl
      have hΛne : Λ t ≠ 0 := by
        unfold localMangoldtMass at hne
        rw [if_pos hpdvd] at hne
        intro hz
        rw [hz, zero_div] at hne
        exact hne rfl
      obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛne)
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdvd)
      subst hpq
      refine mem_image.mpr ⟨j - 1, mem_range.mpr ?_, by congr 1; omega⟩
      have htT : p ^ j ≤ T := (mem_Ioc.mp htI).2
      have hj_lt : j ≤ p ^ j := (Nat.lt_pow_self hp.one_lt).le
      omega
    have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) :=
      fun k₁ k₂ h => Nat.succ.inj ((Nat.pow_right_injective hp.one_lt) h)
    have hpow_val : ∀ k : ℕ, localMangoldtMass p (p ^ (k + 1)) =
        Real.log p / (p : ℝ) ^ (k + 1) := by
      intro k
      rw [localMangoldtMass, if_pos (dvd_pow_self p (by omega)),
        vonMangoldt_prime_pow hp (by omega), Nat.cast_pow]
    -- Split `range T ⊆ range a ∪ image (a + ·) (range T)`.
    have hrng_sub : range T ⊆ range a ∪ (range T).image (fun j => a + j) := by
      intro k hk
      by_cases hka : k < a
      · exact mem_union_left _ (mem_range.mpr hka)
      · exact mem_union_right _ (mem_image.mpr ⟨k - a, mem_range.mpr (by have := mem_range.mp hk; omega),
          by omega⟩)
    have hlow : (∑ k ∈ range a, localMangoldtMass p (p ^ (k + 1)) *
        (Nat.gcd m (p ^ (k + 1)) : ℝ)) ≤ (a : ℝ) * Real.log p := by
      have hpt : ∀ k ∈ range a, localMangoldtMass p (p ^ (k + 1)) *
          (Nat.gcd m (p ^ (k + 1)) : ℝ) ≤ Real.log p := by
        intro k _
        rw [hpow_val k]
        have hgcd : (Nat.gcd m (p ^ (k + 1)) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
          exact_mod_cast Nat.gcd_le_right m (pow_pos hp.pos _)
        calc
          (Real.log p / (p : ℝ) ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) ≤
              (Real.log p / (p : ℝ) ^ (k + 1)) * (p : ℝ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_left hgcd (by positivity)
          _ = Real.log p := div_mul_cancel₀ _ (pow_pos hp0 _).ne'
      calc
        _ ≤ ∑ _k ∈ range a, Real.log p := sum_le_sum hpt
        _ = (a : ℝ) * Real.log p := by rw [sum_const, card_range, nsmul_eq_mul]
    have hhigh : (∑ k ∈ (range T).image (fun j => a + j),
        localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ)) ≤ Real.log p := by
      rw [sum_image (fun j₁ _ j₂ _ h => Nat.add_left_cancel h)]
      have hpt : ∀ j ∈ range T, localMangoldtMass p (p ^ (a + j + 1)) *
          (Nat.gcd m (p ^ (a + j + 1)) : ℝ) ≤ Real.log p / (p : ℝ) ^ (j + 1) := by
        intro j _
        rw [hpow_val (a + j)]
        obtain ⟨i, _, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right m (p ^ (a + j + 1)))
        have hi_le : i ≤ a := by
          by_contra hgt
          have hdvd_a1 : p ^ (a + 1) ∣ p ^ i := Nat.pow_dvd_pow p (by omega)
          have hdvd_m : p ^ i ∣ m := hi_eq ▸ Nat.gcd_dvd_left m _
          exact hndvd (hdvd_a1.trans hdvd_m)
        have hgcd : (Nat.gcd m (p ^ (a + j + 1)) : ℝ) ≤ (p : ℝ) ^ a := by
          rw [hi_eq, Nat.cast_pow]
          exact pow_le_pow_right₀ (by linarith only [hp2]) hi_le
        calc
          (Real.log p / (p : ℝ) ^ (a + j + 1)) * (Nat.gcd m (p ^ (a + j + 1)) : ℝ) ≤
              (Real.log p / (p : ℝ) ^ (a + j + 1)) * (p : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left hgcd (by positivity)
          _ = Real.log p / (p : ℝ) ^ (j + 1) := by
            rw [show a + j + 1 = a + (j + 1) by omega, pow_add]
            field_simp [(pow_pos hp0 a).ne', (pow_pos hp0 (j + 1)).ne']
      -- Finite geometric sum bound `∑_{j < T} log p / p^(j + 1) ≤ log p / (p - 1) ≤ log p`.
      have hgeom : ∀ J : ℕ, (∑ j ∈ range J, Real.log p / (p : ℝ) ^ (j + 1)) =
          Real.log p / ((p : ℝ) - 1) - (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ J := by
        intro J
        induction J with
        | zero => simp
        | succ J ih =>
          rw [Finset.sum_range_succ, ih, pow_succ]
          field_simp [hp0.ne', (show (p : ℝ) - 1 ≠ 0 by linarith only [hp2])]
          ring
      calc
        _ ≤ ∑ j ∈ range T, Real.log p / (p : ℝ) ^ (j + 1) := sum_le_sum hpt
        _ = Real.log p / ((p : ℝ) - 1) - (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ T := hgeom T
        _ ≤ Real.log p / ((p : ℝ) - 1) := sub_le_self _ (by positivity)
        _ ≤ Real.log p := div_le_self hlogp hp1
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    rw [hrestrict]
    calc
      (∑ t ∈ S, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
          ∑ t ∈ (range T).image (fun k => p ^ (k + 1)),
            localMangoldtMass p t * (Nat.gcd m t : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hS_sub fun t _ _ =>
          mul_nonneg (localMangoldtMass_nonneg p t) (Nat.cast_nonneg _)
      _ = ∑ k ∈ range T, localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) :=
        sum_image fun a _ b _ h => hinj h
      _ ≤ ∑ k ∈ range a ∪ (range T).image (fun j => a + j),
            localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hrng_sub fun k _ _ =>
          mul_nonneg (localMangoldtMass_nonneg p _) (Nat.cast_nonneg _)
      _ ≤ (∑ k ∈ range a, localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ)) +
          ∑ k ∈ (range T).image (fun j => a + j),
            localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) :=
        sum_union_le_of_nonneg fun k _ =>
          mul_nonneg (localMangoldtMass_nonneg p _) (Nat.cast_nonneg _)
      _ ≤ (a : ℝ) * Real.log p + Real.log p := add_le_add hlow hhigh
      _ ≤ 2 * (a : ℝ) * Real.log p := by nlinarith only [haR, hlogp]
  have hfact_log : (∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p) = Real.log m := by
    have hprod : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p))) = (m : ℝ) := by
      exact_mod_cast Nat.prod_factorization_pow_eq_self hm.ne'
    rw [← hprod, Real.log_prod (fun p hp =>
      pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
    exact sum_congr rfl fun p _ => (Real.log_pow _ _).symm
  calc
    (∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
        ∑ p ∈ m.primeFactors, 2 * (m.factorization p : ℝ) * Real.log p := sum_le_sum hfor_p
    _ = 2 * ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ = 2 * Real.log m := by rw [hfact_log]

/-- Complete-period `L²` bound on `normalizedPrimeCorrection m y`:
`∑_{n=1}^m normalizedPrimeCorrection m y n ^ 2 ≤ 16 * m * (log m)^2 / y`. -/
private theorem sum_Icc_normalizedPrimeCorrection_sq_le {m y : ℕ} (hm : 0 < m) (hy : 0 < y) :
    (∑ n ∈ Icc 1 m, normalizedPrimeCorrection m y n ^ 2) ≤
      16 * (m : ℝ) * (Real.log m) ^ 2 / (y : ℝ) := by
  let w : ℕ → ℝ := fun t => ∑ p ∈ m.primeFactors, localMangoldtMass p t
  have hw0 : ∀ t, 0 ≤ w t := fun t => sum_nonneg fun p _ => localMangoldtMass_nonneg p t
  -- Pointwise majorization of each upward jump term by `w t`.
  have hterm_le : ∀ n t : ℕ,
      |ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ)| ≤
        |normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n| * w t := by
    intro n t
    have heq : ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ) =
        (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) * Λ t / (t : ℝ) := by
      unfold ramanujanUpCorrectionTerm
      rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm]
      ring
    rw [heq]
    by_cases hΛ : Λ t = 0
    · rw [hΛ, mul_zero, zero_div, abs_zero]
      exact mul_nonneg (abs_nonneg _) (hw0 t)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    by_cases hpm : p ∣ m
    · have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩
      have hmass : Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ≤ w (p ^ k) := by
        dsimp only [w]
        have h := single_le_sum (f := fun q => localMangoldtMass q (p ^ k))
          (fun q _ => localMangoldtMass_nonneg q (p ^ k)) hmem
        rwa [localMangoldtMass, if_pos (dvd_pow_self p hk.ne')] at h
      rw [mul_div_assoc, abs_mul, abs_div,
        abs_of_nonneg (show 0 ≤ Λ (p ^ k) from vonMangoldt_nonneg),
        abs_of_nonneg (show 0 ≤ ((p ^ k : ℕ) : ℝ) from Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
    · have hmp : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
      have hdiff : normalizedRamanujanMode m (n * p ^ k) - normalizedRamanujanMode m n = 0 := by
        rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm,
          ramanujanCoefficient_mul_lag_of_coprime (hmp.pow_right k), sub_self]
      rw [hdiff, zero_mul, zero_div, abs_zero, zero_mul]
  -- Tail weight bound `∑_{t ∈ Ioc y T} w t ≤ 2 * log m / y`.
  have hw_tail : ∀ T : ℕ, (∑ t ∈ Ioc y T, w t) ≤ 2 * Real.log m / (y : ℝ) := by
    intro T
    have hp_tail : ∀ p ∈ m.primeFactors,
        (∑ t ∈ Ioc y T, localMangoldtMass p t) ≤ localMangoldtTail p y := by
      intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      by_cases hTy : T ≤ y
      · rw [Ioc_eq_empty (by omega), sum_empty]
        unfold localMangoldtTail
        exact sub_nonneg.mpr
          ((summable_localMangoldtMass hp).sum_le_tsum _ fun t _ => localMangoldtMass_nonneg p t)
      · have hdisj : Disjoint (range (y + 1)) (Ioc y T) := by
          rw [Finset.disjoint_left]; intro t ht1 ht2; simp only [mem_range, mem_Ioc] at ht1 ht2; omega
        have hunion : range (y + 1) ∪ Ioc y T = range (T + 1) := by
          ext t; simp only [mem_union, mem_range, mem_Ioc]; omega
        have hsum := (summable_localMangoldtMass hp).sum_le_tsum (range (T + 1))
          fun t _ => localMangoldtMass_nonneg p t
        rw [← hunion, sum_union hdisj] at hsum
        unfold localMangoldtTail
        linarith only [hsum]
    have hlog_sum : (∑ p ∈ m.primeFactors, Real.log p) ≤ Real.log m := by
      have hprimes : ∀ p ∈ m.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
      have hpos : 0 < ∏ p ∈ m.primeFactors, p := prod_pos fun p hp => (hprimes p hp).pos
      have hle : ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ≤ m := by
        exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
      rw [← Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero), ← Nat.cast_prod]
      exact Real.log_le_log (by exact_mod_cast hpos) hle
    dsimp only [w]
    rw [sum_comm]
    calc
      (∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T, localMangoldtMass p t) ≤
          ∑ p ∈ m.primeFactors, localMangoldtTail p y := sum_le_sum hp_tail
      _ ≤ ∑ p ∈ m.primeFactors, (2 * Real.log p / (y : ℝ)) :=
        sum_le_sum fun p hp => localMangoldtTail_le (Nat.prime_of_mem_primeFactors hp) hy
      _ = 2 * (∑ p ∈ m.primeFactors, Real.log p) / (y : ℝ) := by
        rw [← sum_div, ← mul_sum]
      _ ≤ 2 * Real.log m / (y : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sum zero_le_two)
          (Nat.cast_nonneg y)
  -- Finite partial-sum `L²` bound for every `T : ℕ`.
  have hT_bound : ∀ T : ℕ,
      (∑ n ∈ Icc 1 m,
        (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2) ≤
        16 * (m : ℝ) * (Real.log m) ^ 2 / (y : ℝ) := by
    intro T
    have hcs_n : ∀ n ∈ Icc 1 m,
        (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2 ≤
          (∑ t ∈ Ioc y T, w t) *
            ∑ t ∈ Ioc y T, w t *
              (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 := by
      intro n _
      rw [neg_sq]
      have habs : |∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ)| ≤
          ∑ t ∈ Ioc y T, Real.sqrt (w t) *
            (Real.sqrt (w t) * |normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n|) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
        refine (hterm_le n t).trans_eq ?_
        rw [← mul_assoc, Real.mul_self_sqrt (hw0 t), mul_comm]
      have hsq := mul_self_le_mul_self (abs_nonneg _) habs
      rw [← sq, sq_abs, ← sq] at hsq
      refine hsq.trans ?_
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Ioc y T) (fun t => Real.sqrt (w t))
        (fun t => Real.sqrt (w t) * |normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n|)
      refine hcs.trans_eq ?_
      congr 1
      · exact sum_congr rfl fun t _ => Real.sq_sqrt (hw0 t)
      · exact sum_congr rfl fun t _ => by rw [mul_pow, Real.sq_sqrt (hw0 t), sq_abs]
    have hdiff_sum : ∀ t ∈ Ioc y T,
        (∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2) ≤
          4 * (Nat.gcd m t : ℝ) * m := by
      intro t ht
      have ht0 : 0 < t := (Nat.zero_le y).trans_lt (mem_Ioc.mp ht).1
      have hgcd1 : (1 : ℝ) ≤ Nat.gcd m t := by exact_mod_cast Nat.gcd_pos_of_pos_left t hm
      have h2sq : ∀ n ∈ Icc 1 m,
          (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 ≤
            2 * normalizedRamanujanMode m (n * t) ^ 2 + 2 * normalizedRamanujanMode m n ^ 2 :=
        fun n _ => by
          nlinarith only [sq_nonneg (normalizedRamanujanMode m (n * t) + normalizedRamanujanMode m n)]
      have hIcc_base : (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2) = (m : ℝ) := by
        have h1 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
        rw [h1, sum_Ioc_normalizedRamanujanMode_sq hm 0]
      calc
        (∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2) ≤
            ∑ n ∈ Icc 1 m,
              (2 * normalizedRamanujanMode m (n * t) ^ 2 + 2 * normalizedRamanujanMode m n ^ 2) :=
          sum_le_sum h2sq
        _ = 2 * (∑ n ∈ Icc 1 m, normalizedRamanujanMode m (n * t) ^ 2) +
              2 * (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ 2 * ((Nat.gcd m t : ℝ) * m) + 2 * (m : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left (sum_Icc_normalizedRamanujanMode_mul_sq_le hm t) zero_le_two)
            (by rw [hIcc_base])
        _ ≤ 4 * (Nat.gcd m t : ℝ) * m := by nlinarith only [hgcd1, show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    have hsecond : (∑ t ∈ Ioc y T, w t *
        ∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2) ≤
          8 * (m : ℝ) * Real.log m := by
      calc
        _ ≤ ∑ t ∈ Ioc y T, w t * (4 * (Nat.gcd m t : ℝ) * m) :=
          sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hdiff_sum t ht) (hw0 t)
        _ = 4 * (m : ℝ) * ∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T,
              localMangoldtMass p t * (Nat.gcd m t : ℝ) := by
          dsimp only [w]
          simp_rw [sum_mul]
          rw [sum_comm, mul_sum]
          exact sum_congr rfl fun p _ => by rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
        _ ≤ 4 * (m : ℝ) * (2 * Real.log m) :=
          mul_le_mul_of_nonneg_left (sum_primeFactors_localMangoldtMass_mul_gcd_le hm y T) (by positivity)
        _ = 8 * (m : ℝ) * Real.log m := by ring
    calc
      (∑ n ∈ Icc 1 m,
          (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2) ≤
          ∑ n ∈ Icc 1 m, (∑ t ∈ Ioc y T, w t) *
            ∑ t ∈ Ioc y T, w t *
              (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 :=
        sum_le_sum hcs_n
      _ = (∑ t ∈ Ioc y T, w t) *
            ∑ t ∈ Ioc y T, w t *
              ∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 := by
        rw [← mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact sum_congr rfl fun t _ => (mul_sum _ _ _).symm
      _ ≤ (2 * Real.log m / (y : ℝ)) * (8 * (m : ℝ) * Real.log m) :=
        mul_le_mul (hw_tail T) hsecond
          (sum_nonneg fun t _ => mul_nonneg (hw0 t) (sum_nonneg fun _ _ => sq_nonneg _))
          (by have := Real.log_natCast_nonneg m; positivity)
      _ = 16 * (m : ℝ) * (Real.log m) ^ 2 / (y : ℝ) := by ring
  -- Pass to `T → ∞`.
  have hlim_sum : Tendsto (fun T : ℕ =>
      ∑ n ∈ Icc 1 m,
        (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2)
      atTop (𝓝 (∑ n ∈ Icc 1 m, normalizedPrimeCorrection m y n ^ 2)) :=
    tendsto_finsetSum _ fun n hn =>
      (tendsto_tail_normalizedPrimeCorrection hm (mem_Icc.mp hn).1 y).pow 2
  exact le_of_tendsto' hlim_sum hT_bound

/-- Individual conductor prime-tower tail bound: for `1 ≤ m` with `m * m ≤ N` and `1 ≤ log N`,
`∑_{n=1}^N normalizedPrimeCorrection m (N / n) n ^ 2 / n ≤ 192 * (log N)^2`. -/
private theorem sum_normalizedPrimeCorrection_sq_div_le {m N : ℕ}
    (hm : 1 ≤ m) (hmN_sq : m * m ≤ N) (hlogN : 1 ≤ Real.log N) :
    (∑ n ∈ Icc 1 N, normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
      192 * (Real.log N) ^ 2 := by
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hmN : m ≤ N := (Nat.le_mul_self m).trans hmN_sq
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  rcases eq_or_lt_of_le hm with rfl | hm2
  · -- `m = 1`: `log 1 = 0`, so every correction term is identically zero.
    have hzero : ∀ n ∈ Icc 1 N, normalizedPrimeCorrection 1 (N / n) n ^ 2 / (n : ℝ) = 0 := by
      intro n hn
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hy : 0 < N / n := Nat.div_pos (mem_Icc.mp hn).2 hn0
      have hb := abs_normalizedRamanujan_correction_le one_pos hn0 hy
      simp only [Nat.cast_one, Real.log_one, mul_zero, zero_div] at hb
      have hz : normalizedPrimeCorrection 1 (N / n) n = 0 := by
        unfold normalizedPrimeCorrection
        rw [Nat.cast_one, Real.log_one]
        exact abs_nonpos_iff.mp hb
      rw [hz, zero_pow (by decide), zero_div]
    rw [sum_eq_zero hzero]
    positivity
  · -- `m ≥ 2`: split `Icc 1 N = Icc 1 (N / m) ∪ Ioc (N / m) N`.
    have hNm_le : N / m ≤ N := Nat.div_le_self N m
    have hunion : Icc 1 N = Icc 1 (N / m) ∪ Ioc (N / m) N := by
      have := Nat.zero_le (N / m)
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 (N / m)) (Ioc (N / m) N) := by
      rw [Finset.disjoint_left]; intro n hn1 hn2; simp only [mem_Icc, mem_Ioc] at hn1 hn2; omega
    have hlogm_le : Real.log m ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN)
    have hlogm_sq : (Real.log m) ^ 2 ≤ (Real.log N) ^ 2 :=
      pow_le_pow_left₀ (Real.log_natCast_nonneg m) hlogm_le 2
    -- Range 1: `n ∈ Icc 1 (N / m)`.
    have hpart1 : (∑ n ∈ Icc 1 (N / m),
        normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤ 64 * (Real.log N) ^ 2 := by
      have hpt : ∀ n ∈ Icc 1 (N / m),
          normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ) ≤ 64 * (Real.log m) ^ 2 / N := by
        intro n hn
        obtain ⟨hn1, hnNm⟩ := mem_Icc.mp hn
        have hnN : n ≤ N := hnNm.trans hNm_le
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have hy : 1 ≤ N / n := Nat.div_pos hnN hn1
        have hyR : (0 : ℝ) < (N / n : ℕ) := by exact_mod_cast hy
        have hb := abs_normalizedRamanujan_correction_le hm hn1 hy
        have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
        rw [← sq, sq_abs, ← sq, div_pow, mul_pow, mul_pow,
          Real.sq_sqrt (Nat.cast_nonneg m.totient)] at hbsq
        have hφ_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
        have hNy : (N : ℝ) ≤ 2 * ((N / n : ℕ) : ℝ) * n := by
          have hmod := Nat.mod_lt N hn1
          have hid := Nat.mod_add_div N n
          have hlt : N < (N / n + 1) * n := by nlinarith only [hmod, hid]
          have hle : N ≤ 2 * (N / n) * n := by nlinarith only [hlt, hy]
          exact_mod_cast hle
        have hinv_y2 : 1 / ((N / n : ℕ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hyR) (sq_pos_of_pos hNR)]
          have hsq := pow_le_pow_left₀ hNR.le hNy 2
          nlinarith only [hsq]
        have hmnN : (m : ℝ) * n ≤ N := by
          have hnat : n * m ≤ N := (Nat.le_div_iff_mul_le hm).mp hnNm
          exact_mod_cast (Nat.mul_comm m n ▸ hnat)
        calc
          normalizedPrimeCorrection m (N / n) n ^ 2 / n ≤
              (16 * (m.totient : ℝ) * (Real.log m) ^ 2 / ((N / n : ℕ) : ℝ) ^ 2) / n :=
            div_le_div_of_nonneg_right (hbsq.trans_eq (by ring)) hnR.le
          _ ≤ (16 * (m : ℝ) * (Real.log m) ^ 2 * (1 / ((N / n : ℕ) : ℝ) ^ 2)) / n := by
            refine div_le_div_of_nonneg_right ?_ hnR.le
            rw [div_eq_mul_inv, ← one_div]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ_le (by norm_num))
                (sq_nonneg _)) (by positivity)
          _ ≤ (16 * (m : ℝ) * (Real.log m) ^ 2 * (4 * (n : ℝ) ^ 2 / (N : ℝ) ^ 2)) / n :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hinv_y2 (by positivity)) hnR.le
          _ = 64 * ((m : ℝ) * n) * (Real.log m) ^ 2 / (N : ℝ) ^ 2 := by
            field_simp [hnR.ne', hNR.ne']; ring
          _ ≤ 64 * (N : ℝ) * (Real.log m) ^ 2 / (N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmnN (by norm_num))
                (sq_nonneg _)) (sq_nonneg _)
          _ = 64 * (Real.log m) ^ 2 / N := by field_simp [hNR.ne']
      have hcard_le : ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast hNm_le
      calc
        (∑ n ∈ Icc 1 (N / m), normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
            ∑ _n ∈ Icc 1 (N / m), 64 * (Real.log m) ^ 2 / N := sum_le_sum hpt
        _ = ((N / m : ℕ) : ℝ) * (64 * (Real.log m) ^ 2 / N) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ (N : ℝ) * (64 * (Real.log m) ^ 2 / N) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = 64 * (Real.log m) ^ 2 := mul_div_cancel₀ _ hNR.ne'
        _ ≤ 64 * (Real.log N) ^ 2 := mul_le_mul_of_nonneg_left hlogm_sq (by norm_num)
    -- Range 2: `n ∈ Ioc (N / m) N`, partitioned by `y = N / n ∈ Icc 1 (m - 1)`.
    have hcover_y : Ioc (N / m) N ⊆
        (Icc 1 (m - 1)).biUnion (fun y => Ioc (N / (y + 1)) (N / y)) := by
      intro n hn
      obtain ⟨hn_gt, hn_le⟩ := mem_Ioc.mp hn
      have hn0 : 0 < n := (Nat.zero_le _).trans_lt hn_gt
      let y := N / n
      have hy1 : 1 ≤ y := Nat.div_pos hn_le hn0
      have hym : y ≤ m - 1 := by
        have hlt : y < m := by
          by_contra hge
          have hnm : m * n ≤ N := (Nat.le_div_iff_mul_le hn0).mp (le_of_not_gt hge)
          have hnle : n ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (Nat.mul_comm m n ▸ hnm)
          omega
        omega
      have hn_hi : n ≤ N / y := (Nat.le_div_iff_mul_le hy1).mpr (Nat.mul_comm n y ▸ Nat.div_mul_le_self N n)
      have hn_lo : N / (y + 1) < n := by
        by_contra hle
        have hmul : n * (y + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp (le_of_not_gt hle)
        have hy_ge : y + 1 ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr (Nat.mul_comm n (y + 1) ▸ hmul)
        omega
      exact mem_biUnion.mpr ⟨y, mem_Icc.mpr ⟨hy1, hym⟩, mem_Ioc.mpr ⟨hn_lo, hn_hi⟩⟩
    have hdisj_y : Set.PairwiseDisjoint (↑(Icc 1 (m - 1)) : Set ℕ)
        (fun y => Ioc (N / (y + 1)) (N / y)) := by
      intro y₁ hy₁ y₂ hy₂ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro n hn₁ hn₂
      obtain ⟨h1a, h1b⟩ := mem_Ioc.mp hn₁
      obtain ⟨h2a, h2b⟩ := mem_Ioc.mp hn₂
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : N / y₂ ≤ N / (y₁ + 1) := Nat.div_le_div_left (by omega) (by omega)
        omega
      · have hle : N / y₁ ≤ N / (y₂ + 1) := Nat.div_le_div_left (by omega) (by omega)
        omega
    have hy_eq : ∀ y ∈ Icc 1 (m - 1), ∀ n ∈ Ioc (N / (y + 1)) (N / y), N / n = y := by
      intro y hyI n hn
      obtain ⟨hy1, _⟩ := mem_Icc.mp hyI
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
      have hn0 : 0 < n := (Nat.zero_le _).trans_lt hn_lo
      have hge : y ≤ N / n :=
        (Nat.le_div_iff_mul_le hn0).mpr (Nat.mul_comm y n ▸ (Nat.le_div_iff_mul_le hy1).mp hn_hi)
      have hlt : N / n < y + 1 := by
        by_contra hge1
        have hmul : (y + 1) * n ≤ N := (Nat.le_div_iff_mul_le hn0).mp (le_of_not_gt hge1)
        have hnle : n ≤ N / (y + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (Nat.mul_comm (y + 1) n ▸ hmul)
        omega
      omega
    have hfor_y : ∀ y ∈ Icc 1 (m - 1),
        (∑ n ∈ Ioc (N / (y + 1)) (N / y),
          normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
          64 * (Real.log m) ^ 2 *
            ((((Ioc (N / (y + 1)) (N / y)).card : ℝ) + m) / N) := by
      intro y hyI
      obtain ⟨hy1, hym⟩ := mem_Icc.mp hyI
      have hyR : (0 : ℝ) < y := by exact_mod_cast hy1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      let I_y := Ioc (N / (y + 1)) (N / y)
      -- Every `n ∈ I_y` satisfies `1 / n ≤ 4 * y / N`.
      have hinv_n : ∀ n ∈ I_y, 1 / (n : ℝ) ≤ 4 * (y : ℝ) / N := by
        intro n hn
        have hn_lo : N / (y + 1) < n := (mem_Ioc.mp hn).1
        have hn0 : 0 < n := (Nat.zero_le _).trans_lt hn_lo
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
        have hdiv : N < (N / (y + 1) + 1) * (y + 1) := by
          have hmod := Nat.mod_lt N (by omega : 0 < y + 1)
          have hid := Nat.mod_add_div N (y + 1)
          nlinarith only [hmod, hid]
        have hle_n : N ≤ n * (y + 1) := by
          have : N / (y + 1) + 1 ≤ n := hn_lo
          have hmul := Nat.mul_le_mul_right (y + 1) this
          omega
        have hle_4 : N ≤ 4 * y * n := by
          have hy4 : y + 1 ≤ 4 * y := by omega
          calc
            N ≤ n * (y + 1) := hle_n
            _ ≤ n * (4 * y) := Nat.mul_le_mul_left n hy4
            _ = 4 * y * n := by ring
        rw [div_le_div_iff₀ hnR hNR, one_mul]
        exact_mod_cast hle_4
      -- Periodicity bound on `∑_{n ∈ I_y} normalizedPrimeCorrection m y n ^ 2`.
      have hper_bound : (∑ n ∈ I_y, normalizedPrimeCorrection m y n ^ 2) ≤
          ((I_y.card : ℝ) / m + 1) * (16 * (m : ℝ) * (Real.log m) ^ 2 / y) := by
        have h1 := sum_Ioc_le_mul_sum_Icc_of_periodic_pos
          (f := fun n => normalizedPrimeCorrection m y n ^ 2) hm (fun _ _ => sq_nonneg _)
          (fun n hn => by rw [normalizedPrimeCorrection_periodic_pos hm y hn])
          (N / (y + 1)) (N / y)
        have hcard_eq : N / y - N / (y + 1) = I_y.card := (Nat.card_Ioc _ _).symm
        rw [hcard_eq] at h1
        have hdiv_le : (((I_y.card / m + 1 : ℕ) : ℝ)) ≤ (I_y.card : ℝ) / m + 1 := by
          push_cast
          have hmul : ((I_y.card / m : ℕ) : ℝ) * m ≤ I_y.card := by
            exact_mod_cast Nat.div_mul_le_self I_y.card m
          linarith [(le_div_iff₀ hmR).mpr hmul]
        exact h1.trans (mul_le_mul hdiv_le (sum_Icc_normalizedPrimeCorrection_sq_le hm hy1)
          (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
      calc
        (∑ n ∈ I_y, normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) =
            ∑ n ∈ I_y, normalizedPrimeCorrection m y n ^ 2 * (1 / (n : ℝ)) :=
          sum_congr rfl fun n hn => by rw [hy_eq y hyI n hn, div_eq_mul_one_div]
        _ ≤ ∑ n ∈ I_y, normalizedPrimeCorrection m y n ^ 2 * (4 * (y : ℝ) / N) :=
          sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hinv_n n hn) (sq_nonneg _)
        _ = (4 * (y : ℝ) / N) * ∑ n ∈ I_y, normalizedPrimeCorrection m y n ^ 2 := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
        _ ≤ (4 * (y : ℝ) / N) *
              (((I_y.card : ℝ) / m + 1) * (16 * (m : ℝ) * (Real.log m) ^ 2 / y)) :=
          mul_le_mul_of_nonneg_left hper_bound (by positivity)
        _ = 64 * (Real.log m) ^ 2 * (((I_y.card : ℝ) + m) / N) := by
          field_simp [hyR.ne', hmR.ne', hNR.ne']; ring
    -- Sum `hfor_y` over `y ∈ Icc 1 (m - 1)`.
    have hIy_sub : (Icc 1 (m - 1)).biUnion (fun y => Ioc (N / (y + 1)) (N / y)) ⊆ Icc 1 N := by
      intro n hn
      obtain ⟨y, hyI, hny⟩ := mem_biUnion.mp hn
      obtain ⟨hy1, _⟩ := mem_Icc.mp hyI
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hny
      have := Nat.zero_le (N / (y + 1))
      exact mem_Icc.mpr ⟨by omega, hn_hi.trans (Nat.div_le_self N y)⟩
    have hsum_cards : (∑ y ∈ Icc 1 (m - 1), ((Ioc (N / (y + 1)) (N / y)).card : ℝ)) ≤ N := by
      have hnat : (∑ y ∈ Icc 1 (m - 1), (Ioc (N / (y + 1)) (N / y)).card) ≤ N := by
        rw [← card_biUnion hdisj_y]
        exact (card_le_card hIy_sub).trans_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel])
      exact_mod_cast hnat
    have hsum_m : (∑ _y ∈ Icc 1 (m - 1), (m : ℝ)) ≤ N := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      have hnat : (m - 1) * m ≤ N := (Nat.mul_le_mul_right m (Nat.sub_le m 1)).trans hmN_sq
      exact_mod_cast hnat
    have hpart2 : (∑ n ∈ Ioc (N / m) N,
        normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤ 128 * (Real.log N) ^ 2 := by
      calc
        (∑ n ∈ Ioc (N / m) N, normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
            ∑ n ∈ (Icc 1 (m - 1)).biUnion (fun y => Ioc (N / (y + 1)) (N / y)),
              normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hcover_y fun _ _ _ => by positivity
        _ = ∑ y ∈ Icc 1 (m - 1), ∑ n ∈ Ioc (N / (y + 1)) (N / y),
              normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ) :=
          sum_biUnion hdisj_y
        _ ≤ ∑ y ∈ Icc 1 (m - 1), 64 * (Real.log m) ^ 2 *
              ((((Ioc (N / (y + 1)) (N / y)).card : ℝ) + m) / N) :=
          sum_le_sum hfor_y
        _ = (64 * (Real.log m) ^ 2 / N) *
              ((∑ y ∈ Icc 1 (m - 1), ((Ioc (N / (y + 1)) (N / y)).card : ℝ)) +
                ∑ _y ∈ Icc 1 (m - 1), (m : ℝ)) := by
          rw [← sum_add_distrib, mul_sum]
          exact sum_congr rfl fun _ _ => by ring
        _ ≤ (64 * (Real.log m) ^ 2 / N) * ((N : ℝ) + N) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum_cards hsum_m) (by positivity)
        _ = 128 * (Real.log m) ^ 2 := by field_simp [hNR.ne']; ring
        _ ≤ 128 * (Real.log N) ^ 2 := mul_le_mul_of_nonneg_left hlogm_sq (by norm_num)
    rw [hunion, sum_union hdisj]
    linarith only [hpart1, hpart2]

/-! ## Section 4: Main Bombieri–Vinogradov theorem for `fullPrimeMatrix` -/

/-- Unconditional Bombieri–Vinogradov level of distribution (`M * M ≤ N`, covering every
exponent `0 < θ < 1 / 2`) for the literal finite prime matrix `fullPrimeMatrix N`:
`∑_{m=1}^M ‖P_N v_m - (log N - E_arith(m)) v_m‖² ≤ C_p M log N`. -/
theorem exists_fullPrimeMatrix_levelOfDistribution :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 1 ≤ Real.log N →
      (∑ m ∈ Icc 1 M,
        ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
        C_p * M * Real.log N := by
  obtain ⟨C₁, hC₁, hMertSum⟩ := sum_mertens_levelOfDistribution_le
  refine ⟨2 * C₁ + 384, by positivity, ?_⟩
  intro M N hM hMN hlogN
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  -- Express each normalized Euclidean residual via `ramanujanPrimeResidual`.
  have hnorm_eq : ∀ m ∈ Icc 1 M,
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 =
        (∑ n ∈ Icc 1 N, ramanujanPrimeResidual m N n ^ 2) / Real.log N := by
    intro m _
    simp only [normalizedRamanujanHorizonVector, map_smul]
    rw [smul_comm (Real.log N - ramanujanAdjunctionEnergy m) (Real.sqrt (Real.log N))⁻¹,
      ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hLN0.le, ramanujanHorizonVector_residual_norm_sq, div_eq_inv_mul]
    rfl
  -- Pointwise split of `ramanujanPrimeResidual m N n ^ 2` into Mertens and prime-tower tail.
  have hres_split : ∀ m ∈ Icc 1 M, ∀ n ∈ Icc 1 N,
      ramanujanPrimeResidual m N n ^ 2 ≤
        2 * (primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / (n : ℝ)) +
          2 * (normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) := by
    intro m _ n hn
    obtain ⟨hn0, hnN⟩ := mem_Icc.mp hn
    let e : ℕ → ℝ := fun y => mertensSum y - Real.log y + Real.eulerMascheroniConstant
    let r : ℝ := Real.log N - Real.log ((N / n : ℕ) : ℝ) - Real.log n
    have hr : 0 ≤ r ∧ r ≤ 1 / ((N / n : ℕ) : ℝ) := roundoff_le hn0 hnN
    have hid : ramanujanPrimeResidual m N n =
        ((e (N / n) - r) * normalizedRamanujanMode m n +
          normalizedPrimeCorrection m (N / n) n) * poleVector n := by
      rw [ramanujanPrimeResidual]
      simp only [ramanujanPoleProfile_eq_mul_poleVector]
      rw [sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m) hn0 hnN]
      dsimp only [e, r, ramanujanAdjunctionEnergy, normalizedPrimeCorrection]
      ring
    have her : |e (N / n) - r| ≤ primeMertensRemainderProfile (N / n) := by
      unfold primeMertensRemainderProfile
      calc
        |e (N / n) - r| ≤ |e (N / n)| + |r| := abs_sub _ _
        _ ≤ |e (N / n)| + 1 / ((N / n : ℕ) : ℝ) := by
          rw [abs_of_nonneg hr.1]; exact add_le_add le_rfl hr.2
    have her_sq : (e (N / n) - r) ^ 2 ≤ primeMertensRemainderProfile (N / n) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg _) her
      simpa only [← sq, sq_abs] using h
    have hpv_sq : poleVector n ^ 2 = 1 / (n : ℝ) := by
      unfold poleVector
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hid, mul_pow, hpv_sq]
    have h2sq : ((e (N / n) - r) * normalizedRamanujanMode m n +
        normalizedPrimeCorrection m (N / n) n) ^ 2 ≤
        2 * ((e (N / n) - r) ^ 2 * normalizedRamanujanMode m n ^ 2) +
          2 * normalizedPrimeCorrection m (N / n) n ^ 2 := by
      nlinarith only [sq_nonneg ((e (N / n) - r) * normalizedRamanujanMode m n -
        normalizedPrimeCorrection m (N / n) n)]
    calc
      ((e (N / n) - r) * normalizedRamanujanMode m n +
          normalizedPrimeCorrection m (N / n) n) ^ 2 * (1 / (n : ℝ)) ≤
          (2 * ((e (N / n) - r) ^ 2 * normalizedRamanujanMode m n ^ 2) +
            2 * normalizedPrimeCorrection m (N / n) n ^ 2) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right h2sq (by positivity)
      _ ≤ (2 * (primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2) +
            2 * normalizedPrimeCorrection m (N / n) n ^ 2) * (1 / (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right her_sq (sq_nonneg _)) zero_le_two
      _ = _ := by ring
  -- Sum over `n` and `m`, then divide by `log N`.
  have htail_sum : (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
      normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤ 192 * M * (Real.log N) ^ 2 := by
    have hpt : ∀ m ∈ Icc 1 M, (∑ n ∈ Icc 1 N,
        normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤ 192 * (Real.log N) ^ 2 := by
      intro m hmI
      obtain ⟨hm1, hmM⟩ := mem_Icc.mp hmI
      exact sum_normalizedPrimeCorrection_sq_div_le hm1 ((Nat.mul_le_mul hmM hmM).trans hMN) hlogN
    calc
      _ ≤ ∑ _m ∈ Icc 1 M, 192 * (Real.log N) ^ 2 := sum_le_sum hpt
      _ = 192 * M * (Real.log N) ^ 2 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  have hraw_total : (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, ramanujanPrimeResidual m N n ^ 2) ≤
      (2 * C₁ + 384) * M * (Real.log N) ^ 2 := by
    calc
      (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N, ramanujanPrimeResidual m N n ^ 2) ≤
          ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
            (2 * (primeMertensRemainderProfile (N / n) ^ 2 *
                normalizedRamanujanMode m n ^ 2 / (n : ℝ)) +
              2 * (normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ))) :=
        sum_le_sum fun m hm => sum_le_sum (hres_split m hm)
      _ = 2 * (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
            primeMertensRemainderProfile (N / n) ^ 2 * normalizedRamanujanMode m n ^ 2 / (n : ℝ)) +
          2 * (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
            normalizedPrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) := by
        simp_rw [sum_add_distrib, ← mul_sum]
      _ ≤ 2 * (C₁ * M * (Real.log N) ^ 2) + 2 * (192 * M * (Real.log N) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hMertSum M N hM hMN hlogN) zero_le_two)
          (mul_le_mul_of_nonneg_left htail_sum zero_le_two)
      _ = (2 * C₁ + 384) * M * (Real.log N) ^ 2 := by ring
  rw [sum_congr rfl hnorm_eq, ← sum_div]
  exact (div_le_div_of_nonneg_right hraw_total hLN0.le).trans_eq
    (by field_simp [hLN0.ne'])

#print axioms exists_fullPrimeMatrix_levelOfDistribution

end GaloisForLFunctions.CompletedArithmeticForms
