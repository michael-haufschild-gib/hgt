import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of a Dirichlet series

For `f : ℕ → ℂ` with `f 0 = f 1 = 0` the Dirichlet-convolution powers `f^{⋆k}` vanish below
`2^k`.  So `exp⋆ f = Σ_k f^{⋆k}/k!` is a finite sum at each `n`.

**Theorem** (`LSeries_dirichletExp`).  If `Σ_n |f(n)| n^{-σ} < ∞` at `σ = Re s`, then `exp⋆ f` is
absolutely summable at `s` and `L(exp⋆ f, s) = exp L(f, s)`.

The proof bounds `Σ_n |f^{⋆k}(n)| n^{-σ}` by `(Σ_n |f(n)| n^{-σ})^k`, so the double series
`Σ_{k,n} f^{⋆k}(n) n^{-s}/k!` converges absolutely and may be summed in either order.
-/

open LSeries Complex Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Dirichlet-convolution powers `f^{⋆k}`, with `f^{⋆0}` the Dirichlet unit. -/
def convPow {R : Type*} [Semiring R] (f : ℕ → R) : ℕ → ℕ → R
  | 0 => fun n => if n = 1 then 1 else 0
  | k + 1 => LSeries.convolution f (convPow f k)

/-- The Dirichlet exponential `exp⋆ f = Σ_{k ≤ n} f^{⋆k}(n)/k!`. -/
def dirichletExp (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), convPow f k n / (k.factorial : ℂ)

theorem convPow_zero_apply {R : Type*} [Semiring R] (f : ℕ → R) (n : ℕ) :
    convPow f 0 n = if n = 1 then 1 else 0 := rfl

theorem convPow_succ {R : Type*} [Semiring R] (f : ℕ → R) (k : ℕ) :
    convPow f (k + 1) = LSeries.convolution f (convPow f k) := rfl

/-- `f^{⋆k}` vanishes below `2^k` when `f 0 = f 1 = 0`. -/
theorem convPow_eq_zero_of_lt {R : Type*} [Semiring R] {f : ℕ → R} (h0 : f 0 = 0)
    (h1 : f 1 = 0) : ∀ (k n : ℕ), n < 2 ^ k → convPow f k n = 0 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have : n = 0 := by simpa using hn
    simp [convPow_zero_apply, this]
  | succ k ih =>
    intro n hn
    rw [convPow_succ, LSeries.convolution_def]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨hpn, hn0⟩ := hp
    rcases Nat.lt_or_ge p.1 2 with h | h
    · interval_cases hp1 : p.1
      · simp [h0]
      · simp [h1]
    · have hq : p.2 < 2 ^ k := by
        by_contra hq
        have hq' : 2 ^ k ≤ p.2 := not_lt.mp hq
        have : 2 * 2 ^ k ≤ p.1 * p.2 := Nat.mul_le_mul h hq'
        rw [hpn, pow_succ] at *
        omega
      simp [ih p.2 hq]

theorem convPow_eq_zero_of_le {R : Type*} [Semiring R] {f : ℕ → R} (h0 : f 0 = 0)
    (h1 : f 1 = 0) {k n : ℕ} (hk : n < k) : convPow f k n = 0 :=
  convPow_eq_zero_of_lt h0 h1 k n
    (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hk.le))

theorem convPow_ofReal (u : ℕ → ℝ) (k n : ℕ) :
    ((convPow u k n : ℝ) : ℂ) = convPow (fun m => (u m : ℂ)) k n := by
  induction k generalizing n with
  | zero => simp [convPow_zero_apply]; split_ifs <;> simp
  | succ k ih =>
    rw [convPow_succ, convPow_succ, LSeries.convolution_def, LSeries.convolution_def]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by rw [ih]

theorem convPow_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) (k n : ℕ) : 0 ≤ convPow u k n := by
  induction k generalizing n with
  | zero => rw [convPow_zero_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [convPow_succ, LSeries.convolution_def]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hu _) (ih _)

/-- The terms of the Dirichlet unit: `1` at `n = 1`, `0` elsewhere. -/
theorem term_convPow_zero (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (convPow f 0) s n = if n = 1 then 1 else 0 := by
  rw [term_def, convPow_zero_apply]
  by_cases h : n = 1
  · subst h; simp
  · by_cases h0 : n = 0
    · subst h0; simp
    · simp [h, h0]

theorem lseriesSummable_convPow_zero' (f : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (convPow f 0) s := by
  unfold LSeriesSummable
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  rw [term_convPow_zero]
  simp only [Finset.mem_singleton] at hn
  simp [hn]

theorem LSeries_convPow_zero (f : ℕ → ℂ) (s : ℂ) : LSeries (convPow f 0) s = 1 := by
  unfold LSeries
  rw [tsum_eq_single 1 fun n hn => by rw [term_convPow_zero]; simp [hn]]
  rw [term_convPow_zero]; simp

/-- **Powers.**  `f^{⋆k}` is absolutely summable at `s` and `L(f^{⋆k}, s) = L(f, s)^k`. -/
theorem lseriesSummable_convPow {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (k : ℕ) :
    LSeriesSummable (convPow f k) s ∧ LSeries (convPow f k) s = LSeries f s ^ k := by
  induction k with
  | zero => exact ⟨lseriesSummable_convPow_zero' f s, by rw [LSeries_convPow_zero, pow_zero]⟩
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [convPow_succ]; exact hf.convolution ih.1
    · rw [convPow_succ, LSeries_convolution' hf ih.1, ih.2, pow_succ]; ring

/-- The terms of `f^{⋆k}` are dominated by the convolution powers of the term norms of `f`. -/
theorem norm_term_convPow_le (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    ‖term (convPow f k) s n‖ ≤ convPow (fun m => ‖term f s m‖) k n := by
  induction k generalizing n with
  | zero =>
    rw [term_convPow_zero, convPow_zero_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [convPow_succ, term_convolution, convPow_succ, LSeries.convolution_def]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ih p.2) (norm_nonneg _)

/-- **Norm bound.**  `Σ_n |f^{⋆k}(n)| n^{-σ} ≤ (Σ_n |f(n)| n^{-σ})^k`. -/
theorem summable_norm_term_convPow {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (k : ℕ) :
    Summable (fun n => ‖term (convPow f k) s n‖) ∧
      ∑' n, ‖term (convPow f k) s n‖ ≤ (∑' n, ‖term f s n‖) ^ k := by
  set u : ℕ → ℝ := fun m => ‖term f s m‖ with hu
  have hu0 : 0 ≤ u := fun m => norm_nonneg _
  have hus : Summable u := hf.norm
  -- the complex lift of `u` is summable at `0`
  set U : ℕ → ℂ := fun m => (u m : ℂ) with hU
  have hterm : ∀ m, term U 0 m = U m := by
    intro m
    rw [term_def]
    split_ifs with h
    · simp [hU, hu, h, term_def]
    · simp
  have hUs : LSeriesSummable U 0 := by
    unfold LSeriesSummable
    rw [funext hterm]
    exact (Complex.summable_ofReal.mpr hus)
  obtain ⟨hPs, hPv⟩ := lseriesSummable_convPow hUs k
  have hconv : ∀ m, term (convPow U k) 0 m = ((convPow u k m : ℝ) : ℂ) := by
    intro m
    rw [term_def, convPow_ofReal]
    split_ifs with h
    · subst h
      rw [← convPow_ofReal]
      have : convPow u k 0 = 0 := by
        cases k with
        | zero => simp [convPow_zero_apply]
        | succ k => rw [convPow_succ]; exact LSeries.convolution_map_zero _ _
      simp [this]
    · simp only [Complex.cpow_zero, div_one]
      rfl
  have hsumR : Summable (fun m => convPow u k m) := by
    have h := hPs
    unfold LSeriesSummable at h
    rw [funext hconv] at h
    exact Complex.summable_ofReal.mp h
  have htsumR : ∑' m, convPow u k m = (∑' m, u m) ^ k := by
    have h := hPv
    unfold LSeries at h
    rw [funext hconv] at h
    have h2 : ∑' n, term U 0 n = ((∑' m, u m : ℝ) : ℂ) := by
      rw [funext hterm]
      exact (Complex.ofReal_tsum u).symm
    rw [h2, ← Complex.ofReal_tsum, ← Complex.ofReal_pow] at h
    exact_mod_cast h
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_convPow_le f s k) hsumR, ?_⟩
  calc ∑' n, ‖term (convPow f k) s n‖ ≤ ∑' n, convPow u k n :=
        Summable.tsum_le_tsum (norm_term_convPow_le f s k)
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_convPow_le f s k) hsumR)
          hsumR
    _ = (∑' n, ‖term f s n‖) ^ k := htsumR

theorem dirichletExp_eq_tsum {f : ℕ → ℂ} (h0 : f 0 = 0) (h1 : f 1 = 0) (n : ℕ) :
    dirichletExp f n = ∑' k, convPow f k n / (k.factorial : ℂ) := by
  rw [dirichletExp, tsum_eq_sum (s := Finset.range (n + 1))]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  rw [convPow_eq_zero_of_le h0 h1 (by omega : n < k), zero_div]

theorem dirichletExp_zero {f : ℕ → ℂ} : dirichletExp f 0 = 0 := by
  simp [dirichletExp, convPow_zero_apply]

theorem dirichletExp_one {f : ℕ → ℂ} (h0 : f 0 = 0) (h1 : f 1 = 0) : dirichletExp f 1 = 1 := by
  rw [dirichletExp, Finset.sum_range_succ, Finset.sum_range_one]
  rw [convPow_eq_zero_of_lt h0 h1 1 1 (by norm_num)]
  simp [convPow_zero_apply]

/-- **The Dirichlet exponential.**  If `f 0 = f 1 = 0` and `f` is absolutely summable at `s`,
then so is `exp⋆ f`, and `L(exp⋆ f, s) = exp L(f, s)`. -/
theorem LSeries_dirichletExp {f : ℕ → ℂ} (h0 : f 0 = 0) (h1 : f 1 = 0) {s : ℂ}
    (hf : LSeriesSummable f s) :
    LSeriesSummable (dirichletExp f) s ∧ LSeries (dirichletExp f) s = Complex.exp (LSeries f s) := by
  set M : ℝ := ∑' n, ‖term f s n‖ with hM
  set g : ℕ × ℕ → ℂ := fun p => term (convPow f p.1) s p.2 / (p.1.factorial : ℂ) with hg
  have hnorm : ∀ p : ℕ × ℕ, ‖g p‖ = ‖term (convPow f p.1) s p.2‖ / (p.1.factorial : ℝ) := by
    intro p
    rw [hg, norm_div, Complex.norm_natCast]
  have hrow : ∀ k, Summable (fun n => ‖g (k, n)‖) := by
    intro k
    simp_rw [hnorm]
    exact (summable_norm_term_convPow hf k).1.div_const _
  have hrowsum : Summable (fun k => ∑' n, ‖g (k, n)‖) := by
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      (Real.summable_pow_div_factorial M)
    simp_rw [hnorm]
    rw [tsum_div_const]
    exact div_le_div_of_nonneg_right (summable_norm_term_convPow hf k).2 (by positivity)
  have hgs : Summable g := by
    refine Summable.of_norm ?_
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hrow, hrowsum⟩
  -- the terms of `exp⋆ f`
  have hterm : ∀ n, term (dirichletExp f) s n = ∑' k, g (k, n) := by
    intro n
    rw [term_def]
    split_ifs with hn
    · subst hn
      simp [hg, term_def]
    · rw [dirichletExp_eq_tsum h0 h1, ← tsum_div_const]
      refine tsum_congr fun k => ?_
      simp only [hg, term_def, if_neg hn]
      ring
  have hcol : ∀ n, Summable (fun k => g (k, n)) := by
    intro n
    exact hgs.prod_symm.prod_factor n
  have hrowc : ∀ k, Summable (fun n => g (k, n)) := fun k => hgs.prod_factor k
  refine ⟨?_, ?_⟩
  · unfold LSeriesSummable
    rw [funext hterm]
    exact hgs.prod_symm.prod
  · unfold LSeries
    rw [funext hterm]
    have hswap : ∑' n, ∑' k, g (k, n) = ∑' k, ∑' n, g (k, n) :=
      Summable.tsum_comm' (f := fun k n => g (k, n)) hgs hrowc hcol
    rw [hswap, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    refine tsum_congr fun k => ?_
    simp only [hg]
    rw [tsum_div_const]
    have := (lseriesSummable_convPow hf k).2
    unfold LSeries at this
    rw [this]

end

end GaloisForLFunctions.HTGeometry
