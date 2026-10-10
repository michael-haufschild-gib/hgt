import GaloisForLFunctions.RHTower.ThetaNaturalScheduleEulerOscillation

/-!
# Comparison of prime power sums

For `S_α(N) = Σ_{p ≤ N} p^{-α}`:

* `S_α(N) → ∞` for `α ≤ 1`;
* `S_{α'}(N) = o(S_α(N))` for `α < α'` and `α ≤ 1` (split at a large prime);
* for `0 < α < 1` and `Δ ≠ 0` the twisted sum satisfies `|Σ_{p ≤ N} p^{-α + iΔ}| ≤ κ S_α(N)` for some
  `κ < 1` and all large `N`.  By the prime number theorem both sums are asymptotic to their main
  terms `N^{1-s}/((1-s) log N)`, whose moduli are in the ratio `(1-α)/|1-α+iΔ| < 1`.

These are the inputs that separate a dominant zero from competitors at other heights or with smaller
distance from the critical line.
-/

open Complex Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The primes at most `N`. -/
def jasPrimesUpTo (N : ℕ) : Finset Nat.Primes := (Nat.primesLE N).subtype Nat.Prime

theorem mem_jasPrimesUpTo {N : ℕ} {p : Nat.Primes} : p ∈ jasPrimesUpTo N ↔ (p : ℕ) ≤ N := by
  have h : p ∈ jasPrimesUpTo N ↔ (p : ℕ) ∈ Nat.primesLE N := Finset.mem_subtype
  rw [h, Nat.primesLE, Nat.mem_primesBelow]
  simp only [p.2, and_true]
  omega

theorem sum_jasPrimesUpTo {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ p ∈ jasPrimesUpTo N, f p = ∑ n ∈ Nat.primesLE N, f n := by
  have h : ∑ p ∈ jasPrimesUpTo N, f p = ∑ n ∈ (Nat.primesLE N).filter Nat.Prime, f n :=
    Finset.sum_subtype_eq_sum_filter f
  rw [h, Finset.filter_true_of_mem]
  intro n hn
  exact Nat.prime_of_mem_primesBelow hn

theorem jasPrimesUpTo_mono {M N : ℕ} (h : M ≤ N) : jasPrimesUpTo M ⊆ jasPrimesUpTo N := by
  intro p hp
  rw [mem_jasPrimesUpTo] at hp ⊢
  omega

/-- `S_α(N) = Σ_{p ≤ N} p^{-α}`. -/
def jasPrimeRpowSum (α : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ jasPrimesUpTo N, Real.exp (-α * Real.log p)

theorem jasPrimeRpowSum_nonneg (α : ℝ) (N : ℕ) : 0 ≤ jasPrimeRpowSum α N :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

theorem jasPrimeRpowSum_mono (α : ℝ) : Monotone (jasPrimeRpowSum α) := fun _ _ h =>
  Finset.sum_le_sum_of_subset_of_nonneg (jasPrimesUpTo_mono h) fun _ _ _ => (Real.exp_pos _).le

theorem one_div_le_exp_neg_mul_log {α : ℝ} (hα : α ≤ 1) (p : Nat.Primes) :
    1 / ((p : ℕ) : ℝ) ≤ Real.exp (-α * Real.log p) := by
  rw [show 1 / ((p : ℕ) : ℝ) = Real.exp (-Real.log p) by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos), one_div]]
  exact Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])

/-- `S_α(N) → ∞` for `α ≤ 1`. -/
theorem tendsto_jasPrimeRpowSum_atTop {α : ℝ} (hα : α ≤ 1) :
    Tendsto (jasPrimeRpowSum α) atTop atTop := by
  refine (jasPrimeRpowSum_mono α).tendsto_atTop_atTop fun B => ?_
  by_contra h
  push Not at h
  apply Nat.Primes.not_summable_one_div
  refine summable_of_sum_le (c := B) (fun p => by positivity) fun s => ?_
  set N := s.sup (fun p : Nat.Primes => (p : ℕ)) with hN
  have hsub : s ⊆ jasPrimesUpTo N := fun p hp => mem_jasPrimesUpTo.mpr (Finset.le_sup hp)
  calc ∑ p ∈ s, 1 / ((p : ℕ) : ℝ) ≤ ∑ p ∈ s, Real.exp (-α * Real.log p) :=
        Finset.sum_le_sum fun p _ => one_div_le_exp_neg_mul_log hα p
    _ ≤ jasPrimeRpowSum α N :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le
    _ ≤ B := (h N).le

/-- `S_{α'}(N) = o(S_α(N))` for `α < α'`, `α ≤ 1`. -/
theorem eventually_jasPrimeRpowSum_le {α α' : ℝ} (hα : α ≤ 1) (hαα' : α < α') {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ N in atTop, jasPrimeRpowSum α' N ≤ ε * jasPrimeRpowSum α N := by
  set L := Real.log (2 / ε) / (α' - α) with hL
  set p₁ : ℕ := ⌈Real.exp L⌉₊ with hp₁
  have hsmall : ∀ p : Nat.Primes, p₁ ≤ (p : ℕ) →
      Real.exp (-α' * Real.log p) ≤ ε / 2 * Real.exp (-α * Real.log p) := by
    intro p hp
    have h1 : Real.exp L ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hp)
    have h2 : L ≤ Real.log p := by
      rw [← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos _) h1
    have h3 : Real.log (2 / ε) ≤ (α' - α) * Real.log p := by
      rw [hL, div_le_iff₀ (by linarith)] at h2; linarith
    have h4 : Real.exp (-(α' - α) * Real.log p) ≤ ε / 2 := by
      calc Real.exp (-(α' - α) * Real.log p) ≤ Real.exp (-Real.log (2 / ε)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = ε / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    calc Real.exp (-α' * Real.log p) = Real.exp (-(α' - α) * Real.log p) * Real.exp (-α * Real.log p) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ ε / 2 * Real.exp (-α * Real.log p) := by gcongr
  set C := jasPrimeRpowSum α' p₁ with hC
  have hC0 : 0 ≤ C := jasPrimeRpowSum_nonneg _ _
  filter_upwards [(tendsto_jasPrimeRpowSum_atTop hα).eventually_ge_atTop (2 * C / ε)] with N hN
  unfold jasPrimeRpowSum
  rw [← Finset.sum_filter_add_sum_filter_not (jasPrimesUpTo N) (fun p : Nat.Primes => (p : ℕ) < p₁)]
  have hlow : ∑ p ∈ (jasPrimesUpTo N).filter (fun p : Nat.Primes => (p : ℕ) < p₁),
      Real.exp (-α' * Real.log p) ≤ C := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => (Real.exp_pos _).le
    rw [Finset.mem_filter] at hp
    exact mem_jasPrimesUpTo.mpr hp.2.le
  have hhigh : ∑ p ∈ (jasPrimesUpTo N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < p₁),
      Real.exp (-α' * Real.log p) ≤ ε / 2 * jasPrimeRpowSum α N := by
    calc _ ≤ ∑ p ∈ (jasPrimesUpTo N).filter (fun p : Nat.Primes => ¬ (p : ℕ) < p₁),
          ε / 2 * Real.exp (-α * Real.log p) :=
          Finset.sum_le_sum fun p hp => hsmall p (not_lt.mp (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ jasPrimesUpTo N, ε / 2 * Real.exp (-α * Real.log p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = ε / 2 * jasPrimeRpowSum α N := by rw [jasPrimeRpowSum, Finset.mul_sum]
  have : C ≤ ε / 2 * jasPrimeRpowSum α N := by
    rw [div_le_iff₀ hε] at hN; nlinarith
  unfold jasPrimeRpowSum at this hhigh
  linarith

/-- `p^{-(α - iΔ)} = p^{-α} e^{iΔ log p}`. -/
theorem natCast_cpow_neg_sub_mul_I {n : ℕ} (hn : 0 < n) (α Δ : ℝ) :
    (n : ℂ) ^ (-((α : ℂ) - (Δ : ℂ) * I)) =
      (Real.exp (-α * Real.log n) : ℂ) * cexp (((Δ * Real.log n : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.natCast_log,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Twisted prime sums lose a fixed proportion.**  For `0 < α < 1` and `Δ ≠ 0` there is `κ < 1`
with `|Σ_{p ≤ N} p^{-α} e^{iΔ log p}| ≤ κ S_α(N)` for all large `N`. -/
theorem exists_twisted_jasPrimeRpowSum_le {α Δ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hΔ : Δ ≠ 0) :
    ∃ κ : ℝ, κ < 1 ∧ ∀ᶠ N in atTop,
      ‖∑ p ∈ jasPrimesUpTo N, (Real.exp (-α * Real.log p) : ℂ) *
          cexp (((Δ * Real.log p : ℝ) : ℂ) * I)‖ ≤ κ * jasPrimeRpowSum α N := by
  set s : ℂ := (α : ℂ) - (Δ : ℂ) * I with hs
  have hsre : s.re = α := by simp [hs]
  have hαre : (α : ℂ).re = α := Complex.ofReal_re α
  have ha : 0 < 1 - α := by linarith
  have hnorm1s : 1 - α < ‖1 - s‖ := by
    have h2 : ‖1 - s‖ ^ 2 = (1 - α) ^ 2 + Δ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [hs]; ring
    have hΔ2 : 0 < Δ ^ 2 := by positivity
    nlinarith [norm_nonneg (1 - s)]
  set κΔ := (1 - α) / ‖1 - s‖ with hκΔ
  have hpos1s : 0 < ‖1 - s‖ := by linarith
  have hκΔ1 : κΔ < 1 := by rw [hκΔ, div_lt_one hpos1s]; exact hnorm1s
  have hκΔ0 : 0 < κΔ := by positivity
  set κ := (1 + κΔ) / 2 with hκ
  refine ⟨κ, by linarith, ?_⟩
  set η := (1 - κΔ) / (2 * (1 - α)) with hη
  have hη0 : 0 < η := by rw [hη]; apply div_pos <;> linarith
  have hA := tendsto_sum_primesLE_cpow_sub_main (s := s) (by rw [hsre]; exact h0) (by rw [hsre]; exact h1)
  have hB := tendsto_sum_primesLE_cpow_sub_main (s := (α : ℂ)) (by rw [hαre]; exact h0)
    (by rw [hαre]; exact h1)
  rw [hsre] at hA
  rw [hαre] at hB
  filter_upwards [hA.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by linarith)),
    hB.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by linarith)),
    eventually_ge_atTop 2] with N hAN hBN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have hNpow : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos (by linarith) _
  set E := (N : ℝ) ^ (1 - α) / Real.log N with hE
  have hE0 : 0 < E := div_pos hNpow hlog
  -- rewrite the sums
  have hT : ∑ p ∈ jasPrimesUpTo N, (Real.exp (-α * Real.log p) : ℂ) *
      cexp (((Δ * Real.log p : ℝ) : ℂ) * I) = ∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s) := by
    rw [sum_jasPrimesUpTo (fun n : ℕ => (Real.exp (-α * Real.log n) : ℂ) *
      cexp (((Δ * Real.log n : ℝ) : ℂ) * I)) N]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hs, natCast_cpow_neg_sub_mul_I (Nat.prime_of_mem_primesBelow hn).pos]
  have hS : ((jasPrimeRpowSum α N : ℝ) : ℂ) = ∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-(α : ℂ)) := by
    rw [jasPrimeRpowSum, Complex.ofReal_sum,
      sum_jasPrimesUpTo (fun n : ℕ => ((Real.exp (-α * Real.log n) : ℝ) : ℂ)) N]
    refine Finset.sum_congr rfl fun n hn => ?_
    have := natCast_cpow_neg_sub_mul_I (Nat.prime_of_mem_primesBelow hn).pos α 0
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, Complex.exp_zero, mul_one] at this
    rw [this]
  -- main terms
  have hMs : ‖((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))‖ = E / ‖1 - s‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog.le,
      show ((N : ℝ) : ℂ) = ((N : ℕ) : ℂ) by push_cast; rfl,
      Complex.norm_natCast_cpow_of_pos (by omega)]
    rw [show (1 - s).re = 1 - α by simp [hs], hE]
    field_simp
  have hMα : ((N : ℝ) : ℂ) ^ (1 - (α : ℂ)) / ((1 - (α : ℂ)) * (Real.log N : ℂ)) =
      (((N : ℝ) ^ (1 - α) / ((1 - α) * Real.log N) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (α : ℂ) = ((1 - α : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    push_cast
    ring
  -- error bounds
  have key : ∀ X : ℝ, X * Real.log N / (N : ℝ) ^ (1 - α) < η / 2 → X ≤ η / 2 * E := by
    intro X hX
    have hXe : X = X * Real.log N / (N : ℝ) ^ (1 - α) * E := by
      rw [hE]; field_simp
    rw [hXe]
    exact mul_le_mul_of_nonneg_right hX.le hE0.le
  have herrA := key _ hAN
  have herrB := key _ hBN
  -- conclude
  rw [hT]
  have hupper : ‖∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s)‖ ≤ E / ‖1 - s‖ + η / 2 * E := by
    have := norm_le_insert' (∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s))
      (((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ)))
    rw [hMs] at this
    linarith
  have hlower : E / (1 - α) - η / 2 * E ≤ jasPrimeRpowSum α N := by
    rw [hMα, ← hS] at herrB
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at herrB
    have hEq : (N : ℝ) ^ (1 - α) / ((1 - α) * Real.log N) = E / (1 - α) := by
      rw [hE]; field_simp
    rw [hEq] at herrB
    linarith [neg_abs_le (jasPrimeRpowSum α N - E / (1 - α))]
  have hκ1 : κ ≤ 1 := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hkey : E / ‖1 - s‖ + η / 2 * E ≤ κ * (E / (1 - α) - η / 2 * E) := by
    have h1' : E / ‖1 - s‖ = κΔ * (E / (1 - α)) := by rw [hκΔ]; field_simp
    rw [h1']
    have h2' : κ * (E / (1 - α)) - κΔ * (E / (1 - α)) = η * E := by
      rw [hκ, hη]; field_simp; ring
    have h3 : κ * (η / 2 * E) ≤ η / 2 * E := mul_le_of_le_one_left (by positivity) hκ1
    have h4 : κ * (E / (1 - α) - η / 2 * E) = κ * (E / (1 - α)) - κ * (η / 2 * E) := by ring
    rw [h4]
    linarith
  calc _ ≤ E / ‖1 - s‖ + η / 2 * E := hupper
    _ ≤ κ * (E / (1 - α) - η / 2 * E) := hkey
    _ ≤ κ * jasPrimeRpowSum α N := by gcongr

end

end RHTower
