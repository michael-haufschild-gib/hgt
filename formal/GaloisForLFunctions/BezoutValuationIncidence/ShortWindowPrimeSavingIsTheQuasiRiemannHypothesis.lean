import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.QuasiRHPowerMeshSquareSampleAndObserverJetAbscissaLaw
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# Short-window prime saving is the quasi-Riemann hypothesis

The prime-row counterpart of the Möbius statement. With `R(N) = ψ(N) - N` and

`F_α(Q) = Σ_{Q ≤ t < 2Q} (Σ_{t < n ≤ t + H} Λ(n) - H)²`,  `H = ⌈Q^α⌉`,

a power saving `F_α(Q) ≤ C Q^{1+2α-δ}` at one power length `0 < α < 1` holds if and only if
`Θ < 1`, `Θ` the zero abscissa.

* `⇐`: `R(N) ≪ N^{Θ+ε}` (`exists_psiRemainder_le_rpow_zetaZeroAbscissa`) gives
  `F_α(Q) ≪ Q^{1+2Θ+2ε}`; at `α = (1+Θ)/2`, `ε = (1-Θ)/4` this is `Q^{1+2α-δ}`, `δ = (1-Θ)/2`.
* `⇒`: the windows telescope, `Σ_t (R(t+H) - R(t)) = Σ_{i<H} (R(2Q+i) - R(Q+i))`, and
  `|R(a+i) - R(a)| ≤ i (log(a+i) + 1)`, so `|R(2Q) - R(Q)| ≤ √Q √F/H + 2H(log 3Q + 1) ≪ Q^γ`,
  `γ = max(1 - δ/2, (1+α)/2) < 1`; induction over halvings gives `R(N) ≪ N^γ`, and the
  square-sample exponent law `Θ = 1/2 + inf{c : Σ_{s<N} R(s²)/N² = O(N^{2c})}` gives `Θ ≤ max(γ, 1/2)`.

Together with the transfer law and Huxley's theorem, the centred prime row gains over the large sieve
by a factor `o(1)` unconditionally, and by a power exactly when `ζ` has a zero-free strip.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Windows and remainders -/

/-- The linear short-window energy `F_α(Q)` of the prime number theorem. -/
def primeWindowEnergy (α : ℝ) (Q : ℕ) : ℝ :=
  ∑ t ∈ Ico Q (2 * Q),
    (∑ n ∈ Ioc t (t + powerWindow α Q), vonMangoldt n - powerWindow α Q) ^ 2

/-- A power saving for the prime number theorem in almost all windows of one power length below
the scale. -/
def PrimePowerWindowSaving : Prop :=
  ∃ α δ C : ℝ, 0 < α ∧ α < 1 ∧ 0 < δ ∧
    ∀ Q : ℕ, 1 ≤ Q → primeWindowEnergy α Q ≤ C * (Q : ℝ) ^ (1 + 2 * α - δ)

theorem sum_Ioc_vonMangoldt_sub_eq (t H : ℕ) :
    ∑ n ∈ Ioc t (t + H), vonMangoldt n - H = psiRemainder (t + H) - psiRemainder t := by
  have h : chebyshevPsi (t + H) = chebyshevPsi t + ∑ n ∈ Ioc t (t + H), vonMangoldt n := by
    simp only [chebyshevPsi]
    rw [show Icc 1 (t + H) = Ioc 0 (t + H) by ext n; simp only [mem_Icc, mem_Ioc]; omega,
      show Icc 1 t = Ioc 0 t by ext n; simp only [mem_Icc, mem_Ioc]; omega,
      sum_Ioc_consecutive _ (Nat.zero_le t) (Nat.le_add_right t H)]
  rw [psiRemainder, psiRemainder, h]
  push_cast
  ring

theorem abs_vonMangoldt_sub_one_le {n M : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    |vonMangoldt n - 1| ≤ Real.log M + 1 := by
  have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hl := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have hm : Real.log n ≤ Real.log M := Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnM)
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [abs_le]; constructor <;> linarith

theorem abs_psiRemainder_add_sub_le (a i : ℕ) :
    |psiRemainder (a + i) - psiRemainder a| ≤ i * (Real.log (a + i : ℕ) + 1) := by
  rw [← sum_Ioc_vonMangoldt_sub_eq, show ∑ n ∈ Ioc a (a + i), vonMangoldt n - (i : ℝ) =
    ∑ n ∈ Ioc a (a + i), (vonMangoldt n - 1) by
      rw [sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul, mul_one]]
  calc |∑ n ∈ Ioc a (a + i), (vonMangoldt n - 1)| ≤ ∑ n ∈ Ioc a (a + i), |vonMangoldt n - 1| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc a (a + i), (Real.log (a + i : ℕ) + 1) := by
        refine sum_le_sum fun n hn => ?_
        have := mem_Ioc.mp hn
        exact abs_vonMangoldt_sub_one_le (by omega) this.2
    _ = i * (Real.log (a + i : ℕ) + 1) := by
        rw [sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]

/-- The windows telescope for every function. -/
theorem sum_Ico_window_telescope (f : ℕ → ℝ) (Q H : ℕ) :
    ∑ t ∈ Ico Q (2 * Q), (f (t + H) - f t) = ∑ i ∈ range H, (f (2 * Q + i) - f (Q + i)) := by
  have h1 : ∀ t, f (t + H) - f t = ∑ i ∈ range H, (f (t + (i + 1)) - f (t + i)) := by
    intro t
    rw [range_eq_Ico, sum_Ico_telescope (fun i => f (t + i)) (Nat.zero_le H), add_zero]
  rw [sum_congr rfl fun t _ => h1 t, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_congr rfl fun t _ => by rw [show t + (i + 1) = t + 1 + i by ring],
    sum_Ico_telescope (fun t => f (t + i)) (by omega : Q ≤ 2 * Q)]

/-- **One doubling.** `|R(2Q) - R(Q)| ≤ √Q √F/H + 2H (log 3Q + 1)` for `1 ≤ H ≤ Q`. -/
theorem abs_psiRemainder_two_mul_sub_le {Q H : ℕ} (hH : 1 ≤ H) (hHQ : H ≤ Q) :
    |psiRemainder (2 * Q) - psiRemainder Q| ≤
      Real.sqrt Q * Real.sqrt (∑ t ∈ Ico Q (2 * Q),
        (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) ^ 2) / H +
        2 * H * (Real.log (3 * Q : ℕ) + 1) := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set E := ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) ^ 2
  set S := ∑ t ∈ Ico Q (2 * Q), (psiRemainder (t + H) - psiRemainder t)
  set ℓ := Real.log (3 * Q : ℕ) + 1
  have hℓ : 0 ≤ ℓ := by
    have : 0 ≤ Real.log (3 * Q : ℕ) := Real.log_natCast_nonneg _
    simp only [ℓ]; linarith
  have hCS : |S| ≤ Real.sqrt Q * Real.sqrt E := by
    rw [show S = ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) from
      sum_congr rfl fun t _ => (sum_Ioc_vonMangoldt_sub_eq t H).symm]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Ico Q (2 * Q)) (fun _ => (1 : ℝ))
      (fun t => |∑ n ∈ Ioc t (t + H), vonMangoldt n - H|)
    simp only [one_mul, one_pow, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, sq_abs] at h
    rwa [show 2 * Q - Q = Q by omega] at h
  have hstep : ∀ a i, i ≤ H → a + i ≤ 3 * Q → |psiRemainder (a + i) - psiRemainder a| ≤ H * ℓ := by
    intro a i hi hai
    refine (abs_psiRemainder_add_sub_le a i).trans ?_
    have hiR : (i : ℝ) ≤ H := by exact_mod_cast hi
    have hlog : Real.log (a + i : ℕ) ≤ Real.log (3 * Q : ℕ) := by
      rcases Nat.eq_zero_or_pos (a + i) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hai)
    have h1 : 0 ≤ Real.log (a + i : ℕ) + 1 := by
      have := Real.log_natCast_nonneg (a + i); linarith
    calc (i : ℝ) * (Real.log (a + i : ℕ) + 1) ≤ H * (Real.log (a + i : ℕ) + 1) :=
          mul_le_mul_of_nonneg_right hiR h1
      _ ≤ H * ℓ := mul_le_mul_of_nonneg_left (by simp only [ℓ]; linarith) (by positivity)
  have hT : |S - H * (psiRemainder (2 * Q) - psiRemainder Q)| ≤ 2 * (H : ℝ) ^ 2 * ℓ := by
    rw [show S = ∑ i ∈ range H, (psiRemainder (2 * Q + i) - psiRemainder (Q + i)) from
      sum_Ico_window_telescope psiRemainder Q H,
      show (H : ℝ) * (psiRemainder (2 * Q) - psiRemainder Q) =
        ∑ _i ∈ range H, (psiRemainder (2 * Q) - psiRemainder Q) by
          rw [sum_const, card_range, nsmul_eq_mul], ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range H,
          |psiRemainder (2 * Q + i) - psiRemainder (Q + i) - (psiRemainder (2 * Q) - psiRemainder Q)|
        ≤ ∑ _i ∈ range H, 2 * (H * ℓ) := by
          refine sum_le_sum fun i hi => ?_
          have hiH := (mem_range.mp hi).le
          have h1 := hstep (2 * Q) i hiH (by omega)
          have h2 := hstep Q i hiH (by omega)
          rw [show psiRemainder (2 * Q + i) - psiRemainder (Q + i) -
              (psiRemainder (2 * Q) - psiRemainder Q) =
            (psiRemainder (2 * Q + i) - psiRemainder (2 * Q)) -
              (psiRemainder (Q + i) - psiRemainder Q) by ring]
          refine (abs_sub _ _).trans ?_
          linarith
      _ = 2 * (H : ℝ) ^ 2 * ℓ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hmain : (H : ℝ) * |psiRemainder (2 * Q) - psiRemainder Q| ≤
      Real.sqrt Q * Real.sqrt E + 2 * (H : ℝ) ^ 2 * ℓ := by
    have hHd : |(H : ℝ) * (psiRemainder (2 * Q) - psiRemainder Q)| =
        H * |psiRemainder (2 * Q) - psiRemainder Q| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < H)]
    have := abs_sub_abs_le_abs_sub (H * (psiRemainder (2 * Q) - psiRemainder Q)) S
    rw [abs_sub_comm] at this
    linarith
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
