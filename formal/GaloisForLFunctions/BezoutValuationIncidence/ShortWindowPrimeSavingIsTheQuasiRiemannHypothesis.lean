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

/-- **One doubling.** `|R(2Q) - R(Q)| ≤ √Q √F/H + 2H (log(2Q + H) + 1)` for `1 ≤ H`. -/
theorem abs_psiRemainder_two_mul_sub_le {Q H : ℕ} (hH : 1 ≤ H) :
    |psiRemainder (2 * Q) - psiRemainder Q| ≤
      Real.sqrt Q * Real.sqrt (∑ t ∈ Ico Q (2 * Q),
        (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) ^ 2) / H +
        2 * H * (Real.log (2 * Q + H : ℕ) + 1) := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set E := ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) ^ 2
  set S := ∑ t ∈ Ico Q (2 * Q), (psiRemainder (t + H) - psiRemainder t)
  set ℓ := Real.log (2 * Q + H : ℕ) + 1
  have hℓ : 0 ≤ ℓ := by
    have : 0 ≤ Real.log (2 * Q + H : ℕ) := Real.log_natCast_nonneg _
    simp only [ℓ]; linarith
  have hCS : |S| ≤ Real.sqrt Q * Real.sqrt E := by
    rw [show S = ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) from
      sum_congr rfl fun t _ => (sum_Ioc_vonMangoldt_sub_eq t H).symm]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Ico Q (2 * Q)) (fun _ => (1 : ℝ))
      (fun t => |∑ n ∈ Ioc t (t + H), vonMangoldt n - H|)
    simp only [one_mul, one_pow, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, sq_abs] at h
    rwa [show 2 * Q - Q = Q by omega] at h
  have hstep : ∀ a i, i ≤ H → a + i ≤ 2 * Q + H →
      |psiRemainder (a + i) - psiRemainder a| ≤ H * ℓ := by
    intro a i hi hai
    refine (abs_psiRemainder_add_sub_le a i).trans ?_
    have hiR : (i : ℝ) ≤ H := by exact_mod_cast hi
    have hlog : Real.log (a + i : ℕ) ≤ Real.log (2 * Q + H : ℕ) := by
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

/-! ## §2. A zero-free strip gives the saving -/

theorem primePowerWindowSaving_of_lt_one (hΘ : zetaZeroAbscissa < 1) : PrimePowerWindowSaving := by
  set Θ := zetaZeroAbscissa
  have hΘ0 : (1 / 2 : ℝ) ≤ Θ := half_le_zetaZeroAbscissa
  set ε : ℝ := (1 - Θ) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨C₀, hC₀, hR⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  set s : ℝ := Θ + ε
  have hs : 0 ≤ s := by simp only [s]; linarith
  refine ⟨(1 + Θ) / 2, (1 - Θ) / 2, 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s), by linarith, by linarith,
    by linarith, fun Q hQ => ?_⟩
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  set H := powerWindow ((1 + Θ) / 2) Q
  have hH : (H : ℝ) ≤ 2 * Q := by
    have h1 : (H : ℝ) < (Q : ℝ) ^ ((1 + Θ) / 2) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hQ0.le _)
    have h2 : (Q : ℝ) ^ ((1 + Θ) / 2) ≤ Q := by
      calc (Q : ℝ) ^ ((1 + Θ) / 2) ≤ (Q : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hQR (by linarith)
        _ = Q := Real.rpow_one _
    linarith
  have hb : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ 5 * Q → |psiRemainder N| ≤ C₀ * (5 * (Q : ℝ)) ^ s := by
    intro N hN hN5
    refine (hR N hN).trans (mul_le_mul_of_nonneg_left ?_ hC₀)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN5 hs
  have hwin : ∀ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), vonMangoldt n - H) ^ 2 ≤
      4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) * (Q : ℝ) ^ (2 * s) := by
    intro t ht
    have ht' := mem_Ico.mp ht
    have ht2 : (t : ℝ) ≤ 2 * Q := by
      have h : ((t : ℕ) : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by exact_mod_cast ht'.2.le
      push_cast at h; exact h
    have htH : ((t + H : ℕ) : ℝ) ≤ 5 * Q := by push_cast; linarith
    have ht5 : (t : ℝ) ≤ 5 * Q := by linarith
    have hA : |∑ n ∈ Ioc t (t + H), vonMangoldt n - H| ≤ 2 * (C₀ * (5 * (Q : ℝ)) ^ s) := by
      rw [sum_Ioc_vonMangoldt_sub_eq]
      refine (abs_sub _ _).trans ?_
      linarith [hb (t + H) (by omega) htH, hb t (by omega) ht5]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hA 2
    rw [sq_abs] at hsq
    have e1 : ((5 * (Q : ℝ)) ^ s) ^ 2 = (5 : ℝ) ^ (2 * s) * (Q : ℝ) ^ (2 * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show s * ((2 : ℕ) : ℝ) = 2 * s by push_cast; ring, Real.mul_rpow (by norm_num) hQ0.le]
    refine hsq.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, e1]
    ring
  calc primeWindowEnergy ((1 + Θ) / 2) Q
      ≤ ∑ _t ∈ Ico Q (2 * Q), 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) * (Q : ℝ) ^ (2 * s) := sum_le_sum hwin
    _ = 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) * ((Q : ℝ) * (Q : ℝ) ^ (2 * s)) := by
        rw [sum_const, Nat.card_Ico, show 2 * Q - Q = Q by omega, nsmul_eq_mul]; ring
    _ = 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) *
        (Q : ℝ) ^ (1 + 2 * ((1 + Θ) / 2) - (1 - Θ) / 2) := by
        rw [← Real.rpow_one_add' hQ0.le (by positivity)]
        congr 2
        simp only [s, ε]; ring

/-! ## §3. The saving gives a zero-free strip -/

/-- `log(4Q) + 1 ≤ (4/η + 1) Q^η` for `Q ≥ 1`, `0 < η ≤ 1`. -/
theorem log_four_mul_add_one_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {Q : ℕ} (hQ : 1 ≤ Q) :
    Real.log (4 * Q : ℕ) + 1 ≤ (4 / η + 1) * (Q : ℝ) ^ η := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have h1 := Real.log_le_rpow_div (x := ((4 * Q : ℕ) : ℝ)) (Nat.cast_nonneg _) hη
  have h4 : (((4 * Q : ℕ) : ℝ)) ^ η ≤ 4 * (Q : ℝ) ^ η := by
    push_cast
    rw [Real.mul_rpow (by norm_num) hQ0.le]
    have : (4 : ℝ) ^ η ≤ 4 := by
      calc (4 : ℝ) ^ η ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
        _ = 4 := Real.rpow_one 4
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hQ0.le _)
  have hQη : 1 ≤ (Q : ℝ) ^ η := Real.one_le_rpow hQR hη.le
  have h5 : (((4 * Q : ℕ) : ℝ)) ^ η / η ≤ 4 / η * (Q : ℝ) ^ η := by
    rw [div_le_iff₀ hη]
    calc (((4 * Q : ℕ) : ℝ)) ^ η ≤ 4 * (Q : ℝ) ^ η := h4
      _ = 4 / η * (Q : ℝ) ^ η * η := by field_simp
  nlinarith

/-- **The saving gives a zero-free strip.** -/
theorem zetaZeroAbscissa_lt_one_of_primePowerWindowSaving (h : PrimePowerWindowSaving) :
    zetaZeroAbscissa < 1 := by
  obtain ⟨α, δ, C, hα0, hα1, hδ, hE⟩ := h
  set η : ℝ := (1 - α) / 2
  have hη0 : 0 < η := by simp only [η]; linarith
  have hη1 : η ≤ 1 := by simp only [η]; linarith
  set γ := max (1 - δ / 2) ((1 + α) / 2)
  have hγ1 : γ < 1 := max_lt (by linarith) (by linarith)
  have hγα : (1 + α) / 2 ≤ γ := le_max_right _ _
  have hγ0 : 0 < γ := lt_of_lt_of_le (by linarith) hγα
  have hηγ : η ≤ γ := by simp only [η]; linarith
  have hC : 0 ≤ C := by
    have h1 := hE 1 le_rfl
    have h0 : 0 ≤ primeWindowEnergy α 1 := sum_nonneg fun _ _ => sq_nonneg _
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h1
    linarith
  set B := Real.sqrt C + 4 * (4 / η + 1) + (4 / η + 1)
  have hB0 : 0 ≤ B := by positivity
  -- one doubling, and one odd step, cost `B Q^γ`
  have hstep : ∀ Q : ℕ, 1 ≤ Q → ∀ N : ℕ, 2 * Q ≤ N → N ≤ 2 * Q + 1 →
      |psiRemainder N - psiRemainder Q| ≤ B * (Q : ℝ) ^ γ := by
    intro Q hQ N hN1 hN2
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hQ0 : (0 : ℝ) < Q := by linarith
    set H := powerWindow α Q
    have hQα : 1 ≤ (Q : ℝ) ^ α := Real.one_le_rpow hQR hα0.le
    have hHlo : (Q : ℝ) ^ α ≤ H := Nat.le_ceil _
    have hH1 : 1 ≤ H := by exact_mod_cast hQα.trans hHlo
    have hHhi : (H : ℝ) ≤ 2 * (Q : ℝ) ^ α := by
      have : (H : ℝ) < (Q : ℝ) ^ α + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hQ0.le α)
      linarith
    have hQαQ : (Q : ℝ) ^ α ≤ Q := by
      calc (Q : ℝ) ^ α ≤ (Q : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQR hα1.le
        _ = Q := Real.rpow_one _
    have hH2Q : 2 * Q + H ≤ 4 * Q := by
      have : (H : ℝ) ≤ 2 * Q := by linarith
      have h' : ((2 * Q + H : ℕ) : ℝ) ≤ ((4 * Q : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
    have hlog4 := log_four_mul_add_one_le hη0 hη1 hQ
    have hlogH : Real.log (2 * Q + H : ℕ) + 1 ≤ (4 / η + 1) * (Q : ℝ) ^ η := by
      refine le_trans ?_ hlog4
      have : Real.log (2 * Q + H : ℕ) ≤ Real.log (4 * Q : ℕ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * Q + H)) (by exact_mod_cast hH2Q)
      linarith
    have hd := abs_psiRemainder_two_mul_sub_le (Q := Q) hH1
    have hEQ : Real.sqrt (primeWindowEnergy α Q) ≤ Real.sqrt C * (Q : ℝ) ^ ((1 + 2 * α - δ) / 2) := by
      rw [show (Q : ℝ) ^ ((1 + 2 * α - δ) / 2) = Real.sqrt ((Q : ℝ) ^ (1 + 2 * α - δ)) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQ0.le]; ring_nf, ← Real.sqrt_mul hC]
      exact Real.sqrt_le_sqrt (hE Q hQ)
    have h1 : Real.sqrt Q * Real.sqrt (primeWindowEnergy α Q) / H ≤ Real.sqrt C * (Q : ℝ) ^ γ := by
      rw [div_le_iff₀ (by linarith)]
      calc Real.sqrt Q * Real.sqrt (primeWindowEnergy α Q)
          ≤ Real.sqrt Q * (Real.sqrt C * (Q : ℝ) ^ ((1 + 2 * α - δ) / 2)) :=
            mul_le_mul_of_nonneg_left hEQ (Real.sqrt_nonneg _)
        _ = Real.sqrt C * (Q : ℝ) ^ (1 - δ / 2) * (Q : ℝ) ^ α := by
            rw [Real.sqrt_eq_rpow, mul_left_comm, mul_assoc, ← Real.rpow_add hQ0,
              ← Real.rpow_add hQ0]
            congr 2
            ring
        _ ≤ Real.sqrt C * (Q : ℝ) ^ γ * H := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hQR (le_max_left _ _)) (Real.sqrt_nonneg _)) hHlo
              (by positivity) (by positivity)
    have h2 : 2 * (H : ℝ) * (Real.log (2 * Q + H : ℕ) + 1) ≤ 4 * (4 / η + 1) * (Q : ℝ) ^ γ := by
      have hl0 : 0 ≤ Real.log (2 * Q + H : ℕ) + 1 := by
        have := Real.log_natCast_nonneg (2 * Q + H); linarith
      calc 2 * (H : ℝ) * (Real.log (2 * Q + H : ℕ) + 1)
          ≤ 2 * (2 * (Q : ℝ) ^ α) * ((4 / η + 1) * (Q : ℝ) ^ η) := by gcongr
        _ = 4 * (4 / η + 1) * (Q : ℝ) ^ ((1 + α) / 2) := by
            rw [show (1 + α) / 2 = α + η by simp only [η]; ring, Real.rpow_add hQ0]; ring
        _ ≤ 4 * (4 / η + 1) * (Q : ℝ) ^ γ := by
            gcongr
    have hodd : |psiRemainder N - psiRemainder (2 * Q)| ≤ (4 / η + 1) * (Q : ℝ) ^ γ := by
      obtain ⟨r, hr, rfl⟩ : ∃ r, r ≤ 1 ∧ N = 2 * Q + r := ⟨N - 2 * Q, by omega, by omega⟩
      refine (abs_psiRemainder_add_sub_le (2 * Q) r).trans ?_
      have hrR : (r : ℝ) ≤ 1 := by exact_mod_cast hr
      have hl : Real.log (2 * Q + r : ℕ) + 1 ≤ (4 / η + 1) * (Q : ℝ) ^ η := by
        refine le_trans ?_ hlog4
        have : Real.log (2 * Q + r : ℕ) ≤ Real.log (4 * Q : ℕ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * Q + r)) (by exact_mod_cast (by omega))
        linarith
      have hl0 : 0 ≤ Real.log (2 * Q + r : ℕ) + 1 := by
        have := Real.log_natCast_nonneg (2 * Q + r); linarith
      have hQηγ : (Q : ℝ) ^ η ≤ (Q : ℝ) ^ γ := Real.rpow_le_rpow_of_exponent_le hQR hηγ
      calc (r : ℝ) * (Real.log (2 * Q + r : ℕ) + 1) ≤ 1 * ((4 / η + 1) * (Q : ℝ) ^ η) :=
            mul_le_mul hrR hl hl0 (by norm_num)
        _ ≤ (4 / η + 1) * (Q : ℝ) ^ γ := by rw [one_mul]; gcongr
    have hd' : |psiRemainder (2 * Q) - psiRemainder Q| ≤
        Real.sqrt Q * Real.sqrt (primeWindowEnergy α Q) / H +
          2 * H * (Real.log (2 * Q + H : ℕ) + 1) := hd
    have := abs_sub_le (psiRemainder N) (psiRemainder (2 * Q)) (psiRemainder Q)
    simp only [B]
    linarith
  -- halving induction: `|R(N)| ≤ K (N+1)^γ`
  have hgap : 0 < (3 / 2 : ℝ) ^ γ - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3 / 2) hγ0; linarith
  set K := max 1 (B / ((3 / 2 : ℝ) ^ γ - 1))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKB : B ≤ K * ((3 / 2 : ℝ) ^ γ - 1) := by
    rw [← div_le_iff₀ hgap]; exact le_max_right _ _
  have hind : ∀ N : ℕ, |psiRemainder N| ≤ K * ((N : ℝ) + 1) ^ γ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      have hN1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ γ :=
        Real.one_le_rpow (by linarith [N.cast_nonneg' (α := ℝ)]) hγ0.le
      rcases Nat.lt_or_ge N 2 with hN | hN
      · have h1 : |psiRemainder N| ≤ 1 := by
          interval_cases N <;> simp [psiRemainder, chebyshevPsi]
        nlinarith
      · set Q := N / 2
        have hQ1 : 1 ≤ Q := by omega
        have hQN : Q < N := by omega
        have hst := hstep Q hQ1 N (by omega) (by omega)
        have hih := ih Q hQN
        have hgrow : (3 / 2 : ℝ) ^ γ * ((Q : ℝ) + 1) ^ γ ≤ ((N : ℝ) + 1) ^ γ := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          refine Real.rpow_le_rpow (by positivity) ?_ hγ0.le
          have h' : ((2 * Q : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * Q ≤ N)
          have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
          push_cast at h'
          linarith
        have hQγ : (Q : ℝ) ^ γ ≤ ((Q : ℝ) + 1) ^ γ :=
          Real.rpow_le_rpow (by positivity) (by linarith) hγ0.le
        have htri : |psiRemainder N| ≤ B * (Q : ℝ) ^ γ + K * ((Q : ℝ) + 1) ^ γ := by
          have := abs_add_le (psiRemainder N - psiRemainder Q) (psiRemainder Q)
          rw [sub_add_cancel] at this
          linarith
        have hfin : B * (Q : ℝ) ^ γ + K * ((Q : ℝ) + 1) ^ γ ≤
            K * ((3 / 2 : ℝ) ^ γ * ((Q : ℝ) + 1) ^ γ) := by
          have hb := mul_le_mul_of_nonneg_right hKB (by positivity : (0 : ℝ) ≤ ((Q : ℝ) + 1) ^ γ)
          have hb2 := mul_le_mul_of_nonneg_left hQγ hB0
          nlinarith
        calc |psiRemainder N| ≤ K * ((3 / 2 : ℝ) ^ γ * ((Q : ℝ) + 1) ^ γ) := htri.trans hfin
          _ ≤ K * ((N : ℝ) + 1) ^ γ := mul_le_mul_of_nonneg_left hgrow (by linarith)
  -- the square-sample exponent law
  set c := max γ (1 / 2)
  have hc1 : c < 1 := max_lt hγ1 (by norm_num)
  have hRc : ∀ N : ℕ, 1 ≤ N → |psiRemainder N| ≤ 2 * K * (N : ℝ) ^ c := by
    intro N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    refine (hind N).trans ?_
    have h1 : ((N : ℝ) + 1) ^ γ ≤ 2 * (N : ℝ) ^ γ := by
      calc ((N : ℝ) + 1) ^ γ ≤ (2 * (N : ℝ)) ^ γ := Real.rpow_le_rpow (by positivity) (by linarith) hγ0.le
        _ = (2 : ℝ) ^ γ * (N : ℝ) ^ γ := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 2 * (N : ℝ) ^ γ := by
            gcongr
            calc (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1.le
              _ = 2 := Real.rpow_one 2
    have h2 : (N : ℝ) ^ γ ≤ (N : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hNR (le_max_left _ _)
    nlinarith
  have hmem : c - 1 / 2 ∈ psiRemainderSquareSumUpperExponentSet := by
    refine ⟨sub_nonneg.mpr (le_max_right _ _), 2 * K, by positivity, fun N hN => ?_⟩
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hN2 : ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
    have hsum : ∑ s ∈ Ico 1 N, psiRemainder (s ^ 2) ≤ N * (2 * K * ((N ^ 2 : ℕ) : ℝ) ^ c) := by
      calc ∑ s ∈ Ico 1 N, psiRemainder (s ^ 2) ≤ ∑ s ∈ Ico 1 N, |psiRemainder (s ^ 2)| :=
            sum_le_sum fun s _ => le_abs_self _
        _ ≤ ∑ _s ∈ Ico 1 N, 2 * K * ((N ^ 2 : ℕ) : ℝ) ^ c := by
            refine sum_le_sum fun s hs => ?_
            have hs' := mem_Ico.mp hs
            refine (hRc (s ^ 2) (Nat.one_le_pow _ _ hs'.1)).trans ?_
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_
              (by linarith [le_max_right γ (1 / 2 : ℝ)])) (by positivity)
            exact_mod_cast Nat.pow_le_pow_left hs'.2.le 2
        _ = ((N - 1 : ℕ) : ℝ) * (2 * K * ((N ^ 2 : ℕ) : ℝ) ^ c) := by
            rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ N * (2 * K * ((N ^ 2 : ℕ) : ℝ) ^ c) := by
            gcongr
            exact_mod_cast Nat.sub_le N 1
    rw [div_le_iff₀ (by positivity)]
    refine hsum.trans (le_of_eq ?_)
    rw [hN2, Real.rpow_sub (by positivity), show ((N : ℝ) ^ 2) ^ (1 / 2 : ℝ) = N by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hN0.le]]
    field_simp
  have hbdd : BddBelow psiRemainderSquareSumUpperExponentSet := ⟨0, fun _ hc => hc.1⟩
  have := csInf_le hbdd hmem
  rw [zetaZeroAbscissa_eq_half_add_sInf_psiRemainder_squareSum_upper]
  linarith

/-- **Short-window prime saving is the quasi-Riemann hypothesis.** A power saving for the prime
number theorem in almost all windows of one power length `Q^α`, `0 < α < 1`, holds if and only if
`ζ` has a zero-free strip `Re s > Θ` with `Θ < 1`. -/
theorem primePowerWindowSaving_iff : PrimePowerWindowSaving ↔ zetaZeroAbscissa < 1 :=
  ⟨zetaZeroAbscissa_lt_one_of_primePowerWindowSaving, primePowerWindowSaving_of_lt_one⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
