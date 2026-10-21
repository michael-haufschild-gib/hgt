import GaloisForLFunctions.BezoutValuationIncidence.MoebiusBlockBeatsTheTypeTwoBarrier
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.MobiusMertensAbsoluteMomentExponentLaw

/-!
# Short-window Möbius saving is the quasi-Riemann hypothesis

The short-window transfer law bounds the Type-II loss of a large-scale row by its mean square over
windows of length `H = o(P)`. For the Möbius row a power gain past the large sieve therefore asks for
a power saving in

`E_α(Q) = Σ_{Q ≤ t < 2Q} (Σ_{t < n ≤ t + ⌈Q^α⌉} μ(n))²`

against the trivial `Q^{1+2α}`. This module proves that such a saving at a single power length is
exactly the quasi-Riemann hypothesis `Θ < 1`, `Θ` the zero abscissa:

`(∃ α ∈ (0,1), δ > 0, C, ∀ Q ≥ 1, E_α(Q) ≤ C Q^{1+2α-δ}) ↔ Θ < 1`.

* `⇐`: Littlewood's bound `M(N) ≪ N^{Θ+ε}` gives `E_α(Q) ≪ Q^{1+2Θ+2ε}`; at `α = (1+Θ)/2`,
  `ε = (1-Θ)/4` this is `Q^{1+2α-δ}` with `δ = (1-Θ)/2`.
* `⇒`: the windows telescope, `Σ_t (M(t+H) - M(t)) = Σ_{i<H} (M(2Q+i) - M(Q+i))`, so
  `|M(2Q) - M(Q)| ≤ √Q √E_α(Q)/H + 2H ≪ Q^γ`, `γ = max(1 - δ/2, α) < 1`; induction over halvings gives
  `M(N) ≪ N^γ`, and the absolute-moment exponent law gives `Θ ≤ γ`.

So the balanced-regime cancellation of the Möbius row that the transfer law needs for an exponent
gain is a zero-free strip, as the receiver bound below half damping is.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Windows and Mertens differences -/

/-- The window length `⌈Q^α⌉`. -/
def powerWindow (α : ℝ) (Q : ℕ) : ℕ := ⌈(Q : ℝ) ^ α⌉₊

/-- The linear short-window energy `E_α(Q)` of the Möbius function. -/
def moebiusWindowEnergy (α : ℝ) (Q : ℕ) : ℝ :=
  ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + powerWindow α Q), moebiusReal n) ^ 2

/-- A power saving for the Möbius function in almost all windows of one power length below the
scale. -/
def MoebiusPowerWindowSaving : Prop :=
  ∃ α δ C : ℝ, 0 < α ∧ α < 1 ∧ 0 < δ ∧
    ∀ Q : ℕ, 1 ≤ Q → moebiusWindowEnergy α Q ≤ C * (Q : ℝ) ^ (1 + 2 * α - δ)

theorem sum_Ioc_moebiusReal_eq_sub (t H : ℕ) :
    ∑ n ∈ Ioc t (t + H), moebiusReal n = mertensM (t + H) - mertensM t := by
  rw [mertensM, mertensM, ← sum_range_add_sum_Ico _ (by omega : t + 1 ≤ t + H + 1),
    add_sub_cancel_left]
  exact sum_congr (by ext n; simp only [mem_Ioc, mem_Ico]; omega) fun n _ => rfl

theorem norm_mobiusMertensPartialSum_eq (N : ℕ) : ‖mobiusMertensPartialSum N‖ = |mertensM N| := by
  have : mobiusMertensPartialSum N = ((mertensM N : ℝ) : ℂ) := by
    simp [mobiusMertensPartialSum, mobiusComplexCoefficient, mertensM]
  rw [this, Complex.norm_real]
  rfl

theorem abs_mertensM_add_sub_le (a i : ℕ) : |mertensM (a + i) - mertensM a| ≤ i := by
  rw [← sum_Ioc_moebiusReal_eq_sub]
  have h := abs_sum_Ioc_le_card abs_moebiusReal_le_one' a (a + i)
  rwa [Nat.add_sub_cancel_left] at h

theorem abs_mertensM_le (N : ℕ) : |mertensM N| ≤ N := by
  have h := abs_mertensM_add_sub_le 0 N
  rw [zero_add] at h
  have h0 : mertensM 0 = 0 := by simp [mertensM]
  rwa [h0, sub_zero] at h

/-! ## §2. A zero-free strip gives the saving -/

theorem moebiusPowerWindowSaving_of_lt_one (hΘ : zetaZeroAbscissa < 1) :
    MoebiusPowerWindowSaving := by
  set Θ := zetaZeroAbscissa
  have hΘ0 : (1 / 2 : ℝ) ≤ Θ := half_le_zetaZeroAbscissa
  set ε : ℝ := (1 - Θ) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨C₀, hC₀, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε
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
  -- each window is at most `2 C₀ (5Q)^s`
  have hwin : ∀ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), moebiusReal n) ^ 2 ≤
      4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) * (Q : ℝ) ^ (2 * s) := by
    intro t ht
    have ht' := mem_Ico.mp ht
    have htR : (t : ℝ) + 1 ≤ 5 * Q := by
      have : t + 1 ≤ 2 * Q := by omega
      have h : ((t + 1 : ℕ) : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h; linarith
    have htH : ((t + H : ℕ) : ℝ) + 1 ≤ 5 * Q := by
      have : (t : ℝ) + 1 ≤ 2 * Q := by
        have : t + 1 ≤ 2 * Q := by omega
        have h : ((t + 1 : ℕ) : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h; linarith
      push_cast; linarith
    have hb : ∀ N : ℕ, (N : ℝ) + 1 ≤ 5 * Q → |mertensM N| ≤ C₀ * (5 * (Q : ℝ)) ^ s := by
      intro N hN
      rw [← norm_mobiusMertensPartialSum_eq]
      refine (hM N).trans (mul_le_mul_of_nonneg_left ?_ hC₀)
      exact Real.rpow_le_rpow (by positivity) hN hs
    have hA : |∑ n ∈ Ioc t (t + H), moebiusReal n| ≤ 2 * (C₀ * (5 * (Q : ℝ)) ^ s) := by
      rw [sum_Ioc_moebiusReal_eq_sub]
      refine (abs_sub _ _).trans ?_
      linarith [hb (t + H) htH, hb t (by linarith)]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hA 2
    rw [sq_abs] at hsq
    have e1 : ((5 * (Q : ℝ)) ^ s) ^ 2 = (5 : ℝ) ^ (2 * s) * (Q : ℝ) ^ (2 * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show s * ((2 : ℕ) : ℝ) = 2 * s by push_cast; ring, Real.mul_rpow (by norm_num) hQ0.le]
    refine hsq.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, e1]
    ring
  calc moebiusWindowEnergy ((1 + Θ) / 2) Q
      ≤ ∑ _t ∈ Ico Q (2 * Q), 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) * (Q : ℝ) ^ (2 * s) := sum_le_sum hwin
    _ = 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) * ((Q : ℝ) * (Q : ℝ) ^ (2 * s)) := by
        rw [sum_const, Nat.card_Ico, show 2 * Q - Q = Q by omega, nsmul_eq_mul]; ring
    _ = 4 * C₀ ^ 2 * (5 : ℝ) ^ (2 * s) *
        (Q : ℝ) ^ (1 + 2 * ((1 + Θ) / 2) - (1 - Θ) / 2) := by
        rw [← Real.rpow_one_add' hQ0.le (by positivity)]
        congr 2
        simp only [s, ε]; ring

/-! ## §3. The saving gives a zero-free strip -/

theorem sum_Ico_telescope (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ t ∈ Ico a b, (f (t + 1) - f t) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [sum_Ico_succ_top hab, ih]; ring

/-- The windows telescope: `Σ_{Q≤t<2Q} (M(t+H) - M(t)) = Σ_{i<H} (M(2Q+i) - M(Q+i))`. -/
theorem sum_Ico_mertensM_window_eq (Q H : ℕ) :
    ∑ t ∈ Ico Q (2 * Q), (mertensM (t + H) - mertensM t) =
      ∑ i ∈ range H, (mertensM (2 * Q + i) - mertensM (Q + i)) := by
  have h1 : ∀ t, mertensM (t + H) - mertensM t =
      ∑ i ∈ range H, (mertensM (t + (i + 1)) - mertensM (t + i)) := by
    intro t
    rw [range_eq_Ico, sum_Ico_telescope (fun i => mertensM (t + i)) (Nat.zero_le H), add_zero]
  rw [sum_congr rfl fun t _ => h1 t, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_congr rfl fun t _ => by rw [show t + (i + 1) = t + 1 + i by ring],
    sum_Ico_telescope (fun t => mertensM (t + i)) (by omega : Q ≤ 2 * Q)]

/-- **One doubling.** `|M(2Q) - M(Q)| ≤ √Q √E/H + 2H` for the window energy `E` at length `H`. -/
theorem abs_mertensM_two_mul_sub_le {Q H : ℕ} (hH : 1 ≤ H) :
    |mertensM (2 * Q) - mertensM Q| ≤
      Real.sqrt Q * Real.sqrt (∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), moebiusReal n) ^ 2) / H +
        2 * H := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set E := ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H), moebiusReal n) ^ 2
  set S := ∑ t ∈ Ico Q (2 * Q), (mertensM (t + H) - mertensM t)
  have hS : S = ∑ t ∈ Ico Q (2 * Q), ∑ n ∈ Ioc t (t + H), moebiusReal n :=
    sum_congr rfl fun t _ => (sum_Ioc_moebiusReal_eq_sub t H).symm
  -- Cauchy–Schwarz over the `Q` starts
  have hCS : |S| ≤ Real.sqrt Q * Real.sqrt E := by
    rw [hS]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Ico Q (2 * Q)) (fun _ => (1 : ℝ))
      (fun t => |∑ n ∈ Ioc t (t + H), moebiusReal n|)
    simp only [one_mul, one_pow, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, sq_abs] at h
    rwa [show 2 * Q - Q = Q by omega] at h
  -- the telescoped sum is `H` doublings up to `2H²`
  have hT : |S - H * (mertensM (2 * Q) - mertensM Q)| ≤ 2 * (H : ℝ) ^ 2 := by
    rw [show S = ∑ i ∈ range H, (mertensM (2 * Q + i) - mertensM (Q + i)) from
      sum_Ico_mertensM_window_eq Q H]
    rw [show (H : ℝ) * (mertensM (2 * Q) - mertensM Q) =
      ∑ _i ∈ range H, (mertensM (2 * Q) - mertensM Q) by rw [sum_const, card_range, nsmul_eq_mul],
      ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range H, |mertensM (2 * Q + i) - mertensM (Q + i) - (mertensM (2 * Q) - mertensM Q)|
        ≤ ∑ _i ∈ range H, 2 * (H : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := abs_mertensM_add_sub_le (2 * Q) i
          have h2 := abs_mertensM_add_sub_le Q i
          have hi' : (i : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hi).le
          rw [show mertensM (2 * Q + i) - mertensM (Q + i) - (mertensM (2 * Q) - mertensM Q) =
            (mertensM (2 * Q + i) - mertensM (2 * Q)) - (mertensM (Q + i) - mertensM Q) by ring]
          refine (abs_sub _ _).trans ?_
          linarith
      _ = 2 * (H : ℝ) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hmain : (H : ℝ) * |mertensM (2 * Q) - mertensM Q| ≤ Real.sqrt Q * Real.sqrt E + 2 * (H : ℝ) ^ 2 := by
    have hHd : |(H : ℝ) * (mertensM (2 * Q) - mertensM Q)| = H * |mertensM (2 * Q) - mertensM Q| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < H)]
    have := abs_sub_abs_le_abs_sub (H * (mertensM (2 * Q) - mertensM Q)) S
    rw [abs_sub_comm] at this
    linarith
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

/-- **The saving gives a zero-free strip.** -/
theorem zetaZeroAbscissa_lt_one_of_moebiusPowerWindowSaving (h : MoebiusPowerWindowSaving) :
    zetaZeroAbscissa < 1 := by
  obtain ⟨α, δ, C, hα0, hα1, hδ, hE⟩ := h
  set γ := max (1 - δ / 2) α
  have hγ1 : γ < 1 := max_lt (by linarith) hα1
  have hγ0 : 0 < γ := lt_of_lt_of_le hα0 (le_max_right _ _)
  have hC : 0 ≤ C := by
    have h1 := hE 1 le_rfl
    have h0 : 0 ≤ moebiusWindowEnergy α 1 := sum_nonneg fun _ _ => sq_nonneg _
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h1
    linarith
  set B := Real.sqrt C + 4
  -- one doubling costs `B Q^γ`
  have hstep : ∀ Q : ℕ, 1 ≤ Q → |mertensM (2 * Q) - mertensM Q| ≤ B * (Q : ℝ) ^ γ := by
    intro Q hQ
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hQ0 : (0 : ℝ) < Q := by linarith
    set H := powerWindow α Q
    have hQα : 1 ≤ (Q : ℝ) ^ α := Real.one_le_rpow hQR hα0.le
    have hHlo : (Q : ℝ) ^ α ≤ H := Nat.le_ceil _
    have hH1 : 1 ≤ H := by exact_mod_cast hQα.trans hHlo
    have hHhi : (H : ℝ) ≤ 2 * (Q : ℝ) ^ α := by
      have : (H : ℝ) < (Q : ℝ) ^ α + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hQ0.le α)
      linarith
    have hd := abs_mertensM_two_mul_sub_le (Q := Q) hH1
    have hEQ : Real.sqrt (moebiusWindowEnergy α Q) ≤
        Real.sqrt C * (Q : ℝ) ^ ((1 + 2 * α - δ) / 2) := by
      rw [show (Q : ℝ) ^ ((1 + 2 * α - δ) / 2) = Real.sqrt ((Q : ℝ) ^ (1 + 2 * α - δ)) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQ0.le]; ring_nf, ← Real.sqrt_mul hC]
      exact Real.sqrt_le_sqrt (hE Q hQ)
    have h1 : Real.sqrt Q * Real.sqrt (moebiusWindowEnergy α Q) / H ≤
        Real.sqrt C * (Q : ℝ) ^ (1 - δ / 2) := by
      rw [div_le_iff₀ (by linarith)]
      calc Real.sqrt Q * Real.sqrt (moebiusWindowEnergy α Q)
          ≤ Real.sqrt Q * (Real.sqrt C * (Q : ℝ) ^ ((1 + 2 * α - δ) / 2)) :=
            mul_le_mul_of_nonneg_left hEQ (Real.sqrt_nonneg _)
        _ = Real.sqrt C * (Q : ℝ) ^ (1 - δ / 2) * (Q : ℝ) ^ α := by
            rw [Real.sqrt_eq_rpow, mul_left_comm, mul_assoc, ← Real.rpow_add hQ0,
              ← Real.rpow_add hQ0]
            congr 2
            ring
        _ ≤ Real.sqrt C * (Q : ℝ) ^ (1 - δ / 2) * H :=
            mul_le_mul_of_nonneg_left hHlo (by positivity)
    have h2 : Real.sqrt C * (Q : ℝ) ^ (1 - δ / 2) ≤ Real.sqrt C * (Q : ℝ) ^ γ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQR (le_max_left _ _))
        (Real.sqrt_nonneg _)
    have h3 : 2 * (H : ℝ) ≤ 4 * (Q : ℝ) ^ γ := by
      have := Real.rpow_le_rpow_of_exponent_le hQR (le_max_right (1 - δ / 2) α)
      linarith
    have hd' : |mertensM (2 * Q) - mertensM Q| ≤
        Real.sqrt Q * Real.sqrt (moebiusWindowEnergy α Q) / H + 2 * H := hd
    simp only [B]
    linarith
  -- halving induction: `|M(N)| ≤ K (N+1)^γ`
  have hgap : 0 < (3 / 2 : ℝ) ^ γ - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3 / 2) hγ0; linarith
  set K := max 1 ((B + 1) / ((3 / 2 : ℝ) ^ γ - 1))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKB : B + 1 ≤ K * ((3 / 2 : ℝ) ^ γ - 1) := by
    rw [← div_le_iff₀ hgap]; exact le_max_right _ _
  have hB0 : 0 ≤ B := by positivity
  have hind : ∀ N : ℕ, |mertensM N| ≤ K * ((N : ℝ) + 1) ^ γ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      have hN1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ γ := Real.one_le_rpow (by linarith [N.cast_nonneg' (α := ℝ)]) hγ0.le
      rcases Nat.lt_or_ge N 2 with hN | hN
      · have := abs_mertensM_le N
        have hNR : (N : ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
        nlinarith
      · set Q := N / 2
        have hQ1 : 1 ≤ Q := by omega
        have hQN : Q < N := by omega
        have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
        have hr : |mertensM N - mertensM (2 * Q)| ≤ 1 := by
          have h := abs_mertensM_add_sub_le (2 * Q) (N % 2)
          rw [show 2 * Q + N % 2 = N by omega] at h
          have : ((N % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : N % 2 ≤ 1)
          linarith
        have hih := ih Q hQN
        have hst := hstep Q hQ1
        have hgrow : (3 / 2 : ℝ) ^ γ * ((Q : ℝ) + 1) ^ γ ≤ ((N : ℝ) + 1) ^ γ := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          refine Real.rpow_le_rpow (by positivity) ?_ hγ0.le
          have : (2 * Q : ℕ) ≤ N := by omega
          have h' : ((2 * Q : ℕ) : ℝ) ≤ N := by exact_mod_cast this
          push_cast at h'
          linarith
        have hQγ : (Q : ℝ) ^ γ ≤ ((Q : ℝ) + 1) ^ γ :=
          Real.rpow_le_rpow (by positivity) (by linarith) hγ0.le
        have hQ1γ : 1 ≤ ((Q : ℝ) + 1) ^ γ := Real.one_le_rpow (by linarith) hγ0.le
        have htri : |mertensM N| ≤ 1 + B * (Q : ℝ) ^ γ + K * ((Q : ℝ) + 1) ^ γ := by
          have := abs_add_three (mertensM N - mertensM (2 * Q)) (mertensM (2 * Q) - mertensM Q)
            (mertensM Q)
          rw [show mertensM N - mertensM (2 * Q) + (mertensM (2 * Q) - mertensM Q) + mertensM Q =
            mertensM N by ring] at this
          linarith
        have hfin : 1 + B * (Q : ℝ) ^ γ + K * ((Q : ℝ) + 1) ^ γ ≤
            K * ((3 / 2 : ℝ) ^ γ * ((Q : ℝ) + 1) ^ γ) := by
          have hb := mul_le_mul_of_nonneg_right hKB (by positivity : (0 : ℝ) ≤ ((Q : ℝ) + 1) ^ γ)
          nlinarith
        have hK0 : 0 ≤ K := by linarith
        calc |mertensM N| ≤ K * ((3 / 2 : ℝ) ^ γ * ((Q : ℝ) + 1) ^ γ) := htri.trans hfin
          _ ≤ K * ((N : ℝ) + 1) ^ γ := mul_le_mul_of_nonneg_left hgrow hK0
  -- the absolute-moment exponent law
  have hsum : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖ ≤
      K * ((X : ℝ) + 1) ^ (1 + γ) := by
    intro X
    calc ∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖
        ≤ ∑ _k ∈ range (X + 1), K * ((X : ℝ) + 1) ^ γ := by
          refine sum_le_sum fun k hk => ?_
          rw [norm_mobiusMertensPartialSum_eq]
          refine (hind k).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
          have : (k : ℝ) ≤ X := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
          exact Real.rpow_le_rpow (by positivity) (by linarith) hγ0.le
      _ = K * ((X : ℝ) + 1) ^ (1 + γ) := by
          rw [sum_const, card_range, nsmul_eq_mul, Real.rpow_one_add' (by positivity)
            (by linarith)]
          push_cast; ring
  have := zetaZeroAbscissa_le_of_sum_norm_mertens_le (by linarith : (1 : ℝ) ≤ 1 + γ) hsum
  linarith

/-- **Short-window Möbius saving is the quasi-Riemann hypothesis.** A power saving for `μ` in almost
all windows of one power length `Q^α`, `0 < α < 1`, holds if and only if `ζ` has a zero-free strip
`Re s > Θ` with `Θ < 1`. -/
theorem moebiusPowerWindowSaving_iff : MoebiusPowerWindowSaving ↔ zetaZeroAbscissa < 1 :=
  ⟨zetaZeroAbscissa_lt_one_of_moebiusPowerWindowSaving, moebiusPowerWindowSaving_of_lt_one⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
