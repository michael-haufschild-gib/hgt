import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralSignChange

/-!
# Cramér's theorem: under RH, primes in every interval `(x, x + K√x log x]`

The two-window squeeze of `ChebyshevShortWindowLowerBound` gives, with `h' = h/4`,
`ψ(x+h) - ψ(x) ≥ h/2 - 16/(xh) - 2h Σ_ρ x^{β-1} min(1, Y/(|ρ||1-ρ|))`, `Y = 32x²/h²`.  Under the
Riemann hypothesis the weight is `x^{-1/2} min(1, Y/(¼+γ²))`; splitting at `S = 6x/h`, the head
counts `≤ 20(S+1)(A + log(S+6))` zeros and the tail is `≤ Y·40(A+1+log(S+4))/S`, so the zero part
is `O(√x log x)` uniformly in `h ≤ x`.  Since `0 ≤ ψ - θ ≤ C√x`, the choice `h = K√x log x`
makes `θ(x+h) > θ(x)` for all large `x`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Under RH the short-window weight is `x^{-1/2} min(1, Y/(¼ + γ²))`. -/
theorem zeroShortWeight_eq_of_riemannHypothesis (hRH : RiemannHypothesis) {x Y : ℝ}
    (q : XiZeroCopy) :
    zeroShortWeight x Y (q.1 : ℂ) = x ^ (-(1 / 2 : ℝ)) * min 1 (Y * cosWeight q) := by
  rw [zeroShortWeight, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q,
    norm_mul_one_sub_eq_inv_cosWeight hRH q, div_div_eq_mul_div, div_one]
  norm_num

/-- **The zero sum of the short window under RH.** -/
theorem tsum_zeroShortWeight_le_of_riemannHypothesis (hRH : RiemannHypothesis) {x Y S : ℝ}
    (hx : 1 ≤ x) (hY : 0 ≤ Y) (hS : 4 ≤ S) :
    ∑' q : XiZeroCopy, zeroShortWeight x Y (q.1 : ℂ)
      ≤ x ^ (-(1 / 2 : ℝ)) * (20 * (S + 1) * (xiLineTwoLogDerivConstant + Real.log (S + 6))
        + Y * lagTailBound S) := by
  classical
  set c : ℝ := x ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by linarith) _
  set g : XiZeroCopy → ℝ := fun q => zeroShortWeight x Y (q.1 : ℂ) with hg
  have hgs : Summable g := summable_zeroShortWeight hx hY
  have hg0 : ∀ q, 0 ≤ g q := fun q => zeroShortWeight_nonneg (by linarith) hY _
  have hgeq : ∀ q, g q = c * min 1 (Y * cosWeight q) := fun q =>
    zeroShortWeight_eq_of_riemannHypothesis hRH q
  set F := xiCopiesBelow S with hF
  have hsplit : ∀ q, g q = (if |zeroOrdinate q| ≤ S then g q else 0)
      + (if S < |zeroOrdinate q| then g q else 0) := by
    intro q
    by_cases hq : |zeroOrdinate q| ≤ S
    · rw [if_pos hq, if_neg (not_lt.mpr hq), add_zero]
    · rw [if_neg hq, if_pos (not_le.mp hq), zero_add]
  have hs1 : Summable (fun q => if |zeroOrdinate q| ≤ S then g q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hg0 q])
      (fun q => by split_ifs <;> simp [hg0 q]) hgs
  have hs2 : Summable (fun q => if S < |zeroOrdinate q| then g q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [hg0 q])
      (fun q => by split_ifs <;> simp [hg0 q]) hgs
  have htsum : ∑' q, g q = ∑' q, (if |zeroOrdinate q| ≤ S then g q else 0)
      + ∑' q, (if S < |zeroOrdinate q| then g q else 0) := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr hsplit
  have hhead : ∑' q, (if |zeroOrdinate q| ≤ S then g q else 0) = ∑ q ∈ F, g q := by
    rw [tsum_eq_sum (s := F) (fun q hq => by
      rw [if_neg]; intro h; exact hq ((mem_xiCopiesBelow).mpr h))]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [if_pos ((mem_xiCopiesBelow).mp hq)]
  have hheadle : ∑ q ∈ F, g q ≤ c * (F.card : ℝ) := by
    calc ∑ q ∈ F, g q ≤ ∑ q ∈ F, c := Finset.sum_le_sum fun q _ => by
          rw [hgeq q]
          exact mul_le_of_le_one_right hc0 (min_le_left _ _)
      _ = c * (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hw := summable_cosWeight hRH
  have hwt : Summable (fun q => if S < |zeroOrdinate q| then cosWeight q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [(cosWeight_pos q).le])
      (fun q => by split_ifs <;> simp [(cosWeight_pos q).le]) hw
  have htail : ∑' q, (if S < |zeroOrdinate q| then g q else 0) ≤ c * Y * lagTailBound S := by
    calc ∑' q, (if S < |zeroOrdinate q| then g q else 0)
        ≤ ∑' q, (c * Y) * (if S < |zeroOrdinate q| then cosWeight q else 0) := by
          refine hs2.tsum_le_tsum (fun q => ?_) (hwt.mul_left _)
          by_cases hq : S < |zeroOrdinate q|
          · rw [if_pos hq, if_pos hq, hgeq q, mul_assoc]
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) hc0
          · rw [if_neg hq, if_neg hq, mul_zero]
      _ = c * Y * ∑' q, (if S < |zeroOrdinate q| then cosWeight q else 0) := tsum_mul_left
      _ ≤ c * Y * lagTailBound S := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc0 hY)
          rw [lagTailBound]
          exact tsum_cosWeight_tail_le hS
  have hcard := card_xiCopiesBelow_le_log (show 0 ≤ S by linarith)
  rw [htsum, hhead]
  have : c * (F.card : ℝ)
      ≤ c * (20 * (S + 1) * (xiLineTwoLogDerivConstant + Real.log (S + 6))) :=
    mul_le_mul_of_nonneg_left hcard hc0
  nlinarith

/-- **The short-window lower bound under RH.** -/
theorem psi_add_sub_psi_ge_of_riemannHypothesis (hRH : RiemannHypothesis) {x h S : ℝ}
    (hx : 2 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hS : 4 ≤ S) :
    h / 2 - 16 / (x * h)
        - 2 * h * (x ^ (-(1 / 2 : ℝ)) * (20 * (S + 1) * (xiLineTwoLogDerivConstant
          + Real.log (S + 6)) + 32 * x ^ 2 / h ^ 2 * lagTailBound S))
      ≤ Chebyshev.psi (x + h) - Chebyshev.psi x := by
  have hmain := psi_window_ge_sub_zeroShortWeight hx (h' := h / 4) (by linarith) (by linarith) hhx
  have hY : 8 * x ^ 2 / (h * (h / 4)) = 32 * x ^ 2 / h ^ 2 := by field_simp; ring
  rw [hY] at hmain
  have hz := tsum_zeroShortWeight_le_of_riemannHypothesis hRH (x := x) (Y := 32 * x ^ 2 / h ^ 2)
    (by linarith) (by positivity) hS
  have h4 : 4 / (x * (h / 4)) = 16 / (x * h) := by field_simp; ring
  rw [h4] at hmain
  have := mul_le_mul_of_nonneg_left hz (by linarith : (0 : ℝ) ≤ 2 * h)
  linarith

/-- A gain in `θ` produces a prime. -/
theorem exists_prime_of_theta_lt {a b : ℝ} (hab : Chebyshev.theta a < Chebyshev.theta b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) ≤ b := by
  classical
  by_contra hno
  push Not at hno
  apply absurd hab
  rw [not_lt, Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
  by_cases hb : 0 ≤ b
  · have hpb : (p : ℝ) ≤ b := (Nat.le_floor_iff hb).mp hp.1.2
    have hpa : (p : ℝ) ≤ a := by
      by_contra h
      exact absurd hpb (not_le.mpr (hno p hp.2 (not_le.mp h)))
    exact Nat.le_floor hpa
  · have : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have hp0 : p = 0 := by omega
    rw [hp0]; exact Nat.zero_le _


/-- The arithmetic of the zero part: with `hS = 6x`, `u² = x`, `L ≥ 8`, the short-window zero
bound is at most `707(A+2)√x log x`. -/
theorem cramer_zero_part_le {A L u x h S T : ℝ} (hA0 : 0 ≤ A) (hL8 : 8 ≤ L) (hu8 : 8 ≤ u)
    (huu : u * u = x) (hh0 : 0 < h) (hhx : h ≤ x) (hhS : h * S = 6 * x) (hS4 : 4 ≤ S)
    {l6 : ℝ} (hl6 : l6 ≤ L) (hT : T ≤ 40 * (A + 1 + L) / S) :
    2 * h * (1 / u * (20 * (S + 1) * (A + l6) + 32 * x ^ 2 / h ^ 2 * T))
      ≤ 707 * (A + 2) * u * L := by
  have hu0 : 0 < u := by linarith
  have hS0 : 0 < S := by linarith
  have hx0 : 0 < x := by nlinarith
  have hc : 0 ≤ 2 * h * (1 / u) := by positivity
  have h1 : 20 * (S + 1) * (A + l6) ≤ 20 * (S + 1) * (A + L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : 32 * x ^ 2 / h ^ 2 * T ≤ 32 * x ^ 2 / h ^ 2 * (40 * (A + 1 + L) / S) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have hmono : 2 * h * (1 / u * (20 * (S + 1) * (A + l6) + 32 * x ^ 2 / h ^ 2 * T))
      ≤ 2 * h * (1 / u) * (20 * (S + 1) * (A + L))
        + 2 * h * (1 / u) * (32 * x ^ 2 / h ^ 2 * (40 * (A + 1 + L) / S)) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hc
    linarith [this]
  have e1 : 2 * h * (1 / u) * (20 * (S + 1) * (A + L)) = 40 * (6 * x + h) * (A + L) / u := by
    rw [← hhS]; field_simp; ring
  have e2 : 2 * h * (1 / u) * (32 * x ^ 2 / h ^ 2 * (40 * (A + 1 + L) / S))
      = 2560 / 6 * u * (A + 1 + L) := by
    have hS' : S = 6 * x / h := by field_simp; linarith
    rw [hS', ← huu]; field_simp; ring
  have e3 : 40 * (6 * x + h) * (A + L) / u ≤ 280 * u * (A + L) := by
    rw [div_le_iff₀ hu0, show 280 * u * (A + L) * u = 280 * (u * u) * (A + L) by ring, huu]
    have : 0 ≤ A + L := by linarith
    nlinarith
  have t1 : u * A ≤ u * A * L / 8 := by
    have : 0 ≤ u * A := mul_nonneg hu0.le hA0
    nlinarith
  have t2 : u ≤ u * L / 8 := by nlinarith
  have hfin : 280 * u * (A + L) + 2560 / 6 * u * (A + 1 + L) ≤ 707 * (A + 2) * u * L := by
    have : 0 ≤ u * A * L := by positivity
    nlinarith
  linarith

/-- The final comparison: `h/2` beats the zero part, the prime powers and the boundary term. -/
theorem cramer_gain_pos {A C u L : ℝ} (hA0 : 0 ≤ A) (hL8 : 8 ≤ L) (hu8 : 8 ≤ u)
    (hC : 0 ≤ C) {Z P B : ℝ} (hZ : Z ≤ 707 * (A + 2) * u * L) (hP : P ≤ C * (2 * u))
    (hB : B ≤ 1) :
    0 < 2 * (1000 * (A + 2) + 2 * C + 2) * u * L / 2 - B - Z - P := by
  have h0 : 0 ≤ (A + 2) * u * L := by positivity
  have hb2 : C * (2 * u) ≤ 2 * C * u * L := by
    have : 0 ≤ C * u := mul_nonneg hC (by linarith)
    nlinarith
  have hb3 : 2 ≤ 2 * u * L := by nlinarith
  nlinarith

/-- **Cramér's theorem (1920).**  Under the Riemann hypothesis there is `K > 0` such that every
interval `(x, x + K√x log x]` with `x` large contains a prime. -/
theorem exists_prime_in_sqrt_log_window_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + K * Real.sqrt x * Real.log x := by
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set A := xiLineTwoLogDerivConstant with hA
  have hA0 : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  set K : ℝ := 2 * (1000 * (A + 2) + 2 * |C₀| + 2) with hK
  have hK1 : 1 ≤ K := by rw [hK]; have := abs_nonneg C₀; nlinarith
  have hKpos : 0 < K := by linarith
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 8),
    eventually_log_le_mul_sqrt (show 0 < 1 / (2 * K) by positivity)] with x hx8 hlogx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx8
  have hL8 : 8 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx8
  have hx64 : 64 ≤ x := by
    have he1 := Real.exp_one_gt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he2 : 7 ≤ Real.exp 2 := by nlinarith
    have e8 : Real.exp 8 = Real.exp 2 * Real.exp 2 * (Real.exp 2 * Real.exp 2) := by
      simp only [← Real.exp_add]; norm_num
    have h49 : 49 ≤ Real.exp 2 * Real.exp 2 := by nlinarith
    have : 64 ≤ Real.exp 8 := by rw [e8]; nlinarith
    linarith
  set L := Real.log x with hLdef
  set u := Real.sqrt x with hu
  have huu : u * u = x := Real.mul_self_sqrt hx0.le
  have hu8 : 8 ≤ u := by
    rw [hu, show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx64
  set h := K * u * L with hhdef
  have hKL : K * L ≤ u / 2 := by
    have : L ≤ 1 / (2 * K) * u := hlogx
    rw [show 1 / (2 * K) * u = u / 2 / K by field_simp] at this
    rw [le_div_iff₀ hKpos] at this
    linarith
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hhx : h ≤ x / 2 := by
    rw [hhdef, ← huu]
    have := mul_le_mul_of_nonneg_left hKL (show (0 : ℝ) ≤ u by linarith)
    have e : K * u * L = u * (K * L) := by ring
    have e2 : u * (u / 2) = u * u / 2 := by ring
    linarith only [this, e, e2]
  set S := 6 * x / h with hSdef
  have hhS : h * S = 6 * x := by rw [hSdef]; field_simp
  have hS12 : 12 ≤ S := by
    rw [hSdef, le_div_iff₀ hh0]; linarith
  have hS4 : 4 ≤ S := by linarith
  have hSx : S + 6 ≤ x := by
    have hS6 : S ≤ 6 * u := by
      rw [hSdef, div_le_iff₀ hh0, hhdef, ← huu]
      have h1 : 1 ≤ K * L := by nlinarith only [hK1, hL8]
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 * u * u by positivity)
      have e : 6 * u * (K * u * L) = 6 * u * u * (K * L) := by ring
      linarith only [h2, e]
    have h3 : 6 * u + 6 ≤ u * u := by nlinarith only [hu8]
    linarith only [hS6, h3, huu]
  have hl6 : Real.log (S + 6) ≤ L := Real.log_le_log (by linarith) hSx
  have hl4 : Real.log (S + 4) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hwin := psi_add_sub_psi_ge_of_riemannHypothesis hRH (x := x) (h := h) (S := S)
    (by linarith) hh0 (by linarith) hS4
  have hxr : x ^ (-(1 / 2 : ℝ)) = 1 / u := by
    rw [Real.rpow_neg hx0.le, hu, Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [hxr, ← hA] at hwin
  have hT : lagTailBound S ≤ 40 * (A + 1 + L) / S := by
    unfold lagTailBound
    rw [← hA]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hzero := cramer_zero_part_le hA0 (by linarith) hu8 huu hh0 (by linarith) hhS hS4 hl6 hT
  have hsmall : 16 / (x * h) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    have hh1 : 1 ≤ h := by
      rw [hhdef]
      have : 1 ≤ K * L := by nlinarith only [hK1, hL8]
      nlinarith only [this, hu8]
    have : 64 ≤ x * h := by nlinarith only [hx64, hh1]
    linarith only [this]
  have hpt := hC₀ (x + h)
  have hθψ := Chebyshev.theta_le_psi x
  have hsq : Real.sqrt (x + h) ≤ 2 * u := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (2 * u) ^ 2 = 4 * x := by rw [← huu]; ring
    linarith only [this, hhx, hx0]
  have hpt' : Chebyshev.psi (x + h) - Chebyshev.theta (x + h) ≤ |C₀| * (2 * u) := by
    calc Chebyshev.psi (x + h) - Chebyshev.theta (x + h) ≤ C₀ * Real.sqrt (x + h) := hpt
      _ ≤ |C₀| * Real.sqrt (x + h) :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (Real.sqrt_nonneg _)
      _ ≤ |C₀| * (2 * u) := mul_le_mul_of_nonneg_left hsq (abs_nonneg C₀)
  have hpos := cramer_gain_pos hA0 (by linarith) hu8 (abs_nonneg C₀) hzero hpt' hsmall
  have hh2 : h / 2 = 2 * (1000 * (A + 2) + 2 * |C₀| + 2) * u * L / 2 := by
    rw [hhdef, hK]
  have hgain : Chebyshev.theta x < Chebyshev.theta (x + h) := by
    linarith only [hwin, hpos, hh2, hθψ]
  obtain ⟨p, hp, hxp, hpb⟩ := exists_prime_of_theta_lt hgain
  exact ⟨p, hp, hxp, by rw [hhdef] at hpb; linarith⟩

end

end RHTower
