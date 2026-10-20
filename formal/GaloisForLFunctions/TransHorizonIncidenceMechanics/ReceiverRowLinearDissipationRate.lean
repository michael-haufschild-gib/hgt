import GaloisForLFunctions.TransHorizonIncidenceMechanics.HalfDampingDissipationLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PMCofactorRowRamanujanTruncation
import GaloisForLFunctions.BezoutValuationIncidence.PhaseUniformWindowSandwichAndQuadraticObservabilityHorizon
import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# The PM receiver row dissipates linearly at the Haar rate

The receiver row `c_Q` (the real PM cofactor row at cutoff `Q`) reads, at horizon `Q`, the damped
divisor function up to `|s_Q(n) - τ_ε(n)| ≤ ((1+ε)/ε) τ(n) Q^{-ε}`. On the linear window
`k ≤ (B+1)Q` the divisor moments `Σ τ(k) ≤ X(1 + log X)` and `Σ τ(k)² ≤ X(1 + log X)³` make this error
negligible against the window length, and the boundary values stay bounded because
`τ(k) ≪ k^{ε/2}`. The Cesàro law of the successor energy of `τ_ε` then gives the exact defect rate
of the actual receiver row:

`D̃_Q((B+1)Q; c_Q)/Q → -(B+1) R(ε)`,   `R(ε) = Σ_{e ≥ 2} (φ(e) - μ(e)) w_ε(e)² ~ ε/2`.

The receiver row inherits the Haar dissipation of `τ_ε`: on every linear trans-horizon window its
renormalized defect decreases linearly, at half the damping per unit of window as `ε → 0`.
-/

open Finset Filter Topology ArithmeticFunction Asymptotics
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- `Q^{-ε} (1 + log(cQ))³ → 0`. -/
private theorem tendsto_rpow_neg_mul_log_cube {ε c : ℝ} (hε : 0 < ε) (hc : 1 ≤ c) :
    Tendsto (fun Q : ℕ => (Q : ℝ) ^ (-ε) * (1 + Real.log (c * Q)) ^ 3) atTop (𝓝 0) := by
  have hlo : Tendsto (fun x : ℝ => Real.log x ^ (3 : ℝ) / x ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hε).tendsto_div_nhds_zero
  have h27 := (hlo.comp tendsto_natCast_atTop_atTop).const_mul 27
  rw [mul_zero] at h27
  obtain ⟨n, hn⟩ := exists_nat_ge c
  refine squeeze_zero' ?_ ?_ h27
  · filter_upwards [eventually_ge_atTop 1] with Q hQ
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have h1 : 0 ≤ 1 + Real.log (c * Q) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ c * Q by nlinarith)]
    positivity
  · filter_upwards [eventually_ge_atTop n, eventually_ge_atTop 3] with Q hQn hQ3
    have hQR : (3 : ℝ) ≤ Q := by exact_mod_cast hQ3
    have hcQ : c ≤ Q := hn.trans (by exact_mod_cast hQn)
    have hQpos : (0 : ℝ) < Q := by linarith
    have hlogQ : 1 ≤ Real.log Q := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hlogc : Real.log (c * Q) ≤ 2 * Real.log Q := by
      rw [Real.log_mul (by linarith) hQpos.ne', two_mul]
      linarith [Real.log_le_log (by linarith) hcQ]
    have hlogc0 : 0 ≤ Real.log (c * Q) := Real.log_nonneg (by nlinarith)
    have hb : (1 + Real.log (c * Q)) ^ 3 ≤ 27 * Real.log Q ^ 3 := by
      calc (1 + Real.log (c * Q)) ^ 3 ≤ (3 * Real.log Q) ^ 3 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 27 * Real.log Q ^ 3 := by ring
    have hrp : Real.log Q ^ (3 : ℝ) = Real.log Q ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    show (Q : ℝ) ^ (-ε) * (1 + Real.log (c * Q)) ^ 3 ≤ 27 * (Real.log Q ^ (3 : ℝ) / (Q : ℝ) ^ ε)
    rw [hrp, Real.rpow_neg hQpos.le, inv_mul_eq_div, mul_div_assoc']
    exact div_le_div_of_nonneg_right hb (Real.rpow_nonneg hQpos.le _)

/-- The approximation error of the receiver row at `k`: `e_Q(k) = ((1+ε)/ε) τ(k) Q^{-ε}`. -/
private def receiverError (ε : ℝ) (Q k : ℕ) : ℝ :=
  (1 + ε) / ε * (k.divisors.card : ℝ) * (Q : ℝ) ^ (-ε)

private theorem receiverError_nonneg {ε : ℝ} (hε : 0 < ε) (Q k : ℕ) : 0 ≤ receiverError ε Q k := by
  unfold receiverError; positivity

private theorem receiverError_eq (ε : ℝ) (Q k : ℕ) :
    receiverError ε Q k = (1 + ε) / ε * (Q : ℝ) ^ (-ε) * (k.divisors.card : ℝ) := by
  unfold receiverError; ring

private theorem receiverError_sq (ε : ℝ) (Q k : ℕ) :
    receiverError ε Q k ^ 2 =
      ((1 + ε) / ε) ^ 2 * ((Q : ℝ) ^ (-ε)) ^ 2 * ((k.divisors.card : ℕ) : ℝ) ^ 2 := by
  unfold receiverError; ring

/-- The error budget of the window `(B+1)Q` vanishes relative to `Q`. -/
private theorem tendsto_receiver_budget {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    Tendsto (fun Q : ℕ => 4 * ((B + 2 : ℝ) * ((1 + ε) / ε * (Q : ℝ) ^ (-ε) *
      (1 + Real.log ((B + 2) * Q)) + ((1 + ε) / ε) ^ 2 * (Q : ℝ) ^ (-ε) *
        (1 + Real.log ((B + 2) * Q)) ^ 3))) atTop (𝓝 0) := by
  set C := (1 + ε) / ε
  have hB2 : (1 : ℝ) ≤ (B : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]
  have hf := tendsto_rpow_neg_mul_log_cube hε (c := (B : ℝ) + 2) hB2
  have hf1 : Tendsto (fun Q : ℕ => (Q : ℝ) ^ (-ε) * (1 + Real.log ((B + 2) * Q))) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hf
    · filter_upwards [eventually_ge_atTop 1] with Q hQ
      have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have : 0 ≤ 1 + Real.log ((B + 2) * Q) := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (B + 2) * Q by nlinarith)]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Q) _) this
    · filter_upwards [eventually_ge_atTop 1] with Q hQ
      have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hl : 1 ≤ 1 + Real.log ((B + 2) * Q) := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ (B + 2) * Q by nlinarith)]
      have : 1 + Real.log ((B + 2) * Q) ≤ (1 + Real.log ((B + 2) * Q)) ^ 3 := by
        nlinarith [mul_le_mul hl hl zero_le_one (by linarith)]
      exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (by linarith) _)
  have h := (((hf1.const_mul C).add (hf.const_mul (C ^ 2))).const_mul ((B : ℝ) + 2)).const_mul 4
  simp only [mul_zero, add_zero] at h
  refine h.congr fun Q => ?_
  ring

/-- The gradient energies of the receiver row and of `τ_ε` on the window differ by at most the
error budget times `Q`. -/
private theorem abs_gradient_receiver_sub_le {ε : ℝ} (hε : 0 < ε) (B : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    |∑ k ∈ Icc 1 ((B + 1) * Q), ((sieveSeq Q (pmCofactorRealWeight ε Q) (k + 1) -
        sieveSeq Q (pmCofactorRealWeight ε Q) k) ^ 2 -
      (RHTower.pmPowerDampedDivisorCoeff ε (k + 1) - RHTower.pmPowerDampedDivisorCoeff ε k) ^ 2)| ≤
      Q * (4 * ((B + 2 : ℝ) * ((1 + ε) / ε * (Q : ℝ) ^ (-ε) * (1 + Real.log ((B + 2) * Q)) +
        ((1 + ε) / ε) ^ 2 * (Q : ℝ) ^ (-ε) * (1 + Real.log ((B + 2) * Q)) ^ 3))) := by
  set C := (1 + ε) / ε
  have hC : 0 ≤ C := by positivity
  set τ := RHTower.pmPowerDampedDivisorCoeff ε
  set s := sieveSeq Q (pmCofactorRealWeight ε Q)
  set e := receiverError ε Q
  set M := (B + 1) * Q
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have he0 : ∀ k, 0 ≤ e k := receiverError_nonneg hε Q
  have happ : ∀ k, 0 < k → |s k - τ k| ≤ e k :=
    fun k hk => abs_sieveSeq_pmCofactor_sub_divisorCoeff_le hε hQ hk
  -- pointwise
  have hpt : ∀ k ∈ Icc 1 M, |(s (k + 1) - s k) ^ 2 - (τ (k + 1) - τ k) ^ 2| ≤
      2 * (e (k + 1) ^ 2 + e k ^ 2) + 2 * (e (k + 1) + e k) := by
    intro k hk
    obtain ⟨hk1, -⟩ := mem_Icc.mp hk
    have a1 := happ (k + 1) (by omega)
    have a2 := happ k (by omega)
    have t1 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le (k + 1)
    have t2 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le (k + 1)
    have t3 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le k
    have t4 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le k
    set x := s (k + 1) - s k
    set y := τ (k + 1) - τ k
    have hxy : |x - y| ≤ e (k + 1) + e k := by
      rw [abs_le] at a1 a2 ⊢; simp only [x, y]; constructor <;> linarith
    have hy : |y| ≤ 1 := by rw [abs_le]; simp only [y]; constructor <;> linarith
    have hxpy : |x + y| ≤ |x - y| + 2 := by
      calc |x + y| = |(x - y) + 2 * y| := by ring_nf
        _ ≤ |x - y| + |2 * y| := abs_add_le _ _
        _ ≤ |x - y| + 2 := by rw [abs_mul]; norm_num; linarith
    rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
    have hA := he0 (k + 1)
    have hB := he0 k
    calc |x - y| * |x + y| ≤ (e (k + 1) + e k) * (e (k + 1) + e k + 2) :=
          mul_le_mul hxy (by linarith) (abs_nonneg _) (by linarith)
      _ ≤ _ := by nlinarith [sq_nonneg (e (k + 1) - e k)]
  -- shifting window sums
  have hshift : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) →
      ∑ k ∈ Icc 1 M, f (k + 1) ≤ ∑ k ∈ Icc 1 (M + 1), f k := fun f hf => by
    have : ∑ k ∈ Icc 1 M, f (k + 1) = ∑ k ∈ Icc 2 (M + 1), f k := by
      refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_ <;> intro k hk <;>
        simp only [mem_Icc] at hk ⊢ <;> omega
    rw [this]
    exact sum_le_sum_of_subset_of_nonneg (fun k hk => by simp only [mem_Icc] at hk ⊢; omega)
      fun k _ _ => hf k
  have hbase : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) →
      ∑ k ∈ Icc 1 M, f k ≤ ∑ k ∈ Icc 1 (M + 1), f k := fun f hf =>
    sum_le_sum_of_subset_of_nonneg (fun k hk => by simp only [mem_Icc] at hk ⊢; omega)
      fun k _ _ => hf k
  have hdiff : |∑ k ∈ Icc 1 M, ((s (k + 1) - s k) ^ 2 - (τ (k + 1) - τ k) ^ 2)| ≤
      4 * ∑ k ∈ Icc 1 (M + 1), e k ^ 2 + 4 * ∑ k ∈ Icc 1 (M + 1), e k := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpt).trans ?_)
    have q1 := hshift (fun k => e k ^ 2) fun k => sq_nonneg _
    have q2 := hbase (fun k => e k ^ 2) fun k => sq_nonneg _
    have q3 := hshift (fun k => e k) he0
    have q4 := hbase (fun k => e k) he0
    simp only [mul_add, sum_add_distrib, ← mul_sum]
    linarith
  -- divisor moments on the window
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ (B + 2 : ℝ) * Q := by simp only [M]; push_cast; nlinarith
  have hMpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hlogM : 1 + Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 + Real.log ((B + 2) * Q) := by
    linarith [Real.log_le_log hMpos hM1]
  have hlog0 : 0 ≤ 1 + Real.log ((M + 1 : ℕ) : ℝ) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))]
  have hrp0 : (0 : ℝ) ≤ (Q : ℝ) ^ (-ε) := Real.rpow_nonneg hQpos.le _
  have hrp1 : (Q : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQR (by linarith)
  have hsum1 : ∑ k ∈ Icc 1 (M + 1), e k ≤
      C * (Q : ℝ) ^ (-ε) * ((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) := by
    have h1 := sum_card_divisors_le (M + 1)
    have h2 : ∑ k ∈ Icc 1 (M + 1), e k =
        C * (Q : ℝ) ^ (-ε) * ∑ k ∈ Icc 1 (M + 1), (k.divisors.card : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => receiverError_eq ε Q k
    rw [h2]
    calc C * (Q : ℝ) ^ (-ε) * ∑ k ∈ Icc 1 (M + 1), (k.divisors.card : ℝ)
        ≤ C * (Q : ℝ) ^ (-ε) * (((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul hM1 hlogM hlog0 (by positivity)))
            (by positivity)
      _ = _ := by ring
  have hsum2 : ∑ k ∈ Icc 1 (M + 1), e k ^ 2 ≤
      C ^ 2 * (Q : ℝ) ^ (-ε) * ((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) ^ 3 := by
    have h1 := RHTower.Sieve.sum_card_divisors_sq_le (M + 1)
    have h2 := RHTower.Sieve.invSum_le_one_add_log (N := M + 1) (by omega)
    have h3 : 0 ≤ RHTower.Sieve.invSum (M + 1) := RHTower.Sieve.invSum_nonneg _
    have hpow : ((Q : ℝ) ^ (-ε)) ^ 2 ≤ (Q : ℝ) ^ (-ε) := by nlinarith
    have h4 : ∑ k ∈ Icc 1 (M + 1), e k ^ 2 =
        C ^ 2 * ((Q : ℝ) ^ (-ε)) ^ 2 * ∑ k ∈ Icc 1 (M + 1), ((k.divisors.card : ℕ) : ℝ) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => receiverError_sq ε Q k
    rw [h4]
    have h5 : ∑ k ∈ Icc 1 (M + 1), ((k.divisors.card : ℕ) : ℝ) ^ 2 ≤
        ((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) ^ 3 := by
      refine h1.trans (mul_le_mul hM1 ?_ (pow_nonneg h3 3) (by positivity))
      exact pow_le_pow_left₀ h3 (h2.trans hlogM) 3
    set T := ∑ k ∈ Icc 1 (M + 1), ((k.divisors.card : ℕ) : ℝ) ^ 2
    have hT0 : 0 ≤ T := sum_nonneg fun k _ => sq_nonneg (((k.divisors.card : ℕ) : ℝ))
    have k1 : C ^ 2 * ((Q : ℝ) ^ (-ε)) ^ 2 * T ≤ C ^ 2 * (Q : ℝ) ^ (-ε) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg C)) hT0
    have k2 : C ^ 2 * (Q : ℝ) ^ (-ε) * T ≤
        C ^ 2 * (Q : ℝ) ^ (-ε) * (((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) ^ 3) :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg (sq_nonneg C) hrp0)
    have k3 : C ^ 2 * (Q : ℝ) ^ (-ε) * (((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) ^ 3) =
        C ^ 2 * (Q : ℝ) ^ (-ε) * ((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) ^ 3 := by ring
    linarith
  calc _ ≤ 4 * ∑ k ∈ Icc 1 (M + 1), e k ^ 2 + 4 * ∑ k ∈ Icc 1 (M + 1), e k := hdiff
    _ ≤ 4 * (C ^ 2 * (Q : ℝ) ^ (-ε) * ((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q)) ^ 3) +
        4 * (C * (Q : ℝ) ^ (-ε) * ((B + 2 : ℝ) * Q) * (1 + Real.log ((B + 2) * Q))) := by
        linarith
    _ = _ := by ring

/-- The boundary values of the receiver row on the window stay bounded. -/
private theorem receiver_boundary_bounded {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ A : ℝ, ∀ Q : ℕ, 1 ≤ Q →
      |sieveSeq Q (pmCofactorRealWeight ε Q) ((B + 1) * Q + 1) ^ 2 -
        sieveSeq Q (pmCofactorRealWeight ε Q) 1 ^ 2| ≤ A := by
  set C := (1 + ε) / ε
  have hC : 0 ≤ C := by positivity
  obtain ⟨K, hK, hτ⟩ := RHTower.card_divisors_le_const_mul_rpow (show (0 : ℝ) < ε / 2 by positivity)
  set A := C * (K * (B + 2 : ℝ) ^ (ε / 2))
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  refine ⟨(1 + A) ^ 2 + (1 + C) ^ 2, fun Q hQ => ?_⟩
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hrp1 : (Q : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQR (by linarith)
  have hM : (((B + 1) * Q + 1 : ℕ) : ℝ) ≤ (B + 2 : ℝ) * Q := by push_cast; nlinarith
  have hdiv : (((B + 1) * Q + 1).divisors.card : ℝ) ≤
      K * (B + 2 : ℝ) ^ (ε / 2) * (Q : ℝ) ^ (ε / 2) := by
    refine (hτ _ (by omega)).trans ?_
    calc K * (((B + 1) * Q + 1 : ℕ) : ℝ) ^ (ε / 2) ≤ K * ((B + 2 : ℝ) * Q) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) hQpos.le]; ring
  have hq : (Q : ℝ) ^ (ε / 2) * (Q : ℝ) ^ (-ε) ≤ 1 := by
    rw [← Real.rpow_add hQpos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQR (by linarith)
  have he1 : receiverError ε Q ((B + 1) * Q + 1) ≤ A := by
    unfold receiverError
    calc (1 + ε) / ε * (((B + 1) * Q + 1).divisors.card : ℝ) * (Q : ℝ) ^ (-ε)
        ≤ C * (K * (B + 2 : ℝ) ^ (ε / 2) * (Q : ℝ) ^ (ε / 2)) * (Q : ℝ) ^ (-ε) := by
          gcongr
      _ = A * ((Q : ℝ) ^ (ε / 2) * (Q : ℝ) ^ (-ε)) := by simp only [A]; ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hq hA0
      _ = A := mul_one A
  have he11 : receiverError ε Q 1 ≤ C := by
    unfold receiverError
    simp only [Nat.divisors_one, card_singleton, Nat.cast_one, mul_one]
    exact mul_le_of_le_one_right hC hrp1
  have hsM := abs_sieveSeq_pmCofactor_sub_divisorCoeff_le hε hQ (show 0 < (B + 1) * Q + 1 by omega)
  have hs1 := abs_sieveSeq_pmCofactor_sub_divisorCoeff_le hε hQ one_pos
  have t1 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le ((B + 1) * Q + 1)
  have t2 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le ((B + 1) * Q + 1)
  have t3 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε.le 1
  have t4 := RHTower.pmPowerDampedDivisorCoeff_le_one hε.le 1
  have b1 : |sieveSeq Q (pmCofactorRealWeight ε Q) ((B + 1) * Q + 1)| ≤ 1 + A := by
    have := he1; unfold receiverError at this
    rw [abs_le] at hsM ⊢; constructor <;> linarith
  have b2 : |sieveSeq Q (pmCofactorRealWeight ε Q) 1| ≤ 1 + C := by
    have := he11; unfold receiverError at this
    rw [abs_le] at hs1 ⊢; constructor <;> linarith
  have q1 := pow_le_pow_left₀ (abs_nonneg _) b1 2
  have q2 := pow_le_pow_left₀ (abs_nonneg _) b2 2
  rw [sq_abs] at q1 q2
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (sieveSeq Q (pmCofactorRealWeight ε Q) 1),
    sq_nonneg (sieveSeq Q (pmCofactorRealWeight ε Q) ((B + 1) * Q + 1))]

/-- **Linear dissipation of the receiver row.** For every `ε > 0` and band `B`,
`D̃_Q((B+1)Q; c_Q)/Q → -(B+1) R(ε)` for the PM cofactor row `c_Q` read at horizon `Q`. -/
theorem tendsto_sieveRenormalizedPrefixDefect_cofactor_linear {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    Tendsto (fun Q : ℕ =>
        sieveRenormalizedPrefixDefect Q ((B + 1) * Q) (pmCofactorRealWeight ε Q) / Q)
      atTop (𝓝 (-((B : ℝ) + 1) * dampedDissipationRate ε)) := by
  set τ := RHTower.pmPowerDampedDivisorCoeff ε
  have hX : Tendsto (fun Q : ℕ => (B + 1) * Q) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega : 0 < B + 1)
  have hGτ : Tendsto (fun Q : ℕ => (∑ k ∈ Icc 1 ((B + 1) * Q), (τ (k + 1) - τ k) ^ 2) / Q) atTop
      (𝓝 (((B : ℝ) + 1) * (2 * dampedDissipationRate ε))) := by
    refine (((tendsto_mean_divisorCoeff_successor_energy hε).comp hX).const_mul
      ((B : ℝ) + 1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Q hQ
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    simp only [Function.comp_apply, τ]
    push_cast
    field_simp
  have hGdiff : Tendsto (fun Q : ℕ =>
      (∑ k ∈ Icc 1 ((B + 1) * Q), (sieveSeq Q (pmCofactorRealWeight ε Q) (k + 1) -
          sieveSeq Q (pmCofactorRealWeight ε Q) k) ^ 2) / Q -
        (∑ k ∈ Icc 1 ((B + 1) * Q), (τ (k + 1) - τ k) ^ 2) / Q) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_receiver_budget hε B)
    filter_upwards [eventually_ge_atTop 1] with Q hQ
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [Real.norm_eq_abs, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos]
    exact (abs_gradient_receiver_sub_le hε B hQ).trans_eq (mul_comm _ _)
  obtain ⟨A, hA⟩ := receiver_boundary_bounded hε B
  have hbdry : Tendsto (fun Q : ℕ => (sieveSeq Q (pmCofactorRealWeight ε Q) ((B + 1) * Q + 1) ^ 2 -
      sieveSeq Q (pmCofactorRealWeight ε Q) 1 ^ 2) / Q) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := A)).div_atTop tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1] with Q hQ
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hQpos]
    exact div_le_div_of_nonneg_right (hA Q hQ) hQpos.le
  have h := ((hbdry.sub (hGdiff.add hGτ)).div_const 2)
  rw [zero_add, show ((0 : ℝ) - ((B : ℝ) + 1) * (2 * dampedDissipationRate ε)) / 2 =
    -((B : ℝ) + 1) * dampedDissipationRate ε by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  have hpol := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary Q ((B + 1) * Q)
    (pmCofactorRealWeight ε Q)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  field_simp
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
