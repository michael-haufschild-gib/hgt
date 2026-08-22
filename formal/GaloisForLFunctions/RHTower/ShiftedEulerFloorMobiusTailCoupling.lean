import GaloisForLFunctions.RHTower.SuzukiTailSummatoryErrorTransform
import GaloisForLFunctions.RHTower.ShiftedEulerMobiusSynthesis
import GaloisForLFunctions.RHTower.Sieve.ConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.RHTower.ComplementaryPacketPowerSumEnvelope

/-!
# The shifted-Euler summatory error is a coupled floor discrepancy and Möbius tail

For `0 < ω < 1/2` the pole-subtracted shifted-Euler summatory error

```text
E_ω(X) = ∑_{n ≤ X} c_ω(n) − X^{1+ω}/((1+ω) ζ(1+2ω))
```

splits **exactly** into a signed Möbius weighting of the power-sum floor discrepancy and the
compensating tail of the Möbius Dirichlet series:

```text
E_ω(X) = ∑_{d ≤ X} μ(d) d^{-ω} R_ω(X/d)  −  X^{1+ω}/(1+ω) · ∑_{d > X} μ(d) d^{-1-2ω}.
```

Taking absolute values in the two pieces separately gives only `O_ω(X^{1-ω})`, which is the exact
ceiling recorded by the card: any critical-scale improvement must use cancellation *between* the
two coupled pieces.

* `suzukiShiftedSummatory_eq` — the Möbius divisor switch, equation (5);
* `suzukiCoupledError_eq` — Theorem A, equation (3);
* `abs_suzukiCoupledError_le` — Theorem B, equations (8)--(9).

The power-sum remainder `R_ω` and its sharp bound `|R_ω(Y)| ≤ (Y+1)^ω` are the corpus objects
`RHTower.powerSumRemainder` and `RHTower.abs_powerSumRemainder_le`.
-/

open Finset ArithmeticFunction Filter Topology

namespace RHTower

noncomputable section

/-! ## The power sum against the corpus power-sum remainder -/

theorem abs_moebiusReal_le_one (n : ℕ) : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
  rcases moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

/-- For a positive exponent the `Icc 1 N` power sum is the `range (N+1)` power sum used by
`powerSumRemainder`. -/
theorem sum_Icc_rpow_eq_range {ω : ℝ} (hω : 0 < ω) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ ω = ∑ i ∈ Finset.range (N + 1), (i : ℝ) ^ ω := by
  rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp)]
  rw [Nat.cast_zero, Real.zero_rpow (ne_of_gt hω)]
  ring

/-- Equation (1) in the corpus normalization:
`∑_{m ≤ Y} m^ω = R_ω(Y) + Y^{1+ω}/(1+ω)`. -/
theorem sum_Icc_rpow_eq_remainder {ω : ℝ} (hω : 0 < ω) (Y : ℝ) :
    ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, (m : ℝ) ^ ω
      = powerSumRemainder ω Y + Y ^ (1 + ω) / (1 + ω) := by
  rw [powerSumRemainder, sum_Icc_rpow_eq_range hω]
  ring

/-! ## The Möbius divisor switch, equation (5) -/

theorem suzukiShiftedCoefficient_eq_shiftedEuler (ω : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    suzukiShiftedCoefficient ω n = shiftedEulerCoefficient ω n := by
  rw [shiftedEulerCoefficient_eq_prod ω (by omega : n ≠ 0), suzukiShiftedCoefficient]
  refine congrArg ((n : ℝ) ^ ω * ·) (Finset.prod_congr rfl fun p _ => ?_)
  congr 2
  ring

/-- **Equation (5).**  The Möbius divisor switch for the shifted-Euler summatory function. -/
theorem suzukiShiftedSummatory_eq (ω : ℝ) (X : ℕ) :
    suzukiShiftedSummatory ω X
      = ∑ d ∈ Finset.Icc 1 X, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
          * ∑ m ∈ Finset.Icc 1 (X / d), (m : ℝ) ^ ω := by
  have hconv : ∀ n : ℕ, 1 ≤ n → suzukiShiftedCoefficient ω n
      = LSeries.convolution (fun d : ℕ => ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω))
          (fun m : ℕ => (m : ℝ) ^ ω) n := by
    intro n hn
    rw [suzukiShiftedCoefficient_eq_shiftedEuler ω hn, shiftedEulerCoefficient,
      LSeries.convolution_def]
  have hleft : suzukiShiftedSummatory ω X
      = ∑ n ∈ Finset.Icc 1 X, LSeries.convolution
          (fun d : ℕ => ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω))
          (fun m : ℕ => (m : ℝ) ^ ω) n := by
    rw [suzukiShiftedSummatory]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact hconv n (Finset.mem_Icc.mp hn).1
  rw [hleft, Sieve.sum_Icc_convolution_apply]

/-! ## The Möbius tail and the exact decomposition, Theorem A -/

theorem summable_moebius_shift {ω : ℝ} (hω : 0 < ω) :
    Summable (fun n : ℕ => ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω))) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + 2 * ω))) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 + 2 * ω)) :=
      Real.summable_one_div_nat_rpow.mpr (by linarith)
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  refine Summable.of_norm_bounded hbase fun n => ?_
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + 2 * ω)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  nlinarith [abs_moebiusReal_le_one n, abs_nonneg (((moebius n : ℤ) : ℝ))]

/-- The Möbius tail `∑_{d > X} μ(d) d^{−1−2ω}`. -/
def mobiusShiftTail (ω : ℝ) (X : ℕ) : ℝ :=
  ∑' i : ℕ, ((moebius (i + (X + 1)) : ℤ) : ℝ) * ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 + 2 * ω))

theorem suzukiEulerDensityConstant_eq_tsum {ω : ℝ} (hω : 0 < ω) :
    suzukiEulerDensityConstant ω
      = ∑' n : ℕ, ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω)) := by
  have hs : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hcx := ofReal_tsum_moebius_rpow hs
  have hzne : riemannZeta (((1 + 2 * ω : ℝ) : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    rw [Complex.ofReal_re]
    exact hs
  have hzeta : riemannZeta (((1 + 2 * ω : ℝ) : ℂ))
      = (((∑' n : ℕ, ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω)) : ℝ) : ℂ))⁻¹ := by
    rw [hcx, inv_inv]
  have hTne : ((∑' n : ℕ, ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω)) : ℝ) : ℂ) ≠ 0 := by
    rw [hcx]
    exact inv_ne_zero hzne
  have hre : (riemannZeta (((1 + 2 * ω : ℝ) : ℂ))).re
      = (∑' n : ℕ, ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω)) : ℝ)⁻¹ := by
    rw [hzeta, ← Complex.ofReal_inv, Complex.ofReal_re]
  have hTne' : (∑' n : ℕ, ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω)) : ℝ) ≠ 0 := by
    intro hcon
    rw [hcon] at hTne
    simp at hTne
  rw [suzukiEulerDensityConstant, hre, one_div, inv_inv]

theorem tsum_moebius_split {ω : ℝ} (hω : 0 < ω) (X : ℕ) :
    (∑' n : ℕ, ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-(1 + 2 * ω)))
      = (∑ d ∈ Finset.Icc 1 X, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω)))
        + mobiusShiftTail ω X := by
  have hsum := (summable_moebius_shift hω).sum_add_tsum_nat_add (X + 1)
  rw [mobiusShiftTail, ← hsum]
  congr 1
  rw [show Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp)]
  simp


/-- **Theorem A, equation (3).**  The pole-subtracted shifted-Euler summatory error splits
exactly into a Möbius-weighted power-sum floor discrepancy and the tail of the Möbius Dirichlet
series. -/
theorem suzukiCoupledError_eq {ω : ℝ} (hω : 0 < ω) (X : ℕ) :
    suzukiCoupledError ω X
      = (∑ d ∈ Finset.Icc 1 X, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
            * powerSumRemainder ω ((X : ℝ) / (d : ℝ)))
        - (X : ℝ) ^ (1 + ω) / (1 + ω) * mobiusShiftTail ω X := by
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hterm : ∀ d ∈ Finset.Icc 1 X,
      ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω) * ∑ m ∈ Finset.Icc 1 (X / d), (m : ℝ) ^ ω
        = ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
            * powerSumRemainder ω ((X : ℝ) / (d : ℝ))
          + (X : ℝ) ^ (1 + ω) / (1 + ω)
            * (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω))) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hsum : ∑ m ∈ Finset.Icc 1 (X / d), (m : ℝ) ^ ω
        = powerSumRemainder ω ((X : ℝ) / (d : ℝ))
          + ((X : ℝ) / (d : ℝ)) ^ (1 + ω) / (1 + ω) := by
      rw [← sum_Icc_rpow_eq_remainder hω, Nat.floor_div_eq_div]
    have hdd : (d : ℝ) ^ (-ω) * ((X : ℝ) / (d : ℝ)) ^ (1 + ω)
        = (X : ℝ) ^ (1 + ω) * (d : ℝ) ^ (-(1 + 2 * ω)) := by
      rw [Real.div_rpow hX0 hd0.le, div_eq_mul_inv, ← Real.rpow_neg hd0.le]
      rw [show (d : ℝ) ^ (-ω) * ((X : ℝ) ^ (1 + ω) * (d : ℝ) ^ (-(1 + ω)))
          = (X : ℝ) ^ (1 + ω) * ((d : ℝ) ^ (-ω) * (d : ℝ) ^ (-(1 + ω))) by ring]
      rw [← Real.rpow_add hd0]
      congr 2
      ring
    rw [hsum]
    have hexp : ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
          * (powerSumRemainder ω ((X : ℝ) / (d : ℝ))
            + ((X : ℝ) / (d : ℝ)) ^ (1 + ω) / (1 + ω))
        = ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
            * powerSumRemainder ω ((X : ℝ) / (d : ℝ))
          + ((moebius d : ℤ) : ℝ)
            * ((d : ℝ) ^ (-ω) * ((X : ℝ) / (d : ℝ)) ^ (1 + ω)) / (1 + ω) := by
      ring
    rw [hexp, hdd]
    ring
  have hM : suzukiMainTerm ω X
      = suzukiEulerDensityConstant ω * (X : ℝ) ^ (1 + ω) / (1 + ω) := by
    rw [← suzukiMainTermReal_natCast, suzukiMainTermReal]
  have hsplit := tsum_moebius_split hω X
  have hr := suzukiEulerDensityConstant_eq_tsum hω
  have hfin : (∑ d ∈ Finset.Icc 1 X, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 + 2 * ω)))
      = suzukiEulerDensityConstant ω - mobiusShiftTail ω X := by
    rw [hr]
    linarith [hsplit]
  rw [suzukiCoupledError, suzukiShiftedSummatory_eq, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum, hfin, hM]
  ring

/-! ## Theorem B: the absolute-value ceiling -/

/-- **Theorem B, equations (8)--(9).**  Under absolute values the coupled decomposition gives
only the elementary scale `X^{1-ω}`. -/
theorem abs_suzukiCoupledError_le {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      |suzukiCoupledError ω X| ≤ C * (X : ℝ) ^ (1 - ω) := by
  have hc1 : (0 : ℝ) < 1 - 2 * ω := by linarith
  have hc2 : (0 : ℝ) < (1 + ω) * (2 * ω) := by positivity
  refine ⟨2 + 2 / (1 - 2 * ω) + 1 / ((1 + ω) * (2 * ω)), by positivity, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hXω : (0 : ℝ) < (X : ℝ) ^ ω := Real.rpow_pos_of_pos hX0 _
  have hpow_le : (X : ℝ) ^ ω ≤ (X : ℝ) ^ (1 - ω) := by
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    linarith
  have hfloor : |∑ d ∈ Finset.Icc 1 X, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
        * powerSumRemainder ω ((X : ℝ) / (d : ℝ))|
      ≤ 2 * (X : ℝ) ^ ω * (1 + (X : ℝ) ^ (1 - 2 * ω) / (1 - 2 * ω)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 X,
        |((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
          * powerSumRemainder ω ((X : ℝ) / (d : ℝ))|
          ≤ 2 * (X : ℝ) ^ ω * (d : ℝ) ^ (-(2 * ω)) := by
      intro d hd
      obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hdXR : (d : ℝ) ≤ (X : ℝ) := by exact_mod_cast hdX
      have hq1 : (1 : ℝ) ≤ (X : ℝ) / (d : ℝ) := (one_le_div hd0).mpr hdXR
      have hq0 : (0 : ℝ) ≤ (X : ℝ) / (d : ℝ) := by linarith
      have hR := abs_powerSumRemainder_le ω hω0.le hq0
      have hdouble : ((X : ℝ) / (d : ℝ) + 1) ^ ω ≤ 2 * ((X : ℝ) / (d : ℝ)) ^ ω := by
        have hle : (X : ℝ) / (d : ℝ) + 1 ≤ 2 * ((X : ℝ) / (d : ℝ)) := by linarith
        have h2 : (2 : ℝ) * ((X : ℝ) / (d : ℝ)) ≥ 0 := by linarith
        have hstep : ((X : ℝ) / (d : ℝ) + 1) ^ ω ≤ (2 * ((X : ℝ) / (d : ℝ))) ^ ω :=
          Real.rpow_le_rpow (by linarith) hle hω0.le
        have hsplit : (2 * ((X : ℝ) / (d : ℝ))) ^ ω
            = (2 : ℝ) ^ ω * ((X : ℝ) / (d : ℝ)) ^ ω :=
          Real.mul_rpow (by norm_num) hq0
        have htwo : (2 : ℝ) ^ ω ≤ 2 := by
          calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := by norm_num
        have hqω : (0 : ℝ) ≤ ((X : ℝ) / (d : ℝ)) ^ ω := Real.rpow_nonneg hq0 _
        nlinarith [hstep, hsplit.le, hsplit.ge, htwo, hqω]
      have hRq : ((X : ℝ) / (d : ℝ)) ^ ω = (X : ℝ) ^ ω * (d : ℝ) ^ (-ω) := by
        rw [Real.div_rpow hX0.le hd0.le, div_eq_mul_inv, ← Real.rpow_neg hd0.le]
      have hdω : (0 : ℝ) < (d : ℝ) ^ (-ω) := Real.rpow_pos_of_pos hd0 _
      have hmul : (d : ℝ) ^ (-ω) * (d : ℝ) ^ (-ω) = (d : ℝ) ^ (-(2 * ω)) := by
        rw [← Real.rpow_add hd0]
        congr 1
        ring
      have hRfinal : |powerSumRemainder ω ((X : ℝ) / (d : ℝ))|
          ≤ 2 * ((X : ℝ) ^ ω * (d : ℝ) ^ (-ω)) := by
        rw [← hRq]
        linarith [hR, hdouble]
      rw [abs_mul, abs_mul, abs_of_pos hdω]
      have hμ := abs_moebiusReal_le_one d
      have habs : (0 : ℝ) ≤ |powerSumRemainder ω ((X : ℝ) / (d : ℝ))| := abs_nonneg _
      calc |((moebius d : ℤ) : ℝ)| * (d : ℝ) ^ (-ω)
              * |powerSumRemainder ω ((X : ℝ) / (d : ℝ))|
          ≤ 1 * (d : ℝ) ^ (-ω) * (2 * ((X : ℝ) ^ ω * (d : ℝ) ^ (-ω))) := by
            have h1 : |((moebius d : ℤ) : ℝ)| * (d : ℝ) ^ (-ω) ≤ 1 * (d : ℝ) ^ (-ω) := by
              nlinarith [hμ, hdω.le]
            nlinarith [h1, hRfinal, habs, hdω.le, hXω.le]
        _ = 2 * (X : ℝ) ^ ω * (d : ℝ) ^ (-(2 * ω)) := by
            rw [← hmul]
            ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hhead := sum_rpow_neg_head_le (c := 2 * ω) (by linarith) (by linarith) X
    have hxw : (0 : ℝ) ≤ 2 * (X : ℝ) ^ ω := by positivity
    nlinarith [hhead, hxw]
  have htail : |(X : ℝ) ^ (1 + ω) / (1 + ω) * mobiusShiftTail ω X|
      ≤ (X : ℝ) ^ (1 + ω) / (1 + ω) * ((X : ℝ) ^ (-(2 * ω)) / (2 * ω)) := by
    have hsummable : Summable (fun i : ℕ =>
        ‖((moebius (i + (X + 1)) : ℤ) : ℝ) * ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 + 2 * ω))‖) := by
      have hshift := ((summable_moebius_shift hω0).comp_injective
        (add_left_injective (X + 1))).norm
      simpa [Function.comp_def] using hshift
    have hnormtail : |mobiusShiftTail ω X|
        ≤ ∑' i : ℕ, ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 + 2 * ω)) := by
      have h1 : ‖mobiusShiftTail ω X‖ ≤ ∑' i : ℕ,
          ‖((moebius (i + (X + 1)) : ℤ) : ℝ) * ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 + 2 * ω))‖ :=
        norm_tsum_le_tsum_norm hsummable
      refine le_trans h1 ?_
      refine Summable.tsum_le_tsum (fun i => ?_) hsummable ?_
      · have hnn : (0 : ℝ) ≤ ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 + 2 * ω)) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
        nlinarith [abs_moebiusReal_le_one (i + (X + 1)),
          abs_nonneg (((moebius (i + (X + 1)) : ℤ) : ℝ))]
      · have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + 2 * ω))) := by
          have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 + 2 * ω)) :=
            Real.summable_one_div_nat_rpow.mpr (by linarith)
          refine h.congr fun n => ?_
          rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
        exact hbase.comp_injective (add_left_injective (X + 1))
    have hgeom := tsum_add_rpow_neg_le (c := 1 + 2 * ω) (by linarith) (M := X) hX
    have hgeom' : ∑' i : ℕ, ((i + (X + 1) : ℕ) : ℝ) ^ (-(1 + 2 * ω))
        ≤ (X : ℝ) ^ (-(2 * ω)) / (2 * ω) := by
      refine le_trans hgeom ?_
      have hEq : (X : ℝ) ^ (1 - (1 + 2 * ω)) / (1 + 2 * ω - 1)
          = (X : ℝ) ^ (-(2 * ω)) / (2 * ω) := by
        congr 2 <;> ring
      exact le_of_eq hEq
    have hfac : (0 : ℝ) ≤ (X : ℝ) ^ (1 + ω) / (1 + ω) := by positivity
    rw [abs_mul, abs_of_nonneg hfac]
    exact mul_le_mul_of_nonneg_left (le_trans hnormtail hgeom') hfac
  rw [suzukiCoupledError_eq hω0 X]
  refine le_trans (abs_sub _ _) ?_
  have hpow1 : (X : ℝ) ^ ω * ((X : ℝ) ^ (1 - 2 * ω) / (1 - 2 * ω))
      = (X : ℝ) ^ (1 - ω) / (1 - 2 * ω) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add hX0]
    congr 2
    ring
  have hpow2 : (X : ℝ) ^ (1 + ω) / (1 + ω) * ((X : ℝ) ^ (-(2 * ω)) / (2 * ω))
      = (X : ℝ) ^ (1 - ω) / ((1 + ω) * (2 * ω)) := by
    rw [div_mul_div_comm, ← Real.rpow_add hX0]
    congr 2
    ring
  rw [hpow2] at htail
  have hfloor' : |∑ d ∈ Finset.Icc 1 X, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ω)
        * powerSumRemainder ω ((X : ℝ) / (d : ℝ))|
      ≤ 2 * (X : ℝ) ^ (1 - ω) + 2 * ((X : ℝ) ^ (1 - ω) / (1 - 2 * ω)) := by
    refine le_trans hfloor ?_
    rw [mul_add, mul_one]
    have hkey : 2 * (X : ℝ) ^ ω * ((X : ℝ) ^ (1 - 2 * ω) / (1 - 2 * ω))
        = 2 * ((X : ℝ) ^ (1 - ω) / (1 - 2 * ω)) := by
      rw [mul_assoc, hpow1]
    rw [hkey]
    linarith [hpow_le]
  have hXpow : (0 : ℝ) < (X : ℝ) ^ (1 - ω) := Real.rpow_pos_of_pos hX0 _
  have hEq : (2 + 2 / (1 - 2 * ω) + 1 / ((1 + ω) * (2 * ω))) * (X : ℝ) ^ (1 - ω)
      = 2 * (X : ℝ) ^ (1 - ω) + 2 * ((X : ℝ) ^ (1 - ω) / (1 - 2 * ω))
        + (X : ℝ) ^ (1 - ω) / ((1 + ω) * (2 * ω)) := by
    field_simp
  rw [hEq]
  linarith [hfloor', htail]

end

end RHTower
