import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTailPairing

/-!
# Terminal receiving limits in every fixed coprime fibre

The transported prime tail pairs diagonally with the fixed receiving modes.
Its scalar coefficient is `t/80`; deleting finitely many primes and the
conductor-product discrepancy both disappear in the physical normalization.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory SelectiveMultiscaleArithmeticPositivity

/-- The clipped logarithmic tail at cutoff `X²` and horizon `X⁴⁰`. -/
def primeChargeTerminalRamp (X n : ℕ) : ℝ :=
  max (Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ 40 : ℕ)) 0

/-- The normalized ramp pairing in two fixed conductor coordinates. -/
def fibreTerminalRampPairing (m l X : ℕ) (t : ℝ) : ℝ :=
  (t / fibreScale m (X ^ 2)) *
    (∑ n ∈ Icc 1 (X ^ 40), primeChargeTerminalRamp X n *
      normalizedRamanujanMode m n * normalizedRamanujanMode l n *
        primeChargeWindowContrast (X ^ 38) (X ^ 39) (X ^ 40) n / (n : ℝ)) /
          Real.log (X ^ 40 : ℕ)

/-- Its scalar diagonal, with the exact coprime normalizer. -/
def fibreTerminalScalarRampPairing (m X : ℕ) (t : ℝ) : ℝ :=
  (t / fibreScale m (X ^ 2)) *
    (∑ n ∈ Icc 1 (X ^ 40), primeChargeTerminalRamp X n *
      primeChargeWindowContrast (X ^ 38) (X ^ 39) (X ^ 40) n / (n : ℝ)) /
        Real.log (X ^ 40 : ℕ)

/-- The transported completed prime tail tested against a terminal mode contrast. -/
def fibreTerminalPrimeTailPairing (m l X : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 (X ^ 40),
    completedPrimeDilationTail (X ^ 2) (fibreRestrict m (fibreCharge m (X ^ 2) t))
      (X ^ 40 / n) n * normalizedRamanujanMode m n * normalizedRamanujanMode l n *
        primeChargeWindowContrast (X ^ 38) (X ^ 39) (X ^ 40) n / (n : ℝ)) /
          Real.log (X ^ 40 : ℕ)

/-- The finite coprime normalization preserves the scalar receiving coefficient. -/
theorem tendsto_fibreTerminalScalarRampPairing {m : ℕ} (hm : 0 < m) (t : ℝ) :
    Tendsto (fun X : ℕ => fibreTerminalScalarRampPairing m X t) atTop (𝓝 (t / 80)) := by
  have hQ : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have h := (tendsto_primeChargeWindow_ramp_pairing (a := 38) (by omega) t).mul
    ((tendsto_primePoleScale_div_fibreScale hm).comp hQ)
  norm_num only [Function.comp_apply, Nat.reduceAdd, Nat.cast_ofNat, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hB : primePoleScale (X ^ 2) ≠ 0 :=
    (primePoleScale_pos (hX.trans (Nat.le_pow (by omega : 0 < 2)))).ne'
  dsimp only [fibreTerminalScalarRampPairing, primeChargeTerminalRamp]
  field_simp [hB]

/-- Fixed receiving modes are orthogonal in the limiting ramp pairing. -/
theorem tendsto_fibreTerminalRamp_sub_diagonal {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (t : ℝ) :
    Tendsto (fun X : ℕ => fibreTerminalRampPairing m l X t -
      (if m = l then 1 else 0) * fibreTerminalScalarRampPairing m X t) atTop (𝓝 0) := by
  have hQ : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hN : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hi := (((fibreScale_tendsto_atTop hm).comp hQ).const_div_atTop t).abs
  have hk := (tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_primeChargeWindowRatio (a := 38) (by omega)).abs
  have hlim := (hk.mul hi).const_mul (8 * (m : ℝ) * l)
  simp only [Function.comp_apply, abs_zero, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 1)] with X hX hL
  change 1 ≤ Real.log (X ^ 40 : ℕ) at hL
  have hL0 : 0 < Real.log (X ^ 40 : ℕ) := zero_lt_one.trans_le hL
  have hab : X ^ 38 ≤ X ^ 39 := Nat.pow_le_pow_right (by omega) (by omega)
  have hbc : X ^ 39 ≤ X ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
  have hb := abs_primeChargeWindowContrast_modeProduct_ramp_pairing_le
    hm hl hab hbc le_rfl (X ^ 2)
  have hlogQN : Real.log (X ^ 2 : ℕ) ≤ Real.log (X ^ 40 : ℕ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    nlinarith only [Real.log_natCast_nonneg X]
  have he : fibreTerminalRampPairing m l X t -
      (if m = l then 1 else 0) * fibreTerminalScalarRampPairing m X t =
      (t / fibreScale m (X ^ 2)) *
        (∑ n ∈ Icc 1 (X ^ 40), primeChargeWindowContrast (X ^ 38) (X ^ 39) (X ^ 40) n *
          ((normalizedRamanujanMode m n * normalizedRamanujanMode l n -
            (if m = l then 1 else 0)) * primeChargeTerminalRamp X n / (n : ℝ))) /
              Real.log (X ^ 40 : ℕ) := by
    unfold fibreTerminalRampPairing fibreTerminalScalarRampPairing
    simp only [mul_sum, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [he, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hL0]
  have hbound := mul_le_mul_of_nonneg_left hb (abs_nonneg (t / fibreScale m (X ^ 2)))
  refine (div_le_div_of_nonneg_right hbound hL0.le).trans ?_
  have h := mul_le_mul_of_nonneg_left hlogQN
    (show 0 ≤ |t / fibreScale m (X ^ 2)| *
      (8 * (m : ℝ) * l * (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
        primeChargeWindowMass (X ^ 38) (X ^ 39)|)) by positivity)
  refine (div_le_div_of_nonneg_right (by simpa only [mul_assoc] using h) hL0.le).trans_eq ?_
  field_simp [hL0.ne']

/-- The normalized tower error vanishes in every pair of fixed conductor modes. -/
theorem tendsto_fibreTerminalPrimeTail_sub_ramp {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (t : ℝ) :
    Tendsto (fun X : ℕ => fibreTerminalPrimeTailPairing m l X t -
      fibreTerminalRampPairing m l X t) atTop (𝓝 0) := by
  have hQ : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hN : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hB := (fibreScale_tendsto_atTop hm).comp hQ
  have hc := (tendsto_fibreReciprocal_add_div_scale hm
    (primeChargeRampErrorConstant + m)).comp hQ
  have hk := (tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_primeChargeWindowRatio (a := 38) (by omega)).abs
  have hlim := (hk.mul hc).const_mul (2 * |t| * modeBound m * modeBound l)
  simp only [Function.comp_apply, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 1),
    hB.eventually (eventually_ge_atTop 1)] with X hX hL hb
  change 1 ≤ Real.log (X ^ 40 : ℕ) at hL
  change 1 ≤ fibreScale m (X ^ 2) at hb
  have hL0 : 0 < Real.log (X ^ 40 : ℕ) := zero_lt_one.trans_le hL
  have hB0 : 0 < fibreScale m (X ^ 2) := zero_lt_one.trans_le hb
  have hbnd := abs_fibreTail_mode_window_sub_ramp_le hm hl
    (Nat.one_le_pow 2 X (by omega)) (Nat.one_le_pow 40 X (by omega))
    (X ^ 38) (X ^ 39) (X ^ 40) t
  have hH : harmonicMass (X ^ 40) ≤ 2 * Real.log (X ^ 40 : ℕ) := by
    have h := harmonic_le_one_add_log (X ^ 40)
    have he : (harmonic (X ^ 40) : ℝ) = harmonicMass (X ^ 40) := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum (X ^ 40)
    rw [he] at h
    linarith only [h, hL]
  have hS : 0 ≤ primeChargeRampErrorConstant + m +
      ∑ p ∈ (Icc 1 (X ^ 2)).filter Nat.Prime, 1 / (p : ℝ) :=
    add_nonneg (add_nonneg primeChargeRampErrorConstant_nonneg (Nat.cast_nonneg m))
      (sum_nonneg fun p _ => by positivity)
  have hM : 0 ≤ (|t / fibreScale m (X ^ 2)| * modeBound m * modeBound l) *
      (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
        primeChargeWindowMass (X ^ 38) (X ^ 39)|) := by
    have hm0 := (modeBound_pos hm).le
    have hl0 := (modeBound_pos hl).le
    positivity
  dsimp only [fibreTerminalPrimeTailPairing, fibreTerminalRampPairing, primeChargeTerminalRamp]
  rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hL0]
  refine (div_le_div_of_nonneg_right hbnd hL0.le).trans ?_
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hM) hS
  refine (div_le_div_of_nonneg_right h hL0.le).trans_eq ?_
  rw [abs_div, abs_of_pos hB0]
  field_simp [hL0.ne', hB0.ne']

/-- Every fixed coprime fibre retains exactly its own signed receiving mode. -/
theorem tendsto_fibreTerminalPrimeTailPairing {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (t : ℝ) :
    Tendsto (fun X : ℕ => fibreTerminalPrimeTailPairing m l X t)
      atTop (𝓝 ((if m = l then 1 else 0) * (t / 80))) := by
  have h := (tendsto_fibreTerminalPrimeTail_sub_ramp hm hl t).add
    ((tendsto_fibreTerminalRamp_sub_diagonal hm hl t).add
      ((tendsto_fibreTerminalScalarRampPairing hm t).const_mul (if m = l then 1 else 0)))
  simp only [zero_add] at h
  convert h using 1
  funext X
  ring

#print axioms tendsto_fibreTerminalPrimeTailPairing

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
