import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeTowerTailMass
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeWindowScales
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePolynomialScales
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeMoments

/-!
# A terminal contrast reads the completed receiving tail

The pointwise tower error needs only the first harmonic incidence moment
against a bounded contrast. On the two terminal polynomial windows the
logarithmic ramp is linear; exact pole neutrality removes its constant part.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

/-- The bounded tower, prime-Mertens and quotient-floor errors in the receiving ramp. -/
def primeChargeRampErrorConstant : ℝ :=
  primeTowerTailMassConstant + 8 +
    2 * |(Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)| + Real.log 2

theorem primeChargeRampErrorConstant_nonneg : 0 ≤ primeChargeRampErrorConstant := by
  have h := primeTowerTailMassConstant_nonneg
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold primeChargeRampErrorConstant
  positivity

/-- The first harmonic incidence moment is controlled by the reciprocal-prime mass. -/
theorem primeDivisorCount_harmonic_first_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, primeDivisorCount P n / (n : ℝ)) ≤
      harmonicMass N * ∑ p ∈ P, 1 / (p : ℝ) := by
  have h := (primeDivisorHarmonicMean_bounds hP hN).2
  rw [primeDivisorHarmonicMean, div_le_iff₀ (harmonicMass_pos hN)] at h
  exact h.trans_eq (mul_comm _ _)

theorem abs_primeChargeWindowContrast_le (A B C n : ℕ) :
    |primeChargeWindowContrast A B C n| ≤
      1 + |primeChargeWindowMass B C / primeChargeWindowMass A B| := by
  have hu : |if n ∈ Ioc B C then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  have hl : |if n ∈ Ioc A B then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  unfold primeChargeWindowContrast
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  simpa only [mul_one] using add_le_add hu
    (mul_le_mul_of_nonneg_left hl (abs_nonneg _))

/-- The finite signed tail pairing differs from its ramp only by a first-moment error. -/
theorem abs_primeChargeTail_window_sub_ramp_le {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (A B C : ℕ) (b : ℝ) :
    |(∑ n ∈ Icc 1 N,
        completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n *
          primeChargeWindowContrast A B C n / (n : ℝ)) -
      b * ∑ n ∈ Icc 1 N, max (Real.log Q + Real.log n - Real.log N) 0 *
        primeChargeWindowContrast A B C n / (n : ℝ)| ≤
      |b| * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) *
        harmonicMass N * (primeChargeRampErrorConstant +
          ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  let P := (Icc 1 Q).filter Nat.Prime
  let D := |b| * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      |(completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n -
          b * max (Real.log Q + Real.log n - Real.log N) 0) *
        primeChargeWindowContrast A B C n / (n : ℝ)| ≤
      D * ((primeChargeRampErrorConstant + primeDivisorCount P n) / (n : ℝ)) := by
    rw [abs_div, abs_mul, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    have h := abs_completedPrimeDilationTail_coherent_sub_ramp_le
      hQ (mem_Icc.mp hn).1 (mem_Icc.mp hn).2 b
    have hg := abs_primeChargeWindowContrast_le A B C n
    exact (div_le_div_of_nonneg_right
      (mul_le_mul h hg (abs_nonneg _) ((abs_nonneg _).trans h)) (Nat.cast_nonneg n)).trans_eq
        (by dsimp only [D, primeChargeRampErrorConstant, P, primeDivisorCount]; ring)
  have hid : (∑ n ∈ Icc 1 N,
      completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n *
        primeChargeWindowContrast A B C n / (n : ℝ)) -
        b * ∑ n ∈ Icc 1 N, max (Real.log Q + Real.log n - Real.log N) 0 *
          primeChargeWindowContrast A B C n / (n : ℝ) =
      ∑ n ∈ Icc 1 N,
        (completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n -
          b * max (Real.log Q + Real.log n - Real.log N) 0) *
            primeChargeWindowContrast A B C n / (n : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hid]
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        |(completedPrimeDilationTail Q (primeIncidenceCoefficients (fun _ => b)) (N / n) n -
          b * max (Real.log Q + Real.log n - Real.log N) 0) *
            primeChargeWindowContrast A B C n / (n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ D * ∑ n ∈ Icc 1 N,
        (primeChargeRampErrorConstant + primeDivisorCount P n) / (n : ℝ) := by
      rw [mul_sum]
      exact sum_le_sum hpoint
    _ = D * (primeChargeRampErrorConstant * harmonicMass N +
        ∑ n ∈ Icc 1 N, primeDivisorCount P n / (n : ℝ)) := by
      simp only [add_div, sum_add_distrib, harmonicMass, mul_sum, mul_one_div]
    _ ≤ D * (primeChargeRampErrorConstant * harmonicMass N +
        harmonicMass N * ∑ p ∈ P, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (primeDivisorCount_harmonic_first_moment_le (fun p hp => (mem_filter.mp hp).2) hN)) hD
    _ = _ := by dsimp only [D, P]; ring

/-- Even a bounded additive tower error disappears after division by the coherent normalizer. -/
theorem tendsto_primeReciprocal_add_div_primePoleScale (C : ℝ) :
    Tendsto (fun Q : ℕ =>
      (C + ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) / primePoleScale Q)
      atTop (𝓝 0) := by
  have hc := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop C
  have hs := tendsto_primeReciprocal_div_log_rpow (q := 1) zero_lt_one
  simp only [Real.rpow_one] at hs
  have h := (hc.add hs).mul tendsto_log_div_primePoleScale
  simp only [zero_add, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  have hL : Real.log (Q : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hQ)).ne'
  change (C / Real.log Q +
    (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) / Real.log Q) *
      (Real.log Q / primePoleScale Q) = _
  field_simp [hL, (primePoleScale_pos hQ).ne']

/-- On terminal polynomial windows, neutrality removes the constant part of the linear ramp. -/
theorem primeChargeWindow_ramp_pairing {X : ℕ} (hX : 2 ≤ X) (a : ℕ) :
    (∑ n ∈ Icc 1 (X ^ (a + 2)),
      max (Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ (a + 2) : ℕ)) 0 *
        primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n / (n : ℝ)) =
      ∑ n ∈ Icc 1 (X ^ (a + 2)),
        primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n *
          (Real.log n / (n : ℝ)) := by
  have hXp : 0 < X := by omega
  have hA : 0 < X ^ a := pow_pos hXp a
  have hAB : X ^ a < X ^ (a + 1) := by
    rw [pow_succ]
    nlinarith only [hX, hA]
  have hBC : X ^ (a + 1) ≤ X ^ (a + 2) := Nat.pow_le_pow_right hXp (by omega)
  have hn := primeChargeWindowContrast_harmonic_neutral hAB hBC le_rfl
  have hp (n : ℕ) :
      max (Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ (a + 2) : ℕ)) 0 *
        primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n =
      (Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ (a + 2) : ℕ)) *
        primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n := by
    by_cases hAn : X ^ a < n
    · have hl := Real.log_le_log (show (0 : ℝ) < (X ^ a : ℕ) by exact_mod_cast hA)
        (show ((X ^ a : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast hAn.le)
      have hr : 0 ≤ Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ (a + 2) : ℕ) := by
        simp only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_ofNat] at hl ⊢
        linarith only [hl]
      rw [max_eq_left hr]
    · have hlo : n ∉ Ioc (X ^ a) (X ^ (a + 1)) := fun h => hAn (mem_Ioc.mp h).1
      have hup : n ∉ Ioc (X ^ (a + 1)) (X ^ (a + 2)) := fun h =>
        hAn (hAB.trans (mem_Ioc.mp h).1)
      simp only [primeChargeWindowContrast, if_neg hlo, if_neg hup, mul_zero, sub_zero]
  calc
    _ = (∑ n ∈ Icc 1 (X ^ (a + 2)),
        primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n *
          (Real.log n / (n : ℝ))) +
        (Real.log (X ^ 2 : ℕ) - Real.log (X ^ (a + 2) : ℕ)) *
          ∑ n ∈ Icc 1 (X ^ (a + 2)),
            primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n / (n : ℝ) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro n _
      rw [hp]
      ring
    _ = _ := by rw [hn, mul_zero, add_zero]

/-- The receiving ramp has a nonzero signed pairing with the bounded terminal contrast. -/
theorem tendsto_primeChargeWindow_ramp_pairing {a : ℕ} (ha : 0 < a) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      (t / primePoleScale (X ^ 2)) *
        (∑ n ∈ Icc 1 (X ^ (a + 2)),
          max (Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ (a + 2) : ℕ)) 0 *
            primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n / (n : ℝ)) /
          Real.log (X ^ (a + 2) : ℕ)) atTop (𝓝 (t / (2 * ((a : ℝ) + 2)))) := by
  have hmass : Tendsto (fun X : ℕ => Real.log X / primePoleScale (X ^ 2))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [pow_one, Nat.cast_one, Nat.cast_ofNat] using
      tendsto_log_pow_div_primePoleScale_pow (a := 2) (by omega) 1
  have h := (hmass.mul (tendsto_primeChargeWindowContrast_log_pairing ha)).const_mul
    (t / ((a : ℝ) + 2))
  have he : (t / ((a : ℝ) + 2)) * ((1 / 2 : ℝ) * 1) = t / (2 * ((a : ℝ) + 2)) := by
    rw [div_mul_eq_div_div]
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [primeChargeWindow_ramp_pairing hX, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_ofNat]
  have hL : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  have hQ : 2 ≤ X ^ 2 := hX.trans (Nat.le_pow (by omega : 0 < 2))
  field_simp [hL, (primePoleScale_pos hQ).ne', show (a : ℝ) + 2 ≠ 0 by positivity]

private theorem harmonicMass_le_log_add_one (N : ℕ) : harmonicMass N ≤ Real.log N + 1 := by
  have h := harmonic_le_one_add_log N
  have he : (harmonic N : ℝ) = harmonicMass N := by
    simpa only [harmonicMass, one_div] using
      _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
  rw [he] at h
  linarith only [h]

/-- The finite tower, Mertens and floor errors vanish in the terminal mixed pairing. -/
theorem tendsto_primeChargeTail_window_sub_ramp {a : ℕ} (ha : 0 < a) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ((∑ n ∈ Icc 1 (X ^ (a + 2)),
          completedPrimeDilationTail (X ^ 2)
            (primeIncidenceCoefficients (fun _ => t / primePoleScale (X ^ 2)))
            (X ^ (a + 2) / n) n *
              primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n / (n : ℝ)) -
        (t / primePoleScale (X ^ 2)) *
          ∑ n ∈ Icc 1 (X ^ (a + 2)),
            max (Real.log (X ^ 2 : ℕ) + Real.log n - Real.log (X ^ (a + 2) : ℕ)) 0 *
              primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n / (n : ℝ)) /
        Real.log (X ^ (a + 2) : ℕ)) atTop (𝓝 0) := by
  have hQtop : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hNtop : Tendsto (fun X : ℕ => X ^ (a + 2)) atTop atTop := tendsto_pow_atTop (by omega)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNtop
  have hc := (tendsto_primeReciprocal_add_div_primePoleScale primeChargeRampErrorConstant).comp hQtop
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_primeChargeWindowRatio ha).abs).mul hc |>.const_mul (2 * |t|)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 1)] with X hX hL
  change 1 ≤ Real.log (X ^ (a + 2) : ℕ) at hL
  have hQ : 2 ≤ X ^ 2 := hX.trans (Nat.le_pow (by omega : 0 < 2))
  have hN : 1 ≤ X ^ (a + 2) := Nat.one_le_pow (a + 2) X (by omega)
  have hL0 : 0 < Real.log (X ^ (a + 2) : ℕ) := zero_lt_one.trans_le hL
  have h := abs_primeChargeTail_window_sub_ramp_le (by omega : 1 ≤ X ^ 2) hN
    (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) (t / primePoleScale (X ^ 2))
  have hH : harmonicMass (X ^ (a + 2)) ≤ 2 * Real.log (X ^ (a + 2) : ℕ) := by
    have hm := harmonicMass_le_log_add_one (X ^ (a + 2))
    linarith only [hm, hL]
  have hS : 0 ≤ primeChargeRampErrorConstant +
      ∑ p ∈ (Icc 1 (X ^ 2)).filter Nat.Prime, 1 / (p : ℝ) :=
    add_nonneg primeChargeRampErrorConstant_nonneg (sum_nonneg fun p _ => by positivity)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL0]
  refine (div_le_div_of_nonneg_right h hL0.le).trans ?_
  have hH' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hH
      (show 0 ≤ |t / primePoleScale (X ^ 2)| *
        (1 + |primeChargeWindowMass (X ^ (a + 1)) (X ^ (a + 2)) /
          primeChargeWindowMass (X ^ a) (X ^ (a + 1))|) by positivity)) hS
  refine (div_le_div_of_nonneg_right hH' hL0.le).trans_eq ?_
  change _ = (2 * |t|) * ((1 +
    |primeChargeWindowMass (X ^ (a + 1)) (X ^ (a + 2)) /
      primeChargeWindowMass (X ^ a) (X ^ (a + 1))|) *
      ((primeChargeRampErrorConstant +
        ∑ p ∈ (Icc 1 (X ^ 2)).filter Nat.Prime, 1 / (p : ℝ)) / primePoleScale (X ^ 2)))
  rw [abs_div, abs_of_pos (primePoleScale_pos hQ)]
  field_simp [hL0.ne', (primePoleScale_pos hQ).ne']

/-- The completed arithmetic receiving tail retains the signed charge at the critical test windows. -/
theorem tendsto_primeChargeTail_window_pairing {a : ℕ} (ha : 0 < a) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Icc 1 (X ^ (a + 2)),
        completedPrimeDilationTail (X ^ 2)
          (primeIncidenceCoefficients (fun _ => t / primePoleScale (X ^ 2)))
          (X ^ (a + 2) / n) n *
            primeChargeWindowContrast (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) n / (n : ℝ)) /
        Real.log (X ^ (a + 2) : ℕ)) atTop (𝓝 (t / (2 * ((a : ℝ) + 2)))) := by
  have h := (tendsto_primeChargeTail_window_sub_ramp ha t).add
    (tendsto_primeChargeWindow_ramp_pairing ha t)
  simp only [zero_add] at h
  convert h using 1
  funext X
  ring

#print axioms abs_primeChargeTail_window_sub_ramp_le
#print axioms tendsto_primeReciprocal_add_div_primePoleScale
#print axioms tendsto_primeChargeTail_window_pairing

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
