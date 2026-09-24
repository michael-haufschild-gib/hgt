import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Log-convexity of the theta-cusp even moments at every index

The kernel is nonnegative, so its even moment sequence is a Stieltjes moment sequence in `x ^ 2`
and Cauchy--Schwarz gives `m (k+1) ^ 2 ≤ m k * m (k+2)` at every index.  The corpus previously had
only the single instance `k = 1`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- **Log-convexity of the theta-cusp even moments.** -/
theorem thetaCuspRawEvenMoment_succ_sq_le (k : ℕ) :
    thetaCuspRawEvenMoment (k + 1) ^ 2 ≤
      thetaCuspRawEvenMoment k * thetaCuspRawEvenMoment (k + 2) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ k * Real.sqrt (thetaCuspFullSource x)
  let g : ℝ → ℝ := fun x => x ^ (k + 2) * Real.sqrt (thetaCuspFullSource x)
  have hphi : 0 ≤ᵐ[μ] thetaCuspFullSource := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (thetaCuspFullSource_pos_of_pos hx).le
  have hf_meas : AEStronglyMeasurable f μ :=
    ((( continuous_id.pow k).mul
      (Real.continuous_sqrt.comp
        contDiff_thetaCuspFullSource.continuous)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hg_meas : AEStronglyMeasurable g μ :=
    ((( continuous_id.pow (k + 2)).mul
      (Real.continuous_sqrt.comp
        contDiff_thetaCuspFullSource.continuous)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hf_sq : Integrable (fun x => f x ^ 2) μ := by
    have h := integrableOn_thetaCuspRawMoment (2 * k)
    apply h.congr
    filter_upwards [hphi] with x hx
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt hx, ← pow_mul, Nat.mul_comm]
  have hg_sq : Integrable (fun x => g x ^ 2) μ := by
    have h := integrableOn_thetaCuspRawMoment (2 * (k + 2))
    apply h.congr
    filter_upwards [hphi] with x hx
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt hx, ← pow_mul, Nat.mul_comm]
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf_meas).2 hf_sq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg_meas).2 hg_sq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) (Real.HolderConjugate.two_two) hf' hg'
  have hfg : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) =
      ∫ x in Ioi 0, x ^ (2 * (k + 1)) * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi, ae_restrict_mem measurableSet_Ioi] with x hx hxi
    dsimp [f, g]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hxi.le k) (Real.sqrt_nonneg _)),
      abs_of_nonneg (mul_nonneg (pow_nonneg hxi.le (k + 2)) (Real.sqrt_nonneg _))]
    calc
      x ^ k * √(thetaCuspFullSource x) * (x ^ (k + 2) * √(thetaCuspFullSource x)) =
          x ^ (k + (k + 2)) * (√(thetaCuspFullSource x)) ^ 2 := by
        rw [pow_add]; ring
      _ = x ^ (2 * (k + 1)) * thetaCuspFullSource x := by
        rw [Real.sq_sqrt hx]
        congr 2
        omega
  have hf2 : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x in Ioi 0, x ^ (2 * k) * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi] with x hx
    dsimp [f]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs, mul_pow,
      Real.sq_sqrt hx, ← pow_mul, Nat.mul_comm]
  have hg2 : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) =
      ∫ x in Ioi 0, x ^ (2 * (k + 2)) * thetaCuspFullSource x := by
    apply integral_congr_ae
    filter_upwards [hphi] with x hx
    dsimp [g]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs, mul_pow,
      Real.sq_sqrt hx, ← pow_mul, Nat.mul_comm]
  rw [hfg, hf2, hg2] at hcs
  have hnn : ∀ n : ℕ, 0 ≤ ∫ x in Ioi 0, x ^ (2 * n) * thetaCuspFullSource x := by
    intro n
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) (thetaCuspFullSource_pos_of_pos hx).le
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  simp only [thetaCuspRawEvenMoment]
  have h1 := hnn k
  have h2 := hnn (k + 2)
  have h3 := hnn (k + 1)
  have hsq : (Real.sqrt (∫ x in Ioi 0, x ^ (2 * k) * thetaCuspFullSource x) *
      Real.sqrt (∫ x in Ioi 0, x ^ (2 * (k + 2)) * thetaCuspFullSource x)) ^ 2 =
      (∫ x in Ioi 0, x ^ (2 * k) * thetaCuspFullSource x) *
        (∫ x in Ioi 0, x ^ (2 * (k + 2)) * thetaCuspFullSource x) := by
    rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
  nlinarith [hcs, h3, hsq,
    Real.sqrt_nonneg (∫ x in Ioi 0, x ^ (2 * k) * thetaCuspFullSource x),
    Real.sqrt_nonneg (∫ x in Ioi 0, x ^ (2 * (k + 2)) * thetaCuspFullSource x)]

end

end RHTower
