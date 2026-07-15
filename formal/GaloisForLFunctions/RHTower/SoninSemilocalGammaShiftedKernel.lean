import GaloisForLFunctions.RHTower.SoninSemilocalGammaLogKernel

/-!
# Shifted Gamma log kernels

The derivatives of the quarter-Gamma log kernel are finite linear combinations of the shifted
kernels with parameters `j + 1/4`.  This file supplies the analytic input for that calculation:
every shifted kernel is integrable and uniformly bounded.  The left-tail estimate uses one term of
the exponential series, so the superexponential decay is retained without a Gamma asymptotic.
-/

noncomputable section

open Complex MeasureTheory Real Set

namespace RHTower

theorem exp_neg_exp_neg_le_factorial_mul_exp_nat_mul (n : ℕ) (x : ℝ) :
    Real.exp (-Real.exp (-x)) ≤
      (Nat.factorial n : ℝ) * Real.exp ((n : ℝ) * x) := by
  have hpow := Real.pow_div_factorial_le_exp
    (x := Real.exp (-x)) (Real.exp_pos (-x)).le n
  have hpowPos : 0 < Real.exp (-x) ^ n / (Nat.factorial n : ℝ) := by
    positivity
  calc
    Real.exp (-Real.exp (-x)) = (Real.exp (Real.exp (-x)))⁻¹ := by
      rw [Real.exp_neg]
    _ ≤ (Real.exp (-x) ^ n / (Nat.factorial n : ℝ))⁻¹ := by
      exact (inv_le_inv₀ (Real.exp_pos _) hpowPos).2 hpow
    _ = (Nat.factorial n : ℝ) * Real.exp ((n : ℝ) * x) := by
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_pow,
        ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]

theorem norm_semilocalGammaShiftedKernel_le_of_nonpos
    (j : ℕ) {x : ℝ} (_hx : x ≤ 0) :
    ‖semilocalGammaLogKernel ((j : ℝ) + 1 / 4) x‖ ≤
      (Nat.factorial (j + 1) : ℝ) * Real.exp ((3 / 4 : ℝ) * x) := by
  rw [norm_semilocalGammaLogKernel]
  have hsuper := exp_neg_exp_neg_le_factorial_mul_exp_nat_mul (j + 1) x
  calc
    Real.exp (-((j : ℝ) + 1 / 4) * x) * Real.exp (-Real.exp (-x)) ≤
        Real.exp (-((j : ℝ) + 1 / 4) * x) *
          ((Nat.factorial (j + 1) : ℝ) *
            Real.exp (((j + 1 : ℕ) : ℝ) * x)) := by
      gcongr
    _ = (Nat.factorial (j + 1) : ℝ) * Real.exp ((3 / 4 : ℝ) * x) := by
      calc
        Real.exp (-((j : ℝ) + 1 / 4) * x) *
              ((Nat.factorial (j + 1) : ℝ) *
                Real.exp (((j + 1 : ℕ) : ℝ) * x)) =
            (Nat.factorial (j + 1) : ℝ) *
              (Real.exp (-((j : ℝ) + 1 / 4) * x) *
                Real.exp (((j + 1 : ℕ) : ℝ) * x)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring_nf

theorem integrable_semilocalGammaShiftedKernel (j : ℕ) :
    Integrable (semilocalGammaLogKernel ((j : ℝ) + 1 / 4)) := by
  have hleftMajorant : IntegrableOn
      (fun x : ℝ => (Nat.factorial (j + 1) : ℝ) * Real.exp ((3 / 4 : ℝ) * x))
      (Iic 0) :=
    (integrableOn_exp_mul_Iic (by norm_num) 0).const_mul _
  have hrightMajorant : IntegrableOn
      (fun x : ℝ => Real.exp (-((j : ℝ) + 1 / 4) * x)) (Ioi 0) := by
    exact integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity)) 0
  have hmeas : AEStronglyMeasurable
      (semilocalGammaLogKernel ((j : ℝ) + 1 / 4)) :=
    (continuous_semilocalGammaLogKernel _).aestronglyMeasurable
  have hleft : IntegrableOn
      (semilocalGammaLogKernel ((j : ℝ) + 1 / 4)) (Iic 0) := by
    refine hleftMajorant.mono'
      (hmeas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact norm_semilocalGammaShiftedKernel_le_of_nonpos j hx
  have hright : IntegrableOn
      (semilocalGammaLogKernel ((j : ℝ) + 1 / 4)) (Ioi 0) := by
    refine hrightMajorant.mono'
      (hmeas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_semilocalGammaLogKernel_le_of_nonneg hx.le
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hleft.union hright

theorem norm_semilocalGammaShiftedKernel_le (j : ℕ) (x : ℝ) :
    ‖semilocalGammaLogKernel ((j : ℝ) + 1 / 4) x‖ ≤
      (Nat.factorial (j + 1) : ℝ) + 1 := by
  by_cases hx : x ≤ 0
  · refine (norm_semilocalGammaShiftedKernel_le_of_nonpos j hx).trans ?_
    have hexp : Real.exp ((3 / 4 : ℝ) * x) ≤ 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hx)
    calc
      (Nat.factorial (j + 1) : ℝ) * Real.exp ((3 / 4 : ℝ) * x) ≤
          (Nat.factorial (j + 1) : ℝ) * 1 := by gcongr
      _ ≤ (Nat.factorial (j + 1) : ℝ) + 1 := by linarith
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    refine (norm_semilocalGammaLogKernel_le_of_nonneg hx0).trans ?_
    have hparam : 0 ≤ (j : ℝ) + 1 / 4 := by positivity
    have hexp : Real.exp (-((j : ℝ) + 1 / 4) * x) ≤ 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hparam) hx0)
    exact hexp.trans (by
      have hfact : (0 : ℝ) ≤ Nat.factorial (j + 1) := by positivity
      linarith)

end RHTower
