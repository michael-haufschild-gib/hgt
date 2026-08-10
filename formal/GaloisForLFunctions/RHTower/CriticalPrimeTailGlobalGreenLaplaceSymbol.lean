import GaloisForLFunctions.RHTower.XiMassCriticalGlobalPrimeTailGreen
import GaloisForLFunctions.RHTower.PerronLaplaceKernel
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog

/-!
# Laplace symbol of the global critical prime-tail Green potential

The source-fixed zero-rate Green potential has an exact safe-half-plane Laplace transform:

`Laplace(G)(z) = -canonicalEulerLogZeta(1/2+z) / z^2`,  `Re z > 1/2`.

Thus the potential constructed before any divisor is selected is literally the second causal
primitive of the canonical Euler logarithm.  Exponentiating removes every logarithm-branch choice
and recovers `riemannZeta (1/2+z)` exactly.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

namespace RHTower

noncomputable section

/-- Shifted causal linear-exponential kernel. -/
def shiftedLinearLaplaceKernel (z : ℂ) (t L : ℝ) : ℂ :=
  Set.indicator (Ioi t)
    (fun L : ℝ => ((L - t : ℝ) : ℂ) * Complex.exp (-(z * (L : ℂ)))) L

/-- Real norm companion of the shifted causal kernel. -/
def shiftedLinearExpKernel (r t L : ℝ) : ℝ :=
  Set.indicator (Ioi t)
    (fun L : ℝ => (L - t) * Real.exp (-(r * L))) L

theorem integrable_shiftedLinearLaplaceKernel
    {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    Integrable (shiftedLinearLaplaceKernel z t) := by
  let base : ℝ → ℂ := fun x => Set.indicator (Ioi (0 : ℝ))
    (fun x : ℝ => (x : ℂ) * Complex.exp (-(z * (x : ℂ)))) x
  have hreal := integrableOn_pow_mul_exp_neg_mul_Ioi hz 1
  have hbaseOn : IntegrableOn
      (fun x : ℝ => (x : ℂ) * Complex.exp (-(z * (x : ℂ)))) (Ioi 0) := by
    apply Integrable.mono' hreal
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
        Complex.norm_exp]
      simp [Complex.mul_re]
  have hbase : Integrable base := by
    dsimp only [base]
    exact (integrable_indicator_iff measurableSet_Ioi).mpr hbaseOn
  have hshift := hbase.comp_add_right (-t)
  have hscaled := hshift.const_mul (Complex.exp (-(z * (t : ℂ))))
  refine hscaled.congr ?_
  filter_upwards with L
  by_cases hL : t < L
  · have h0 : 0 < L - t := sub_pos.mpr hL
    rw [shiftedLinearLaplaceKernel, Set.indicator_of_mem (mem_Ioi.mpr hL)]
    dsimp only [base]
    rw [show L + -t = L - t by ring]
    rw [Set.indicator_of_mem (mem_Ioi.mpr h0)]
    have hexp : Complex.exp (-(z * (t : ℂ))) *
        Complex.exp (-(z * ((L - t : ℝ) : ℂ))) =
        Complex.exp (-(z * (L : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = ((L - t : ℝ) : ℂ) *
          (Complex.exp (-(z * (t : ℂ))) *
            Complex.exp (-(z * ((L - t : ℝ) : ℂ)))) := by ring
      _ = _ := by rw [hexp]
  · rw [shiftedLinearLaplaceKernel, Set.indicator_of_notMem (by simpa using hL)]
    dsimp only [base]
    rw [show L + -t = L - t by ring]
    rw [Set.indicator_of_notMem (by simpa using hL)]
    ring

theorem integral_shiftedLinearLaplaceKernel
    {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    (∫ L : ℝ, shiftedLinearLaplaceKernel z t L) =
      Complex.exp (-(z * (t : ℂ))) / z ^ 2 := by
  let base : ℝ → ℂ := fun x => Set.indicator (Ioi (0 : ℝ))
    (fun x : ℝ => (x : ℂ) * Complex.exp (-(z * (x : ℂ)))) x
  have htranslate := integral_add_right_eq_self (μ := (volume : Measure ℝ)) base (-t)
  have hpoint : (fun L : ℝ => shiftedLinearLaplaceKernel z t L) =
      fun L : ℝ => Complex.exp (-(z * (t : ℂ))) * base (L - t) := by
    funext L
    by_cases hL : t < L
    · have h0 : 0 < L - t := sub_pos.mpr hL
      rw [shiftedLinearLaplaceKernel, Set.indicator_of_mem (mem_Ioi.mpr hL)]
      dsimp only [base]
      rw [Set.indicator_of_mem (mem_Ioi.mpr h0)]
      have hexp : Complex.exp (-(z * (t : ℂ))) *
          Complex.exp (-(z * ((L - t : ℝ) : ℂ))) =
          Complex.exp (-(z * (L : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = ((L - t : ℝ) : ℂ) *
            (Complex.exp (-(z * (t : ℂ))) *
              Complex.exp (-(z * ((L - t : ℝ) : ℂ)))) := by rw [hexp]
        _ = _ := by ring
    · rw [shiftedLinearLaplaceKernel, Set.indicator_of_notMem (by simpa using hL)]
      dsimp only [base]
      rw [Set.indicator_of_notMem (by simpa using hL)]
      ring
  rw [hpoint, integral_const_mul]
  have hbase : (∫ x : ℝ, base x) = 1 / z ^ 2 := by
    dsimp only [base]
    rw [integral_indicator measurableSet_Ioi, integral_mul_exp_neg_mul_Ioi hz]
  have hshift : (∫ L : ℝ, base (L - t)) = ∫ L : ℝ, base L := by
    simpa only [sub_eq_add_neg] using htranslate
  rw [hshift, hbase]
  ring

theorem integral_shiftedLinearExpKernel
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (∫ L : ℝ, shiftedLinearExpKernel r t L) =
      Real.exp (-(r * t)) / r ^ 2 := by
  let base : ℝ → ℝ := fun x => Set.indicator (Ioi (0 : ℝ))
    (fun x : ℝ => x * Real.exp (-(r * x))) x
  have htranslate := integral_add_right_eq_self (μ := (volume : Measure ℝ)) base (-t)
  have hpoint : (fun L : ℝ => shiftedLinearExpKernel r t L) =
      fun L : ℝ => Real.exp (-(r * t)) * base (L - t) := by
    funext L
    by_cases hL : t < L
    · have h0 : 0 < L - t := sub_pos.mpr hL
      rw [shiftedLinearExpKernel, Set.indicator_of_mem (mem_Ioi.mpr hL)]
      dsimp only [base]
      rw [Set.indicator_of_mem (mem_Ioi.mpr h0)]
      have hexp : Real.exp (-(r * t)) * Real.exp (-(r * (L - t))) =
          Real.exp (-(r * L)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (L - t) * (Real.exp (-(r * t)) * Real.exp (-(r * (L - t)))) := by
          rw [hexp]
        _ = _ := by ring
    · rw [shiftedLinearExpKernel, Set.indicator_of_notMem (by simpa using hL)]
      dsimp only [base]
      rw [Set.indicator_of_notMem (by simpa using hL)]
      ring
  rw [hpoint, integral_const_mul]
  have hbase : (∫ x : ℝ, base x) = 1 / r ^ 2 := by
    dsimp only [base]
    rw [integral_indicator measurableSet_Ioi]
    convert integral_pow_mul_exp_neg_mul_Ioi hr 1 using 1 <;> norm_num [pow_one]
  have hshift : (∫ L : ℝ, base (L - t)) = ∫ L : ℝ, base L := by
    simpa only [sub_eq_add_neg] using htranslate
  rw [hshift, hbase]
  ring

/-- One Green atom has the exact second-resolvent Laplace value. -/
theorem integral_exp_mul_criticalPrimeTailZeroGreenAtom
    {z : ℂ} (hz : 0 < z.re) (n : DeningerPrimePowerIndex) :
    (∫ L : ℝ, Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenAtom n L) =
      -((criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))) / z ^ 2 := by
  have hpoint : (fun L : ℝ => Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenAtom n L) =
      fun L : ℝ => -(criticalPrimeTailAtomWeight n : ℂ) *
        shiftedLinearLaplaceKernel z (deningerPrimePowerTime n) L := by
    funext L
    by_cases hL : deningerPrimePowerTime n < L
    · rw [criticalPrimeTailZeroGreenAtom, if_pos hL,
        shiftedLinearLaplaceKernel, Set.indicator_of_mem (mem_Ioi.mpr hL)]
      ring
    · rw [criticalPrimeTailZeroGreenAtom, if_neg hL,
        shiftedLinearLaplaceKernel, Set.indicator_of_notMem (by simpa using hL)]
      ring
  rw [hpoint, integral_const_mul, integral_shiftedLinearLaplaceKernel hz]
  ring

theorem integrable_exp_mul_criticalPrimeTailZeroGreenAtom
    {z : ℂ} (hz : 0 < z.re) (n : DeningerPrimePowerIndex) :
    Integrable (fun L : ℝ => Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenAtom n L) := by
  have hkernel := integrable_shiftedLinearLaplaceKernel hz (deningerPrimePowerTime n)
  have hscaled := hkernel.const_mul (-(criticalPrimeTailAtomWeight n : ℂ))
  refine hscaled.congr ?_
  filter_upwards with L
  by_cases hL : deningerPrimePowerTime n < L
  · rw [criticalPrimeTailZeroGreenAtom, if_pos hL,
      shiftedLinearLaplaceKernel, Set.indicator_of_mem (mem_Ioi.mpr hL)]
    ring
  · rw [criticalPrimeTailZeroGreenAtom, if_neg hL,
      shiftedLinearLaplaceKernel, Set.indicator_of_notMem (by simpa using hL)]
    ring

theorem integral_norm_exp_mul_criticalPrimeTailZeroGreenAtom
    {z : ℂ} (hz : 0 < z.re) (n : DeningerPrimePowerIndex) :
    (∫ L : ℝ, ‖Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenAtom n L‖) =
      criticalPrimeTailAtomWeight n *
        Real.exp (-(z.re * deningerPrimePowerTime n)) / z.re ^ 2 := by
  have hpoint : (fun L : ℝ => ‖Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenAtom n L‖) =
      fun L : ℝ => criticalPrimeTailAtomWeight n *
        shiftedLinearExpKernel z.re (deningerPrimePowerTime n) L := by
    funext L
    by_cases hL : deningerPrimePowerTime n < L
    · have hsub : 0 ≤ L - deningerPrimePowerTime n := sub_nonneg.mpr (le_of_lt hL)
      rw [criticalPrimeTailZeroGreenAtom, if_pos hL,
        shiftedLinearExpKernel, Set.indicator_of_mem (mem_Ioi.mpr hL),
        norm_mul, Complex.norm_exp, norm_neg, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (criticalPrimeTailAtomWeight_nonneg n),
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsub]
      simp [Complex.mul_re]
      ring
    · rw [criticalPrimeTailZeroGreenAtom, if_neg hL,
        shiftedLinearExpKernel, Set.indicator_of_notMem (by simpa using hL),
        mul_zero, norm_zero]
      ring
  rw [hpoint, integral_const_mul, integral_shiftedLinearExpKernel hz]
  ring

theorem summable_integral_norm_exp_mul_criticalPrimeTailZeroGreenAtom
    {z : ℂ} (hz : 1 / 2 < z.re) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ∫ L : ℝ, ‖Complex.exp (-(z * (L : ℂ))) *
        criticalPrimeTailZeroGreenAtom n L‖) := by
  have hr : 0 < z.re := lt_trans (by norm_num) hz
  have hcoef := summable_criticalPrimeTailAtomWeight_mul_exp_neg hz
  have hscaled := hcoef.mul_right ((z.re ^ 2)⁻¹)
  refine hscaled.congr ?_
  intro n
  rw [integral_norm_exp_mul_criticalPrimeTailZeroGreenAtom hr]
  ring

/-- Critical prime-tail Dirichlet coefficient is the canonical Euler-log `LSeries` term. -/
theorem criticalPrimeTailDirichletCoefficient_eq_eulerLogTerm
    (s : ℂ) (n : DeningerPrimePowerIndex) :
    criticalPrimeTailDirichletCoefficient s n =
      LSeries.term eulerLogDirichletCoeff s (n : ℕ) := by
  have hn : (n : ℕ) ≠ 0 := ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two n.property)
  rw [criticalPrimeTailDirichletCoefficient_eq_cpow,
    LSeries.term_of_ne_zero hn, eulerLogDirichletCoeff]
  have hlog :
      Complex.log (((n : ℕ) : ℂ)) = (Real.log (n : ℕ) : ℂ) :=
    Complex.natCast_log.symm
  rw [hlog, Complex.cpow_neg]
  push_cast
  ring

/-- The subtype-indexed divided-log prime series is exactly the canonical Euler logarithm. -/
theorem tsum_criticalPrimeTailDirichletCoefficient_eq_canonicalEulerLogZeta
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : DeningerPrimePowerIndex, criticalPrimeTailDirichletCoefficient s n) =
      canonicalEulerLogZeta s := by
  have hsum := canonicalEulerLogZeta_summable hs
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hzero : (∑ n ∈ Finset.range 2,
      LSeries.term eulerLogDirichletCoeff s n) = 0 := by
    simp [Finset.sum_range_succ, LSeries.term_zero,
      LSeries.term_of_ne_zero, eulerLogDirichletCoeff_one]
  rw [hzero, zero_add] at hsplit
  rw [canonicalEulerLogZeta, LSeries]
  calc
    (∑' n : DeningerPrimePowerIndex, criticalPrimeTailDirichletCoefficient s n) =
        ∑' k : ℕ, criticalPrimeTailDirichletCoefficient s
          (natEquivDeningerPrimePowerIndex k) := by
      symm
      exact Equiv.tsum_eq natEquivDeningerPrimePowerIndex
        (criticalPrimeTailDirichletCoefficient s)
    _ = ∑' k : ℕ, LSeries.term eulerLogDirichletCoeff s (k + 2) := by
      apply tsum_congr
      intro k
      rw [criticalPrimeTailDirichletCoefficient_eq_eulerLogTerm]
      rfl
    _ = ∑' n : ℕ, LSeries.term eulerLogDirichletCoeff s n := hsplit

/-- The extracted critical coefficients are the Euler logarithm at the shifted parameter. -/
theorem tsum_criticalPrimeTailAtomWeight_mul_cexp_eq_canonicalEulerLogZeta
    {z : ℂ} (hz : 1 / 2 < z.re) :
    (∑' n : DeningerPrimePowerIndex,
      (criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))) =
      canonicalEulerLogZeta ((1 / 2 : ℂ) + z) := by
  have hs : 1 < (((1 / 2 : ℂ) + z).re) := by simp; linarith
  rw [← tsum_criticalPrimeTailDirichletCoefficient_eq_canonicalEulerLogZeta hs]
  apply tsum_congr
  intro n
  have h := criticalPrimeTail_prefactor_mul_coefficient
    ((1 / 2 : ℂ) + z) n 0
  simpa [criticalPrimeTailTransportRate] using h.symm

/-- **C42 Euler-log symbol.**  Global source Green potential has exact second-resolvent symbol. -/
theorem integral_exp_mul_criticalPrimeTailZeroGreenPotential_eq_eulerLog
    {z : ℂ} (hz : 1 / 2 < z.re) :
    (∫ L : ℝ, Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenPotential L) =
      -canonicalEulerLogZeta ((1 / 2 : ℂ) + z) / z ^ 2 := by
  let f : DeningerPrimePowerIndex → ℝ → ℂ := fun n L =>
    Complex.exp (-(z * (L : ℂ))) * criticalPrimeTailZeroGreenAtom n L
  have hr : 0 < z.re := lt_trans (by norm_num) hz
  have hFint : ∀ n, Integrable (f n) := fun n =>
    integrable_exp_mul_criticalPrimeTailZeroGreenAtom hr n
  have hsum := summable_integral_norm_exp_mul_criticalPrimeTailZeroGreenAtom hz
  rw [show (fun L : ℝ => Complex.exp (-(z * (L : ℂ))) *
      criticalPrimeTailZeroGreenPotential L) = fun L : ℝ => ∑' n, f n L by
    funext L
    rw [criticalPrimeTailZeroGreenPotential, tsum_mul_left]]
  rw [← integral_tsum_of_summable_integral_norm hFint hsum]
  dsimp only [f]
  simp_rw [integral_exp_mul_criticalPrimeTailZeroGreenAtom hr]
  rw [show (fun n : DeningerPrimePowerIndex =>
      -((criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))) / z ^ 2) =
      fun n : DeningerPrimePowerIndex =>
        ((criticalPrimeTailAtomWeight n : ℂ) *
          Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))) *
          (-1 / z ^ 2) by
    funext n
    ring]
  rw [tsum_mul_right,
    tsum_criticalPrimeTailAtomWeight_mul_cexp_eq_canonicalEulerLogZeta hz]
  ring

/-- Branch-free form: exponentiated global Green symbol is exactly zeta. -/
theorem exp_neg_sq_mul_integral_globalGreen_eq_riemannZeta
    {z : ℂ} (hz : 1 / 2 < z.re) :
    Complex.exp (-(z ^ 2 *
      (∫ L : ℝ, Complex.exp (-(z * (L : ℂ))) *
        criticalPrimeTailZeroGreenPotential L))) =
      riemannZeta ((1 / 2 : ℂ) + z) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  rw [integral_exp_mul_criticalPrimeTailZeroGreenPotential_eq_eulerLog hz]
  have harg : -(z ^ 2 *
      (-canonicalEulerLogZeta ((1 / 2 : ℂ) + z) / z ^ 2)) =
      canonicalEulerLogZeta ((1 / 2 : ℂ) + z) := by
    field_simp
  rw [harg]
  exact exp_canonicalEulerLogZeta_eq_riemannZeta (by simp; linarith)

end

end RHTower
