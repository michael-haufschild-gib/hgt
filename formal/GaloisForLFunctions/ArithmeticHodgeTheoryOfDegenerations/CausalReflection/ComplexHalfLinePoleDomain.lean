import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceWeight
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm

/-!
# Actual complex profiles admit both half-pole moments

Unweighted and eighth-exponential square integrability on the negative
half-line give the prime-source weighted norm of the absolute value.
Weighted Cauchy–Schwarz then admits every complex Laplace weight in the
closed half-pole strip, without compact support or smoothness.
-/

noncomputable section
open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower CriticalArithmeticCorrelationTheory

/-- Squaring the weighted complex norm gives the literal exponential energy. -/
theorem norm_sq_causalLaplaceWeighted (x : ℝ) (f : ℝ → ℂ) (u : ℝ) :
    ‖causalLaplaceWeighted x f u‖ ^ 2 =
      ‖f u‖ ^ 2 * Real.exp (-(2 * Real.pi * x * u)) := by
  simp only [causalLaplaceWeighted, norm_mul, Complex.norm_exp,
    Complex.ofReal_re, Complex.neg_re, mul_pow, ← Real.exp_nat_mul]
  change Real.exp ((2 : ℝ) * (-(Real.pi * x * u))) * ‖f u‖ ^ 2 = _
  rw [show (2 : ℝ) * (-(Real.pi * x * u)) = -(2 * Real.pi * x * u) by ring,
    mul_comm]

/-- The actual half-line square domain controls the weighted norm of the modulus. -/
theorem weightedTwo_norm_of_halfLine_memLp {f : ℝ → ℂ}
    (hf2 : MemLp f 2 volume)
    (hf8 : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0) : WeightedTwo (fun u => ‖f u‖) := by
  have h2 := (memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).mp hf2
  have hw := (memLp_two_iff_integrable_sq_norm hf8.aestronglyMeasurable).mp hf8
  have h8 : Integrable (fun u => ‖f u‖ ^ 2 * Real.exp (-(8 * u))) := by
    apply hw.congr
    refine Eventually.of_forall fun u => ?_
    change ‖causalLaplaceWeighted (4 / Real.pi) f u‖ ^ 2 =
      ‖f u‖ ^ 2 * Real.exp (-(8 * u))
    rw [norm_sq_causalLaplaceWeighted,
      show 2 * Real.pi * (4 / Real.pi) = 8 by field_simp; norm_num]
  exact (exponentialSourceMass_le_of_support (Y := 0) le_rfl
    hf2.aestronglyMeasurable.norm h2 h8 (Eventually.of_forall fun u hu => by
      rw [hs u hu.le, norm_zero])).1

/-- The closed half-pole strip is admitted by the actual weighted square domain. -/
theorem integrable_complexLaplaceWeighted_of_halfLine_memLp {q : ℂ}
    (hq : |q.re| ≤ 1 / 2) {f : ℝ → ℂ}
    (hf2 : MemLp f 2 volume)
    (hf8 : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0) :
    Integrable (complexLaplaceWeighted q f) := by
  have hb (u : ℝ) : |Real.exp (q.re * u)| ≤ Real.exp (|u| / 2) := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      q.re * u ≤ |q.re * u| := le_abs_self _
      _ = |q.re| * |u| := abs_mul _ _
      _ ≤ (1 / 2) * |u| := mul_le_mul_of_nonneg_right hq (abs_nonneg _)
      _ = |u| / 2 := by ring
  have hi := (abs_integral_mul_kernel_le
    (weightedTwo_norm_of_halfLine_memLp hf2 hf8 hs)
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (q.re * u))) hb).1
  have hm : AEStronglyMeasurable (complexLaplaceWeighted q f) :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (q * (u : ℂ)))).aestronglyMeasurable.mul
      hf2.aestronglyMeasurable
  apply hi.mono' hm
  refine Eventually.of_forall fun u => ?_
  rw [complexLaplaceWeighted, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (mul_comm _ _).le

end GaloisForLFunctions.HTGeometry
