import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalL1TranslationGenerator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalLogKernelW1One
import GaloisForLFunctions.RHTower.Suzuki.SuzukiBoundaryLayerCutoff

/-!
# Strong `L¹` translation derivative of Suzuki's logarithmic source

The literal logarithmic source is locally a fixed finite arithmetic sum, but a sharp auxiliary
upper cutoff would create an extraneous endpoint Dirac mass.  This module instead constructs an
exact smooth compact extension below any prescribed positive horizon.  Its weak derivative is
globally integrable, its fundamental-theorem identity is exact across the countable arithmetic
cusps, and its complete translation orbit is strongly differentiable in `L¹(ℝ)`.
-/

open ArithmeticFunction Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace RHTower

/-- Smooth compact cutoff which is identically one on `[0, B]` when `B ≥ 0`. -/
def suzukiSourceHLogSmoothCutoff (B r : ℝ) : ℝ :=
  suzukiBoundaryCutoff (B + 2) 1 r

/-- Compact extension of the literal logarithmic Suzuki source below horizon `B`. -/
def suzukiSourceHLogSmoothExtension (omega B r : ℝ) : ℂ :=
  (suzukiSourceHLogSmoothCutoff B r : ℂ) *
    suzukiSourceHLogFixed omega ⌊Real.exp B⌋₊ r

/-- Exact a.e. derivative field of `suzukiSourceHLogSmoothExtension`. -/
def suzukiSourceHLogSmoothExtensionDerivative (omega B r : ℝ) : ℂ :=
  ((deriv (suzukiSourceHLogSmoothCutoff B) r : ℝ) : ℂ) *
      suzukiSourceHLogFixed omega ⌊Real.exp B⌋₊ r +
    (suzukiSourceHLogSmoothCutoff B r : ℂ) *
      suzukiSourceHLogFixedDerivative omega ⌊Real.exp B⌋₊ r

theorem suzukiSourceHLogSmoothCutoff_eq_one
    {B r : ℝ} (hB : 0 ≤ B) (hr : r ∈ Icc 0 B) :
    suzukiSourceHLogSmoothCutoff B r = 1 := by
  apply suzukiBoundaryCutoff_eq_one_of_mem_inner (by norm_num : (0 : ℝ) < 1)
  constructor <;> linarith [hr.1, hr.2]

theorem deriv_suzukiSourceHLogSmoothCutoff_eq_zero
    {B r : ℝ} (hB : 0 ≤ B) (hr : r ∈ Icc 0 B) :
    deriv (suzukiSourceHLogSmoothCutoff B) r = 0 := by
  apply deriv_suzukiBoundaryCutoff_eq_zero_of_inner (by norm_num : (0 : ℝ) < 1)
  constructor <;> linarith [hr.1, hr.2]

/-- Fixed arithmetic log source is differentiable away from the countable cusp set. -/
theorem hasDerivAt_suzukiSourceHLogFixed_of_not_mem_log_nat
    {omega r : ℝ} (homega : 1 < omega) (N : ℕ)
    (hr : r ∉ Set.range (fun n : ℕ => Real.log n)) :
    HasDerivAt (suzukiSourceHLogFixed omega N)
      (suzukiSourceHLogFixedDerivative omega N r) r := by
  have hsum := HasDerivAt.sum (u := Finset.Icc 1 N) (fun n hn =>
    (hasDerivAt_suzukiSourceGLogAtom (r := r) homega (Finset.mem_Icc.mp hn).1 (by
      intro hcusp
      apply hr
      refine ⟨n, ?_⟩
      have hn0 : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
      have hlog := congrArg Real.log hcusp
      rw [Real.log_mul (ne_of_gt hn0) (Real.exp_ne_zero _), Real.log_exp,
        Real.log_one] at hlog
      linarith)).const_mul (((suzukiShiftedCoefficient omega n : ℝ) : ℂ)))
  have heq : (∑ n ∈ Finset.Icc 1 N, fun y =>
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceGLogAtom omega n y) =
      suzukiSourceHLogFixed omega N := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [heq] at hsum
  simpa only [suzukiSourceHLogFixedDerivative] using hsum

theorem hasDerivAt_suzukiSourceHLogSmoothExtension_of_not_mem_log_nat
    {omega B r : ℝ} (homega : 1 < omega)
    (hr : r ∉ Set.range (fun n : ℕ => Real.log n)) :
    HasDerivAt (suzukiSourceHLogSmoothExtension omega B)
      (suzukiSourceHLogSmoothExtensionDerivative omega B r) r := by
  have hcut := (hasDerivAt_suzukiBoundaryCutoff (B + 2) 1 r).ofReal_comp
  have hfixed := hasDerivAt_suzukiSourceHLogFixed_of_not_mem_log_nat
    homega ⌊Real.exp B⌋₊ hr
  convert hcut.mul hfixed using 1 <;> rfl

theorem continuous_suzukiSourceHLogSmoothExtension
    {omega : ℝ} (homega : 1 < omega) (B : ℝ) :
    Continuous (suzukiSourceHLogSmoothExtension omega B) := by
  unfold suzukiSourceHLogSmoothExtension suzukiSourceHLogSmoothCutoff
  exact (Complex.continuous_ofReal.comp
      (contDiff_suzukiBoundaryCutoff (B + 2) 1).continuous).mul
    (continuous_suzukiSourceHLogFixed homega _)

theorem hasCompactSupport_suzukiSourceHLogSmoothExtension
    {omega B : ℝ} :
    HasCompactSupport (suzukiSourceHLogSmoothExtension omega B) := by
  unfold suzukiSourceHLogSmoothExtension suzukiSourceHLogSmoothCutoff
  exact ((hasCompactSupport_suzukiBoundaryCutoff (by norm_num : (0 : ℝ) < 1)).comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by simp)).mul_right

theorem integrable_suzukiSourceHLogSmoothExtension
    {omega : ℝ} (homega : 1 < omega) (B : ℝ) :
    Integrable (suzukiSourceHLogSmoothExtension omega B) :=
  (continuous_suzukiSourceHLogSmoothExtension homega B).integrable_of_hasCompactSupport
    hasCompactSupport_suzukiSourceHLogSmoothExtension

theorem locallyIntegrable_suzukiSourceHLogFixedDerivative
    {omega : ℝ} (homega : 1 < omega) (N : ℕ) :
    LocallyIntegrable (suzukiSourceHLogFixedDerivative omega N) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (intervalIntegrable_suzukiSourceHLogFixedDerivative homega N (x - 1) (x + 1))

/-- The exact derivative field of the compact source extension is globally integrable. -/
theorem integrable_suzukiSourceHLogSmoothExtensionDerivative
    {omega : ℝ} (homega : 1 < omega) (B : ℝ) :
    Integrable (suzukiSourceHLogSmoothExtensionDerivative omega B) := by
  have hcutCont : Continuous fun r : ℝ =>
      ((suzukiSourceHLogSmoothCutoff B r : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (contDiff_suzukiBoundaryCutoff (B + 2) 1).continuous
  have hcutCompact : HasCompactSupport fun r : ℝ =>
      ((suzukiSourceHLogSmoothCutoff B r : ℝ) : ℂ) := by
    have hraw := (hasCompactSupport_suzukiBoundaryCutoff (a := B + 2)
      (by norm_num : (0 : ℝ) < 1)).comp_left
        (show Complex.ofReal (0 : ℝ) = 0 by simp)
    simpa only [suzukiSourceHLogSmoothCutoff, Function.comp_def] using hraw
  have hcutDerivCont : Continuous fun r : ℝ =>
      ((deriv (suzukiSourceHLogSmoothCutoff B) r : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_deriv_suzukiBoundaryCutoff (B + 2) 1)
  have hcutDerivCompact : HasCompactSupport fun r : ℝ =>
      ((deriv (suzukiSourceHLogSmoothCutoff B) r : ℝ) : ℂ) := by
    have hraw := ((hasCompactSupport_suzukiBoundaryCutoff (a := B + 2)
      (by norm_num : (0 : ℝ) < 1)).deriv).comp_left
        (show Complex.ofReal (0 : ℝ) = 0 by simp)
    rw [show suzukiSourceHLogSmoothCutoff B =
      suzukiBoundaryCutoff (B + 2) 1 from rfl]
    simpa only [Function.comp_def] using hraw
  have hfirst : Integrable fun r : ℝ =>
      ((deriv (suzukiSourceHLogSmoothCutoff B) r : ℝ) : ℂ) *
        suzukiSourceHLogFixed omega ⌊Real.exp B⌋₊ r :=
    (hcutDerivCont.mul (continuous_suzukiSourceHLogFixed homega _)).integrable_of_hasCompactSupport
      hcutDerivCompact.mul_right
  have hsecond : Integrable fun r : ℝ =>
      ((suzukiSourceHLogSmoothCutoff B r : ℝ) : ℂ) *
        suzukiSourceHLogFixedDerivative omega ⌊Real.exp B⌋₊ r := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_suzukiSourceHLogFixedDerivative homega ⌊Real.exp B⌋₊).integrable_smul_left_of_hasCompactSupport
        hcutCont hcutCompact
  exact hfirst.add hsecond

/-- Exact global FTC identity, including intervals crossing arithmetic cusps. -/
theorem integral_suzukiSourceHLogSmoothExtensionDerivative_eq_sub
    {omega : ℝ} (homega : 1 < omega) (B p q : ℝ) :
    (∫ r in p..q, suzukiSourceHLogSmoothExtensionDerivative omega B r) =
      suzukiSourceHLogSmoothExtension omega B q -
        suzukiSourceHLogSmoothExtension omega B p := by
  apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable
    (s := Set.range (fun n : ℕ => Real.log n))
    (suzukiSourceHLogSmoothExtension omega B)
    (suzukiSourceHLogSmoothExtensionDerivative omega B)
    (Set.countable_range (fun n : ℕ => Real.log n))
    (continuous_suzukiSourceHLogSmoothExtension homega B).continuousOn
  · intro r hr
    exact hasDerivAt_suzukiSourceHLogSmoothExtension_of_not_mem_log_nat homega hr.2
  · exact (integrable_suzukiSourceHLogSmoothExtensionDerivative homega B).intervalIntegrable

/-- Strong `L¹(ℝ)` derivative of every logarithmic translation of the compact extension. -/
theorem hasDerivAt_suzukiSourceHLogSmoothExtension_translate
    {omega : ℝ} (homega : 1 < omega) (B s : ℝ) :
    HasDerivAt
      (fun t : ℝ => realL1Translate t
        (integrableToL1 (suzukiSourceHLogSmoothExtension omega B)
          (integrable_suzukiSourceHLogSmoothExtension homega B)))
      (realL1Translate s
        (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega B)
          (integrable_suzukiSourceHLogSmoothExtensionDerivative homega B))) s :=
  hasDerivAt_realL1Translate_of_integral_eq_sub _ _
    (integrable_suzukiSourceHLogSmoothExtension homega B)
    (integrable_suzukiSourceHLogSmoothExtensionDerivative homega B)
    (integral_suzukiSourceHLogSmoothExtensionDerivative_eq_sub homega B) s

/-- Below its horizon, the smooth extension is exactly Suzuki's literal logarithmic source,
including the nonpositive half-line where the source vanishes. -/
theorem suzukiSourceHLogSmoothExtension_eq_sourceHFinite_exp
    (omega : ℝ) {B r : ℝ} (hB : 0 ≤ B) (hrB : r ≤ B) :
    suzukiSourceHLogSmoothExtension omega B r =
      suzukiSourceHFinite omega (Real.exp r) := by
  by_cases hr0 : r ≤ 0
  · rw [suzukiSourceHLogSmoothExtension,
      suzukiSourceHLogFixed_eq_zero_of_nonpos omega _ hr0, mul_zero,
      suzukiSourceHFinite_exp_eq_logFixed_floor_of_le omega hrB,
      suzukiSourceHLogFixed_eq_zero_of_nonpos omega _ hr0]
  · have hr : r ∈ Icc 0 B := ⟨le_of_not_ge hr0, hrB⟩
    rw [suzukiSourceHLogSmoothExtension,
      suzukiSourceHLogSmoothCutoff_eq_one hB hr, Complex.ofReal_one, one_mul,
      ← suzukiSourceHFinite_exp_eq_logFixed_floor_of_le omega hrB]

/-- Below its horizon, the derivative of the smooth extension is exactly the local derivative
field of Suzuki's literal source. -/
theorem suzukiSourceHLogSmoothExtensionDerivative_eq_sourceHLogDerivativeBelow
    (omega : ℝ) {B r : ℝ} (hB : 0 ≤ B) (hrB : r ≤ B) :
    suzukiSourceHLogSmoothExtensionDerivative omega B r =
      suzukiSourceHLogDerivativeBelow omega B r := by
  by_cases hr0 : r ≤ 0
  · rw [suzukiSourceHLogSmoothExtensionDerivative,
      suzukiSourceHLogFixed_eq_zero_of_nonpos omega _ hr0,
      suzukiSourceHLogFixedDerivative_eq_zero_of_nonpos omega _ hr0]
    simp only [mul_zero, add_zero]
    exact (suzukiSourceHLogFixedDerivative_eq_zero_of_nonpos omega _ hr0).symm
  · have hr : r ∈ Icc 0 B := ⟨le_of_not_ge hr0, hrB⟩
    rw [suzukiSourceHLogSmoothExtensionDerivative,
      deriv_suzukiSourceHLogSmoothCutoff_eq_zero hB hr,
      suzukiSourceHLogSmoothCutoff_eq_one hB hr]
    simp [suzukiSourceHLogDerivativeBelow]

end RHTower
