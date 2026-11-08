import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanNumerator
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPrincipalPart

/-!
# Exact regularization of the averaged Narain Mellin transform

The filled constant terms remove the apparent central singularity.
Two divided differences then extract the universal double pole and
its simple-pole coefficient. The latter has elementary target-height
dependence and a universal expression in xi derivatives.
-/

open Complex RHTower Set Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The entire quotient of the filled numerator by its universal zero. -/
def dividedFilledNumeratorMean (Y : Height) : ℂ → ℂ :=
  dslope (filledNumeratorMean Y) 0

theorem differentiable_dividedFilledNumeratorMean (Y : Height) :
    Differentiable ℂ (dividedFilledNumeratorMean Y) := by
  intro u
  exact (analyticAt_dslope_of_analyticAt
    ((differentiable_filledNumeratorMean Y).analyticAt 0)
    ((differentiable_filledNumeratorMean Y).analyticAt u)).differentiableAt

theorem filledNumeratorMean_eq_mul_divided
    (Y : Height) (u : ℂ) :
    filledNumeratorMean Y u = u * dividedFilledNumeratorMean Y u := by
  by_cases hu : u = 0
  · subst u
    simp only [filledNumeratorMean_zero, zero_mul]
  · rw [dividedFilledNumeratorMean, dslope_of_ne _ hu, slope_def_field,
      filledNumeratorMean_zero, sub_zero, sub_zero, mul_div_cancel₀ _ hu]

/-- The main-pole numerator with its apparent central singularity removed. -/
def narainReducedMeanMainPoleNumerator (Y Z : Height) (u : ℂ) : ℂ :=
  u * dividedFilledNumeratorMean Y u * dividedFilledNumeratorMean Z u /
    (2 * (1 + 2 * u) * xi (1 + 2 * u))

theorem narainMeanMainPoleNumerator_eq_reduced (Y Z : Height) (u : ℂ) :
    narainMeanMainPoleNumerator Y Z u = narainReducedMeanMainPoleNumerator Y Z u := by
  by_cases hu : u = 0
  · subst u
    simp [narainMeanMainPoleNumerator, narainReducedMeanMainPoleNumerator]
  · rw [narainMeanMainPoleNumerator, filledNumeratorMean_eq_mul_divided Y,
      filledNumeratorMean_eq_mul_divided Z, narainReducedMeanMainPoleNumerator]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp [hu]

/-- Only the arithmetic denominator and the endpoint `u=-1/2` remain. -/
theorem analyticAt_narainMeanMainPoleNumerator (Y Z : Height)
    {u : ℂ} (hu : (1 + 2 * u) * xi (1 + 2 * u) ≠ 0) :
    AnalyticAt ℂ (narainMeanMainPoleNumerator Y Z) u := by
  have heq : narainMeanMainPoleNumerator Y Z = narainReducedMeanMainPoleNumerator Y Z :=
    funext (narainMeanMainPoleNumerator_eq_reduced Y Z)
  rw [heq]
  have hn := (differentiable_id.mul (differentiable_dividedFilledNumeratorMean Y)).mul
    (differentiable_dividedFilledNumeratorMean Z)
  have hd := (by fun_prop : Differentiable ℂ (fun u : ℂ => 2 * (1 + 2 * u))).mul
    differentiable_xi_shift
  exact (hn.analyticAt u).div (hd.analyticAt u) (by
    rw [mul_assoc]
    exact mul_ne_zero two_ne_zero hu)

theorem narainMeanMainPoleNumerator_zero (Y Z : Height) :
    narainMeanMainPoleNumerator Y Z 0 = 0 := by
  simp [narainMeanMainPoleNumerator]

/-- The apparent pole at `s=1/2` is removable for every target pair. -/
theorem analyticAt_narainMellinMean_zero (Y Z : Height) :
    AnalyticAt ℂ (narainMellinMean Y Z) 0 := by
  have ha := analyticAt_narainMeanMainPoleNumerator Y Z (u := 0) (by norm_num [xi_one])
  have hd : AnalyticAt ℂ (fun u : ℂ => (u - 1 / 2) ^ 2) 0 := by fun_prop
  have hq := ha.div hd (by norm_num)
  apply hq.congr
  filter_upwards [isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 / 2 by norm_num)] with u hu
  have htwo : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h / 2
  symm
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hu))).mpr
  rw [narainMeanMainPoleNumerator_eq Y Z htwo]
  ring

theorem narainMellinMean_zero (Y Z : Height) :
    narainMellinMean Y Z 0 = 0 := by
  simp [narainMellinMean]

/-- The exact constant associated with the scalar logarithmic main term. -/
def narainAverageConstant (Y Z : Height) : ℂ :=
  deriv (narainMeanMainPoleNumerator Y Z) (1 / 2)

/-- The holomorphic remainder after subtracting both principal terms. -/
def narainMellinMeanRegularPart (Y Z : Height) : ℂ → ℂ :=
  slopeExt (slopeExt (narainMeanMainPoleNumerator Y Z) (1 / 2)) (1 / 2)

theorem differentiableOn_narainMeanMainPoleNumerator (Y Z : Height) :
    DifferentiableOn ℂ (narainMeanMainPoleNumerator Y Z) narainMellinRegularDomain :=
  fun _ hu => (analyticAt_narainMeanMainPoleNumerator Y Z hu).differentiableAt.differentiableWithinAt

theorem differentiableOn_narainMellinMeanRegularPart (Y Z : Height) :
    DifferentiableOn ℂ (narainMellinMeanRegularPart Y Z) narainMellinRegularDomain :=
  differentiableOn_slopeExt isOpen_narainMellinRegularDomain
    (differentiableOn_slopeExt isOpen_narainMellinRegularDomain
      (differentiableOn_narainMeanMainPoleNumerator Y Z) half_mem_narainMellinRegularDomain)
    half_mem_narainMellinRegularDomain

/-- Exact principal-part subtraction, including the target-dependent simple pole. -/
theorem narainMellinMean_principalPart (Y Z : Height)
    {u : ℂ} (hu : u ≠ 1 / 2) :
    narainMellinMean Y Z u =
      (3 / (Real.pi : ℂ)) / (u - 1 / 2) ^ 2 +
        narainAverageConstant Y Z / (u - 1 / 2) + narainMellinMeanRegularPart Y Z u := by
  have h₁ := eq_add_mul_slopeExt (f := narainMeanMainPoleNumerator Y Z) hu
  have h₂ := eq_add_mul_slopeExt (f := slopeExt (narainMeanMainPoleNumerator Y Z) (1 / 2)) hu
  rw [slopeExt_self] at h₂
  rw [h₂, narainMeanMainPoleNumerator_half] at h₁
  have hw : u - 1 / 2 ≠ 0 := sub_ne_zero.mpr hu
  have htwo : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h / 2
  calc
    _ = narainMeanMainPoleNumerator Y Z u / (u - 1 / 2) ^ 2 := by
      apply (eq_div_iff (pow_ne_zero 2 hw)).mpr
      rw [narainMeanMainPoleNumerator_eq Y Z htwo]
      ring
    _ = _ := by
      rw [h₁]
      unfold narainAverageConstant narainMellinMeanRegularPart
      generalize u - 1 / 2 = w at hw ⊢
      field_simp [hw]
      ring

/-- The simple-pole coefficient in terms of the two target derivatives and the xi derivative. -/
theorem narainAverageConstant_eq (Y Z : Height) :
    narainAverageConstant Y Z = (3 / (Real.pi : ℂ)) *
      (deriv (filledNumeratorMean Y) (1 / 2) +
        deriv (filledNumeratorMean Z) (1 / 2) - 3 -
          2 * deriv xi 2 / xi 2) := by
  have hlin := ((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2).const_add 1
  have hpoly := ((hasDerivAt_id (1 / 2 : ℂ)).mul hlin).const_mul 2
  have hxi := (xi_differentiable (1 + 2 * (1 / 2 : ℂ))).hasDerivAt.comp
    (1 / 2) hlin
  have hn := ((differentiable_filledNumeratorMean Y) (1 / 2)).hasDerivAt.mul
    ((differentiable_filledNumeratorMean Z) (1 / 2)).hasDerivAt
  have hd := hpoly.mul hxi
  have hquot := hn.div hd (by norm_num [xi_two_ne_zero])
  have heq := hquot.deriv
  change narainAverageConstant Y Z = _ at heq
  rw [heq, ← xi_one_div_xi_two, xi_one]
  norm_num [filledNumeratorMean_half]
  field_simp [xi_two_ne_zero]
  ring

/-- Differentiating the explicit constant term isolates its height dependence. -/
theorem filledNumeratorMean_deriv_half (Y : Height) :
    deriv (filledNumeratorMean Y) (1 / 2) =
      2 * (Y.val : ℂ) * xi 2 + 1 + 4 * deriv xi 1 - Complex.log (Y.val : ℂ) := by
  have hY : (Y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hlin := (hasDerivAt_id (1 / 2 : ℂ)).const_mul 2
  have ha := hlin.sub_const 1
  have hb := hlin.const_add 1
  have hp := ((hasDerivAt_id (1 / 2 : ℂ)).const_add (1 / 2)).const_cpow
    (c := (Y.val : ℂ)) (Or.inl hY)
  have hm := ((hasDerivAt_id (1 / 2 : ℂ)).const_sub (1 / 2)).const_cpow
    (c := (Y.val : ℂ)) (Or.inl hY)
  have hxi := (xi_differentiable (1 + 2 * (1 / 2 : ℂ))).hasDerivAt.comp (1 / 2) hb
  have hxj := (xi_differentiable (2 * (1 / 2 : ℂ))).hasDerivAt.comp (1 / 2) hlin
  have h := (((ha.mul hp).mul hxi).add ((hb.mul hxj).mul hm)).deriv
  change deriv (filledNumeratorMean Y) (1 / 2) = _ at h
  rw [h]
  norm_num [xi_one]
  ring

/-- All target-height dependence of the exact scalar constant is elementary. -/
theorem narainAverageConstant_explicit (Y Z : Height) :
    narainAverageConstant Y Z = (Y.val : ℂ) + (Z.val : ℂ) + (3 / (Real.pi : ℂ)) *
      (-1 + 8 * deriv xi 1 - (Real.log Y.val : ℂ) - (Real.log Z.val : ℂ) -
        2 * deriv xi 2 / xi 2) := by
  rw [narainAverageConstant_eq, filledNumeratorMean_deriv_half,
    filledNumeratorMean_deriv_half, ← Complex.ofReal_log Y.property.le,
    ← Complex.ofReal_log Z.property.le, ← xi_one_div_xi_two, xi_one]
  field_simp [xi_two_ne_zero]
  ring

#print axioms analyticAt_narainMellinMean_zero
#print axioms differentiableOn_narainMellinMeanRegularPart
#print axioms narainMellinMean_principalPart
#print axioms narainAverageConstant_explicit
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
