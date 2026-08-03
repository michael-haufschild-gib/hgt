import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.RHTower.GelfondSchneiderProof.AnalyticPart

/-!
# Burnol co-Poisson conormal reflection cover

At a zeta zero of multiplicity `m`, the first nonzero Mellin jet of the actual
Burnol sub-window `[exp (-L), 1]` has a common nonzero divisor-conormal factor
times `exp (L * rho) - 1`.  Comparing the nested windows of lengths `L` and
`2L` cancels that common factor and recovers `exp (L * rho)` exactly.

After half-density centering, the resulting source character is uniformly
bounded and invertible on the open critical strip.  Functional-equation/Schwarz
reflection exchanges it with its conjugate inverse.  The invariant sum and
product therefore define a quadratic reflection cover whose discriminant
vanishes exactly on the critical line.

All theorems here are unconditional.  The final ramification condition is a
classification, not an assertion that it holds at every zeta zero.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact endpoint factor in the Mellin transform of the actual Burnol
sub-window `[exp (-L), 1]`. -/
def burnolCoPoissonExpWindowEndpointFactor (L : ℝ) (rho : ℂ) : ℂ :=
  (((1 : ℝ) : ℂ) ^ (-rho) -
    ((Real.exp (-L) : ℝ) : ℂ) ^ (-rho))

/-- Uncompleted Mellin germ of the literal Burnol window `[exp (-L), 1]`.
The completed Sonin evaluator differs by the common nonzero Gamma factor. -/
def burnolCoPoissonExpWindowZetaMellinGerm (L : ℝ) (w : ℂ) : ℂ :=
  riemannZeta w * ((Complex.exp ((L : ℂ) * w) - 1) / w)

/-- Exact analytic order of the zeta factor at an Xi divisor support point. -/
def burnolCoPoissonXiConormalOrder (rho : XiDivisorSupport) : ℕ :=
  (analyticOrderAt riemannZeta (rho : ℂ)).toNat

/-- Actual common leading zeta conormal at a multiplicity-exact Xi divisor,
after removing the nonzero coordinate `rho`. -/
def burnolCoPoissonXiConormalLead (rho : XiDivisorSupport) : ℂ :=
  iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) /
    (rho : ℂ)

/-- First nonzero completed Mellin conormal coefficient of the Burnol
sub-window of logarithmic length `L`, after packaging every factor common to
all window labels into `lead`. -/
def burnolCoPoissonSubWindowConormalCoefficient
    (L : ℝ) (rho lead : ℂ) : ℂ :=
  (Complex.exp ((L : ℂ) * rho) - 1) * lead

/-- Projective comparison of the nested sub-windows of lengths `L` and `2L`. -/
def burnolCoPoissonDoubledWindowConormalRatio
    (L : ℝ) (rho lead : ℂ) : ℂ :=
  burnolCoPoissonSubWindowConormalCoefficient (2 * L) rho lead /
  burnolCoPoissonSubWindowConormalCoefficient L rho lead - 1

/-- Actual projective conormal ratio of the two literal nested Burnol Mellin
germs at a multiplicity-exact Xi divisor. -/
def burnolCoPoissonActualDoubledWindowConormalRatio
    (L : ℝ) (rho : XiDivisorSupport) : ℂ :=
  iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowZetaMellinGerm (2 * L)) (rho : ℂ) /
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) - 1

/-- Half-density centered conormal character. -/
def burnolCoPoissonCenteredConormalCharacter (L : ℝ) (rho : ℂ) : ℂ :=
  Complex.exp ((L : ℂ) * (rho - 1 / 2))

/-- Functional-equation/Schwarz reflection on the spectral coordinate. -/
def burnolCoPoissonConormalReflection (rho : ℂ) : ℂ :=
  1 - starRingEnd ℂ rho

/-- First invariant coefficient of the reflected conormal orbit. -/
def burnolCoPoissonConormalOrbitSum (L : ℝ) (rho : ℂ) : ℂ :=
  burnolCoPoissonCenteredConormalCharacter L rho +
    burnolCoPoissonCenteredConormalCharacter L
      (burnolCoPoissonConormalReflection rho)

/-- Second invariant coefficient of the reflected conormal orbit. -/
def burnolCoPoissonConormalOrbitProduct (L : ℝ) (rho : ℂ) : ℂ :=
  burnolCoPoissonCenteredConormalCharacter L rho *
    burnolCoPoissonCenteredConormalCharacter L
      (burnolCoPoissonConormalReflection rho)

/-- Discriminant of the quadratic reflected conormal orbit. -/
def burnolCoPoissonConormalOrbitDiscriminant (L : ℝ) (rho : ℂ) : ℂ :=
  burnolCoPoissonConormalOrbitSum L rho ^ 2 -
    4 * burnolCoPoissonConormalOrbitProduct L rho

/-- The actual Burnol endpoint factor is the uncentered exponential source
character, with the sign forced by endpoint orientation. -/
theorem burnolCoPoissonExpWindowEndpointFactor_eq
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonExpWindowEndpointFactor L rho =
      1 - Complex.exp ((L : ℂ) * rho) := by
  have hc : ((Real.exp (-L) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have hlog : Complex.log ((Real.exp (-L) : ℝ) : ℂ) = (-L : ℝ) := by
    rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  rw [burnolCoPoissonExpWindowEndpointFactor]
  norm_num only [ofReal_one, one_cpow]
  rw [Complex.cpow_def_of_ne_zero hc, hlog]
  congr 1
  push_cast
  ring_nf

/-- Exact uncompleted Mellin transform of the actual logarithmic Burnol
window. -/
theorem integral_Ioi_burnolCoPoisson_expWindow_cpow
    {L : ℝ} (hL : 0 < L) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum
            (coPoissonSubWindowSeed (Real.exp (-L)) 1) t * (t : ℂ) ^ (-w)) =
      burnolCoPoissonExpWindowZetaMellinGerm L w := by
  rw [integral_Ioi_burnolCoPoisson_subWindow_cpow (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (by linarith)) hw0 hw1]
  change burnolCoPoissonExpWindowEndpointFactor L w * (-(riemannZeta w / w)) = _
  rw [burnolCoPoissonExpWindowEndpointFactor_eq]
  unfold burnolCoPoissonExpWindowZetaMellinGerm
  ring

/-- Exact Mellin evaluation of the actual logarithmic Burnol window.  This
binds the conormal character below to the existing co-Poisson source object,
rather than postulating an abstract exponential family. -/
theorem soninMellinEvaluation_coPoissonExpWindowSonin
    {L : ℝ} (hL : 0 < L) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    let hc : 0 < Real.exp (-L) := Real.exp_pos _
    let hcd : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    soninMellinEvaluation w
        (((coPoissonSubWindowSonin hc hcd :
          soninExtendedSpace (subWindowAperture (Real.exp (-L)) 1)) :
            evenSubspace) : SoninL2) =
      mellinCompletionFactor w *
        burnolCoPoissonExpWindowZetaMellinGerm L w := by
  dsimp only
  rw [soninMellinEvaluation_coPoissonSubWindowSonin
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) hw0 hw1,
    ← burnolCoPoissonExpWindowEndpointFactor,
    burnolCoPoissonExpWindowEndpointFactor_eq]
  unfold burnolCoPoissonExpWindowZetaMellinGerm
  ring

/-- The conormal order defined from zeta is exactly the completed-Xi analytic
order at every divisor support point. -/
theorem burnolCoPoissonXiConormalOrder_eq_xi_analyticOrder_toNat
    (rho : XiDivisorSupport) :
    burnolCoPoissonXiConormalOrder rho =
      (analyticOrderAt xi (rho : ℂ)).toNat := by
  rw [burnolCoPoissonXiConormalOrder,
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
      (xi_divisor_support_re_mem_open_unit rho)]

/-- Exact zeta-jet classification at the completed-Xi conormal order: every
lower jet vanishes and the leading jet is nonzero. -/
theorem riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder
    (rho : XiDivisorSupport) :
    (∀ j < burnolCoPoissonXiConormalOrder rho,
      iteratedDeriv j riemannZeta (rho : ℂ) = 0) ∧
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        riemannZeta (rho : ℂ) ≠ 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have horder :
      analyticOrderAt xi (rho : ℂ) =
        analyticOrderAt riemannZeta (rho : ℂ) :=
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have hzetaFinite : analyticOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
    rw [← horder]
    exact xi_orderAt_ne_top (rho : ℂ)
  have hm :
      ((burnolCoPoissonXiConormalOrder rho : ℕ) : ℕ∞) =
        analyticOrderAt riemannZeta (rho : ℂ) := by
    unfold burnolCoPoissonXiConormalOrder
    exact ENat.coe_toNat hzetaFinite
  have hjets :=
    GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero
      (analyticOn_riemannZeta (rho : ℂ) hne1)
      (burnolCoPoissonXiConormalOrder rho) hm.symm
  simpa only [iteratedDeriv_eq_iterate] using hjets

/-- The zeta jet at the exact Xi conormal order is nonzero. -/
theorem iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder
    (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      riemannZeta (rho : ℂ) ≠ 0 :=
  (riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder rho).2

/-- The actual common conormal factor is nonzero at every Xi divisor. -/
theorem burnolCoPoissonXiConormalLead_ne_zero
    (rho : XiDivisorSupport) :
    burnolCoPoissonXiConormalLead rho ≠ 0 := by
  apply div_ne_zero
    (iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder rho)
  intro hrho
  have hre := congrArg Complex.re hrho
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  simp at hre
  linarith

/-- **Actual first-conormal formula.**  Leibniz collapses at the exact Xi
multiplicity, leaving the literal endpoint character times one common
nonzero zeta conormal. -/
theorem iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm
    (L : ℝ) (rho : XiDivisorSupport) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (burnolCoPoissonExpWindowZetaMellinGerm L) (rho : ℂ) =
      burnolCoPoissonSubWindowConormalCoefficient L (rho : ℂ)
        (burnolCoPoissonXiConormalLead rho) := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hne1 : (rho : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hne0 : (rho : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hzeta :
      ContDiffAt ℂ (burnolCoPoissonXiConormalOrder rho)
        riemannZeta (rho : ℂ) :=
    (analyticOn_riemannZeta (rho : ℂ) hne1).contDiffAt
  have hgauge :
      ContDiffAt ℂ (burnolCoPoissonXiConormalOrder rho)
        (fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w) (rho : ℂ) := by
    fun_prop
  change iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
    (riemannZeta * fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w)
      (rho : ℂ) = _
  rw [iteratedDeriv_mul hzeta hgauge]
  rw [Finset.sum_eq_single (burnolCoPoissonXiConormalOrder rho)]
  · simp [burnolCoPoissonSubWindowConormalCoefficient,
      burnolCoPoissonXiConormalLead]
    ring
  · intro j hj hjne
    have hjlt : j < burnolCoPoissonXiConormalOrder rho := by
      have hjle := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact lt_of_le_of_ne hjle hjne
    rw [(riemannZeta_exact_jet_at_burnolCoPoissonXiConormalOrder rho).1 j hjlt]
    simp
  · simp

/-- The first conormal coefficient is nonzero throughout the open right
half-plane. -/
theorem burnolCoPoissonSubWindowConormalCoefficient_ne_zero
    {L : ℝ} (hL : 0 < L) {rho lead : ℂ} (hrho : 0 < rho.re)
    (hlead : lead ≠ 0) :
    burnolCoPoissonSubWindowConormalCoefficient L rho lead ≠ 0 := by
  have hexp : Complex.exp ((L : ℂ) * rho) ≠ 1 := by
    intro h
    have hnorm := congrArg norm h
    rw [Complex.norm_exp, norm_one, Real.exp_eq_one_iff] at hnorm
    have hre : (((L : ℂ) * rho).re) = L * rho.re := by
      simp [Complex.mul_re]
    rw [hre] at hnorm
    nlinarith
  exact mul_ne_zero (sub_ne_zero.mpr hexp) hlead

/-- Doubling a source window multiplies its first conormal coefficient by the
exact endpoint character plus one. -/
theorem burnolCoPoissonSubWindowConormalCoefficient_two_mul
    (L : ℝ) (rho lead : ℂ) :
    burnolCoPoissonSubWindowConormalCoefficient (2 * L) rho lead =
      (Complex.exp ((L : ℂ) * rho) + 1) *
        burnolCoPoissonSubWindowConormalCoefficient L rho lead := by
  rw [burnolCoPoissonSubWindowConormalCoefficient,
    burnolCoPoissonSubWindowConormalCoefficient]
  have harg : (((2 * L : ℝ) : ℂ) * rho) =
      (L : ℂ) * rho + (L : ℂ) * rho := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  ring

/-- **Doubled-window conormal tomography.**  The projective ratio of two
actual nested source windows recovers the complete exponential divisor
coordinate; the common zeta conormal and its multiplicity cancel. -/
theorem burnolCoPoissonDoubledWindowConormalRatio_eq_exp
    {L : ℝ} (hL : 0 < L) {rho lead : ℂ} (hrho : 0 < rho.re)
    (hlead : lead ≠ 0) :
    burnolCoPoissonDoubledWindowConormalRatio L rho lead =
      Complex.exp ((L : ℂ) * rho) := by
  have hcoeff :=
    burnolCoPoissonSubWindowConormalCoefficient_ne_zero hL hrho hlead
  rw [burnolCoPoissonDoubledWindowConormalRatio,
    burnolCoPoissonSubWindowConormalCoefficient_two_mul]
  field_simp [hcoeff]
  ring

/-- **Actual doubled-window conormal tomography.**  At every multiplicity-
exact Xi divisor, the ratio of the literal Mellin jets of the nested Burnol
windows recovers the full exponential spectral coordinate. -/
theorem burnolCoPoissonActualDoubledWindowConormalRatio_eq_exp
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolCoPoissonActualDoubledWindowConormalRatio L rho =
      Complex.exp ((L : ℂ) * (rho : ℂ)) := by
  rw [burnolCoPoissonActualDoubledWindowConormalRatio,
    iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm,
    iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm]
  exact burnolCoPoissonDoubledWindowConormalRatio_eq_exp hL
    (xi_divisor_support_re_mem_open_unit rho).1
    (burnolCoPoissonXiConormalLead_ne_zero rho)

/-- The source projective ratio becomes the centered divisor character after
the forced half-density normalization. -/
theorem burnolCoPoisson_centered_doubledWindowConormalRatio_eq
    {L : ℝ} (hL : 0 < L) {rho lead : ℂ} (hrho : 0 < rho.re)
    (hlead : lead ≠ 0) :
    Complex.exp (-(L : ℂ) / 2) *
        burnolCoPoissonDoubledWindowConormalRatio L rho lead =
      burnolCoPoissonCenteredConormalCharacter L rho := by
  rw [burnolCoPoissonDoubledWindowConormalRatio_eq_exp hL hrho hlead,
    burnolCoPoissonCenteredConormalCharacter, ← Complex.exp_add]
  congr 1
  ring

/-- Exact radial coordinate of the centered conormal character. -/
theorem norm_burnolCoPoissonCenteredConormalCharacter
    (L : ℝ) (rho : ℂ) :
    ‖burnolCoPoissonCenteredConormalCharacter L rho‖ =
      Real.exp (L * (rho.re - 1 / 2)) := by
  rw [burnolCoPoissonCenteredConormalCharacter, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The centered source character recovers the horizontal spectral coordinate
without loss. -/
theorem log_norm_burnolCoPoissonCenteredConormalCharacter_div
    {L : ℝ} (hL : 0 < L) (rho : ℂ) :
    Real.log ‖burnolCoPoissonCenteredConormalCharacter L rho‖ / L =
      rho.re - 1 / 2 := by
  rw [norm_burnolCoPoissonCenteredConormalCharacter, Real.log_exp]
  field_simp

/-- The centered conormal character has uniform upper and lower capacity on
the full open critical strip. -/
theorem burnolCoPoissonCenteredConormalCharacter_uniform_capacity
    {L : ℝ} (hL : 0 < L) {rho : ℂ}
    (hlo : 0 < rho.re) (hhi : rho.re < 1) :
    Real.exp (-L / 2) <
        ‖burnolCoPoissonCenteredConormalCharacter L rho‖ ∧
      ‖burnolCoPoissonCenteredConormalCharacter L rho‖ <
        Real.exp (L / 2) := by
  rw [norm_burnolCoPoissonCenteredConormalCharacter]
  constructor <;> apply Real.exp_lt_exp.mpr <;> nlinarith

/-- The inverse character has the same strip-uniform capacity. -/
theorem burnolCoPoissonCenteredConormalCharacter_inv_uniform_capacity
    {L : ℝ} (hL : 0 < L) {rho : ℂ}
    (hlo : 0 < rho.re) (hhi : rho.re < 1) :
    Real.exp (-L / 2) <
        ‖(burnolCoPoissonCenteredConormalCharacter L rho)⁻¹‖ ∧
      ‖(burnolCoPoissonCenteredConormalCharacter L rho)⁻¹‖ <
        Real.exp (L / 2) := by
  rw [norm_inv, norm_burnolCoPoissonCenteredConormalCharacter,
    ← Real.exp_neg]
  constructor <;> apply Real.exp_lt_exp.mpr <;> nlinarith

/-- Reflection exchanges the centered character with its conjugate inverse. -/
theorem burnolCoPoissonCenteredConormalCharacter_reflection
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonCenteredConormalCharacter L
        (burnolCoPoissonConormalReflection rho) =
      ((starRingEnd ℂ)
        (burnolCoPoissonCenteredConormalCharacter L rho))⁻¹ := by
  rw [burnolCoPoissonCenteredConormalCharacter,
    burnolCoPoissonCenteredConormalCharacter]
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  apply Complex.ext
  all_goals
    simp [burnolCoPoissonConormalReflection, Complex.mul_re,
      Complex.mul_im] <;> ring

@[simp] theorem burnolCoPoissonConormalReflection_involutive
    (rho : ℂ) :
    burnolCoPoissonConormalReflection
        (burnolCoPoissonConormalReflection rho) = rho := by
  simp [burnolCoPoissonConormalReflection]

/-- The orbit sum descends to the reflection quotient. -/
theorem burnolCoPoissonConormalOrbitSum_reflection
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonConormalOrbitSum L
        (burnolCoPoissonConormalReflection rho) =
      burnolCoPoissonConormalOrbitSum L rho := by
  simp [burnolCoPoissonConormalOrbitSum, add_comm]

/-- The orbit product descends to the reflection quotient. -/
theorem burnolCoPoissonConormalOrbitProduct_reflection
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonConormalOrbitProduct L
        (burnolCoPoissonConormalReflection rho) =
      burnolCoPoissonConormalOrbitProduct L rho := by
  simp [burnolCoPoissonConormalOrbitProduct, mul_comm]

/-- The invariant orbit product has unit norm: reflection changes only the
radial sheet, not the quotient determinant. -/
theorem norm_burnolCoPoissonConormalOrbitProduct
    (L : ℝ) (rho : ℂ) :
    ‖burnolCoPoissonConormalOrbitProduct L rho‖ = 1 := by
  rw [burnolCoPoissonConormalOrbitProduct, norm_mul,
    norm_burnolCoPoissonCenteredConormalCharacter,
    norm_burnolCoPoissonCenteredConormalCharacter]
  have hrefre : (burnolCoPoissonConormalReflection rho).re = 1 - rho.re := by
    simp [burnolCoPoissonConormalReflection]
  rw [hrefre, ← Real.exp_add]
  have hexp :
      L * (rho.re - 1 / 2) + L * (1 - rho.re - 1 / 2) = 0 := by
    ring
  rw [hexp, Real.exp_zero]

/-- Both reflected source characters are roots of the invariant quadratic. -/
theorem burnolCoPoissonCenteredConormalCharacter_quadratic
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonCenteredConormalCharacter L rho ^ 2 -
        burnolCoPoissonConormalOrbitSum L rho *
          burnolCoPoissonCenteredConormalCharacter L rho +
        burnolCoPoissonConormalOrbitProduct L rho = 0 := by
  simp only [burnolCoPoissonConormalOrbitSum,
    burnolCoPoissonConormalOrbitProduct]
  ring

/-- The reflected sheet is the second root of the same invariant quadratic. -/
theorem burnolCoPoissonCenteredConormalCharacter_reflection_quadratic
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonCenteredConormalCharacter L
          (burnolCoPoissonConormalReflection rho) ^ 2 -
        burnolCoPoissonConormalOrbitSum L rho *
          burnolCoPoissonCenteredConormalCharacter L
            (burnolCoPoissonConormalReflection rho) +
        burnolCoPoissonConormalOrbitProduct L rho = 0 := by
  have h := burnolCoPoissonCenteredConormalCharacter_quadratic L
    (burnolCoPoissonConormalReflection rho)
  rwa [burnolCoPoissonConormalOrbitSum_reflection,
    burnolCoPoissonConormalOrbitProduct_reflection] at h

/-- The discriminant is the square of the reflected character difference. -/
theorem burnolCoPoissonConormalOrbitDiscriminant_eq_sq_sub
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonConormalOrbitDiscriminant L rho =
      (burnolCoPoissonCenteredConormalCharacter L rho -
        burnolCoPoissonCenteredConormalCharacter L
          (burnolCoPoissonConormalReflection rho)) ^ 2 := by
  simp only [burnolCoPoissonConormalOrbitDiscriminant,
    burnolCoPoissonConormalOrbitSum,
    burnolCoPoissonConormalOrbitProduct]
  ring

/-- The quadratic discriminant itself descends to the reflection quotient. -/
theorem burnolCoPoissonConormalOrbitDiscriminant_reflection
    (L : ℝ) (rho : ℂ) :
    burnolCoPoissonConormalOrbitDiscriminant L
        (burnolCoPoissonConormalReflection rho) =
      burnolCoPoissonConormalOrbitDiscriminant L rho := by
  unfold burnolCoPoissonConormalOrbitDiscriminant
  rw [burnolCoPoissonConormalOrbitSum_reflection,
    burnolCoPoissonConormalOrbitProduct_reflection]

/-- The two sheets of the conormal cover meet exactly on the critical line. -/
theorem burnolCoPoissonCenteredConormalCharacter_eq_reflection_iff
    {L : ℝ} (hL : 0 < L) (rho : ℂ) :
    burnolCoPoissonCenteredConormalCharacter L rho =
        burnolCoPoissonCenteredConormalCharacter L
          (burnolCoPoissonConormalReflection rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · intro h
    have hnorm := congrArg norm h
    rw [norm_burnolCoPoissonCenteredConormalCharacter,
      norm_burnolCoPoissonCenteredConormalCharacter] at hnorm
    have hrefre : (burnolCoPoissonConormalReflection rho).re = 1 - rho.re := by
      simp [burnolCoPoissonConormalReflection]
    rw [hrefre] at hnorm
    have hexp := Real.exp_injective hnorm
    nlinarith
  · intro hre
    have href : burnolCoPoissonConormalReflection rho = rho :=
      (fe_reflection_fixed_iff rho).mpr hre
    rw [href]

/-- **Quadratic conormal ramification law.**  The invariant Burnol source
cover ramifies exactly at critical-line points.  Applying this theorem to all
zeta divisor points would be RH; no such universal premise is used here. -/
theorem burnolCoPoissonConormalOrbitDiscriminant_eq_zero_iff
    {L : ℝ} (hL : 0 < L) (rho : ℂ) :
    burnolCoPoissonConormalOrbitDiscriminant L rho = 0 ↔
      rho.re = 1 / 2 := by
  rw [burnolCoPoissonConormalOrbitDiscriminant_eq_sq_sub]
  rw [sq_eq_zero_iff, sub_eq_zero]
  exact burnolCoPoissonCenteredConormalCharacter_eq_reflection_iff hL rho

end

end RHTower
