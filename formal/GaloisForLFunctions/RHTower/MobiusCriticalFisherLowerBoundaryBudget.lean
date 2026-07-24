import GaloisForLFunctions.RHTower.MobiusCriticalFisherCutoffLimits
import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform
import Mathlib.Analysis.SumIntegralExpDecay

/-!
# One-sided Möbius Fisher boundary budget

The squarefree Möbius Fisher cutoff commutator has two adjoint boundary
orientations.  Its lower orientation is an actual non-diagonal
Hilbert--Schmidt operator, not a scalar readout.  The general rank-two cutoff
law identifies the full commutator energy with twice the energy of this one
corner.

Consequently the established eight-unit bound for the two-sided commutator is
already the exact four-unit bound for either native boundary orientation.
This removes an artificial budget doubling from the CCM source-to-Xi
incidence problem: the remaining theorem is one-corner Gamma/Sonin transport,
not construction of another eight-unit source.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-- Hilbert--Schmidt energy of the lower boundary orientation of the
squarefree critical pointed Fisher connection.  It is extended by zero
outside the strict Euler half-plane. -/
def squarefreeMobiusCriticalFisherLowerBoundaryEnergy
    (sigma u : ℝ) : ℝ :=
  if hsigma : 1 < sigma then
    hsNormSq
      (cutoffLowerBoundary
        (squarefreeMobiusCriticalClockCutoff sigma u)
        (pointedFisherConnection
          (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma)))
  else 0

/-- At every finite Euler parameter, the two-sided commutator energy is
exactly twice the energy of one native boundary orientation. -/
theorem squarefreeMobiusCriticalFisherCutoffCommutatorEnergy_eq_two_mul_lower
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    squarefreeMobiusCriticalFisherCutoffCommutatorEnergy sigma u =
      2 * squarefreeMobiusCriticalFisherLowerBoundaryEnergy sigma u := by
  rw [squarefreeMobiusCriticalFisherCutoffCommutatorEnergy, dif_pos hsigma,
    squarefreeMobiusCriticalFisherLowerBoundaryEnergy, dif_pos hsigma]
  exact hsNormSq_cutoffCommutator_eq_two_mul_lowerBoundary
    (squarefreeMobiusCriticalClockCutoff sigma u)
    (pointedFisherConnection
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma))
    (squarefreeMobiusCriticalClockCutoff_idempotent sigma u)
    (squarefreeMobiusCriticalClockCutoff_selfAdjoint sigma u)
    (pointedFisherConnection_selfAdjoint _ _)
    (pointedFisherConnection_isHilbertSchmidt _ _)

/-- Closed critical profile of one native boundary orientation. -/
def squarefreeMobiusCriticalFisherLowerBoundaryLimit (u : ℝ) : ℝ :=
  squarefreeMobiusCriticalFisherCutoffWardLimit u / 2

/-- The actual lower boundary operator converges to half the two-sided Ward
profile. -/
theorem tendsto_squarefreeMobiusCriticalFisherLowerBoundaryEnergy
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        squarefreeMobiusCriticalFisherLowerBoundaryEnergy sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (squarefreeMobiusCriticalFisherLowerBoundaryLimit u)) := by
  have h :=
    (tendsto_squarefreeMobiusCriticalFisherCutoffCommutatorEnergy hu).const_mul
      (1 / 2 : ℝ)
  have h' :
      Tendsto
        (fun sigma : ℝ =>
          (1 / 2 : ℝ) *
            squarefreeMobiusCriticalFisherCutoffCommutatorEnergy sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (squarefreeMobiusCriticalFisherLowerBoundaryLimit u)) := by
    simpa [squarefreeMobiusCriticalFisherLowerBoundaryLimit, div_eq_mul_inv,
      mul_comm] using h
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  rw [squarefreeMobiusCriticalFisherCutoffCommutatorEnergy_eq_two_mul_lower
    hsigma]
  simp

/-- One boundary orientation is nonnegative on every physical window. -/
theorem squarefreeMobiusCriticalFisherLowerBoundaryLimit_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ squarefreeMobiusCriticalFisherLowerBoundaryLimit u := by
  rw [squarefreeMobiusCriticalFisherLowerBoundaryLimit]
  exact div_nonneg
    (squarefreeMobiusCriticalFisherCutoffWardLimit_nonneg hu) (by norm_num)

/-- **One-sided four-unit source budget.**  The native lower boundary
orientation has at most four units per squarefree clock mass. -/
theorem squarefreeMobiusCriticalFisherLowerBoundaryLimit_le_four_mul_CDF
    {u : ℝ} (hu : 0 ≤ u) :
    squarefreeMobiusCriticalFisherLowerBoundaryLimit u ≤
      4 * (1 - Real.exp (-u)) := by
  rw [squarefreeMobiusCriticalFisherLowerBoundaryLimit]
  nlinarith
    [squarefreeMobiusCriticalFisherCutoffWardLimit_le_eight_mul_CDF hu]

/-- The one-sided source boundary density is exactly four. -/
theorem tendsto_squarefreeMobiusCriticalFisherLowerBoundaryLimit_div :
    Tendsto
      (fun u : ℝ =>
        squarefreeMobiusCriticalFisherLowerBoundaryLimit u / u)
      (nhdsWithin 0 (Ioi 0)) (nhds 4) := by
  apply
    tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [squarefreeMobiusCriticalFisherLowerBoundaryLimit]
  field_simp

private theorem integrableOn_pow_mul_exp_nat_neg
    (k p : ℕ) (hp : 0 < p) :
    IntegrableOn
      (fun u : ℝ => u ^ k * Real.exp (-((p : ℝ) * u))) (Ioi 0) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (p : ℝ)) hk (by exact_mod_cast hp)
  have hne :
      (∫ u : ℝ in Ioi 0,
        u ^ ((k : ℝ) + 1 - 1) * Real.exp (-((p : ℝ) * u))) ≠ 0 := by
    rw [hvalue]
    positivity
  have hint : IntegrableOn
      (fun u : ℝ =>
        u ^ ((k : ℝ) + 1 - 1) * Real.exp (-((p : ℝ) * u))) (Ioi 0) :=
    Integrable.of_integral_ne_zero hne
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using hint

private theorem integral_pow_mul_exp_nat_neg
    (k p : ℕ) (hp : 0 < p) :
    (∫ u : ℝ in Ioi 0, u ^ k * Real.exp (-((p : ℝ) * u))) =
      k.factorial / (p : ℝ) ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (p : ℝ)) (by positivity)
      (by exact_mod_cast hp)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h, Real.Gamma_nat_eq_factorial]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  simp only [one_div, inv_pow, pow_succ]
  field_simp

/-- The critical one-corner profile is integrable over the complete physical
cutoff ray. -/
theorem integrableOn_squarefreeMobiusCriticalFisherLowerBoundaryLimit :
    IntegrableOn squarefreeMobiusCriticalFisherLowerBoundaryLimit (Ioi 0) := by
  have h01 := integrableOn_pow_mul_exp_nat_neg 0 1 (by norm_num)
  have h21 := integrableOn_pow_mul_exp_nat_neg 2 1 (by norm_num)
  have h02 := integrableOn_pow_mul_exp_nat_neg 0 2 (by norm_num)
  have h22 := integrableOn_pow_mul_exp_nat_neg 2 2 (by norm_num)
  norm_num at h01 h21 h02 h22
  have hsum :
      IntegrableOn
        (fun u : ℝ =>
          4 * Real.exp (-u) +
            2 * (u ^ 2 * Real.exp (-u)) -
            (4 * Real.exp (-(2 * u)) +
              8 * (u ^ 2 * Real.exp (-((2 : ℝ) * u))))) (Ioi 0) :=
    by
      simpa only [Pi.add_apply, Pi.sub_apply] using
        ((h01.const_mul 4).add (h21.const_mul 2)).sub
          ((h02.const_mul 4).add (h22.const_mul 8))
  apply hsum.congr
  filter_upwards with u
  simp only [squarefreeMobiusCriticalFisherLowerBoundaryLimit,
    squarefreeMobiusCriticalFisherCutoffWardLimit]
  ring_nf

/-- **Global one-corner four-unit conservation law.**  After the critical
squarefree limit, integrating the actual non-diagonal lower Fisher boundary
over every hard cutoff spends exactly four Hilbert--Schmidt units. -/
theorem integral_squarefreeMobiusCriticalFisherLowerBoundaryLimit :
    (∫ u : ℝ in Ioi 0,
      squarefreeMobiusCriticalFisherLowerBoundaryLimit u) = 4 := by
  have h01 := integrableOn_pow_mul_exp_nat_neg 0 1 (by norm_num)
  have h21 := integrableOn_pow_mul_exp_nat_neg 2 1 (by norm_num)
  have h02 := integrableOn_pow_mul_exp_nat_neg 0 2 (by norm_num)
  have h22 := integrableOn_pow_mul_exp_nat_neg 2 2 (by norm_num)
  norm_num at h01 h21 h02 h22
  rw [show squarefreeMobiusCriticalFisherLowerBoundaryLimit =
      fun u : ℝ =>
        4 * Real.exp (-u) +
          2 * (u ^ 2 * Real.exp (-u)) -
          (4 * Real.exp (-(2 * u)) +
            8 * (u ^ 2 * Real.exp (-((2 : ℝ) * u))) ) by
      funext u
      simp only [squarefreeMobiusCriticalFisherLowerBoundaryLimit,
        squarefreeMobiusCriticalFisherCutoffWardLimit]
      ring_nf]
  have hleft :
      IntegrableOn
        (fun u : ℝ =>
          4 * Real.exp (-u) + 2 * (u ^ 2 * Real.exp (-u))) (Ioi 0) := by
    simpa only [Pi.add_apply] using
      (h01.const_mul 4).add (h21.const_mul 2)
  have hright :
      IntegrableOn
        (fun u : ℝ =>
          4 * Real.exp (-(2 * u)) +
            8 * (u ^ 2 * Real.exp (-(2 * u)))) (Ioi 0) := by
    simpa only [Pi.add_apply] using
      (h02.const_mul 4).add (h22.const_mul 8)
  have hsplit :
      (∫ u : ℝ in Ioi 0,
          (4 * Real.exp (-u) + 2 * (u ^ 2 * Real.exp (-u))) -
            (4 * Real.exp (-(2 * u)) +
              8 * (u ^ 2 * Real.exp (-(2 * u))))) =
        (∫ u : ℝ in Ioi 0,
          4 * Real.exp (-u) + 2 * (u ^ 2 * Real.exp (-u))) -
        ∫ u : ℝ in Ioi 0,
          4 * Real.exp (-(2 * u)) +
            8 * (u ^ 2 * Real.exp (-(2 * u))) := by
    simpa only [Pi.sub_apply] using
      MeasureTheory.integral_sub hleft hright
  have hleftSplit :
      (∫ u : ℝ in Ioi 0,
          4 * Real.exp (-u) + 2 * (u ^ 2 * Real.exp (-u))) =
        (∫ u : ℝ in Ioi 0, 4 * Real.exp (-u)) +
          ∫ u : ℝ in Ioi 0, 2 * (u ^ 2 * Real.exp (-u)) := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add (h01.const_mul 4) (h21.const_mul 2)
  have hrightSplit :
      (∫ u : ℝ in Ioi 0,
          4 * Real.exp (-(2 * u)) +
            8 * (u ^ 2 * Real.exp (-(2 * u)))) =
        (∫ u : ℝ in Ioi 0, 4 * Real.exp (-(2 * u))) +
          ∫ u : ℝ in Ioi 0,
            8 * (u ^ 2 * Real.exp (-(2 * u))) := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add (h02.const_mul 4) (h22.const_mul 8)
  have hi01 :
      (∫ u : ℝ in Ioi 0, Real.exp (-u)) = 1 := by
    simpa using integral_pow_mul_exp_nat_neg 0 1 (by norm_num)
  have hi21 :
      (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-u)) = 2 := by
    simpa using integral_pow_mul_exp_nat_neg 2 1 (by norm_num)
  have hi02 :
      (∫ u : ℝ in Ioi 0, Real.exp (-(2 * u))) = 1 / 2 := by
    simpa using integral_pow_mul_exp_nat_neg 0 2 (by norm_num)
  have hi22 :
      (∫ u : ℝ in Ioi 0, u ^ 2 * Real.exp (-(2 * u))) = 1 / 4 := by
    have h := integral_pow_mul_exp_nat_neg 2 2 (by norm_num)
    norm_num at h ⊢
    exact h
  rw [hsplit, hleftSplit, hrightSplit,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hi01, hi21, hi02, hi22]
  norm_num

/-- The universal hard-cut/soft-shift transform specializes to the physical
squarefree critical clock.  Its semigroup factors are literally the damping
coefficients of `infiniteMobiusCriticalDampedSignedWeight`; thus the hard
one-corner field and the soft Möbius source are one non-diagonal object before
Gamma/Sonin scalarization. -/
theorem
    squarefreeMobiusCriticalClock_orientedCutoffLaplaceCoefficient_eq_dampingDividedDifference
    {sigma u : ℝ} {n m : ℕ} {k : ℂ}
    (hu : u ≠ 0)
    (hmn :
      squarefreeMobiusCriticalClock sigma m ≤
        squarefreeMobiusCriticalClock sigma n) :
    orientedCutoffLaplaceCoefficient
        (squarefreeMobiusCriticalClock sigma m)
        (squarefreeMobiusCriticalClock sigma n) k (u : ℂ) =
      k *
        ((Real.exp (-(u * (sigma - 1) * Real.log m)) : ℂ) -
          (Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ)) /
            (u : ℂ) := by
  rw [orientedCutoffLaplaceCoefficient_eq_dividedDifference
      (Complex.ofReal_ne_zero.mpr hu),
    semigroupDividedDifferenceCoefficient, if_pos hmn]
  have hdamp (j : ℕ) :
      Complex.exp
          (-(u : ℂ) *
            (squarefreeMobiusCriticalClock sigma j : ℂ)) =
        (Real.exp (-(u * (sigma - 1) * Real.log j)) : ℂ) := by
    rw [Complex.ofReal_exp]
    apply congrArg Complex.exp
    have hreal :
        (-u) * squarefreeMobiusCriticalClock sigma j =
          -(u * (sigma - 1) * Real.log j) := by
      simp only [squarefreeMobiusCriticalClock]
      ring
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simpa only [Complex.ofReal_neg, Complex.ofReal_mul] using hcast
  rw [hdamp m, hdamp n]

end RHTower
