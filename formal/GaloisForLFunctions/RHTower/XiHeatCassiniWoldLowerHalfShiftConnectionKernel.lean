import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHalfShiftPhysicalObserver

/-!
# Lower-half-strip connection kernel for the centered Route-T Wold residual

The physical `sqrt p` observer is already the legal contour translation to depth `1/2`.  This
module performs the remaining finite Abel transport *under that contour integral*.  The terminal
residual and all adjacent-prime connection atoms become one joint source kernel.  Its two exact
normal forms expose complementary structure:

* the primitive form retains the vanishing Wold discrepancy on prime-log edges;
* the increment form is the Fourier transform of the local Wold-versus-log-mesh defect.

Thus no triangle inequality is taken before adjacent-prime cancellation.  The open quantitative
problem is reduced to this literal lower-boundary Fourier kernel.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Negative-frequency character on the ordered prime-log mesh. -/
def xiHeatCassiniOrderedPrimeNegativePhase (N : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) * (x : ℂ)))

/-- One ordered prime character paired with the physical lower-half-strip mass boundary. -/
def xiHeatCassiniOrderedPrimeLowerHalfIntegrand
    (a : ℝ) (τ : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  xiMassAnalyticTest a τ ((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) *
    xiHeatCassiniOrderedPrimeNegativePhase N x

/-- Its integral is exactly the ordered lower-half-shift profile. -/
theorem integral_xiHeatCassiniOrderedPrimeLowerHalfIntegrand
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    (∫ x : ℝ, xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ N x) =
      xiHeatCassiniPrimeMassLowerShiftProfile
        a (1 / 2) τ (nthPrimeSubtype N) := by
  rfl

/-- Every ordered lower-half prime character is absolutely integrable against the mass test. -/
theorem integrable_xiHeatCassiniOrderedPrimeLowerHalfIntegrand
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re) (N : ℕ) :
    Integrable (xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ N) := by
  let K : ℝ := Real.exp (|τ.im| * (1 / 2))
  have hmajor : Integrable (fun x : ℝ =>
      K * Real.exp (-(τ.re * |x|))) :=
    (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hτ).const_mul K
  have hcontinuous :
      Continuous (xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ N) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hmem :
        ((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) ∈ xiMassStrip a := by
      change |((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I).im| < a
      simpa using ha
    change ContinuousAt
      (fun y : ℝ =>
        xiMassAnalyticTest a τ
            ((y : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) *
          xiHeatCassiniOrderedPrimeNegativePhase N y) x
    have htestAt : ContinuousAt
        (fun y : ℝ =>
          xiMassAnalyticTest a τ
            ((y : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I)) x :=
      (hasDerivAt_xiMassAnalyticTest (by linarith) τ hmem).continuousAt.comp'
        (x := x) (Complex.continuous_ofReal.continuousAt.sub
          (continuousAt_const.mul continuousAt_const))
    have hphaseAt : ContinuousAt
        (xiHeatCassiniOrderedPrimeNegativePhase N) x := by
      unfold xiHeatCassiniOrderedPrimeNegativePhase
      fun_prop
    exact htestAt.mul hphaseAt
  refine hmajor.mono' hcontinuous.aestronglyMeasurable ?_
  filter_upwards with x
  have hmem :
      ((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) ∈ xiMassStrip a := by
    change |((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I).im| < a
    simpa using ha
  have htest := norm_xiMassAnalyticTest_le (by linarith) hτ.le hmem
  rw [xiHeatCassiniOrderedPrimeLowerHalfIntegrand,
    xiHeatCassiniOrderedPrimeNegativePhase, norm_mul, Complex.norm_exp]
  have hphase :
      (-(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) * (x : ℂ))).re = 0 := by
    simp
  rw [hphase, Real.exp_zero, mul_one]
  calc
    ‖xiMassAnalyticTest a τ
        (↑x - ((1 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        Real.exp (-(τ.re * |x|) + |τ.im| * (1 / 2)) := by
      simpa using htest
    _ = K * Real.exp (-(τ.re * |x|)) := by
      dsimp only [K]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Primitive normal form of the finite lower-half residual connection. -/
def xiHeatCassiniWoldResidualLowerHalfPhaseKernel (N : ℕ) (x : ℝ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
      xiHeatCassiniOrderedPrimeNegativePhase N x +
    ∑ n ∈ Finset.range N,
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
        (xiHeatCassiniOrderedPrimeNegativePhase n x -
          xiHeatCassiniOrderedPrimeNegativePhase (n + 1) x)

/-- Joint analytic-arithmetic source kernel on the physical lower boundary. -/
def xiHeatCassiniWoldResidualLowerHalfJointKernel
    (a : ℝ) (τ : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
      xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ N x +
    ∑ n ∈ Finset.range N,
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
        (xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ n x -
          xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ (n + 1) x)

/-- The joint kernel factors into one lower-boundary mass test and the residual phase kernel. -/
theorem xiHeatCassiniWoldResidualLowerHalfJointKernel_eq_mass_mul_phaseKernel
    (a : ℝ) (τ : ℂ) (N : ℕ) (x : ℝ) :
    xiHeatCassiniWoldResidualLowerHalfJointKernel a τ N x =
      xiMassAnalyticTest a τ
          ((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) *
        xiHeatCassiniWoldResidualLowerHalfPhaseKernel N x := by
  unfold xiHeatCassiniWoldResidualLowerHalfJointKernel
    xiHeatCassiniWoldResidualLowerHalfPhaseKernel
    xiHeatCassiniOrderedPrimeLowerHalfIntegrand
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro n hn
    ring

/-- Successive centered Wold primitives differ by one local Wold weight minus one prime-log gap. -/
theorem xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub
    (N : ℕ) :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N =
      woldCoeff 1 (nthPrimeSubtype (N + 1)) -
        (xiMassNthPrimeLogHeight (N + 1) - xiMassNthPrimeLogHeight N) := by
  simp only [xiHeatCassiniOrderedWoldResidualLogDiscrepancy,
    xiHeatCassiniOrderedWoldLogDiscrepancy,
    xiHeatCassiniOrderedWoldPartialMass, Finset.sum_range_succ]
  ring

/-- Finite Abel transport inside the lower-half contour: primitive edge form equals increment
form. -/
theorem xiHeatCassiniWoldResidualLowerHalfPhaseKernel_eq_increment
    (N : ℕ) (x : ℝ) :
    xiHeatCassiniWoldResidualLowerHalfPhaseKernel N x =
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
          xiHeatCassiniOrderedPrimeNegativePhase 0 x +
        ∑ n ∈ Finset.range N,
          ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (n + 1) -
              xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeNegativePhase (n + 1) x := by
  induction N with
  | zero => simp [xiHeatCassiniWoldResidualLowerHalfPhaseKernel]
  | succ N ih =>
      simp only [xiHeatCassiniWoldResidualLowerHalfPhaseKernel,
        Finset.sum_range_succ] at ih ⊢
      push_cast at ih ⊢
      calc
        (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) : ℂ) *
              xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x +
            ((∑ n ∈ Finset.range N,
                (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
                  (xiHeatCassiniOrderedPrimeNegativePhase n x -
                    xiHeatCassiniOrderedPrimeNegativePhase (n + 1) x)) +
              (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
                (xiHeatCassiniOrderedPrimeNegativePhase N x -
                  xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x)) =
            ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
                xiHeatCassiniOrderedPrimeNegativePhase N x +
              ∑ n ∈ Finset.range N,
                (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
                  (xiHeatCassiniOrderedPrimeNegativePhase n x -
                    xiHeatCassiniOrderedPrimeNegativePhase (n + 1) x)) +
              ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) : ℂ) -
                xiHeatCassiniOrderedWoldResidualLogDiscrepancy N) *
                  xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x := by ring
        _ = _ := by rw [ih]; ring

/-- Arithmetic normal form: the joint boundary source is the Fourier transform of the exact local
Wold-minus-Lebesgue quadrature defect. -/
theorem xiHeatCassiniWoldResidualLowerHalfPhaseKernel_eq_wold_sub_logGap
    (N : ℕ) (x : ℝ) :
    xiHeatCassiniWoldResidualLowerHalfPhaseKernel N x =
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
          xiHeatCassiniOrderedPrimeNegativePhase 0 x +
        ∑ n ∈ Finset.range N,
          ((woldCoeff 1 (nthPrimeSubtype (n + 1)) -
              (xiMassNthPrimeLogHeight (n + 1) -
                xiMassNthPrimeLogHeight n) : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeNegativePhase (n + 1) x := by
  rw [xiHeatCassiniWoldResidualLowerHalfPhaseKernel_eq_increment]
  apply congrArg (fun z : ℂ =>
    (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
      xiHeatCassiniOrderedPrimeNegativePhase 0 x + z)
  apply Finset.sum_congr rfl
  intro n hn
  rw [xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub]

/-- Joint kernel is integrable before any norm or sheet projection. -/
theorem integrable_xiHeatCassiniWoldResidualLowerHalfJointKernel
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re) (N : ℕ) :
    Integrable (xiHeatCassiniWoldResidualLowerHalfJointKernel a τ N) := by
  apply Integrable.add
  · exact (integrable_xiHeatCassiniOrderedPrimeLowerHalfIntegrand ha hτ N).const_mul _
  · apply integrable_finsetSum
    intro n hn
    exact ((integrable_xiHeatCassiniOrderedPrimeLowerHalfIntegrand ha hτ n).sub
      (integrable_xiHeatCassiniOrderedPrimeLowerHalfIntegrand ha hτ (n + 1))).const_mul _

/-- Exact finite source identity: terminal residual plus all connection atoms is one integral on
the legal lower-half boundary. -/
theorem integral_xiHeatCassiniWoldResidualLowerHalfJointKernel_eq_flux
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re) (N : ℕ) :
    (∫ x : ℝ, xiHeatCassiniWoldResidualLowerHalfJointKernel a τ N x) =
      xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedWoldResidualConnectionAtom a τ n := by
  have hint (n : ℕ) :=
    integrable_xiHeatCassiniOrderedPrimeLowerHalfIntegrand ha hτ n
  unfold xiHeatCassiniWoldResidualLowerHalfJointKernel
  calc
    _ =
        (∫ x : ℝ,
          (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
            xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ N x) +
        (∫ x : ℝ,
          ∑ n ∈ Finset.range N,
            (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
              (xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ n x -
                xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ (n + 1) x)) := by
      exact integral_add ((hint N).const_mul _)
        (integrable_finsetSum (Finset.range N) fun n _ =>
          ((hint n).sub (hint (n + 1))).const_mul _)
    _ = _ := by
      rw [integral_const_mul]
      have hfin :
          (∫ x : ℝ,
            ∑ n ∈ Finset.range N,
              (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
                (xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ n x -
                  xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ (n + 1) x)) =
            ∑ n ∈ Finset.range N,
              ∫ x : ℝ,
                (xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℂ) *
                  (xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ n x -
                    xiHeatCassiniOrderedPrimeLowerHalfIntegrand a τ (n + 1) x) := by
        exact integral_finsetSum (Finset.range N) (fun n _ =>
          ((hint n).sub (hint (n + 1))).const_mul _)
      rw [hfin]
      conv_lhs =>
        enter [2, 2, n]
        rw [integral_const_mul, integral_sub (hint n) (hint (n + 1)),
          integral_xiHeatCassiniOrderedPrimeLowerHalfIntegrand,
          integral_xiHeatCassiniOrderedPrimeLowerHalfIntegrand,
          xiHeatCassiniPrimeMassLowerHalfShiftProfile_nthPrime_eq_ordered ha hτ,
          xiHeatCassiniPrimeMassLowerHalfShiftProfile_nthPrime_eq_ordered ha hτ]
      rw [integral_xiHeatCassiniOrderedPrimeLowerHalfIntegrand,
        xiHeatCassiniPrimeMassLowerHalfShiftProfile_nthPrime_eq_ordered ha hτ]
      unfold xiHeatCassiniOrderedWoldResidualTerminalFlux
        xiHeatCassiniOrderedWoldResidualConnectionAtom
      congr 1
      ring

end

end RHTower
