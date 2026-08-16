import GaloisForLFunctions.HTGeometry.VolterraWindowedEquation

/-!
# Global existence for the linear second-order initial value problem

For a continuous coefficient `P`, the problem

`v″ = P·v`,  `v(0) = α`,  `v′(0) = β`

has a solution on the whole line.  The equation is equivalent to the Volterra equation

`v(ξ) = α + βξ + ∫₀^ξ (ξ − t)·P(t)·v(t) dt` ,

whose kernel is locally bounded, so the Picard series of the previous files converges at every
time with no smallness or growth hypothesis.  Differentiating the Volterra form twice — the inner
`ξ` splits off as `ξ·∫₀^ξ P v − ∫₀^ξ t P v`, and the two boundary contributions cancel — returns the
differential equation.

mathlib has Picard–Lindelöf, which is local; the global statement for a linear equation is not
there.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Volterra kernel of the second-order problem. -/
def secondOrderKernel (P : ℝ → ℝ) (t s : ℝ) : ℝ →L[ℝ] ℝ :=
  ((t - s) * P s) • (ContinuousLinearMap.id ℝ ℝ)

/-- The free term carrying the initial data. -/
def secondOrderFree (α β : ℝ) : ℝ → ℝ := fun t => α + β * t

/-- The solution of `v″ = P·v` with `v(0) = α`, `v′(0) = β`. -/
def secondOrderSolution (P : ℝ → ℝ) (α β : ℝ) : ℝ → ℝ :=
  volterraSolution (secondOrderFree α β) (secondOrderKernel P)

theorem secondOrderKernel_apply (P : ℝ → ℝ) (t s y : ℝ) :
    secondOrderKernel P t s y = (t - s) * P s * y := by
  rw [secondOrderKernel]
  simp [smul_eq_mul]

theorem norm_secondOrderKernel_le (P : ℝ → ℝ) (t s : ℝ) :
    ‖secondOrderKernel P t s‖ ≤ |(t - s) * P s| := by
  rw [secondOrderKernel, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le

theorem continuous_secondOrderKernel {P : ℝ → ℝ} (hP : Continuous P) :
    Continuous fun p : ℝ × ℝ => secondOrderKernel P p.1 p.2 := by
  have hscal : Continuous fun p : ℝ × ℝ => (p.1 - p.2) * P p.2 :=
    (continuous_fst.sub continuous_snd).mul (hP.comp continuous_snd)
  exact (continuous_id.smul continuous_const).comp hscal

theorem secondOrderFree_eq (α β : ℝ) : secondOrderFree α β = fun t => α + β * t := rfl

theorem continuous_secondOrderFree (α β : ℝ) : Continuous (secondOrderFree α β) := by
  rw [secondOrderFree_eq]
  fun_prop

theorem locallyBounded_secondOrder {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) :
    VolterraLocallyBounded (secondOrderFree α β) (secondOrderKernel P) := by
  intro T hT
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hP.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (P 0)) (hB 0 ⟨by linarith, hT⟩)
  refine ⟨2 * T * B, |α| + |β| * T, by positivity, by positivity, ?_, ?_⟩
  · intro t s ht hs
    refine le_trans (norm_secondOrderKernel_le P t s) ?_
    have hst : |t - s| ≤ 2 * T := by
      have h1 := abs_le.1 ht
      have h2 := abs_le.1 hs
      rw [abs_le]
      constructor <;> linarith
    have hPs : |P s| ≤ B := by
      have := hB s ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
      rwa [Real.norm_eq_abs] at this
    rw [abs_mul]
    calc |t - s| * |P s| ≤ (2 * T) * B :=
          mul_le_mul hst hPs (abs_nonneg _) (by linarith)
      _ = 2 * T * B := by ring
  · intro t ht
    rw [secondOrderFree, Real.norm_eq_abs]
    calc |α + β * t| ≤ |α| + |β * t| := abs_add_le _ _
      _ = |α| + |β| * |t| := by rw [abs_mul]
      _ ≤ |α| + |β| * T := by
          have : |β| * |t| ≤ |β| * T := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
          linarith

theorem continuous_secondOrderSolution {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) :
    Continuous (secondOrderSolution P α β) :=
  continuous_volterraSolution_of_locallyBounded (continuous_secondOrderFree α β)
    (continuous_secondOrderKernel hP) (locallyBounded_secondOrder hP α β)

/-- **The Volterra form of the initial value problem.** -/
theorem secondOrderSolution_volterra {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) (ξ : ℝ) :
    secondOrderSolution P α β ξ
      = α + β * ξ + ∫ t in (0 : ℝ)..ξ, (ξ - t) * P t * secondOrderSolution P α β t := by
  have h := volterraSolution_eq_of_locallyBounded (continuous_secondOrderFree α β)
    (continuous_secondOrderKernel hP) (locallyBounded_secondOrder hP α β) ξ
  rw [secondOrderSolution, h, secondOrderFree]
  congr 1

@[simp]
theorem secondOrderSolution_zero {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) :
    secondOrderSolution P α β 0 = α := by
  have h := secondOrderSolution_volterra hP α β 0
  simpa using h

/-- The derivative of the solution. -/
def secondOrderDeriv (P : ℝ → ℝ) (α β : ℝ) : ℝ → ℝ :=
  fun ξ => β + ∫ t in (0 : ℝ)..ξ, P t * secondOrderSolution P α β t

theorem secondOrderDeriv_eq (P : ℝ → ℝ) (α β : ℝ) :
    secondOrderDeriv P α β
      = fun ξ => β + ∫ t in (0 : ℝ)..ξ, P t * secondOrderSolution P α β t := rfl

@[simp]
theorem secondOrderDeriv_zero (P : ℝ → ℝ) (α β : ℝ) : secondOrderDeriv P α β 0 = β := by
  rw [secondOrderDeriv]
  simp

theorem hasDerivAt_integral_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (a x : ℝ) :
    HasDerivAt (fun u => ∫ t in a..u, g t) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a x)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

/-- The Volterra form with the `ξ` pulled out of the kernel. -/
theorem secondOrderSolution_split {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) (ξ : ℝ) :
    secondOrderSolution P α β ξ
      = α + β * ξ + ξ * (∫ t in (0 : ℝ)..ξ, P t * secondOrderSolution P α β t)
        - ∫ t in (0 : ℝ)..ξ, t * (P t * secondOrderSolution P α β t) := by
  have hg : Continuous fun t => P t * secondOrderSolution P α β t :=
    hP.mul (continuous_secondOrderSolution hP α β)
  have h1 : IntervalIntegrable (fun t => ξ * (P t * secondOrderSolution P α β t))
      volume 0 ξ := (continuous_const.mul hg).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => t * (P t * secondOrderSolution P α β t))
      volume 0 ξ := (continuous_id.mul hg).intervalIntegrable _ _
  rw [secondOrderSolution_volterra hP]
  have hsplit : (∫ t in (0 : ℝ)..ξ, (ξ - t) * P t * secondOrderSolution P α β t)
      = (∫ t in (0 : ℝ)..ξ, ξ * (P t * secondOrderSolution P α β t))
        - ∫ t in (0 : ℝ)..ξ, t * (P t * secondOrderSolution P α β t) := by
    rw [← intervalIntegral.integral_sub h1 h2]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsplit, intervalIntegral.integral_const_mul]
  ring

/-- **The solution differentiates to `secondOrderDeriv`.** -/
theorem hasDerivAt_secondOrderSolution {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) (ξ : ℝ) :
    HasDerivAt (secondOrderSolution P α β) (secondOrderDeriv P α β ξ) ξ := by
  have hg : Continuous fun t => P t * secondOrderSolution P α β t :=
    hP.mul (continuous_secondOrderSolution hP α β)
  have hgt : Continuous fun t : ℝ => t * (P t * secondOrderSolution P α β t) :=
    continuous_id.mul hg
  have hW := hasDerivAt_integral_of_continuous hg 0 ξ
  have hZ := hasDerivAt_integral_of_continuous hgt 0 ξ
  have hbase : HasDerivAt
      (fun x : ℝ => α + β * x + x * (∫ t in (0 : ℝ)..x, P t * secondOrderSolution P α β t)
        - ∫ t in (0 : ℝ)..x, t * (P t * secondOrderSolution P α β t))
      (β + ((∫ t in (0 : ℝ)..ξ, P t * secondOrderSolution P α β t)
          + ξ * (P ξ * secondOrderSolution P α β ξ))
        - ξ * (P ξ * secondOrderSolution P α β ξ)) ξ := by
    have h1 : HasDerivAt (fun x : ℝ => α + β * x) β ξ := by
      simpa using ((hasDerivAt_id ξ).const_mul β).const_add α
    have h2 : HasDerivAt
        (fun x : ℝ => x * ∫ t in (0 : ℝ)..x, P t * secondOrderSolution P α β t)
        ((∫ t in (0 : ℝ)..ξ, P t * secondOrderSolution P α β t)
          + ξ * (P ξ * secondOrderSolution P α β ξ)) ξ := by
      have hid : HasDerivAt (fun x : ℝ => x) 1 ξ := hasDerivAt_id ξ
      have hmul := hid.mul hW
      refine hmul.congr_deriv ?_
      ring
    exact (h1.add h2).sub hZ
  have hfun : secondOrderSolution P α β
      = fun x : ℝ => α + β * x + x * (∫ t in (0 : ℝ)..x, P t * secondOrderSolution P α β t)
        - ∫ t in (0 : ℝ)..x, t * (P t * secondOrderSolution P α β t) :=
    funext fun x => secondOrderSolution_split hP α β x
  rw [hfun]
  refine hbase.congr_deriv ?_
  rw [secondOrderDeriv]
  ring

/-- **The derivative differentiates to `P·v`: the differential equation.** -/
theorem hasDerivAt_secondOrderDeriv {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) (ξ : ℝ) :
    HasDerivAt (secondOrderDeriv P α β) (P ξ * secondOrderSolution P α β ξ) ξ := by
  have hg : Continuous fun t => P t * secondOrderSolution P α β t :=
    hP.mul (continuous_secondOrderSolution hP α β)
  rw [secondOrderDeriv_eq]
  simpa using (hasDerivAt_integral_of_continuous hg 0 ξ).const_add β

/-- **Global existence.**  For a continuous coefficient the linear second-order initial value
problem has a solution on the whole line. -/
theorem exists_secondOrder_solution {P : ℝ → ℝ} (hP : Continuous P) (α β : ℝ) :
    ∃ v v' : ℝ → ℝ, v 0 = α ∧ v' 0 = β ∧
      (∀ ξ, HasDerivAt v (v' ξ) ξ) ∧ (∀ ξ, HasDerivAt v' (P ξ * v ξ) ξ) :=
  ⟨secondOrderSolution P α β, secondOrderDeriv P α β, secondOrderSolution_zero hP α β,
    secondOrderDeriv_zero P α β, hasDerivAt_secondOrderSolution hP α β,
    hasDerivAt_secondOrderDeriv hP α β⟩

end GaloisForLFunctions.HTGeometry
