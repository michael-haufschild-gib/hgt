import GaloisForLFunctions.HTGeometry.ClockTubeMixedSecond
import GaloisForLFunctions.HTGeometry.ClockNullMultiDalembert
import GaloisForLFunctions.HTGeometry.ClockTubeRealKernels
import GaloisForLFunctions.HTGeometry.ClockRealProbeData

/-!
# The real field of the clock construction with several transverse coordinates

The field of the clock probe is the real part of the solution at real transverse points. Taking the
real part costs nothing: it is a continuous linear map, so it commutes with every derivative taken so
far, and the real points lie inside every tube, so each transverse variable is a genuine real
variable there.

This file records the real functions the chart calculus consumes — the field, its two null and `k`
transverse first derivatives, and its second derivatives — and assembles them into the
differentiability records that the d'Alembertian of the several-variable chart asks for.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

theorem realTube_update (y : Fin k → ℝ) (i : Fin k) (a : ℝ) :
    realTube (Function.update y i a) = Function.update (realTube y) i ((a : ℝ) : ℂ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [realTube]
  · simp [realTube, Function.update_of_ne hj]

/-! ## The real functions -/

/-- The field of the clock probe: the real part of the solution at real transverse points. -/
noncomputable def probeMultiU (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (tubeSolution V (boxClamp T s) (boxClamp T t) (realTube y)).re

/-- Its derivative along the first null coordinate. -/
noncomputable def probeMultiA (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..t, clampedTubeStep V T (realTube y) s r).re

/-- Its derivative along the second null coordinate. -/
noncomputable def probeMultiB (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..s, clampedTubeStep V T (realTube y) r t).re

/-- Its derivative along a transverse coordinate. -/
noncomputable def probeMultiC (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (i : Fin k) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (cpartial i (clampedTubeSolution V T (s, t)) (realTube y)).re

/-- The pure second derivative along the first null coordinate. -/
noncomputable def probeMultiAa (V Vs : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..t, clampedTubeStepFst V Vs T (realTube y) s r).re

/-- The mixed null second derivative, which is the step operator itself. -/
noncomputable def probeMultiAb (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (clampedTubeStep V T (realTube y) s t).re

/-- The mixed derivative along the first null coordinate and a transverse one. -/
noncomputable def probeMultiAc (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (i : Fin k) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..t, dClampedTubeStep V T i (realTube y) s r).re

/-- The pure second derivative along the second null coordinate. -/
noncomputable def probeMultiBb (V Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..s, clampedTubeStepSnd V Vt T (realTube y) r t).re

/-- The mixed derivative along the second null coordinate and a transverse one. -/
noncomputable def probeMultiBc (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (i : Fin k) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..s, dClampedTubeStep V T i (realTube y) r t).re

/-- The second transverse derivative along two transverse coordinates. -/
noncomputable def probeMultiCc (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (i j : Fin k) (s t : ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (cpartial j (cpartial i (clampedTubeSolution V T (s, t))) (realTube y)).re

/-- The open rectangle of null coordinates, with the transverse points unrestricted. -/
def clockMultiBox (k : ℕ) (T : ℝ) : Set ((ℝ × ℝ) × (Fin k → ℝ)) :=
  {q | |q.1.1| < T ∧ |q.1.2| < T}

theorem isOpen_clockMultiBox (k : ℕ) (T : ℝ) : IsOpen (clockMultiBox k T) := by
  have h1 : IsOpen {q : (ℝ × ℝ) × (Fin k → ℝ) | |q.1.1| < T} :=
    isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_fst)) continuous_const
  have h2 : IsOpen {q : (ℝ × ℝ) × (Fin k → ℝ) | |q.1.2| < T} :=
    isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_fst)) continuous_const
  simpa [clockMultiBox, Set.setOf_and] using h1.inter h2

theorem mem_clockMultiBox {T : ℝ} {q : (ℝ × ℝ) × (Fin k → ℝ)} :
    q ∈ clockMultiBox k T ↔ |q.1.1| < T ∧ |q.1.2| < T := Iff.rfl

namespace TubeDatum

variable {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-- **The mixed transverse derivative of the solution along the real points.** -/
theorem continuous_d2SolMixedReal (i j : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      cpartial j (cpartial i (clampedTubeSolution V T q.1)) (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_cpartial_cpartial_mixed hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂ i j
    (q := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ))) (hD.memTube₂ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-! ## Continuity of the real functions -/

theorem continuous_probeMultiU :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiU V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp hD.continuous_solReal

theorem continuous_probeMultiA :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiA V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_innerRealTube (K := fun z s t => clampedTubeStep V T z s t) hD.continuous_stepReal)

theorem continuous_probeMultiB :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiB V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_outerRealTube (K := fun z s t => clampedTubeStep V T z s t) hD.continuous_stepReal)

theorem continuous_probeMultiC (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiC V T i q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp (hD.continuous_dSolReal i)

theorem continuous_probeMultiAa :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiAa V Vs T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_innerRealTube (K := fun z s t => clampedTubeStepFst V Vs T z s t)
      hD.continuous_stepFstReal)

theorem continuous_probeMultiAb :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiAb V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp hD.continuous_stepReal

theorem continuous_probeMultiAc (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiAc V T i q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_innerRealTube (K := fun z s t => dClampedTubeStep V T i z s t)
      (hD.continuous_dStepReal i))

theorem continuous_probeMultiBb :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiBb V Vt T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_outerRealTube (K := fun z s t => clampedTubeStepSnd V Vt T z s t)
      hD.continuous_stepSndReal)

theorem continuous_probeMultiBc (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiBc V T i q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_outerRealTube (K := fun z s t => dClampedTubeStep V T i z s t)
      (hD.continuous_dStepReal i))

theorem continuous_probeMultiCc (i j : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => probeMultiCc V T i j q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp (hD.continuous_d2SolMixedReal i j)

/-! ## The differentiability records -/

/-- **The field of the probe is continuously differentiable in all its variables.** -/
theorem isC1OnMulti_probeMultiU :
    IsC1OnMulti (probeMultiU V T) (probeMultiA V T) (probeMultiB V T) (probeMultiC V T)
      (clockMultiBox k T) where
  isOpen := isOpen_clockMultiBox k T
  hasDerivFst := by
    intro q hq
    have hcx := hasDerivAt_tubeSolution_fst hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg
      hD.rad hD.sideNonneg hD.small hq.1 (le_of_lt hq.2) (hD.absIm q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.1) fun x hx => ?_
    show probeMultiU V T x q.1.2 q.2 = _
    rw [probeMultiU, boxClamp_eq_self (le_of_lt hx), boxClamp_eq_self (le_of_lt hq.2)]
  hasDerivSnd := by
    intro q hq
    have hcx := hasDerivAt_tubeSolution_snd hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg
      hD.rad hD.sideNonneg hD.small (le_of_lt hq.1) hq.2 (hD.absIm q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.2) fun y hy => ?_
    show probeMultiU V T q.1.1 y q.2 = _
    rw [probeMultiU, boxClamp_eq_self (le_of_lt hq.1), boxClamp_eq_self (le_of_lt hy)]
  hasDerivTrans := by
    intro q _ i
    have hslice := sliceHolo_clampedTubeSolution hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small q.1 (realTube q.2) (hD.memTube q.2) i
    have hdiff := hslice.differentiableAt
      ((isOpen_imStrip ρ).mem_nhds (mem_imStrip.mpr (hD.memTube q.2 i)))
    have hfun : (fun a : ℝ => probeMultiU V T q.1.1 q.1.2 (Function.update q.2 i a))
        = fun a : ℝ =>
          (clampedTubeSolution V T q.1 (Function.update (realTube q.2) i ((a : ℝ) : ℂ))).re := by
      funext a
      rw [probeMultiU, realTube_update]
      rfl
    rw [hfun]
    exact hasDerivAt_re_ofReal hdiff.hasDerivAt
  contFst := hD.continuous_probeMultiA
  contSnd := hD.continuous_probeMultiB
  contTrans := hD.continuous_probeMultiC

/-- **The first null derivative is continuously differentiable in all its variables.** -/
theorem isC1OnMulti_probeMultiA :
    IsC1OnMulti (probeMultiA V T) (probeMultiAa V Vs T) (probeMultiAb V T) (probeMultiAc V T)
      (clockMultiBox k T) where
  isOpen := isOpen_clockMultiBox k T
  hasDerivFst := by
    intro q hq
    have hcx := hasDerivAt_deriv_tubeSolution_fst_fst hD.pos hD.potC1 hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Pos hD.rad₁ hD.rad₂Pos hD.rad₂
      hD.rad₃Nonneg hD.rad₃ hq.1 hq.2 (hD.memTube₃ q.2)
    have hint : (fun x : ℝ => ∫ r in (0 : ℝ)..q.1.2, clampedTubeStep V T (realTube q.2) x r)
        =ᶠ[nhds q.1.1]
        fun x : ℝ => deriv (fun y : ℝ => tubeSolution V y q.1.2 (realTube q.2)) x := by
      refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.1) fun x hx => ?_
      exact (deriv_tubeSolution_fst hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small hx (le_of_lt hq.2) (hD.absIm q.2)).symm
    exact hasDerivAt_re (hcx.congr_of_eventuallyEq hint)
  hasDerivSnd := by
    intro q _
    have hsl : Continuous fun r : ℝ => clampedTubeStep V T (realTube q.2) q.1.1 r :=
      (continuous_clampedTubeStep hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small (hD.absIm q.2)).comp
        (f := fun r : ℝ => ((q.1.1, r) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
    exact hasDerivAt_re (hsl.integral_hasStrictDerivAt 0 q.1.2).hasDerivAt
  hasDerivTrans := by
    intro q _ i
    have hcx := hasDerivAt_clampedTubeInner_transverse hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂ q.1.1 q.1.2
      (hD.memTube₂ q.2) i
    have hfun : (fun a : ℝ => probeMultiA V T q.1.1 q.1.2 (Function.update q.2 i a))
        = fun a : ℝ => (∫ r in (0 : ℝ)..q.1.2,
          clampedTubeStep V T (Function.update (realTube q.2) i ((a : ℝ) : ℂ)) q.1.1 r).re := by
      funext a
      rw [probeMultiA, realTube_update]
    rw [hfun]
    exact hasDerivAt_re_ofReal hcx
  contFst := hD.continuous_probeMultiAa
  contSnd := hD.continuous_probeMultiAb
  contTrans := hD.continuous_probeMultiAc

/-- **The second null derivative is continuously differentiable in all its variables.** -/
theorem isC1OnMulti_probeMultiB :
    IsC1OnMulti (probeMultiB V T) (probeMultiAb V T) (probeMultiBb V Vt T) (probeMultiBc V T)
      (clockMultiBox k T) where
  isOpen := isOpen_clockMultiBox k T
  hasDerivFst := by
    intro q _
    have hsl : Continuous fun r : ℝ => clampedTubeStep V T (realTube q.2) r q.1.2 :=
      (continuous_clampedTubeStep hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small (hD.absIm q.2)).comp
        (f := fun r : ℝ => ((r, q.1.2) : ℝ × ℝ)) (continuous_id.prodMk continuous_const)
    exact hasDerivAt_re (hsl.integral_hasStrictDerivAt 0 q.1.1).hasDerivAt
  hasDerivSnd := by
    intro q hq
    have hcx := hasDerivAt_deriv_tubeSolution_snd_snd hD.pos hD.potC1 hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Pos hD.rad₁ hD.rad₂Pos hD.rad₂
      hD.rad₃Nonneg hD.rad₃ hq.1 hq.2 (hD.memTube₃ q.2)
    have hint : (fun y : ℝ => ∫ r in (0 : ℝ)..q.1.1, clampedTubeStep V T (realTube q.2) r y)
        =ᶠ[nhds q.1.2]
        fun y : ℝ => deriv (fun x : ℝ => tubeSolution V q.1.1 x (realTube q.2)) y := by
      refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.2) fun y hy => ?_
      exact (deriv_tubeSolution_snd hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small (le_of_lt hq.1) hy (hD.absIm q.2)).symm
    exact hasDerivAt_re (hcx.congr_of_eventuallyEq hint)
  hasDerivTrans := by
    intro q _ i
    have hcx := hasDerivAt_clampedTubeOuter_transverse hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂ q.1.1 q.1.2
      (hD.memTube₂ q.2) i
    have hfun : (fun a : ℝ => probeMultiB V T q.1.1 q.1.2 (Function.update q.2 i a))
        = fun a : ℝ => (∫ r in (0 : ℝ)..q.1.1,
          clampedTubeStep V T (Function.update (realTube q.2) i ((a : ℝ) : ℂ)) r q.1.2).re := by
      funext a
      rw [probeMultiB, realTube_update]
    rw [hfun]
    exact hasDerivAt_re_ofReal hcx
  contFst := hD.continuous_probeMultiAb
  contSnd := hD.continuous_probeMultiBb
  contTrans := hD.continuous_probeMultiBc

/-- **Each transverse derivative is continuously differentiable in all its variables.** -/
theorem isC1OnMulti_probeMultiC (i : Fin k) :
    IsC1OnMulti (probeMultiC V T i) (probeMultiAc V T i) (probeMultiBc V T i)
      (probeMultiCc V T i) (clockMultiBox k T) where
  isOpen := isOpen_clockMultiBox k T
  hasDerivFst := by
    intro q hq
    have hcx := hasDerivAt_cpartial_tubeSolution_fst hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Pos hD.rad₁ hD.rad₂Nonneg hD.rad₂ i
      hq.1 (le_of_lt hq.2) (hD.memTube₂ q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.1) fun x hx => ?_
    show probeMultiC V T i x q.1.2 q.2 = _
    rw [probeMultiC, clampedTubeSolution, boxClamp_eq_self (le_of_lt hx),
      boxClamp_eq_self (le_of_lt hq.2)]
  hasDerivSnd := by
    intro q hq
    have hcx := hasDerivAt_cpartial_tubeSolution_snd hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Pos hD.rad₁ hD.rad₂Nonneg hD.rad₂ i
      (le_of_lt hq.1) hq.2 (hD.memTube₂ q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.2) fun y hy => ?_
    show probeMultiC V T i q.1.1 y q.2 = _
    rw [probeMultiC, clampedTubeSolution, boxClamp_eq_self (le_of_lt hq.1),
      boxClamp_eq_self (le_of_lt hy)]
  hasDerivTrans := by
    intro q _ j
    have hslice := sliceHolo_cpartial_clampedTubeSolution hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small i q.1 (realTube q.2) (hD.memTube q.2) j
    have hdiff := hslice.differentiableAt
      ((isOpen_imStrip ρ).mem_nhds (mem_imStrip.mpr (hD.memTube q.2 j)))
    have hfun : (fun a : ℝ => probeMultiC V T i q.1.1 q.1.2 (Function.update q.2 j a))
        = fun a : ℝ => (cpartial i (clampedTubeSolution V T q.1)
          (Function.update (realTube q.2) j ((a : ℝ) : ℂ))).re := by
      funext a
      rw [probeMultiC, realTube_update]
    rw [hfun]
    exact hasDerivAt_re_ofReal hdiff.hasDerivAt
  contFst := hD.continuous_probeMultiAc i
  contSnd := hD.continuous_probeMultiBc i
  contTrans := hD.continuous_probeMultiCc i

end TubeDatum

end GaloisForLFunctions.HTGeometry
