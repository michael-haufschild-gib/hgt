import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelUpperTonelliNoGo
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalResidualDivisorCarrier

/-!
# Finite Abel renormalization of the positive Route-T Borel ray

The positive normal Borel ray cannot be summed by sourcewise absolute Tonelli.  This module keeps
one finite prime-source cutoff and its terminal residual flux before integration.  Finite Abel
transport then proves an exact, source-faithful identity: the terminal-plus-edge Borel cutoff is
the Borel lift of the Wold current minus the right-endpoint log-mesh current minus static holonomy.
After scalar Borel--Laplace integration, the same cutoff lands exactly on the corresponding upper
phase current.  No infinite interchange or convergence premise is used.

Consequently lateral continuation has one precise burden: continue this renormalized finite family
while retaining its terminal flux.  Borel summation cannot bypass the Wold--mesh cancellation or
erase the residual terminal that carries every possible off-line pole.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section


/-- One source node of the order-two Borel transform, before taking its discrete boundary. -/
def xiHeatCassiniWoldResidualBorelNode (x : ℝ) (xi : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeNegativePhase N x *
    secondFactorialBorelKernel
      ((-Complex.I * (xiMassNthPrimeLogHeight N : ℂ)) * xi)

/-- The source-labelled Borel edge is the discrete boundary of adjacent Borel nodes. -/
def xiHeatCassiniWoldResidualBorelSourceEdge (x : ℝ) (xi : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (xiHeatCassiniWoldResidualBorelNode x xi N - xiHeatCassiniWoldResidualBorelNode x xi (N + 1))

theorem xiHeatCassiniWoldResidualBorelNode_upperRay (x s : ℝ) (N : ℕ) :
    xiHeatCassiniWoldResidualBorelNode x (Complex.I * (s : ℂ)) N =
      xiHeatCassiniOrderedPrimeNegativePhase N x *
        secondFactorialBorelKernel
          ((xiMassNthPrimeLogHeight N * s : ℝ) : ℂ) := by
  unfold xiHeatCassiniWoldResidualBorelNode
  congr 2
  calc
    -Complex.I * (xiMassNthPrimeLogHeight N : ℂ) *
        (Complex.I * (s : ℂ)) =
      -(Complex.I * Complex.I) *
        ((xiMassNthPrimeLogHeight N : ℂ) * (s : ℂ)) := by ring
    _ = ((xiMassNthPrimeLogHeight N * s : ℝ) : ℂ) := by
      rw [Complex.I_mul_I]
      push_cast
      ring

theorem xiHeatCassiniWoldResidualBorelSourceEdge_upperRay (x s : ℝ) (N : ℕ) :
    xiHeatCassiniWoldResidualBorelSourceEdge x (Complex.I * (s : ℂ)) N =
      xiHeatCassiniWoldResidualBorelUpperRaySourceAtom x s N := by
  unfold xiHeatCassiniWoldResidualBorelSourceEdge xiHeatCassiniWoldResidualBorelUpperRaySourceAtom
  rw [xiHeatCassiniWoldResidualBorelNode_upperRay, xiHeatCassiniWoldResidualBorelNode_upperRay]

theorem xiHeatCassiniWoldResidualBorelFiniteAbel (x : ℝ) (xi : ℂ) (N : ℕ) :
    (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
        xiHeatCassiniWoldResidualBorelNode x xi N +
      ∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelSourceEdge x xi n =
    (xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 : ℂ) *
        xiHeatCassiniWoldResidualBorelNode x xi 0 +
      ∑ n ∈ Finset.range N,
        ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (n + 1) -
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy n : ℝ) : ℂ) *
            xiHeatCassiniWoldResidualBorelNode x xi (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ] at ih ⊢
      rw [xiHeatCassiniWoldResidualBorelSourceEdge]
      push_cast at ih ⊢
      calc
        (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) : ℂ) *
              xiHeatCassiniWoldResidualBorelNode x xi (N + 1) +
            ((∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelSourceEdge x xi n) +
              (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
                (xiHeatCassiniWoldResidualBorelNode x xi N - xiHeatCassiniWoldResidualBorelNode x xi (N + 1))) =
            ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
                xiHeatCassiniWoldResidualBorelNode x xi N +
              ∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelSourceEdge x xi n) +
              ((xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) : ℂ) -
                xiHeatCassiniOrderedWoldResidualLogDiscrepancy N) *
                  xiHeatCassiniWoldResidualBorelNode x xi (N + 1) := by ring
        _ = _ := by rw [ih]; ring

/-- Wold node before Borel--Laplace integration. -/
def xiHeatCassiniWoldResidualBorelWoldNodeAtom (x : ℝ) (xi : ℂ) (N : ℕ) : ℂ :=
  (woldCoeff 1 (nthPrimeSubtype N) : ℂ) * xiHeatCassiniWoldResidualBorelNode x xi N

/-- Right-endpoint log-mesh node before Borel--Laplace integration. -/
def xiHeatCassiniWoldResidualBorelLogMeshNodeAtom (x : ℝ) (xi : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedPrimeLogGap N : ℂ) * xiHeatCassiniWoldResidualBorelNode x xi (N + 1)

theorem xiHeatCassiniWoldResidualBorelFiniteRenormalization (x : ℝ) (xi : ℂ) (N : ℕ) :
    (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
        xiHeatCassiniWoldResidualBorelNode x xi N +
      ∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelSourceEdge x xi n =
    (∑ n ∈ Finset.range (N + 1), xiHeatCassiniWoldResidualBorelWoldNodeAtom x xi n) -
      (∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelLogMeshNodeAtom x xi n) -
      ((xiMassNthPrimeLogHeight 0 +
        xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) *
          xiHeatCassiniWoldResidualBorelNode x xi 0 := by
  rw [xiHeatCassiniWoldResidualBorelFiniteAbel]
  conv_lhs =>
    enter [2, 2, n]
    rw [xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub]
  rw [show (∑ n ∈ Finset.range N,
      ((woldCoeff 1 (nthPrimeSubtype (n + 1)) -
        (xiMassNthPrimeLogHeight (n + 1) -
          xiMassNthPrimeLogHeight n) : ℝ) : ℂ) *
            xiHeatCassiniWoldResidualBorelNode x xi (n + 1)) =
      (∑ n ∈ Finset.range N,
        (woldCoeff 1 (nthPrimeSubtype (n + 1)) : ℂ) *
          xiHeatCassiniWoldResidualBorelNode x xi (n + 1)) -
      ∑ n ∈ Finset.range N,
        ((xiMassNthPrimeLogHeight (n + 1) -
          xiMassNthPrimeLogHeight n : ℝ) : ℂ) *
            xiHeatCassiniWoldResidualBorelNode x xi (n + 1) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      push_cast
      ring]
  rw [show (∑ n ∈ Finset.range N,
      (woldCoeff 1 (nthPrimeSubtype (n + 1)) : ℂ) *
        xiHeatCassiniWoldResidualBorelNode x xi (n + 1)) =
      ∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelWoldNodeAtom x xi (n + 1) by rfl]
  rw [show (∑ n ∈ Finset.range N,
      ((xiMassNthPrimeLogHeight (n + 1) -
        xiMassNthPrimeLogHeight n : ℝ) : ℂ) *
          xiHeatCassiniWoldResidualBorelNode x xi (n + 1)) =
      ∑ n ∈ Finset.range N, xiHeatCassiniWoldResidualBorelLogMeshNodeAtom x xi n by
        apply Finset.sum_congr rfl
        intro n hn
        unfold xiHeatCassiniWoldResidualBorelLogMeshNodeAtom xiHeatCassiniOrderedPrimeLogGap
        push_cast
        rfl]
  rw [Finset.sum_range_succ']
  unfold xiHeatCassiniWoldResidualBorelWoldNodeAtom
  have hzeroC := congrArg (fun u : ℝ => (u : ℂ))
    xiHeatCassiniWoldResidualLogDiscrepancy_zero_sub_woldCoeff
  push_cast at hzeroC
  push_cast
  linear_combination hzeroC * xiHeatCassiniWoldResidualBorelNode x xi 0

/-- Exponentially damped positive-normal Borel node. -/
def xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom
    (x y : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-t) : ℝ) : ℂ) *
    xiHeatCassiniWoldResidualBorelNode x (Complex.I * ((y * t : ℝ) : ℂ)) N

theorem integrableOn_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    IntegrableOn (xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N) (Ioi 0) := by
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let w : ℂ := ((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ)
  have h :=
    (integrableOn_exp_neg_mul_secondFactorialBorelKernel w).const_mul A
  apply MeasureTheory.IntegrableOn.congr_fun h
  · intro t ht
    rw [xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom, xiHeatCassiniWoldResidualBorelNode_upperRay]
    dsimp only [A, w]
    have hw :
        ((xiMassNthPrimeLogHeight N * (y * t) : ℝ) : ℂ) =
          ((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ) * (t : ℂ) := by
      push_cast
      ring
    rw [hw]
    ring
  · exact measurableSet_Ioi

theorem integral_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    (∫ t : ℝ in Ioi 0, xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N t) =
      xiHeatCassiniOrderedPrimeComplexNegativePhase N
        ((x : ℂ) + Complex.I * (y : ℂ)) := by
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let w : ℂ := ((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ)
  rw [show (fun t : ℝ => xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N t) =
      fun t : ℝ => A *
        (((Real.exp (-t) : ℝ) : ℂ) *
          secondFactorialBorelKernel (w * (t : ℂ))) by
    funext t
    rw [xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom, xiHeatCassiniWoldResidualBorelNode_upperRay]
    dsimp only [A, w]
    have hw :
        ((xiMassNthPrimeLogHeight N * (y * t) : ℝ) : ℂ) =
          ((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ) * (t : ℂ) := by
      push_cast
      ring
    rw [hw]
    ring]
  rw [integral_const_mul, integral_secondFactorialBorelKernel_eq_exp]
  dsimp only [A, w]
  unfold xiHeatCassiniOrderedPrimeNegativePhase
    xiHeatCassiniOrderedPrimeComplexNegativePhase
  rw [← Complex.exp_add]
  congr 1
  rw [mul_add]
  rw [show Complex.I * (xiMassNthPrimeLogHeight N : ℂ) *
      (Complex.I * (y : ℂ)) =
      -((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ) by
    calc
      Complex.I * (xiMassNthPrimeLogHeight N : ℂ) *
          (Complex.I * (y : ℂ)) =
        (Complex.I * Complex.I) *
          ((xiMassNthPrimeLogHeight N : ℂ) * (y : ℂ)) := by ring
      _ = -((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ) := by
        rw [Complex.I_mul_I]
        push_cast
        ring]
  push_cast
  ring

theorem integral_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    (∫ t : ℝ in Ioi 0,
      xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y N t) =
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        ((x : ℂ) + Complex.I * (y : ℂ)) N := by
  let R : ℂ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  have hn := integrableOn_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N
  have hs := integrableOn_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y (N + 1)
  rw [show (fun t : ℝ =>
      xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y N t) =
      fun t : ℝ => R *
        (xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N t -
          xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y (N + 1) t) by
    funext t
    rw [xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom,
      ← xiHeatCassiniWoldResidualBorelSourceEdge_upperRay]
    unfold xiHeatCassiniWoldResidualBorelSourceEdge xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom
    dsimp only [R]
    ring]
  rw [integral_const_mul, integral_sub hn hs,
    integral_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom,
    integral_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom]
  rfl

/-- Terminal-plus-edge positive-normal Borel cutoff. -/
def xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace
    (x y : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
      xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N t +
    ∑ n ∈ Finset.range N,
      xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t

theorem integrableOn_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace
    (x y : ℝ) (N : ℕ) :
    IntegrableOn (xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace x y N) (Ioi 0) := by
  apply Integrable.add
  · exact (integrableOn_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N).const_mul _
  · apply integrable_finsetSum
    intro n hn
    exact integrableOn_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom
      x y n

/-- Exact positive-ray cutoff landing before any infinite interchange. -/
theorem integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace
    (x y : ℝ) (N : ℕ) :
    (∫ t : ℝ in Ioi 0, xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace x y N t) =
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase N
          ((x : ℂ) + Complex.I * (y : ℂ)) +
      ∑ n ∈ Finset.range N,
        xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          ((x : ℂ) + Complex.I * (y : ℂ)) n := by
  have hnode := integrableOn_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom x y N
  have hedge : ∀ n ∈ Finset.range N,
      IntegrableOn
        (xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n) (Ioi 0) :=
    fun n hn =>
      integrableOn_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n
  unfold xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace
  rw [integral_add (hnode.const_mul _)
      (integrable_finsetSum (Finset.range N) hedge),
    integral_const_mul,
    integral_xiHeatCassiniWoldResidualBorelUpperRayNodeLaplaceAtom,
    integral_finsetSum (Finset.range N) hedge]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n

def xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent
    (x y : ℝ) (N : ℕ) : ℂ :=
  let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  (∑ n ∈ Finset.range (N + 1),
      (woldCoeff 1 (nthPrimeSubtype n) : ℂ) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase n z) -
    (∑ n ∈ Finset.range N,
      (xiHeatCassiniOrderedPrimeLogGap n : ℂ) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase (n + 1) z) -
    ((xiMassNthPrimeLogHeight 0 +
      xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase 0 z

/-- Positive Borel cutoff is exactly finite Wold--mesh--holonomy renormalization. -/
theorem integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace_eq_renormalized
    (x y : ℝ) (N : ℕ) :
    (∫ t : ℝ in Ioi 0, xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace x y N t) =
      xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N := by
  rw [integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace]
  let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have habel := xiHeatCassiniWoldResidualComplexFiniteAbel N z
  rw [habel]
  unfold xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent
  dsimp only [z]
  conv_lhs =>
    enter [2, 2, n]
    rw [xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub]
  rw [show (∑ n ∈ Finset.range N,
      ((woldCoeff 1 (nthPrimeSubtype (n + 1)) -
        (xiMassNthPrimeLogHeight (n + 1) -
          xiMassNthPrimeLogHeight n) : ℝ) : ℂ) *
            xiHeatCassiniOrderedPrimeComplexNegativePhase (n + 1) z) =
      (∑ n ∈ Finset.range N,
        (woldCoeff 1 (nthPrimeSubtype (n + 1)) : ℂ) *
          xiHeatCassiniOrderedPrimeComplexNegativePhase (n + 1) z) -
      ∑ n ∈ Finset.range N,
        (xiHeatCassiniOrderedPrimeLogGap n : ℂ) *
          xiHeatCassiniOrderedPrimeComplexNegativePhase (n + 1) z by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      unfold xiHeatCassiniOrderedPrimeLogGap
      push_cast
      ring]
  rw [Finset.sum_range_succ']
  have hzeroC := congrArg (fun u : ℝ => (u : ℂ))
    xiHeatCassiniWoldResidualLogDiscrepancy_zero_sub_woldCoeff
  push_cast at hzeroC
  push_cast
  linear_combination
    hzeroC * xiHeatCassiniOrderedPrimeComplexNegativePhase 0 z

theorem xiHeatCassiniOrderedPrimeLaplacePhase_I_mul (N : ℕ) (z : ℂ) :
    xiHeatCassiniOrderedPrimeLaplacePhase N (Complex.I * z) =
      xiHeatCassiniOrderedPrimeComplexNegativePhase N z := by
  unfold xiHeatCassiniOrderedPrimeLaplacePhase
  congr 1
  calc
    -Complex.I * (Complex.I * z) =
        -(Complex.I * Complex.I) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; ring

/-- The Borel renormalization is literally the existing finite Laplace Wold--mesh--holonomy
cutoff at the rotated upper coordinate. -/
theorem xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_eq_laplaceCutoff
    (x y : ℝ) (N : ℕ) :
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N =
      let s : ℂ := Complex.I * ((x : ℂ) + Complex.I * (y : ℂ))
      (∑ n ∈ Finset.range (N + 1), xiHeatCassiniWoldLaplaceAtom s n) -
        (∑ n ∈ Finset.range N, xiHeatCassiniLogMeshLaplaceAtom s n) -
        xiHeatCassiniWoldLaplaceHolonomyCounterterm s := by
  unfold xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent
    xiHeatCassiniWoldLaplaceAtom xiHeatCassiniLogMeshLaplaceAtom
    xiHeatCassiniWoldLaplaceHolonomyCounterterm
  dsimp only
  simp_rw [xiHeatCassiniOrderedPrimeLaplacePhase_I_mul]

theorem integral_finset_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    (∫ t : ℝ in Ioi 0,
      ∑ n ∈ Finset.range N,
        xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t) =
      ∑ n ∈ Finset.range N,
        xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          ((x : ℂ) + Complex.I * (y : ℂ)) n := by
  have hedge : ∀ n ∈ Finset.range N,
      IntegrableOn
        (xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n) (Ioi 0) :=
    fun n hn =>
      integrableOn_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n
  rw [integral_finsetSum (Finset.range N) hedge]
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n

/-- Exact terminal obstruction left after cancellation-first positive Borel integration. -/
theorem xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral
    (x y : ℝ) (N : ℕ) :
    xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
        (∫ t : ℝ in Ioi 0,
          ∑ n ∈ Finset.range N,
            xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t) =
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase N
          ((x : ℂ) + Complex.I * (y : ℂ)) := by
  rw [← integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace_eq_renormalized,
    integral_xiHeatCassiniWoldResidualBorelUpperRayFiniteJointLaplace,
    integral_finset_xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom]
  ring

/-- Exact size of the surviving terminal: phase cancellation removes `x`, but not upper height. -/
theorem norm_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral
    (x y : ℝ) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
        (∫ t : ℝ in Ioi 0,
          ∑ n ∈ Finset.range N,
            xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t)‖ =
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (xiMassNthPrimeLogHeight N * y) := by
  rw [xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_xiHeatCassiniOrderedPrimeComplexNegativePhase]
  congr 2
  simp

/-- Terminal-flux classification of cancellation-first positive Borel convergence. -/
theorem
    tendsto_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral_zero_iff
    (x y : ℝ) :
    Tendsto (fun N : ℕ =>
      xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
        (∫ t : ℝ in Ioi 0,
          ∑ n ∈ Finset.range N,
            xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t))
      atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ =>
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (xiMassNthPrimeLogHeight N * y)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_congr'
  exact Eventually.of_forall fun N =>
    norm_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral
      x y N

/-- The terminal obstruction cannot vanish beyond the critical half height. -/
theorem
    not_tendsto_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral_zero_of_half_lt
    (x : ℝ) {y : ℝ} (hy : 1 / 2 < y) :
    ¬Tendsto (fun N : ℕ =>
      xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
        (∫ t : ℝ in Ioi 0,
          ∑ n ∈ Finset.range N,
            xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t))
      atTop (𝓝 0) := by
  intro hterminal
  have hweighted :=
    (tendsto_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral_zero_iff
      x y).mp hterminal
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          Real.exp (xiMassNthPrimeLogHeight N * y) < 1 :=
    hweighted (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        1 * Real.exp (-y * xiMassNthPrimeLogHeight N) := by
    filter_upwards [hsmall] with N hN
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| =
          (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            Real.exp (xiMassNthPrimeLogHeight N * y)) *
              Real.exp (-y * xiMassNthPrimeLogHeight N) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ 1 * Real.exp (-y * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_right hN.le (Real.exp_nonneg _)
  exact not_eventually_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate_of_half_lt
    hy (by norm_num) hrate


end

end RHTower
