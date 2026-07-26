import GaloisForLFunctions.RHTower.ThetaPrimeCubeCrossedPhaseRadialFactorizationUniversalityLaw
import GaloisForLFunctions.RHTower.ThetaProductFiberFixedPointCenterEscapeUniversalityLaw

/-!
# Theta prime-cube endpoint two-heat-shell universality

The four ordered divisor atoms in a prime-cube theta product fibre pair into two unoriented
Gaussian heat shells.  Consequently the corrected fixed-point seam has an exact two-shell
centre-escape limit, with no residual divisor sum.
-/

open Complex Real Finset Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact two-shell fixed-point current of the prime-cube product fibre. -/
def thetaPrimeCubeEndpointTwoHeatShellCurrent (p : ℕ) : ℝ :=
  16 * Real.exp (-Real.pi * (1 + (p : ℝ) ^ 6)) *
      (2 * Real.pi * (1 + (p : ℝ) ^ 6) - 1) +
    16 * Real.exp (-Real.pi * ((p : ℝ) ^ 2 + (p : ℝ) ^ 4)) *
      (2 * Real.pi * ((p : ℝ) ^ 2 + (p : ℝ) ^ 4) - 1)

/-- The four ordered prime-cube endpoint atoms collapse exactly into the outer and inner
unoriented heat shells. -/
theorem thetaPrimeCube_endpointGibbsSum_eq_twoHeatShellCurrent
    {p : ℕ} (hp : p.Prime) :
    (∑ q ∈ thetaPositiveFactorPairs (p ^ 3),
      (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ 2)) *
        ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ 2 - 2) *
          Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ 2))) =
      thetaPrimeCubeEndpointTwoHeatShellCurrent p := by
  rw [thetaPositiveFactorPairs_prime_cube hp]
  have hpOne : 1 ≤ p := hp.one_lt.le
  have hp2One : 1 ≤ p ^ 2 := by
    exact one_le_pow₀ hpOne
  have hp3One : 1 ≤ p ^ 3 := by
    exact one_le_pow₀ hpOne
  have hpp : p < p ^ 2 := by
    calc
      p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
      _ = p ^ 2 := by ring
  have hp2p3 : p ^ 2 < p ^ 3 := by
    calc
      p ^ 2 < p ^ 2 * p :=
        lt_mul_of_one_lt_right (pow_pos hp.pos 2) hp.one_lt
      _ = p ^ 3 := by ring
  have hleft : (0, p ^ 3 - 1) ∉
      ({(p - 1, p ^ 2 - 1), (p ^ 2 - 1, p - 1), (p ^ 3 - 1, 0)} :
        Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    omega
  have hinnerLeft : (p - 1, p ^ 2 - 1) ∉
      ({(p ^ 2 - 1, p - 1), (p ^ 3 - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro heq
      have hfst : p - 1 = p ^ 2 - 1 := congrArg Prod.fst heq
      omega
    · intro heq
      have hfst : p - 1 = p ^ 3 - 1 := congrArg Prod.fst heq
      omega
  have hinnerRight : (p ^ 2 - 1, p - 1) ∉
      ({(p ^ 3 - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    intro heq
    have hfst : p ^ 2 - 1 = p ^ 3 - 1 := congrArg Prod.fst heq
    omega
  rw [Finset.sum_insert hleft, Finset.sum_insert hinnerLeft,
    Finset.sum_insert hinnerRight, Finset.sum_singleton]
  simp only [zero_add, Nat.cast_one, one_pow,
    Nat.sub_add_cancel hpOne, Nat.sub_add_cancel hp2One,
    Nat.sub_add_cancel hp3One, Nat.cast_pow]
  unfold thetaPrimeCubeEndpointTwoHeatShellCurrent
  ring_nf
  have houter :
      Real.exp (-Real.pi) * Real.exp (-(Real.pi * (p : ℝ) ^ 6)) =
        Real.exp (-Real.pi - Real.pi * (p : ℝ) ^ 6) := by
    rw [← Real.exp_add]
    congr 1
  have hinner :
      Real.exp (-(Real.pi * (p : ℝ) ^ 2)) *
          Real.exp (-(Real.pi * (p : ℝ) ^ 4)) =
        Real.exp (-(Real.pi * (p : ℝ) ^ 2) -
          Real.pi * (p : ℝ) ^ 4) := by
    rw [← Real.exp_add]
    congr 1
  calc
    _ =
        32 * Real.pi * ((p : ℝ) ^ 6 + 1) *
            (Real.exp (-Real.pi) *
              Real.exp (-(Real.pi * (p : ℝ) ^ 6))) -
          16 * (Real.exp (-Real.pi) *
            Real.exp (-(Real.pi * (p : ℝ) ^ 6))) +
        32 * Real.pi * ((p : ℝ) ^ 2 + (p : ℝ) ^ 4) *
            (Real.exp (-(Real.pi * (p : ℝ) ^ 2)) *
              Real.exp (-(Real.pi * (p : ℝ) ^ 4))) -
          16 * (Real.exp (-(Real.pi * (p : ℝ) ^ 2)) *
            Real.exp (-(Real.pi * (p : ℝ) ^ 4))) := by ring
    _ =
        32 * Real.pi * ((p : ℝ) ^ 6 + 1) *
            Real.exp (-Real.pi - Real.pi * (p : ℝ) ^ 6) -
          16 * Real.exp (-Real.pi - Real.pi * (p : ℝ) ^ 6) +
        32 * Real.pi * ((p : ℝ) ^ 2 + (p : ℝ) ^ 4) *
            Real.exp (-(Real.pi * (p : ℝ) ^ 2) -
              Real.pi * (p : ℝ) ^ 4) -
          16 * Real.exp (-(Real.pi * (p : ℝ) ^ 2) -
            Real.pi * (p : ℝ) ^ 4) := by rw [houter, hinner]
    _ = _ := by ring

/-- **Prime-cube endpoint two-heat-shell universality law.**  At every prime cube, escaping the
common tail centre converges to the explicit sum of one outer and one inner positive heat shell. -/
theorem thetaPrimeCube_endpointTwoHeatShellUniversality
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun c : ℝ =>
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent (p ^ 3) c 0)
      atTop
      (nhds (thetaPrimeCubeEndpointTwoHeatShellCurrent p)) ∧
    0 < thetaPrimeCubeEndpointTwoHeatShellCurrent p := by
  simpa only [thetaPrimeCube_endpointGibbsSum_eq_twoHeatShellCurrent hp] using
    thetaProductFiber_fixedPoint_centerEscape_positiveGibbsUniversality
      (p ^ 3) (pow_pos hp.pos 3)

end

end RHTower
