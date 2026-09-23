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
  16 * Real.exp (-Real.pi * (1 + (p : ℝ) ^ (6 : ℕ))) *
      (2 * Real.pi * (1 + (p : ℝ) ^ (6 : ℕ)) - 1) +
    16 * Real.exp (-Real.pi * ((p : ℝ) ^ (2 : ℕ) + (p : ℝ) ^ (4 : ℕ))) *
      (2 * Real.pi * ((p : ℝ) ^ (2 : ℕ) + (p : ℝ) ^ (4 : ℕ)) - 1)

/-- The four ordered prime-cube endpoint atoms collapse exactly into the outer and inner
unoriented heat shells. -/
theorem thetaPrimeCube_endpointGibbsSum_eq_twoHeatShellCurrent
    {p : ℕ} (hp : p.Prime) :
    (∑ q ∈ thetaPositiveFactorPairs (p ^ (3 : ℕ)),
      (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) *
        ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
          Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ)))) =
      thetaPrimeCubeEndpointTwoHeatShellCurrent p := by
  rw [thetaPositiveFactorPairs_prime_cube hp]
  have hpOne : 1 ≤ p := hp.one_lt.le
  have hp2One : 1 ≤ p ^ (2 : ℕ) := by
    exact one_le_pow₀ hpOne
  have hp3One : 1 ≤ p ^ (3 : ℕ) := by
    exact one_le_pow₀ hpOne
  obtain ⟨hpp, hp2p3⟩ := prime_lt_sq_and_sq_lt_cube hp
  have hleft : (0, p ^ (3 : ℕ) - 1) ∉
      ({(p - 1, p ^ (2 : ℕ) - 1), (p ^ (2 : ℕ) - 1, p - 1), (p ^ (3 : ℕ) - 1, 0)} :
        Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    omega
  have hinnerLeft : (p - 1, p ^ (2 : ℕ) - 1) ∉
      ({(p ^ (2 : ℕ) - 1, p - 1), (p ^ (3 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro heq
      have hfst : p - 1 = p ^ (2 : ℕ) - 1 := congrArg Prod.fst heq
      omega
    · intro heq
      have hfst : p - 1 = p ^ (3 : ℕ) - 1 := congrArg Prod.fst heq
      omega
  have hinnerRight : (p ^ (2 : ℕ) - 1, p - 1) ∉
      ({(p ^ (3 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    intro heq
    have hfst : p ^ (2 : ℕ) - 1 = p ^ (3 : ℕ) - 1 := congrArg Prod.fst heq
    omega
  rw [Finset.sum_insert hleft, Finset.sum_insert hinnerLeft,
    Finset.sum_insert hinnerRight, Finset.sum_singleton]
  simp only [zero_add, Nat.cast_one, one_pow,
    Nat.sub_add_cancel hpOne, Nat.sub_add_cancel hp2One,
    Nat.sub_add_cancel hp3One, Nat.cast_pow]
  unfold thetaPrimeCubeEndpointTwoHeatShellCurrent
  ring_nf
  have houter :
      Real.exp (-Real.pi) * Real.exp (-(Real.pi * (p : ℝ) ^ (6 : ℕ))) =
        Real.exp (-Real.pi - Real.pi * (p : ℝ) ^ (6 : ℕ)) := by
    rw [← Real.exp_add]
    congr 1
  have hinner :
      Real.exp (-(Real.pi * (p : ℝ) ^ (2 : ℕ))) *
          Real.exp (-(Real.pi * (p : ℝ) ^ (4 : ℕ))) =
        Real.exp (-(Real.pi * (p : ℝ) ^ (2 : ℕ)) -
          Real.pi * (p : ℝ) ^ (4 : ℕ)) := by
    rw [← Real.exp_add]
    congr 1
  calc
    _ =
        32 * Real.pi * ((p : ℝ) ^ (6 : ℕ) + 1) *
            (Real.exp (-Real.pi) *
              Real.exp (-(Real.pi * (p : ℝ) ^ (6 : ℕ)))) -
          16 * (Real.exp (-Real.pi) *
            Real.exp (-(Real.pi * (p : ℝ) ^ (6 : ℕ)))) +
        32 * Real.pi * ((p : ℝ) ^ (2 : ℕ) + (p : ℝ) ^ (4 : ℕ)) *
            (Real.exp (-(Real.pi * (p : ℝ) ^ (2 : ℕ))) *
              Real.exp (-(Real.pi * (p : ℝ) ^ (4 : ℕ)))) -
          16 * (Real.exp (-(Real.pi * (p : ℝ) ^ (2 : ℕ))) *
            Real.exp (-(Real.pi * (p : ℝ) ^ (4 : ℕ)))) := by ring
    _ =
        32 * Real.pi * ((p : ℝ) ^ (6 : ℕ) + 1) *
            Real.exp (-Real.pi - Real.pi * (p : ℝ) ^ (6 : ℕ)) -
          16 * Real.exp (-Real.pi - Real.pi * (p : ℝ) ^ (6 : ℕ)) +
        32 * Real.pi * ((p : ℝ) ^ (2 : ℕ) + (p : ℝ) ^ (4 : ℕ)) *
            Real.exp (-(Real.pi * (p : ℝ) ^ (2 : ℕ)) -
              Real.pi * (p : ℝ) ^ (4 : ℕ)) -
          16 * Real.exp (-(Real.pi * (p : ℝ) ^ (2 : ℕ)) -
            Real.pi * (p : ℝ) ^ (4 : ℕ)) := by rw [houter, hinner]
    _ = _ := by ring

/-- **Prime-cube endpoint two-heat-shell universality law.**  At every prime cube, escaping the
common tail centre converges to the explicit sum of one outer and one inner positive heat shell. -/
theorem thetaPrimeCube_endpointTwoHeatShellUniversality
    {p : ℕ} (hp : p.Prime) :
    Tendsto (fun c : ℝ =>
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent (p ^ (3 : ℕ)) c 0)
      atTop
      (nhds (thetaPrimeCubeEndpointTwoHeatShellCurrent p)) ∧
    0 < thetaPrimeCubeEndpointTwoHeatShellCurrent p := by
  simpa only [thetaPrimeCube_endpointGibbsSum_eq_twoHeatShellCurrent hp] using
    thetaProductFiber_fixedPoint_centerEscape_positiveGibbsUniversality
      (p ^ (3 : ℕ)) (pow_pos hp.pos 3)

end

end RHTower
