import GaloisForLFunctions.RHTower.GammaSewnPluckerNuclearRootBudget

/-!
# Summable root incidence profile for the Gamma-sewn critical Plücker packets

Each block `z = (depth, prime index)` of the Gamma-sewn critical adjacent-prime construction
places four nodes, with weights `node_i(z)`, at physical labels in `ℓ²(ℕ × ℕ)`. This module
defines the coordinate profile `P(z, u) = ∑_{i : label(z,i) = u} √node_i(z)` and the root profile
`√w(z) · P(z, u)`, with `w(z)` the block weight, and proves the root profile is summable jointly
over `(z, u)`. The column sums `B(u) = ∑_z √w(z) P(z, u)` form a summable diagonal budget
dominating every entry, and the `u`-th coordinates of the centered and mean Plücker vectors of
block `z` are bounded in absolute value by `P(z, u)`.

## Main results

- `summable_gammaSewnCriticalPluckerRootProfile`: `(z, u) ↦ √w(z) P(z, u)` is summable.
- `summable_gammaSewnCriticalPluckerRootDiagonalBudget`: `u ↦ B(u)` is summable.
- `gammaSewnCriticalPluckerRootProfile_le_budget`: `√w(z) P(z, u) ≤ B(u)`.
- `norm_gammaSewnCriticalPhysicalPluckerCenteredVector_apply_le_profile` and
  `norm_gammaSewnCriticalPhysicalPluckerMeanVector_apply_le_profile`: coordinatewise bounds
  `|v_z(u)| ≤ P(z, u)` for the centered and mean vectors.

## Hypotheses

Unconditional.
-/

open Real Set Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
namespace RHTower.HedenmalmThetaSource

/-- Coordinate profile `P(z, u)`: the sum of `√node_i(z)` over the nodes `i` of block `z` whose
physical label is `u`. -/
def gammaSewnCriticalPluckerCoordinateProfile (z : ℕ × ℕ)
    (u : GammaSewnCriticalPhysicalPluckerIndex) : ℝ :=
  ∑ i : Fin 4,
    if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u then
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i)
    else 0

theorem gammaSewnCriticalPluckerCoordinateProfile_nonneg (z u : ℕ × ℕ) :
    0 ≤ gammaSewnCriticalPluckerCoordinateProfile z u := by
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- Root profile `√w(z) · P(z, u)`, with `w(z)` the Plücker block weight. -/
def gammaSewnCriticalPluckerRootProfile (z u : ℕ × ℕ) : ℝ :=
  Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
    gammaSewnCriticalPluckerCoordinateProfile z u

theorem gammaSewnCriticalPluckerRootProfile_nonneg (z u : ℕ × ℕ) :
    0 ≤ gammaSewnCriticalPluckerRootProfile z u :=
  mul_nonneg (Real.sqrt_nonneg _) (gammaSewnCriticalPluckerCoordinateProfile_nonneg _ _)

/-- The root profile `(z, u) ↦ √w(z) P(z, u)` is summable over `(ℕ × ℕ) × (ℕ × ℕ)`. -/
theorem summable_gammaSewnCriticalPluckerRootProfile :
    Summable (fun zu : (ℕ × ℕ) × (ℕ × ℕ) =>
      gammaSewnCriticalPluckerRootProfile zu.1 zu.2) := by
  classical
  let f : Fin 4 → ((ℕ × ℕ) × (ℕ × ℕ)) → ℝ := fun i zu =>
    if gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel zu.1 i = zu.2 then
      Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zu.1) *
        Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node zu.1.1
          (gammaSewnCriticalAdjacentPrime_lower zu.1.2)
          (gammaSewnCriticalAdjacentPrime_upper zu.1.2) i)
    else 0
  have hf (i : Fin 4) : Summable (f i) := by
    rw [summable_prod_of_nonneg (show 0 ≤ f i by intro zu; dsimp [f]; split_ifs <;> positivity)]
    constructor
    · intro z
      simpa only [f, eq_comm] using
        (hasSum_ite_eq (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)
          (Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
            Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i))).summable
    · simpa only [f, eq_comm, tsum_ite_eq] using summable_gammaSewnCriticalPluckerRootIncidence i
  have hsum : Summable (fun zu => ∑ i : Fin 4, f i zu) := by
    simp_rw [Fin.sum_univ_four]
    exact (((hf 0).add (hf 1)).add (hf 2)).add (hf 3)
  refine hsum.congr fun zu => ?_
  simp only [gammaSewnCriticalPluckerRootProfile, gammaSewnCriticalPluckerCoordinateProfile,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [f]; split_ifs <;> simp

/-- Diagonal budget `B(u) = ∑_z √w(z) P(z, u)`, the column sum of the root profile. -/
def gammaSewnCriticalPluckerRootDiagonalBudget (u : ℕ × ℕ) : ℝ :=
  ∑' z : ℕ × ℕ, gammaSewnCriticalPluckerRootProfile z u

theorem summable_gammaSewnCriticalPluckerRootProfile_left (u : ℕ × ℕ) :
    Summable (fun z : ℕ × ℕ => gammaSewnCriticalPluckerRootProfile z u) :=
  summable_gammaSewnCriticalPluckerRootProfile.prod_symm.prod_factor u

/-- The diagonal budget `u ↦ B(u)` is summable. -/
theorem summable_gammaSewnCriticalPluckerRootDiagonalBudget :
    Summable gammaSewnCriticalPluckerRootDiagonalBudget := by
  exact (summable_prod_of_nonneg
    (fun uz => gammaSewnCriticalPluckerRootProfile_nonneg uz.2 uz.1)).mp
      summable_gammaSewnCriticalPluckerRootProfile.prod_symm |>.2

/-- Each root-profile entry is dominated by its column budget: `√w(z) P(z, u) ≤ B(u)`. -/
theorem gammaSewnCriticalPluckerRootProfile_le_budget (z u : ℕ × ℕ) :
    gammaSewnCriticalPluckerRootProfile z u ≤ gammaSewnCriticalPluckerRootDiagonalBudget u :=
  (summable_gammaSewnCriticalPluckerRootProfile_left u).le_tsum z
    (fun k _ => gammaSewnCriticalPluckerRootProfile_nonneg k u)

theorem gammaSewnCriticalPluckerRootDiagonalBudget_nonneg (u : ℕ × ℕ) :
    0 ≤ gammaSewnCriticalPluckerRootDiagonalBudget u :=
  tsum_nonneg fun z => gammaSewnCriticalPluckerRootProfile_nonneg z u

/-- Each centered node feature is bounded by the square root of its node weight. -/
theorem gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature_abs_le_node
    (z : ℕ × ℕ) (s : Fin 6) (i : Fin 4) :
    |gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i| ≤
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i) := by
  have hsquare := fourRateSelectedSum_coordinateDelta_sq i s
  have hselected : RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s ∈
      Set.Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [sq_nonneg (RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s)]
    · nlinarith [sq_nonneg (RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s - 1)]
  have hmean := gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i
  have hdiff :
      |RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s -
        gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean z i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hselected.1, hselected.2, hmean.1, hmean.2]
  unfold gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hdiff

private theorem coordinate_sum_norm_le (z u : ℕ × ℕ) (d : Fin 4 → ℝ)
    (hd : ∀ i, |d i| ≤ Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i)) :
    ‖(∑ i : Fin 4, (d i : ℂ) • gammaSewnCriticalPhysicalPluckerBasis
      (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)) u‖ ≤
        gammaSewnCriticalPluckerCoordinateProfile z u := by
  classical
  let E := lp.evalCLM ℂ (fun _ : ℕ × ℕ => ℂ) 2 u
  change ‖E (∑ i : Fin 4, (d i : ℂ) • gammaSewnCriticalPhysicalPluckerBasis
    (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i))‖ ≤ _
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i = u
  · simpa [E, lp.evalCLM, lp.evalₗ, gammaSewnCriticalPhysicalPluckerBasis, h] using hd i
  · simp [E, lp.evalCLM, lp.evalₗ, gammaSewnCriticalPhysicalPluckerBasis, h, Ne.symm h]

/-- The `u`-th coordinate of the centered Plücker vector of block `z` (any of the six selections
`s`) has absolute value at most `P(z, u)`. -/
theorem norm_gammaSewnCriticalPhysicalPluckerCenteredVector_apply_le_profile
    (z u : ℕ × ℕ) (s : Fin 6) :
    ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s u‖ ≤
      gammaSewnCriticalPluckerCoordinateProfile z u :=
  coordinate_sum_norm_le z u _
    (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature_abs_le_node z s)

/-- The `u`-th coordinate of the mean Plücker vector of block `z` has absolute value at most
`P(z, u)`. -/
theorem norm_gammaSewnCriticalPhysicalPluckerMeanVector_apply_le_profile
    (z u : ℕ × ℕ) :
    ‖gammaSewnCriticalPhysicalPluckerMeanVector z u‖ ≤
      gammaSewnCriticalPluckerCoordinateProfile z u := by
  apply coordinate_sum_norm_le z u
  intro i
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).1]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
    (gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_mem z i).2

end RHTower.HedenmalmThetaSource
