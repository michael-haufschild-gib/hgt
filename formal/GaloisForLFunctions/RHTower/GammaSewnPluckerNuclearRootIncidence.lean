import GaloisForLFunctions.RHTower.GammaSewnPluckerNuclearRootBudget

open Real Set Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
namespace RHTower.HedenmalmThetaSource

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

def gammaSewnCriticalPluckerRootProfile (z u : ℕ × ℕ) : ℝ :=
  Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
    gammaSewnCriticalPluckerCoordinateProfile z u

theorem gammaSewnCriticalPluckerRootProfile_nonneg (z u : ℕ × ℕ) :
    0 ≤ gammaSewnCriticalPluckerRootProfile z u :=
  mul_nonneg (Real.sqrt_nonneg _) (gammaSewnCriticalPluckerCoordinateProfile_nonneg _ _)

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

def gammaSewnCriticalPluckerRootDiagonalBudget (u : ℕ × ℕ) : ℝ :=
  ∑' z : ℕ × ℕ, gammaSewnCriticalPluckerRootProfile z u

theorem summable_gammaSewnCriticalPluckerRootProfile_left (u : ℕ × ℕ) :
    Summable (fun z : ℕ × ℕ => gammaSewnCriticalPluckerRootProfile z u) :=
  summable_gammaSewnCriticalPluckerRootProfile.prod_symm.prod_factor u

theorem summable_gammaSewnCriticalPluckerRootDiagonalBudget :
    Summable gammaSewnCriticalPluckerRootDiagonalBudget := by
  exact (summable_prod_of_nonneg
    (fun uz => gammaSewnCriticalPluckerRootProfile_nonneg uz.2 uz.1)).mp
      summable_gammaSewnCriticalPluckerRootProfile.prod_symm |>.2

theorem gammaSewnCriticalPluckerRootProfile_le_budget (z u : ℕ × ℕ) :
    gammaSewnCriticalPluckerRootProfile z u ≤ gammaSewnCriticalPluckerRootDiagonalBudget u :=
  (summable_gammaSewnCriticalPluckerRootProfile_left u).le_tsum z
    (fun k _ => gammaSewnCriticalPluckerRootProfile_nonneg k u)

theorem gammaSewnCriticalPluckerRootDiagonalBudget_nonneg (u : ℕ × ℕ) :
    0 ≤ gammaSewnCriticalPluckerRootDiagonalBudget u :=
  tsum_nonneg fun z => gammaSewnCriticalPluckerRootProfile_nonneg z u

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

theorem norm_gammaSewnCriticalPhysicalPluckerCenteredVector_apply_le_profile
    (z u : ℕ × ℕ) (s : Fin 6) :
    ‖gammaSewnCriticalPhysicalPluckerCenteredVector z s u‖ ≤
      gammaSewnCriticalPluckerCoordinateProfile z u :=
  coordinate_sum_norm_le z u _
    (gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature_abs_le_node z s)

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
