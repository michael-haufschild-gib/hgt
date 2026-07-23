import GaloisForLFunctions.RHTower.PrimeWordClawFreeConflictNoGo
import GaloisForLFunctions.RHTower.PrimeWordYoungShapeNoGo

/-!
# Prime-support resolution threshold universality

Prime support has two different resolution thresholds.  Below three ports, its intersection
conflict geometry is universally claw-free.  But already at two ports, support loses the Young
multiplicity shape: two words have identical support and identical complete scalar boundary germ
while carrying different multiplicity partitions.  At three ports the first induced claw appears.

Thus support rank is an exact coarse-resolution filtration: rank two suppresses the first conflict
obstruction without recovering multiplicity, and rank three is the sharp first claw threshold.
-/

namespace GaloisForLFunctions.RHTower

/-- Every statistic factoring only through prime support identifies the `[3,1]` and `[2,2]`
witnesses, although their Young multiplicity partitions differ. -/
theorem every_primeSupportStatistic_blind_to_multiplicityPartition
    {β : Type*} (F : Finset (Fin 2) → β) :
    F (GaloisForLFunctions.primeWordSupport multiplicityWord31) =
        F (GaloisForLFunctions.primeWordSupport multiplicityWord22) ∧
      primeWordMultiplicityPartition multiplicityWord31 ≠
        primeWordMultiplicityPartition multiplicityWord22 := by
  exact ⟨congrArg F multiplicityWords_support_eq, multiplicityWords_partition_ne⟩

/-- The Young-blind witnesses lie exactly in the two-port regime. -/
theorem multiplicityWords_support_card_eq_two :
    (GaloisForLFunctions.primeWordSupport multiplicityWord31).card = 2 ∧
      (GaloisForLFunctions.primeWordSupport multiplicityWord22).card = 2 := by
  simp [multiplicityWord31, multiplicityWord22, GaloisForLFunctions.primeWordSupport]

/-- **Prime-support resolution-threshold universality law.**

1. every support-conflict neighborhood with a center of rank at most two is claw-free;
2. rank two nevertheless identifies distinct Young shapes under every support statistic and under
   the complete scalar boundary germ;
3. rank three realizes an induced claw.

Hence the first conflict obstruction and recovery of multiplicity information are independent:
passing from two to three support ports creates the claw, while no support rank can reconstruct
multiplicities discarded before support was formed. -/
theorem primeSupport_resolutionThreshold_universality :
    (∀ {α : Type*} [DecidableEq α] (c a b d : List α),
        (GaloisForLFunctions.primeWordSupport c).card ≤ 2 →
          ¬ IsSupportConflictClaw
            (GaloisForLFunctions.primeWordSupport c)
            (GaloisForLFunctions.primeWordSupport a)
            (GaloisForLFunctions.primeWordSupport b)
            (GaloisForLFunctions.primeWordSupport d)) ∧
      (∀ (β : Type*) (F : Finset (Fin 2) → β),
        F (GaloisForLFunctions.primeWordSupport multiplicityWord31) =
          F (GaloisForLFunctions.primeWordSupport multiplicityWord22)) ∧
      (GaloisForLFunctions.primeWordSupport multiplicityWord31).card = 2 ∧
      (∀ r : ℕ,
        ((derivative^[r])
          (primeWordEnsembleDeformation multiplicityEnsemble31 multiplicityUnitWeight)).eval 1 =
        ((derivative^[r])
          (primeWordEnsembleDeformation multiplicityEnsemble22 multiplicityUnitWeight)).eval 1) ∧
      primeWordMultiplicityPartition multiplicityWord31 ≠
        primeWordMultiplicityPartition multiplicityWord22 ∧
      IsSupportConflictClaw
        (GaloisForLFunctions.primeWordSupport supportClawCenter)
        (GaloisForLFunctions.primeWordSupport supportClawLeaf0)
        (GaloisForLFunctions.primeWordSupport supportClawLeaf1)
        (GaloisForLFunctions.primeWordSupport supportClawLeaf2) ∧
      (GaloisForLFunctions.primeWordSupport supportClawCenter).card = 3 := by
  refine ⟨?_, ?_, multiplicityWords_support_card_eq_two.1,
    boundaryGerm_blind_to_multiplicityPartition.1,
    multiplicityWords_partition_ne, primeWordSupportConflict_explicit_claw, ?_⟩
  · intro α _ c a b d hc
    exact primeWordSupportConflict_no_claw_of_center_card_le_two hc
  · intro β F
    exact congrArg F multiplicityWords_support_eq
  · simp [supportClawCenter, GaloisForLFunctions.primeWordSupport]

end GaloisForLFunctions.RHTower
