import GaloisForLFunctions.HTGeometry.NonabelianHiggsMechanism

/-!
# Finite multi-Higgs symmetry breaking

The existing one-point `S₃` vacuum retains a maximal `S₂` subgroup.  Selecting
two distinct ordered points removes that residual swap: every permutation fixing
both points is the identity.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

def finiteTwoPointHiggsVacuum : Fin 3 × Fin 3 := (0, 1)

def finiteTwoPointHiggsMechanism :
    HiggsMechanism (Equiv.Perm (Fin 3)) (Fin 3 × Fin 3) :=
  HiggsMechanism.canonicalOrbitWell finiteTwoPointHiggsVacuum

theorem permFinThree_eq_one_of_fix_zero_one (g : Equiv.Perm (Fin 3))
    (h0 : g 0 = 0) (h1 : g 1 = 1) : g = 1 := by
  apply Equiv.ext
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · have h2 : g 2 = 2 := by
      generalize hy : g 2 = y
      fin_cases y
      · have hbad : (2 : Fin 3) = 0 := g.injective (hy.trans h0.symm)
        omega
      · have hbad : (2 : Fin 3) = 1 := g.injective (hy.trans h1.symm)
        omega
      · rfl
    change g 2 = 2
    exact h2

theorem finiteTwoPointHiggs_unbroken_eq_bot :
    finiteTwoPointHiggsMechanism.unbroken = ⊥ := by
  ext g
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  constructor
  · intro hfix
    change g • finiteTwoPointHiggsVacuum = finiteTwoPointHiggsVacuum at hfix
    have h0 := congrArg Prod.fst hfix
    have h1 := congrArg Prod.snd hfix
    change g 0 = 0 at h0
    change g 1 = 1 at h1
    have hg : g = 1 := permFinThree_eq_one_of_fix_zero_one g h0 h1
    simp [hg]
  · intro hg
    have hg1 : g = 1 := by simpa using hg
    rw [hg1]
    exact one_smul _ _

theorem finiteTwoPointHiggs_fullyBroken : finiteTwoPointHiggsMechanism.IsFullyBroken :=
  finiteTwoPointHiggs_unbroken_eq_bot

end GaloisForLFunctions.HTGeometry
