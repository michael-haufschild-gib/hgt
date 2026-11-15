import GaloisForLFunctions.HTGeometry.MilnorKTheory.PerfectFieldDivisibility
import GaloisForLFunctions.HTGeometry.MilnorResidueInfinity

/-!
# Frobenius, specialization, and residue ramification

Frobenius has weight equal to Milnor degree. Specialization preserves degree and
commutes with Frobenius. Residue lowers degree by one, so its compatibility includes
the inseparable ramification factor `p`, or `p^r` for the `r`th iterate.
These identities hold on all classes, including the concrete residue at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K k : Type*} [Field K] [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP k p]

/-- A map preserving Milnor degree intertwines Frobenius because both weights agree. -/
theorem milnorDegreeHom_iterateFrobenius (r n : ℕ)
    (f : MilnorKDeg K n →+ MilnorKDeg k n) (x : MilnorKDeg K n) :
    f (milnorKDegMap (iterateFrobenius K p r) n x) =
      milnorKDegMap (iterateFrobenius k p r) n (f x) := by
  rw [milnorKDegMap_iterateFrobenius, milnorKDegMap_iterateFrobenius, map_nsmul]

/-- Lowering degree by `e` introduces the Frobenius factor `p^(r*e)`. -/
theorem milnorDegreeDropHom_iterateFrobenius (r n e : ℕ)
    (f : MilnorKDeg K (n + e) →+ MilnorKDeg k n) (x : MilnorKDeg K (n + e)) :
    f (milnorKDegMap (iterateFrobenius K p r) (n + e) x) =
      p ^ (r * e) • milnorKDegMap (iterateFrobenius k p r) n (f x) := by
  rw [milnorKDegMap_iterateFrobenius, milnorKDegMap_iterateFrobenius, map_nsmul,
    smul_smul, Nat.mul_add, pow_add, Nat.mul_comm (p ^ (r * n))]

/-- Specialization at a discrete valuation commutes with every Frobenius iterate. -/
theorem milnorSpecialization_iterateFrobenius (D : ResidueData K k) (r n : ℕ)
    (x : MilnorKDeg K n) :
    milnorSpecialization D n (milnorKDegMap (iterateFrobenius K p r) n x) =
      milnorKDegMap (iterateFrobenius k p r) n (milnorSpecialization D n x) :=
  milnorDegreeHom_iterateFrobenius p r n (milnorSpecialization D n) x

/-- The residue of a Frobenius pullback includes its inseparable ramification index. -/
theorem milnorResidue_iterateFrobenius (D : ResidueData K k) (r n : ℕ)
    (x : MilnorKDeg K (n + 1)) :
    milnorResidue D (n + 1) (milnorKDegMap (iterateFrobenius K p r) (n + 1) x) =
      p ^ r • milnorKDegMap (iterateFrobenius k p r) n (milnorResidue D (n + 1) x) := by
  rw [milnorKDegMap_iterateFrobenius, milnorKDegMap_iterateFrobenius, map_nsmul,
    smul_smul, Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm (p ^ (r * n))]
  rfl

/-- At infinity on the rational function field, the same ramification factor is forced. -/
theorem milnorResidueInfty_iterateFrobenius (r n : ℕ)
    (x : MilnorKDeg (RatFunc k) (n + 1)) :
    milnorResidueInfty n (milnorKDegMap (iterateFrobenius (RatFunc k) p r) (n + 1) x) =
      p ^ r • milnorKDegMap (iterateFrobenius k p r) n (milnorResidueInfty n x) := by
  simpa only [Nat.mul_one] using
    milnorDegreeDropHom_iterateFrobenius p r n 1 (milnorResidueInfty n) x

/-- With perfect residue field, Frobenius preserves vanishing of every positive-degree residue.
The original field need not be perfect. -/
theorem milnorResidue_iterateFrobenius_eq_zero_iff [PerfectRing k p]
    (D : ResidueData K k) (r n : ℕ) (x : MilnorKDeg K (n + 2)) :
    milnorResidue D (n + 2) (milnorKDegMap (iterateFrobenius K p r) (n + 2) x) = 0 ↔
      milnorResidue D (n + 2) x = 0 := by
  rw [milnorKDegMap_iterateFrobenius, map_nsmul]
  exact milnorKDeg_charPower_smul_eq_zero_iff p (r * (n + 2)) n _

/-- Frobenius preserves the kernel of the infinity residue over a perfect constant field. -/
theorem milnorResidueInfty_iterateFrobenius_eq_zero_iff [PerfectRing k p]
    (r n : ℕ) (x : MilnorKDeg (RatFunc k) (n + 2)) :
    milnorResidueInfty (n + 1)
        (milnorKDegMap (iterateFrobenius (RatFunc k) p r) (n + 2) x) = 0 ↔
      milnorResidueInfty (n + 1) x = 0 := by
  rw [milnorKDegMap_iterateFrobenius, map_nsmul]
  exact milnorKDeg_charPower_smul_eq_zero_iff p (r * (n + 2)) n _

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.milnorResidue_iterateFrobenius
#print axioms GaloisForLFunctions.HTGeometry.milnorResidueInfty_iterateFrobenius_eq_zero_iff
