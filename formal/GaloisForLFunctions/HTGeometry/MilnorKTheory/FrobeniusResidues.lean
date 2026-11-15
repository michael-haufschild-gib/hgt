import GaloisForLFunctions.HTGeometry.MilnorKTheory.FrobeniusWeights
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
  simpa only [Nat.mul_one] using
    milnorDegreeDropHom_iterateFrobenius p r n 1 (milnorResidue D (n + 1)) x

/-- At infinity on the rational function field, the same ramification factor is forced. -/
theorem milnorResidueInfty_iterateFrobenius (r n : ℕ)
    (x : MilnorKDeg (RatFunc k) (n + 1)) :
    milnorResidueInfty n (milnorKDegMap (iterateFrobenius (RatFunc k) p r) (n + 1) x) =
      p ^ r • milnorKDegMap (iterateFrobenius k p r) n (milnorResidueInfty n x) := by
  simpa only [Nat.mul_one] using
    milnorDegreeDropHom_iterateFrobenius p r n 1 (milnorResidueInfty n) x

end GaloisForLFunctions.HTGeometry
