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

/-- Characteristic-power multiplication is injective in every degree over a perfect field.
Degree zero is the integer group; positive degrees admit unique characteristic-power division. -/
theorem milnorKDeg_charPower_injective_all [PerfectRing k p] (r n : ℕ) :
    Function.Injective (fun x : MilnorKDeg k n => p ^ r • x) := by
  cases n with
  | zero =>
      intro x y h
      apply (milnorDegZeroEquiv k).injective
      have hh := congrArg (milnorDegZeroEquiv k) h
      simp only [map_nsmul, nsmul_eq_mul] at hh
      have hzero : ((p ^ r : ℕ) : ℤ) *
          (milnorDegZeroEquiv k x - milnorDegZeroEquiv k y) = 0 := by
        rw [mul_sub, hh, sub_self]
      have hp : p ≠ 0 := (show p.Prime from Fact.out).ne_zero
      have hne : ((p ^ r : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero r hp)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hne)
  | succ n => exact (milnorKDeg_charPower_bijective (F := k) p r n).1

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

/-- Over a perfect residue field, Frobenius preserves the residue kernel in every degree. -/
theorem milnorResidue_iterateFrobenius_eq_zero_iff_all_degrees [PerfectRing k p]
    (D : ResidueData K k) (r n : ℕ) (x : MilnorKDeg K (n + 1)) :
    milnorResidue D (n + 1) (milnorKDegMap (iterateFrobenius K p r) (n + 1) x) = 0 ↔
      milnorResidue D (n + 1) x = 0 := by
  rw [milnorKDegMap_iterateFrobenius, map_nsmul]
  constructor
  · intro h
    apply milnorKDeg_charPower_injective_all p (r * (n + 1)) n
    simpa only [smul_zero] using h
  · rintro h
    rw [h, smul_zero]

/-- The infinity-residue kernel is preserved by Frobenius in all degrees. -/
theorem milnorResidueInfty_iterateFrobenius_eq_zero_iff_all_degrees [PerfectRing k p]
    (r n : ℕ) (x : MilnorKDeg (RatFunc k) (n + 1)) :
    milnorResidueInfty n (milnorKDegMap (iterateFrobenius (RatFunc k) p r) (n + 1) x) = 0 ↔
      milnorResidueInfty n x = 0 := by
  rw [milnorKDegMap_iterateFrobenius, map_nsmul]
  constructor
  · intro h
    apply milnorKDeg_charPower_injective_all p (r * (n + 1)) n
    simpa only [smul_zero] using h
  · rintro h
    rw [h, smul_zero]

/-- With perfect residue field, Frobenius preserves vanishing of every positive-degree residue.
The original field need not be perfect. -/
theorem milnorResidue_iterateFrobenius_eq_zero_iff [PerfectRing k p]
    (D : ResidueData K k) (r n : ℕ) (x : MilnorKDeg K (n + 2)) :
    milnorResidue D (n + 2) (milnorKDegMap (iterateFrobenius K p r) (n + 2) x) = 0 ↔
      milnorResidue D (n + 2) x = 0 :=
  milnorResidue_iterateFrobenius_eq_zero_iff_all_degrees p D r (n + 1) x

/-- Frobenius preserves the kernel of the infinity residue over a perfect constant field. -/
theorem milnorResidueInfty_iterateFrobenius_eq_zero_iff [PerfectRing k p]
    (r n : ℕ) (x : MilnorKDeg (RatFunc k) (n + 2)) :
    milnorResidueInfty (n + 1)
        (milnorKDegMap (iterateFrobenius (RatFunc k) p r) (n + 2) x) = 0 ↔
      milnorResidueInfty (n + 1) x = 0 :=
  milnorResidueInfty_iterateFrobenius_eq_zero_iff_all_degrees p r (n + 1) x

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.milnorResidue_iterateFrobenius
#print axioms GaloisForLFunctions.HTGeometry.milnorResidueInfty_iterateFrobenius_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.milnorResidue_iterateFrobenius_eq_zero_iff_all_degrees
#print axioms GaloisForLFunctions.HTGeometry.milnorResidueInfty_iterateFrobenius_eq_zero_iff_all_degrees
