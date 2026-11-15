import GaloisForLFunctions.HTGeometry.MilnorKTheory.FrobeniusWeights
import GaloisForLFunctions.HTGeometry.MilnorKDegRingEquiv
import Mathlib.FieldTheory.Perfect

/-!
# Unique characteristic-primary division over perfect fields

Frobenius is invertible on a perfect field, hence on its Milnor groups. Its explicit
weight `p^n` therefore makes multiplication by `p` invertible in every positive degree.
Inverse Frobenius supplies division by `p^n`; composing with multiplication by
`p^(n-1)` supplies division by `p`. The same argument gives unique division by `p^r`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

/-- Frobenius identifies its scalar weight with an additive automorphism. -/
theorem milnorKDeg_frobeniusWeight_bijective (r n : ℕ) :
    Function.Bijective (fun x : MilnorKDeg F n => p ^ (r * n) • x) := by
  let e := milnorKDegAddEquivOfRingEquiv (iterateFrobeniusEquiv F p r) n
  have he (x : MilnorKDeg F n) : e x = p ^ (r * n) • x :=
    milnorKDegMap_iterateFrobenius p r n x
  constructor
  · intro x y h
    apply e.injective
    exact (he x).trans (h.trans (he y).symm)
  · intro x
    obtain ⟨y, hy⟩ := e.surjective x
    exact ⟨y, (he y).symm.trans hy⟩

/-- In every positive degree, multiplication by any power of the characteristic is bijective. -/
theorem milnorKDeg_charPower_bijective (r n : ℕ) :
    Function.Bijective (fun x : MilnorKDeg F (n + 1) => p ^ r • x) := by
  have h := milnorKDeg_frobeniusWeight_bijective (F := F) p r (n + 1)
  constructor
  · intro x y hxy
    apply h.1
    have heq := congrArg (fun z : MilnorKDeg F (n + 1) => p ^ (r * n) • z) hxy
    simpa only [smul_smul, Nat.mul_add, Nat.mul_one, pow_add] using heq
  · intro x
    obtain ⟨y, hy⟩ := h.2 x
    refine ⟨p ^ (r * n) • y, ?_⟩
    calc
      p ^ r • (p ^ (r * n) • y) = p ^ (r * (n + 1)) • y := by
        rw [smul_smul, Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm (p ^ r)]
      _ = x := hy

/-- Positive Milnor groups over perfect fields have no characteristic-primary torsion. -/
theorem milnorKDeg_charPower_smul_eq_zero_iff (r n : ℕ) (x : MilnorKDeg F (n + 1)) :
    p ^ r • x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply (milnorKDeg_charPower_bijective (F := F) p r n).1
    simpa only [smul_zero] using hx
  · rintro rfl
    exact smul_zero _

/-- Each positive-degree Milnor class admits a unique characteristic-power division. -/
theorem milnorKDeg_existsUnique_charPower_division (r n : ℕ) (x : MilnorKDeg F (n + 1)) :
    ∃! y : MilnorKDeg F (n + 1), p ^ r • y = x := by
  obtain ⟨y, hy⟩ := (milnorKDeg_charPower_bijective (F := F) p r n).2 x
  exact ⟨y, hy, fun z hz => (milnorKDeg_charPower_bijective (F := F) p r n).1 (hz.trans hy.symm)⟩

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.milnorKDeg_existsUnique_charPower_division
