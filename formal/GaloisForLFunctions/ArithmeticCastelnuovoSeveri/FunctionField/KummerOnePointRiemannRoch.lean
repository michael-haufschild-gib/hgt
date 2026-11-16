import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.WeightedResiduePoleCounts
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleSpaceDimension
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityConductor

/-!
# One-point Riemann–Roch for Kummer normalizations

The integral radical coordinates count bounded pole orders without
multiplicity. The missing orders number exactly the differential genus
and all lie below twice that genus. Counting the resulting partition of
an initial interval proves the one-point Riemann–Roch formula directly.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "N" => p ^ (s + 1) + 1
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "L" => SquareKummerField p s c (q - 2) R
local notation "g" => Module.finrank K (globalRegularDifferentials K L)

/-- Beyond the final possible gap, the actual one-point pole space has dimension `m+1-g`. -/
theorem squareKummer_poleSpace_riemannRoch (m : ℕ) (hm : 2 * g ≤ m + 1) :
    Module.finrank K (squareKummerPoleSpace p s c d r m) + g = m + 1 := by
  let D : Fin N → ℕ := fun i => i.val + (q - 1) * (i.val * R % N)
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcop := (kummerInfinity_primePower_poleDegree_coprime p s d r).symm
  rw [show q - 2 + 1 = q - 1 by omega] at hcop
  have hresidue (i j : Fin N) (h : D i % N = D j % N) : i = j := by
    dsimp only [D] at h
    rw [reducedResidue_mod, reducedResidue_mod] at h
    have hij : Nat.ModEq N i.val j.val := Nat.ModEq.cancel_left_of_coprime hcop.symm h
    exact Fin.ext (hij.eq_of_lt_of_lt i.isLt j.isLt)
  let E : WeightedResidueGaps D ≃ SquareKummerInfinityGaps p s c d r :=
    { toFun := fun a => ⟨a.val, fun h => a.property
        ((squareKummer_exists_integral_pole_iff p s c d r a.val).mp h)⟩
      invFun := fun a => ⟨a.val, fun h => a.property
        ((squareKummer_exists_integral_pole_iff p s c d r a.val).mpr h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hgap (a : WeightedResidueGaps D) : a.val ≤ m := by
    have h := squareKummerInfinityGap_lt_twice_genus p s c d r (E a)
    change a.val < 2 * g at h
    omega
  have h := poleDegreeCutoff_sum_add_gaps (Nat.succ_pos _) D hresidue m hgap
  rw [Nat.card_congr E, squareKummerInfinityGaps_card_eq_genus] at h
  rw [squareKummer_poleSpace_finrank]
  exact h

/-- The pole-space Hilbert function is linear on the entire tail starting at twice the actual genus. -/
theorem squareKummer_poleSpace_twice_genus_add_finrank (m : ℕ) :
    Module.finrank K (squareKummerPoleSpace p s c d r (2 * g + m)) = g + m + 1 := by
  have h := squareKummer_poleSpace_riemannRoch p s c d r (2 * g + m) (by omega)
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
