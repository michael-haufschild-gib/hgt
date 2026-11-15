import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierNilpotence
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.DiagonalCommutingNilpotence

/-!
# The constant-field period annihilates regular Cartier forms

After the prime-field degree of the constant field, Cartier is linear
over all constants. Naturality makes that iterate commute with full
cyclic scaling. The regular differential characters are distinct, so
the iterate is diagonal. Its nilpotence forces every diagonal entry
to vanish. The resulting bound is independent of the branch exponent.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis

/-- A full constant-field period of Cartier is linear over all constants. -/
def squareKummerRegularCartierPeriod (p : ℕ) [Fact p.Prime] (s : ℕ)
    (c : (SquareConstantField p s)ˣ) (d r : ℕ) :
    globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) →ₗ[SquareConstantField p s]
    globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) where
  toFun := squareKummerRegularCartierIterate p s c d r (2 * (s + 1))
  map_add' := (squareKummerRegularCartierIterate p s c d r (2 * (s + 1))).map_add
  map_smul' a ω := by
    have ha : a ^ (p ^ (2 * (s + 1))) = a := by
      letI := Fintype.ofFinite (SquareConstantField p s)
      have h := FiniteField.pow_card a
      rwa [← Nat.card_eq_fintype_card, squareConstantField_card] at h
    have h := squareKummerRegularCartierIterate_frobenius_smul p s c d r
      (2 * (s + 1)) a ω
    rwa [ha] at h

variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
local notation "G" => globalRegularDifferentials K L
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "F" => 2 * (s + 1)
local notation "k" => ((d + 1) * r) * M

/-- The constant-field-period Cartier operator vanishes on every actual regular differential. -/
theorem primePowerKummerRegularCartierPeriod_eq_zero :
    squareKummerRegularCartierPeriod p s c d r = 0 := by
  classical
  let B := squareKummerRegularMonomialBasis p s c d r
  let weight := squareKummerRegularWeight p s d r
  let T := squareKummerRegularCartierPeriod p s c d r
  have hM : 0 < M := primePowerKummerCyclicDegree_pos p d n
  obtain ⟨ζ, hζ'⟩ := squareConstantField_threePoint_primitiveRoots p d n
  have hζ : IsPrimitiveRoot ζ M := (mem_primitiveRoots hM).mp hζ'
  let S := squareKummerRegularScaling p s c d r ζ hζ.pow_eq_one
  have hweight (i : SquareKummerRegularIndex p s d r) : weight i < M :=
    (squareKummerRegularWeight_bounds p s d r i).2
  have hinjective : Function.Injective (fun i => ζ ^ weight i) := by
    intro i j hij
    exact squareKummerRegularWeight_injective p s d r
      (hζ.pow_inj (hweight i) (hweight j) hij)
  refine diagonal_commuting_nilpotent_eq_zero B S.toLinearMap T (fun i => ζ ^ weight i) hinjective
    (squareKummerRegularScaling_basis p s c d r ζ hζ.pow_eq_one) ?_ k ?_
  · intro ω
    exact squareKummerRegularCartierIterate_aut p s c d r F
      (squareKummerCyclicScalingAut p s c d r ζ hζ.pow_eq_one) ω
  · intro ω
    apply Subtype.ext
    change (((squareKummerRegularCartierIterate p s c d r F : G → G)^[k]) ω).val = 0
    rw [squareKummerRegularCartierIterate_iterate]
    have he : F * k = k * (F - 1) + k := by
      rw [← Nat.mul_succ, Nat.sub_add_cancel (show 1 ≤ F by omega), Nat.mul_comm]
    rw [he, squareKummerCartierIterate_add,
      primePowerKummerCartier_iterate_eq_zero p d n r c ω, map_zero]

/-- Cartier is killed after the prime-field degree of the stated square constant field. -/
theorem primePowerKummerRegularCartier_constant_period (ω : G) :
    (squareKummerRegularCartier p s c d r : G → G)^[F] ω = 0 := by
  apply Subtype.ext
  have h := squareKummerRegularCartierIterate_iterate p s c d r 1 F ω
  rw [one_mul] at h
  rw [h]
  have hz := LinearMap.congr_fun (primePowerKummerRegularCartierPeriod_eq_zero p d n r c) ω
  exact congrArg Subtype.val hz

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
