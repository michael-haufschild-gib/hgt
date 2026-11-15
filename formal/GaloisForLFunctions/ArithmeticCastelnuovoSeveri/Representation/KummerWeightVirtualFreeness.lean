import GaloisForLFunctions.RepresentationLifting.KTheory.UniformCharacterMultiplicity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularMonomialBasis
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Virtual freeness of the complex Kummer weight lift

The integral weights of the actual regular-differential basis define a
complex character of the full cyclic covering degree. No weight is trivial,
so the regular-character criterion forces every virtually free lift to vanish.
The exact cutoff sum identifies this boundary with divisibility of the branch
exponent by the radical degree. This concerns the complex lift of the proved
weight multiset; no comparison with étale cohomology is assumed.
-/

open scoped BigOperators Classical
noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.KummerWeightFreeness
open RepresentationLifting ArithmeticHarmonicAnalysis

/-- The complex character of a cyclic group with residue weight `w`. -/
def cyclicWeightCharacter (N : ℕ) [NeZero N] (w : ZMod N) :
    LinearCharacter (Multiplicative (ZMod N)) where
  toFun g := Circle.toUnits (ZMod.toCircle (w * g.toAdd))
  map_one' := by simp
  map_mul' g h := by simp [mul_add, AddChar.map_add_eq_mul]

theorem cyclicWeightCharacter_apply (N : ℕ) [NeZero N] (w : ZMod N)
    (g : Multiplicative (ZMod N)) :
    (cyclicWeightCharacter N w g : ℂ) = ZMod.stdAddChar (w * g.toAdd) := rfl

/-- Evaluation at the cyclic generator distinguishes residue weights. -/
theorem cyclicWeightCharacter_injective (N : ℕ) [NeZero N] :
    Function.Injective (cyclicWeightCharacter N) := by
  intro a b h
  have he := congrArg (fun χ : LinearCharacter (Multiplicative (ZMod N)) =>
    (χ (Multiplicative.ofAdd (1 : ZMod N)) : ℂ)) h
  simp only [cyclicWeightCharacter_apply, Multiplicative.toAdd_ofAdd, mul_one] at he
  exact ZMod.injective_stdAddChar he

theorem cyclicWeightCharacter_zero (N : ℕ) [NeZero N] : cyclicWeightCharacter N 0 = 1 := by
  ext g
  simp [cyclicWeightCharacter]

variable (p : ℕ) [Fact p.Prime] (s d r : ℕ)

/-- The full cyclic order attached to the regular Kummer weights. -/
abbrev weightOrder : ℕ := (p ^ (s + 1) + 1) * (p ^ (d + 1) - 1)

instance weightOrder_neZero : NeZero (weightOrder p s d) := by
  have hq : 1 < p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  exact ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt hq))⟩

/-- The full cyclic group, written multiplicatively for the character ring. -/
abbrev WeightGroup := Multiplicative (ZMod (weightOrder p s d))

/-- Complex character with the weight of a regular Kummer basis vector. -/
def regularWeightCharacter (a : SquareKummerRegularIndex p s d r) :
    LinearCharacter (WeightGroup p s d) :=
  cyclicWeightCharacter (weightOrder p s d) (squareKummerRegularWeight p s d r a)

/-- Positive weights below the cyclic order exclude the trivial character. -/
theorem regularWeightCharacter_ne_one (a : SquareKummerRegularIndex p s d r) :
    regularWeightCharacter p s d r a ≠ 1 := by
  intro h
  have hz : (squareKummerRegularWeight p s d r a : ZMod (weightOrder p s d)) = 0 :=
    cyclicWeightCharacter_injective _ (h.trans (cyclicWeightCharacter_zero _).symm)
  have hv := congrArg ZMod.val hz
  have hb := squareKummerRegularWeight_bounds p s d r a
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hb.2, ZMod.val_zero] at hv
  exact hb.1.ne' hv

/-- Distinct regular basis vectors have distinct complex cyclic characters. -/
theorem regularWeightCharacter_injective : Function.Injective (regularWeightCharacter p s d r) := by
  intro a b h
  have hz := cyclicWeightCharacter_injective (weightOrder p s d) h
  have hv := congrArg ZMod.val hz
  simp only [ZMod.val_natCast,
    Nat.mod_eq_of_lt (squareKummerRegularWeight_bounds p s d r a).2,
    Nat.mod_eq_of_lt (squareKummerRegularWeight_bounds p s d r b).2] at hv
  exact squareKummerRegularWeight_injective p s d r hv

/-- The complex character lift of the intrinsic regular-differential weights. -/
def complexLift : VirtualRepresentationRing (WeightGroup p s d) :=
  ∑ a : SquareKummerRegularIndex p s d r,
    linearCharacterVirtualHom (WeightGroup p s d) (regularWeightCharacter p s d r a)

/-- Every supported character occurs exactly once; every other multiplicity is zero. -/
theorem complexLift_multiplicity (χ : LinearCharacter (WeightGroup p s d)) :
    linearMultiplicity (WeightGroup p s d) χ (complexLift p s d r) =
      if ∃ a : SquareKummerRegularIndex p s d r, regularWeightCharacter p s d r a = χ
      then 1 else 0 := by
  rw [complexLift, linearMultiplicity_sum]
  simp_rw [linearMultiplicity_linear]
  by_cases h : ∃ a : SquareKummerRegularIndex p s d r, regularWeightCharacter p s d r a = χ
  · obtain ⟨a, rfl⟩ := h
    simp only [(regularWeightCharacter_injective p s d r).eq_iff,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, exists_eq, ↓reduceIte]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun ha => h ⟨a, ha.symm⟩)

/-- The lift has no trivial-character component. -/
theorem complexLift_trivialMultiplicity :
    linearMultiplicity (WeightGroup p s d) 1 (complexLift p s d r) = 0 := by
  rw [complexLift, linearMultiplicity_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [linearMultiplicity_linear, if_neg (regularWeightCharacter_ne_one p s d r a).symm]

/-- The identity trace counts the actual regular-differential basis vectors. -/
theorem complexLift_at_one :
    (complexLift p s d r).val 1 = (Fintype.card (SquareKummerRegularIndex p s d r) : ℂ) := by
  simp [complexLift, linearCharacterVirtualHom]

/-- The lift vanishes exactly when there are no regular basis vectors. -/
theorem complexLift_eq_zero_iff :
    complexLift p s d r = 0 ↔ IsEmpty (SquareKummerRegularIndex p s d r) := by
  constructor
  · intro h
    have hc := congrArg (fun χ : VirtualRepresentationRing (WeightGroup p s d) => χ.val 1) h
    rw [complexLift_at_one] at hc
    exact Fintype.card_eq_zero_iff.mp (Nat.cast_eq_zero.mp hc)
  · intro h
    letI := h
    simp [complexLift]

/-- The regular-character criterion is rigid on the Kummer weight lift. -/
theorem complexLift_isVirtuallyFree_iff_empty :
    IsVirtuallyFree (WeightGroup p s d) (complexLift p s d r) ↔
      IsEmpty (SquareKummerRegularIndex p s d r) := by
  rw [← complexLift_eq_zero_iff]
  constructor
  · intro h
    exact (isVirtuallyFree_and_trivialMultiplicity_zero_iff _ _).mp
      ⟨h, complexLift_trivialMultiplicity p s d r⟩
  · intro h
    exact (isVirtuallyFree_and_trivialMultiplicity_zero_iff _ _).mpr h |>.1

/-- The number of regular basis vectors has the exact ramification-defect formula. -/
theorem regularIndex_card_twice :
    2 * Fintype.card (SquareKummerRegularIndex p s d r) =
      (p ^ (d + 1) - 1) *
        (p ^ (s + 1) + 1 - Nat.gcd (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r)) := by
  simpa only [SquareKummerRegularIndex, Fintype.card_sigma, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range] using kummerDifferentialCutoff_sum_twice p s d r

/-- Vanishing of all regular differentials is exactly a branch-exponent divisibility law. -/
theorem regularIndex_empty_iff_dvd :
    IsEmpty (SquareKummerRegularIndex p s d r) ↔
      p ^ (s + 1) + 1 ∣ kummerExponent (p ^ (d + 1)) r := by
  rw [← Fintype.card_eq_zero_iff]
  have hc := regularIndex_card_twice p s d r
  have hq : 0 < p ^ (d + 1) - 1 := Nat.sub_pos_of_lt
    (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt)
  have hg := Nat.gcd_le_left (kummerExponent (p ^ (d + 1)) r)
    (Nat.succ_pos (p ^ (s + 1)))
  constructor
  · intro h
    rw [h, mul_zero] at hc
    have hz := (Nat.mul_eq_zero.mp hc.symm).resolve_left hq.ne'
    have he : Nat.gcd (p ^ (s + 1) + 1) (kummerExponent (p ^ (d + 1)) r) =
        p ^ (s + 1) + 1 := by omega
    rw [← he]
    exact Nat.gcd_dvd_right _ _
  · intro h
    rw [Nat.gcd_eq_left h, Nat.sub_self, mul_zero] at hc
    omega

/-- Exact virtual-freeness boundary for every prime-power Kummer weight family. -/
theorem complexLift_isVirtuallyFree_iff_dvd :
    IsVirtuallyFree (WeightGroup p s d) (complexLift p s d r) ↔
      p ^ (s + 1) + 1 ∣ kummerExponent (p ^ (d + 1)) r := by
  rw [complexLift_isVirtuallyFree_iff_empty, regularIndex_empty_iff_dvd]

/-- A nonidentity trace detects exactly the nonzero regular-differential families. -/
theorem exists_nonidentity_trace_iff_not_dvd :
    (∃ g : WeightGroup p s d, g ≠ 1 ∧ (complexLift p s d r).val g ≠ 0) ↔
      ¬ p ^ (s + 1) + 1 ∣ kummerExponent (p ^ (d + 1)) r := by
  rw [← not_isVirtuallyFree_iff, complexLift_isVirtuallyFree_iff_dvd]

/-- The complex lift and the actual regular-differential space have the same dimension. -/
theorem complexLift_dimension (c : (SquareConstantField p s)ˣ) :
    (complexLift p s d r).val 1 =
      (Module.finrank (SquareConstantField p s)
        (globalRegularDifferentials (SquareConstantField p s)
          (SquareKummerField p s c (p ^ (d + 1) - 2)
            (kummerExponent (p ^ (d + 1)) r))) : ℂ) := by
  rw [complexLift_at_one, Module.finrank_eq_card_basis (squareKummerRegularMonomialBasis p s c d r)]

/-- Virtual freeness of the lift is equivalent to zero dimension of the intrinsic differential space. -/
theorem complexLift_isVirtuallyFree_iff_finrank_zero (c : (SquareConstantField p s)ˣ) :
    IsVirtuallyFree (WeightGroup p s d) (complexLift p s d r) ↔
      Module.finrank (SquareConstantField p s)
        (globalRegularDifferentials (SquareConstantField p s)
          (SquareKummerField p s c (p ^ (d + 1) - 2)
            (kummerExponent (p ^ (d + 1)) r))) = 0 := by
  rw [complexLift_isVirtuallyFree_iff_empty,
    Module.finrank_eq_card_basis (squareKummerRegularMonomialBasis p s c d r),
    Fintype.card_eq_zero_iff]

#print axioms complexLift_trivialMultiplicity
#print axioms complexLift_multiplicity
#print axioms complexLift_isVirtuallyFree_iff_dvd
#print axioms exists_nonidentity_trace_iff_not_dvd
#print axioms complexLift_dimension
#print axioms complexLift_isVirtuallyFree_iff_finrank_zero

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.KummerWeightFreeness
