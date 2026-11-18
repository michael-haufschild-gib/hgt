import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianSinglePointPoleOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPointClassOrders
import Mathlib.Data.ZMod.Basic

/-!
# Recovering geometric Frobenius orbits from divisor classes

The simple-pole gap at every point makes the Abel–Jacobi point map injective.
Consequently a point class knows the point's field of definition: its degree
is the multiplicative order of -Q modulo the class order. In particular,
the minimum possible class order Q+1 singles out precisely the rational points.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Function IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "Div" => HermitianGeometricPlaceDivisor p s
local notation "J" => hermitianAffineClass p s
local notation "F" => hermitianFrobeniusPoint p s E
local notation "V" => hermitianGeometricPointValuation p s
local notation "W" => hermitianGeometricInfinityValuation p s
local notation "Δ" => hermitianGeometricPointDifference p s
local notation "cl" => hermitianGeometricClass p s
local notation "w" => hermitianGeometricPointPrime p s

/-- Distinct geometric affine points represent distinct degree-zero divisor classes. -/
theorem hermitianAffineClass_injective : Injective J := by
  intro P R h
  by_contra hne
  change cl (Δ (some P)) = cl (Δ (some R)) at h
  have hz : cl (Δ (some P) - Δ (some R)) = 0 := by rw [map_sub,h,sub_self]
  obtain ⟨v,hv⟩ := (QuotientAddGroup.eq_zero_iff _).1 hz
  let f : H := (v.toMul:Hˣ)
  have hf : f ≠ 0 := v.toMul.ne_zero
  have hlogs (U : Pts) : -WithZero.log (V U f) =
      (if U=P then (1:ℤ) else 0) - (if U=R then 1 else 0) := by
    have hs (X : Pts) : (Finsupp.single (w X) (1:ℤ)) (w U) = if U=X then 1 else 0 := by
      by_cases he : U=X
      · rw [he,if_pos rfl,Finsupp.single_eq_same]
      · have hw : w U ≠ w X := (hermitianGeometricFinitePointEquiv p s).symm.injective.ne he
        rw [if_neg he,Finsupp.single_eq_of_ne hw]
    have hc := congrArg (fun D : Div => D.1 (w U)) hv
    change -WithZero.log ((w U).valuation H f) = Finsupp.single (w P) (1:ℤ) (w U) -
      Finsupp.single (w R) (1:ℤ) (w U) at hc
    rwa [hermitianGeometricPointPrime_valuation,hs,hs] at hc
  have hi := congrArg Prod.snd hv
  change -WithZero.log (W f) = (-1:ℤ)-(-1) at hi
  have hex (U : Pts) : V U f = WithZero.exp (WithZero.log (V U f)) :=
    (WithZero.exp_log ((map_ne_zero _).2 hf)).symm
  have hbound : hermitianSinglePoleBound p s R 1 f := by
    refine ⟨?_,?_,?_⟩
    · rw [← WithZero.exp_log ((map_ne_zero W).2 hf),← WithZero.exp_zero,WithZero.exp_le_exp]
      omega
    · rw [hex,WithZero.exp_le_exp]
      have he := hlogs R
      rw [if_neg (Ne.symm hne),if_pos rfl] at he
      omega
    · intro U hU
      rw [hex,← WithZero.exp_zero,WithZero.exp_le_exp]
      have he := hlogs U
      rw [if_neg hU] at he
      split_ifs at he <;> omega
  have hQ : 1<Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  obtain ⟨a,ha⟩ := hermitianSinglePole_constant_of_lt p s R 1 hQ f hbound
  have ha₀ : a ≠ 0 := fun he => hf (ha.trans (he ▸ map_zero _))
  have he := hlogs P
  rw [ha,hermitianGeometricPointValuation_constant p s P a ha₀,WithZero.log_one,
    if_pos rfl,if_neg hne] at he
  omega

/-- A Frobenius return is equivalent to a congruence modulo the actual order of the point class. -/
theorem hermitianAffineClass_return_iff (P : Pts) (n : ℕ) :
    F^[n] P = P ↔ (addOrderOf (J P):ℤ) ∣ (-((Q:ℕ):ℤ))^n - 1 := by
  rw [← (hermitianAffineClass_injective p s).eq_iff,hermitianAffineClass_iterate,
    addOrderOf_dvd_iff_zsmul_eq_zero,sub_zsmul,one_zsmul,← sub_eq_add_neg,sub_eq_zero]

private theorem modular_order_test (d q n : ℕ) :
    (d:ℤ) ∣ (-(q:ℤ))^n-1 ↔ orderOf (-(q:ZMod d)) ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one,← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,
    Int.cast_pow,Int.cast_neg,Int.cast_natCast,Int.cast_one,sub_eq_zero]

/-- The exact orbit length is the multiplicative order of -Q modulo the Abel–Jacobi order. -/
theorem hermitianOrbitDegree_eq_modular_order (P : Pts) :
    hermitianOrbitDegree p s P = orderOf (-((Q:ℕ):ZMod (addOrderOf (J P)))) := by
  have hd (n : ℕ) : hermitianOrbitDegree p s P ∣ n ↔
      orderOf (-((Q:ℕ):ZMod (addOrderOf (J P)))) ∣ n :=
    (hermitianFrobenius_return_iff p s P n).symm.trans
      ((hermitianAffineClass_return_iff p s P n).trans (modular_order_test _ Q n))
  exact Nat.dvd_antisymm ((hd _).2 dvd_rfl) ((hd _).1 dvd_rfl)

/-- Minimum-order Abel–Jacobi classes of affine points occur exactly over the square constant field. -/
theorem hermitianAffineClass_minimal_order_iff (P : Pts) :
    addOrderOf (J P) = Q+1 ↔ F P=P := by
  refine ⟨fun h => ?_,hermitianAffineClass_order_of_fixed p s P⟩
  apply (hermitianAffineClass_injective p s)
  rw [hermitianAffineClass_frobenius]
  have hz := addOrderOf_nsmul_eq_zero (J P)
  rw [h,succ_nsmul] at hz
  exact (neg_eq_iff_add_eq_zero).2 hz

/-- The class-group orbit distinguishes precisely the same pairs of times as geometric Frobenius. -/
theorem hermitianAffineClass_iterate_collision (P : Pts) (i j : ℕ) :
    (-((Q:ℕ):ℤ))^i • J P = (-((Q:ℕ):ℤ))^j • J P ↔
      i ≡ j [MOD hermitianOrbitDegree p s P] := by
  rw [← hermitianAffineClass_iterate,← hermitianAffineClass_iterate,
    (hermitianAffineClass_injective p s).eq_iff,hermitianFrobenius_iterate_eq_iff]

#print axioms hermitianAffineClass_injective
#print axioms hermitianAffineClass_return_iff
#print axioms hermitianOrbitDegree_eq_modular_order
#print axioms hermitianAffineClass_minimal_order_iff
#print axioms hermitianAffineClass_iterate_collision

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
