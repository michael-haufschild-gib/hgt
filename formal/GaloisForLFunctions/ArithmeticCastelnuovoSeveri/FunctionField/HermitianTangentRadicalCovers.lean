import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.BinomialIrreducibility
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPrimitivePoleWindows
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Separable and purely inseparable tangent radical covers

Every geometric tangent gives irreducible radical covers of all positive
degrees. In degree m·pʳ, with p not dividing m, the separable degree is m
and the inseparable degree is pʳ. At pure p-power degree the defining map
therefore has one geometric branch and its full degree can be arbitrarily large.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IntermediateField
open scoped IntermediateField
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "L" => AlgebraicClosure H
local notation "Pts" => HermitianAffinePoint p s E
local notation "T" => hermitianGeometricTangentFunction p s
local notation "B" => fun (P : Pts) (n : ℕ) => (X^n - C (T P) : H[X])

/-- The tangent binomial is irreducible for every degree, including multiples of the characteristic. -/
theorem hermitianTangentBinomial_irreducible (P : Pts) (n : ℕ) (hn : 0<n) :
    Irreducible (B P n) := by
  obtain ⟨i,hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1:E) (n := 2) zero_lt_two
  have hsign : (algebraMap E H i)^2 = -1 := by rw [← map_pow,hi,map_neg,map_one]
  exact (binomial_irreducible_iff_over_sqrt_neg_one ⟨_,hsign⟩ (T P) hn.ne').2
    fun d hd _ => hermitianGeometricTangent_powerFree p s P d hd.two_le

/-- Separability of the tangent binomial detects exactly the prime-to-characteristic degrees. -/
theorem hermitianTangentBinomial_separable_iff (P : Pts) (n : ℕ) (hn : 0<n) :
    (B P n).Separable ↔ ¬ p ∣ n := by
  refine ⟨fun hs hd => ?_, fun hd => separable_X_pow_sub_C' p n (T P) hd
    (hermitianGeometricTangentFunction_ne_zero p s P)⟩
  have hf := (separable_iff_derivative_ne_zero (hermitianTangentBinomial_irreducible p s P n hn)).1 hs
  apply hf
  change derivative (X^n - C (T P)) = 0
  simp only [derivative_sub,derivative_C,sub_zero,derivative_X_pow,
    (CharP.cast_eq_zero_iff H p n).2 hd,zero_mul,Polynomial.C_0]

/-- A chosen root in the actual algebraic closure of the geometric function field. -/
def hermitianTangentRoot (P : Pts) (n : ℕ) (hn : 0<n) : L :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap H L (T P)) hn).choose

local notation "r" => hermitianTangentRoot p s

theorem hermitianTangentRoot_pow (P : Pts) (n : ℕ) (hn : 0<n) :
    (r P n hn)^n = algebraMap H L (T P) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap H L (T P)) hn).choose_spec

/-- The minimum polynomial over the function field recovers the complete defining binomial. -/
theorem hermitianTangentRoot_minpoly (P : Pts) (n : ℕ) (hn : 0<n) :
    minpoly H (r P n hn) = B P n := by
  refine (minpoly.eq_of_irreducible_of_monic (hermitianTangentBinomial_irreducible p s P n hn)
    ?_ (monic_X_pow_sub_C (T P) hn.ne')).symm
  rw [map_sub,map_pow,aeval_X,aeval_C,hermitianTangentRoot_pow,sub_self]

/-- The intermediate function field of a tangent radical cover. -/
abbrev HermitianTangentCover (P : Pts) (n : ℕ) (hn : 0<n) := H⟮r P n hn⟯
local notation "K" => HermitianTangentCover p s

/-- Degree at every positive level of every geometric tangent cover. -/
theorem hermitianTangentCover_finrank (P : Pts) (n : ℕ) (hn : 0<n) :
    Module.finrank H (K P n hn) = n := by
  have ha : IsIntegral H (r P n hn) := Algebra.IsIntegral.isIntegral _
  rw [HermitianTangentCover, adjoin.finrank ha, hermitianTangentRoot_minpoly, natDegree_X_pow_sub_C]

/-- The mixed Frobenius cover has separable degree m and inseparable degree pʳ. -/
theorem hermitianTangentCover_degrees (P : Pts) (m t : ℕ) (hm : ¬ p ∣ m) :
    let n := m*p^t
    let hn : 0<n := Nat.mul_pos (Nat.pos_of_ne_zero (fun h => hm (by rw [h]; exact dvd_zero _)))
      (pow_pos (Fact.out : p.Prime).pos _)
    Field.finSepDegree H (K P n hn) = m ∧ Field.finInsepDegree H (K P n hn) = p^t := by
  dsimp only
  let n := m*p^t
  have hm₀ : 0 < m := Nat.pos_of_ne_zero (fun h => hm (by rw [h]; exact dvd_zero _))
  have hn : 0<n := Nat.mul_pos hm₀ (pow_pos (Fact.out : p.Prime).pos _)
  have ha : IsIntegral H (r P n hn) := Algebra.IsIntegral.isIntegral _
  have hx : expand H (p^t) (B P m) = B P n := by
    simp only [map_sub, map_pow, expand_X, expand_C, ← pow_mul, n, Nat.mul_comm (p^t) m]
  have hsep := (hermitianTangentBinomial_separable_iff p s P m hm₀).2 hm
  have hs : Field.finSepDegree H (K P n hn) = m := by
    rw [HermitianTangentCover,finSepDegree_adjoin_simple_eq_natSepDegree H L ha.isAlgebraic,
      hermitianTangentRoot_minpoly, ← hx, natSepDegree_expand _ p, hsep.natSepDegree_eq_natDegree,
      natDegree_X_pow_sub_C]
  refine ⟨hs,?_⟩
  have hdeg := Field.finSepDegree_mul_finInsepDegree H (K P n hn)
  rw [hs, hermitianTangentCover_finrank] at hdeg
  exact Nat.eq_of_mul_eq_mul_left hm₀ hdeg

/-- Every tangent has purely inseparable radical covers of all characteristic-power degrees. -/
theorem hermitianTangentCover_purelyInseparable (P : Pts) (t : ℕ) :
    IsPurelyInseparable H (K P (p^t) (pow_pos (Fact.out : p.Prime).pos _)) := by
  apply (isPurelyInseparable_iff_finSepDegree_eq_one H _).2
  have ht := pow_pos (Fact.out : p.Prime).pos t
  have transport (a b : ℕ) (e : a=b) (ha : 0<a) (hb : 0<b) :
      Field.finSepDegree H (K P a ha) = Field.finSepDegree H (K P b hb) := by cases e; rfl
  exact (transport _ _ (one_mul (p^t)) (Nat.mul_pos Nat.zero_lt_one ht) ht).symm.trans
    (hermitianTangentCover_degrees p s P 1 t (Fact.out : p.Prime).not_dvd_one).1

#print axioms hermitianTangentRoot_pow
#print axioms hermitianTangentBinomial_irreducible
#print axioms hermitianTangentBinomial_separable_iff
#print axioms hermitianTangentRoot_minpoly
#print axioms hermitianTangentCover_finrank
#print axioms hermitianTangentCover_degrees
#print axioms hermitianTangentCover_purelyInseparable

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
