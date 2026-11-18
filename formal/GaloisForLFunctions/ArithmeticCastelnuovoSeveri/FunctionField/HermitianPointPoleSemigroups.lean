import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianSinglePointPoleOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianQuadraticAbscissas

/-!
# Explicit generators for Hermitian one-point pole semigroups

At a nonrational point P the quotient
(x-x(P))ʲ t(Fr P) / t(P)^(j+1) has just one pole of order Q+j(Q-1),
for 0 ≤ j < Q. At a rational point the reciprocal tangent gives order Q+1.
The construction comes from the complete orbit of contact points of each tangent.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p^(s+1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "φ" => algebraMap E H
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "T" => hermitianGeometricTangentFunction p s
local notation "V" => hermitianGeometricPointValuation p s
local notation "W" => hermitianGeometricInfinityValuation p s
local notation "F" => hermitianFrobeniusPoint p s E

/-- The additive semigroup of exact pole orders achievable with no other poles. -/
def hermitianPointPoleSemigroup (P : Pts) : AddSubmonoid ℕ where
  carrier := {m | ∃ f : H, hermitianSinglePoleBound p s P m f ∧ V P f = WithZero.exp (m:ℤ)}
  zero_mem' := ⟨1,by simp [hermitianSinglePoleBound],by simp⟩
  add_mem' := by
    rintro a b ⟨f,hf,ef⟩ ⟨g,hg,eg⟩
    have he : V P (f*g) = WithZero.exp ((a+b:ℕ):ℤ) := by
      rw [map_mul,ef,eg,Int.natCast_add,WithZero.exp_add]
    exact ⟨f*g,⟨by rw [map_mul]; exact mul_le_one' hf.1 hg.1,he.le,
      fun U hU => by rw [map_mul]; exact mul_le_one' (hf.2.2 U hU) (hg.2.2 U hU)⟩,he⟩

/-- The two consecutive tangent lines and a vertical line through P. -/
def hermitianSuccessiveTangentRatio (P : Pts) (j : ℕ) : H :=
  (z - φ P.val.1)^j * T (F P) / (T P)^(j+1)

local notation "R" => hermitianSuccessiveTangentRatio p s

private theorem vertical_value (P U : Pts) :
    V U (z - φ P.val.1) = WithZero.exp (-(if U.val.1 = P.val.1 then 1 else 0 : ℤ)) := by
  by_cases h : U.val.1 = P.val.1
  · rw [if_pos h,← h,hermitianGeometricPointValuation_radical_sub]
  · rw [if_neg h,neg_zero,WithZero.exp_zero,hermitianGeometricPointValuation_radical_sub_of_ne p s U _ h]

/-- At every finite point the ratio reads the signed sum of the two tangent contacts
and the multiplicity of the vertical line. -/
theorem hermitianSuccessiveTangentRatio_at_point (P U : Pts) (j : ℕ) :
    V U (R P j) = WithZero.exp
      (-(j:ℤ)*(if U.val.1 = P.val.1 then 1 else 0) -
       (((if U = F P then Q else 0) + (if U = F (F P) then 1 else 0) : ℕ):ℤ) +
       ((j:ℤ)+1)*(((if U = P then Q else 0) + (if U = F P then 1 else 0) : ℕ):ℤ)) := by
  rw [hermitianSuccessiveTangentRatio,map_div₀,map_mul,map_pow,map_pow,vertical_value,
    hermitianGeometricPointValuation_tangent_all,hermitianGeometricPointValuation_tangent_all,
    ← WithZero.exp_nsmul,← WithZero.exp_nsmul,← WithZero.exp_add,← WithZero.exp_sub]
  congr 1
  simp only [nsmul_eq_mul,Int.natCast_add,Int.natCast_one]; ring

/-- At infinity the ratio has a zero of order j. -/
theorem hermitianSuccessiveTangentRatio_infinity (P : Pts) (j : ℕ) :
    W (R P j) = WithZero.exp (-(j:ℤ)) := by
  have hc : W (φ P.val.1) ≤ 1 := by
    by_cases h : P.val.1=0
    · rw [h,map_zero,map_zero]; exact zero_le_one
    · exact (hermitianGeometricInfinityValuation_constant p s _ h).le
  have hlt : W (φ P.val.1) < W z := hc.trans_lt (by
    rw [hermitianGeometricInfinityValuation_radical,← WithZero.exp_zero,WithZero.exp_lt_exp]
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos (s+1))
  have hv : W (z-φ P.val.1) = WithZero.exp ((Q:ℕ):ℤ) := by
    rw [(W).map_sub_eq_of_lt_left hlt,hermitianGeometricInfinityValuation_radical]
  rw [hermitianSuccessiveTangentRatio,map_div₀,map_mul,map_pow,map_pow,hv,
    hermitianGeometricInfinityValuation_tangent,hermitianGeometricInfinityValuation_tangent,
    ← WithZero.exp_nsmul,← WithZero.exp_nsmul,← WithZero.exp_add,← WithZero.exp_sub]
  congr 1
  simp only [nsmul_eq_mul,Int.natCast_add,Int.natCast_one]; ring

/-- The nonrational sequence of Q pole orders fills one representative of every residue modulo Q. -/
theorem hermitianPointPoleSemigroup_nonrational_generators (P : Pts) (hP : F P ≠ P)
    (j : ℕ) (hj : j<Q) : Q+j*(Q-1) ∈ hermitianPointPoleSemigroup p s P := by
  have htwo : F (F P) ≠ P := fun h => hP ((hermitianFrobenius_two_fixed_iff p s P).1 h)
  have hQ : 1 ≤ Q := pow_pos (Fact.out : p.Prime).pos _
  have he : V P (R P j) = WithZero.exp ((Q+j*(Q-1):ℕ):ℤ) := by
    rw [hermitianSuccessiveTangentRatio_at_point]
    simp only [if_true,if_neg hP.symm,if_neg htwo.symm,Nat.add_zero,
      Int.natCast_zero,Int.natCast_add,Int.natCast_mul,Int.natCast_sub hQ,Int.natCast_one]
    congr 1; ring
  refine ⟨R P j,⟨?_,he.le,?_⟩,he⟩
  · rw [hermitianSuccessiveTangentRatio_infinity,← WithZero.exp_zero,WithZero.exp_le_exp]; omega
  · intro U hU
    rw [hermitianSuccessiveTangentRatio_at_point,← WithZero.exp_zero,WithZero.exp_le_exp,if_neg hU]
    split_ifs <;> simp only [Nat.zero_add,Nat.add_zero,Int.natCast_add,Int.natCast_zero,
      Int.natCast_one,mul_zero,mul_one] <;> omega

/-- Rational points have a reciprocal tangent with its only pole of order Q+1. -/
theorem hermitianPointPoleSemigroup_rational_generator (P : Pts) (hP : F P=P) :
    Q+1 ∈ hermitianPointPoleSemigroup p s P := by
  have he : V P (T P)⁻¹ = WithZero.exp ((Q+1:ℕ):ℤ) := by
    rw [map_inv₀,hermitianGeometricPointValuation_tangent_all,hP,if_pos rfl,if_pos rfl,
      ← WithZero.exp_neg,neg_neg]
  refine ⟨(T P)⁻¹,⟨?_,he.le,?_⟩,he⟩
  · rw [map_inv₀,hermitianGeometricInfinityValuation_tangent,← WithZero.exp_neg,
      ← WithZero.exp_zero,WithZero.exp_le_exp]; omega
  · intro U hU
    rw [map_inv₀,hermitianGeometricPointValuation_tangent_unit p s P U hU (by rwa [hP]),inv_one]

/-- At a nonrational point all orders Q+aQ+b(Q-1) occur for arbitrary a,b. -/
theorem hermitianPointPoleSemigroup_nonrational_progressions (P : Pts) (hP : F P ≠ P) (a b : ℕ) :
    Q+a*Q+b*(Q-1) ∈ hermitianPointPoleSemigroup p s P := by
  let M := hermitianPointPoleSemigroup p s P
  have hQ : Q ∈ M := (hermitianAffinePoint_first_nongap p s P).1.2
  have hpQ : 0<Q := pow_pos (Fact.out : p.Prime).pos _
  have hrem := hermitianPointPoleSemigroup_nonrational_generators p s P hP (b%Q) (Nat.mod_lt b hpQ)
  have hmul := M.nsmul_mem hQ (a+(b/Q)*(Q-1))
  rw [nsmul_eq_mul] at hmul
  have he : Q+a*Q+b*(Q-1) = Q+(b%Q)*(Q-1)+(a+(b/Q)*(Q-1))*Q := by
    calc
      _ = Q+a*Q+(b%Q+Q*(b/Q))*(Q-1) := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [he]
  exact M.add_mem hrem hmul

/-- Every rational point realizes the full two-generator semigroup of the infinity pole orders. -/
theorem hermitianPointPoleSemigroup_rational_progressions (P : Pts) (hP : F P=P) (a b : ℕ) :
    a*Q+b*(Q+1) ∈ hermitianPointPoleSemigroup p s P := by
  let M := hermitianPointPoleSemigroup p s P
  have h₁ : Q ∈ M := (hermitianAffinePoint_first_nongap p s P).1.2
  have h₂ := hermitianPointPoleSemigroup_rational_generator p s P hP
  simpa only [nsmul_eq_mul,Nat.cast_id] using M.add_mem (M.nsmul_mem h₁ a) (M.nsmul_mem h₂ b)

private theorem consecutive_representation (k n : ℕ) (hk : 0<k) (hn : k*(k-1) ≤ n) :
    ∃ a b : ℕ, n = a*k + b*(k+1) := by
  have hdiv : k-1 ≤ n/k := (Nat.le_div_iff_mul_le hk).2 (by simpa only [Nat.mul_comm] using hn)
  have hrem := Nat.mod_lt n hk
  have hsub : n/k-n%k+n%k=n/k := Nat.sub_add_cancel (by omega)
  refine ⟨n/k-n%k,n%k,?_⟩
  calc
    n = n%k+k*(n/k) := (Nat.mod_add_div n k).symm
    _ = _ := by
      conv_lhs => rw [← hsub]
      ring

/-- Every order at least Q(Q-1) occurs at a square-field point. -/
theorem hermitianPointPoleSemigroup_rational_conductor_bound (P : Pts) (hP : F P=P) (m : ℕ)
    (hm : Q*(Q-1) ≤ m) : m ∈ hermitianPointPoleSemigroup p s P := by
  obtain ⟨a,b,h⟩ := consecutive_representation Q m (pow_pos (Fact.out : p.Prime).pos _) hm
  rw [h]
  exact hermitianPointPoleSemigroup_rational_progressions p s P hP a b

private theorem shifted_consecutive_bound (q m : ℕ) (hq : 1<q) (hm : (q-1)^2 < m) :
    ∃ a b : ℕ, m=q+a*q+b*(q-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 2≤q from hq)
  have hb : (2+k-1)*(2+k-1-1)+(2+k) = (2+k-1)^2+1 := by
    rw [show 2+k-1=k+1 by omega, Nat.add_sub_cancel]; ring
  have hk : (2+k-1)*(2+k-1-1) ≤ m-(2+k) := by omega
  obtain ⟨b,a,h⟩ := consecutive_representation (2+k-1) (m-(2+k)) (by omega) hk
  refine ⟨a,b,?_⟩
  rw [show 2+k-1+1=2+k by omega] at h
  omega

/-- Away from the square field every order above (Q-1)² occurs. -/
theorem hermitianPointPoleSemigroup_nonrational_conductor_bound (P : Pts) (hP : F P ≠ P) (m : ℕ)
    (hm : (Q-1)^2 < m) : m ∈ hermitianPointPoleSemigroup p s P := by
  have hQ := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  obtain ⟨a,b,h⟩ := shifted_consecutive_bound Q m hQ hm
  rw [h]
  exact hermitianPointPoleSemigroup_nonrational_progressions p s P hP a b

#print axioms hermitianPointPoleSemigroup_rational_conductor_bound
#print axioms hermitianPointPoleSemigroup_nonrational_conductor_bound
#print axioms hermitianSuccessiveTangentRatio_at_point
#print axioms hermitianSuccessiveTangentRatio_infinity
#print axioms hermitianPointPoleSemigroup_nonrational_generators
#print axioms hermitianPointPoleSemigroup_rational_generator
#print axioms hermitianPointPoleSemigroup_nonrational_progressions
#print axioms hermitianPointPoleSemigroup_rational_progressions
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
