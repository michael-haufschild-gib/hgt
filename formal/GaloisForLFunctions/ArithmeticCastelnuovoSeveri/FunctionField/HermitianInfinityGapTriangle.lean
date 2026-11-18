import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPoleExpansions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact pole orders and gaps at the Hermitian infinity point

The reduced polynomial expansion identifies the infinity pole semigroup
with the two-generator semigroup of Q and Q+1. A gap has coordinates
0 ≤ quotient < remainder < Q in Euclidean division by Q. This gives its
exact cardinality and the last gap directly on the geometric function field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p^(s+1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "V" => hermitianGeometricInfinityValuation p s

/-- Exact pole orders of functions in the geometric affine normalization. -/
def hermitianInfinityOrders : Set ℕ :=
  {m | ∃ f : H, IsIntegral E[X] f ∧ V f = WithZero.exp (m:ℤ)}

/-- In a reduced polynomial expansion the largest weight actually occurs. -/
theorem hermitianInfinityOrders_reduced (m : ℕ) :
    m ∈ hermitianInfinityOrders p s → ∃ i : Fin (Q+1), ∃ d : ℕ, m=(Q+1)*d+Q*i.val := by
  rintro ⟨f,hf,hm⟩
  by_cases hz : m=0
  · exact ⟨0,0,by simp [hz]⟩
  obtain ⟨a,ha,hb⟩ := hermitianGeometric_exists_bounded_polynomial_expansion p s f m
    ((hermitianGeometric_integral_iff_finite_valuations p s f).1 hf) hm.le
  by_contra! hn
  have ht (i : Fin (Q+1)) (hi : a i ≠ 0) : (Q+1)*(a i).natDegree+Q*i.val ≤ m-1 := by
    have h := hb i hi
    have hne := hn i (a i).natDegree
    omega
  have hv := (hermitianGeometricPolynomialExpansion_pole_bound_iff p s a (m-1)).2 ht
  rw [← ha,hm,WithZero.exp_le_exp] at hv
  omega

/-- The two generators and all their combinations are actual infinity pole orders. -/
theorem hermitianInfinityOrders_iff (m : ℕ) :
    m ∈ hermitianInfinityOrders p s ↔ ∃ a b : ℕ, m=Q*a+(Q+1)*b := by
  constructor
  · intro h
    obtain ⟨i,d,he⟩ := hermitianInfinityOrders_reduced p s m h
    exact ⟨i.val,d,he.trans (add_comm _ _)⟩
  · rintro ⟨a,b,rfl⟩
    let x := algebraMap E[X] H (X : E[X])
    have hx : IsIntegral E[X] x := isIntegral_algebraMap
    have hz : IsIntegral E[X] z := (hermitianGeometricIntegralRadical p s).property
    refine ⟨z^a*x^b,(hz.pow _).mul (hx.pow _),?_⟩
    have hv := hermitianGeometricInfinityValuation_polynomial p s (X : E[X]) X_ne_zero
    simp only [natDegree_X,mul_one] at hv
    rw [map_mul,map_pow,map_pow,hermitianGeometricInfinityValuation_radical,hv,
      ← WithZero.exp_nsmul,← WithZero.exp_nsmul,← WithZero.exp_add]
    congr 1; push_cast; simp only [nsmul_eq_mul]; ring

private theorem residue_criterion (q m : ℕ) (hq : 0<q) :
    (∃ a b : ℕ, m=q*a+(q+1)*b) ↔ m%q ≤ m/q := by
  constructor
  · rintro ⟨a,b,rfl⟩
    rw [show q*a+(q+1)*b=b+q*(a+b) by ring, Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ hq]
    exact (Nat.mod_le b q).trans ((Nat.le_add_left b a).trans (Nat.le_add_left (a+b) (b/q)))
  · intro h
    have hs := Nat.sub_add_cancel h
    refine ⟨m/q-m%q,m%q,?_⟩
    calc
      m = m%q+q*(m/q) := (Nat.mod_add_div m q).symm
      _ = _ := by
        conv_lhs => rw [← hs]
        ring

/-- Euclidean quotient and remainder alone decide whether a pole order occurs. -/
theorem hermitianInfinityOrders_residue (m : ℕ) :
    m ∈ hermitianInfinityOrders p s ↔ m%Q ≤ m/Q :=
  (hermitianInfinityOrders_iff p s m).trans (residue_criterion Q m (pow_pos (Fact.out : p.Prime).pos _))

/-- The geometric gaps are naturally indexed by strict pairs of residues below Q. -/
def hermitianInfinityGapEquiv :
    {m : ℕ // m ∉ hermitianInfinityOrders p s} ≃ Σ r : Fin Q, Fin r.val where
  toFun m := ⟨⟨m.val%Q,Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos _)⟩,
    ⟨m.val/Q,lt_of_not_ge (fun h => m.property ((hermitianInfinityOrders_residue p s _).2 h))⟩⟩
  invFun t := ⟨t.1.val+Q*t.2.val,by
    rw [hermitianInfinityOrders_residue,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt t.1.isLt,
      Nat.add_mul_div_left _ _ (pow_pos (Fact.out : p.Prime).pos _),Nat.div_eq_of_lt t.1.isLt,zero_add]
    exact not_le_of_gt t.2.isLt⟩
  left_inv m := Subtype.ext (Nat.mod_add_div m.val Q)
  right_inv := by
    rintro ⟨r,t⟩
    simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt,Nat.add_mul_div_left _ _ (pow_pos (Fact.out : p.Prime).pos (s+1)),
      Nat.div_eq_of_lt r.isLt]
    exact (Fin.heq_ext_iff (by simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt])).2 rfl

/-- The actual infinity pole semigroup has exactly Q(Q-1)/2 gaps. -/
theorem hermitianInfinity_gap_count :
    Nat.card {m : ℕ // m ∉ hermitianInfinityOrders p s} = Q*(Q-1)/2 := by
  rw [Nat.card_congr (hermitianInfinityGapEquiv p s),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun n => n),Finset.sum_range_id]

/-- The last missing pole order is Q(Q-1)-1. -/
theorem hermitianInfinity_last_gap :
    IsGreatest (hermitianInfinityOrders p s)ᶜ (Q*(Q-1)-1) := by
  have hQ : 1<Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hs : Q*(Q-1)-1 = (Q-1)+Q*(Q-2) := by
    have h : Q-1=(Q-2)+1 := by omega
    have hmul := congrArg (Q*·) h
    rw [Nat.mul_add,Nat.mul_one] at hmul
    omega
  rw [hs]
  constructor
  · change _ ∉ hermitianInfinityOrders p s
    rw [hermitianInfinityOrders_residue,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega),
      Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt (by omega),zero_add]
    omega
  · intro m hm
    have h : m/Q < m%Q := Nat.lt_of_not_ge (fun he => hm ((hermitianInfinityOrders_residue p s _).2 he))
    have hr := Nat.mod_lt m (by omega : 0<Q)
    have ht := Nat.mul_le_mul_left Q (show m/Q ≤ Q-2 by omega)
    have he := Nat.mod_add_div m Q
    omega

#print axioms hermitianInfinityOrders_reduced
#print axioms hermitianInfinityOrders_iff
#print axioms hermitianInfinityOrders_residue
#print axioms hermitianInfinityGapEquiv
#print axioms hermitianInfinity_gap_count
#print axioms hermitianInfinity_last_gap
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
