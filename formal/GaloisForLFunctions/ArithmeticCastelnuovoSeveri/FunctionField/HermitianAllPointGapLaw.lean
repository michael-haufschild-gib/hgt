import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPointGapComparison
import Mathlib.Data.Set.Card

/-!
# The Weierstrass gaps at every geometric Hermitian point

In a complete block of Q consecutive orders, negating the residue modulo
Q pairs the candidate nonrational gaps with the known infinity gaps.
Multiplication by a function with divisor N(P-infinity), at arbitrarily
large common multiples of Q and the point-class order, forces every one
of those candidate gaps to be genuine.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p^(s+1)
local notation "E" => HermitianGeometricConstants p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "F" => hermitianFrobeniusPoint p s E
local notation "J" => hermitianAffineClass p s
local notation "S" => hermitianPointPoleSemigroup p s
local notation "I∞" => hermitianInfinityOrders p s

private def oppositeResidue (q r : ℕ) := if r=0 then 0 else q-r
/-- Negation modulo q inside each consecutive block of length q. -/
def hermitianReflectedPoleIndex (q m : ℕ) := oppositeResidue q (m%q)+q*(m/q)

private theorem opposite_lt {q r : ℕ} (hr : r<q) : oppositeResidue q r < q := by
  unfold oppositeResidue; split <;> omega

private theorem reflect_mod {q : ℕ} (hq : 0<q) (m : ℕ) :
    hermitianReflectedPoleIndex q m % q = oppositeResidue q (m%q) := by
  rw [hermitianReflectedPoleIndex,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (opposite_lt (Nat.mod_lt _ hq))]

private theorem reflect_div {q : ℕ} (hq : 0<q) (m : ℕ) :
    hermitianReflectedPoleIndex q m / q = m/q := by
  rw [hermitianReflectedPoleIndex,Nat.add_mul_div_left _ _ hq,Nat.div_eq_of_lt (opposite_lt (Nat.mod_lt _ hq)),zero_add]

private theorem reflect_twice {q : ℕ} (hq : 0<q) (m : ℕ) :
    hermitianReflectedPoleIndex q (hermitianReflectedPoleIndex q m) = m := by
  change oppositeResidue q (hermitianReflectedPoleIndex q m % q) +
    q*(hermitianReflectedPoleIndex q m / q) = m
  rw [reflect_mod hq, reflect_div hq]
  have hr := Nat.mod_lt m hq
  have h : oppositeResidue q (oppositeResidue q (m%q)) = m%q := by
    unfold oppositeResidue; split_ifs <;> omega
  rw [h,Nat.mod_add_div]

private theorem reflect_le_block {q N : ℕ} (hq : 0<q) (hN : q ∣ N) (m : ℕ) (hm : m≤N) :
    hermitianReflectedPoleIndex q m ≤ N := by
  obtain ⟨k,rfl⟩ := hN
  by_cases he : m=q*k
  · rw [he,hermitianReflectedPoleIndex,Nat.mul_mod_right,oppositeResidue,if_pos rfl,zero_add,Nat.mul_div_cancel_left _ hq]
  · have ht : m/q<k := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm k]; omega)
    have hb := Nat.mul_le_mul_left q (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at hb
    have hr := opposite_lt (Nat.mod_lt m hq)
    unfold hermitianReflectedPoleIndex; omega

private def reflectWindow {q N : ℕ} (hq : 0<q) (hN : q ∣ N) : Equiv.Perm (Fin (N+1)) where
  toFun i := ⟨hermitianReflectedPoleIndex q i.val,Nat.lt_succ_of_le (reflect_le_block hq hN _ (Nat.le_of_lt_succ i.isLt))⟩
  invFun i := ⟨hermitianReflectedPoleIndex q i.val,Nat.lt_succ_of_le (reflect_le_block hq hN _ (Nat.le_of_lt_succ i.isLt))⟩
  left_inv i := Fin.ext (reflect_twice hq i.val)
  right_inv i := Fin.ext (reflect_twice hq i.val)

private theorem reflected_nongap_sufficient (P : Pts) (m : ℕ) :
    (if F P=P then m else hermitianReflectedPoleIndex Q m) ∈ I∞ → m ∈ S P := by
  have hQ : 0<Q := pow_pos (Fact.out : p.Prime).pos _
  by_cases hP : F P=P
  · rw [if_pos hP,hermitianInfinityOrders_iff]
    rintro ⟨a,b,he⟩
    rw [he,mul_comm Q a,mul_comm (Q+1) b]
    exact hermitianPointPoleSemigroup_rational_progressions p s P hP a b
  rw [if_neg hP,hermitianInfinityOrders_residue,reflect_mod hQ,reflect_div hQ]
  intro h
  have hm := Nat.mod_add_div m Q
  have hr := Nat.mod_lt m hQ
  by_cases hz : m%Q=0
  · rw [hz,zero_add] at hm
    have hn : Q ∈ S P := (hermitianAffinePoint_first_nongap p s P).1.2
    rw [← hm,mul_comm]
    simpa only [nsmul_eq_mul,Nat.cast_id] using (S P).nsmul_mem hn (m/Q)
  · let r := Q-m%Q
    have he : r+(m%Q)=Q := Nat.sub_add_cancel (Nat.le_of_lt hr)
    have hrt : r ≤ m/Q := by simpa [r,oppositeResidue,hz] using h
    have hsum := Nat.sub_add_cancel hrt
    have hQ' : Q-1+1=Q := by omega
    have hstep : Q+r*(Q-1) = m%Q+Q*r := by
      have hmul := congrArg (r*·) hQ'
      rw [Nat.mul_add,mul_one,mul_comm r Q] at hmul
      omega
    have hs : m=Q+(m/Q-r)*Q+r*(Q-1) := by
      calc
        m = m%Q+Q*(m/Q) := hm.symm
        _ = m%Q+Q*r+(m/Q-r)*Q := by
          conv_lhs => rw [← hsum]
          ring
        _ = _ := by rw [← hstep]; ring
    rw [hs]
    exact hermitianPointPoleSemigroup_nonrational_progressions p s P hP _ _

/-- At a square-field point the infinity semigroup is unchanged. At every other
point one negates the residue in each block while retaining the quotient. -/
theorem hermitianPointPoleSemigroup_exact (P : Pts) (m : ℕ) :
    m ∈ S P ↔ (if F P=P then m else hermitianReflectedPoleIndex Q m) ∈ I∞ := by
  refine ⟨fun hm => ?_,reflected_nongap_sufficient p s P m⟩
  let N := Q*(addOrderOf (J P)*(m+1))
  have hQ : 0<Q := pow_pos (Fact.out : p.Prime).pos _
  have hJ := (hermitianAffineClass_order_coprime p s P).1
  have hmN : m≤N := by
    have h := Nat.le_mul_of_pos_left (m+1) hJ
    exact (Nat.le_succ _).trans (h.trans (Nat.le_mul_of_pos_left _ hQ))
  have hQN : Q ∣ N := dvd_mul_right _ _
  have hJN : addOrderOf (J P) ∣ N := dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  let e : Equiv.Perm (Fin (N+1)) := if F P=P then Equiv.refl _ else reflectWindow hQ hQN
  have he (i : Fin (N+1)) : (e i).val = if F P=P then i.val else hermitianReflectedPoleIndex Q i.val := by
    by_cases h : F P=P <;> simp [e,h,reflectWindow]
  let A : Set (Fin (N+1)) := {i | (e i).val ∈ I∞}
  let B : Set (Fin (N+1)) := {i | i.val ∈ S P}
  let C : Set (Fin (N+1)) := {i | i.val ∈ I∞}
  have hAB : A ⊆ B := fun i hi => reflected_nongap_sufficient p s P i.val (by rw [← he]; exact hi)
  let ec : A ≃ C := e.subtypeEquiv (fun _ => Iff.rfl)
  have hc : B.ncard ≤ A.ncard := by
    change Nat.card B ≤ Nat.card A
    rw [Nat.card_congr ec]
    exact hermitianPoint_nongap_count_le p s P N hJN
  have eqAB := Set.eq_of_subset_of_ncard_le hAB hc
  let i : Fin (N+1) := ⟨m,Nat.lt_succ_of_le hmN⟩
  have hi : i ∈ A := by rw [eqAB]; exact hm
  change (e i).val ∈ I∞ at hi
  rwa [he] at hi

/-- At a rational affine point the quotient must be at least the remainder. -/
theorem hermitianRationalPoint_gap_iff (P : Pts) (hP : F P=P) (m : ℕ) :
    m ∉ S P ↔ m/Q < m%Q := by
  rw [hermitianPointPoleSemigroup_exact,if_pos hP,hermitianInfinityOrders_residue,not_le]

/-- At a nonrational affine point the positive residues missing from block t are 1 through Q-t-1. -/
theorem hermitianNonrationalPoint_gap_iff (P : Pts) (hP : F P ≠ P) (m : ℕ) :
    m ∉ S P ↔ 0 < m%Q ∧ m/Q+m%Q<Q := by
  have hQ : 0<Q := pow_pos (Fact.out : p.Prime).pos _
  rw [hermitianPointPoleSemigroup_exact,if_neg hP,hermitianInfinityOrders_residue,
    reflect_mod hQ,reflect_div hQ,oppositeResidue]
  have arithmetic (t r q : ℕ) : ¬ (if r=0 then 0 else q-r) ≤ t ↔ 0 < r ∧ t+r<q := by
    split_ifs <;> omega
  exact arithmetic (m/Q) (m%Q) Q

/-- Every gap is indexed by a pair of residues, with the smaller one recording its block. -/
def hermitianPointGapEquiv (P : Pts) :
    {m : ℕ // m ∉ S P} ≃ Σ r : Fin Q, Fin r.val := by
  let hQ : 0<Q := pow_pos (Fact.out : p.Prime).pos _
  let e : Equiv.Perm ℕ := if F P=P then Equiv.refl _ else
    ⟨hermitianReflectedPoleIndex Q,hermitianReflectedPoleIndex Q,reflect_twice hQ,reflect_twice hQ⟩
  have he (m : ℕ) : m ∉ S P ↔ e m ∉ I∞ := by
    rw [hermitianPointPoleSemigroup_exact]
    by_cases h : F P=P <;> simp [e,h]
  exact (e.subtypeEquiv he).trans (hermitianInfinityGapEquiv p s)

/-- Every geometric affine point has exactly Q(Q-1)/2 gaps, independently of its Frobenius degree. -/
theorem hermitianAffinePoint_gap_count (P : Pts) :
    Nat.card {m : ℕ // m ∉ S P} = Q*(Q-1)/2 := by
  rw [← hermitianInfinity_gap_count p s,Nat.card_congr (hermitianPointGapEquiv p s P),
    Nat.card_congr (hermitianInfinityGapEquiv p s)]

/-- The inverse triangle parametrization gives each actual missing pole order. -/
theorem hermitianPointGapEquiv_label (P : Pts) (r : Fin Q) (t : Fin r.val) :
    ((hermitianPointGapEquiv p s P).symm ⟨r,t⟩).val =
      (if F P=P then r.val else Q-r.val) + Q*t.val := by
  have hQ : 0<Q := pow_pos (Fact.out : p.Prime).pos _
  by_cases h : F P=P
  · rw [if_pos h]
    simp only [hermitianPointGapEquiv,h,if_true]; rfl
  · rw [if_neg h]
    simp only [hermitianPointGapEquiv,h,if_false]
    change hermitianReflectedPoleIndex Q (r.val+Q*t.val) = _
    have hr : r.val ≠ 0 := ((Nat.zero_le t.val).trans_lt t.isLt).ne'
    rw [hermitianReflectedPoleIndex,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt,
      Nat.add_mul_div_left _ _ hQ,Nat.div_eq_of_lt r.isLt,zero_add,oppositeResidue,if_neg hr]

/-- The largest gap at a nonrational point is (Q-1)². -/
theorem hermitianNonrationalPoint_last_gap (P : Pts) (hP : F P ≠ P) :
    IsGreatest (↑(S P) : Set ℕ)ᶜ ((Q-1)^2) := by
  have hQ : 1<Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have h (q : ℕ) (hq : 1<q) : (q-1)^2=1+q*(q-2) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 2≤q from hq)
    rw [show 2+k-1=k+1 by omega,show 2+k-2=k by omega]; ring
  constructor
  · change (Q-1)^2 ∉ S P
    rw [hermitianNonrationalPoint_gap_iff p s P hP,h Q hQ,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hQ,Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hQ,zero_add]
    omega
  · intro m hm
    exact le_of_not_gt fun h => hm (hermitianPointPoleSemigroup_nonrational_conductor_bound p s P hP m h)

/-- Above the elliptic case, the single pole order Q+1 detects exactly the square-field points. -/
theorem hermitianAffinePoint_rational_iff_second_nongap (P : Pts) (hq : 2<Q) :
    Q+1 ∈ S P ↔ F P=P := by
  refine ⟨fun hm => ?_,hermitianPointPoleSemigroup_rational_generator p s P⟩
  by_contra hn
  apply ((hermitianNonrationalPoint_gap_iff p s P hn _).2 ?_) hm
  rw [add_comm Q 1, Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),
    Nat.add_div_right _ (by omega),Nat.div_eq_of_lt (by omega)]
  omega

/-- At Q=2 the unique gap at every affine point is one. -/
theorem hermitianEllipticPoint_gap_iff (P : Pts) (hq : Q=2) (m : ℕ) :
    m ∉ S P ↔ m=1 := by
  by_cases h : F P=P
  · rw [hermitianRationalPoint_gap_iff p s P h,hq]
    omega
  · rw [hermitianNonrationalPoint_gap_iff p s P h,hq]
    omega

#print axioms hermitianPointGapEquiv
#print axioms hermitianPointGapEquiv_label
#print axioms hermitianNonrationalPoint_last_gap
#print axioms hermitianAffinePoint_rational_iff_second_nongap
#print axioms hermitianEllipticPoint_gap_iff
#print axioms hermitianPointPoleSemigroup_exact
#print axioms hermitianRationalPoint_gap_iff
#print axioms hermitianNonrationalPoint_gap_iff
#print axioms hermitianAffinePoint_gap_count
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
