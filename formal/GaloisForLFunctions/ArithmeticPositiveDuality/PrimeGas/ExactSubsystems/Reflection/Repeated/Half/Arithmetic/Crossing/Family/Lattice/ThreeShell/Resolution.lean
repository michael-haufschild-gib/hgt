import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.PrimeSquare

/-! # Exact state cost of separating two positive damping parameters -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell

open Real

/-- Coordinate in which the state count is four times a threshold denominator. -/
def cut (p : Nat.Primes) (t : ℝ) := 1/(primeCoordinate p (t/2)+2)

theorem square_states_card (A B : ℕ) : Fintype.card (SquareStates A B)=4*(A+2*B) := by
  simp only [SquareStates,Fintype.card_sum,Fintype.card_fin]
  omega

private theorem coordinate_positive (p : Nat.Primes) (t : ℝ) : 0<primeCoordinate p t :=
  add_pos (exp_pos _) (exp_pos _)

theorem cut_lt_half (p : Nat.Primes) (t : ℝ) : cut p t < 1/2 := by
  apply one_div_lt_one_div_of_lt zero_lt_two
  linarith only [coordinate_positive p (t/2)]

private theorem cut_decreases (p : Nat.Primes) {t u : ℝ} (ht : 0<t) (lt : t<u) : cut p u<cut p t := by
  apply one_div_lt_one_div_of_lt (add_pos (coordinate_positive p _) zero_lt_two)
  refine add_lt_add_of_lt_of_le ?_ le_rfl
  have eq (v : ℝ) : primeCoordinate p v=2*cosh (v*log p.val) := by rw [primeCoordinate,coordinate,cosh_eq]; ring
  have pos := log_pos (Nat.one_lt_cast.mpr p.property.one_lt : 1<(p.val : ℝ))
  rw [eq,eq,mul_lt_mul_iff_right₀ zero_lt_two,cosh_lt_cosh,
    abs_of_pos (mul_pos (half_pos ht) pos),abs_of_pos (mul_pos (half_pos (ht.trans lt)) pos)]
  exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right lt zero_lt_two) pos

theorem square_positive_cut (p : Nat.Primes) (A B : ℕ) (hb : 0<B) {t : ℝ} (ht : 0<t) :
    0<squareResponse p A B t ↔ cut p t<(B : ℝ)/((A : ℝ)+2*B) := by
  rw [square_positive_iff,response_pos_iff p A B hb]
  have hp : 0<t/2 := half_pos ht
  simp only [hp,true_and,not_lt_of_gt hp,false_and,or_false]
  have bp : 0<(B : ℝ) := Nat.cast_pos.mpr hb
  have den := add_pos_of_nonneg_of_pos (Nat.cast_nonneg A : 0≤(A : ℝ)) (mul_pos zero_lt_two bp)
  rw [div_lt_iff₀ bp,cut,div_lt_div_iff₀ (add_pos (coordinate_positive p _) zero_lt_two) den]
  constructor <;> intro h <;> linarith only [h, mul_add (B : ℝ) (primeCoordinate p (t/2)) 2,
    mul_comm (B : ℝ) (primeCoordinate p (t/2)),mul_comm (B : ℝ) 2]

def separatesWithin (p : Nat.Primes) (t u : ℝ) (N : ℕ) : Prop :=
  ∃ A B : ℕ, 0<B ∧ Fintype.card (SquareStates A B)≤N ∧
    ¬(0<squareResponse p A B t ↔ 0<squareResponse p A B u)

/-- The endpoint of the lower temperature is included because the bit uses
a strict partition comparison. -/
def admissible (p : Nat.Primes) (t u : ℝ) (n : ℕ) : Prop :=
  0<n ∧ ∃ m : ℕ, 0 < m ∧ cut p u<(m : ℝ)/n ∧ (m : ℝ)/n≤cut p t

theorem cost_iff_denominator (p : Nat.Primes) {t u : ℝ} (ht : 0<t) (lt : t<u) (N : ℕ) :
    separatesWithin p t u N ↔ ∃ n : ℕ, admissible p t u n ∧ 4*n≤N := by
  have order := cut_decreases p ht lt
  have test (A B : ℕ) (hb : 0<B) :
      ¬(0<squareResponse p A B t ↔ 0<squareResponse p A B u) ↔
        cut p u<(B : ℝ)/((A : ℝ)+2*B) ∧ (B : ℝ)/((A : ℝ)+2*B)≤cut p t := by
    rw [square_positive_cut p A B hb ht,square_positive_cut p A B hb (ht.trans lt)]
    by_cases lo : cut p u<(B : ℝ)/((A : ℝ)+2*B)
    · simp only [lo,iff_true,not_lt,true_and]
    · have hi : ¬cut p t<(B : ℝ)/((A : ℝ)+2*B) := fun h => lo (order.trans h)
      simp only [lo,hi,iff_self,not_true_eq_false,false_and]
  constructor
  · rintro ⟨A,B,hb,count,sep⟩
    refine ⟨A+2*B,⟨by omega,B,hb,?_⟩,by rwa [← square_states_card]⟩
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using (test A B hb).mp sep
  · rintro ⟨n,⟨hn,m,hm,lo,hi⟩,count⟩
    have bound := (div_lt_div_iff₀ (Nat.cast_pos.mpr hn : 0<(n : ℝ)) (zero_lt_two : (0 : ℝ)<2)).mp
      (hi.trans_lt (cut_lt_half p t))
    have small : 2*m≤n := by
      exact_mod_cast (by linarith only [bound,mul_comm (m : ℝ) 2] : (2 : ℝ)*m≤n)
    let A := n-2*m
    have eq : A+2*m=n := Nat.sub_add_cancel small
    refine ⟨A,m,hm,by rwa [square_states_card,eq],(test A m hm).mpr ?_⟩
    have realEq : (A : ℝ)+2*m=n := by exact_mod_cast eq
    rw [realEq]
    exact ⟨lo,hi⟩

/-- The least rational denominator in the half-open interval gives the
exact threshold in the number of states of the measuring packet. -/
theorem least_state_cost (p : Nat.Primes) {t u : ℝ} (ht : 0<t) (lt : t<u) :
    ∃ d : ℕ, admissible p t u d ∧ (∀ n, admissible p t u n → d≤n) ∧
      ∀ N, separatesWithin p t u N ↔ 4*d≤N := by
  classical
  obtain ⟨A,B,hb,sep⟩ := separates p (div_lt_div_of_pos_right lt (zero_lt_two : (0 : ℝ)<2))
  have feasible : separatesWithin p t u (Fintype.card (SquareStates A B)) :=
    ⟨A,B,hb,le_rfl,by simpa only [square_positive_iff] using sep⟩
  obtain ⟨n,wit,_⟩ := (cost_iff_denominator p ht lt _).mp feasible
  have non : ∃ n, admissible p t u n := ⟨n,wit⟩
  refine ⟨Nat.find non,Nat.find_spec non,fun _ h => Nat.find_min' non h,fun N => ?_⟩
  rw [cost_iff_denominator p ht lt]
  exact ⟨fun ⟨k,h,cap⟩ => (Nat.mul_le_mul_left 4 (Nat.find_min' non h)).trans cap,
    fun cap => ⟨Nat.find non,Nat.find_spec non,cap⟩⟩

#print axioms square_positive_cut
#print axioms cost_iff_denominator
#print axioms least_state_cost

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell
