import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.Packet

/-! # Recovering every real temperature from positive signed responses -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell

open Real

/-- The even prime coordinate is strictly increasing with the absolute damping. -/
def primeCoordinate (p : Nat.Primes) (t : ℝ) := coordinate (t*log p.val)

private theorem coord_pos (p : Nat.Primes) (t : ℝ) : 0<primeCoordinate p t :=
  add_pos (exp_pos _) (exp_pos _)

private theorem coord_lt (p : Nat.Primes) {t u : ℝ} (lt : |t| < |u|) :
    primeCoordinate p t<primeCoordinate p u := by
  have logp := log_pos (Nat.one_lt_cast.mpr p.property.one_lt : 1<(p.val : ℝ))
  have eq (x : ℝ) : coordinate x=2*cosh x := by rw [coordinate,cosh_eq]; ring
  rw [primeCoordinate,primeCoordinate,eq,eq,mul_lt_mul_iff_right₀ zero_lt_two,cosh_lt_cosh,
    abs_mul,abs_mul,abs_of_pos logp]
  exact mul_lt_mul_of_pos_right lt logp

private theorem base_neg (x : ℝ) : base (-x)= -base x := by
  simp only [base,coordinate,neg_neg]
  ring

/-- The bit is a rational lower cut at positive damping and an upper cut
at negative damping. At zero every centered comparison ties. -/
theorem response_pos_iff (p : Nat.Primes) (A B : ℕ) (hb : 0<B) (t : ℝ) :
    0<response p A B t ↔ (0<t ∧ (A : ℝ)/B<primeCoordinate p t) ∨
      (t<0 ∧ primeCoordinate p t<(A : ℝ)/B) := by
  let x := t*log p.val
  have bp : 0<(B : ℝ) := Nat.cast_pos.mpr hb
  have logp := log_pos (Nat.one_lt_cast.mpr p.property.one_lt : 1<(p.val : ℝ))
  have low : (A : ℝ)/B<primeCoordinate p t ↔ 0<(B : ℝ)*primeCoordinate p t-A := by
    rw [div_lt_iff₀ bp,sub_pos,mul_comm]
  have high : primeCoordinate p t<(A : ℝ)/B ↔ (B : ℝ)*primeCoordinate p t-A<0 := by
    rw [lt_div_iff₀ bp,sub_neg,mul_comm]
  rw [response_eq,low,high]
  change 0<base x*((B : ℝ)*primeCoordinate p t-A) ↔ _
  rcases lt_trichotomy t 0 with neg | equal | pos
  · have np : 0< -x := neg_pos.mpr (mul_neg_of_neg_of_pos neg logp)
    have b := base_pos np
    rw [base_neg,neg_pos] at b
    rw [mul_pos_iff]
    simp only [not_lt_of_gt b,b,not_lt_of_gt neg,neg,false_and,true_and,false_or]
  · subst t
    simp only [x,zero_mul,base,neg_zero,sub_self,lt_irrefl,false_and,or_false]
  · have b : 0<base x := base_pos (mul_pos pos logp)
    rw [mul_pos_iff_of_pos_left b]
    simp only [pos,true_and,not_lt_of_gt pos,false_and,or_false]

private theorem threshold_between {x y : ℝ} (xp : 0<x) (lt : x<y) :
    ∃ A B : ℕ, 0<B ∧ x<(A : ℝ)/B ∧ (A : ℝ)/B<y := by
  obtain ⟨q,lo,hi⟩ := exists_rat_btwn lt
  have qp : 0<q := Rat.cast_pos.mp (xp.trans lo)
  have repr : ((q.num.toNat : ℕ) : ℝ)/q.den=(q : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (Rat.num_pos.mpr qp).le,← Rat.cast_def]
  exact ⟨q.num.toNat,q.den,q.den_pos,repr.symm ▸ lo,repr.symm ▸ hi⟩

/-- A single three-shell packet separates any two ordered real readings by
the strict sign of its centered partition difference. -/
theorem separates (p : Nat.Primes) {t u : ℝ} (lt : t<u) :
    ∃ A B : ℕ, 0<B ∧ ¬(0<response p A B t ↔ 0<response p A B u) := by
  by_cases un : u<0
  · have tn := lt.trans un
    have order := coord_lt p (show |u| < |t| by rw [abs_of_neg un,abs_of_neg tn]; exact neg_lt_neg lt)
    obtain ⟨A,B,hb,lo,hi⟩ := threshold_between (coord_pos p u) order
    refine ⟨A,B,hb,?_⟩
    rw [response_pos_iff p A B hb,response_pos_iff p A B hb]
    intro eq
    exact (eq.mpr (Or.inr ⟨un,lo⟩)).elim (fun h => tn.asymm h.1) (fun h => hi.asymm h.2)
  · have up := le_of_not_gt un
    by_cases tn : t<0
    · obtain ⟨A,large⟩ := exists_nat_gt (max (primeCoordinate p t) (primeCoordinate p u))
      have l := (le_max_left _ _).trans_lt large
      have r := (le_max_right _ _).trans_lt large
      refine ⟨A,1,zero_lt_one,?_⟩
      rw [response_pos_iff p A 1 zero_lt_one,response_pos_iff p A 1 zero_lt_one]
      simp only [Nat.cast_one,div_one]
      intro eq
      exact (eq.mp (Or.inr ⟨tn,l⟩)).elim (fun h => r.asymm h.2) (fun h => un h.1)
    · have tp := le_of_not_gt tn
      have order := coord_lt p (show |t| < |u| by rwa [abs_of_nonneg tp,abs_of_nonneg up])
      obtain ⟨A,B,hb,lo,hi⟩ := threshold_between (coord_pos p t) order
      refine ⟨A,B,hb,?_⟩
      rw [response_pos_iff p A B hb,response_pos_iff p A B hb]
      intro eq
      exact (eq.mpr (Or.inl ⟨tp.trans_lt lt,hi⟩)).elim (fun h => lo.asymm h.2) (fun h => tn h.1)

theorem readings_iff (p : Nat.Primes) (t u : ℝ) :
    (∀ A B : ℕ, 0<B → (0<response p A B t ↔ 0<response p A B u)) ↔ t=u := by
  constructor
  · intro same
    rcases lt_trichotomy t u with lt | eq | gt
    · obtain ⟨A,B,hb,no⟩ := separates p lt
      exact (no (same A B hb)).elim
    · exact eq
    · obtain ⟨A,B,hb,no⟩ := separates p gt
      exact (no (same A B hb).symm).elim
  · rintro rfl
    exact fun _ _ _ => Iff.rfl

#print axioms response_pos_iff
#print axioms separates
#print axioms readings_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell
