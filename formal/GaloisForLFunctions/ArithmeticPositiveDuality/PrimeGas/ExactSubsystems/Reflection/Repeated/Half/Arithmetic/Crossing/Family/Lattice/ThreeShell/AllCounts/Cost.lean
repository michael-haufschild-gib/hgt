import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Packet

/-! # Exact unrestricted state cost on the vacuum, prime and square -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Real

def distinguishes (p : Nat.Primes) (l j r : ℕ) (t u : ℝ) :=
  ¬(0<reading p l j r t ↔ 0<reading p l j r u)

/-- Every allocation of exactly n copies to the three shells is allowed. -/
def feasible (p : Nat.Primes) (t u : ℝ) (n : ℕ) :=
  ∃ l j r : ℕ, l+j+r=n ∧ distinguishes p l j r t u

/-- Rational point in a closed interval. Reversing the packet accounts
for the inclusion of both endpoints in a strict one-bit comparison. -/
def admissibleCount (p : Nat.Primes) (t u : ℝ) (n : ℕ) :=
  ∃ m h : ℕ, 0< m ∧ 2*m<n ∧ 2*h+m≤n ∧
    threshold n m (clock p n u)≤(h : ℝ)/(h+m : ℕ) ∧
    (h : ℝ)/(h+m : ℕ)≤threshold n m (clock p n t)

private theorem gap_neg_iff {a b x : ℝ} (hb : 0≤b) (hba : b≤a) (hx : 0<x) :
    gap a b x<0 ↔ 0<b ∧ b<a := by
  rcases hb.eq_or_lt with eq | pos
  · rw [← eq]; simp [gap]
  rcases hba.eq_or_lt with rfl | lt
  · simp [gap]
  · have h := gap_pos pos lt hx
    dsimp only [gap] at h ⊢
    exact iff_of_true (by linarith only [h]) ⟨pos,lt⟩

private theorem high_bits (p : Nat.Primes) (h j m : ℕ) (hm : 0< m)
    (high : h+j+(h+m)≤2*m) {t : ℝ} (ht : 0<t) :
    ¬(0<reading p h j (h+m) t) ∧
    (0<reading p (h+m) j h t ↔ 0<h ∨ (m<h+j+(h+m) ∧ h+j+(h+m)<2*m)) := by
  let n := h+j+(h+m)
  let x := clock p n t
  have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have np : 0<(n : ℝ) := Nat.cast_pos.mpr (by dsimp only [n]; omega)
  have mb : (m : ℝ)≤n := by exact_mod_cast (show m≤n by dsimp only [n]; omega)
  have bm : (n : ℝ)≤2*m := by exact_mod_cast high
  have xp : 0<x := clock_pos p (by dsimp only [n]; omega) ht
  have den := gap_pos mp (show (m : ℝ)<n+m by linarith only [np]) xp
  have non := gap_nonpos (sub_nonneg.mpr mb) (show (n : ℝ)-m≤ m by linarith only [bm]) xp
  have neg := gap_neg_iff (sub_nonneg.mpr mb) (show (n : ℝ)-m≤ m by linarith only [bm]) xp
  have le : threshold n m x≤0 := div_nonpos_of_nonpos_of_nonneg non den.le
  obtain ⟨lo,hi⟩ := sorted_bits p h j m hm ht
  change (0<reading p h j (h+m) t ↔ (h : ℝ)/(h+m : ℕ)<threshold n m x) at lo
  change (0<reading p (h+m) j h t ↔ threshold n m x<(h : ℝ)/(h+m : ℕ)) at hi
  rw [lo,hi]
  refine ⟨not_lt_of_ge (le.trans (by positivity)),?_⟩
  by_cases hp : 0<h
  · exact iff_of_true (le.trans_lt (div_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (by omega)))) (Or.inl hp)
  · have hz : h=0 := by omega
    rw [show (h : ℝ)/(h+m : ℕ)=0 by rw [hz,Nat.cast_zero,zero_div],threshold,div_lt_iff₀ den,zero_mul,neg]
    simp only [hp,false_or,sub_pos]
    have ab : (n : ℝ)-m< m ↔ (n : ℝ)<2*m := by constructor <;> intro h <;> linarith only [h]
    rw [ab]
    exact_mod_cast (Iff.rfl : (m<n ∧ n<2*m) ↔ _)

/-- Classification at fixed counts, allowing either orientation of the extreme shells. -/
theorem sorted_separator_iff (p : Nat.Primes) (h j m : ℕ) {t u : ℝ} (ht : 0<t) (lt : t<u) :
    let n := h+j+(h+m)
    (distinguishes p h j (h+m) t u ∨ distinguishes p (h+m) j h t u) ↔
      0< m ∧ 2*m<n ∧ threshold n m (clock p n u)≤(h : ℝ)/(h+m : ℕ) ∧
        (h : ℝ)/(h+m : ℕ)≤threshold n m (clock p n t) := by
  dsimp only
  by_cases hm : 0< m
  · by_cases small : 2*m<h+j+(h+m)
    · have nn : 0<h+j+(h+m) := by omega
      have order := threshold_strictAnti hm small (clock_pos p nn ht) (clock_pos p nn (ht.trans lt))
        (clock_lt p nn lt)
      obtain ⟨a,b⟩ := sorted_bits p h j m hm ht
      obtain ⟨c,d⟩ := sorted_bits p h j m hm (ht.trans lt)
      simp only [distinguishes,a,b,c,d,hm,small,true_and]
      change threshold _ _ _<threshold _ _ _ at order
      grind only
    · obtain ⟨a,b⟩ := high_bits p h j m hm (le_of_not_gt small) ht
      obtain ⟨c,d⟩ := high_bits p h j m hm (le_of_not_gt small) (ht.trans lt)
      simp only [distinguishes,a,b,c,d,iff_self,not_true_eq_false,or_self,small,false_and,and_false]
  · have mz : m=0 := by omega
    subst m
    have eq (v : ℝ) : reading p h j h v=0 := by
      have := reverse_reading p h j h v
      linarith only [this]
    simp [distinguishes,eq]

/-- Exact criterion for an arbitrary state budget with all three shell
multiplicities free. The integer feasibility condition has no partition sums. -/
theorem feasible_iff (p : Nat.Primes) {t u : ℝ} (ht : 0<t) (lt : t<u) (n : ℕ) :
    feasible p t u n ↔ admissibleCount p t u n := by
  constructor
  · rintro ⟨l,j,r,rfl,sep⟩
    rcases le_total l r with le | le
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le le
      obtain ⟨hm,small,lo,hi⟩ := (sorted_separator_iff p l j m ht lt).mp (Or.inl sep)
      exact ⟨m,l,hm,small,by omega,lo,hi⟩
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le le
      obtain ⟨hm,small,lo,hi⟩ := (sorted_separator_iff p r j m ht lt).mp (Or.inr sep)
      rw [show r+m+j+r=r+j+(r+m) by omega]
      exact ⟨m,r,hm,small,by omega,lo,hi⟩
  · rintro ⟨m,h,hm,small,space,lo,hi⟩
    let j := n-(2*h+m)
    have total : h+j+(h+m)=n := by dsimp only [j]; omega
    have ok : distinguishes p h j (h+m) t u ∨ distinguishes p (h+m) j h t u := by
      apply (sorted_separator_iff p h j m ht lt).mpr
      simpa only [total] using And.intro hm (And.intro small (And.intro lo hi))
    exact ok.elim (fun v => ⟨h,j,h+m,total,v⟩) (fun v => ⟨h+m,j,h,by omega,v⟩)

/-- The closed-interval criterion has a least feasible state count for every
two distinct positive dampings; that count is attained by a physical packet. -/
theorem minimum_state_count (p : Nat.Primes) {t u : ℝ} (ht : 0<t) (lt : t<u) :
    ∃ n : ℕ, feasible p t u n ∧ admissibleCount p t u n ∧
      (∀ k, admissibleCount p t u k → n≤k) ∧
      ∀ N, (∃ k≤N, feasible p t u k) ↔ n≤N := by
  classical
  obtain ⟨A,B,hb,sep⟩ := separates p (div_lt_div_of_pos_right lt (zero_lt_two : (0 : ℝ)<2))
  have phys : distinguishes p (A+3*B) (3*A+4*B) B t u := by
    change ¬(0<squareResponse p A B t ↔ 0<squareResponse p A B u)
    simpa only [square_positive_iff] using sep
  have someN : ∃ n, admissibleCount p t u n :=
    ⟨_,(feasible_iff p ht lt _).mp ⟨_,_,_,rfl,phys⟩⟩
  have chosen := Nat.find_spec someN
  have real := (feasible_iff p ht lt _).mpr chosen
  exact ⟨_,real,chosen,fun _ h => Nat.find_min' someN h,fun _ =>
    ⟨fun ⟨k,hk,w⟩ => (Nat.find_min' someN ((feasible_iff p ht lt k).mp w)).trans hk,
      fun cap => ⟨_,cap,real⟩⟩⟩

#print axioms sorted_separator_iff
#print axioms feasible_iff
#print axioms minimum_state_count

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
