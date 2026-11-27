import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Cost
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Range

/-! # Integer classification of positive crossings on adjacent shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Real

/-- Existence of a strict binary separator at two positive dampings, allowing
either assignment of the extreme multiplicities. -/
def crosses (p : Nat.Primes) (h j m : ℕ) :=
  ∃ t u : ℝ, 0<t ∧ t<u ∧ (distinguishes p h j (h+m) t u ∨ distinguishes p (h+m) j h t u)

/-- The cubic wall after all common positive factors have been cancelled. -/
private theorem wall_iff (n m h : ℕ) (hm : 0< m) (hs : 2*m<n) :
    (h : ℝ)/(h+m : ℕ)<wall m ((n : ℝ)-m) ((n : ℝ)+m) ↔
      6*h*n<(n-m)*(n-2*m) := by
  have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have np : 0<(n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmp : 0<((h+m : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have eq : wall m ((n : ℝ)-m) ((n : ℝ)+m)=
      (((n : ℝ)-m)*(n-2*m))/(((n : ℝ)+m)*(n+2*m)) := by
    unfold wall
    have a : ((n : ℝ)-m)^2-m^2=n*(n-2*m) := by ring
    have b : ((n : ℝ)+m)^2-m^2=n*(n+2*m) := by ring
    rw [a,b]
    field_simp [np.ne']
  rw [eq,div_lt_div_iff₀ hmp (mul_pos (add_pos np mp) (by positivity)),Nat.cast_add]
  have key : (((n : ℝ)-m)*(n-2*m))*((h : ℝ)+m)-
      h*(((n : ℝ)+m)*(n+2*m))=m*((n-m)*(n-2*m)-6*h*n) := by ring
  rw [← sub_pos,key,mul_pos_iff_of_pos_left mp,sub_pos]
  have mn : m≤n := by omega
  have two : 2*m≤n := hs.le
  have r : ((n-m : ℕ) : ℝ)=(n : ℝ)-m := Nat.cast_sub mn
  have s : ((n-2*m : ℕ) : ℝ)=(n : ℝ)-2*m := by rw [Nat.cast_sub two,Nat.cast_mul,Nat.cast_ofNat]
  rw [← r,← s]
  exact_mod_cast (Iff.rfl : 6*h*n<(n-m)*(n-2*m) ↔ _)

private theorem clock_onto (p : Nat.Primes) {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) :
    ∃ t : ℝ, 0<t ∧ clock p n t=x := by
  have logp : 0<log (p.val : ℝ) := log_pos (Nat.one_lt_cast.mpr p.property.one_lt)
  have np : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  exact ⟨x*n/log p.val,div_pos (mul_pos hx np) logp,by
    rw [clock,div_mul_cancel₀ _ logp.ne',mul_div_cancel_right₀ _ np.ne']⟩

/-- Counts admit a positive crossing iff their cubic asymmetry opposes the
large-damping sign. Clearing the wall gives a strict integer inequality. -/
theorem crosses_iff (p : Nat.Primes) (h j m : ℕ) :
    let n := h+j+(h+m)
    crosses p h j m ↔ 0< m ∧ 0<h ∧ 2*m<n ∧ 6*h*n<(n-m)*(n-2*m) := by
  let n := h+j+(h+m)
  let q := (h : ℝ)/(h+m : ℕ)
  constructor
  · rintro ⟨t,u,ht,lt,sep⟩
    obtain ⟨hm,hs,lo,hi⟩ := (sorted_separator_iff p h j m ht lt).mp sep
    have nn : 0<n := by dsimp only [n]; omega
    have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
    have middle : (m : ℝ)<(n : ℝ)-m := by
      have : 2*(m : ℝ)<n := by exact_mod_cast hs
      linarith only [this]
    have outer : (n : ℝ)-m<n+m := by linarith only [mp]
    have law := gap_ratio_unique_iff mp middle outer
    have atClock {x : ℝ} (hx : 0<x) : ∃! y : ℝ, 0<y ∧ threshold n m y=threshold n m x :=
      ⟨x,⟨hx,rfl⟩,fun y hy => (threshold_strictAnti hm hs).injOn hy.1 hx hy.2⟩
    have pos := ((law _).mp (atClock (clock_pos p nn (ht.trans lt)))).1
    have upper := ((law _).mp (atClock (clock_pos p nn ht))).2
    have qp : 0<q := pos.trans_le lo
    have hp : 0<h := by
      by_contra! hz
      have z : h=0 := by omega
      simp only [q,z,Nat.cast_zero,zero_div,lt_irrefl] at qp
    exact ⟨hm,hp,hs,(wall_iff n m h hm hs).mp (hi.trans_lt upper)⟩
  · rintro ⟨hm,hp,hs,cubic⟩
    have nn : 0<n := by dsimp only [n]; omega
    have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
    have middle : (m : ℝ)<(n : ℝ)-m := by
      have : 2*(m : ℝ)<n := by exact_mod_cast hs
      linarith only [this]
    have outer : (n : ℝ)-m<n+m := by linarith only [mp]
    have qp : 0<q := div_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (by omega))
    obtain ⟨x,⟨hx,eq⟩,_⟩ := (gap_ratio_unique_iff mp middle outer q).mpr
      ⟨qp,(wall_iff n m h hm hs).mpr cubic⟩
    obtain ⟨t,ht,clockEq⟩ := clock_onto p nn hx
    have atT : threshold n m (clock p n t)=q := clockEq ▸ eq
    have lt : t<t+1 := lt_add_one t
    have order := threshold_strictAnti hm hs (clock_pos p nn ht) (clock_pos p nn (ht.trans lt))
      (clock_lt p nn lt)
    refine ⟨t,t+1,ht,lt,(sorted_separator_iff p h j m ht lt).mpr ?_⟩
    exact ⟨hm,hs,order.le.trans atT.le,atT.ge⟩

/-- A crossing occurs at a unique positive temperature, even though the
signed statistic is formed from three exponentially weighted energies. -/
theorem unique_tie_of_crosses (p : Nat.Primes) (h j m : ℕ) (cross : crosses p h j m) :
    ∃! t : ℝ, 0<t ∧ reading p h j (h+m) t=0 := by
  let n := h+j+(h+m)
  let q := (h : ℝ)/(h+m : ℕ)
  obtain ⟨hm,hp,hs,cubic⟩ := (crosses_iff p h j m).mp cross
  have nn : 0<n := by dsimp only [n]; omega
  have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have twice : 2*(m : ℝ)<n := by exact_mod_cast hs
  have qp : 0<q := div_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (by omega))
  obtain ⟨x,⟨hx,eq⟩,uniq⟩ := (gap_ratio_unique_iff mp
    (show (m : ℝ)<(n : ℝ)-m by linarith only [twice])
    (show (n : ℝ)-m<n+m by linarith only [mp]) q).mpr ⟨qp,(wall_iff n m h hm hs).mpr cubic⟩
  obtain ⟨t,ht,atT⟩ := clock_onto p nn hx
  have tie (u : ℝ) (hu : 0<u) : reading p h j (h+m) u=0 ↔ threshold n m (clock p n u)=q := by
    obtain ⟨a,b⟩ := sorted_bits p h j m hm hu
    rw [reverse_reading p h j (h+m) u,neg_pos] at b
    change (0<reading p h j (h+m) u ↔ q<threshold n m (clock p n u)) at a
    change (reading p h j (h+m) u<0 ↔ threshold n m (clock p n u)<q) at b
    grind only
  refine ⟨t,⟨ht,(tie t ht).mpr (by rw [atT]; exact eq)⟩,?_⟩
  intro u hu
  have same := uniq (clock p n u) ⟨clock_pos p nn hu.1,(tie u hu.1).mp hu.2⟩
  exact (show StrictMono (clock p n) from fun _ _ lt => clock_lt p nn lt).injective (same.trans atT.symm)

/-- At least nine states are needed on the adjacent shells to distinguish
any two positive damping values, independently of prime spacing. -/
theorem nine_le_of_crosses (p : Nat.Primes) (h j m : ℕ) (cross : crosses p h j m) :
    9≤h+j+(h+m) := by
  let n := h+j+(h+m)
  obtain ⟨hm,hp,hs,key⟩ := (crosses_iff p h j m).mp cross
  change 6*h*n<(n-m)*(n-2*m) at key
  by_contra! small
  have low : n-2*m≤6 := by dsimp only [n]; omega
  have upper := Nat.mul_le_mul (Nat.sub_le n m) low
  have six : 6≤6*h := by omega
  exact key.not_ge (upper.trans (by simpa only [Nat.mul_comm n 6] using Nat.mul_le_mul_right n six))

/-- Up to reversal, the unique optimal packet has extreme multiplicities
one and two, and six states in the middle shell. -/
theorem nine_state_classification (p : Nat.Primes) (h j m : ℕ) (size : h+j+(h+m)=9) :
    crosses p h j m ↔ h=1 ∧ j=6 ∧ m=1 := by
  have law := crosses_iff p h j m
  dsimp only at law
  rw [law,size]
  constructor
  · rintro ⟨hm,hp,hs,key⟩
    have bound : 9-m≤9 := Nat.sub_le _ _
    have oneM : m=1 := by
      by_contra! bad
      have low : 9-2*m≤5 := by omega
      have := Nat.mul_le_mul bound low
      omega
    subst m
    omega
  · rintro ⟨rfl,rfl,rfl⟩
    norm_num

/-- The smallest apparatus exists on every prime, at its original energy spacing. -/
theorem nine_state_witness (p : Nat.Primes) : crosses p 1 6 1 :=
  (nine_state_classification p 1 6 1 (by omega)).mpr ⟨rfl,rfl,rfl⟩

#print axioms nine_state_witness
#print axioms unique_tie_of_crosses
#print axioms crosses_iff
#print axioms nine_le_of_crosses
#print axioms nine_state_classification

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
