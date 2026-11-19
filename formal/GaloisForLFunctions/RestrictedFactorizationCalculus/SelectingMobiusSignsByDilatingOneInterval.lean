import GaloisForLFunctions.«twin-prime».AffineSquarefreeTransfer
import Mathlib.Data.ZMod.Basic

/-!
# Squarefree signs selected by dilating consecutive intervals

An auxiliary prime square can erase one unwanted position in a dilated
interval while protecting a prescribed finite family of marked primes.
Repeating this on subprogressions preserves a positive proportion of
simultaneous squarefree marked values.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev atMark (D b a n : ℕ) := D*n+b+a

/-- Primes dividing the progression modulus never obstruct a mark. -/
private def clearAt (A : Finset ℕ) (D b : ℕ) : Prop :=
  ∀ a ∈ A,∀ q : ℕ,q.Prime → q ∣ D → ∀ n : ℕ,¬q^2 ∣ atMark D b a n

private theorem hits_one_residue {D b a q : ℕ} (hq : q.Prime) (hd : ¬q ∣ D) (N : ℕ) :
    ((Icc 1 N).filter (fun n => q^2 ∣ atMark D b a n)).card ≤ N/(q^2)+1 := by
  let k := q^2
  have cop : k.Coprime D := (hq.coprime_iff_not_dvd.mpr hd).pow_left _
  apply (card_le_card_of_injOn (t := range (N/k+1)) (fun n => n/k) ?_ ?_).trans_eq (card_range _)
  · intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hn).1).2))
  · intro s hs t ht he
    have modv : Nat.ModEq k (atMark D b a s) (atMark D b a t) := by
      exact ((Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hs).2)).trans
        (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp ht).2).symm
    have m : Nat.ModEq k s t := Nat.ModEq.cancel_left_of_coprime cop
      (Nat.ModEq.add_right_cancel (Nat.ModEq.refl b)
        (Nat.ModEq.add_right_cancel (Nat.ModEq.refl a) modv))
    have es := Nat.mod_add_div s k
    have et := Nat.mod_add_div t k
    change s%k=t%k at m
    change s/k=t/k at he
    rw [m,he] at es
    exact es.symm.trans et

private theorem bad_mark_count (A : Finset ℕ) {D b R H : ℕ} (hD : 0<D) (hR : 0<R)
    (small : ∀ q : ℕ,q.Prime → q ≤ R → q ∣ D) (clear : clearAt A D b)
    {a : ℕ} (ha : a ∈ A) (hH : a ≤ H) (N : ℕ) :
    (((Icc 1 N).filter (fun n => ¬Squarefree (atMark D b a n))).card:ℝ) ≤
      (N:ℝ)/R+(Nat.sqrt (D*N+b+H):ℝ) := by
  let S := Nat.sqrt (D*N+b+H)
  let Q := (Icc (R+1) S).filter Nat.Prime
  let row := fun q : ℕ => (Icc 1 N).filter (fun n => q^2 ∣ atMark D b a n)
  have sub : (Icc 1 N).filter (fun n => ¬Squarefree (atMark D b a n)) ⊆ Q.biUnion row := by
    intro n hn
    obtain ⟨hi,bad⟩ := mem_filter.mp hn
    obtain ⟨q,hq,hit⟩ : ∃ q : ℕ,q.Prime ∧ q^2 ∣ atMark D b a n := by
      simpa only [pow_two,Nat.squarefree_iff_prime_squarefree,not_forall,exists_prop,not_not] using bad
    have hd : ¬q ∣ D := fun h => clear a ha q hq h n hit
    have lo : R<q := lt_of_not_ge (fun h => hd (small q hq h))
    have pos : 0<atMark D b a n :=
      Nat.add_pos_left (Nat.add_pos_left (Nat.mul_pos hD (mem_Icc.mp hi).1) b) a
    have ub : atMark D b a n ≤ D*N+b+H :=
      Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left D (mem_Icc.mp hi).2) b) hH
    have sq : q ≤ S := Nat.le_sqrt.mpr (by simpa only [pow_two] using (Nat.le_of_dvd pos hit).trans ub)
    exact mem_biUnion.mpr ⟨q,mem_filter.mpr ⟨mem_Icc.mpr ⟨lo,sq⟩,hq⟩,mem_filter.mpr ⟨hi,hit⟩⟩
  have cost (q : ℕ) (hq : q ∈ Q) : ((row q).card:ℝ) ≤ (N:ℝ)/(q:ℝ)^2+1 := by
    have prime := (mem_filter.mp hq).2
    by_cases hd : q ∣ D
    · have em : row q=∅ := filter_eq_empty_iff.mpr (fun n _ => clear a ha q prime hd n)
      rw [em,card_empty,Nat.cast_zero]; positivity
    · have hh := (Nat.cast_le (α := ℝ)).mpr (hits_one_residue (b := b) (a := a) prime hd N)
      rw [Nat.cast_add,Nat.cast_one] at hh
      have frac : ((N/(q^2):ℕ):ℝ) ≤ (N:ℝ)/((q^2:ℕ):ℝ) := Nat.cast_div_le
      rw [Nat.cast_pow] at frac
      exact hh.trans (add_le_add frac le_rfl)
  apply ((Nat.cast_le (α := ℝ)).mpr ((card_le_card sub).trans (card_biUnion_le ..))).trans
  rw [Nat.cast_sum]
  apply (sum_le_sum cost).trans
  apply (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)).trans
  simp only [div_eq_mul_inv,sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one]
  have tail := RHTower.sum_inv_sq_tail_le hR S
  simp only [one_div] at tail
  have size : ((Icc (R+1) S).card:ℝ) ≤ S := by
    apply Nat.cast_le.mpr
    rw [Nat.card_Icc]; omega
  exact add_le_add (mul_le_mul_of_nonneg_left tail (Nat.cast_nonneg N)) size

/-- After removing all small local obstructions, at least half the
progression realizes all marked squarefree values simultaneously. -/
private theorem many_squarefree_marks (A : Finset ℕ) {D b : ℕ} (hD : 0<D) (clear : clearAt A D b)
    (small : ∀ q : ℕ,q.Prime → q ≤ 4*(A.card+1) → q ∣ D) :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)/2 ≤
      (((Icc 1 N).filter (fun n => ∀ a ∈ A,Squarefree (atMark D b a n))).card:ℝ) := by
  let R := 4*(A.card+1)
  let H := A.sup id
  let C := D+b+H+1
  have hr : 0<R := by dsimp only [R]; omega
  filter_upwards [eventually_ge_atTop (R^2*C+1)] with N hn
  have hN : 1 ≤ N := by omega
  have bu : D*N+b+H ≤ C*N := by
    dsimp only [C]; nlinarith only [Nat.mul_le_mul_left b hN,Nat.mul_le_mul_left H hN]
  let S := Nat.sqrt (D*N+b+H)
  have hs : S^2 ≤ D*N+b+H := Nat.sqrt_le' _
  have hp : R*S ≤ N := by
    have sq : (R*S)^2 ≤ N^2 := calc
      (R*S)^2 = R^2*S^2 := mul_pow ..
      _ ≤ R^2*(C*N) := Nat.mul_le_mul_left _ (hs.trans bu)
      _ = R^2*C*N := (Nat.mul_assoc ..).symm
      _ ≤ N*N := Nat.mul_le_mul_right N (by omega)
      _ = N^2 := (pow_two _).symm
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp sq
  let good := (Icc 1 N).filter (fun n => ∀ a ∈ A,Squarefree (atMark D b a n))
  let bad := fun a => (Icc 1 N).filter (fun n => ¬Squarefree (atMark D b a n))
  have cover : Icc 1 N ⊆ good ∪ A.biUnion bad := by
    intro n hi
    by_cases h : ∀ a ∈ A,Squarefree (atMark D b a n)
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,h⟩)
    push Not at h
    obtain ⟨a,ha,hn⟩ := h
    exact mem_union_right _ (mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hi,hn⟩⟩)
  have cnt := (Nat.cast_le (α := ℝ)).mpr (((card_le_card cover).trans (card_union_le ..)).trans
    (Nat.add_le_add_left (card_biUnion_le ..) _))
  simp only [Nat.cast_add,Nat.cast_sum,Nat.card_Icc,Nat.add_sub_cancel] at cnt
  have price := sum_le_sum (fun a ha => bad_mark_count A hD hr small clear ha (Finset.le_sup (f := id) ha) N)
  change (∑ a ∈ A,((bad a).card:ℝ)) ≤ ∑ _a ∈ A,((N:ℝ)/R+(S:ℝ)) at price
  simp only [sum_const,nsmul_eq_mul] at price
  have pos : (0:ℝ)<R := Nat.cast_pos.mpr hr
  have step : (S:ℝ) ≤ N/R := (le_div_iff₀ pos).mpr (by
    rw [mul_comm]; exact_mod_cast hp)
  have saved := mul_le_mul_of_nonneg_left (add_le_add_left step ((N:ℝ)/R)) (Nat.cast_nonneg A.card)
  have ar : 4*(A.card:ℝ) ≤ R := by dsimp only [R]; push_cast; linarith
  have budget : (A.card:ℝ)*((N:ℝ)/R+N/R) ≤ N/2 := by
    rw [←add_div,mul_div_assoc',div_le_iff₀ pos]
    nlinarith only [mul_le_mul_of_nonneg_right ar (Nat.cast_nonneg N)]
  change _ ≤ (good.card:ℝ)
  linarith only [cnt,price,saved,budget]

private theorem solve_linear_square {a : ℕ} (b : ℕ) {q : ℕ} (hq : q.Prime) (ha : ¬q ∣ a) :
    ∃ s : ℕ, q^2 ∣ a*s+b := by
  letI : NeZero (q^2) := ⟨pow_ne_zero _ hq.ne_zero⟩
  let u := ZMod.unitOfCoprime a ((hq.coprime_iff_not_dvd.mpr ha).symm.pow_right 2)
  let z : ZMod (q^2) := -((u⁻¹ : (ZMod (q^2))ˣ):ZMod (q^2))*b
  refine ⟨z.val,(ZMod.natCast_eq_zero_iff ..).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  change (u:ZMod (q^2))*(-((u⁻¹:_):ZMod (q^2))*b)+b=0
  simp [←mul_assoc]

/-- One congruence kills a nonmarked position in a dilated window. The
determinants r−ta protect every marked offset from the new prime. -/
private theorem erase_position (A : Finset ℕ) {D b t r : ℕ} (hD : 0<D) (ht : 0<t)
    (clear : clearAt A D b) (miss : ∀ a ∈ A,r ≠ t*a) :
    ∃ q s : ℕ,0<q ∧ clearAt A (D*q^2) (D*s+b) ∧
      ∀ n : ℕ,¬Squarefree (t*((D*q^2)*n+(D*s+b))+r) := by
  let H := A.sup id
  obtain ⟨q,large,prime⟩ := Nat.exists_infinite_primes (t*D+t*H+r+1)
  have big : t*D<q := by omega
  have qfree : ¬q ∣ t*D := fun h => big.not_ge (Nat.le_of_dvd (Nat.mul_pos ht hD) h)
  obtain ⟨s,root⟩ := solve_linear_square (t*b+r) prime qfree
  have kills (n : ℕ) : q^2 ∣ t*((D*q^2)*n+(D*s+b))+r := by
    have eq : t*((D*q^2)*n+(D*s+b))+r=(t*D*s+(t*b+r))+q^2*(t*D*n) := by ring
    rw [eq]; exact dvd_add root (dvd_mul_right ..)
  refine ⟨q,s,prime.pos,?_,fun n hs => (Nat.squarefree_iff_prime_squarefree.mp hs q prime)
    (by simpa only [pow_two] using kills n)⟩
  intro a ha p hp hdiv n
  rcases hp.dvd_mul.mp hdiv with old | fresh
  · have eq : atMark (D*q^2) (D*s+b) a n=atMark D b a (q^2*n+s) := by unfold atMark; ring
    rw [eq]; exact clear a ha p hp old _
  have eq : p=q := (Nat.prime_dvd_prime_iff_eq hp prime).mp (hp.dvd_of_dvd_pow fresh)
  subst p
  intro hit
  let x := D*q^2*n+(D*s+b)
  have dv : q ∣ x+a := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hit
  have dv' := (dvd_pow_self q (by decide : 2 ≠ 0)).trans (kills n)
  have hmod : Nat.ModEq q (t*x+r) (t*x+t*a) := by
    exact (Nat.modEq_zero_iff_dvd.mpr dv').trans (Nat.modEq_zero_iff_dvd.mpr
      (show q ∣ t*x+t*a by rw [←Nat.mul_add]; exact dvd_mul_of_dvd_right dv _)).symm
  have mr := Nat.ModEq.add_left_cancel (Nat.ModEq.refl (t*x)) hmod
  have hr : r<q := by omega
  have haH : a ≤ H := Finset.le_sup (f := id) ha
  have hta : t*a<q := (Nat.mul_le_mul_left t haH).trans_lt (by omega)
  change r%q=(t*a)%q at mr
  rw [Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hta] at mr
  exact miss a ha mr

private theorem erase_all_positions (A : Finset ℕ) (B : ℕ) (hB : 0<B)
    (prime : ∀ a ∈ A,a.Prime) (V : Finset (ℕ × ℕ))
    (off : ∀ v ∈ V,0<v.1 ∧ ∀ a ∈ A,v.2 ≠ v.1*a) :
    ∃ D b : ℕ,0<D ∧ B ∣ D ∧ B ∣ b ∧ clearAt A D b ∧
      ∀ v ∈ V,∀ n : ℕ,¬Squarefree (v.1*(D*n+b)+v.2) := by
  induction V using Finset.induction_on with
  | empty =>
    refine ⟨B^2,0,pow_pos hB _,dvd_pow_self B (by decide : 2 ≠ 0),dvd_zero _,?_,by simp⟩
    intro a ha q hq hd n hit
    have sq : q^2 ∣ B^2 := pow_dvd_pow_of_dvd (hq.dvd_of_dvd_pow hd) _
    have hh := (Nat.dvd_add_right (dvd_mul_of_dvd_left sq n)).mp
      (show q^2 ∣ B^2*n+a by simpa only [atMark,add_zero] using hit)
    exact (Nat.squarefree_iff_prime_squarefree.mp (Irreducible.squarefree (prime a ha)) q hq)
      (by simpa only [pow_two] using hh)
  | @insert v V hv ih =>
    obtain ⟨D,b,hD,BD,Bb,clear,old⟩ := ih (fun v' h => off v' (mem_insert_of_mem h))
    obtain ⟨ht,miss⟩ := off v (mem_insert_self ..)
    obtain ⟨q,s,hq,clear',new'⟩ := erase_position A hD ht clear miss
    refine ⟨D*q^2,D*s+b,Nat.mul_pos hD (pow_pos hq _),dvd_mul_of_dvd_left BD _,
      dvd_add (dvd_mul_of_dvd_left BD _) Bb,clear',?_⟩
    intro v' h n
    rcases mem_insert.mp h with rfl | h
    · exact new' n
    · have eq : D*q^2*n+(D*s+b)=D*(q^2*n+s)+b := by ring
      rw [eq]; exact old v' h _

/-- Dilation by t reads the marked offset r/t unless its label divides t. -/
def markedMobiusReading (P : Finset ℕ) (t x r : ℕ) : ℤ :=
  if t ∣ r ∧ r/t ∈ P ∧ ¬r/t ∣ t then μ t*μ (x+r/t) else 0

/-- All dilations up to T read exactly the indicated marks of the same
length-H window. At least half the progression indices eventually have
every marked sign nonzero. Both statements use one fixed progression. -/
theorem all_bounded_dilations_of_one_mobius_window (P : Finset ℕ) (prime : ∀ p ∈ P,p.Prime)
    (T H : ℕ) :
    ∃ D b : ℕ,0<D ∧
      (∀ n t : ℕ,1 ≤ t → t ≤ T → ∀ r ∈ Icc 1 H,
        μ (t*(D*n+b)+r)=markedMobiusReading P t (D*n+b) r) ∧
      ∀ᶠ N : ℕ in atTop,(N:ℝ)/2 ≤
        (((Icc 1 N).filter (fun n => ∀ p ∈ P,Squarefree (D*n+b+p))).card:ℝ) := by
  let L := max (4*(P.card+1)) (max T (P.sup id))
  let B := L.factorial
  let V := ((Icc 1 T) ×ˢ (Icc 1 H)).filter (fun v => ∀ p ∈ P,v.2 ≠ v.1*p)
  have off (v : ℕ × ℕ) (hv : v ∈ V) : 0<v.1 ∧ ∀ p ∈ P,v.2 ≠ v.1*p := by
    simp only [V,mem_filter,mem_product,mem_Icc] at hv
    exact ⟨hv.1.1.1,hv.2⟩
  obtain ⟨D,b,hD,BD,Bb,clear,erase⟩ := erase_all_positions P B (Nat.factorial_pos _) prime V off
  have each {j : ℕ} (hj : 0<j) (hL : j ≤ L) : j ∣ B := Nat.dvd_factorial hj hL
  have small (q : ℕ) (hq : q.Prime) (h : q ≤ 4*(P.card+1)) := (each hq.pos (h.trans (le_max_left ..))).trans BD
  refine ⟨D,b,hD,?_,many_squarefree_marks P hD clear small⟩
  intro n t ht hT r hr
  let x := D*n+b
  have divx {j : ℕ} (h : j ∣ B) : j ∣ x := dvd_add (dvd_mul_of_dvd_left (h.trans BD) _) (h.trans Bb)
  have tx : t ∣ x := divx (each ht (hT.trans ((le_max_left T _).trans (le_max_right ..))))
  by_cases mark : ∃ p ∈ P,r=t*p
  · obtain ⟨p,hp,rfl⟩ := mark
    have hp' := prime p hp
    have hpt : p ∣ x := divx (each hp'.pos ((Finset.le_sup (f := id) hp).trans
      ((le_max_right T _).trans (le_max_right ..))))
    have eq : t*x+t*p=t*(x+p) := (Nat.mul_add ..).symm
    change μ (t*x+t*p)=markedMobiusReading P t x (t*p)
    rw [eq,markedMobiusReading]
    simp only [dvd_mul_right,Nat.mul_div_cancel_left _ ht,hp,true_and]
    by_cases hit : p ∣ t
    · rw [if_neg (not_not.mpr hit)]
      apply moebius_eq_zero_of_not_squarefree
      intro sq
      have hco := (Nat.squarefree_mul_iff.mp sq).1
      exact (hp'.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_left hit hco)) (dvd_add hpt dvd_rfl)
    · rw [if_pos hit]
      obtain ⟨s,hs⟩ := tx
      have co : t.Coprime (x+p) := by
        rw [hs,Nat.coprime_mul_left_add_right]
        exact (hp'.coprime_iff_not_dvd.mpr hit).symm
      exact isMultiplicative_moebius.map_mul_of_coprime co
  · have hv : (t,r) ∈ V := by
      simp only [V,mem_filter,mem_product]
      exact ⟨⟨mem_Icc.mpr ⟨ht,hT⟩,hr⟩,fun p hp eq => mark ⟨p,hp,eq⟩⟩
    have em : ¬(t ∣ r ∧ r/t ∈ P ∧ ¬r/t ∣ t) := fun h => mark ⟨_,h.2.1,(Nat.mul_div_cancel' h.1).symm⟩
    rw [moebius_eq_zero_of_not_squarefree (erase _ hv n),markedMobiusReading,if_neg em]

#print axioms all_bounded_dilations_of_one_mobius_window

end GaloisForLFunctions.RestrictedFactorizationCalculus
