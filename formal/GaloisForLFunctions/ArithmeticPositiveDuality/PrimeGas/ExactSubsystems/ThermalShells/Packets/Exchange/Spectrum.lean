import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.ArithmeticGaugeTheory.TheTypicalExponentIsOneHalf

/-! # Two-prime spectra in the integer energy basis -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange

open Finset

def quantum (p : Nat.Primes) : ℕ+ := label (Finsupp.single p 1)

def pair (p q : Nat.Primes) : ℕ+ := quantum p * quantum q

theorem pair_comm (p q : Nat.Primes) : pair p q = pair q p := mul_comm _ _

theorem pair_vector (p q : Nat.Primes) :
    label.symm (pair p q) = Finsupp.single p 1 + Finsupp.single q 1 := by
  rw [pair,quantum,quantum,← label_add,Equiv.symm_apply_apply]

/-- Sorting the primes removes exchange multiplicity while retaining each permitted square once. -/
private def triangle (S : Finset Nat.Primes) (squares : Bool) :=
  if squares then (S ×ˢ S).filter fun z => z.1.val ≤ z.2.val
  else (S ×ˢ S).filter fun z => z.1.val < z.2.val

def levels (S : Finset Nat.Primes) (squares : Bool) :=
  (triangle S squares).image fun z => pair z.1 z.2

private theorem sorted {S : Finset Nat.Primes} {b : Bool} {v : Nat.Primes × Nat.Primes}
    (hv : v ∈ triangle S b) : v.1.val ≤ v.2.val := by
  cases b
  · exact (show v.1.val < v.2.val from (mem_filter.mp hv).2).le
  · exact (mem_filter.mp hv).2

private theorem label_inj (S : Finset Nat.Primes) (b : Bool) :
    Set.InjOn (fun z : Nat.Primes × Nat.Primes => pair z.1 z.2) (triangle S b : Set _) := by
  intro x hx y hy he
  have n := congrArg (fun u : ℕ+ => (u : ℕ)) he
  change ((quantum x.1 : ℕ)*(quantum x.2 : ℕ)) = (quantum y.1 : ℕ)*(quantum y.2 : ℕ) at n
  simp only [quantum,label_one_quantum] at n
  rcases ArithmeticGaugeTheory.mul_eq_mul_of_one_or_prime (Or.inr x.1.property) (Or.inr x.2.property)
    (Or.inr y.1.property) (Or.inr y.2.property) n with h | h
  · exact Prod.ext (Subtype.ext h.1.symm) (Subtype.ext h.2.symm)
  · have a := sorted hx
    have b' := sorted hy
    exact Prod.ext (Subtype.ext (by omega)) (Subtype.ext (by omega))

/-- Exactly the sums of two prime quanta occur. The strict sector excludes equal modes. -/
theorem mem_levels {S : Finset Nat.Primes} {squares : Bool} {n : ℕ+} :
    n ∈ levels S squares ↔ ∃ p ∈ S, ∃ q ∈ S, (squares=true ∨ p≠q) ∧
      label.symm n = Finsupp.single p 1 + Finsupp.single q 1 := by
  constructor
  · intro hn
    obtain ⟨⟨p,q⟩,hm,rfl⟩ := mem_image.mp hn
    cases squares
    · obtain ⟨hs,hl⟩ := mem_filter.mp hm
      exact ⟨p,(mem_product.mp hs).1,q,(mem_product.mp hs).2,Or.inr (fun e => (lt_irrefl _)
        (show p.val < p.val from e ▸ hl)),pair_vector _ _⟩
    · obtain ⟨hs,_⟩ := mem_filter.mp hm
      exact ⟨p,(mem_product.mp hs).1,q,(mem_product.mp hs).2,Or.inl rfl,pair_vector _ _⟩
  · rintro ⟨p,hp,q,hq,h,he⟩
    have hn : pair p q=n := label.symm.injective ((pair_vector p q).trans he.symm)
    cases squares with
    | false =>
      have hne : p≠q := h.resolve_left Bool.false_ne_true
      rcases lt_or_gt_of_ne (show p.val≠q.val from fun e => hne (Subtype.ext e)) with hl | hl
      · exact mem_image.mpr ⟨(p,q),mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,hl⟩,hn⟩
      · exact mem_image.mpr ⟨(q,p),mem_filter.mpr ⟨mem_product.mpr ⟨hq,hp⟩,hl⟩,(pair_comm q p).trans hn⟩
    | true =>
      rcases le_total p.val q.val with hl | hl
      · exact mem_image.mpr ⟨(p,q),mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,hl⟩,hn⟩
      · exact mem_image.mpr ⟨(q,p),mem_filter.mpr ⟨mem_product.mpr ⟨hq,hp⟩,hl⟩,(pair_comm q p).trans hn⟩

/-- Sum an observable over actual integer labels of the chosen sector. -/
def reading (S : Finset Nat.Primes) (squares : Bool) (F : ℕ+ → ℝ) := ∑ n ∈ levels S squares,F n

private theorem expanded (S : Finset Nat.Primes) (squares : Bool) (F : ℕ+ → ℝ) :
    reading S squares F = ∑ p ∈ S, ∑ q ∈ S,
      if (if squares then p.val ≤ q.val else p.val < q.val) then F (pair p q) else 0 := by
  classical
  unfold reading levels
  rw [sum_image (label_inj S squares)]
  cases squares <;> simp only [triangle,Bool.false_eq_true,if_false,if_true,sum_filter,sum_product]

/-- Adding the two sector traces counts ordered pairs, for every diagonal observable. -/
theorem reading_add (S : Finset Nat.Primes) (F : ℕ+ → ℝ) :
    reading S true F + reading S false F = ∑ p ∈ S, ∑ q ∈ S, F (pair p q) := by
  simp only [expanded,Bool.false_eq_true,if_false,if_true]
  have flip : (∑ p ∈ S, ∑ q ∈ S, if p.val < q.val then F (pair p q) else 0) =
      ∑ p ∈ S, ∑ q ∈ S, if q.val < p.val then F (pair p q) else 0 := by
    conv_lhs => rw [sum_comm]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by rw [pair_comm q p]
  rw [flip,← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  by_cases h : p.val ≤ q.val <;> simp [h,lt_of_not_ge,not_lt.mpr]

/-- Subtraction isolates the repeated-prime spectrum, with multiplicity one. -/
theorem reading_sub (S : Finset Nat.Primes) (F : ℕ+ → ℝ) :
    reading S true F - reading S false F = ∑ p ∈ S,F (pair p p) := by
  simp only [expanded,Bool.false_eq_true,if_false,if_true,← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  calc _ = ∑ q ∈ S, if p=q then F (pair p q) else 0 := by
             apply sum_congr rfl
             intro q _
             rcases lt_trichotomy p.val q.val with hl | he | hl
             · have hn : p≠q := fun h => hl.ne (congrArg Subtype.val h)
               simp only [if_pos hl.le,if_pos hl,if_neg hn,sub_self]
             · obtain rfl : p=q := Subtype.ext he
               simp
             · have hn : p≠q := fun h => hl.ne' (congrArg Subtype.val h)
               simp only [if_neg (not_le.mpr hl),if_neg (not_lt.mpr hl.le),if_neg hn,sub_zero]
       _ = _ := by rw [sum_ite_eq,if_pos hp]

#print axioms mem_levels
#print axioms reading_add
#print axioms reading_sub

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange
