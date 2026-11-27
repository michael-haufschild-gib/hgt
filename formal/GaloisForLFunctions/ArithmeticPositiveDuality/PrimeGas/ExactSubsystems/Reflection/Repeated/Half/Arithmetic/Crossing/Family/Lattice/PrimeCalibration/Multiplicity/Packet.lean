import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Moments

/-! # A finite preparation attaining the prime multiplicity threshold -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity

open Finset

/-- Coefficient height of the reciprocal cubic with roots p and 1/p. -/
def threshold (p : Nat.Primes) := p.val*(p.val-1)+1

private def outer : Finset ℕ := {0,3,16,19,20,23}
private def inner : Finset ℕ := {5,6,9,10,25,26}

/-- The six outer occupations carry p states each and the six inner
occupations carry the threshold multiplicity. Both groups have mean 27/2. -/
abbrev States (p : Nat.Primes) := (outer × Fin p.val) ⊕ (inner × Fin (threshold p))

def packet (p : Nat.Primes) : States p → ℕ := Sum.elim (fun x => x.1.val) (fun x => x.1.val)

private theorem weighted {R : Type*} [Semiring R] (p : Nat.Primes) (f : ℕ → R) :
    (∑ i, f (packet p i))=(p.val : R)*(∑ j ∈ outer, f j)+(threshold p : R)*(∑ j ∈ inner, f j) := by
  simp only [packet,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_sum,univ_eq_attach,sum_attach]

private theorem totals (p : Nat.Primes) :
    Fintype.card (States p)=6*(p.val+threshold p) ∧
      2*(∑ i, packet p i)=Fintype.card (States p)*27 := by
  have size := weighted p (fun _ => (1 : ℕ))
  have mass := weighted p id
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] at size
  change (∑ i, packet p i)=_ at mass
  have sizes : outer.card=6 ∧ inner.card=6 := by simp [outer,inner]
  rw [sizes.1,sizes.2] at size
  have sums : (∑ j ∈ outer, id j)=81 ∧ (∑ j ∈ inner, id j)=81 := by simp [outer,inner]
  rw [sums.1,sums.2] at mass
  change Fintype.card (States p)=p.val*6+threshold p*6 at size
  change (∑ i, packet p i)=p.val*81+threshold p*81 at mass
  constructor <;> omega

private theorem bounded (p : Nat.Primes) (i : States p) : packet p i ≤ 27 := by
  rcases i with ⟨⟨j,h⟩,_⟩ | ⟨⟨j,h⟩,_⟩
  · change j≤27
    simp only [outer,mem_insert,mem_singleton] at h
    omega
  · change j≤27
    simp only [inner,mem_insert,mem_singleton] at h
    omega

/-- No occupation exceeds the threshold, independently of the prime. -/
theorem packet_cap (p : Nat.Primes) (m : ℕ) : Sparse.multiplicity (packet p) m ≤ threshold p := by
  have seen := weighted p (fun j => if j=m then (1 : ℕ) else 0)
  rw [sum_ite_eq',sum_ite_eq'] at seen
  simp only [sum_boole,Nat.cast_id] at seen
  change (univ.filter (fun i => packet p i=m)).card≤threshold p
  rw [seen]
  have le : p.val≤threshold p := by
    have hp := p.property.one_lt
    exact (Nat.le_mul_of_pos_right _ (by omega : 0<p.val-1)).trans (Nat.le_succ _)
  by_cases ho : m∈outer
  · have hi : m∉inner := by
      simp only [outer,mem_insert,mem_singleton] at ho
      simp only [inner,mem_insert,mem_singleton]
      omega
    simp only [if_pos ho,if_neg hi,mul_one,mul_zero,add_zero,le]
  · simp only [if_neg ho,mul_zero,zero_add]
    split <;> simp

private theorem cubic_height (p : Nat.Primes) :
    (threshold p : ℝ)=(p.val : ℝ)^2-p.val+1 := by
  have hp := p.property.one_lt.le
  simp only [threshold,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp,Nat.cast_one]
  ring

/-- The reflected polynomial factors into the reciprocal prime cubic and
three separated differences. Its only root above one is the chosen prime. -/
theorem positive_return (p : Nat.Primes) {t : ℝ} (ht : 0<t) :
    agrees (levels (packet p)) t ↔ t=Real.log p.val := by
  have hn : Nonempty (States p) := Fintype.card_pos_iff.mp (by
    rw [(totals p).1]
    have := p.property.pos
    omega)
  letI := hn
  rw [reflected_exponentials (packet p) (totals p).2 (bounded p) t]
  let x := Real.exp t
  let b : ℝ := p.val
  have hx : 1<x := Real.one_lt_exp_iff.mpr ht
  have hb : 1<b := Nat.one_lt_cast.mpr p.property.one_lt
  have difference : (∑ i, x^(packet p i))-(∑ i, x^(27-packet p i))=
      (b*x-1)*(x-b)*(1+x)*(1-x^4)*(1-x^8)*(1-x^12) := by
    rw [weighted p (fun j => x^j),weighted p (fun j => x^(27-j)),cubic_height]
    simp [outer,inner,b]
    ring
  have nz (j : ℕ) (hj : j≠0) : 1-x^j≠0 := sub_ne_zero.mpr (one_lt_pow₀ hx hj).ne
  have left : b*x-1≠0 := by
    have lt := mul_lt_mul_of_pos_left hx (zero_lt_one.trans hb)
    rw [mul_one] at lt
    exact (sub_pos.mpr (hb.trans lt)).ne'
  have pos : 1+x≠0 := by linarith only [hx]
  change (∑ i, x^(packet p i))=(∑ i, x^(27-packet p i)) ↔ _
  rw [← sub_eq_zero,difference]
  simp only [mul_eq_zero,nz 4 (by omega),nz 8 (by omega),nz 12 (by omega),
    left,pos,or_false,false_or,sub_eq_zero]
  change Real.exp t=b ↔ t=Real.log b
  constructor
  · intro eq; rw [←eq,Real.log_exp]
  · intro eq; rw [eq,Real.exp_log (zero_lt_one.trans hb)]

theorem packet_test (p q : Nat.Primes) : accepts (packet p) q 1 ↔ q=p := by
  rw [accepts_iff,abs_one,one_mul,positive_return p (log_pos_prime q)]
  have pos (r : Nat.Primes) : 0<(r.val : ℝ) := Nat.cast_pos.mpr r.property.pos
  exact ⟨fun eq => Subtype.ext (Nat.cast_injective (Real.log_injOn_pos (pos q) (pos p) eq)),
    fun eq => congrArg (fun r : Nat.Primes => Real.log r.val) eq⟩

theorem packet_asymmetric (p : Nat.Primes) : ¬Reflects (levels (packet p)) := by
  obtain ⟨r,hr,prime⟩ := Nat.exists_infinite_primes (p.val+1)
  let q : Nat.Primes := ⟨r,prime⟩
  intro symm
  have hit := (accepts_iff (packet p) q 1).mpr (reflection_agrees symm _)
  have eq := congrArg Subtype.val ((packet_test p q).mp hit)
  change r=p.val at eq
  omega

#print axioms positive_return
#print axioms packet_test
#print axioms packet_cap
#print axioms packet_asymmetric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity
