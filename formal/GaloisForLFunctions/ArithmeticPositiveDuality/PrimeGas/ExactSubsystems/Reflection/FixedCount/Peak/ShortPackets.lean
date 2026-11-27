import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Paired

/-! # Three and four prime modes are distinguished by the largest outgoing shell probability -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Finset Real
open scoped ComplexConjugate

/-- An ordered prime packet has three modes when the interior primes coincide and four otherwise. -/
structure ShortPacket where
  low : Nat.Primes
  left : Nat.Primes
  right : Nat.Primes
  high : Nat.Primes
  low_lt : low.val < left.val
  middle_le : left.val ≤ right.val
  high_lt : right.val < high.val

namespace ShortPacket

def modes (A : ShortPacket) : Finset Nat.Primes := {A.low, A.left, A.right, A.high}

def l (A : ShortPacket) : A.modes := ⟨A.low, mem_insert_self ..⟩
def q (A : ShortPacket) : A.modes := ⟨A.left, mem_insert_of_mem (mem_insert_self ..)⟩
def r (A : ShortPacket) : A.modes := ⟨A.right, mem_insert_of_mem (mem_insert_of_mem (mem_insert_self ..))⟩
def u (A : ShortPacket) : A.modes :=
  ⟨A.high, mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))⟩

theorem cases_mode (A : ShortPacket) (i : A.modes) : i=A.l ∨ i=A.q ∨ i=A.r ∨ i=A.u := by
  have h := i.property
  simp only [modes, mem_insert, mem_singleton] at h
  rcases h with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

def flip (A : ShortPacket) : Equiv.Perm A.modes :=
  (Equiv.swap A.l A.u).trans (Equiv.swap A.q A.r)

private theorem neq_of_lt {A : ShortPacket} {i j : A.modes} (h : i.val.val < j.val.val) : i ≠ j :=
  fun eqv => h.ne (congrArg (fun k : A.modes => k.val.val) eqv)

private theorem lq (A : ShortPacket) : A.l ≠ A.q := neq_of_lt A.low_lt
private theorem lr (A : ShortPacket) : A.l ≠ A.r := neq_of_lt (A.low_lt.trans_le A.middle_le)
private theorem qu (A : ShortPacket) : A.q ≠ A.u := neq_of_lt (A.middle_le.trans_lt A.high_lt)
private theorem ru (A : ShortPacket) : A.r ≠ A.u := neq_of_lt A.high_lt

theorem flip_l (A : ShortPacket) : A.flip A.l = A.u := by
  simp only [flip, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (qu A).symm (ru A).symm]

theorem flip_u (A : ShortPacket) : A.flip A.u = A.l := by
  simp only [flip, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (lq A) (lr A)]

theorem flip_q (A : ShortPacket) : A.flip A.q = A.r := by
  simp only [flip, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (lq A).symm (qu A), Equiv.swap_apply_left]

theorem flip_r (A : ShortPacket) : A.flip A.r = A.q := by
  simp only [flip, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (lr A).symm (ru A), Equiv.swap_apply_right]

theorem energy_bounds (A : ShortPacket) (i : A.modes) :
    primeEnergy A.l ≤ primeEnergy i ∧ primeEnergy i ≤ primeEnergy A.u := by
  have mono {a b : A.modes} (h : a.val.val ≤ b.val.val) : primeEnergy a ≤ primeEnergy b :=
    log_le_log (Nat.cast_pos.mpr a.val.property.pos) (Nat.cast_le.mpr h)
  have lq' := mono (a := A.l) (b := A.q) A.low_lt.le
  have qr' := mono (a := A.q) (b := A.r) A.middle_le
  have ru' := mono (a := A.r) (b := A.u) A.high_lt.le
  rcases cases_mode A i with rfl | rfl | rfl | rfl <;> constructor <;> linarith only [lq', qr', ru']

private theorem pair_log {S : Finset Nat.Primes} (a b : S) :
    primeEnergy a + primeEnergy b = log ((a.val.val*b.val.val : ℕ) : ℝ) := by
  rw [Nat.cast_mul, log_mul (Nat.cast_ne_zero.mpr a.val.property.ne_zero)
    (Nat.cast_ne_zero.mpr b.val.property.ne_zero)]
  rfl

/-- Unique factorization distinguishes even the square of a single interior prime from the endpoint product. -/
theorem products_ne (A : ShortPacket) : A.low.val*A.high.val ≠ A.left.val*A.right.val := by
  intro he
  have hd : A.low.val ∣ A.left.val*A.right.val := he ▸ dvd_mul_right _ _
  rcases A.low.property.dvd_mul.mp hd with h | h
  · exact A.low_lt.ne ((Nat.prime_dvd_prime_iff_eq A.low.property A.left.property).mp h)
  · exact (A.low_lt.trans_le A.middle_le).ne ((Nat.prime_dvd_prime_iff_eq A.low.property A.right.property).mp h)

theorem gaps_ne (A : ShortPacket) :
    primeEnergy A.q-primeEnergy A.l ≠ primeEnergy A.u-primeEnergy A.r := by
  intro h
  have eqv : primeEnergy A.l+primeEnergy A.u = primeEnergy A.q+primeEnergy A.r := by linarith only [h]
  rw [pair_log, pair_log] at eqv
  change log ((A.low.val*A.high.val : ℕ) : ℝ) = log ((A.left.val*A.right.val : ℕ) : ℝ) at eqv
  have he := congrArg exp eqv
  simp only [exp_log (Nat.cast_pos.mpr (Nat.mul_pos A.low.property.pos A.high.property.pos)),
    exp_log (Nat.cast_pos.mpr (Nat.mul_pos A.left.property.pos A.right.property.pos))] at he
  exact A.products_ne (Nat.cast_injective (R := ℝ) he)

private theorem paired_values (A : ShortPacket) (i : A.modes) :
    primeEnergy i + primeEnergy (A.flip i) = primeEnergy A.l + primeEnergy A.u ∨
    primeEnergy i + primeEnergy (A.flip i) = primeEnergy A.q + primeEnergy A.r := by
  rcases cases_mode A i with rfl | rfl | rfl | rfl
  · exact Or.inl (by rw [flip_l])
  · exact Or.inr (by rw [flip_q])
  · exact Or.inr (by rw [flip_r, add_comm])
  · exact Or.inl (by rw [flip_u, add_comm])

/-- The sign of the peak difference at positive damping is the sign of the interior product
minus the endpoint product, independently of positive particle number. -/
theorem peak_order (A : ShortPacket) {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    (A.low.val*A.high.val < A.left.val*A.right.val ∧
      largest (read primeEnergy : Boson A.modes m → ℝ) (-t) < largest (read primeEnergy : Boson A.modes m → ℝ) t) ∨
    (A.left.val*A.right.val < A.low.val*A.high.val ∧
      largest (read primeEnergy : Boson A.modes m → ℝ) t < largest (read primeEnergy : Boson A.modes m → ℝ) (-t)) := by
  have inc {a b c d : A.modes} (h : a.val.val*b.val.val < c.val.val*d.val.val) :
      primeEnergy a + primeEnergy b < primeEnergy c + primeEnergy d := by
    rw [pair_log, pair_log]
    exact log_lt_log (Nat.cast_pos.mpr (Nat.mul_pos a.val.property.pos b.val.property.pos)) (Nat.cast_lt.mpr h)
  rcases lt_or_gt_of_ne A.products_ne with h | h
  · have he := inc (a := A.l) (b := A.u) (c := A.q) (d := A.r) h
    refine Or.inl ⟨h, boson_peak_above hm primeEnergy A.l A.u (fun i => (A.energy_bounds i).1)
      (fun i => (A.energy_bounds i).2) A.flip ?_ ⟨A.q, by rw [flip_q]; exact he⟩ ht⟩
    intro i
    rcases paired_values A i with hi | hi
    · exact hi.ge
    · exact he.le.trans_eq hi.symm
  · have he := inc (a := A.q) (b := A.r) (c := A.l) (d := A.u) h
    refine Or.inr ⟨h, boson_peak_below hm primeEnergy A.l A.u (fun i => (A.energy_bounds i).1)
      (fun i => (A.energy_bounds i).2) A.flip ?_ ⟨A.q, by rw [flip_q]; exact he⟩ ht⟩
    intro i
    rcases paired_values A i with hi | hi
    · exact hi.le
    · exact hi.le.trans he.le

/-- One largest Born probability detects the line on every three- or four-mode packet. -/
theorem critical_iff_peak (A : ShortPacket) (n : ℕ) (s : ℂ) :
    s.re = 1/2 ↔ measured A.modes (n+1) s = measured A.modes (n+1) (1-conj s) := by
  apply Iff.symm
  apply measured_reflection_iff
  intro t ht
  rcases peak_order A (Nat.zero_lt_succ n) ht with h | h
  · exact h.2.ne'
  · exact h.2.ne

/-- The fixed packet of primes 2,3,5, already at two particles, needs only the largest
conditional shell probability to decide the line. -/
theorem first_three_peak_iff (n : ℕ) (s : ℂ) :
    s.re = 1/2 ↔ measured firstThree (n+1) s = measured firstThree (n+1) (1-conj s) := by
  let A : ShortPacket :=
    ⟨⟨2,Nat.prime_two⟩, ⟨3,Nat.prime_three⟩, ⟨3,Nat.prime_three⟩, ⟨5,Nat.prime_five⟩,
      by change 2 < 3; omega, le_rfl, by change 3 < 5; omega⟩
  have h : A.modes = firstThree := by
    exact congrArg (fun T : Finset Nat.Primes => insert A.low T) (Finset.insert_idem A.left {A.high})
  rw [← h]
  exact A.critical_iff_peak n s

#print axioms first_three_peak_iff
#print axioms products_ne
#print axioms peak_order
#print axioms critical_iff_peak

end ShortPacket
end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
