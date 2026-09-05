import GaloisForLFunctions.RHTower.CoprimeBlockCarryTransgression

/-!
# Complete-period cancellation of coprime chronological words

A strict chronological word in positive pairwise-coprime deletion labels has a
periodic prefix, with period the product of the labels. Every nonempty word
vanishes at every complete period, even after independent phase shifts of its
letters. Each prefix is recovered exactly from its finite cutoff residue.

The proof is generic: independent residue coordinates factor a complete-period
sum by Chinese remaindering, and a zero-mean periodic increment has a periodic
primitive. The same induction works for any family of zero-mean periodic sources
with pairwise-coprime periods. No weights, zeta zero, analytic continuation, or
numerical certificate enters. Overlapping periods and weighted histories are
outside the vanishing statement.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionCoprimeWords

private theorem finEquiv_eq_natCast (d : ℕ) [NeZero d] (n : Fin d) :
    ZMod.finEquiv d n = (n.val : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d =>
    apply Fin.ext
    change n.val = n.val % (d+1)
    exact (Nat.mod_eq_of_lt n.isLt).symm

/-- Independent residue coordinates factor a complete coprime period exactly. -/
theorem coprime_period_sum_mul {R : Type*} [CommRing R]
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    {f g : ℕ → R} (hf : Function.Periodic f p) (hg : Function.Periodic g q) :
    (∑ n ∈ Finset.range (p*q), f n * g n) =
      (∑ n ∈ Finset.range p, f n) * (∑ n ∈ Finset.range q, g n) := by
  letI : NeZero p := ⟨hp.ne'⟩
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (p*q) := ⟨(Nat.mul_pos hp hq).ne'⟩
  let G (x : ZMod p × ZMod q) : R := f x.1.val * g x.2.val
  let e : Fin (p*q) ≃ ZMod p × ZMod q :=
    (ZMod.finEquiv (p*q)).toEquiv.trans (ZMod.chineseRemainder hpq).toEquiv
  have he (n : Fin (p*q)) : G (e n) = f n * g n := by
    change G (ZMod.chineseRemainder hpq (ZMod.finEquiv (p*q) n)) = _
    rw [finEquiv_eq_natCast, map_natCast]
    change f ((n.val : ZMod p).val) * g ((n.val : ZMod q).val) = _
    rw [ZMod.val_natCast, ZMod.val_natCast, hf.map_mod_nat, hg.map_mod_nat]
  have hsum {d : ℕ} [NeZero d] (hd : 0 < d) (u : ℕ → R) :
      ∑ x : ZMod d, u x.val = ∑ n ∈ Finset.range d, u n := by
    letI : NeZero d := ⟨hd.ne'⟩
    rw [← (ZMod.finEquiv d).toEquiv.sum_comp (fun x => u x.val)]
    change (∑ n : Fin d, u (ZMod.finEquiv d n).val) = _
    simp only [finEquiv_eq_natCast, ZMod.val_natCast]
    simp only [Nat.mod_eq_of_lt (Fin.isLt _), Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ n : Fin (p*q), f n * g n := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ n : Fin (p*q), G (e n) := Finset.sum_congr rfl (fun n _ => (he n).symm)
    _ = ∑ x : ZMod p × ZMod q, G x := e.sum_comp G
    _ = (∑ x : ZMod p, f x.val) * ∑ y : ZMod q, g y.val := by
      rw [Fintype.sum_prod_type]
      simp only [G, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by rw [hsum hp, hsum hq]

/-- A zero-mass periodic increment has a periodic primitive. -/
theorem prefix_periodic_of_zero_sum {R : Type*} [AddCommMonoid R]
    {d : ℕ} {f : ℕ → R} (hf : Function.Periodic f d)
    (hzero : ∑ n ∈ Finset.range d, f n = 0) :
    Function.Periodic (fun N => ∑ n ∈ Finset.range N, f n) d := by
  intro N
  dsimp only
  rw [Nat.add_comm N d, Finset.sum_range_add, hzero, zero_add]
  exact Finset.sum_congr rfl (fun n _ => by simpa [Nat.add_comm] using hf n)

theorem deletion_periodic (p : ℕ) :
    Function.Periodic (blockDeletionCoefficient p) p := by
  intro n
  simp [blockDeletionCoefficient, Nat.dvd_add_self_right]

theorem deletion_period_sum_zero {p : ℕ} (hp : 0 < p) :
    ∑ n ∈ Finset.range p, blockDeletionCoefficient p n = 0 := by
  have hid (n : ℕ) (hn : n ∈ Finset.range p) : p ∣ n ↔ n = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
  calc
    _ = ∑ n ∈ Finset.range p, (1 - (p : ℤ) * if n = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [blockDeletionCoefficient, hid n hn]
    _ = 0 := by simp [Finset.sum_sub_distrib, hp]

theorem shifted_deletion_periodic (p : ℕ) :
    Function.Periodic (fun n => blockDeletionCoefficient p (n+1)) p := by
  intro n
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using deletion_periodic p (n+1)

theorem shifted_deletion_period_sum_zero {p : ℕ} (hp : 0 < p) :
    ∑ n ∈ Finset.range p, blockDeletionCoefficient p (n+1) = 0 := by
  have h := Finset.sum_range_succ' (blockDeletionCoefficient p) p
  rw [Finset.sum_range_succ, deletion_period_sum_zero hp] at h
  have he := deletion_periodic p 0
  simp only [zero_add] at he
  rw [he] at h
  exact (add_right_cancel h).symm

/-- Every periodic test on a coprime clock has zero deletion-weighted block mass. -/
theorem deletion_against_coprime_periodic_zero {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    {b : ℕ → ℤ} (hb : Function.Periodic b q) :
    ∑ n ∈ Finset.range (p*q), blockDeletionCoefficient p (n+1) * b n = 0 := by
  rw [coprime_period_sum_mul hp hq hpq (shifted_deletion_periodic p) hb,
    shifted_deletion_period_sum_zero hp, zero_mul]

/-- Strict chronological sums of a family of periodic sources, latest letter first. -/
def sourceWordPrefix {ι R : Type*} [CommRing R] (x : ι → ℕ → R) : List ι → ℕ → R
  | [], _ => 1
  | i :: w, N => ∑ n ∈ Finset.range N, x i n * sourceWordPrefix x w n

/-- The mechanism is residue independence, valid for any zero-mean periodic sources. -/
theorem sourceWordPrefix_periodic {ι R : Type*} [CommRing R]
    (x : ι → ℕ → R) (d : ι → ℕ) (w : List ι)
    (hpos : ∀ i ∈ w, 0 < d i)
    (hperiod : ∀ i ∈ w, Function.Periodic (x i) (d i))
    (hzero : ∀ i ∈ w, ∑ n ∈ Finset.range (d i), x i n = 0)
    (hpair : w.Pairwise (fun i j => (d i).Coprime (d j))) :
    Function.Periodic (sourceWordPrefix x w) (w.map d).prod := by
  induction w with
  | nil => intro n; rfl
  | cons i w ih =>
    have hw : ∀ j ∈ w, 0 < d j := fun j hj => hpos j (List.mem_cons_of_mem i hj)
    have hp := hpos i (by simp)
    have hwp : 0 < (w.map d).prod := List.prod_pos (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      exact hw j hj)
    have hsplit := List.pairwise_cons.mp hpair
    have hper := ih hw
      (fun j hj => hperiod j (List.mem_cons_of_mem i hj))
      (fun j hj => hzero j (List.mem_cons_of_mem i hj)) hsplit.2
    have hpw : (d i).Coprime (w.map d).prod := Nat.coprime_list_prod_right_iff.mpr (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      exact hsplit.1 j hj)
    change Function.Periodic
      (fun N => ∑ n ∈ Finset.range N, x i n * sourceWordPrefix x w n)
      (d i * (w.map d).prod)
    apply prefix_periodic_of_zero_sum
    · intro n
      have hleft := (hperiod i (by simp)).nat_mul (w.map d).prod n
      have hright := hper.nat_mul (d i) n
      simpa only [Nat.cast_id, Nat.mul_comm] using congrArg₂ (· * ·) hleft hright
    · rw [coprime_period_sum_mul hp hwp hpw (hperiod i (by simp)) hper,
        hzero i (by simp), zero_mul]

/-- Shifting the origin of a zero-mass periodic source preserves its block cancellation. -/
theorem period_sum_shift_zero {R : Type*} [AddCommGroup R]
    {d : ℕ} {f : ℕ → R} (hf : Function.Periodic f d)
    (hz : ∑ n ∈ Finset.range d, f n = 0) (r : ℕ) :
    ∑ n ∈ Finset.range d, f (n+r) = 0 := by
  have h := (prefix_periodic_of_zero_sum hf hz) r
  change (∑ n ∈ Finset.range (r+d), f n) = ∑ n ∈ Finset.range r, f n at h
  rw [Finset.sum_range_add] at h
  have hc : (∑ n ∈ Finset.range r, f n) +
      (∑ n ∈ Finset.range d, f (r+n)) = (∑ n ∈ Finset.range r, f n) + 0 := by
    simpa only [add_zero] using h
  simpa only [Nat.add_comm] using add_left_cancel hc

/-- Each arithmetic letter may have its own independently chosen phase. -/
def shiftedWordPrefix (r : ℕ → ℕ) : List ℕ → ℕ → ℤ :=
  sourceWordPrefix (fun p n => blockDeletionCoefficient p (n+r p+1))

theorem shiftedWordPrefix_periodic (r : ℕ → ℕ) (w : List ℕ)
    (hpos : ∀ p ∈ w, 0 < p) (hpair : w.Pairwise Nat.Coprime) :
    Function.Periodic (shiftedWordPrefix r w) w.prod := by
  simpa [shiftedWordPrefix] using sourceWordPrefix_periodic
    (fun p n => blockDeletionCoefficient p (n+r p+1)) (fun p => p) w hpos
    (fun p _ => (shifted_deletion_periodic p).add_const (r p))
    (fun p hp => period_sum_shift_zero (shifted_deletion_periodic p)
      (shifted_deletion_period_sum_zero (hpos p hp)) (r p)) hpair

/-- Independent changes of phase do not rescue complete-period coprime words. -/
theorem shiftedWordPrefix_complete_period_zero (r : ℕ → ℕ) (p : ℕ) (w : List ℕ)
    (hpos : ∀ q ∈ p::w, 0 < q) (hpair : (p::w).Pairwise Nat.Coprime) (k : ℕ) :
    shiftedWordPrefix r (p::w) (k*(p::w).prod) = 0 := by
  have h := (shiftedWordPrefix_periodic r (p::w) hpos hpair).nat_mul_eq k
  simpa only [Nat.cast_id, shiftedWordPrefix, sourceWordPrefix, Finset.sum_range_zero] using h

/-- Lists put the latest chronological letter first. Empty word has coefficient one. -/
def wordPrefix : List ℕ → ℕ → ℤ :=
  sourceWordPrefix (fun p n => blockDeletionCoefficient p (n+1))

/-- All depths retain an exact finite residue description for pairwise-coprime letters. -/
theorem wordPrefix_periodic (w : List ℕ)
    (hpos : ∀ p ∈ w, 0 < p) (hpair : w.Pairwise Nat.Coprime) :
    Function.Periodic (wordPrefix w) w.prod := by
  simpa [wordPrefix] using sourceWordPrefix_periodic
    (fun p n => blockDeletionCoefficient p (n+1)) (fun p => p) w hpos
    (fun p _ => shifted_deletion_periodic p)
    (fun p hp => shifted_deletion_period_sum_zero (hpos p hp)) hpair

theorem wordPrefix_zero (p : ℕ) (w : List ℕ) : wordPrefix (p::w) 0 = 0 := by
  simp [wordPrefix, sourceWordPrefix]

/-- Every cutoff is recovered from its residue modulo the product period. -/
theorem wordPrefix_eq_residue (w : List ℕ)
    (hpos : ∀ p ∈ w, 0 < p) (hpair : w.Pairwise Nat.Coprime) (N : ℕ) :
    wordPrefix w N = wordPrefix w (N % w.prod) :=
  ((wordPrefix_periodic w hpos hpair).map_mod_nat N).symm

/-- Every nonempty coprime word vanishes at all complete arithmetic periods. -/
theorem wordPrefix_complete_period_zero (p : ℕ) (w : List ℕ)
    (hpos : ∀ q ∈ p::w, 0 < q) (hpair : (p::w).Pairwise Nat.Coprime) (k : ℕ) :
    wordPrefix (p::w) (k*(p::w).prod) = 0 := by
  have h := (wordPrefix_periodic (p::w) hpos hpair).nat_mul_eq k
  simpa only [Nat.cast_id, wordPrefix_zero] using h

end RHTower.DeletionCoprimeWords
