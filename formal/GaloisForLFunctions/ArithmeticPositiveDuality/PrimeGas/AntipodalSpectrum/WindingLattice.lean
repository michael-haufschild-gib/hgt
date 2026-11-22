import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.ExceptionalTimes
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayArithmeticPartition
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Integer windings of an exceptional relative clock

The realized integer windings form a subgroup of the integers. Its generator
has a reduced positive label ratio. Passage to a common dyadic return makes
rejection the complement of the multiples of a single two-power order.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture DyadicAperture.Binary
open scoped Classical

def gap (a b : ℕ+) := energy a-energy b

def pair (a b : ℕ+) (i : Bool) := cond i b a

def signed (z : ℝ) (k : ℕ) (d : ℝ) := z = (k:ℝ)*d ∨ z = -((k:ℝ)*d)

private def windings (T : ℝ) : AddSubgroup ℤ where
  carrier := {j | ∃ a b : ℕ+, T*gap a b = (j:ℝ)*(2*Real.pi)}
  zero_mem' := ⟨1,1,by simp [gap]⟩
  add_mem' := by
    rintro j k ⟨a,b,ha⟩ ⟨c,d,hc⟩
    refine ⟨a*c,b*d,?_⟩
    rw [Int.cast_add]
    unfold gap at *
    rw [energy_mul,energy_mul]
    linear_combination ha+hc
  neg_mem' := by
    rintro j ⟨a,b,ha⟩
    refine ⟨b,a,?_⟩
    rw [Int.cast_neg]
    unfold gap at *
    linear_combination -ha

private theorem primitive (a b : ℕ+) : ∃ A B : ℕ+, A.Coprime B ∧ gap a b = gap A B := by
  obtain ⟨⟨p,n⟩,h⟩ := _root_.RHTower.thetaCuspPrimitiveRayIndexEquivPositivePair.surjective (a,b)
  change (p.val.1*n,p.val.2*n) = (a,b) at h
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
  exact ⟨_,_,p.property,by unfold gap; rw [energy_mul,energy_mul]; abel⟩

private theorem resonance (T : ℝ) (x : Word) : (binary T).Resonant x ↔
    ∃ j : ℤ, T*gap (x false) (x true) = (j:ℝ)*(2*Real.pi) :=
  ⟨fun h => Circle.exp_eq_one.mp (h ()),fun h _ => Circle.exp_eq_one.mpr h⟩

/-- Every nonzero sampling time admits one reduced generator for all stationary energy gaps. -/
theorem stationary_lattice (T : {T : ℝ // T ≠ 0}) : ∃ a b : ℕ+, a.Coprime b ∧ ∀ x : Word,
    (binary T.val).Resonant x ↔ ∃ k : ℕ, signed (gap (x false) (x true)) k (gap a b) := by
  obtain ⟨g,hg⟩ := IsAddCyclic.exists_generator (α := windings T.val)
  obtain ⟨a₀,b₀,hbase⟩ := g.property
  obtain ⟨a,b,hab,he⟩ := primitive a₀ b₀
  rw [he] at hbase
  refine ⟨a,b,hab,fun x => ?_⟩
  rw [resonance]
  constructor
  · rintro ⟨j,hj⟩
    let w : windings T.val := ⟨j,x false,x true,hj⟩
    obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg w)
    have hs : k • (g.val : ℤ) = j := congrArg (fun v : windings T.val => v.val) hk
    have hm : k*g.val = j := by simpa [zsmul_eq_mul] using hs
    have hr : gap (x false) (x true) = (k:ℝ)*gap a b := by
      apply mul_left_cancel₀ T.property
      rw [hj,← hm,Int.cast_mul, mul_assoc,← hbase]
      ring
    cases k with
    | ofNat n =>
      change gap (x false) (x true) = ((n:ℤ):ℝ)*gap a b at hr
      exact ⟨n,Or.inl (by simpa only [Int.cast_natCast] using hr)⟩
    | negSucc n => exact ⟨n+1,Or.inr (by simpa only [Int.cast_negSucc,neg_mul] using hr)⟩
  · rintro ⟨k,h|h⟩
    · refine ⟨(k:ℤ)*g.val,?_⟩
      rw [h,Int.cast_mul,Int.cast_natCast,mul_assoc,← hbase]; ring
    · refine ⟨-((k:ℤ)*g.val),?_⟩
      rw [h,Int.cast_neg,Int.cast_mul,Int.cast_natCast,neg_mul,mul_assoc,← hbase]; ring

private theorem fixed_signed (t : ℝ) {x : Word} {k : ℕ} {d : ℝ}
    (h : signed (gap (x false) (x true)) k d) :
    (binary t).Resonant x ↔ orderOf (Circle.exp (t*d)) ∣ k := by
  have he : (binary t).Resonant x ↔ Circle.exp (t*gap (x false) (x true)) = 1 :=
    ⟨fun h => h (),fun h _ => h⟩
  rw [he,orderOf_dvd_iff_pow_eq_one,← Circle.exp_natCast_mul]
  rcases h with h | h
  · rw [h,show t*((k:ℝ)*d) = k*(t*d) by ring]
  · rw [h,show t*(-((k:ℝ)*d)) = -(k*(t*d)) by ring,Circle.exp_neg,inv_eq_one]

/-- Reduced ratio, two-power order, and all rejected windings, proved for every exceptional time. -/
theorem rejected_lattice (t : {t : ℝ // t ∈ exceptional}) :
    ∃ (a b : ℕ+) (m : ℕ), a.Coprime b ∧ a ≠ b ∧ 1 < m ∧ (∃ j : ℕ, m = 2^j) ∧
      ∀ x : Word, rejected t.val x ↔ ∃ k : ℕ, ¬m ∣ k ∧ signed (gap (x false) (x true)) k (gap a b) := by
  obtain ⟨y,hy⟩ := t.property
  obtain ⟨K,hK⟩ := rejected_difference t.val
  let T := ((2^K:ℕ):ℝ)*t.val
  have ht : t.val ≠ 0 := by
    intro hz
    exact ((hK y).mp hy).2 (fun _ => by simp [Network.phase,binary,hz])
  have hT : T ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (pow_ne_zero K (by norm_num))) ht
  obtain ⟨a,b,hab,hh⟩ := stationary_lattice ⟨T,hT⟩
  let m := orderOf (Circle.exp (t.val*gap a b))
  have list (x : Word) : rejected t.val x ↔ ∃ k : ℕ, ¬m ∣ k ∧ signed (gap (x false) (x true)) k (gap a b) := by
    rw [hK,hh]
    constructor
    · rintro ⟨⟨k,h⟩,hn⟩
      exact ⟨k,fun hd => hn ((fixed_signed t.val h).mpr hd),h⟩
    · rintro ⟨k,hn,h⟩
      exact ⟨⟨k,h⟩,fun hf => hn ((fixed_signed t.val h).mp hf)⟩
  have base : (binary T).Resonant (pair a b) := (hh _).mpr ⟨1,Or.inl (by simp [pair])⟩
  have hd : m ∣ 2^K := orderOf_dvd_of_pow_eq_one ((binary_power t.val (2^K) (pair a b)).mp base)
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  obtain ⟨k,hk,_⟩ := (list y).mp hy
  have hne : m ≠ 1 := fun hm => hk (hm ▸ one_dvd _)
  have hp : 0 < m := hj ▸ pow_pos (by norm_num) j
  have hdiff : a ≠ b := by
    rintro rfl
    exact hne (by simp [m,gap])
  exact ⟨a,b,m,hab,hdiff,by omega,⟨j,hj⟩,list⟩

#print axioms stationary_lattice
#print axioms rejected_lattice

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
