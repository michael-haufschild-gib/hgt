import GaloisForLFunctions.BezoutValuationIncidence.Divisors.UnitFractionWitnessFibers
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Coprime.Basic

/-!
# Congruence intersections of unit-fraction witnesses

Trybushnyi's Type II events have an explicit inverse multiplier. Their
intersection can therefore be read off from the offsets even when the moduli
share factors. This is the arithmetic input to the square expansion in
Lemmas 2.1–2.2 of arXiv:2611.14167.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence.UnitFractions

/-- Parameters of one Type II residue test; the numerator is allowed to vary. -/
structure Event where
  K : ℕ+
  a : ℕ+
  c : ℕ+
  d : ℕ+

namespace Event
def modulus (e : Event) : ℤ := (e.K : ℤ)*e.a*e.c*e.d-1
def residue (e : Event) : ℤ := -(e.K : ℤ)*e.a^2*e.d
def holds (e : Event) (n : ℤ) : Prop := e.modulus ∣ n*e.c+e.a

/-- The inverse of the slope is explicit even at composite moduli. -/
theorem holds_iff (e : Event) (n : ℤ) : e.holds n ↔ e.residue ≡ n [ZMOD e.modulus] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨(e.K : ℤ)*e.a*e.d*t-n,?_⟩
    unfold residue modulus at *
    linear_combination (e.K : ℤ)*e.a*e.d*ht
  · rintro ⟨t,ht⟩
    refine ⟨(e.c : ℤ)*t-e.a,?_⟩
    unfold residue modulus at *
    linear_combination (e.c : ℤ)*ht

/-- The entire integer event is an explicitly parametrized progression. -/
theorem progression (e : Event) :
    {n : ℤ | e.holds n} = Set.range (fun t : ℤ => e.residue+e.modulus*t) := by
  ext n
  change e.holds n ↔ ∃ t : ℤ, _ = n
  rw [holds_iff,Int.modEq_iff_add_fac]
  exact exists_congr fun _ => eq_comm

/-- The integer progression reconstructs the actual positive unit fractions. -/
theorem positive_fiber (e : Event) (n : ℕ+) :
    e.residue ≡ (n : ℤ) [ZMOD e.modulus] ↔
      ∃! b : ℕ+, Represents e.K n (e.a*b*e.d) (e.a*e.c*e.d*n) (b*e.c*e.d*n) := by
  rw [← holds_iff]
  simp_rw [structured_iff]
  rw [← event_iff_existsUnique]
  unfold holds modulus
  have hp : 0 < (e.K : ℕ)*e.a*e.c*e.d := by positivity
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub hp]
  rfl

/-- Two events can coexist precisely when the offsets agree modulo the common divisor. -/
theorem intersection_nonempty (e f : Event) :
    (∃ n, e.holds n ∧ f.holds n) ↔
      (e.modulus.gcd f.modulus : ℤ) ∣ f.residue-e.residue := by
  simp only [holds_iff,Int.modEq_iff_dvd]
  constructor
  · rintro ⟨n,he,hf⟩
    simpa only [show n-e.residue-(n-f.residue) = f.residue-e.residue by ring] using
      dvd_sub ((Int.gcd_dvd_left _ _).trans he) ((Int.gcd_dvd_right _ _).trans hf)
  · rintro ⟨k,hk⟩
    let a := Int.gcdA e.modulus f.modulus
    let b := Int.gcdB e.modulus f.modulus
    have hb : (e.modulus.gcd f.modulus : ℤ) = e.modulus*a + f.modulus*b :=
      Int.gcd_eq_gcd_ab _ _
    refine ⟨e.residue+e.modulus*a*k,⟨a*k,by ring⟩,⟨-b*k,?_⟩⟩
    linear_combination -hk - k*hb

/-- Relative to any common witness the simultaneous event is one exact lcm class. -/
theorem intersection_class (e f : Event) (n t : ℤ) :
    e.holds n → f.holds n → (e.holds t ∧ f.holds t ↔ n ≡ t [ZMOD e.modulus.lcm f.modulus]) := by
  simp only [holds_iff]
  intro he hf
  rw [← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨fun ⟨a,b⟩ => ⟨he.symm.trans a,hf.symm.trans b⟩,
    fun ⟨a,b⟩ => ⟨he.trans a,hf.trans b⟩⟩

/-- The common period for any finite intersection is exactly the lcm, including
degenerate singleton events of modulus zero and the empty family. -/
theorem family_class {ι : Type*} (s : Finset ι) (e : ι → Event) (n t : ℤ) :
    (∀ i ∈ s, (e i).holds n) → ((∀ i ∈ s, (e i).holds t) ↔
      s.lcm (fun i => (e i).modulus) ∣ t-n) := by
  intro H
  rw [Finset.lcm_dvd_iff]
  constructor
  · intro T i hi
    exact Int.modEq_iff_dvd.mp (((holds_iff _ _).1 (H i hi)).symm.trans
      ((holds_iff _ _).1 (T i hi)))
  · intro D i hi
    exact (holds_iff _ _).2 (((holds_iff _ _).1 (H i hi)).trans (Int.modEq_iff_dvd.mpr (D i hi)))

/-- All translations preserving a nonempty family intersection are multiples of its lcm. -/
theorem family_periods {ι : Type*} (s : Finset ι) (e : ι → Event) (b : ℤ) :
    (∃ n, ∀ i ∈ s, (e i).holds n) →
      ((∀ n, (∀ i ∈ s, (e i).holds n) → (∀ i ∈ s, (e i).holds (n+b))) ↔
        s.lcm (fun i => (e i).modulus) ∣ b) := by
  rintro ⟨n,H⟩
  constructor
  · intro T
    simpa only [add_sub_cancel_left] using (family_class s e n (n+b) H).1 (T n H)
  · intro hb t ht
    apply (family_class s e t (t+b) ht).2
    simpa only [add_sub_cancel_left] using hb

/-- Exchanging the intercept and slope inverts the residue class. -/
def dual (e : Event) : Event := ⟨e.K,e.c,e.a,e.d⟩

private theorem dual_modulus (e : Event) : e.dual.modulus=e.modulus := by
  unfold dual modulus
  ring

/-- The two offsets multiply to one modulo the common modulus, even for
composite or zero modulus. -/
theorem inverse_residues (e : Event) : e.residue*e.dual.residue ≡ 1 [ZMOD e.modulus] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(e.modulus+2),?_⟩
  unfold residue dual modulus
  ring

/-- Every successful numerator is coprime to its witness modulus. -/
theorem witness_coprime (e : Event) (n : ℤ) (hn : e.holds n) : IsCoprime n e.modulus := by
  have h := (((holds_iff _ _).1 hn).symm.mul_right e.dual.residue).trans (inverse_residues e)
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp h
  exact ⟨e.dual.residue,t,by linear_combination -ht⟩

/-- For any witness, all of its modular inverses are exactly the witnesses to
the event obtained by swapping slope and intercept. -/
theorem dual_witness_iff (e : Event) (n m : ℤ) (hn : e.holds n) :
    e.dual.holds m ↔ n*m ≡ 1 [ZMOD e.modulus] := by
  rw [holds_iff,dual_modulus]
  have h := (holds_iff _ _).1 hn
  have hi := inverse_residues e
  constructor
  · intro hm
    exact (h.mul hm).symm.trans hi
  · intro hm
    have hn' := (h.symm.mul_right e.dual.residue).trans hi
    have h₁ := (hn'.mul_left m).symm
    have h₂ := hm.mul_right e.dual.residue
    rw [mul_one] at h₁
    rw [one_mul] at h₂
    rw [show m*(n*e.dual.residue)=n*m*e.dual.residue by ring] at h₁
    exact (h₁.trans h₂).symm

/-- The reciprocal event is identical precisely when the difference of the
squares of its two shape parameters vanishes modulo the modulus. -/
theorem self_dual_iff (e : Event) :
    (∀ n, e.holds n ↔ e.dual.holds n) ↔ e.modulus ∣ (e.a : ℤ)^2-(e.c : ℤ)^2 := by
  have hr : e.holds e.residue := (holds_iff _ _).2 Int.ModEq.rfl
  have test : e.dual.holds e.residue ↔ e.modulus ∣ (e.a : ℤ)^2-(e.c : ℤ)^2 := by
    change e.dual.modulus ∣ e.residue*(e.a : ℤ)+e.c ↔ _
    rw [dual_modulus]
    constructor
    · rintro ⟨t,ht⟩
      refine ⟨-(e.c : ℤ)*t-(e.a : ℤ)^2,?_⟩
      unfold residue modulus at *
      linear_combination -(e.c : ℤ)*ht
    · rintro ⟨t,ht⟩
      refine ⟨-(e.K : ℤ)*e.a*e.d*t-e.c,?_⟩
      unfold residue modulus at *
      linear_combination -(e.K : ℤ)*e.a*e.d*ht
  constructor
  · exact fun H => test.1 ((H _).1 hr)
  · intro H n
    have he := (holds_iff e.dual e.residue).1 (test.2 H)
    rw [dual_modulus] at he
    rw [holds_iff,holds_iff,dual_modulus]
    exact ⟨fun h => he.trans h,fun h => he.symm.trans h⟩

end Event
end GaloisForLFunctions.BezoutValuationIncidence.UnitFractions

#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.holds_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.progression
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.positive_fiber
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.intersection_nonempty
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.intersection_class
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.family_class
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.family_periods
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.inverse_residues
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.witness_coprime
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.dual_witness_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.self_dual_iff
