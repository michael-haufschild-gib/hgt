import GaloisForLFunctions.BezoutValuationIncidence.Divisors.UnitFractionWitnessFibers
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.GCDMonoid.Finset

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

end Event
end GaloisForLFunctions.BezoutValuationIncidence.UnitFractions

#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.holds_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.progression
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.positive_fiber
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.intersection_nonempty
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.intersection_class
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.family_class
#print axioms GaloisForLFunctions.BezoutValuationIncidence.UnitFractions.Event.family_periods
