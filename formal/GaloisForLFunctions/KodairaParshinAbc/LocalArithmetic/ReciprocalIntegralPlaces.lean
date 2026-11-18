import GaloisForLFunctions.RHTower.Deninger.DeningerRationalDivisorSequence
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# The two inequalities defining rational S-integrality

With |p|ₚ = 1/p, the inequality in Ziegler (arXiv:2609.15487, §2)
selects the rationals with S-supported numerator. Ordinary S-integrality
selects those with S-supported denominator. The former set fails addition
even on positive elements, and generates all of ℚ additively.
-/

noncomputable section
namespace GaloisForLFunctions.KodairaParshinAbc
open _root_.RHTower
variable (S : Finset Nat.Primes)

/-- Rational elements integral at each unselected prime. -/
def rationalIntegralPlaces : Subring ℚ where
  carrier := {q | ∀ p : Nat.Primes, p ∉ S → padicNorm p.val q ≤ 1}
  zero_mem' _ _ := by simp
  one_mem' _ _ := by simp
  add_mem' := by
    intro x y hx hy p hp
    letI : Fact p.val.Prime := ⟨p.property⟩
    exact padicNorm.nonarchimedean.trans (max_le (hx p hp) (hy p hp))
  mul_mem' := by
    intro x y hx hy p hp
    letI : Fact p.val.Prime := ⟨p.property⟩
    rw [padicNorm.mul]
    exact mul_le_one₀ (hx p hp) (padicNorm.nonneg _) (hy p hp)
  neg_mem' := by
    intro x hx p hp
    rw [padicNorm.neg]
    exact hx p hp

/-- Rational elements satisfying the reversed nonarchimedean inequalities. -/
def reciprocalIntegralPlaces : Set ℚ := {q | ∀ p : Nat.Primes, p ∉ S → 1 ≤ padicNorm p.val q}

private theorem norm_le_one_iff (p : Nat.Primes) (q : ℚ) :
    padicNorm p.val q ≤ 1 ↔ ¬ p.val ∣ q.den := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hpos : 0 < padicNorm p.val (q.den:ℚ) :=
    (padicNorm.nonneg _).lt_of_ne' (padicNorm.nonzero (Nat.cast_ne_zero.mpr q.den_nz))
  nth_rw 1 [← q.num_div_den, padicNorm.div, div_le_one hpos]
  by_cases hd : p.val ∣ q.den
  · have hn : ¬(p.val:ℤ) ∣ q.num := by
      intro h
      exact Nat.not_coprime_of_dvd_of_dvd p.property.one_lt hd (Int.natCast_dvd.mp h) q.reduced.symm
    rw [(padicNorm.int_eq_one_iff _).2 hn, iff_false_intro (not_not.mpr hd)]
    exact iff_false_intro (not_le_of_gt ((padicNorm.nat_lt_one_iff _).2 hd))
  · rw [(padicNorm.nat_eq_one_iff _).2 hd]
    exact iff_of_true (padicNorm.of_int _) hd

/-- Ordinary rational S-integers are exactly the fractions with S-supported denominator. -/
theorem rationalIntegralPlaces_denominator (q : ℚ) :
    q ∈ rationalIntegralPlaces S ↔ ∀ p : Nat.Primes, p.val ∣ q.den → p ∈ S := by
  change (∀ p : Nat.Primes, p ∉ S → padicNorm p.val q ≤ 1) ↔ _
  simp_rw [norm_le_one_iff]
  constructor <;> intro h p hp
  · by_contra hs
    exact h p hs hp
  · exact fun hd => hp (h p hd)

/-- Inversion identifies the reversed locus with the nonzero ordinary S-integers. -/
theorem reciprocalIntegralPlaces_inv (q : ℚ) :
    q ∈ reciprocalIntegralPlaces S ↔ q ≠ 0 ∧ q⁻¹ ∈ rationalIntegralPlaces S := by
  have equivalence (hq : q ≠ 0) (p : Nat.Primes) :
      1 ≤ padicNorm p.val q ↔ padicNorm p.val q⁻¹ ≤ 1 := by
    letI : Fact p.val.Prime := ⟨p.property⟩
    have hpos := (padicNorm.nonneg (p := p.val) q).lt_of_ne' (padicNorm.nonzero hq)
    rw [← one_div, padicNorm.div, padicNorm.one, div_le_one hpos]
  constructor
  · intro h
    have hq : q ≠ 0 := by
      rintro rfl
      obtain ⟨p,hp⟩ := Infinite.exists_notMem_finset S
      have hz : (1:ℚ) ≤ 0 := by simpa only [padicNorm.zero] using h p hp
      exact (not_le_of_gt zero_lt_one) hz
    exact ⟨hq,fun p hp => (equivalence hq p).1 (h p hp)⟩
  · exact fun ⟨hq,h⟩ p hp => (equivalence hq p).2 (h p hp)

/-- The printed inequality characterizes S-supported reduced numerators. -/
theorem reciprocalIntegralPlaces_numerator (q : ℚ) :
    q ∈ reciprocalIntegralPlaces S ↔ q ≠ 0 ∧
      ∀ p : Nat.Primes, p.val ∣ q.num.natAbs → p ∈ S := by
  rw [reciprocalIntegralPlaces_inv,rationalIntegralPlaces_denominator]
  exact and_congr_right fun hq => by rw [Rat.den_inv_of_ne_zero hq]

/-- The positive overlap of the two loci is precisely the corpus S-unit subgroup. -/
theorem integral_reciprocal_intersection (u : ℚˣ) :
    u ∈ deningerSUnits S ↔ 0 < (u:ℚ) ∧ (u:ℚ) ∈ rationalIntegralPlaces S ∧
      (u:ℚ) ∈ reciprocalIntegralPlaces S := by
  change (0 < (u:ℚ) ∧ ∀ p : Nat.Primes, p ∉ S → padicValRat p.val (u:ℚ) = 0) ↔ _
  apply and_congr_right
  intro _
  have h (p : Nat.Primes) : padicNorm p.val (u:ℚ) = 1 ↔ padicValRat p.val (u:ℚ) = 0 := by
    rw [padicNorm.eq_zpow_of_nonzero u.ne_zero, ← zpow_zero (p.val:ℚ),
      (zpow_right_strictMono₀ (by exact_mod_cast p.property.one_lt : (1:ℚ)<p.val)).injective.eq_iff,
      neg_eq_zero]
  constructor
  · intro H
    exact ⟨fun p hp => ((h p).2 (H p hp)).le, fun p hp => ((h p).2 (H p hp)).ge⟩
  · exact fun ⟨h₁,h₂⟩ p hp => (h p).1 (le_antisymm (h₁ p hp) (h₂ p hp))

private theorem reciprocal_nat (n : ℕ) (hn : n ≠ 0) :
    (n:ℚ)⁻¹ ∈ reciprocalIntegralPlaces S := by
  rw [reciprocalIntegralPlaces_inv,inv_inv]
  refine ⟨inv_ne_zero (Nat.cast_ne_zero.mpr hn),?_⟩
  intro p _
  letI : Fact p.val.Prime := ⟨p.property⟩
  simpa only [Int.cast_natCast] using padicNorm.of_int (p := p.val) (n:ℤ)

/-- For every omitted prime p, the positive summands 1 and 1/(p-1) belong to the printed
locus but their sum does not. -/
theorem reciprocalIntegralPlaces_positive_add_fails (p : Nat.Primes) (hp : p ∉ S) :
    let x : ℚ := ((p.val-1:ℕ):ℚ)⁻¹
    0 < x ∧ x ∈ reciprocalIntegralPlaces S ∧ 1 ∈ reciprocalIntegralPlaces S ∧
      1+x ∉ reciprocalIntegralPlaces S := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hn : 0 < p.val-1 := Nat.sub_pos_of_lt p.property.one_lt
  have hne : ((p.val-1:ℕ):ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  refine ⟨inv_pos.mpr (by exact_mod_cast hn),reciprocal_nat S _ hn.ne',
    fun _ _ => padicNorm.one.ge,?_⟩
  intro h
  have ha := h p hp
  have he : 1 + ((p.val-1:ℕ):ℚ)⁻¹ = (p.val:ℚ)/((p.val-1:ℕ):ℚ) := by
    field_simp [hne]
    rw [Nat.cast_sub p.property.one_le]
    push_cast
    ring
  have hnd : ¬ p.val ∣ p.val-1 := fun h => (Nat.not_le_of_lt (Nat.sub_lt p.property.pos Nat.zero_lt_one))
    (Nat.le_of_dvd hn h)
  rw [he,padicNorm.div,(padicNorm.nat_eq_one_iff _).2 hnd,div_one] at ha
  exact (not_lt_of_ge ha) ((padicNorm.nat_lt_one_iff _).2 dvd_rfl)

/-- Closing the printed locus under addition and subtraction recovers the entire rational field. -/
theorem reciprocalIntegralPlaces_additiveClosure :
    AddSubgroup.closure (reciprocalIntegralPlaces S) = ⊤ := by
  apply top_unique
  intro q _
  have h := AddSubgroup.subset_closure (reciprocal_nat S q.den q.den_nz)
  have hz := (AddSubgroup.closure (reciprocalIntegralPlaces S)).zsmul_mem h q.num
  simpa only [zsmul_eq_mul,← div_eq_mul_inv,Rat.num_div_den] using hz

#print axioms rationalIntegralPlaces_denominator
#print axioms reciprocalIntegralPlaces_inv
#print axioms reciprocalIntegralPlaces_numerator
#print axioms integral_reciprocal_intersection
#print axioms reciprocalIntegralPlaces_positive_add_fails
#print axioms reciprocalIntegralPlaces_additiveClosure
end GaloisForLFunctions.KodairaParshinAbc
