import GaloisForLFunctions.RHTower.Deninger.DeningerFinitePrecisionSelector

/-!
# Exact correction of finitely many denominator parities

Multiplying by a squarefree prime product toggles denominator parity only
at poles. Consequently the primes of negative odd valuation are forced
into every correcting product; primes of negative even valuation are
forbidden, and integral primes are free. This gives both a finite
square-denominator test away from a prescribed set and its least correction.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry.Arithmetic
open scoped Classical

/-- Square-denominator parity is required only outside the finite set. -/
def DeningerSquareDenominatorAway (S : Finset Nat.Primes) (q : ℚ) : Prop :=
  ∀ p : Nat.Primes, p ∉ S → 0 ≤ padicValRat (p : ℕ) q ∨ Even (padicValRat (p : ℕ) q)

/-- The forced correcting primes: negative odd valuations inside `S`. -/
noncomputable def deningerNegativeOddPrimes (S : Finset Nat.Primes) (q : ℚ) : Finset Nat.Primes :=
  S.filter (fun p => padicValRat (p : ℕ) q < 0 ∧ ¬ Even (padicValRat (p : ℕ) q))

/-- A squarefree multiplier corrects precisely the odd poles and must
avoid every even pole. Its behavior at integral primes is unrestricted. -/
theorem deninger_squareDenominator_product_iff (T : Finset Nat.Primes) (q : ℚ) :
    SquareDenominator (deningerPrecisionParameter T * q) ↔
      ∀ p : Nat.Primes, padicValRat (p : ℕ) q < 0 →
        (p ∈ T ↔ ¬ Even (padicValRat (p : ℕ) q)) := by
  by_cases hq : q = 0
  · subst q
    simp [squareDenominator_zero]
  rw [squareDenominator_iff]
  constructor
  · intro h p hpneg
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hv := h (p : ℕ) p.2
    rw [padicValRat.mul (deningerPrecisionParameter_pos T).ne' hq] at hv
    by_cases hmem : p ∈ T
    · have hR : padicValRat (p : ℕ) (deningerPrecisionParameter T) = 1 :=
        (deningerPrecisionParameter_val T p).trans (if_pos hmem)
      rw [hR] at hv
      have hodd : ¬ Even (padicValRat (p : ℕ) q) := by
        rw [Int.even_iff] at hv ⊢
        omega
      exact ⟨fun _ => hodd, fun _ => hmem⟩
    · have hR : padicValRat (p : ℕ) (deningerPrecisionParameter T) = 0 :=
        (deningerPrecisionParameter_val T p).trans (if_neg hmem)
      rw [hR, zero_add] at hv
      have heven := hv.resolve_left (not_le_of_gt hpneg)
      exact ⟨fun hm => (hmem hm).elim, fun ho => (ho heven).elim⟩
  · intro h p hp
    letI : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.mul (deningerPrecisionParameter_pos T).ne' hq]
    by_cases hv : 0 ≤ padicValRat p q
    · left
      have hR : 0 ≤ padicValRat p (deningerPrecisionParameter T) := by
        rw [deningerPrecisionParameter_val T ⟨p, hp⟩]
        split_ifs <;> norm_num
      exact add_nonneg hR hv
    · right
      have heq := h ⟨p, hp⟩ (lt_of_not_ge hv)
      by_cases hmem : (⟨p, hp⟩ : Nat.Primes) ∈ T
      · have hR : padicValRat p (deningerPrecisionParameter T) = 1 :=
          (deningerPrecisionParameter_val T ⟨p, hp⟩).trans (if_pos hmem)
        rw [hR]
        have hodd : ¬ Even (padicValRat p q) := heq.mp hmem
        rw [Int.even_iff] at hodd ⊢
        omega
      · have hR : padicValRat p (deningerPrecisionParameter T) = 0 :=
          (deningerPrecisionParameter_val T ⟨p, hp⟩).trans (if_neg hmem)
        rw [hR, zero_add]
        by_contra hodd
        exact hmem (heq.mpr hodd)

/-- The canonical correction succeeds exactly when all unlisted primes
already have admissible denominator parity. -/
theorem deninger_canonical_correction_iff (S : Finset Nat.Primes) (q : ℚ) :
    SquareDenominator (deningerPrecisionParameter (deningerNegativeOddPrimes S q) * q) ↔
      DeningerSquareDenominatorAway S q := by
  rw [deninger_squareDenominator_product_iff]
  constructor
  · intro h p hp
    by_cases hv : 0 ≤ padicValRat (p : ℕ) q
    · exact Or.inl hv
    right
    by_contra he
    have hmem := (h p (lt_of_not_ge hv)).mpr he
    exact hp (Finset.mem_filter.mp hmem).1
  · intro h p hpneg
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2.2
    · intro hpodd
      apply Finset.mem_filter.mpr
      refine ⟨?_, hpneg, hpodd⟩
      by_contra hp
      rcases h p hp with hv | he
      · omega
      · exact hpodd he

/-- Allowing the finitely many squarefree subproducts of `S` removes
exactly the denominator restrictions at the primes in `S`. -/
theorem deninger_finite_squareDenominator_saturation (S : Finset Nat.Primes) (q : ℚ) :
    (∃ T : Finset Nat.Primes, T ⊆ S ∧ SquareDenominator (deningerPrecisionParameter T * q)) ↔
      DeningerSquareDenominatorAway S q := by
  constructor
  · rintro ⟨T, hTS, hT⟩ p hp
    by_cases hv : 0 ≤ padicValRat (p : ℕ) q
    · exact Or.inl hv
    right
    by_contra he
    have hmem := ((deninger_squareDenominator_product_iff T q).mp hT p
      (lt_of_not_ge hv)).mpr he
    exact hp (hTS hmem)
  · intro h
    exact ⟨deningerNegativeOddPrimes S q, Finset.filter_subset _ _,
      (deninger_canonical_correction_iff S q).mpr h⟩

/-- Every correction contains the canonical set of forced primes. -/
theorem deninger_canonical_correction_minimal (S T : Finset Nat.Primes) (q : ℚ)
    (hT : SquareDenominator (deningerPrecisionParameter T * q)) :
    deningerNegativeOddPrimes S q ⊆ T := by
  intro p hp
  obtain ⟨_, hpneg, hpodd⟩ := Finset.mem_filter.mp hp
  exact ((deninger_squareDenominator_product_iff T q).mp hT p hpneg).mpr hpodd

#print axioms deninger_squareDenominator_product_iff
#print axioms deninger_finite_squareDenominator_saturation
#print axioms deninger_canonical_correction_minimal

end RHTower
