import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldOddGaussEvaluation
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldNormCharacters
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticGaussLift

/-!
# Semiprimitive Gauss sums at every extension level

Odd levels follow from the trace-zero line in the quadratic extension
over the middle fixed field. At an even level the character descends
through the middle-field norm. Quadratic lifting squares the lower-level
sum and introduces a minus sign. The norm of the original trace-zero
constant is its square, so the character factor descends compatibly.
-/

universe u
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (p : ℕ) [Fact p.Prime]

private theorem even_add_one_dvd_pow_sub_one (q t : ℕ) (hq : 0 < q) (ht : Even t) :
    q + 1 ∣ q ^ t - 1 := by
  have hpow : 1 ≤ q ^ t := Nat.one_le_pow t q hq
  have hi : ((q + 1 : ℕ) : ℤ) ∣ ((q ^ t - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one]
    simpa only [sub_neg_eq_add, ht.neg_one_pow] using
      sub_dvd_pow_sub_pow (q : ℤ) (-1) t
  exact_mod_cast hi

/-- A semiprimitive character has the exact signed Gauss value at every finite extension level. -/
theorem finiteField_semiprimitive_gauss (h t : ℕ) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    ∀ (E : Type u) [Field E] [Fintype E] [CharP E p] [Algebra (ZMod p) E],
      Module.finrank (ZMod p) E = 2 * (h * t) →
      ∀ (χ : MulChar E ℂ), χ ≠ 1 → χ ^ (p ^ h + 1) = 1 →
      ∀ (η : E), η ≠ 0 → η ^ p ^ h = -η →
      gaussSum χ (finiteFieldTraceCharacter (L := E) ψ) =
        (-1 : ℂ) ^ (t + 1) * (p : ℂ) ^ (h * t) * χ η := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro E _ _ _ _ hdegree χ hχ horder η hη0 hη
    have htpos : 0 < t := by
      by_contra hn
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos hn
      rw [ht0, Nat.mul_zero, Nat.mul_zero] at hdegree
      have hpos : 0 < Module.finrank (ZMod p) E := Module.finrank_pos
      omega
    rcases Nat.even_or_odd t with hteven | htodd
    · obtain ⟨a, ha⟩ := hteven
      have hat : a < t := by omega
      let F := frobeniusFixedSubfield p E (h * t)
      letI : Fintype F := Fintype.ofFinite _
      letI : Algebra (ZMod p) F := ZMod.algebra F p
      letI : @IsScalarTower (ZMod p) F E
          Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
        @ZMod.instIsScalarTower p F E _ _ Algebra.toModule Algebra.toModule Algebra.toModule
      have htwo : Module.finrank F E = 2 :=
        finiteField_frobeniusFixedSubfield_finrank_two p E (h * t) hdegree
      have hcF : Nat.card F = p ^ (h * t) := by
        rw [frobeniusFixedSubfield_card, hdegree,
          Nat.gcd_eq_right (dvd_mul_left (h * t) 2)]
      have hFdegree : @Module.finrank (ZMod p) F _ _ Algebra.toModule = 2 * (h * a) := by
        -- Prime-field module structures are unique.
        rw [show (Algebra.toModule : Module (ZMod p) F) = (inferInstance : Module (ZMod p) F) from
          Subsingleton.elim _ _]
        rw [finiteField_middle_prime_finrank p E (h * t) hdegree, ha]
        ring
      have heven : Even t := ⟨a, ha⟩
      have hηfixed : η ^ p ^ (h * t) = η :=
        frobenius_negated_power_even p h t η hη heven
      let ηF : F := ⟨η, hηfixed⟩
      have hηF0 : ηF ≠ 0 := fun hz => hη0 (congrArg Subtype.val hz)
      have hηF : ηF ^ p ^ h = -ηF := Subtype.ext hη
      have hdiv : p ^ h + 1 ∣ p ^ (h * t) - 1 := by
        rw [pow_mul]
        exact even_add_one_dvd_pow_sub_one (p ^ h) t
          (pow_pos (Fact.out : p.Prime).pos h) heven
      have hdescend : χ ^ (Fintype.card F - 1) = 1 := by
        rw [← Nat.card_eq_fintype_card, hcF]
        obtain ⟨b, hb⟩ := hdiv
        rw [hb, pow_mul, horder, one_pow]
      obtain ⟨θ, hθpull, _⟩ := finiteField_existsUnique_norm_character (K := F) χ hdescend
      have hθ : θ ≠ 1 := by
        intro hz
        apply hχ
        rw [← hθpull, hz, finiteFieldNormCharacter_one]
      have hθorder : θ ^ (p ^ h + 1) = 1 := by
        apply finiteFieldNormCharacter_injective (L := E)
        rw [finiteFieldNormCharacter_pow, hθpull, horder, finiteFieldNormCharacter_one]
      have hnorm : Algebra.norm F η = ηF ^ 2 := by
        apply (algebraMap F E).injective
        rw [finiteField_quadratic_norm htwo, hcF]
        change η * η ^ p ^ (h * t) = η ^ 2
        rw [hηfixed, pow_two]
      have hχη : χ η = θ ηF ^ 2 := by
        calc
          χ η = θ (Algebra.norm F η) := (DFunLike.congr_fun hθpull η).symm
          _ = θ ηF ^ 2 := by rw [hnorm, map_pow]
      have hsmall := ih a hat F hFdegree θ hθ hθorder ηF hηF0 hηF
      have hlift : gaussSum χ (finiteFieldTraceCharacter (L := E) ψ) =
          -((gaussSum θ (finiteFieldTraceCharacter (L := F) ψ)) ^ 2) := by
        rw [← hθpull, ← finiteFieldTraceCharacter_tower (L := F) (M := E) ψ]
        exact finiteField_quadratic_gauss_lift htwo θ
          (finiteFieldTraceCharacter (L := F) ψ)
          (Or.inr ((finiteFieldTraceCharacter_ne_one_iff ψ).mpr hψ))
      have hsign : ((-1 : ℂ) ^ (a + 1)) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm (a + 1) 2, pow_mul]
        simp only [neg_one_sq, one_pow]
      have hexp : (h * a) * 2 = h * t := by rw [ha]; ring
      calc
        _ = -(((-1 : ℂ) ^ (a + 1) * (p : ℂ) ^ (h * a) * θ ηF) ^ 2) := by
          rw [hlift, hsmall]
        _ = -((p : ℂ) ^ (h * t) * χ η) := by
          rw [mul_pow, mul_pow, hsign, one_mul, ← pow_mul, hexp, ← hχη]
        _ = _ := by
          rw [pow_succ, heven.neg_one_pow, one_mul, neg_one_mul, neg_mul]
    · rw [finiteField_odd_semiprimitive_gauss p E h t htodd hdegree χ hχ horder ψ hψ η hη0 hη]
      rw [pow_succ, htodd.neg_one_pow, neg_mul_neg, one_mul, one_mul]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
