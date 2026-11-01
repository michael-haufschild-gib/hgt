import GaloisForLFunctions.RHTower.QuasiRHSubfieldMoment
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Integer intervals in quadratic prime fields

An interval of integer shifts lies in the prime subfield. Sextic characters
trivial on that subfield retain a fourth-moment excess of cube-root-prime
size, even when the interval has at most cube-root-field cardinality.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset RHTower.QuasiRHShiftCorrelation
open scoped Classical

/-- The literal interval of the first `B` nonnegative integers in a field. -/
def integerShiftInterval (K : Type*) [Field K] (B : ℕ) : Finset K :=
  (range B).image (fun n : ℕ => (n : K))

private theorem interval_card {p B : ℕ} [Fact p.Prime] (hB : B ≤ p) :
    (integerShiftInterval (ZMod p) B).card = B := by
  letI : DecidableEq (ZMod p) := fun a b => Classical.propDecidable (a = b)
  have hi : Set.InjOn (fun a : ℕ => (a : ZMod p)) (range B) := by
    intro a ha b hb hab
    have ha' : a < p := (mem_range.mp ha).trans_le hB
    have hb' : b < p := (mem_range.mp hb).trans_le hB
    simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using
      congrArg ZMod.val hab
  simpa only [integerShiftInterval, card_range] using card_image_of_injOn hi

private theorem interval_image {p B : ℕ} [Fact p.Prime]
    (K : Type*) [Field K] [Algebra (ZMod p) K] :
    (integerShiftInterval (ZMod p) B).image (algebraMap (ZMod p) K) =
      integerShiftInterval K B := by
  classical
  simp only [integerShiftInterval, image_image, Function.comp_def, map_natCast]

private theorem interval_moment_scale {p t : ℝ} (ht : 0 ≤ t)
    (hhalf : 2 * t ^ 2 ≤ p) (hupper : p ≤ 8 * t ^ 3) :
    t * p ^ 2 * (t ^ 2) ^ 2 ≤ 16 * ((p - t ^ 2) * (t ^ 2) ^ 4) := by
  have hp : 0 ≤ p := le_trans (by positivity) hhalf
  have htp : t * p ≤ 8 * t ^ 4 := by
    nlinarith only [mul_le_mul_of_nonneg_left hupper ht]
  calc
    _ = (t * p) * (p * t ^ 4) := by ring
    _ ≤ (8 * t ^ 4) * (p * t ^ 4) :=
      mul_le_mul_of_nonneg_right htp (by positivity)
    _ = 8 * p * (t ^ 2) ^ 4 := by ring
    _ ≤ 16 * ((p - t ^ 2) * (t ^ 2) ^ 4) := by
      nlinarith only [mul_le_mul_of_nonneg_right hhalf (sq_nonneg ((t ^ 2) ^ 2))]

/-- Arbitrarily large prime-field intervals retain a power-sized sextic moment excess.
The scale relations imply `B³ ≤ |K|` and `t ≍ |K|^(1/6)`. -/
theorem exists_integerInterval_sextic_moment_excess (n : ℕ) :
    ∃ (p t : ℕ) (K : Type) (_ : Field K) (_ : Fintype K)
      (χ : MulChar K ℂ),
      p.Prime ∧ p % 6 = 5 ∧ n < t ∧ 2 ≤ t ∧
      t ^ 3 ≤ p ∧ p < (t + 1) ^ 3 ∧
      Fintype.card K = p ^ 2 ∧ orderOf χ = 6 ∧
      (integerShiftInterval K (t ^ 2)).card = t ^ 2 ∧
      (integerShiftInterval K (t ^ 2)).card ^ 3 ≤ Fintype.card K ∧
      (t : ℝ) * (Fintype.card K : ℝ) *
          ((integerShiftInterval K (t ^ 2)).card : ℝ) ^ 2 ≤
        16 * shiftFourthMoment χ (integerShiftInterval K (t ^ 2)) := by
  obtain ⟨p, hpbig, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    ((n + 2) ^ 3) (q := 6) (a := 5) (by norm_num) (by norm_num)
  letI : Fact p.Prime := ⟨hp⟩
  let t := Nat.nthRoot 3 p
  have ht : n + 2 ≤ t := (Nat.le_nthRoot_iff (by norm_num)).mpr hpbig.le
  have ht2 : 2 ≤ t := by omega
  have hlow : t ^ 3 ≤ p := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hupp : p < (t + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by norm_num) p
  have hhalf : 2 * t ^ 2 ≤ p := calc
    _ ≤ t * t ^ 2 := Nat.mul_le_mul_right _ ht2
    _ = t ^ 3 := by ring
    _ ≤ p := hlow
  have hB : t ^ 2 ≤ p := by omega
  have hupper : p ≤ 8 * t ^ 3 := calc
    p ≤ (t + 1) ^ 3 := hupp.le
    _ ≤ (2 * t) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    _ = _ := by ring
  let K := FiniteField.Extension (ZMod p) p 2
  letI : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = Nat.card (ZMod p) ^ 2 :=
    FiniteField.natCard_extension (ZMod p) p 2
  have hK' : Fintype.card K = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, hK, Nat.card_zmod]
  have hmod : 6 ∣ Nat.card (ZMod p) + 1 := by
    rw [Nat.card_zmod]
    apply Nat.dvd_of_mod_eq_zero
    have hm : p % 6 = 5 := hpmod
    omega
  obtain ⟨χ, horder, hrestrict⟩ := exists_sextic_quadratic_character hK hmod
  have hcard : (integerShiftInterval K (t ^ 2)).card = t ^ 2 := by
    rw [← interval_image (p := p) K,
      card_image_of_injective _ (algebraMap (ZMod p) K).injective]
    exact interval_card hB
  refine ⟨p, t, K, inferInstance, inferInstance, χ, hp, hpmod, by omega,
    ht2, hlow, hupp, hK', horder, hcard, ?_, ?_⟩
  · rw [hcard, hK']
    calc
      (t ^ 2) ^ 3 = (t ^ 3) ^ 2 := by ring
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hlow 2
  · have hlocal := subfield_shiftFourthMoment_lower χ hrestrict
      (integerShiftInterval (ZMod p) (t ^ 2))
    rw [interval_image (p := p) K, interval_card hB, ZMod.card] at hlocal
    have hscale := interval_moment_scale (t := (t : ℝ)) (p := (p : ℝ))
      (Nat.cast_nonneg _) (by exact_mod_cast hhalf) (by exact_mod_cast hupper)
    rw [hK', hcard]
    push_cast
    calc
      _ ≤ 16 * (((p : ℝ) - (t : ℝ) ^ 2) * ((t : ℝ) ^ 2) ^ 4) := hscale
      _ ≤ 16 * shiftFourthMoment χ (integerShiftInterval K (t ^ 2)) := by
        push_cast at hlocal
        have hpos : 0 ≤ (t : ℝ) ^ 2 * ((t : ℝ) ^ 2 - 1) ^ 4 := by positivity
        linarith only [hlocal, hpos]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
