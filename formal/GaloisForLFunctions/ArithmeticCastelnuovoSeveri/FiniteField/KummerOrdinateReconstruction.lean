import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerZeroFibers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerTraceBalance

/-!
# Recovering Kummer ordinate parameters

A Frobenius-fixed branch value gives a multiplicative balance between the
branch factor and its conjugate. Their difference reconstructs a trace-one
parameter; the complementary-parameter identity recovers its scalar.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Multiplicative branch balance passes to the complementary conjugate ratios. -/
theorem conjugate_ratio_power_balance {K : Type*} [Field K] (A B y y' : K) (R : ℕ)
    (h : (-1) ^ R * y' * B ^ R = y * A ^ R) :
    y' * (-B / (A - B)) ^ R = y * (A / (A - B)) ^ R := by
  simp only [div_eq_mul_inv]
  calc
    _ = ((-1) ^ R * y' * B ^ R) * ((A - B) ^ R)⁻¹ := by ring
    _ = _ := by rw [h]; ring

variable (p : ℕ) [Fact p.Prime]

/-- A soluble norm fiber gives the conjugate branch-factor equation. -/
theorem normalizedKummerBranch_fixed_equation (s d r : ℕ) (y : SquareConstantField p s)
    (hy : ((normalizedKummerBranch p s d r).eval y) ^ p ^ (s + 1) =
      (normalizedKummerBranch p s d r).eval y) :
    (-1) ^ kummerExponent (p ^ (d + 1)) (r + 1) * y ^ p ^ (s + 1) *
        ((1 - y ^ (p ^ (d + 1) - 1)) ^ p ^ (s + 1)) ^
          kummerExponent (p ^ (d + 1)) (r + 1) =
      y * (1 - y ^ (p ^ (d + 1) - 1)) ^ kummerExponent (p ^ (d + 1)) (r + 1) := by
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  let c := ((kummerTraceConstant p s : SquareConstantField p s)⁻¹) ^ R
  have hc : c ^ p ^ (s + 1) = (-1) ^ R * c := by
    dsimp only [c]
    rw [← pow_mul, Nat.mul_comm R (p ^ (s + 1)), pow_mul, inv_pow,
      kummerTraceConstant_frobenius, inv_neg, neg_pow]
  have hA : ((1 - y ^ (p ^ (d + 1) - 1)) ^ R) ^ p ^ (s + 1) =
      ((1 - y ^ (p ^ (d + 1) - 1)) ^ p ^ (s + 1)) ^ R := by
    rw [← pow_mul, Nat.mul_comm R (p ^ (s + 1)), pow_mul]
  rw [normalizedKummerBranch_eval, mul_pow, mul_pow, hc, hA] at hy
  apply mul_left_cancel₀ (pow_ne_zero R (inv_ne_zero (Units.ne_zero (kummerTraceConstant p s))))
  change c * _ = c * _
  calc
    _ = ((-1) ^ R * c) * y ^ p ^ (s + 1) *
        ((1 - y ^ (p ^ (d + 1) - 1)) ^ p ^ (s + 1)) ^ R := by ring
    _ = c * y * (1 - y ^ (p ^ (d + 1) - 1)) ^ R := hy
    _ = _ := by ring

/-- The conjugate ratio used to recover a trace-one parameter. -/
def squareConjugateRatio (s : ℕ) (a : SquareConstantField p s) : SquareConstantField p s :=
  -(a ^ p ^ (s + 1)) / (a - a ^ p ^ (s + 1))

/-- Frobenius exchanges the conjugate numerator for the original numerator. -/
theorem squareConjugateRatio_frobenius (s : ℕ) (a : SquareConstantField p s) :
    (squareConjugateRatio p s a) ^ p ^ (s + 1) = a / (a - a ^ p ^ (s + 1)) := by
  have hn : (-(a ^ p ^ (s + 1))) ^ p ^ (s + 1) = -a := by
    simpa only [iterateFrobenius_def, squareConstantField_frobenius_sq] using
      map_neg (iterateFrobenius (SquareConstantField p s) p (s + 1)) (a ^ p ^ (s + 1))
  have hd : (a - a ^ p ^ (s + 1)) ^ p ^ (s + 1) = -(a - a ^ p ^ (s + 1)) := by
    rw [sub_pow_char_pow, squareConstantField_frobenius_sq]
    ring
  rw [squareConjugateRatio, div_pow, hn, hd, neg_div_neg_eq]

/-- A nonfixed branch factor supplies a trace-one parameter. -/
theorem squareConjugateRatio_trace_one (s : ℕ) (a : SquareConstantField p s)
    (ha : a ^ p ^ (s + 1) ≠ a) :
    (squareConjugateRatio p s a) ^ p ^ (s + 1) + squareConjugateRatio p s a = 1 := by
  rw [squareConjugateRatio_frobenius, squareConjugateRatio]
  field_simp [sub_ne_zero.mpr (Ne.symm ha)]
  ring

/-- The recovered parameter balances a branch factor against its conjugate. -/
theorem squareConjugateRatio_balance (s : ℕ) (a : SquareConstantField p s)
    (ha : a ^ p ^ (s + 1) ≠ a) :
    squareConjugateRatio p s a * a + (1 - squareConjugateRatio p s a) * a ^ p ^ (s + 1) = 0 := by
  rw [squareConjugateRatio]
  field_simp [sub_ne_zero.mpr (Ne.symm ha)]
  ring

/-- A nonzero nonfixed factor gives a nonzero recovered parameter. -/
theorem squareConjugateRatio_ne_zero (s : ℕ) (a : SquareConstantField p s)
    (ha0 : a ≠ 0) (ha : a ^ p ^ (s + 1) ≠ a) : squareConjugateRatio p s a ≠ 0 := by
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ha0)) (sub_ne_zero.mpr (Ne.symm ha))

/-- Dividing by the recovered trace power leaves a scalar fixed by middle Frobenius. -/
theorem normalizedKummer_reconstructed_scalar_fixed (s d r : ℕ) (y : SquareConstantField p s)
    (hy : ((normalizedKummerBranch p s d r).eval y) ^ p ^ (s + 1) =
      (normalizedKummerBranch p s d r).eval y)
    (hA : (1 - y ^ (p ^ (d + 1) - 1)) ^ p ^ (s + 1) ≠ 1 - y ^ (p ^ (d + 1) - 1)) :
    (y / (squareConjugateRatio p s (1 - y ^ (p ^ (d + 1) - 1))) ^
      kummerExponent (p ^ (d + 1)) (r + 1)) ^ p ^ (s + 1) =
    y / (squareConjugateRatio p s (1 - y ^ (p ^ (d + 1) - 1))) ^
      kummerExponent (p ^ (d + 1)) (r + 1) := by
  let A := 1 - y ^ (p ^ (d + 1) - 1)
  let u := squareConjugateRatio p s A
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  have hA0 : A ≠ 0 := by
    intro hz
    apply hA
    change A ^ p ^ (s + 1) = A
    rw [hz, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  have hu0 := squareConjugateRatio_ne_zero p s A hA0 hA
  have he := normalizedKummerBranch_fixed_equation p s d r y hy
  change (-1) ^ R * y ^ p ^ (s + 1) * (A ^ p ^ (s + 1)) ^ R = y * A ^ R at he
  have hcross : y ^ p ^ (s + 1) * u ^ R = y * (u ^ p ^ (s + 1)) ^ R := by
    change y ^ p ^ (s + 1) * (squareConjugateRatio p s A) ^ R =
      y * ((squareConjugateRatio p s A) ^ p ^ (s + 1)) ^ R
    rw [squareConjugateRatio_frobenius, squareConjugateRatio]
    exact conjugate_ratio_power_balance A (A ^ p ^ (s + 1)) y (y ^ p ^ (s + 1)) R he
  have hpow : (u ^ R) ^ p ^ (s + 1) = (u ^ p ^ (s + 1)) ^ R := by
    rw [← pow_mul, Nat.mul_comm R (p ^ (s + 1)), pow_mul]
  change (y / u ^ R) ^ p ^ (s + 1) = y / u ^ R
  rw [div_pow, hpow]
  exact (div_eq_div_iff (pow_ne_zero R (pow_ne_zero _ hu0)) (pow_ne_zero R hu0)).mpr hcross

/-- Every nonzero soluble ordinate belongs to one of the two explicit constructions. -/
theorem kummerConstructedOrdinate_surjective_on_nonzero_fixed (s d r : ℕ)
    (y : SquareConstantField p s) (hnon : y ^ p ^ (d + 1) ≠ y)
    (hy : ((normalizedKummerBranch p s d r).eval y) ^ p ^ (s + 1) =
      (normalizedKummerBranch p s d r).eval y) :
    ∃ i : KummerOrdinateParameters p s d r, kummerConstructedOrdinate p s d r i = y := by
  let A := 1 - y ^ (p ^ (d + 1) - 1)
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  have hy0 : y ≠ 0 := by
    intro hz
    apply hnon
    rw [hz, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  have hA0 : A ≠ 0 := by
    intro hz
    have he : y ^ (p ^ (d + 1) - 1) = 1 := (sub_eq_zero.mp hz).symm
    apply hnon
    rw [← Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos), pow_succ, he, one_mul]
  by_cases hA : A ^ p ^ (s + 1) = A
  · have he := normalizedKummerBranch_fixed_equation p s d r y hy
    change (-1) ^ R * y ^ p ^ (s + 1) * (A ^ p ^ (s + 1)) ^ R = y * A ^ R at he
    rw [hA] at he
    have hs := mul_right_cancel₀ (pow_ne_zero R hA0) he
    have hsign : y ^ p ^ (s + 1) = (-1) ^ R * y := by
      rcases neg_one_pow_eq_or (SquareConstantField p s) R with h | h
      · rw [h, one_mul] at hs ⊢
        exact hs
      · rw [h, neg_one_mul] at hs ⊢
        linear_combination -hs
    exact ⟨Sum.inr ⟨y, hsign, hnon⟩, rfl⟩
  · let u := squareConjugateRatio p s A
    let a := y / u ^ R
    have hu0 := squareConjugateRatio_ne_zero p s A hA0 hA
    have htrace := squareConjugateRatio_trace_one p s A hA
    have huQ : u ^ p ^ (s + 1) = 1 - u := by
      linear_combination htrace
    have haQ : a ^ p ^ (s + 1) = a :=
      normalizedKummer_reconstructed_scalar_fixed p s d r y hy hA
    have ha0 : a ≠ 0 := div_ne_zero hy0 (pow_ne_zero R hu0)
    have hrep : a * u ^ R = y := div_mul_cancel₀ y (pow_ne_zero R hu0)
    have hrepQ : a * (1 - u) ^ R = y ^ p ^ (s + 1) := by
      have he := congrArg (fun z : SquareConstantField p s => z ^ p ^ (s + 1)) hrep
      rw [mul_pow, haQ] at he
      have hpow : (u ^ R) ^ p ^ (s + 1) = (u ^ p ^ (s + 1)) ^ R := by
        rw [← pow_mul, Nat.mul_comm R (p ^ (s + 1)), pow_mul]
      rwa [hpow, huQ] at he
    have hAr : A = 1 - (a * u ^ R) ^ (p ^ (d + 1) - 1) := by rw [hrep]
    have hArQ : A ^ p ^ (s + 1) = 1 - (a * (1 - u) ^ R) ^ (p ^ (d + 1) - 1) := by
      rw [hrepQ]
      change (1 - y ^ (p ^ (d + 1) - 1)) ^ p ^ (s + 1) = _
      rw [sub_pow_char_pow, one_pow]
      congr 1
      rw [← pow_mul, Nat.mul_comm (p ^ (d + 1) - 1) (p ^ (s + 1)), pow_mul]
    have hb := squareConjugateRatio_balance p s A hA
    change u * A + (1 - u) * A ^ p ^ (s + 1) = 0 at hb
    rw [hArQ, hAr, kummer_trace_balance] at hb
    have haroot : a ^ (p ^ (d + 1) - 1) = 1 := (sub_eq_zero.mp hb).symm
    have haux : u ^ (p ^ (d + 1)) ^ (r + 1) ≠ u := by
      intro huf
      have hR : R ≠ 0 := by
        rw [R, kummerExponent, geom_sum_succ]
        omega
      apply normalizedKummerBranch_ne_zero_of_not_fixed p s d r y hnon
      rw [← hrep, normalizedKummerBranch_eval_scale p s d r a _ haroot,
        normalizedKummerBranch_trace_substitution, huf, sub_self, zero_div, zero_pow hR, mul_zero]
    let aF : squareFrobeniusFixedField p s := ⟨a, haQ⟩
    have haF0 : aF ≠ 0 := by
      intro hz
      apply ha0
      exact congrArg (fun x : squareFrobeniusFixedField p s => (x : SquareConstantField p s)) hz
    let aU : (squareFrobeniusFixedField p s)ˣ := Units.mk0 aF haF0
    have haU : aU ^ (p ^ (d + 1) - 1) = 1 := by
      apply Units.ext
      apply Subtype.ext
      exact haroot
    let aS : KummerTraceScalars p s d :=
      ⟨aU, (mem_rootsOfUnity (p ^ (d + 1) - 1) aU).mpr haU⟩
    let uS : KummerTraceParameters p s d r := ⟨u, htrace, haux⟩
    refine ⟨Sum.inl (aS, uS), ?_⟩
    change a * u ^ R = y
    exact hrep

/-- Every constructed ordinate has a Frobenius-fixed branch value. -/
theorem kummerConstructedOrdinate_branch_fixed (s d r : ℕ) (i : KummerOrdinateParameters p s d r) :
    ((normalizedKummerBranch p s d r).eval (kummerConstructedOrdinate p s d r i)) ^ p ^ (s + 1) =
      (normalizedKummerBranch p s d r).eval (kummerConstructedOrdinate p s d r i) := by
  by_contra hf
  have hc := kummerConstructedOrdinate_fiber_card p s d r i
  rw [squareConstantField_norm_fiber_card,
    if_neg (kummerConstructedOrdinate_branch_ne_zero p s d r i), if_neg hf] at hc
  omega

/-- The two constructions classify exactly the nonzero soluble branch values. -/
theorem exists_kummerConstructedOrdinate_iff (s d r : ℕ) (y : SquareConstantField p s) :
    (∃ i : KummerOrdinateParameters p s d r, kummerConstructedOrdinate p s d r i = y) ↔
      (normalizedKummerBranch p s d r).eval y ≠ 0 ∧
        ((normalizedKummerBranch p s d r).eval y) ^ p ^ (s + 1) =
          (normalizedKummerBranch p s d r).eval y := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨kummerConstructedOrdinate_branch_ne_zero p s d r i,
      kummerConstructedOrdinate_branch_fixed p s d r i⟩
  · intro h
    exact kummerConstructedOrdinate_surjective_on_nonzero_fixed p s d r y
      (fun hy => h.1 ((normalizedKummerBranch_eq_zero_iff p s d r y).mpr hy)) h.2

/-- Every soluble affine fiber is a branch zero or belongs to one of the two explicit families. -/
theorem normalizedKummer_soluble_ordinate_iff (s d r : ℕ) (y : SquareConstantField p s) :
    (∃ z : SquareConstantField p s,
      z ^ (p ^ (s + 1) + 1) = (normalizedKummerBranch p s d r).eval y) ↔
      y ^ p ^ (d + 1) = y ∨
        ∃ i : KummerOrdinateParameters p s d r, kummerConstructedOrdinate p s d r i = y := by
  rw [squareConstantField_exists_norm_iff]
  constructor
  · intro hy
    by_cases hz : (normalizedKummerBranch p s d r).eval y = 0
    · exact Or.inl ((normalizedKummerBranch_eq_zero_iff p s d r y).mp hz)
    · exact Or.inr ((exists_kummerConstructedOrdinate_iff p s d r y).mpr ⟨hz, hy⟩)
  · rintro (hy | hy)
    · rw [(normalizedKummerBranch_eq_zero_iff p s d r y).mpr hy,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
    · exact ((exists_kummerConstructedOrdinate_iff p s d r y).mp hy).2

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
