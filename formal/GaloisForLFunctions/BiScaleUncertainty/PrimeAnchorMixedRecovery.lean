import GaloisForLFunctions.BiScaleUncertainty.SieveArithmeticSourceAnchors
import GaloisForLFunctions.BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression

/-!
# Terminal-prime mixed observations

One full mixed quadratic row recovers active sieve coefficients up to global
sign when its anchor is nonzero. A prescribed negative arithmetic anchor fixes
that sign. The inverse estimate displays the loss as the anchor shrinks; the
zero-anchor fibre is an entire hyperplane.
-/

open Finset RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
noncomputable section
set_option autoImplicit false

def mixed (N p : ℕ) (c : ℕ → ℝ) (q : ℕ) : ℝ :=
  selbergMultiplesCoord N c p * selbergMultiplesCoord N c q

def error (N p : ℕ) (c b : ℕ → ℝ) (q : ℕ) : ℝ :=
  |mixed N p c q - mixed N p b q|

theorem coord_neg (N q : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (fun d => -c d) q = -selbergMultiplesCoord N c q := by
  simp only [selbergMultiplesCoord, neg_div, sum_neg_distrib]

theorem mixed_neg (N p q : ℕ) (c : ℕ → ℝ) :
    mixed N p (fun d => -c d) q = mixed N p c q := by
  simp only [mixed, coord_neg, neg_mul_neg]

/-- The zero observation fibre is exactly the anchor hyperplane. -/
theorem mixed_zero_iff {N p : ℕ} (hp : p ∈ Icc 1 N) (c : ℕ → ℝ) :
    (∀ q ∈ Icc 1 N, mixed N p c q = 0) ↔ selbergMultiplesCoord N c p = 0 := by
  constructor
  · intro h
    have hh := h p hp
    dsimp [mixed] at hh
    exact (mul_self_eq_zero.mp hh)
  · intro h q _
    simp [mixed, h]

/-- A live mixed row has exactly the two simultaneous-sign fibres. -/
theorem mixed_eq_iff {N p : ℕ} (hp : p ∈ Icc 1 N) (c b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b p ≠ 0) :
    (∀ q ∈ Icc 1 N, mixed N p c q = mixed N p b q) ↔
      (∀ d ∈ Icc 1 N, c d = b d) ∨ (∀ d ∈ Icc 1 N, c d = -b d) := by
  constructor
  · intro h
    have hs : selbergMultiplesCoord N c p ^ 2 = selbergMultiplesCoord N b p ^ 2 := by
      simpa only [mixed, pow_two] using h p hp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · left
      apply (sieve_active_coefficients_eq_iff N c b).mpr
      intro q hq
      have hh := h q hq
      dsimp [mixed] at hh
      rw [he] at hh
      exact mul_left_cancel₀ hb hh
    · right
      apply (sieve_active_coefficients_eq_iff N c (fun d => -b d)).mpr
      intro q hq
      rw [coord_neg]
      have hh := h q hq
      dsimp [mixed] at hh
      rw [he] at hh
      apply mul_left_cancel₀ hb
      nlinarith only [hh]
  · rintro (h | h) q hq
    · have he := (sieve_active_coefficients_eq_iff N c b).mp h
      simp only [mixed, he p hp, he q hq]
    · have he := (sieve_active_coefficients_eq_iff N c (fun d => -b d)).mp h
      simp only [mixed, he p hp, he q hq, coord_neg, neg_mul_neg]

/-- Known negative anchor phase removes the quadratic global sign ambiguity. -/
theorem mixed_eq_iff_of_negative {N p : ℕ} (hp : p ∈ Icc 1 N) (c b : ℕ → ℝ)
    (hc : selbergMultiplesCoord N c p < 0) (hb : selbergMultiplesCoord N b p < 0) :
    (∀ q ∈ Icc 1 N, mixed N p c q = mixed N p b q) ↔
      ∀ d ∈ Icc 1 N, c d = b d := by
  rw [mixed_eq_iff hp c b hb.ne]
  constructor
  · rintro (h | h)
    · exact h
    · have he := (sieve_active_coefficients_eq_iff N c (fun d => -b d)).mp h p hp
      rw [coord_neg] at he
      linarith
  · exact Or.inl

/-- A denominator-free inverse estimate, valid even on singular fibres. -/
theorem scalar_inverse (a b x y : ℝ) :
    |a| * |a + b| * |x - y| ≤
      |a + b| * |a * x - b * y| + |y| * |a ^ 2 - b ^ 2| := by
  have h : |a| * |x - y| ≤ |a * x - b * y| + |a - b| * |y| := by
    calc
      _ = |a * (x - y)| := (abs_mul _ _).symm
      _ = |(a * x - b * y) - (a - b) * y| := by congr 1; ring
      _ ≤ |a * x - b * y| + |(a - b) * y| := abs_sub _ _
      _ = _ := by rw [abs_mul]
  have hs : |a - b| * |a + b| = |a ^ 2 - b ^ 2| := by
    rw [← abs_mul]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg (a + b))
  nlinarith only [hm, congrArg (fun t : ℝ => t * |y|) hs]

theorem coordinate_inverse (N p q : ℕ) (c b : ℕ → ℝ) :
    |selbergMultiplesCoord N c p| *
        |selbergMultiplesCoord N c p + selbergMultiplesCoord N b p| *
        |selbergMultiplesCoord N c q - selbergMultiplesCoord N b q| ≤
      |selbergMultiplesCoord N c p + selbergMultiplesCoord N b p| * error N p c b q +
        |selbergMultiplesCoord N b q| * error N p c b p := by
  simpa only [error, mixed, pow_two] using scalar_inverse
    (selbergMultiplesCoord N c p) (selbergMultiplesCoord N b p)
    (selbergMultiplesCoord N c q) (selbergMultiplesCoord N b q)

/-- Literal Möbius tapers lie on the oriented branch whenever both prime tapers are positive. -/
theorem moebius_mixed_eq_iff {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (w v : ℕ → ℝ) (hw : 0 < w p) (hv : 0 < v p) :
    (∀ q ∈ Icc 1 N, mixed N p (fun d => (μ d : ℝ) * w d) q =
      mixed N p (fun d => (μ d : ℝ) * v d) q) ↔
    ∀ d ∈ Icc 1 N, (μ d : ℝ) * w d = (μ d : ℝ) * v d := by
  have hpI : p ∈ Icc 1 N := mem_Icc.mpr
    ⟨by have := (mem_Icc.mp (mem_filter.mp hp).1).1; omega,
      (mem_Icc.mp (mem_filter.mp hp).1).2⟩
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (mem_filter.mp hp).2.1.pos
  apply mixed_eq_iff_of_negative hpI
  · rw [selbergMultiplesCoord_moebius_mul_primeTail hp w]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hw) hp0
  · rw [selbergMultiplesCoord_moebius_mul_primeTail hp v]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hv) hp0

/-- Vanishing taper erases the entire mixed row, not just its anchor square. -/
theorem moebius_mixed_zero_iff {N p : ℕ} (hp : p ∈ sievePrimeTail N) (w : ℕ → ℝ) :
    (∀ q ∈ Icc 1 N, mixed N p (fun d => (μ d : ℝ) * w d) q = 0) ↔ w p = 0 := by
  have hpI : p ∈ Icc 1 N := mem_Icc.mpr
    ⟨by have := (mem_Icc.mp (mem_filter.mp hp).1).1; omega,
      (mem_Icc.mp (mem_filter.mp hp).1).2⟩
  rw [mixed_zero_iff hpI]
  exact not_iff_not.mp (selbergMultiplesCoord_moebius_mul_primeTail_ne_zero_iff hp w)

/-- Changing the coefficient at one preserves every other multiples coordinate. -/
def unitPerturb (c : ℕ → ℝ) (t : ℝ) (d : ℕ) : ℝ :=
  c d + if d = 1 then t else 0

theorem coordinate_unitPerturb {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (t : ℝ) (q : ℕ) :
    selbergMultiplesCoord N (unitPerturb c t) q =
      selbergMultiplesCoord N c q + if q = 1 then t else 0 := by
  unfold selbergMultiplesCoord unitPerturb
  rw [sum_congr rfl (fun d _ => add_div (c d) _ (d : ℝ)), sum_add_distrib]
  congr 1
  by_cases hq : q = 1
  · subst q
    rw [if_pos rfl, sum_eq_single 1]
    · simp
    · intro d _ hd
      simp [hd]
    · intro h
      exact (h (mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hN⟩, by simp⟩)).elim
  · rw [if_neg hq]
    apply sum_eq_zero
    intro d hd
    have hd1 : d ≠ 1 := by
      intro he
      have hqd := (mem_filter.mp hd).2
      rw [he, Nat.dvd_one] at hqd
      exact hq hqd
    simp [hd1]

theorem mixed_unitPerturb {N p : ℕ} (hN : 1 ≤ N) (hp : p ≠ 1)
    (c : ℕ → ℝ) (t : ℝ) (q : ℕ) :
    mixed N p (unitPerturb c t) q - mixed N p c q =
      if q = 1 then selbergMultiplesCoord N c p * t else 0 := by
  simp only [mixed, coordinate_unitPerturb hN, if_neg hp, add_zero]
  split_ifs <;> ring

/-- Exact conditioning witness inside the same squarefree Möbius-taper family. -/
theorem moebius_unitPerturb (w : ℕ → ℝ) (t : ℝ) :
    unitPerturb (fun d => (μ d : ℝ) * w d) t =
      fun d => (μ d : ℝ) * (w d + if d = 1 then t else 0) := by
  funext d
  by_cases hd : d = 1 <;> simp [unitPerturb, hd]

theorem moebius_conditioning_witness {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (w : ℕ → ℝ) (t : ℝ) :
    |unitPerturb (fun d => (μ d : ℝ) * w d) t 1 - (μ 1 : ℝ) * w 1| = |t| ∧
    error N p (unitPerturb (fun d => (μ d : ℝ) * w d) t)
      (fun d => (μ d : ℝ) * w d) 1 = |w p / (p : ℝ)| * |t| := by
  have hprime := (mem_filter.mp hp).2.1
  have hN : 1 ≤ N := by
    have := (mem_Icc.mp (mem_filter.mp hp).1).2
    have := hprime.two_le
    omega
  refine ⟨by simp [unitPerturb], ?_⟩
  rw [error, mixed_unitPerturb hN hprime.ne_one, if_pos rfl,
    selbergMultiplesCoord_moebius_mul_primeTail hp w, abs_mul, neg_div, abs_neg]

theorem barbanVehov_mixed_zero_iff {N p : ℕ} (hp : p ∈ sievePrimeTail N) (X : ℕ) :
    (∀ q ∈ Icc 1 N, mixed N p (barbanVehovWeight X) q = 0) ↔ X ≤ p := by
  have hpI : p ∈ Icc 1 N := mem_Icc.mpr
    ⟨by have := (mem_Icc.mp (mem_filter.mp hp).1).1; omega,
      (mem_Icc.mp (mem_filter.mp hp).1).2⟩
  rw [mixed_zero_iff hpI]
  simpa only [not_not, not_lt] using
    not_congr (selbergMultiplesCoord_barbanVehov_primeTail_ne_zero_iff hp X)

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
