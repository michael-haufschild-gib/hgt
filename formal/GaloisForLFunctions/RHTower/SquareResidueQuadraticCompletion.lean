import GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower
import Mathlib.Analysis.Fourier.ZMod

/-!
Quadratic Gauss sums with arbitrary coefficients and positive modulus.
Translation and character orthogonality retain the entire kernel of
multiplication by `2 * a`, so even moduli and non-coprime coefficients are
included. Its cardinality is `gcd q (2 * a).val`. Fourier completion then
controls a weighted quadratic sum by the Fourier coefficient mass of its
weight. The arithmetic estimate for that mass is a separate obligation.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Complex

namespace RHTower

variable {q : ℕ} [NeZero q]

noncomputable def squareResidueQuadraticGaussSum (a b : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar (a * x ^ 2 + b * x)

def squareResidueQuadraticRadical (a : ZMod q) : Finset (ZMod q) :=
  univ.filter (fun h => 2 * a * h = 0)

private theorem squareResidue_linear_character_sum (c : ZMod q) :
    (∑ y : ZMod q, ZMod.stdAddChar (c * y)) = if c = 0 then (q : ℂ) else 0 := by
  split_ifs with hc
  · simp [hc, AddChar.map_zero_eq_one, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hc)

private theorem squareResidue_quadratic_shift (a b h y : ZMod q) :
    ZMod.stdAddChar (a * (h + y) ^ 2 + b * (h + y)) *
        (starRingEnd ℂ) (ZMod.stdAddChar (a * y ^ 2 + b * y)) =
      ZMod.stdAddChar (a * h ^ 2 + b * h) * ZMod.stdAddChar ((2 * a * h) * y) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem squareResidueQuadraticGaussSum_mul_conj (a b : ZMod q) :
    squareResidueQuadraticGaussSum a b * (starRingEnd ℂ) (squareResidueQuadraticGaussSum a b) =
      (q : ℂ) * ∑ h ∈ squareResidueQuadraticRadical a,
        ZMod.stdAddChar (a * h ^ 2 + b * h) := by
  calc
    _ = ∑ y : ZMod q, ∑ x : ZMod q,
        ZMod.stdAddChar (a * x ^ 2 + b * x) *
          (starRingEnd ℂ) (ZMod.stdAddChar (a * y ^ 2 + b * y)) := by
      simp only [squareResidueQuadraticGaussSum, map_sum, sum_mul, mul_sum]
    _ = ∑ y : ZMod q, ∑ h : ZMod q,
        ZMod.stdAddChar (a * h ^ 2 + b * h) * ZMod.stdAddChar ((2 * a * h) * y) := by
      apply sum_congr rfl
      intro y _
      rw [← Equiv.sum_comp (Equiv.addRight y) (fun x : ZMod q =>
        ZMod.stdAddChar (a * x ^ 2 + b * x) *
          (starRingEnd ℂ) (ZMod.stdAddChar (a * y ^ 2 + b * y)))]
      apply sum_congr rfl
      intro h _
      exact squareResidue_quadratic_shift a b h y
    _ = ∑ h : ZMod q, ZMod.stdAddChar (a * h ^ 2 + b * h) *
        ∑ y : ZMod q, ZMod.stdAddChar ((2 * a * h) * y) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro h _
      rw [mul_sum]
    _ = _ := by
      simp_rw [squareResidue_linear_character_sum]
      simp only [squareResidueQuadraticRadical, sum_filter, mul_sum]
      apply sum_congr rfl
      intro h _
      simp [mul_ite, mul_comm]

theorem norm_squareResidueQuadraticGaussSum_sq_eq_radical (a b : ZMod q) :
    ‖squareResidueQuadraticGaussSum a b‖ ^ 2 =
      (q : ℝ) * ‖∑ h ∈ squareResidueQuadraticRadical a,
        ZMod.stdAddChar (a * h ^ 2 + b * h)‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (squareResidueQuadraticGaussSum_mul_conj a b)
  simpa only [norm_mul, Complex.norm_conj, Complex.norm_natCast, pow_two] using h

theorem norm_squareResidueQuadraticGaussSum_sq_le (a b : ZMod q) :
    ‖squareResidueQuadraticGaussSum a b‖ ^ 2 ≤
      (q : ℝ) * (squareResidueQuadraticRadical a).card := by
  rw [norm_squareResidueQuadraticGaussSum_sq_eq_radical]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  calc
    _ ≤ ∑ h ∈ squareResidueQuadraticRadical a,
        ‖ZMod.stdAddChar (a * h ^ 2 + b * h)‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply]

theorem squareResidueQuadraticRadical_eq_singleton (a : ZMod q) (ha : IsUnit (2 * a)) :
    squareResidueQuadraticRadical a = {0} := by
  rcases ha with ⟨u, hu⟩
  ext h
  simp only [squareResidueQuadraticRadical, mem_filter, mem_univ, true_and, mem_singleton]
  rw [← hu]
  simp

theorem norm_squareResidueQuadraticGaussSum_sq_of_isUnit (a b : ZMod q)
    (ha : IsUnit (2 * a)) : ‖squareResidueQuadraticGaussSum a b‖ ^ 2 = q := by
  rw [norm_squareResidueQuadraticGaussSum_sq_eq_radical,
    squareResidueQuadraticRadical_eq_singleton a ha]
  simp [AddChar.map_zero_eq_one]

theorem squareResidueQuadraticGaussSum_zero_eq_gaussQ (a : ℤ) :
    squareResidueQuadraticGaussSum (q := q) (a : ZMod q) 0 =
      GaloisForLFunctions.RHTower.HalfWeight.gaussQ a q := by
  rw [GaloisForLFunctions.RHTower.HalfWeight.gaussQ_eq_sum_zmod]
  simp [squareResidueQuadraticGaussSum]

noncomputable def squareResidueFourierCoeff (w : ZMod q → ℂ) (b : ZMod q) : ℂ :=
  ∑ x : ZMod q, w x * ZMod.stdAddChar (-b * x)

theorem squareResidueFourier_inversion (w : ZMod q → ℂ) (y : ZMod q) :
    (∑ b : ZMod q, squareResidueFourierCoeff w b * ZMod.stdAddChar (b * y)) =
      (q : ℂ) * w y := by
  calc
    _ = ∑ x : ZMod q, w x * ∑ b : ZMod q, ZMod.stdAddChar ((y - x) * b) := by
      simp only [squareResidueFourierCoeff, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      rw [mul_assoc]
      congr 1
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = _ := by
      simp_rw [squareResidue_linear_character_sum]
      simp [sub_eq_zero, mul_ite, mul_comm]

theorem squareResidueQuadraticGaussSum_completion (w : ZMod q → ℂ) (a : ZMod q) :
    (q : ℂ) * (∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2)) =
      ∑ b : ZMod q, squareResidueFourierCoeff w b *
        squareResidueQuadraticGaussSum a b := by
  calc
    _ = ∑ x : ZMod q, ((q : ℂ) * w x) * ZMod.stdAddChar (a * x ^ 2) := by
      simp only [mul_sum, mul_assoc]
    _ = ∑ x : ZMod q,
        (∑ b : ZMod q, squareResidueFourierCoeff w b * ZMod.stdAddChar (b * x)) *
          ZMod.stdAddChar (a * x ^ 2) := by
      simp only [squareResidueFourier_inversion]
    _ = _ := by
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [squareResidueQuadraticGaussSum, mul_sum]
      apply sum_congr rfl
      intro x _
      rw [mul_assoc, ← AddChar.map_add_eq_mul, add_comm]

theorem norm_squareResidueQuadraticGaussSum_le (a b : ZMod q) :
    ‖squareResidueQuadraticGaussSum a b‖ ≤
      Real.sqrt ((q : ℝ) * (squareResidueQuadraticRadical a).card) := by
  have h := norm_squareResidueQuadraticGaussSum_sq_le a b
  have hs := Real.sq_sqrt (show 0 ≤ (q : ℝ) * (squareResidueQuadraticRadical a).card by
    positivity)
  have hn := Real.sqrt_nonneg ((q : ℝ) * (squareResidueQuadraticRadical a).card)
  nlinarith [norm_nonneg (squareResidueQuadraticGaussSum a b)]

theorem norm_squareResidueQuadraticGaussSum_completion_le
    (w : ZMod q → ℂ) (a : ZMod q) :
    (q : ℝ) * ‖∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2)‖ ≤
      Real.sqrt ((q : ℝ) * (squareResidueQuadraticRadical a).card) *
        ∑ b : ZMod q, ‖squareResidueFourierCoeff w b‖ := by
  calc
    _ = ‖∑ b : ZMod q, squareResidueFourierCoeff w b *
        squareResidueQuadraticGaussSum a b‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) (squareResidueQuadraticGaussSum_completion w a)
      simpa only [norm_mul, Complex.norm_natCast] using h
    _ ≤ ∑ b : ZMod q, ‖squareResidueFourierCoeff w b *
        squareResidueQuadraticGaussSum a b‖ := norm_sum_le _ _
    _ ≤ ∑ b : ZMod q, ‖squareResidueFourierCoeff w b‖ *
        Real.sqrt ((q : ℝ) * (squareResidueQuadraticRadical a).card) := by
      apply sum_le_sum
      intro b _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_squareResidueQuadraticGaussSum_le a b)
        (norm_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Exact size of the multiplication kernel, without a coprimality assumption. -/
theorem squareResidue_mul_kernel_card (c : ZMod q) :
    (univ.filter (fun x : ZMod q => c * x = 0)).card = Nat.gcd q c.val := by
  let g := Nat.gcd q c.val
  let m := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left c.val (NeZero.pos q)
  have hdiv (n : ℕ) : m ∣ n ↔ q ∣ c.val * n := by
    rw [show m = q / g from rfl,
      Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q c.val) hg]
    constructor
    · intro h
      exact h.trans (Nat.mul_dvd_mul_right (Nat.gcd_dvd_right q c.val) n)
    · intro h
      have hd := Nat.dvd_gcd (dvd_mul_right q n) h
      simpa only [Nat.gcd_mul_right] using hd
  have hmul (n : ℕ) : c * (n : ZMod q) = 0 ↔ q ∣ c.val * n := by
    have he : ((c.val * n : ℕ) : ZMod q) = c * (n : ZMod q) := by
      simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [← he, ZMod.natCast_eq_zero_iff]
  let f : ZMod q → ℕ := fun x => if x.val = 0 then q else x.val
  have hf_bounds (x : ZMod q) : 0 < f x ∧ f x ≤ q := by
    dsimp [f]
    split_ifs with hx
    · exact ⟨NeZero.pos q, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero hx, (ZMod.val_lt x).le⟩
  have hfcast (x : ZMod q) : (f x : ZMod q) = x := by
    by_cases hx : x.val = 0
    · have hx0 := (ZMod.val_eq_zero x).mp hx
      dsimp only [f]
      rw [if_pos hx, ZMod.natCast_self]
      exact hx0.symm
    · dsimp only [f]
      rw [if_neg hx, ZMod.natCast_zmod_val]
  have hfn {n : ℕ} (hn : 0 < n ∧ n ≤ q) : f (n : ZMod q) = n := by
    by_cases h : n = q
    · subst n
      simp [f]
    · have hnq : n < q := lt_of_le_of_ne hn.2 h
      have hval : (n : ZMod q).val = n := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hnq]
      simp only [f, hval, if_neg (Nat.ne_of_gt hn.1)]
  calc
    _ = ((Ioc 0 q).filter (fun n => m ∣ n)).card := by
      apply Finset.card_nbij' f (fun n => (n : ZMod q))
      · intro x hx
        change x ∈ univ.filter (fun x : ZMod q => c * x = 0) at hx
        simp only [mem_filter, mem_univ, true_and] at hx
        apply mem_filter.mpr
        refine ⟨mem_Ioc.mpr (hf_bounds x), (hdiv (f x)).mpr ?_⟩
        apply (hmul (f x)).mp
        simpa only [hfcast] using hx
      · intro n hn
        obtain ⟨_, hn⟩ := mem_filter.mp hn
        change (n : ZMod q) ∈ univ.filter (fun x : ZMod q => c * x = 0)
        simp only [mem_filter, mem_univ, true_and]
        exact (hmul n).mpr ((hdiv n).mp hn)
      · intro x _
        exact hfcast x
      · intro n hn
        exact hfn (mem_Ioc.mp (mem_filter.mp hn).1)
    _ = q / m := Nat.Ioc_filter_dvd_card_eq_div q m
    _ = _ := Nat.div_div_self (Nat.gcd_dvd_left q c.val) (NeZero.ne q)

theorem squareResidueQuadraticRadical_card (a : ZMod q) :
    (squareResidueQuadraticRadical a).card = Nat.gcd q (2 * a).val :=
  squareResidue_mul_kernel_card (2 * a)

theorem norm_squareResidueQuadraticGaussSum_sq_le_gcd (a b : ZMod q) :
    ‖squareResidueQuadraticGaussSum a b‖ ^ 2 ≤
      (q : ℝ) * Nat.gcd q (2 * a).val := by
  simpa only [squareResidueQuadraticRadical_card] using
    norm_squareResidueQuadraticGaussSum_sq_le a b

theorem norm_squareResidueQuadraticGaussSum_le_gcd (a b : ZMod q) :
    ‖squareResidueQuadraticGaussSum a b‖ ≤
      Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) := by
  simpa only [squareResidueQuadraticRadical_card] using
    norm_squareResidueQuadraticGaussSum_le a b

/-- Uniform weighted completion bound, including all degenerate frequencies. -/
theorem norm_squareResidueQuadraticGaussSum_completion_le_gcd
    (w : ZMod q → ℂ) (a : ZMod q) :
    (q : ℝ) * ‖∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2)‖ ≤
      Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
        ∑ b : ZMod q, ‖squareResidueFourierCoeff w b‖ := by
  simpa only [squareResidueQuadraticRadical_card] using
    norm_squareResidueQuadraticGaussSum_completion_le w a

end RHTower
