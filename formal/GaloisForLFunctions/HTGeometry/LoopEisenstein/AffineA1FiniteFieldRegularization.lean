import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZetaBounds
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1FiniteFieldCoefficients
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineDegreeGaussianSeries

/-!
# Removing the common arithmetic denominator from affine coefficients

On the level-four spectral slice, only the finite simple root can meet a
Frobenius denominator zero. Removing that factor makes every Weyl coefficient
holomorphic on one common strip, with an exponential bound in the Weyl length.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

open ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- The level-four slice through the finite simple-root pole line. -/
def levelFourParameter (s : ℂ) : ℂ × ℂ := (4 - s, s)

lemma levelFourArgument_plus (s : ℂ) (n : ℤ) :
    rootArgument (levelFourParameter s) (.plus n) = 4 * n + s := by
  simp only [rootArgument, levelFourParameter, Root.corootZero, Root.corootOne,
    Int.cast_add, Int.cast_one]
  ring

lemma levelFourArgument_minus (s : ℂ) (n : ℤ) :
    rootArgument (levelFourParameter s) (.minus n) = 4 * n - s := by
  simp only [rootArgument, levelFourParameter, Root.corootZero, Root.corootOne,
    Int.cast_sub, Int.cast_one]
  ring

@[simp] lemma levelFourArgument_simple (s : ℂ) :
    rootArgument (levelFourParameter s) (.plus 0) = s := by
  rw [levelFourArgument_plus]
  simp only [Int.cast_zero, mul_zero, zero_add]

lemma levelFourArgument_analytic (β : Root) (s : ℂ) :
    AnalyticAt ℂ (fun z => rootArgument (levelFourParameter z) β) s := by
  unfold rootArgument levelFourParameter
  fun_prop

/-- Every remaining positive root stays uniformly inside the regular half-plane. -/
lemma levelFourArgument_re_gt_two (s : ℂ) (hs : s ∈ levelFourStrip)
    (β : Root) (hβ : β.positive) (hne : β ≠ .plus 0) :
    2 < (rootArgument (levelFourParameter s) β).re := by
  rcases hs with ⟨hlo, hhi⟩
  cases β with
  | plus n =>
    have hn : (1 : ℝ) ≤ n := by
      have hn' : (1 : ℤ) ≤ n := by
        change 0 ≤ n at hβ
        have : n ≠ 0 := fun h => hne (congrArg Root.plus h)
        omega
      exact_mod_cast hn'
    rw [levelFourArgument_plus]
    norm_num [Complex.mul_re]
    linarith only [hn, hlo]
  | minus n =>
    have hn : (1 : ℝ) ≤ n := by
      have hn' : (1 : ℤ) ≤ n := by change 0 < n at hβ; omega
      exact_mod_cast hn'
    rw [levelFourArgument_minus]
    norm_num [Complex.mul_re]
    linarith only [hn, hhi]

/-- Product of the nonsingular root factors, excluding the finite simple root. -/
def regularFiniteFieldProduct (w : Weyl) (s : ℂ) : ℂ :=
  ∏ β ∈ (inversions w).erase (.plus 0),
    reducedArithmeticRatio (rootArgument (levelFourParameter s) β)

lemma regularFiniteFieldProduct_analytic (w : Weyl) :
    AnalyticOnNhd ℂ (regularFiniteFieldProduct w) levelFourStrip := by
  intro s hs
  have hf : ∀ β ∈ (inversions w).erase (.plus 0),
      AnalyticAt ℂ (fun z => reducedArithmeticRatio
        (rootArgument (levelFourParameter z) β)) s := by
    intro β hβ
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hβ
    exact (reducedArithmeticRatio_analytic_right _
      (levelFourArgument_re_gt_two s hs β ((mem_inversions w β).mp hmem).1 hne).le).comp
        (f := fun z => rootArgument (levelFourParameter z) β)
        (levelFourArgument_analytic β s)
  have he : regularFiniteFieldProduct w =
      ∏ β ∈ (inversions w).erase (.plus 0),
        (fun z => reducedArithmeticRatio (rootArgument (levelFourParameter z) β)) := by
    funext z
    simp only [regularFiniteFieldProduct, Finset.prod_apply]
  rw [he]
  exact Finset.analyticAt_prod _ hf

/-- Multiplication by the common denominator removes all arithmetic poles on the strip. -/
def clearedFiniteFieldCoefficient (w : Weyl) (s : ℂ) : ℂ :=
  (if Root.plus 0 ∈ inversions w then arithmeticRatioNumerator s
    else arithmeticRatioDenominator s) * regularFiniteFieldProduct w s

lemma clearedFiniteFieldCoefficient_analytic (w : Weyl) :
    AnalyticOnNhd ℂ (clearedFiniteFieldCoefficient w) levelFourStrip := by
  intro s hs
  unfold clearedFiniteFieldCoefficient
  split_ifs
  · exact (arithmeticRatioNumerator_analytic s).mul
      (regularFiniteFieldProduct_analytic w s hs)
  · exact (arithmeticRatioDenominator_analytic s).mul
      (regularFiniteFieldProduct_analytic w s hs)

@[simp] lemma clearedFiniteFieldCoefficient_one (s : ℂ) :
    clearedFiniteFieldCoefficient 1 s = arithmeticRatioDenominator s := by
  simp [clearedFiniteFieldCoefficient, regularFiniteFieldProduct]

@[simp] lemma clearedFiniteFieldCoefficient_finiteReflection (s : ℂ) :
    clearedFiniteFieldCoefficient finiteReflection s = arithmeticRatioNumerator s := by
  simp only [clearedFiniteFieldCoefficient, inversions_finiteReflection,
    Finset.mem_singleton, ite_true, regularFiniteFieldProduct, Finset.erase_singleton,
    Finset.prod_empty, mul_one]

/-- One constant controls all regularized coefficients exponentially in inversion length. -/
theorem exists_clearedFiniteFieldCoefficient_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ w s, s ∈ levelFourStrip →
      ‖clearedFiniteFieldCoefficient w s‖ ≤
        Real.exp (((inversions w).card + 1 : ℝ) * C) := by
  obtain ⟨B, hB, hb⟩ := exists_reducedArithmeticRatio_bound
  obtain ⟨K, hK, hk⟩ := exists_arithmeticRatio_parts_bound
  let C := max B K
  have hC : 1 ≤ C := hB.trans (le_max_left _ _)
  have hCexp : C ≤ Real.exp C := by linarith only [Real.add_one_le_exp C]
  have hBexp : B ≤ Real.exp C := (le_max_left _ _).trans hCexp
  have hKexp : K ≤ Real.exp C := (le_max_right _ _).trans hCexp
  refine ⟨C, hC, fun w s hs => ?_⟩
  have hparts := hk s hs.1.le
  have hfirst : ‖if Root.plus 0 ∈ inversions w then arithmeticRatioNumerator s
      else arithmeticRatioDenominator s‖ ≤ Real.exp C := by
    split_ifs
    · exact hparts.1.trans hKexp
    · exact hparts.2.trans hKexp
  have hprod : ‖regularFiniteFieldProduct w s‖ ≤
      Real.exp (((inversions w).erase (.plus 0)).card * C) := by
    unfold regularFiniteFieldProduct
    apply (Finset.norm_prod_le _ _).trans
    calc
      _ ≤ ∏ _β ∈ (inversions w).erase (.plus 0), Real.exp C := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro β hβ
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hβ
        exact (hb _ (levelFourArgument_re_gt_two s hs β
          ((mem_inversions w β).mp hmem).1 hne).le).trans hBexp
      _ = _ := by rw [Finset.prod_const, ← Real.exp_nat_mul]
  rw [clearedFiniteFieldCoefficient, norm_mul]
  calc
    _ ≤ Real.exp C * Real.exp (((inversions w).erase (.plus 0)).card * C) :=
      mul_le_mul hfirst hprod (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (((inversions w).card + 1 : ℝ) * C) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hc : (((inversions w).erase (.plus 0)).card : ℝ) ≤ (inversions w).card :=
        by exact_mod_cast (Finset.card_erase_le :
          ((inversions w).erase (.plus 0)).card ≤ (inversions w).card)
      have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ C by linarith only [hC])
      linarith only [hm]

/-- The two integer-indexed Weyl families have one common exponential coefficient bound. -/
theorem exists_clearedFiniteFieldCoefficient_family_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℤ, ∀ s, s ∈ levelFourStrip →
      ‖clearedFiniteFieldCoefficient (.r n) s‖ ≤ Real.exp (2 * C + 2 * C * |(n : ℝ)|) ∧
      ‖clearedFiniteFieldCoefficient (.sr n) s‖ ≤ Real.exp (2 * C + 2 * C * |(n : ℝ)|) := by
  obtain ⟨C, hC, hb⟩ := exists_clearedFiniteFieldCoefficient_bound
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hcast (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  refine ⟨C, hC, fun n s hs => ⟨?_, ?_⟩⟩
  · apply (hb (.r n) s hs).trans
    apply Real.exp_le_exp.mpr
    rw [inversions_translation_card, hcast]
    norm_num [abs_mul]
    nlinarith only [hC0]
  · apply (hb (.sr n) s hs).trans
    apply Real.exp_le_exp.mpr
    rw [inversions_reflection_card, hcast]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    have ha : |2 * (n : ℝ) + 1| ≤ 2 * |(n : ℝ)| + 1 := by
      simpa only [abs_mul, abs_two, abs_one] using abs_add_le (2 * (n : ℝ)) 1
    have hm := mul_le_mul_of_nonneg_right ha hC0
    nlinarith only [hm]

/-- The holomorphic coefficient is exactly the original coefficient times its common denominator. -/
theorem clearedFiniteFieldCoefficient_eq (w : Weyl) (s : ℂ)
    (hs : s ∈ levelFourStrip) (hs0 : s.re ≠ 0)
    (hQ : arithmeticRatioDenominator s ≠ 0) :
    clearedFiniteFieldCoefficient w s =
      arithmeticRatioDenominator s * finiteFieldCoefficient (levelFourParameter s) w := by
  have he : finiteFieldCoefficient (levelFourParameter s) w =
      ∏ β ∈ inversions w, reducedArithmeticRatio (rootArgument (levelFourParameter s) β) := by
    apply Finset.prod_congr rfl
    intro β hβ
    apply (reducedArithmeticRatio_eq _ ?_).symm
    by_cases hb : β = .plus 0
    · subst β
      simpa only [levelFourArgument_simple] using hs0
    · exact (lt_trans (by norm_num : (0 : ℝ) < 2)
        (levelFourArgument_re_gt_two s hs β ((mem_inversions w β).mp hβ).1 hb)).ne'
  rw [he, clearedFiniteFieldCoefficient]
  by_cases hmem : Root.plus 0 ∈ inversions w
  · have hcancel : arithmeticRatioDenominator s *
        (arithmeticRatioNumerator s / arithmeticRatioDenominator s) =
          arithmeticRatioNumerator s := by
      rw [mul_comm, div_mul_cancel₀ _ hQ]
    rw [if_pos hmem, ← Finset.mul_prod_erase _ _ hmem, levelFourArgument_simple,
      reducedArithmeticRatio_eq_div, ← mul_assoc, hcancel]
    rfl
  · rw [if_neg hmem, regularFiniteFieldProduct, Finset.erase_eq_of_notMem hmem]

/-- The common denominator is nonzero in the original convergence chamber. -/
lemma arithmeticRatioDenominator_ne_zero_chamber (s : ℂ) (hs : 1 < s.re) :
    arithmeticRatioDenominator s ≠ 0 := by
  have ht : ‖zetaCoordinate s‖ < 1 / 3 := by
    rw [zetaCoordinate_norm]
    calc
      Real.exp (-Real.log 3 * s.re) < Real.exp (-Real.log 3) := by
        apply Real.exp_lt_exp.mpr
        nlinarith only [log_three_pos, hs]
      _ = 1 / 3 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        norm_num
  apply mul_ne_zero
  · intro hz
    have he : zetaCoordinate s = 1 / 3 := by
      change 1 - 3 * zetaCoordinate s = 0 at hz
      linear_combination -(1 / 3 : ℂ) * hz
    rw [he] at ht
    norm_num [norm_div] at ht
  · apply numerator_ne_zero_small_norm
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    linarith only [ht]

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
