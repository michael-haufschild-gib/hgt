import GaloisForLFunctions.RHTower.InfiniteSymmetry.CurveDatumZetaRatio
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1FiniteFieldWeylPoles

/-!
# The affine `A₁` Weyl sum of an arbitrary curve datum and its exact poles

The affine `A₁` constant-term expansion attaches to a Weyl element `w` the Gindikin–Karpelevich
coefficient `Π_{β ∈ I(w)} Z(⟨λ, β∨⟩)/Z(⟨λ, β∨⟩ + 1)` and Garland's degree-rotated torus factor.
This module builds the complete infinite sum for **every** curve datum satisfying the strip
condition `1 < |α_i| < q`, unitary or not, on the level-four slice `λ(s) = (4 − s, s)`:

* clearing the common denominator `Q` makes every coefficient holomorphic on `−1 < Re s < 2`
  with an exponential bound in the Weyl length; the cleared sum `H_R` is holomorphic
  (`regularizedWeylSum_analytic`) and `H_R / Q` continues the literal series from the Godement
  half-plane (`continuedWeylSum_eq_chamber`);
* strong degree rotation isolates the identity and finite-reflection coefficients `Q + N`
  (`regularizedWeylSum_tendsto`); at a zero of `Z(s + 1)` the identity term vanishes and `N ≠ 0`,
  so every pole survives with its exact multiplicity (`weylSum_eventual_order`);
* off the zeros of `Q` the continuation is holomorphic (`continuedWeylSum_analytic`).

The same proof works for the actual genus-one curve over `𝔽₃` and for the impure golden datum:
nothing in it sees whether `|β_i| = 1`.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower.InfiniteSymmetry

open ArithmeticCastelnuovoSeveri HTGeometry.LoopEisenstein.AffineA1

noncomputable section

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : ArithmeticCastelnuovoSeveri.CurveDatum ι)

/-! ### The literal Weyl sum -/

/-- The Gindikin–Karpelevich coefficient of `w` for the datum's zeta function. -/
def weylCoefficient (lam : ℂ × ℂ) (w : Weyl) : ℂ :=
  ∏ β ∈ inversions w, zetaRatio D (rootArgument lam β)

/-- A term of the affine constant-term expansion. -/
def weylTerm (lam : ℂ × ℂ) (t z r : ℝ) (w : Weyl) : ℂ :=
  weylCoefficient D lam w * Complex.exp (weylExponent lam t z r w)

/-- The complete infinite affine Weyl sum, independently of any regularization. -/
def weylSum (lam : ℂ × ℂ) (t z r : ℝ) : ℂ := ∑' w : Weyl, weylTerm D lam t z r w

/-! ### Clearing the common denominator -/

/-- Product of the root factors other than the finite simple root. -/
def regularProduct (w : Weyl) (s : ℂ) : ℂ :=
  ∏ β ∈ (inversions w).erase (.plus 0), reducedRatio D (rootArgument (levelFourParameter s) β)

lemma regularProduct_analytic (hD : StripCondition D) (w : Weyl) :
    AnalyticOnNhd ℂ (regularProduct D w) levelFourStrip := by
  intro s hs
  have hf : ∀ β ∈ (inversions w).erase (.plus 0),
      AnalyticAt ℂ (fun z => reducedRatio D (rootArgument (levelFourParameter z) β)) s := by
    intro β hβ
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hβ
    exact (reducedRatio_analytic_right D hD _
      (levelFourArgument_re_gt_two s hs β ((mem_inversions w β).mp hmem).1 hne).le).comp
        (f := fun z => rootArgument (levelFourParameter z) β) (levelFourArgument_analytic β s)
  have he : regularProduct D w =
      ∏ β ∈ (inversions w).erase (.plus 0),
        (fun z => reducedRatio D (rootArgument (levelFourParameter z) β)) := by
    funext z
    simp only [regularProduct, Finset.prod_apply]
  rw [he]
  exact Finset.analyticAt_prod _ hf

/-- The coefficient times the common denominator `Q`, holomorphic on the strip. -/
def clearedCoefficient (w : Weyl) (s : ℂ) : ℂ :=
  (if Root.plus 0 ∈ inversions w then ratioNumerator D s else ratioDenominator D s) *
    regularProduct D w s

lemma clearedCoefficient_analytic (hD : StripCondition D) (w : Weyl) :
    AnalyticOnNhd ℂ (clearedCoefficient D w) levelFourStrip := by
  intro s hs
  unfold clearedCoefficient
  split_ifs
  · exact (ratioNumerator_analytic D s).mul (regularProduct_analytic D hD w s hs)
  · exact (ratioDenominator_analytic D s).mul (regularProduct_analytic D hD w s hs)

@[simp] lemma clearedCoefficient_one (s : ℂ) :
    clearedCoefficient D 1 s = ratioDenominator D s := by
  simp [clearedCoefficient, regularProduct]

@[simp] lemma clearedCoefficient_finiteReflection (s : ℂ) :
    clearedCoefficient D finiteReflection s = ratioNumerator D s := by
  simp only [clearedCoefficient, inversions_finiteReflection, Finset.mem_singleton, ite_true,
    regularProduct, Finset.erase_singleton, Finset.prod_empty, mul_one]

/-- One constant bounds all cleared coefficients exponentially in the inversion length. -/
theorem exists_clearedCoefficient_bound (hD : StripCondition D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ w s, s ∈ levelFourStrip →
      ‖clearedCoefficient D w s‖ ≤ Real.exp (((inversions w).card + 1 : ℝ) * C) := by
  obtain ⟨B, hB, hb⟩ := exists_reducedRatio_bound D hD
  obtain ⟨K, hK, hk⟩ := exists_ratioParts_bound D
  let C := max B K
  have hC : 1 ≤ C := hB.trans (le_max_left _ _)
  have hCexp : C ≤ Real.exp C := by linarith only [Real.add_one_le_exp C]
  have hBexp : B ≤ Real.exp C := (le_max_left _ _).trans hCexp
  have hKexp : K ≤ Real.exp C := (le_max_right _ _).trans hCexp
  refine ⟨C, hC, fun w s hs => ?_⟩
  have hparts := hk s hs.1.le
  have hfirst : ‖if Root.plus 0 ∈ inversions w then ratioNumerator D s
      else ratioDenominator D s‖ ≤ Real.exp C := by
    split_ifs
    · exact hparts.1.trans hKexp
    · exact hparts.2.trans hKexp
  have hprod : ‖regularProduct D w s‖ ≤
      Real.exp (((inversions w).erase (.plus 0)).card * C) := by
    unfold regularProduct
    apply (Finset.norm_prod_le _ _).trans
    calc
      _ ≤ ∏ _β ∈ (inversions w).erase (.plus 0), Real.exp C := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro β hβ
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hβ
        exact (hb _ (levelFourArgument_re_gt_two s hs β
          ((mem_inversions w β).mp hmem).1 hne).le).trans hBexp
      _ = _ := by rw [Finset.prod_const, ← Real.exp_nat_mul]
  rw [clearedCoefficient, norm_mul]
  calc
    _ ≤ Real.exp C * Real.exp (((inversions w).erase (.plus 0)).card * C) :=
      mul_le_mul hfirst hprod (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (((inversions w).card + 1 : ℝ) * C) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hc : (((inversions w).erase (.plus 0)).card : ℝ) ≤ (inversions w).card := by
        exact_mod_cast (Finset.card_erase_le :
          ((inversions w).erase (.plus 0)).card ≤ (inversions w).card)
      have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ C by linarith only [hC])
      linarith only [hm]

/-- The two integer-indexed Weyl families share one exponential coefficient bound. -/
theorem exists_clearedCoefficient_family_bound (hD : StripCondition D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℤ, ∀ s, s ∈ levelFourStrip →
      ‖clearedCoefficient D (.r n) s‖ ≤ Real.exp (2 * C + 2 * C * |(n : ℝ)|) ∧
      ‖clearedCoefficient D (.sr n) s‖ ≤ Real.exp (2 * C + 2 * C * |(n : ℝ)|) := by
  obtain ⟨C, hC, hb⟩ := exists_clearedCoefficient_bound D hD
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

/-- Off the denominator zeros, the cleared coefficient is `Q` times the original coefficient. -/
theorem clearedCoefficient_eq (w : Weyl) (s : ℂ) (hs : s ∈ levelFourStrip) (hs0 : s.re ≠ 0)
    (hQ : ratioDenominator D s ≠ 0) :
    clearedCoefficient D w s = ratioDenominator D s * weylCoefficient D (levelFourParameter s) w := by
  have he : weylCoefficient D (levelFourParameter s) w =
      ∏ β ∈ inversions w, reducedRatio D (rootArgument (levelFourParameter s) β) := by
    apply Finset.prod_congr rfl
    intro β hβ
    apply zetaRatio_eq_reduced
    by_cases hb : β = .plus 0
    · subst β
      simpa only [levelFourArgument_simple] using hs0
    · exact (lt_trans (by norm_num : (0 : ℝ) < 2)
        (levelFourArgument_re_gt_two s hs β ((mem_inversions w β).mp hβ).1 hb)).ne'
  rw [he, clearedCoefficient]
  by_cases hmem : Root.plus 0 ∈ inversions w
  · have hcancel : ratioDenominator D s * (ratioNumerator D s / ratioDenominator D s) =
        ratioNumerator D s := by
      rw [mul_comm, div_mul_cancel₀ _ hQ]
    rw [if_pos hmem, ← Finset.mul_prod_erase _ _ hmem, levelFourArgument_simple,
      reducedRatio_eq_div, ← mul_assoc, hcancel]
    rfl
  · rw [if_neg hmem, regularProduct, Finset.erase_eq_of_notMem hmem]

/-! ### The regularized sum and its continuation -/

/-- A Weyl summand with the common denominator removed. -/
def clearedWeylTerm (R : ℝ) (s : ℂ) (w : Weyl) : ℂ :=
  clearedCoefficient D w s * degreeFourFactor R s (affineDegreeIndex w)

/-- The holomorphic regularization `H_R`, written as its two integer-indexed series. -/
def regularizedWeylSum (R : ℝ) (s : ℂ) : ℂ :=
  degreeFourSeries (fun n => clearedCoefficient D (.r n)) R s +
    degreeFourSeries (fun n => clearedCoefficient D (.sr n)) R s

lemma summable_norm_clearedWeylTerm (hD : StripCondition D) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    Summable (fun w : Weyl => ‖clearedWeylTerm D R s w‖) := by
  obtain ⟨C, _, hb⟩ := exists_clearedCoefficient_family_bound D hD
  apply DihedralGroup.equivSum.symm.summable_iff.mp
  exact Summable.sum _
    (summable_norm_degreeFourSeries (fun n s hs => (hb n s hs).1) R hR s hs)
    (summable_norm_degreeFourSeries (fun n s hs => (hb n s hs).2) R hR s hs)

private lemma tsum_weyl_two_families (f : Weyl → ℂ)
    (hr : Summable (fun n : ℤ => f (.r n))) (hs : Summable (fun n : ℤ => f (.sr n))) :
    (∑' w : Weyl, f w) = (∑' n : ℤ, f (.r n)) + ∑' n : ℤ, f (.sr n) := by
  calc
    _ = ∑' a : ℤ ⊕ ℤ, f (DihedralGroup.equivSum.symm a) :=
      (DihedralGroup.equivSum.symm.tsum_eq f).symm
    _ = _ := hr.tsum_sum hs

lemma regularizedWeylSum_eq_tsum (hD : StripCondition D) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    regularizedWeylSum D R s = ∑' w : Weyl, clearedWeylTerm D R s w := by
  obtain ⟨C, _, hb⟩ := exists_clearedCoefficient_family_bound D hD
  have hr : Summable (fun n : ℤ => clearedWeylTerm D R s (.r n)) :=
    (summable_norm_degreeFourSeries (f := fun n => clearedCoefficient D (.r n))
      (fun n s hs => (hb n s hs).1) R hR s hs).of_norm
  have ht : Summable (fun n : ℤ => clearedWeylTerm D R s (.sr n)) :=
    (summable_norm_degreeFourSeries (f := fun n => clearedCoefficient D (.sr n))
      (fun n s hs => (hb n s hs).2) R hR s hs).of_norm
  exact (tsum_weyl_two_families (clearedWeylTerm D R s) hr ht).symm

/-- Normal convergence makes the regularized complete Weyl sum holomorphic. -/
theorem regularizedWeylSum_analytic (hD : StripCondition D) (R : ℝ) (hR : 0 < R) :
    AnalyticOnNhd ℂ (regularizedWeylSum D R) levelFourStrip := by
  obtain ⟨C, _, hb⟩ := exists_clearedCoefficient_family_bound D hD
  exact (degreeFourSeries_analyticOn (fun n => clearedCoefficient_analytic D hD (.r n))
    (fun n s hs => (hb n s hs).1) R hR).add
    (degreeFourSeries_analyticOn (fun n => clearedCoefficient_analytic D hD (.sr n))
      (fun n s hs => (hb n s hs).2) R hR)

lemma weylTerm_eq_cleared_div (R : ℝ) (hR : 0 < R) (s : ℂ) (hs : s ∈ levelFourStrip)
    (hs0 : s.re ≠ 0) (hQ : ratioDenominator D s ≠ 0) (w : Weyl) :
    weylTerm D (levelFourParameter s) 0 0 (Real.log R) w =
      clearedWeylTerm D R s w / ratioDenominator D s := by
  rw [weylTerm, exp_weylExponent_levelFour R hR, clearedWeylTerm,
    clearedCoefficient_eq D w s hs hs0 hQ]
  field_simp

/-- Where `Q ≠ 0`, the literal series equals the regularized sum divided by `Q`. -/
theorem weylSum_eq_regularized_div (hD : StripCondition D) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) (hs0 : s.re ≠ 0) (hQ : ratioDenominator D s ≠ 0) :
    weylSum D (levelFourParameter s) 0 0 (Real.log R) =
      regularizedWeylSum D R s / ratioDenominator D s := by
  rw [weylSum, regularizedWeylSum_eq_tsum D hD R hR s hs]
  simp_rw [weylTerm_eq_cleared_div D R hR s hs hs0 hQ]
  exact tsum_div_const

/-- The meromorphic continuation `H_R / Q` of the complete Weyl expansion. -/
def continuedWeylSum (R : ℝ) (s : ℂ) : ℂ := regularizedWeylSum D R s / ratioDenominator D s

theorem continuedWeylSum_meromorphic (hD : StripCondition D) (R : ℝ) (hR : 0 < R) :
    MeromorphicOn (continuedWeylSum D R) levelFourStrip := fun s hs =>
  (regularizedWeylSum_analytic D hD R hR s hs).meromorphicAt.div
    (ratioDenominator_analytic D s).meromorphicAt

/-- The continuation is the literal convergent series on the Godement subchamber. -/
theorem continuedWeylSum_eq_chamber (hD : StripCondition D) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hlo : 1 < s.re) (hhi : s.re < 2) :
    continuedWeylSum D R s = weylSum D (levelFourParameter s) 0 0 (Real.log R) :=
  (weylSum_eq_regularized_div D hD R hR s ⟨by linarith only [hlo], hhi⟩
    (by linarith only [hlo]) (ratioDenominator_ne_zero_chamber D hD s hlo)).symm

/-- Off the zeros of `Q` the continuation is holomorphic. -/
theorem continuedWeylSum_analytic (hD : StripCondition D) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) (hQ : ratioDenominator D s ≠ 0) :
    AnalyticAt ℂ (continuedWeylSum D R) s :=
  (regularizedWeylSum_analytic D hD R hR s hs).div (ratioDenominator_analytic D s) hQ

/-! ### Exact poles at every zero -/

/-- Strong rotation isolates the identity and finite simple-reflection terms `Q + N`. -/
theorem regularizedWeylSum_tendsto (hD : StripCondition D) (s : ℂ) (hs : s ∈ levelFourStrip) :
    Tendsto (fun R : ℝ => regularizedWeylSum D R s) atTop
      (𝓝 (ratioDenominator D s + ratioNumerator D s)) := by
  obtain ⟨C, _, hb⟩ := exists_clearedCoefficient_family_bound D hD
  have h := (degreeFourSeries_tendsto (fun n s hs => (hb n s hs).1) s hs).add
    (degreeFourSeries_tendsto (fun n s hs => (hb n s hs).2) s hs)
  change Tendsto (fun R => regularizedWeylSum D R s) atTop
    (𝓝 (clearedCoefficient D 1 s + clearedCoefficient D finiteReflection s)) at h
  simpa only [clearedCoefficient_one, clearedCoefficient_finiteReflection] using h

lemma mem_levelFourStrip_of_root (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) : s ∈ levelFourStrip := by
  obtain ⟨h₁, h₂⟩ := re_root_mem D hD s hs
  exact ⟨h₁, by linarith⟩

lemma re_ne_zero_of_root (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) : s.re ≠ 0 :=
  (re_root_mem D hD s hs).2.ne

/-- At a pole the leading regularized term `N(s)` is nonzero. -/
theorem regularizedWeylSum_eventually_ne_zero (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    ∀ᶠ R : ℝ in atTop, regularizedWeylSum D R s ≠ 0 := by
  have ht := regularizedWeylSum_tendsto D hD s (mem_levelFourStrip_of_root D hD s hs)
  rw [ratioDenominator_zero_at_root D s hs, zero_add] at ht
  exact ht.eventually_ne (ratioNumerator_ne_zero_at_root D hD s hs)

/-- Every pole of the coefficient survives in the continuation with its exact multiplicity. -/
theorem continuedWeylSum_eventual_order (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      meromorphicOrderAt (continuedWeylSum D R) s =
        -(((numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) : ℤ) : WithTop ℤ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    regularizedWeylSum_eventually_ne_zero D hD s hs] with R hR hN
  refine ⟨hR, ?_⟩
  have hH := regularizedWeylSum_analytic D hD R hR s (mem_levelFourStrip_of_root D hD s hs)
  have ho : meromorphicOrderAt (regularizedWeylSum D R) s = 0 := by
    rw [hH.meromorphicOrderAt_eq, hH.analyticOrderAt_eq_zero.mpr hN]
    rfl
  have hd : meromorphicOrderAt (continuedWeylSum D R) s =
      meromorphicOrderAt (regularizedWeylSum D R) s -
        meromorphicOrderAt (ratioDenominator D) s := by
    convert! meromorphicOrderAt_div hH.meromorphicAt
      (ratioDenominator_analytic D s).meromorphicAt using 1
  rw [hd, ho, ratioDenominator_order_at_root D hD s hs, zero_sub]

/-- Near a pole the literal series and its continuation have the same punctured germ. -/
theorem weylSum_eventuallyEq_continued (hD : StripCondition D) (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    (fun z => weylSum D (levelFourParameter z) 0 0 (Real.log R)) =ᶠ[𝓝[≠] s]
      continuedWeylSum D R := by
  have hQ : ∀ᶠ z in 𝓝[≠] s, ratioDenominator D z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (ratioDenominator_analytic D s).meromorphicAt).mp
    rw [ratioDenominator_order_at_root D hD s hs]
    exact WithTop.coe_ne_top
  have hS : ∀ᶠ z in 𝓝[≠] s, z ∈ levelFourStrip :=
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_levelFourStrip.mem_nhds (mem_levelFourStrip_of_root D hD s hs))
  have hRe : ∀ᶠ z in 𝓝[≠] s, z.re ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      (Complex.continuous_re.continuousAt.eventually_ne (re_ne_zero_of_root D hD s hs))
  filter_upwards [hQ, hS, hRe] with z hQ hS hRe
  exact weylSum_eq_regularized_div D hD R hR z hS hRe hQ

/-- **Exact pole survival.** For every datum with zeros in the open strip, each zero of
`Z(s + 1)` is a pole of the complete affine Weyl sum of exactly its multiplicity, for all
sufficiently strong degree rotations. -/
theorem weylSum_eventual_order (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      meromorphicOrderAt (fun z => weylSum D (levelFourParameter z) 0 0 (Real.log R)) s =
        -(((numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) : ℤ) : WithTop ℤ) := by
  filter_upwards [continuedWeylSum_eventual_order D hD s hs] with R hR
  refine ⟨hR.1, ?_⟩
  rw [meromorphicOrderAt_congr (weylSum_eventuallyEq_continued D hD R hR.1 s hs)]
  exact hR.2

end CurveDatum

end

end GaloisForLFunctions.RHTower.InfiniteSymmetry
