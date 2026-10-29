import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1FiniteFieldRegularization
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Weights

/-!
# Arithmetic poles survive the complete affine Weyl sum

The degree factor gives normal convergence after clearing the common arithmetic
denominator. As rotation increases, the regularized sum tends to the sum of its
identity and finite simple-reflection coefficients. At a Frobenius pole the first
vanishes and the second does not, so the full pole multiplicity survives.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

open ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- A term of the arithmetic affine Weyl expansion with the actual zeta coefficient. -/
def finiteFieldWeylTerm (lam : ℂ × ℂ) (t z r : ℝ) (w : Weyl) : ℂ :=
  finiteFieldCoefficient lam w * Complex.exp (weylExponent lam t z r w)

/-- The complete infinite affine Weyl expansion, independently of regularization. -/
def finiteFieldWeylSum (lam : ℂ × ℂ) (t z r : ℝ) : ℂ :=
  ∑' w : Weyl, finiteFieldWeylTerm lam t z r w

/-- The same degree factor for both families of the infinite dihedral group. -/
def affineDegreeIndex : Weyl → ℤ
  | .r n => n
  | .sr n => n

lemma exp_weylExponent_levelFour (R : ℝ) (hR : 0 < R) (s : ℂ) (w : Weyl) :
    Complex.exp (weylExponent (levelFourParameter s) 0 0 (Real.log R) w) =
      degreeFourFactor R s (affineDegreeIndex w) := by
  cases w with
  | r n =>
    rw [weylExponent_translation, Real.exp_log hR]
    unfold levelFourParameter degreeFourFactor affineDegreeIndex
    congr 1
    push_cast
    ring
  | sr n =>
    rw [weylExponent_reflection, Real.exp_log hR]
    unfold levelFourParameter degreeFourFactor affineDegreeIndex
    congr 1
    push_cast
    ring

/-- A Weyl summand with the common arithmetic denominator removed. -/
def clearedFiniteFieldWeylTerm (R : ℝ) (s : ℂ) (w : Weyl) : ℂ :=
  clearedFiniteFieldCoefficient w s * degreeFourFactor R s (affineDegreeIndex w)

/-- The holomorphic regularization, written as its two integer-indexed series. -/
def regularizedFiniteFieldWeylSum (R : ℝ) (s : ℂ) : ℂ :=
  degreeFourSeries (fun n => clearedFiniteFieldCoefficient (.r n)) R s +
    degreeFourSeries (fun n => clearedFiniteFieldCoefficient (.sr n)) R s

lemma summable_norm_clearedFiniteFieldWeylTerm (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    Summable (fun w : Weyl => ‖clearedFiniteFieldWeylTerm R s w‖) := by
  obtain ⟨C, _, hb⟩ := exists_clearedFiniteFieldCoefficient_family_bound
  apply DihedralGroup.equivSum.symm.summable_iff.mp
  exact Summable.sum _
    (summable_norm_degreeFourSeries (fun n s hs => (hb n s hs).1) R hR s hs)
    (summable_norm_degreeFourSeries (fun n s hs => (hb n s hs).2) R hR s hs)

private lemma tsum_weyl_two_families (f : Weyl → ℂ)
    (hr : Summable (fun n : ℤ => f (.r n)))
    (hs : Summable (fun n : ℤ => f (.sr n))) :
    (∑' w : Weyl, f w) = (∑' n : ℤ, f (.r n)) + ∑' n : ℤ, f (.sr n) := by
  calc
    _ = ∑' a : ℤ ⊕ ℤ, f (DihedralGroup.equivSum.symm a) :=
      (DihedralGroup.equivSum.symm.tsum_eq f).symm
    _ = _ := hr.tsum_sum hs

lemma regularizedFiniteFieldWeylSum_eq_tsum (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    regularizedFiniteFieldWeylSum R s = ∑' w : Weyl, clearedFiniteFieldWeylTerm R s w := by
  obtain ⟨C, _, hb⟩ := exists_clearedFiniteFieldCoefficient_family_bound
  have hr : Summable (fun n : ℤ => clearedFiniteFieldWeylTerm R s (.r n)) :=
    (summable_norm_degreeFourSeries
      (f := fun n => clearedFiniteFieldCoefficient (.r n))
      (fun n s hs => (hb n s hs).1) R hR s hs).of_norm
  have ht : Summable (fun n : ℤ => clearedFiniteFieldWeylTerm R s (.sr n)) :=
    (summable_norm_degreeFourSeries
      (f := fun n => clearedFiniteFieldCoefficient (.sr n))
      (fun n s hs => (hb n s hs).2) R hR s hs).of_norm
  exact (tsum_weyl_two_families (clearedFiniteFieldWeylTerm R s) hr ht).symm

/-- Normal convergence makes the regularized complete Weyl sum holomorphic. -/
theorem regularizedFiniteFieldWeylSum_analytic (R : ℝ) (hR : 0 < R) :
    AnalyticOnNhd ℂ (regularizedFiniteFieldWeylSum R) levelFourStrip := by
  obtain ⟨C, _, hb⟩ := exists_clearedFiniteFieldCoefficient_family_bound
  exact (degreeFourSeries_analyticOn
    (fun n => clearedFiniteFieldCoefficient_analytic (.r n))
    (fun n s hs => (hb n s hs).1) R hR).add
    (degreeFourSeries_analyticOn
      (fun n => clearedFiniteFieldCoefficient_analytic (.sr n))
      (fun n s hs => (hb n s hs).2) R hR)

lemma finiteFieldWeylTerm_eq_cleared_div (R : ℝ) (hR : 0 < R) (s : ℂ)
    (hs : s ∈ levelFourStrip) (hs0 : s.re ≠ 0)
    (hQ : arithmeticRatioDenominator s ≠ 0) (w : Weyl) :
    finiteFieldWeylTerm (levelFourParameter s) 0 0 (Real.log R) w =
      clearedFiniteFieldWeylTerm R s w / arithmeticRatioDenominator s := by
  rw [finiteFieldWeylTerm, exp_weylExponent_levelFour R hR,
    clearedFiniteFieldWeylTerm, clearedFiniteFieldCoefficient_eq w s hs hs0 hQ]
  field_simp

/-- The original arithmetic Weyl series converges absolutely off its common denominator zeros. -/
theorem summable_norm_finiteFieldWeylTerm_levelFour (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) (hs0 : s.re ≠ 0)
    (hQ : arithmeticRatioDenominator s ≠ 0) :
    Summable (fun w : Weyl => ‖finiteFieldWeylTerm
      (levelFourParameter s) 0 0 (Real.log R) w‖) := by
  simp_rw [finiteFieldWeylTerm_eq_cleared_div R hR s hs hs0 hQ, norm_div]
  exact (summable_norm_clearedFiniteFieldWeylTerm R hR s hs).div_const _

/-- The quotient agrees with the original infinite Weyl expansion wherever both are regular. -/
theorem finiteFieldWeylSum_eq_regularized_div (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : s ∈ levelFourStrip) (hs0 : s.re ≠ 0)
    (hQ : arithmeticRatioDenominator s ≠ 0) :
    finiteFieldWeylSum (levelFourParameter s) 0 0 (Real.log R) =
      regularizedFiniteFieldWeylSum R s / arithmeticRatioDenominator s := by
  rw [finiteFieldWeylSum, regularizedFiniteFieldWeylSum_eq_tsum R hR s hs]
  simp_rw [finiteFieldWeylTerm_eq_cleared_div R hR s hs hs0 hQ]
  exact tsum_div_const

/-- Meromorphic continuation of the complete arithmetic Weyl expansion on the level-four slice. -/
def continuedFiniteFieldWeylSum (R : ℝ) (s : ℂ) : ℂ :=
  regularizedFiniteFieldWeylSum R s / arithmeticRatioDenominator s

theorem continuedFiniteFieldWeylSum_meromorphic (R : ℝ) (hR : 0 < R) :
    MeromorphicOn (continuedFiniteFieldWeylSum R) levelFourStrip := by
  intro s hs
  exact (regularizedFiniteFieldWeylSum_analytic R hR s hs).meromorphicAt.div
    (arithmeticRatioDenominator_analytic s).meromorphicAt

/-- The continuation matches the full convergent series in an open Godement subchamber. -/
theorem continuedFiniteFieldWeylSum_eq_chamber (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hlo : 1 < s.re) (hhi : s.re < 2) :
    continuedFiniteFieldWeylSum R s =
      finiteFieldWeylSum (levelFourParameter s) 0 0 (Real.log R) := by
  exact (finiteFieldWeylSum_eq_regularized_div R hR s
    ⟨by linarith only [hlo], hhi⟩ (by linarith only [hlo])
    (arithmeticRatioDenominator_ne_zero_chamber s hlo)).symm

/-- Strong rotation isolates exactly the identity and finite simple-reflection terms. -/
theorem regularizedFiniteFieldWeylSum_tendsto (s : ℂ) (hs : s ∈ levelFourStrip) :
    Tendsto (fun R : ℝ => regularizedFiniteFieldWeylSum R s) atTop
      (𝓝 (arithmeticRatioDenominator s + arithmeticRatioNumerator s)) := by
  obtain ⟨C, _, hb⟩ := exists_clearedFiniteFieldCoefficient_family_bound
  have h := (degreeFourSeries_tendsto (fun n s hs => (hb n s hs).1) s hs).add
    (degreeFourSeries_tendsto (fun n s hs => (hb n s hs).2) s hs)
  change Tendsto (fun R => regularizedFiniteFieldWeylSum R s) atTop
    (𝓝 (clearedFiniteFieldCoefficient 1 s +
      clearedFiniteFieldCoefficient finiteReflection s)) at h
  simpa only [clearedFiniteFieldCoefficient_one,
    clearedFiniteFieldCoefficient_finiteReflection] using h

/-- Every arithmetic zero lies inside the common continuation strip. -/
lemma mem_levelFourStrip_of_arithmetic_root (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) : s ∈ levelFourStrip := by
  constructor <;> rw [arithmeticZetaRatio_zero_re s hs] <;> norm_num

/-- At an arithmetic pole, the leading regularized term is nonzero. -/
theorem regularizedFiniteFieldWeylSum_eventually_ne_zero (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    ∀ᶠ R : ℝ in atTop, regularizedFiniteFieldWeylSum R s ≠ 0 := by
  have ht := regularizedFiniteFieldWeylSum_tendsto s
    (mem_levelFourStrip_of_arithmetic_root s hs)
  rw [arithmeticRatioDenominator_zero_at_root s hs, zero_add] at ht
  exact ht.eventually_ne (arithmeticRatioNumerator_ne_zero_at_root s hs)

/-- For every sufficiently strong rotation, the full continued sum retains the exact root order. -/
theorem continuedFiniteFieldWeylSum_eventual_order (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      meromorphicOrderAt (continuedFiniteFieldWeylSum R) s =
        -((numerator.rootMultiplicity (zetaCoordinate (s + 1)) : ℤ) : WithTop ℤ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    regularizedFiniteFieldWeylSum_eventually_ne_zero s hs] with R hR hN
  refine ⟨hR, ?_⟩
  have hH := regularizedFiniteFieldWeylSum_analytic R hR s
    (mem_levelFourStrip_of_arithmetic_root s hs)
  have ho : meromorphicOrderAt (regularizedFiniteFieldWeylSum R) s = 0 := by
    rw [hH.meromorphicOrderAt_eq, hH.analyticOrderAt_eq_zero.mpr hN]
    rfl
  have hd : meromorphicOrderAt (continuedFiniteFieldWeylSum R) s =
      meromorphicOrderAt (regularizedFiniteFieldWeylSum R) s -
        meromorphicOrderAt arithmeticRatioDenominator s := by
    convert! meromorphicOrderAt_div hH.meromorphicAt
      (arithmeticRatioDenominator_analytic s).meromorphicAt using 1
  rw [hd, ho, arithmeticRatioDenominator_order_at_root s hs, zero_sub]

/-- The literal Weyl sum and its continuation have the same punctured germ at an arithmetic pole. -/
theorem finiteFieldWeylSum_eventuallyEq_continued (R : ℝ) (hR : 0 < R)
    (s : ℂ) (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    (fun z => finiteFieldWeylSum (levelFourParameter z) 0 0 (Real.log R)) =ᶠ[𝓝[≠] s]
      continuedFiniteFieldWeylSum R := by
  have hQ : ∀ᶠ z in 𝓝[≠] s, arithmeticRatioDenominator z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (arithmeticRatioDenominator_analytic s).meromorphicAt).mp
    rw [arithmeticRatioDenominator_order_at_root s hs]
    exact WithTop.coe_ne_top
  have hS : ∀ᶠ z in 𝓝[≠] s, z ∈ levelFourStrip :=
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_levelFourStrip.mem_nhds (mem_levelFourStrip_of_arithmetic_root s hs))
  have hzero : s.re ≠ 0 := by rw [arithmeticZetaRatio_zero_re s hs]; norm_num
  have hRe : ∀ᶠ z in 𝓝[≠] s, z.re ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      (Complex.continuous_re.continuousAt.eventually_ne hzero)
  filter_upwards [hQ, hS, hRe] with z hQ hS hRe
  exact finiteFieldWeylSum_eq_regularized_div R hR z hS hRe hQ

/-- Noncancellation is a theorem about the complete infinite series, with the original multiplicity. -/
theorem finiteFieldWeylSum_eventual_order (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      meromorphicOrderAt (fun z => finiteFieldWeylSum
        (levelFourParameter z) 0 0 (Real.log R)) s =
        -((numerator.rootMultiplicity (zetaCoordinate (s + 1)) : ℤ) : WithTop ℤ) := by
  filter_upwards [continuedFiniteFieldWeylSum_eventual_order s hs] with R hR
  refine ⟨hR.1, ?_⟩
  rw [meromorphicOrderAt_congr (finiteFieldWeylSum_eventuallyEq_continued R hR.1 s hs)]
  exact hR.2

/-- Every actual Frobenius zero survives in the full affine Weyl sum at large integral rotations. -/
theorem finiteFieldWeylSum_integral_rotation_poles (i : FrobeniusIndex) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < (d : ℝ) * Real.log 3 ∧
      meromorphicOrderAt (fun z => finiteFieldWeylSum (levelFourParameter z) 0 0
        (Real.log ((d : ℝ) * Real.log 3))) (arithmeticPoleParameter i) =
        -((numerator.rootMultiplicity (zetaCoordinate (arithmeticPoleParameter i + 1)) : ℤ) :
          WithTop ℤ) ∧
      meromorphicOrderAt (fun z => finiteFieldWeylSum (levelFourParameter z) 0 0
        (Real.log ((d : ℝ) * Real.log 3))) (arithmeticPoleParameter i) < 0 := by
  have ht : Tendsto (fun d : ℕ => (d : ℝ) * Real.log 3) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos log_three_pos).mpr tendsto_natCast_atTop_atTop
  have he := ht.eventually (finiteFieldWeylSum_eventual_order
    (arithmeticPoleParameter i) (arithmeticPoleParameter_zero i))
  apply eventually_atTop.mp
  filter_upwards [he] with d hd
  refine ⟨hd.1, hd.2, ?_⟩
  rw [hd.2, ← arithmeticZetaRatio_order_at_zero _ (arithmeticPoleParameter_zero i)]
  exact (arithmeticPoleParameter_spec i).2

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
