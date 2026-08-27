import GaloisForLFunctions.HilbertMetric.ReflectionSixthJet
import GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure
import GaloisForLFunctions.RHTower.ThetaSingleGibbsLikelihoodSingleLossClosure
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSeamJets

/-!
# Positive reflected sixth-curvature chamber at the theta modular seam

The self-dual four-state theta ODE closes not only the Gaussian-aperture sixth seam but also
the reflected second--sixth Hankel invariant.  Its exact degree-eight polynomial is positive in
the bounded chamber occupied by the actual theta-nullwert.  This gives an unconditional strict
source theorem at the modular seam and, by smoothness, on a nontrivial open source interval.

No zero data or Riemann-hypothesis premise enters the argument.  The upper edge of the modular
chamber comes from the existing exact rational enclosure of `exp (-pi)` and a geometric majorant
for the theta mass.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial HurwitzZeta

namespace RHTower

noncomputable section

/-- Exact upper enclosure for the self-dual theta mass. -/
theorem thetaCuspSelfDualThetaMass_lt_one_point_zero_nine_one :
    thetaCuspSelfDualThetaMass < (1091 / 1000 : ℝ) := by
  let q : ℝ := (0.0432139182638 : ℝ)
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hqexp : Real.exp (-Real.pi) ≤ q := by
    simpa [q] using exp_neg_pi_rationalEnclosure_upper
  have hterm (n : ℕ) :
      Real.exp (-Real.pi * (n + 1) ^ 2) ≤ q ^ (n + 1) := by
    calc
      Real.exp (-Real.pi * (n + 1) ^ 2) =
          Real.exp (-Real.pi) ^ ((n + 1) ^ 2) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
      _ ≤ q ^ ((n + 1) ^ 2) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hqexp _
      _ ≤ q ^ (n + 1) :=
        pow_le_pow_of_le_one hq0 hq1.le (by
          have hn : 0 ≤ n := Nat.zero_le n
          nlinarith [sq_nonneg (n : ℝ)])
  have hs0 := hasSum_nat_cosKernel₀ 0 (by norm_num : (0 : ℝ) < 1)
  have hs : HasSum (fun n : ℕ =>
      2 * Real.exp (-Real.pi * (n + 1) ^ 2))
      (thetaCuspSelfDualThetaMass - 1) := by
    have hs' : HasSum (fun n : ℕ =>
        2 * Real.exp (-Real.pi * (n + 1) ^ 2 * 1))
        (cosKernel (0 : UnitAddCircle) 1 - 1) := by
      simpa using hs0
    rw [← congrFun evenKernel_eq_cosKernel_of_zero (1 : ℝ)] at hs'
    simpa [thetaCuspSelfDualThetaMass] using hs'
  have hgeom : Summable (fun n : ℕ => 2 * q ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_right q).mul_left 2
  have hsum : thetaCuspSelfDualThetaMass - 1 ≤
      ∑' n : ℕ, 2 * q ^ (n + 1) := by
    rw [← hs.tsum_eq]
    exact hs.summable.tsum_le_tsum (fun n => by
      gcongr
      exact hterm n) hgeom
  rw [show (∑' n : ℕ, 2 * q ^ (n + 1)) = 2 * q / (1 - q) by
    rw [show (fun n : ℕ => 2 * q ^ (n + 1)) =
        fun n => (2 * q) * q ^ n by
      funext n
      rw [pow_succ]
      ring,
      tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    ring] at hsum
  norm_num [q] at hsum ⊢
  linarith

/-- The actual squared modular scale lies below `20`. -/
theorem thetaCuspSelfDualModularScale_sq_lt_twenty :
    thetaCuspSelfDualModularScale ^ 2 < (20 : ℝ) := by
  have hp : Real.pi < (22 / 7 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    linarith
  have hm := thetaCuspSelfDualThetaMass_lt_one_point_zero_nine_one
  have hm0 : 0 ≤ thetaCuspSelfDualThetaMass := by
    have hlow :=
      thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
    linarith
  rw [thetaCuspSelfDualModularScale]
  calc
    (Real.pi * thetaCuspSelfDualThetaMass ^ 4) ^ 2 =
        Real.pi ^ 2 * thetaCuspSelfDualThetaMass ^ 8 := by ring
    _ < (22 / 7 : ℝ) ^ 2 * (1091 / 1000 : ℝ) ^ 8 := by gcongr
    _ < (20 : ℝ) := by norm_num

/-- The reflected degree-eight modular polynomial is positive on the theta chamber
`191/10 ≤ X ≤ 20`. -/
theorem thetaCuspReflectedSixthSeamModularPolynomial_pos_of_chamber
    {X : ℝ} (hlo : (191 / 10 : ℝ) ≤ X) (hhi : X ≤ 20) :
    0 < thetaCuspReflectedSixthSeamModularPolynomial X := by
  let y := X - (191 / 10 : ℝ)
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; linarith
  have hX : X = (191 / 10 : ℝ) + y := by dsimp [y]; ring
  have hy6 : y ^ 6 ≤ 1 := by
    calc
      y ^ 6 ≤ (1 : ℝ) ^ 6 := pow_le_pow_left₀ hy0 hy1 6
      _ = 1 := by norm_num
  have hy7 : y ^ 7 ≤ 1 := by
    calc
      y ^ 7 ≤ (1 : ℝ) ^ 7 := pow_le_pow_left₀ hy0 hy1 7
      _ = 1 := by norm_num
  have hy8 : y ^ 8 ≤ 1 := by
    calc
      y ^ 8 ≤ (1 : ℝ) ^ 8 := pow_le_pow_left₀ hy0 hy1 8
      _ = 1 := by norm_num
  rw [hX]
  rw [show thetaCuspReflectedSixthSeamModularPolynomial
      ((191 / 10 : ℝ) + y) =
      24080301935046283533 / 26843545600000 +
        y * (100396126421717439 / 335544320000) +
        y ^ 2 * (2671351074244743 / 67108864000) +
        y ^ 3 * (8843821683429 / 3355443200) +
        y ^ 4 * (21967078659 / 268435456) +
        y ^ 5 * (7860801 / 33554432) -
        y ^ 6 * (1949685 / 33554432) -
        y ^ 7 * (12525 / 8388608) -
        y ^ 8 * (375 / 33554432) by
      unfold thetaCuspReflectedSixthSeamModularPolynomial
      ring]
  have hpos1 : 0 ≤ y * (100396126421717439 / 335544320000 : ℝ) := by positivity
  have hpos2 : 0 ≤ y ^ 2 * (2671351074244743 / 67108864000 : ℝ) := by positivity
  have hpos3 : 0 ≤ y ^ 3 * (8843821683429 / 3355443200 : ℝ) := by positivity
  have hpos4 : 0 ≤ y ^ 4 * (21967078659 / 268435456 : ℝ) := by positivity
  have hpos5 : 0 ≤ y ^ 5 * (7860801 / 33554432 : ℝ) := by positivity
  nlinarith

/-- The actual self-dual theta scale occupies the positive reflected chamber. -/
theorem thetaCuspReflectedSixthSeamModularPolynomial_source_pos :
    0 < thetaCuspReflectedSixthSeamModularPolynomial
      (thetaCuspSelfDualModularScale ^ 2) :=
  thetaCuspReflectedSixthSeamModularPolynomial_pos_of_chamber
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
    thetaCuspSelfDualModularScale_sq_lt_twenty.le

/-- The source-specialized reflected modular-closure value is strictly positive. -/
theorem thetaCuspReflectedSixthSeamModularClosureValue_pos :
    0 < thetaCuspReflectedSixthSeamModularClosureValue := by
  rw [thetaCuspReflectedSixthSeamModularClosureValue]
  have hm : 0 < thetaCuspSelfDualThetaMass := by
    linarith [
      thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand]
  exact mul_pos (pow_pos hm 4)
    thetaCuspReflectedSixthSeamModularPolynomial_source_pos

/-- Raw reflected second--sixth invariant of the complete theta source. -/
def thetaCuspFullSourceReflectionSecondSixthCurvature (x : ℝ) : ℝ :=
  let f : ℕ → ℝ := fun n => iteratedDeriv n thetaCuspFullSource x
  HilbertMetric.reflectedProductSecondJet (f 0) (f 1) (f 2) *
      HilbertMetric.reflectedProductSixthJet
        (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) -
    HilbertMetric.reflectedProductFourthJet
      (f 0) (f 1) (f 2) (f 3) (f 4) ^ 2

/-- At the modular seam, raw reflected curvature is four times the modular invariant. -/
theorem thetaCuspFullSourceReflectionSecondSixthCurvature_zero_eq :
    thetaCuspFullSourceReflectionSecondSixthCurvature 0 =
      4 * thetaCuspReflectedSixthSeamModularClosureValue := by
  have h1 : iteratedDeriv 1 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by norm_num)
  have h3 : iteratedDeriv 3 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by norm_num)
  have h5 : iteratedDeriv 5 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by norm_num)
  rw [thetaCuspFullSourceReflectionSecondSixthCurvature]
  dsimp only
  rw [h1, h3, h5]
  calc
    HilbertMetric.reflectedProductSecondJet
          (iteratedDeriv 0 thetaCuspFullSource 0) 0
          (iteratedDeriv 2 thetaCuspFullSource 0) *
        HilbertMetric.reflectedProductSixthJet
          (iteratedDeriv 0 thetaCuspFullSource 0) 0
          (iteratedDeriv 2 thetaCuspFullSource 0) 0
          (iteratedDeriv 4 thetaCuspFullSource 0) 0
          (iteratedDeriv 6 thetaCuspFullSource 0) -
        HilbertMetric.reflectedProductFourthJet
          (iteratedDeriv 0 thetaCuspFullSource 0) 0
          (iteratedDeriv 2 thetaCuspFullSource 0) 0
          (iteratedDeriv 4 thetaCuspFullSource 0) ^ 2 =
      4 * (iteratedDeriv 0 thetaCuspFullSource 0 ^ 2 *
          (iteratedDeriv 2 thetaCuspFullSource 0 *
              iteratedDeriv 6 thetaCuspFullSource 0 -
            iteratedDeriv 4 thetaCuspFullSource 0 ^ 2) +
        9 * iteratedDeriv 0 thetaCuspFullSource 0 *
          iteratedDeriv 2 thetaCuspFullSource 0 ^ 2 *
          iteratedDeriv 4 thetaCuspFullSource 0 -
        9 * iteratedDeriv 2 thetaCuspFullSource 0 ^ 4) := by
          unfold HilbertMetric.reflectedProductSecondJet
            HilbertMetric.reflectedProductFourthJet
            HilbertMetric.reflectedProductSixthJet
          ring
    _ = 4 * thetaCuspReflectedSixthSeamModularClosureValue := by
      rw [thetaCuspFullSource_reflectedSixthSeam_eq_modularClosure]

/-- Strict reflected second--sixth source curvature at the modular seam. -/
theorem thetaCuspFullSourceReflectionSecondSixthCurvature_zero_pos :
    0 < thetaCuspFullSourceReflectionSecondSixthCurvature 0 := by
  rw [thetaCuspFullSourceReflectionSecondSixthCurvature_zero_eq]
  nlinarith [thetaCuspReflectedSixthSeamModularClosureValue_pos]

/-- Reflected second--sixth source curvature varies continuously with source coordinate. -/
theorem continuous_thetaCuspFullSourceReflectionSecondSixthCurvature :
    Continuous thetaCuspFullSourceReflectionSecondSixthCurvature := by
  have hj (n : ℕ) : Continuous (iteratedDeriv n thetaCuspFullSource) := by
    rw [iteratedDeriv_thetaCuspFullSource]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspFullDerivative n x).continuousAt
  unfold thetaCuspFullSourceReflectionSecondSixthCurvature
    HilbertMetric.reflectedProductSecondJet
    HilbertMetric.reflectedProductFourthJet
    HilbertMetric.reflectedProductSixthJet
  fun_prop

/-- Nontrivial open theta-source chamber with strict reflected second--sixth curvature. -/
theorem exists_thetaCuspFullSourceReflectionSecondSixthCurvature_pos_near_zero :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : ℝ, |x| < delta →
      0 < thetaCuspFullSourceReflectionSecondSixthCurvature x := by
  have hev : ∀ᶠ x : ℝ in 𝓝 0,
      0 < thetaCuspFullSourceReflectionSecondSixthCurvature x :=
    continuous_thetaCuspFullSourceReflectionSecondSixthCurvature.continuousAt.eventually
      (eventually_gt_nhds thetaCuspFullSourceReflectionSecondSixthCurvature_zero_pos)
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨delta, hdelta, fun x hx => hball ?_⟩
  simpa [Real.dist_eq] using hx

end


end RHTower
