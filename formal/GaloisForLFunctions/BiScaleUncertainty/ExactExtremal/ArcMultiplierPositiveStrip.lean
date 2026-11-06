import GaloisForLFunctions.BiScaleUncertainty.ExactExtremal.QuadraticProductPositiveStrip
import GaloisForLFunctions.RHTower.TwistedArcNullLaplacePositivity

/-!
# A positive-real strip for every twisted-arc multiplier

The constant coefficient controls a disc of radius three halves. Outside that
disc, the quadratic products remain in the right half-plane. Their overlap
gives a strip wider than the critical strip and admits a single analytic square root.
-/

open Complex MeasureTheory Set Filter Topology Finset
open scoped Nat ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

open _root_.RHTower _root_.RHTower.WeilSpectral

noncomputable section

def arcSpectralWeight (ν : Measure ArcParam) (j : ℕ) : ℝ :=
  arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j

def arcSpectralMultiplier (ν : Measure ArcParam) (z : ℂ) : ℂ :=
  arcGammaMultiplier (arcSpectralWeight ν) (1 / 2 + z * I)

theorem arcSpectralWeight_nonneg (ν : Measure ArcParam) (j : ℕ) :
    0 ≤ arcSpectralWeight ν j :=
  arcGammaWeight_nonneg (twArcEvenMoment_one_nonneg' ν j) j

theorem arcSpectralWeight_zero (ν : Measure ArcParam) :
    arcSpectralWeight ν 0 = 4 * Real.sqrt 2 * twArcEvenMoment ν (fun _ => 1) 0 := by
  simp [arcSpectralWeight, arcGammaWeight]

theorem summable_arcSpectralWeight (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Summable fun j => arcSpectralWeight ν j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
  summable_arcGammaWeight (M := twArcEvenMoment ν (fun _ => 1) 0) (twArcEvenMoment_one_nonneg' ν)
    (fun j => by simpa only [mul_comm] using twArcEvenMoment_one_le_mul_zero ν j)

private theorem spectralCoordinate_left (z : ℂ) : -I * (1 / 2 + z * I - 1 / 2) = z := by
  ring_nf
  rw [I_sq]
  ring

private theorem spectralCoordinate_right (z : ℂ) : I * (1 / 2 + z * I - 1 / 2) = -z := by
  ring_nf
  rw [I_sq]
  ring

theorem arcSpectralMultiplier_eq_tsum (ν : Measure ArcParam) (z : ℂ) :
    arcSpectralMultiplier ν z = ∑' j, (arcSpectralWeight ν j : ℂ) *
      (shiftedGammaPoly j z * shiftedGammaPoly j (-z)) := by
  simp only [arcSpectralMultiplier, arcGammaMultiplier,
    spectralCoordinate_left, spectralCoordinate_right]

theorem summable_arcSpectralTerm (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {z : ℂ} (hz : |z.im| ≤ 3 / 2) :
    Summable fun j => (arcSpectralWeight ν j : ℂ) *
      (shiftedGammaPoly j z * shiftedGammaPoly j (-z)) := by
  have hs := summable_norm_arcGammaMultiplier_term (arcSpectralWeight_nonneg ν)
    (summable_arcSpectralWeight ν) (s := 1 / 2 + z * I) (by simpa using hz)
  simp only [spectralCoordinate_left, spectralCoordinate_right] at hs
  exact hs.of_norm

theorem differentiableAt_arcSpectralMultiplier (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {z : ℂ} (hz : |z.im| < 3 / 2) : DifferentiableAt ℂ (arcSpectralMultiplier ν) z :=
  (differentiableAt_arcGammaMultiplier (arcSpectralWeight_nonneg ν)
    (summable_arcSpectralWeight ν) (by simpa using hz)).comp z (by fun_prop)

theorem norm_arcSpectralMultiplier_le (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {z : ℂ} (hz : |z.im| ≤ 3 / 2) :
    ‖arcSpectralMultiplier ν z‖ ≤
      9 * (∑' j, arcSpectralWeight ν j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) *
        Real.exp (Real.log 3 * |z.re|) := by
  simpa [arcSpectralMultiplier] using
    norm_arcGammaMultiplier_le (arcSpectralWeight_nonneg ν)
      (summable_arcSpectralWeight ν) (s := 1 / 2 + z * I) (by simpa using hz)

theorem arcSpectralMultiplier_even (ν : Measure ArcParam) (z : ℂ) :
    arcSpectralMultiplier ν (-z) = arcSpectralMultiplier ν z := by
  rw [arcSpectralMultiplier_eq_tsum, arcSpectralMultiplier_eq_tsum]
  apply tsum_congr
  intro j
  rw [neg_neg, mul_comm (shiftedGammaPoly j (-z))]

theorem shiftedGammaPair_eq_product (j : ℕ) (z : ℂ) :
    shiftedGammaPoly j z * shiftedGammaPoly j (-z) =
      ∏ k ∈ range j, (((k : ℂ) + 1 / 4) ^ 2 + z ^ 2 / 4) := by
  unfold shiftedGammaPoly
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro k _
  ring_nf
  rw [I_sq]
  ring

private theorem norm_shiftedGammaPoly_le_factorial_of_norm_le (j : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 3 / 2) : ‖shiftedGammaPoly j z‖ ≤ (j ! : ℝ) := by
  unfold shiftedGammaPoly
  rw [norm_prod, ← prod_range_add_one_eq_factorial, Nat.cast_prod]
  apply prod_le_prod (fun _ _ => norm_nonneg _)
  intro k _
  have h1 := norm_add_le ((k : ℂ) + 1 / 4) (I * z / 2)
  have h2 := norm_add_le (k : ℂ) (1 / 4)
  norm_num [norm_mul, norm_div] at h1 h2 ⊢
  linarith only [h1, h2, hz]

private theorem norm_arcSpectralTerm_le (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) (j : ℕ) :
    ‖(arcSpectralWeight ν j : ℂ) * (shiftedGammaPoly j z * shiftedGammaPoly j (-z))‖ ≤
      4 * Real.sqrt 2 * twArcEvenMoment ν (fun _ => 1) 0 *
        (3 / 2 * (1 / 3 : ℝ) ^ j) := by
  let m := twArcEvenMoment ν (fun _ => 1)
  have hm0 : 0 ≤ m 0 := twArcEvenMoment_one_nonneg' ν 0
  have hmj : 0 ≤ m j := twArcEvenMoment_one_nonneg' ν j
  have hle := twArcEvenMoment_one_le_mul_zero ν j
  have hQ := norm_shiftedGammaPoly_le_factorial_of_norm_le j hz
  have hQn := norm_shiftedGammaPoly_le_factorial_of_norm_le j (z := -z) (by simpa using hz)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (arcSpectralWeight_nonneg ν j)]
  calc
    arcSpectralWeight ν j * (‖shiftedGammaPoly j z‖ * ‖shiftedGammaPoly j (-z)‖) ≤
        arcGammaWeight ((1 / 4 : ℝ) ^ j * m 0) j * (j ! : ℝ) ^ 2 := by
      apply mul_le_mul
      · unfold arcSpectralWeight arcGammaWeight
        gcongr
      · simpa only [pow_two] using mul_le_mul hQ hQn (norm_nonneg _) (by positivity)
      · positivity
      · unfold arcGammaWeight
        positivity
    _ = 4 * Real.sqrt 2 * m 0 * ((j ! : ℝ) ^ 2 / ((2 * j)! : ℝ)) := by
      have h4 : (4 : ℝ) ^ j * (1 / 4) ^ j = 1 := by rw [← mul_pow]; norm_num
      unfold arcGammaWeight
      calc _ = 4 * Real.sqrt 2 * m 0 * ((4 : ℝ) ^ j * (1 / 4) ^ j) *
          ((j ! : ℝ) ^ 2 / ((2 * j)! : ℝ)) := by ring
        _ = _ := by rw [h4, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_sq_div_factorial_two_mul_le j) (by positivity)

private theorem re_arcSpectralMultiplier_ge_on_disc (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 2) :
    Real.sqrt 2 * twArcEvenMoment ν (fun _ => 1) 0 ≤ (arcSpectralMultiplier ν z).re := by
  let m0 := twArcEvenMoment ν (fun _ => 1) 0
  let f : ℕ → ℂ := fun j => (arcSpectralWeight ν j : ℂ) *
    (shiftedGammaPoly j z * shiftedGammaPoly j (-z))
  have hs : Summable f := summable_arcSpectralTerm ν ((Complex.abs_im_le_norm z).trans hz)
  have hsn := (hs.comp_injective (add_left_injective 1)).norm
  have hgeo : Summable fun j : ℕ => 4 * Real.sqrt 2 * m0 *
      (3 / 2 * (1 / 3 : ℝ) ^ (j + 1)) :=
    (((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1)).comp_injective
      (add_left_injective 1)).mul_left (3 / 2)).mul_left _
  have hval : (∑' j : ℕ, 4 * Real.sqrt 2 * m0 *
      (3 / 2 * (1 / 3 : ℝ) ^ (j + 1))) = 3 * Real.sqrt 2 * m0 := by
    have he (j : ℕ) : 4 * Real.sqrt 2 * m0 * (3 / 2 * (1 / 3 : ℝ) ^ (j + 1)) =
        2 * Real.sqrt 2 * m0 * (1 / 3 : ℝ) ^ j := by ring
    simp_rw [he]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  have htail : ‖∑' j, f (j + 1)‖ ≤ 3 * Real.sqrt 2 * m0 := by
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    rw [← hval]
    exact Summable.tsum_le_tsum (fun j => norm_arcSpectralTerm_le ν hz (j + 1)) hsn hgeo
  have h0 : f 0 = (4 * Real.sqrt 2 * m0 : ℝ) := by
    simp [f, shiftedGammaPoly, arcSpectralWeight_zero, m0]
  have he : arcSpectralMultiplier ν z = f 0 + ∑' j, f (j + 1) := by
    rw [arcSpectralMultiplier_eq_tsum]
    exact hs.tsum_eq_zero_add
  have hlow := Complex.re_le_norm (-(∑' j, f (j + 1)))
  simp only [Complex.neg_re, norm_neg] at hlow
  rw [he, h0, Complex.add_re, Complex.ofReal_re]
  linarith only [hlow, htail]

private theorem re_arcSpectralMultiplier_ge_far (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {z : ℂ} (hx : 7 / 5 ≤ |z.re|) (hy : |z.im| ≤ 501 / 1000) :
    arcSpectralWeight ν 0 ≤ (arcSpectralMultiplier ν z).re := by
  let f : ℕ → ℂ := fun j => (arcSpectralWeight ν j : ℂ) *
    (shiftedGammaPoly j z * shiftedGammaPoly j (-z))
  have hs : Summable f := summable_arcSpectralTerm ν (by linarith only [hy])
  have hpos (j : ℕ) : 0 ≤ (f j).re := by
    dsimp only [f]
    rw [Complex.re_ofReal_mul, shiftedGammaPair_eq_product]
    exact mul_nonneg (arcSpectralWeight_nonneg ν j) (re_shifted_quadratic_product_pos hx hy j).le
  have ht : 0 ≤ (∑' j, f (j + 1)).re := by
    have hs' : Summable (fun j => f (j + 1)) := hs.comp_injective (add_left_injective 1)
    rw [Complex.re_tsum hs']
    exact tsum_nonneg fun j => hpos (j + 1)
  have h0 : f 0 = (arcSpectralWeight ν 0 : ℂ) := by simp [f, shiftedGammaPoly]
  have he : arcSpectralMultiplier ν z = f 0 + ∑' j, f (j + 1) := by
    rw [arcSpectralMultiplier_eq_tsum]
    exact hs.tsum_eq_zero_add
  rw [he, h0, Complex.add_re, Complex.ofReal_re]
  linarith only [ht]

/-- Every probability measure on the arc gives a multiplier with positive real part
through height `501/1000`, uniformly along the real direction. -/
theorem arcSpectralMultiplier_re_pos (μ : ProbabilityMeasure ArcParam) {z : ℂ}
    (hy : |z.im| ≤ 501 / 1000) : 0 < (arcSpectralMultiplier (μ : Measure ArcParam) z).re := by
  have hm := twArcEvenMoment_one_zero_pos μ
  by_cases hx : |z.re| ≤ 7 / 5
  · have hxsq := pow_le_pow_left₀ (abs_nonneg z.re) hx 2
    have hysq := pow_le_pow_left₀ (abs_nonneg z.im) hy 2
    rw [sq_abs] at hxsq hysq
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hz : ‖z‖ ≤ 3 / 2 := by nlinarith only [hxsq, hysq, hnorm, norm_nonneg z]
    exact (mul_pos (by positivity) hm).trans_le
      (re_arcSpectralMultiplier_ge_on_disc (μ : Measure ArcParam) hz)
  · have hl := re_arcSpectralMultiplier_ge_far (μ : Measure ArcParam) (le_of_not_ge hx) hy
    rw [arcSpectralWeight_zero] at hl
    exact (mul_pos (by positivity) hm).trans_le hl

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal
