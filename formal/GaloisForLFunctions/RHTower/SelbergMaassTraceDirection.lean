import GaloisForLFunctions.RHTower.SelbergMaassTraceRadial

/-!
# Actual Maass family directions, weighted means, and separation

Normalize the literal finite congruence family by its trace amplitude. Reconstruction
and modular permutation covariance hold even at common zeros. On the positive-density
locus its actual derivative energy is precisely the radial-subtracted source energy
with the density weight retained.

The original complex constant-term theorem gives amplitude-weighted zero direction
means. Actual continuity and nonvanishing force negative correlation and squared
normalized chord distance strictly greater than two within a level period. The weighted
mean squared chord distance is exactly twice the amplitude mean, including common zeros.

These are actual-source constraints, not a nonnegative core/Bessel lower bound. No
regularity of normalized direction at common zeros and no Selberg conclusion is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceDirection
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceRadial SelbergMaassTraceBoundary
  SelbergMaassMean SelbergMaassCuspTransport SelbergEulerDecay
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Literal finite-family direction, with Lean's zero division at common zeros. -/
def direction (q : Deck N) (z : ℍ) : ℂ :=
  (quotientForm N f q).1.1 z / (Real.sqrt (density N f z) : ℂ)

/-- Every actual component vanishes at a common trace zero. -/
theorem component_zero_of_density_zero (z : ℍ) (hz : density N f z = 0) (q : Deck N) :
    (quotientForm N f q).1.1 z = 0 := by
  apply Complex.normSq_eq_zero.mp
  apply le_antisymm _ (Complex.normSq_nonneg _)
  have h := Finset.single_le_sum (f := fun r : Deck N =>
    normSq ((quotientForm N f r).1.1 z)) (fun r _ => normSq_nonneg _) (Finset.mem_univ q)
  exact h.trans (le_of_eq hz)

/-- Exact source reconstruction, including its common zeros. -/
theorem amplitude_mul_direction (q : Deck N) (z : ℍ) :
    (Real.sqrt (density N f z) : ℂ) * direction N f q z = (quotientForm N f q).1.1 z := by
  by_cases hz : density N f z = 0
  · simp [direction, hz, component_zero_of_density_zero N f z hz q]
  · unfold direction
    have hr : (Real.sqrt (density N f z) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (lt_of_le_of_ne (density_nonneg N f z) (Ne.symm hz))).ne'
    field_simp

/-- At positive density the actual normalized family has unit squared norm. -/
theorem direction_normSq (z : ℍ) (hz : 0 < density N f z) :
    (∑ q : Deck N, normSq (direction N f q z)) = 1 := by
  simp only [direction, normSq_div, normSq_ofReal, ← Finset.sum_div]
  rw [← pow_two, Real.sq_sqrt hz.le]
  exact div_self hz.ne'

/-- Modular transport permutes the actual normalized components. -/
theorem direction_equivariant (q : Deck N) (A : SL2Z) (z : ℍ) :
    direction N f q (A • z) = direction N f (q * QuotientGroup.mk A) z := by
  unfold direction
  rw [density_invariant, quotientForm_mul, translate_apply]

/-- Real correlation of two literal finite-family source values. -/
def correlation (z w : ℍ) : ℝ :=
  ∑ q : Deck N, ((quotientForm N f q).1.1 w * (starRingEnd ℂ) ((quotientForm N f q).1.1 z)).re

/-- The diagonal correlation is exactly the actual trace density. -/
theorem correlation_self (z : ℍ) : correlation N f z z = density N f z := by
  simp [correlation, density, Complex.mul_conj]

/-- Correlation vanishes when its second source value is a common zero. -/
theorem correlation_zero_of_density_zero (z w : ℍ) (hw : density N f w = 0) :
    correlation N f z w = 0 := by
  simp [correlation, component_zero_of_density_zero N f w hw]

/-- Every actual translated Maass component retains its complex mean on every level period. -/
theorem component_mean_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (q : Deck N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ), (quotientForm N f q).1.1 (ofComplex (point x y))) = 0 := by
  have hp : Function.Periodic (fun x => (quotientForm N f q).1.1 (ofComplex (point x y)))
      ((N + 1 : ℕ) : ℝ) := fun x => maass_periodic N (quotientForm N f q) x hy
  rw [hp.intervalIntegral_add_eq a 0, zero_add,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))]
  have hz : (ofComplex (point 0 y)).im = y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point]
  simpa only [maassMean, periodIntegral, Function.comp_def, hz] using
    maassMean_subquarter_zero N lam (quotientForm N f q) (ofComplex (point 0 y))

/-- Normalization preserves the actual zero mean with its amplitude weight. -/
theorem weighted_direction_mean_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (q : Deck N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      (Real.sqrt (density N f (ofComplex (point x y))) : ℂ) *
        direction N f q (ofComplex (point x y))) = 0 := by
  simp_rw [amplitude_mul_direction]
  exact component_mean_zero N lam f q hy a

/-- A correlation against any fixed actual source value has zero mean on every level period. -/
theorem correlation_mean_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (z : ℍ) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ), correlation N f z (ofComplex (point x y))) = 0 := by
  have hc (q : Deck N) := slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy
  have hint (q : Deck N) : IntervalIntegrable
      (fun x => ((quotientForm N f q).1.1 (ofComplex (point x y)) *
        (starRingEnd ℂ) ((quotientForm N f q).1.1 z)).re) volume a (a + (N + 1 : ℕ)) :=
    (Complex.continuous_re.comp ((hc q).mul continuous_const)).intervalIntegrable _ _
  unfold correlation
  rw [intervalIntegral.integral_finsetSum (fun q _ => hint q)]
  apply Finset.sum_eq_zero
  intro q _
  have hci : IntervalIntegrable (fun x =>
      (quotientForm N f q).1.1 (ofComplex (point x y)) *
        (starRingEnd ℂ) ((quotientForm N f q).1.1 z)) volume a (a + (N + 1 : ℕ)) :=
    ((hc q).mul continuous_const).intervalIntegrable _ _
  have h := Complex.reCLM.intervalIntegral_comp_comm hci
  change (∫ x in a..a + (N + 1 : ℕ),
    Complex.reCLM ((quotientForm N f q).1.1 (ofComplex (point x y)) *
      (starRingEnd ℂ) ((quotientForm N f q).1.1 z))) = 0
  rw [h, intervalIntegral.integral_mul_const, component_mean_zero N lam f q hy a]
  simp

/-- Original nonzero source correlation forces a negative correlation within a centered level period. -/
theorem exists_negative_correlation (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (z : ℍ) (hz : 0 < density N f z) :
    ∃ x ∈ Icc (z.re - (N + 1 : ℕ) / 2) (z.re + (N + 1 : ℕ) / 2),
      correlation N f z (ofComplex (point x z.im)) < 0 := by
  let a := z.re - (N + 1 : ℕ) / 2
  let b := z.re + (N + 1 : ℕ) / 2
  have hw : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : a + (N + 1 : ℕ) = b := by dsimp [a, b]; ring
  have hcenter : z.re ∈ Icc a b := by dsimp [a, b]; constructor <;> linarith
  have hp : ofComplex (point z.re z.im) = z := by
    have h : point z.re z.im = (z : ℂ) := by apply Complex.ext <;> simp [point]
    rw [h, ofComplex_apply]
  have hc : Continuous (fun x => correlation N f z (ofComplex (point x z.im))) :=
    continuous_finsetSum Finset.univ (fun q _ => Complex.continuous_re.comp
      ((slice_continuous (quotientForm N f q).2.2.1.1.continuousOn z.im_pos).mul continuous_const))
  by_contra hn
  have hnn : ∀ x ∈ Icc a b, 0 ≤ correlation N f z (ofComplex (point x z.im)) := by
    intro x hx
    exact le_of_not_gt (fun h => hn ⟨x, hx, h⟩)
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    (continuous_const.continuousOn) hc.continuousOn
    (fun x hx => hnn x (Ioc_subset_Icc_self hx)) ⟨z.re, hcenter, by rwa [hp, correlation_self]⟩
  have hm := correlation_mean_zero N lam f z z.im_pos a
  rw [hb] at hm
  simp only [intervalIntegral.integral_zero, hm, lt_self_iff_false] at hi

/-- The actual scalar amplitude has strictly positive mean around every positive source value. -/
theorem amplitude_mean_pos (z : ℍ) (hz : 0 < density N f z) :
    0 < ∫ x in (z.re - (N + 1 : ℕ) / 2)..(z.re + (N + 1 : ℕ) / 2),
      Real.sqrt (density N f (ofComplex (point x z.im))) := by
  have hw : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hp : ofComplex (point z.re z.im) = z := by
    have h : point z.re z.im = (z : ℂ) := by apply Complex.ext <;> simp [point]
    rw [h, ofComplex_apply]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show z.re - (N + 1 : ℕ) / 2 < z.re + (N + 1 : ℕ) / 2 by linarith)
    continuous_const.continuousOn (density_slice_continuous N f z.im_pos).sqrt.continuousOn
    (fun x _ => Real.sqrt_nonneg _) ⟨z.re, ⟨by linarith, by linarith⟩,
      by rw [hp]; exact Real.sqrt_pos.mpr hz⟩
  simpa only [intervalIntegral.integral_zero] using h

/-- Real correlation of the literal normalized family directions. -/
def directionCorrelation (z w : ℍ) : ℝ :=
  ∑ q : Deck N, (direction N f q w * (starRingEnd ℂ) (direction N f q z)).re

/-- Normalized correlation retains both actual amplitudes, also at common zeros. -/
theorem correlation_eq_amplitudes_mul (z w : ℍ) :
    correlation N f z w = Real.sqrt (density N f z) * Real.sqrt (density N f w) *
      directionCorrelation N f z w := by
  unfold correlation directionCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← amplitude_mul_direction N f q w, ← amplitude_mul_direction N f q z]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Literal squared chord distance between two finite-family directions. -/
def directionDistanceSq (z w : ℍ) : ℝ :=
  ∑ q : Deck N, normSq (direction N f q w - direction N f q z)

private theorem normSq_sub_pair (u v : ℂ) :
    normSq (u - v) = normSq u + normSq v - 2 * (u * (starRingEnd ℂ) v).re := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The exact squared-chord law holds on the actual positive-density locus. -/
theorem directionDistanceSq_eq (z w : ℍ) (hz : 0 < density N f z) (hw : 0 < density N f w) :
    directionDistanceSq N f z w = 2 - 2 * directionCorrelation N f z w := by
  simp only [directionDistanceSq, normSq_sub_pair, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, direction_normSq N f z hz,
    direction_normSq N f w hw, directionCorrelation]
  ring

/-- Each positive actual source value has a direction more than a right angle away within one level period. -/
theorem exists_separated_direction (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (z : ℍ) (hz : 0 < density N f z) :
    ∃ x ∈ Icc (z.re - (N + 1 : ℕ) / 2) (z.re + (N + 1 : ℕ) / 2),
      0 < density N f (ofComplex (point x z.im)) ∧
      2 < directionDistanceSq N f z (ofComplex (point x z.im)) := by
  obtain ⟨x, hx, hn⟩ := exists_negative_correlation N lam f z hz
  let w := ofComplex (point x z.im)
  have hw : 0 < density N f w := by
    apply lt_of_le_of_ne (density_nonneg N f w)
    intro he
    have hc := correlation_zero_of_density_zero N f z w he.symm
    change correlation N f z w < 0 at hn
    rw [hc] at hn
    exact (lt_irrefl 0) hn
  have hprod : 0 < Real.sqrt (density N f z) * Real.sqrt (density N f w) :=
    mul_pos (Real.sqrt_pos.mpr hz) (Real.sqrt_pos.mpr hw)
  have hc : directionCorrelation N f z w < 0 := by
    by_contra hc
    have hnn := mul_nonneg hprod.le (le_of_not_gt hc)
    rw [← correlation_eq_amplitudes_mul] at hnn
    exact (not_lt_of_ge hnn) hn
  refine ⟨x, hx, hw, ?_⟩
  change 2 < directionDistanceSq N f z w
  rw [directionDistanceSq_eq N f z w hz hw]
  linarith

/-- Actual nonvanishing and the original zero means produce separated normalized directions. -/
theorem source_direction_separation (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ∃ z w : ℍ, w.im = z.im ∧ 0 < density N f z ∧ 0 < density N f w ∧
      2 < directionDistanceSq N f z w := by
  obtain ⟨z, hz⟩ := density_pos_somewhere N f
  obtain ⟨x, _, hw, hs⟩ := exists_separated_direction N lam f z hz
  refine ⟨z, ofComplex (point x z.im), ?_, hz, hw, hs⟩
  rw [ofComplex_apply_of_im_pos (by simpa [point] using z.im_pos)]
  simp [point]

/-- On the positive-density locus the actual amplitude is differentiable. -/
theorem amplitude_differentiableAt (z : ℍ) (hz : 0 < density N f z) :
    DifferentiableAt ℝ (amplitude N f) (z : ℂ) := by
  have hd := ((density_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  exact hd.sqrt (by simpa only [Function.comp_apply, ofComplex_apply] using hz.ne')

/-- Actual normalized components are differentiable away from common trace zeros. -/
theorem direction_differentiableAt (q : Deck N) (z : ℍ) (hz : 0 < density N f z) :
    DifferentiableAt ℝ (direction N f q ∘ ofComplex) (z : ℂ) := by
  have ha := Complex.ofRealCLM.differentiableAt.comp (z : ℂ) (amplitude_differentiableAt N f z hz)
  have hr : (Real.sqrt (density N f z) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hz).ne'
  have hi := ha.fun_inv (by simpa only [Function.comp_apply, Complex.ofRealCLM_apply, amplitude, ofComplex_apply] using hr)
  have hF := (quotientForm N f q).2.2.1.1.contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  change DifferentiableAt ℝ (fun w => (quotientForm N f q).1.1 (ofComplex w) /
    (Real.sqrt (density N f (ofComplex w)) : ℂ)) (z : ℂ)
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, amplitude, div_eq_mul_inv, Pi.inv_apply] using
    (hF.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).fun_mul hi

/-- The actual derivative of direction is precisely the radial-subtracted derivative divided by amplitude. -/
theorem amplitude_mul_direction_dir (q : Deck N) (v : ℂ) (z : ℍ) (hz : 0 < density N f z) :
    (Real.sqrt (density N f z) : ℂ) * dir v (direction N f q ∘ ofComplex) (z : ℂ) =
      dir v ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) -
        (radialSlope N f v z : ℂ) * (quotientForm N f q).1.1 z := by
  have ha := Complex.ofRealCLM.hasFDerivAt.comp (z : ℂ)
    (amplitude_differentiableAt N f z hz).hasFDerivAt
  have hu := (direction_differentiableAt N f q z hz).hasFDerivAt
  have hp := congrArg (fun L => L v) (ha.mul hu).fderiv
  have he : (fun w => (amplitude N f w : ℂ) * direction N f q (ofComplex w)) =
      ((quotientForm N f q).1.1 ∘ ofComplex) := by
    funext w
    exact amplitude_mul_direction N f q (ofComplex w)
  change dir v (fun w => (amplitude N f w : ℂ) * direction N f q (ofComplex w)) (z : ℂ) =
    (amplitude N f (z : ℂ) : ℂ) * dir v (direction N f q ∘ ofComplex) (z : ℂ) +
      direction N f q (ofComplex (z : ℂ)) * ((dir v (amplitude N f) (z : ℂ) : ℝ) : ℂ) at hp
  rw [he, amplitude_dir N f v z hz] at hp
  simp only [amplitude, ofComplex_apply] at hp
  have hr : (Real.sqrt (density N f z) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hz).ne'
  have hs : (Real.sqrt (density N f z) : ℂ) ^ (2 : ℕ) = (density N f z : ℂ) := by
    exact_mod_cast Real.sq_sqrt hz.le
  have hrad : direction N f q z * (current N f v z / (2 * Real.sqrt (density N f z)) : ℝ) =
      (radialSlope N f v z : ℂ) * (quotientForm N f q).1.1 z := by
    unfold direction radialSlope
    push_cast
    rw [← hs]
    field_simp [hr]
  rw [hrad] at hp
  linear_combination -hp

/-- The radial residual is the literal weighted derivative energy of the normalized family. -/
theorem radialResidual_eq_direction_energy (v : ℂ) (z : ℍ) (hz : 0 < density N f z) :
    radialResidual N f v (radialSlope N f v z) z = density N f z *
      ∑ q : Deck N, normSq (dir v (direction N f q ∘ ofComplex) (z : ℂ)) := by
  unfold radialResidual
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← amplitude_mul_direction_dir N f q v z hz, normSq_mul, normSq_ofReal,
    ← pow_two, Real.sq_sqrt hz.le]

/-- Amplitude-weighted squared distance remains source-exact even at common zeros. -/
theorem amplitude_mul_directionDistanceSq (z w : ℍ) (hz : 0 < density N f z) :
    Real.sqrt (density N f w) * directionDistanceSq N f z w =
      2 * Real.sqrt (density N f w) - 2 * correlation N f z w / Real.sqrt (density N f z) := by
  by_cases hw : density N f w = 0
  · simp only [hw, Real.sqrt_zero, zero_mul, correlation_zero_of_density_zero N f z w hw,
      mul_zero, zero_div, sub_zero]
  · have hwpos := lt_of_le_of_ne (density_nonneg N f w) (Ne.symm hw)
    rw [directionDistanceSq_eq N f z w hz hwpos, correlation_eq_amplitudes_mul]
    field_simp [(Real.sqrt_pos.mpr hz).ne']

/-- Amplitude weight makes the actual squared-chord slice continuous even across common zeros. -/
theorem weighted_distance_slice_continuous (z : ℍ) (hz : 0 < density N f z)
    {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => Real.sqrt (density N f (ofComplex (point x y))) *
      directionDistanceSq N f z (ofComplex (point x y))) := by
  have hc : Continuous (fun x => correlation N f z (ofComplex (point x y))) :=
    continuous_finsetSum Finset.univ (fun q _ => Complex.continuous_re.comp
      ((slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy).mul continuous_const))
  have he : (fun x => Real.sqrt (density N f (ofComplex (point x y))) *
      directionDistanceSq N f z (ofComplex (point x y))) =
      (fun x => 2 * Real.sqrt (density N f (ofComplex (point x y))) -
        2 * correlation N f z (ofComplex (point x y)) / Real.sqrt (density N f z)) := by
    funext x
    exact amplitude_mul_directionDistanceSq N f z _ hz
  rw [he]
  exact (continuous_const.mul (density_slice_continuous N f hy).sqrt).sub
    ((continuous_const.mul hc).div_const _)

/-- The original complex mean fixes the exact amplitude-weighted mean squared distance from each positive direction. -/
theorem weighted_direction_distance_mean (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (z : ℍ) (hz : 0 < density N f z) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ), Real.sqrt (density N f (ofComplex (point x y))) *
      directionDistanceSq N f z (ofComplex (point x y))) =
      2 * ∫ x in a..a + (N + 1 : ℕ), Real.sqrt (density N f (ofComplex (point x y))) := by
  have hc : Continuous (fun x => correlation N f z (ofComplex (point x y))) :=
    continuous_finsetSum Finset.univ (fun q _ => Complex.continuous_re.comp
      ((slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy).mul continuous_const))
  have ha : IntervalIntegrable (fun x => 2 * Real.sqrt (density N f (ofComplex (point x y))))
      volume a (a + (N + 1 : ℕ)) :=
    (continuous_const.mul (density_slice_continuous N f hy).sqrt).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun x => 2 * correlation N f z (ofComplex (point x y)) /
      Real.sqrt (density N f z)) volume a (a + (N + 1 : ℕ)) :=
    ((continuous_const.mul hc).div_const _).intervalIntegrable _ _
  simp_rw [amplitude_mul_directionDistanceSq N f z _ hz]
  rw [intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    correlation_mean_zero N lam f z hy a, mul_zero, zero_div, sub_zero]

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceDirection
