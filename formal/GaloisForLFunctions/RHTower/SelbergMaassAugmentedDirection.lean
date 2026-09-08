import GaloisForLFunctions.RHTower.SelbergMaassTraceRegularized

/-!
# Smooth augmented Maass directions and the exact mean defect

Append the positive regulator as a literal extra coordinate before normalizing the
actual finite congruence family. The resulting unit vector is C² through original
common zeros, and its derivative energy is exactly the retained regularized
remainder. Original coordinates retain weighted mean zero; the added coordinate
has nonzero weighted mean. Exact squared-chord formulas retain that defect.
Original nonvanishing and zero means give fixed points separated for every
sufficiently small positive regulator. No uniform core spectral bound is assumed.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassAugmentedDirection
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
  SelbergMaassTraceBoundary SelbergMaassTraceRadial SelbergMaassTraceRegularized
  SelbergMaassTraceDirection SelbergMaassCuspTransport
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ))

/-- The literal congruence family with one added positive constant coordinate. -/
def source : Option (Deck N) → ℂ → ℂ
  | none, _ => ((e : ℝ) : ℂ)
  | some q, z => (quotientForm N f q).1.1 (ofComplex z)

/-- Actual normalized augmented family; its denominator never vanishes. -/
def unit (j : Option (Deck N)) (z : ℂ) : ℂ := source N f e j z / (radius N f e z : ℂ)

/-- The augmented source has exactly the regularized squared radius. -/
theorem source_normSq (z : ℂ) :
    (∑ j : Option (Deck N), normSq (source N f e j z)) = radius N f e z ^ 2 := by
  rw [Fintype.sum_option, radius_sq]
  simp only [source, normSq_ofReal]
  change (e : ℝ) * (e : ℝ) + density N f (ofComplex z) = _
  ring

/-- Literal reconstruction of every augmented coordinate. -/
theorem radius_mul_unit (j : Option (Deck N)) (z : ℂ) :
    (radius N f e z : ℂ) * unit N f e j z = source N f e j z := by
  unfold unit
  have hr : (radius N f e z : ℂ) ≠ 0 := by exact_mod_cast (radius_pos N f e z).ne'
  field_simp

/-- The augmented direction lies on the unit sphere, even at original common zeros. -/
theorem unit_normSq (z : ℂ) : (∑ j : Option (Deck N), normSq (unit N f e j z)) = 1 := by
  simp only [unit, normSq_div, normSq_ofReal, ← pow_two, ← Finset.sum_div, source_normSq]
  exact div_self (pow_ne_zero 2 (radius_pos N f e z).ne')

/-- Every augmented source coordinate retains C² regularity on the original upper half-plane. -/
theorem source_contDiffOn (j : Option (Deck N)) :
    ContDiffOn ℝ 2 (source N f e j) {z : ℂ | 0 < z.im} := by
  cases j with
  | none => exact contDiffOn_const
  | some q => exact (quotientForm N f q).2.2.1.1

/-- Normalized augmented coordinates are C² through the original nodal set. -/
theorem unit_contDiffOn (j : Option (Deck N)) :
    ContDiffOn ℝ 2 (unit N f e j) {z : ℂ | 0 < z.im} := by
  have hr := Complex.ofRealCLM.contDiff.comp_contDiffOn (radius_contDiffOn N f e)
  have hi := hr.fun_inv (fun z _ => by
    change (radius N f e z : ℂ) ≠ 0
    exact_mod_cast (radius_pos N f e z).ne')
  change ContDiffOn ℝ 2 (fun z => source N f e j z / (radius N f e z : ℂ)) _
  simpa only [div_eq_mul_inv, Function.comp_apply, Complex.ofRealCLM_apply] using (source_contDiffOn N f e j).mul hi

/-- Modular transport permutes the original coordinates and fixes the added coordinate. -/
theorem unit_equivariant (j : Option (Deck N)) (A : SL2Z) (z : ℍ) :
    unit N f e j (A • z : ℍ) =
      unit N f e (j.map (fun q => q * QuotientGroup.mk A)) (z : ℂ) := by
  cases j with
  | none => simp only [unit, source, radius_invariant, Option.map_none]
  | some q =>
    simp only [unit, source, radius_invariant, Option.map_some, ofComplex_apply]
    rw [quotientForm_mul, translate_apply]

/-- The added positive coordinate's original derivative is exactly zero. -/
theorem source_none_dir (v : ℂ) (z : ℂ) : dir v (source N f e none) z = 0 := by
  change dir v (fun _ : ℂ => ((e : ℝ) : ℂ)) z = 0
  simp [dir]

/-- Literal derivative reconstruction retains the common radial subtraction in every coordinate. -/
theorem radius_mul_unit_dir (j : Option (Deck N)) (v : ℂ) (z : ℍ) :
    (radius N f e (z : ℂ) : ℂ) * dir v (unit N f e j) (z : ℂ) =
      dir v (source N f e j) (z : ℂ) -
        (slope N f e v z : ℂ) * source N f e j (z : ℂ) := by
  have hr := ((radius_contDiffOn N f e).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hu := ((unit_contDiffOn N f e j).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have ha := Complex.ofRealCLM.hasFDerivAt.comp (z : ℂ) hr.hasFDerivAt
  have hp := congrArg (fun L => L v) (ha.mul hu.hasFDerivAt).fderiv
  have he : (fun w => (radius N f e w : ℂ) * unit N f e j w) = source N f e j :=
    funext (radius_mul_unit N f e j)
  change dir v (fun w => (radius N f e w : ℂ) * unit N f e j w) (z : ℂ) =
    (radius N f e (z : ℂ) : ℂ) * dir v (unit N f e j) (z : ℂ) +
      unit N f e j (z : ℂ) * ((dir v (radius N f e) (z : ℂ) : ℝ) : ℂ) at hp
  rw [he, radius_dir N f e v z] at hp
  have hr0 : (radius N f e (z : ℂ) : ℂ) ≠ 0 := by exact_mod_cast (radius_pos N f e (z : ℂ)).ne'
  have hs : (radius N f e (z : ℂ) : ℂ) ^ 2 = ((density N f z + (e : ℝ) ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (by simpa only [ofComplex_apply] using radius_sq N f e (z : ℂ))
  push_cast at hs
  have hrad : unit N f e j (z : ℂ) * (current N f v z / (2 * radius N f e (z : ℂ)) : ℝ) =
      (slope N f e v z : ℂ) * source N f e j (z : ℂ) := by
    unfold unit SelbergMaassTraceRegularized.slope
    push_cast
    rw [← hs]
    field_simp [hr0]
  rw [hrad] at hp
  linear_combination -hp

/-- The augmented residual is exactly the original regularized remainder, including its constant-coordinate term. -/
theorem residual_eq (v : ℂ) (z : ℍ) :
    (∑ j : Option (Deck N), normSq (dir v (source N f e j) (z : ℂ) -
      (slope N f e v z : ℂ) * source N f e j (z : ℂ))) = directionalRemainder N f e v z := by
  rw [Fintype.sum_option, source_none_dir]
  simp only [source, ofComplex_apply, zero_sub, normSq_neg, normSq_mul, normSq_ofReal]
  change slope N f e v z * slope N f e v z * ((e : ℝ) * (e : ℝ)) +
    radialResidual N f v (slope N f e v z) z = _
  unfold directionalRemainder
  ring

/-- The retained remainder is the literal smooth augmented direction energy at every actual source point. -/
theorem directionalRemainder_eq_energy (v : ℂ) (z : ℍ) :
    directionalRemainder N f e v z = radius N f e (z : ℂ) ^ 2 *
      ∑ j : Option (Deck N), normSq (dir v (unit N f e j) (z : ℂ)) := by
  rw [← residual_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← radius_mul_unit_dir, normSq_mul, normSq_ofReal, ← pow_two]

/-- The complete curvature remainder is the literal two-direction augmented energy. -/
theorem remainder_eq_energy (z : ℍ) :
    remainder N f e z = radius N f e (z : ℂ) ^ 2 *
      ∑ j : Option (Deck N),
        (normSq (dir 1 (unit N f e j) (z : ℂ)) + normSq (dir Complex.I (unit N f e j) (z : ℂ))) := by
  rw [remainder, directionalRemainder_eq_energy, directionalRemainder_eq_energy,
    Finset.sum_add_distrib, mul_add]

/-- Real correlation of the complete augmented directions. -/
def unitCorrelation (z w : ℍ) : ℝ :=
  ∑ j : Option (Deck N), (unit N f e j (w : ℂ) * (starRingEnd ℂ) (unit N f e j (z : ℂ))).re

/-- The constant coordinate contributes exactly its positive square to source correlation. -/
theorem correlation_eq_radii_mul (z w : ℍ) :
    correlation N f z w + (e : ℝ) ^ 2 = radius N f e (z : ℂ) * radius N f e (w : ℂ) *
      unitCorrelation N f e z w := by
  have he : correlation N f z w + (e : ℝ) ^ 2 =
      ∑ j : Option (Deck N), (source N f e j (w : ℂ) * (starRingEnd ℂ) (source N f e j (z : ℂ))).re := by
    rw [Fintype.sum_option]
    simp only [source, ofComplex_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    change correlation N f z w + _ = (e : ℝ) * (e : ℝ) + correlation N f z w
    ring
  rw [he, unitCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← radius_mul_unit N f e j (w : ℂ), ← radius_mul_unit N f e j (z : ℂ)]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Complete augmented squared chord distance. -/
def distanceSq (z w : ℍ) : ℝ :=
  ∑ j : Option (Deck N), normSq (unit N f e j (w : ℂ) - unit N f e j (z : ℂ))

private theorem normSq_sub_pair (u v : ℂ) :
    normSq (u-v) = normSq u + normSq v - 2 * (u * (starRingEnd ℂ) v).re := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Exact unit-sphere chord law, without excluding original common zeros. -/
theorem distanceSq_eq (z w : ℍ) : distanceSq N f e z w = 2 - 2 * unitCorrelation N f e z w := by
  simp only [distanceSq, normSq_sub_pair, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, unit_normSq, unitCorrelation]
  ring

/-- Exact weighted chord formula retains the added-coordinate correlation correction. -/
theorem radius_mul_distanceSq (z w : ℍ) :
    radius N f e (w : ℂ) * distanceSq N f e z w =
      2 * radius N f e (w : ℂ) - 2 * (correlation N f z w + (e : ℝ) ^ 2) / radius N f e (z : ℂ) := by
  rw [distanceSq_eq, correlation_eq_radii_mul]
  field_simp [(radius_pos N f e (z : ℂ)).ne']

/-- The radius depends only on the upper-half-plane projection of a chart point. -/
theorem radius_ofComplex (z : ℂ) : radius N f e (ofComplex z : ℂ) = radius N f e z := by
  simp only [radius, ofComplex_apply]

/-- Actual regularized amplitudes have continuous horizontal slices. -/
theorem radius_slice_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => radius N f e (point x y)) := by
  exact ((density_slice_continuous N f hy).add continuous_const).sqrt

/-- Original coordinates retain their exact amplitude-weighted zero means. -/
theorem weighted_original_mean_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (e : Ioi (0 : ℝ)) (q : Deck N) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      (radius N f e (point x y) : ℂ) * unit N f e (some q) (point x y)) = 0 := by
  simp_rw [radius_mul_unit]
  exact component_mean_zero N lam f q hy a

/-- The added coordinate has its literal nonzero amplitude-weighted period mean. -/
theorem weighted_added_mean (y a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      (radius N f e (point x y) : ℂ) * unit N f e none (point x y)) =
        ((N + 1 : ℕ) : ℂ) * ((e : ℝ) : ℂ) := by
  simp_rw [radius_mul_unit]
  simp [source, intervalIntegral.integral_const, real_smul]

/-- The augmented vector cannot be treated as a vector with weighted mean zero. -/
theorem weighted_added_mean_ne_zero (y a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ),
      (radius N f e (point x y) : ℂ) * unit N f e none (point x y)) ≠ 0 := by
  rw [weighted_added_mean]
  apply mul_ne_zero
  · exact_mod_cast (Nat.succ_ne_zero N)
  · exact_mod_cast e.2.ne'

/-- Exact weighted squared-distance mean includes the added-coordinate defect. -/
theorem weighted_distance_mean (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (e : Ioi (0 : ℝ)) (z : ℍ) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ x in a..a + (N + 1 : ℕ), radius N f e (ofComplex (point x y) : ℂ) *
      distanceSq N f e z (ofComplex (point x y))) =
      2 * (∫ x in a..a + (N + 1 : ℕ), radius N f e (point x y)) -
        2 * (e : ℝ) ^ 2 * (N + 1 : ℕ) / radius N f e (z : ℂ) := by
  have hc : Continuous (fun x => correlation N f z (ofComplex (point x y))) :=
    continuous_finsetSum Finset.univ (fun q _ => Complex.continuous_re.comp
      ((slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy).mul continuous_const))
  have ha : IntervalIntegrable (fun x => 2 * radius N f e (point x y)) volume a (a + (N + 1 : ℕ)) :=
    (continuous_const.mul (radius_slice_continuous N f e hy)).intervalIntegrable a (a + (N + 1 : ℕ))
  have hb : IntervalIntegrable (fun x => 2 * (correlation N f z (ofComplex (point x y)) + (e : ℝ) ^ 2) /
      radius N f e (z : ℂ)) volume a (a + (N + 1 : ℕ)) :=
    ((continuous_const.mul (hc.add continuous_const)).div_const (radius N f e (z : ℂ))).intervalIntegrable a (a + (N + 1 : ℕ))
  simp_rw [radius_mul_distanceSq, radius_ofComplex]
  rw [intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    correlation_mean_zero N lam f z hy a, intervalIntegral.integral_const]
  simp only [zero_add, add_sub_cancel_left, smul_eq_mul]
  ring

/-- Augmented directions remain separated beyond a right angle precisely below the source correlation threshold. -/
theorem distanceSq_gt_two_iff (z w : ℍ) :
    2 < distanceSq N f e z w ↔ correlation N f z w + (e : ℝ) ^ 2 < 0 := by
  have h := correlation_eq_radii_mul N f e z w
  have hp := mul_pos (radius_pos N f e (z : ℂ)) (radius_pos N f e (w : ℂ))
  rw [distanceSq_eq]
  constructor
  · intro hd
    have hn : unitCorrelation N f e z w < 0 := by linarith
    rw [h]
    exact mul_neg_of_pos_of_neg hp hn
  · intro hc
    have hn : unitCorrelation N f e z w < 0 := by
      by_contra hn
      have hh := mul_nonneg hp.le (le_of_not_gt hn)
      linarith
    linarith

/-- Original nonvanishing and zero means supply fixed separated points for every sufficiently small positive regulator. -/
theorem source_separation_for_small_regulator (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ∃ z w : ℍ, w.im = z.im ∧ ∃ r : Ioi (0 : ℝ),
      ∀ e : Ioi (0 : ℝ), (e : ℝ) ≤ (r : ℝ) → 2 < distanceSq N f e z w := by
  obtain ⟨z, hz⟩ := density_pos_somewhere N f
  obtain ⟨x, _, hx⟩ := exists_negative_correlation N lam f z hz
  let w := ofComplex (point x z.im)
  have hc : 0 < -correlation N f z w := by dsimp [w]; linarith
  have hr : 0 < Real.sqrt (-correlation N f z w) / 2 := div_pos (Real.sqrt_pos.mpr hc) (by norm_num)
  refine ⟨z, w, ?_, ⟨Real.sqrt (-correlation N f z w) / 2, hr⟩, ?_⟩
  · dsimp [w]
    rw [ofComplex_apply_of_im_pos (by simpa [point] using z.im_pos)]
    simp [point]
  · intro e he
    rw [distanceSq_gt_two_iff]
    have hs := Real.sq_sqrt hc.le
    have hh := mul_nonneg (sub_nonneg.mpr he) (add_nonneg hr.le e.2.le)
    dsimp only at he hh
    nlinarith

end
end GaloisForLFunctions.RHTower.SelbergMaassAugmentedDirection
