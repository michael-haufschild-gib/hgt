import GaloisForLFunctions.RHTower.SelbergMaassAugmentedDirection
import GaloisForLFunctions.RHTower.SelbergWeightedPathEnergy

/-!
# Actual Maass chord energy with the full path resistance

The literal smooth augmented family satisfies a weighted finite-family endpoint
comparison. Its weight is the actual regularized amplitude; its energy is the
retained horizontal curvature density. Every continuity and FTC condition is
proved from the original C² source. Exceptional zero means and nonvanishing give
a fixed nondegenerate source path with a positive capacity cost and a uniform
positive squared coordinate-variation bound for every small regulator. The reciprocal-amplitude resistance is explicit, with no uniform bound
assumed and no Selberg conclusion.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassChordEnergy
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
  SelbergMaassTraceRegularized SelbergMaassAugmentedDirection SelbergWeightedPathEnergy
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ))

/-- Literal inverse-amplitude resistance along the original horizontal source path. -/
def pathResistance (y a b : ℝ) : ℝ := resistance (fun x => radius N f e (point x y)) a b

/-- Literal retained horizontal curvature energy along the original source path. -/
def pathEnergy (y a b : ℝ) : ℝ :=
  ∫ x in a..b, directionalRemainder N f e 1 (ofComplex (point x y)) / radius N f e (point x y)

/-- Actual horizontal derivative of each smooth augmented source component. -/
theorem unit_slice_hasDerivAt (j : Option (Deck N)) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => unit N f e j (point t y)) (dir 1 (unit N f e j) (point x y)) x := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((unit_contDiffOn N f e j).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)

/-- Actual first augmented derivatives have continuous horizontal slices. -/
theorem unit_dir_slice_continuous (j : Option (Deck N)) (v : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => dir v (unit N f e j) (point x y)) := by
  have hc := (dir_contDiffOn (unit_contDiffOn N f e j) (m := 1) (by norm_num) v).continuousOn
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (hc.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp
    (f := fun t : ℝ => point t y) (point_horizontal x y).continuousAt

/-- The literal retained curvature is precisely the amplitude-weighted smooth path energy. -/
theorem weighted_remainder_eq_energy (x : ℝ) {y : ℝ} (hy : 0 < y) :
    directionalRemainder N f e 1 (ofComplex (point x y)) / radius N f e (point x y) =
      radius N f e (point x y) *
        ∑ j : Option (Deck N), normSq (dir 1 (unit N f e j) (point x y)) := by
  have h := directionalRemainder_eq_energy N f e 1 (ofComplex (point x y))
  have hc : ((ofComplex (point x y) : ℍ) : ℂ) = point x y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point x y).im)]
  rw [hc] at h
  rw [h]
  field_simp [(radius_pos N f e (point x y)).ne']

/-- The retained path-energy density is continuous, including original common zeros. -/
theorem weighted_remainder_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => directionalRemainder N f e 1 (ofComplex (point x y)) / radius N f e (point x y)) := by
  have he : (fun x => directionalRemainder N f e 1 (ofComplex (point x y)) / radius N f e (point x y)) =
      (fun x => radius N f e (point x y) *
        ∑ j : Option (Deck N), normSq (dir 1 (unit N f e j) (point x y))) :=
    funext (fun x => weighted_remainder_eq_energy N f e x hy)
  rw [he]
  exact (radius_slice_continuous N f e hy).mul
    (continuous_finsetSum Finset.univ (fun j _ => Complex.continuous_normSq.comp (unit_dir_slice_continuous N f e j 1 hy)))

/-- Every actual retained path-energy density is interval integrable. -/
theorem path_energy_intervalIntegrable {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable (fun x => directionalRemainder N f e 1 (ofComplex (point x y)) /
      radius N f e (point x y)) volume a b :=
  (weighted_remainder_continuous N f e hy).intervalIntegrable a b

/-- Every actual nondegenerate horizontal path has positive regularized resistance. -/
theorem pathResistance_pos {y a b : ℝ} (hy : 0 < y) (hab : a < b) :
    0 < pathResistance N f e y a b :=
  resistance_pos (radius_slice_continuous N f e hy) (fun x => radius_pos N f e (point x y)) hab

/-- The retained horizontal path energy is nonnegative in its positive orientation. -/
theorem pathEnergy_nonneg (y : ℝ) {a b : ℝ} (hab : a ≤ b) : 0 ≤ pathEnergy N f e y a b := by
  exact intervalIntegral.integral_nonneg_of_forall hab (fun x =>
    div_nonneg (directionalRemainder_nonneg N f e 1 _) (radius_pos N f e _).le)

/-- Actual endpoint directions satisfy the source-built weighted resistance/energy comparison. -/
theorem chord_le_resistance_energy {y a b : ℝ} (hy : 0 < y) (hab : a ≤ b) :
    distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) ≤
      pathResistance N f e y a b * pathEnergy N f e y a b := by
  have h := sum_normSq_sub_le_resistance_energy
    (fun j => unit_dir_slice_continuous N f e j 1 hy)
    (radius_slice_continuous N f e hy) (fun x => radius_pos N f e (point x y)) hab
    (fun j x _ => unit_slice_hasDerivAt N f e j hy x)
  have hE : (∫ x in a..b, radius N f e (point x y) *
      ∑ j : Option (Deck N), normSq (dir 1 (unit N f e j) (point x y))) = pathEnergy N f e y a b := by
    unfold pathEnergy
    apply intervalIntegral.integral_congr
    intro x _
    exact (weighted_remainder_eq_energy N f e x hy).symm
  rw [hE] at h
  have ha : ((ofComplex (point a y) : ℍ) : ℂ) = point a y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point a y).im)]
  have hb : ((ofComplex (point b y) : ℍ) : ℂ) = point b y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point b y).im)]
  simpa only [distanceSq, ha, hb, pathResistance] using h

private theorem distanceSq_comm (z w : ℍ) : distanceSq N f e z w = distanceSq N f e w z := by
  unfold distanceSq
  apply Finset.sum_congr rfl
  intro j _
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

private theorem path_product_comm (y a b : ℝ) :
    pathResistance N f e y b a * pathEnergy N f e y b a =
      pathResistance N f e y a b * pathEnergy N f e y a b := by
  unfold pathResistance resistance pathEnergy
  rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm b a, neg_mul_neg]

/-- The literal resistance/energy product is independent of path orientation. -/
theorem chord_le_oriented_resistance_energy {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) ≤
      pathResistance N f e y a b * pathEnergy N f e y a b := by
  rcases le_total a b with h | h
  · exact chord_le_resistance_energy N f e hy h
  · have hh := chord_le_resistance_energy N f e hy h
    rw [path_product_comm] at hh
    rwa [distanceSq_comm] at hh

private theorem ofComplex_point_self (z : ℍ) : ofComplex (point z.re z.im) = z := by
  have h : point z.re z.im = (z : ℂ) := by apply Complex.ext <;> simp [point]
  rw [h, ofComplex_apply]

/-- Literal sum of squared coordinate variations along the smooth augmented source. -/
def pathVariationSq (y a b : ℝ) : ℝ :=
  ∑ j : Option (Deck N), (∫ x in a..b, ‖dir 1 (unit N f e j) (point x y)‖) ^ 2

/-- Actual endpoint separation controls coordinate variation without introducing inverse-amplitude resistance. -/
theorem chord_le_variation {y a b : ℝ} (hy : 0 < y) (hab : a ≤ b) :
    distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) ≤ pathVariationSq N f e y a b := by
  have h := sum_normSq_sub_le_sum_sq_variation
    (fun j => unit_dir_slice_continuous N f e j 1 hy) hab
    (fun j x _ => unit_slice_hasDerivAt N f e j hy x)
  have ha : ((ofComplex (point a y) : ℍ) : ℂ) = point a y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point a y).im)]
  have hb : ((ofComplex (point b y) : ℍ) : ℂ) = point b y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point b y).im)]
  simpa only [distanceSq, ha, hb, pathVariationSq] using h

/-- Original zero means give a fixed ordered path with separated endpoints at every small regulator. -/
theorem source_fixed_path_separation (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ∃ y : Ioi (0 : ℝ), ∃ a b : ℝ, a < b ∧ ∃ r : Ioi (0 : ℝ),
      ∀ e : Ioi (0 : ℝ), (e : ℝ) ≤ (r : ℝ) →
        2 < distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) := by
  obtain ⟨z, w, hw, r, hr⟩ := source_separation_for_small_regulator N lam f
  have hd (e : Ioi (0 : ℝ)) (he : (e : ℝ) ≤ (r : ℝ)) :
      2 < distanceSq N f e (ofComplex (point z.re z.im)) (ofComplex (point w.re z.im)) := by
    have hp : ofComplex (point w.re z.im) = w := by rw [← hw]; exact ofComplex_point_self w
    rw [ofComplex_point_self z, hp]
    exact hr e he
  have hne : z.re ≠ w.re := by
    intro heq
    have h := hd r le_rfl
    rw [heq] at h
    simp [distanceSq] at h
    norm_num at h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨⟨z.im, z.im_pos⟩, z.re, w.re, hlt, r, hd⟩
  · refine ⟨⟨z.im, z.im_pos⟩, w.re, z.re, hgt, r, ?_⟩
    intro e he
    rw [distanceSq_comm]
    exact hd e he

/-- Every exceptional source supplies the same fixed path with an explicit capacity cost and a regulator-independent lower bound on squared variation. -/
theorem source_capacity_variation_witness (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ∃ y : Ioi (0 : ℝ), ∃ a b : ℝ, a < b ∧ ∃ r : Ioi (0 : ℝ),
      ∀ e : Ioi (0 : ℝ), (e : ℝ) ≤ (r : ℝ) →
        2 / pathResistance N f e y a b < pathEnergy N f e y a b ∧
          2 < pathVariationSq N f e y a b := by
  obtain ⟨y, a, b, hab, r, hr⟩ := source_fixed_path_separation N lam f
  refine ⟨y, a, b, hab, r, ?_⟩
  intro e he
  constructor
  · apply (div_lt_iff₀ (pathResistance_pos N f e y.2 hab)).mpr
    have h := (hr e he).trans_le (chord_le_resistance_energy N f e y.2 hab.le)
    nlinarith
  · exact (hr e he).trans_le (chord_le_variation N f e y.2 hab.le)

end
end GaloisForLFunctions.RHTower.SelbergMaassChordEnergy
