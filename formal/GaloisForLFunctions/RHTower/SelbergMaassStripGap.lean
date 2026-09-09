import GaloisForLFunctions.RHTower.SelbergMaassStripSlice
import GaloisForLFunctions.RHTower.SelbergModularStripComparison

/-!
# An explicit physical Maass gap and small principal-level exclusion

Original source Fourier energy on the complete modular strip, its literal
inversion cover, and the full-cell Stokes identity imply
`3*pi^2 <= 2*lambda*(N+1)^2` for every exceptional source. All full-domain
integrability, hyperbolic coordinate changes, infinite-height Fubini, and
positive-mass cancellation are derived. The exceptional-source type is
therefore empty at each principal level one through seven.

The quantitative bound retains its level dependence. This module does not
assert the uniform Selberg conjecture.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassStripGap
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassFullGradient
  SelbergMaassTraceMass SelbergMaassFullCurvatureBudget SelbergMaassCellCurvature
  SelbergMaassMean SelbergModularDomainSlices SelbergMaassCurvatureTransport
  SelbergModularStripComparison SelbergMaassStripSlice
noncomputable section

/-- Real coordinates of the complete modular comparison strip. -/
def rectangle : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ici arcFloor

theorem rectangle_measurable : MeasurableSet rectangle := measurableSet_Icc.prod measurableSet_Ici

theorem rectangle_height_pos {p : ℝ × ℝ} (hp : p ∈ rectangle) : 0 < p.2 :=
  arcFloor_pos.trans_le hp.2

/-- Real and hyperbolic strip coordinates agree including the bottom boundary. -/
theorem rectangle_iff_strip (z : ℍ) : (z.re, z.im) ∈ rectangle ↔ z ∈ strip := by
  change (z.re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ arcFloor ≤ z.im) ↔
    (|z.re| ≤ (1 : ℝ) / 2 ∧ 3 ≤ 4 * z.im ^ 2)
  have hs := arcFloor_sq
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨abs_le.mpr hx, ?_⟩
    have hp := mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ z.im + arcFloor by linarith [arcFloor_pos, z.im_pos])
    nlinarith
  · rintro ⟨hx, hy⟩
    exact ⟨abs_le.mp hx, by nlinarith [arcFloor_pos, z.im_pos]⟩

/-- Exact change from hyperbolic strip area to ordinary rectangular area. -/
theorem integral_height_sq_strip (F : ℝ × ℝ → ℝ) :
    (∫ z : ℍ in strip, z.im ^ 2 * F (z.re, z.im)) = ∫ p in rectangle, F p := by
  let G : ℂ → ℝ := fun z => rectangle.indicator F (z.re, z.im)
  have he : (∫ z : ℍ in strip, z.im ^ 2 * F (z.re, z.im)) = ∫ z : ℍ, z.im ^ 2 * G z := by
    rw [← integral_indicator strip_measurable]
    apply integral_congr_ae
    filter_upwards with z
    simp only [G, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    by_cases hz : z ∈ strip
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((rectangle_iff_strip z).mpr hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
        (fun hp => hz ((rectangle_iff_strip z).mp hp)), mul_zero]
  rw [he, integral_height_sq_chart]
  calc
    (∫ z in {z : ℂ | 0 < z.im}, G z) = ∫ z : ℂ, G z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      exact Set.indicator_of_notMem
        (fun (hp : (z.re, z.im) ∈ rectangle) => hz (rectangle_height_pos hp)) F
    _ = ∫ p : ℝ × ℝ, rectangle.indicator F p :=
      Complex.volume_preserving_equiv_real_prod.integral_comp
        Complex.measurableEquivRealProd.measurableEmbedding (rectangle.indicator F)
    _ = _ := integral_indicator rectangle_measurable

private theorem rectangle_product_integrable {F : ℝ × ℝ → ℝ}
    (hi : IntegrableOn F rectangle) :
    Integrable F ((volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))).prod
      (volume.restrict (Ici arcFloor))) := by
  rw [Measure.prod_restrict]
  simpa only [Measure.volume_eq_prod, IntegrableOn, rectangle] using hi

/-- Actual integrable strip sources admit horizontal Fubini slices. -/
theorem rectangle_integral {F : ℝ × ℝ → ℝ} (hi : IntegrableOn F rectangle) :
    (∫ p in rectangle, F p) =
      ∫ y in Ici arcFloor, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), F (x, y) := by
  have h := integral_prod_symm F (rectangle_product_integrable hi)
  simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod, rectangle] using h

/-- The true horizontal slice integrals remain integrable over the infinite strip. -/
theorem rectangle_slices_integrable {F : ℝ × ℝ → ℝ} (hi : IntegrableOn F rectangle) :
    IntegrableOn (fun y => ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), F (x, y)) (Ici arcFloor) :=
  (rectangle_product_integrable hi).integral_prod_right

variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- The actual trace mass has exactly its original planar normalization on the cell. -/
theorem cell_mass_identity :
    (∫ z : ℍ in fd, density N f z) = ∫ p in fullDomain, massDensity N f p := by
  convert integral_height_sq_cell (massDensity N f) using 1
  congr 1
  funext z
  simp only [massDensity]
  rw [show point z.re z.im = (z : ℂ) from Complex.re_add_im (z : ℂ), ofComplex_apply]
  field_simp [z.im_pos.ne']

/-- The original complete-cell trace mass is integrable. -/
theorem cell_mass_integrable : IntegrableOn (density N f) fd := by
  apply Integrable.of_integral_ne_zero
  rw [cell_mass_identity]
  exact (full_mass_pos N lam f).ne'

/-- Both source energies on the strip retain their exact coordinate normalization. -/
theorem strip_gradient_identity :
    (∫ z : ℍ in strip, hyperbolicGradient N f z) = ∫ p in rectangle, planarGradient N f p := by
  convert integral_height_sq_strip (planarGradient N f) using 1
  congr 1
  funext z
  simp only [hyperbolicGradient, planarGradient]
  rw [show point z.re z.im = (z : ℂ) from Complex.re_add_im (z : ℂ)]

/-- The actual mass on the strip keeps the full reciprocal-height square. -/
theorem strip_mass_identity :
    (∫ z : ℍ in strip, density N f z) = ∫ p in rectangle, massDensity N f p := by
  convert integral_height_sq_strip (massDensity N f) using 1
  congr 1
  funext z
  simp only [massDensity]
  rw [show point z.re z.im = (z : ℂ) from Complex.re_add_im (z : ℂ), ofComplex_apply]
  field_simp [z.im_pos.ne']

/-- The infinite rectangular gradient integral is genuinely integrable. -/
theorem rectangle_gradient_integrable : IntegrableOn (planarGradient N f) rectangle := by
  have hi := integrable_strip (cell_gradient_integrable N lam f)
    (hyperbolicGradient_invariant N f S)
  have hle := setIntegral_mono_set hi (Eventually.of_forall (hyperbolicGradient_nonneg N f))
    (Eventually.of_forall fd_subset_strip)
  change (∫ z : ℍ in fd, hyperbolicGradient N f z) ≤ ∫ z in strip, hyperbolicGradient N f z at hle
  apply Integrable.of_integral_ne_zero
  rw [← strip_gradient_identity]
  exact (lt_of_lt_of_le (cell_gradient_pos N lam f) hle).ne'

/-- Original mass and inversion give finite mass throughout the complete rectangle. -/
theorem rectangle_mass_integrable : IntegrableOn (massDensity N f) rectangle := by
  have hi := integrable_strip (cell_mass_integrable N lam f) (density_invariant N f S)
  have hle := setIntegral_mono_set hi (Eventually.of_forall (density_nonneg N f))
    (Eventually.of_forall fd_subset_strip)
  change (∫ z : ℍ in fd, density N f z) ≤ ∫ z in strip, density N f z at hle
  rw [cell_mass_identity, strip_mass_identity] at hle
  exact Integrable.of_integral_ne_zero (lt_of_lt_of_le (full_mass_pos N lam f) hle).ne'

/-- Fourier energy at every actual strip height bounds the hyperbolic slice mass. -/
theorem rectangle_slice_gap {y : ℝ} (hy : y ∈ Ici arcFloor) :
    ((3 / 4 : ℝ) * (2 * Real.pi / (N + 1 : ℕ)) ^ 2) *
        (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)) ≤
      ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y) := by
  have hp : 0 < y := arcFloor_pos.trans_le hy
  have hs : 3 / 4 ≤ y ^ 2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ y + arcFloor by linarith [arcFloor_pos])
    nlinarith [arcFloor_sq]
  have hgap := centered_energy_ge_mass N lam f hp
  have hm : 0 ≤ ∫ x in (-(1 / 2 : ℝ))..(1 / 2), density N f (ofComplex (point x y)) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => density_nonneg N f _)
  simp only [massDensity, planarGradient]
  rw [integral_div]
  simp only [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hd : (3 / 4 : ℝ) / y ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos hp)).mpr (by linarith)
  calc
    _ = ((2 * Real.pi / (N + 1 : ℕ)) ^ 2 *
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2), density N f (ofComplex (point x y)))) *
        ((3 / 4 : ℝ) / y ^ 2) := by ring
    _ ≤ ((2 * Real.pi / (N + 1 : ℕ)) ^ 2 *
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2), density N f (ofComplex (point x y)))) * 1 :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg (sq_nonneg _) hm)
    _ ≤ _ := by simpa only [mul_one] using hgap

/-- The complete original-source strip has the integrated Fourier energy lower bound. -/
theorem rectangle_energy_lower :
    ((3 / 4 : ℝ) * (2 * Real.pi / (N + 1 : ℕ)) ^ 2) *
        (∫ p in rectangle, massDensity N f p) ≤ ∫ p in rectangle, planarGradient N f p := by
  rw [rectangle_integral (rectangle_mass_integrable N lam f),
    rectangle_integral (rectangle_gradient_integrable N lam f), ← integral_const_mul]
  apply integral_mono_ae
    ((rectangle_slices_integrable (rectangle_mass_integrable N lam f)).const_mul _)
    (rectangle_slices_integrable (rectangle_gradient_integrable N lam f))
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  exact rectangle_slice_gap N lam f hy

include f in
/-- The physical source mass cancels to give an explicit level-scaled eigenvalue bound. -/
theorem level_scaled_eigenvalue_bound :
    3 * Real.pi ^ 2 ≤ 2 * (lam : ℝ) * ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have hupper := integral_strip_le_twice (cell_gradient_integrable N lam f)
    (hyperbolicGradient_nonneg N f) (hyperbolicGradient_invariant N f S)
  rw [strip_gradient_identity, cell_gradient_identity] at hupper
  have hmass := setIntegral_mono_set
    (integrable_strip (cell_mass_integrable N lam f) (density_invariant N f S))
    (Eventually.of_forall (density_nonneg N f)) (Eventually.of_forall fd_subset_strip)
  change (∫ z : ℍ in fd, density N f z) ≤ ∫ z in strip, density N f z at hmass
  rw [cell_mass_identity, strip_mass_identity] at hmass
  have hlow := (mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (3 / 4 : ℝ) * (2 * Real.pi / (N + 1 : ℕ)) ^ 2 by positivity)).trans
      (rectangle_energy_lower N lam f)
  have hcancel : ((3 / 4 : ℝ) * (2 * Real.pi / (N + 1 : ℕ)) ^ 2) ≤ 2 * (lam : ℝ) := by
    apply le_of_mul_le_mul_right (a := ∫ p in fullDomain, massDensity N f p) ?_ (full_mass_pos N lam f)
    simpa only [mul_assoc] using hlow.trans hupper
  have hdiv : (3 * Real.pi ^ 2) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (lam : ℝ) := by
    convert hcancel using 1
    ring
  exact (div_le_iff₀ (by positivity : 0 < ((N + 1 : ℕ) : ℝ) ^ 2)).mp hdiv

include f in
/-- An unconditional quantitative lower bound for the original congruence Maass source. -/
theorem eigenvalue_lower_bound :
    (3 * Real.pi ^ 2) / (2 * ((N + 1 : ℕ) : ℝ) ^ 2) ≤ (lam : ℝ) := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * ((N + 1 : ℕ) : ℝ) ^ 2)).mpr
  nlinarith [level_scaled_eigenvalue_bound N lam f]

/-- The original exceptional-source type is empty at every principal level one through seven. -/
theorem small_level_no_exceptional (n : Fin 7) (l : Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (n.val + 1))) (l : ℝ)) := by
  constructor
  intro g
  have hb := level_scaled_eigenvalue_bound n.val l g
  have hn : ((n.val + 1 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (show n.val + 1 ≤ 7 from n.isLt)
  have hp : 0 ≤ ((n.val + 1 : ℕ) : ℝ) := by positivity
  have hsq : ((n.val + 1 : ℕ) : ℝ) ^ 2 ≤ 49 := by nlinarith
  have hpi := Real.pi_gt_three
  have hl := l.2.2
  nlinarith [sq_nonneg (Real.pi - 3), mul_nonneg (sub_nonneg.mpr hsq) l.2.1.le]

end
end GaloisForLFunctions.RHTower.SelbergMaassStripGap
