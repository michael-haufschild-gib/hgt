import GaloisForLFunctions.HTGeometry.GaussianLatticeTheta

/-!
# Gaussian theta inversion with characteristics

A spatial shift contributes a Fourier phase, while modulation translates dual
frequency. Normal convergence of affine Gaussian samples supplies absolute
convergence on both lattices. Their Poisson identity therefore holds for every
pair of real characteristics and every positive Gaussian decay rate.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform


namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "X" => ι → ℝ
local notation "Z" => ι → ℤ

/-- The additive character determined by the Euclidean pairing. -/
def latticePhase (x w : E) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ x w : ℝ) * Complex.I)

theorem norm_latticePhase (x w : E) : ‖latticePhase x w‖ = 1 := by
  simp [latticePhase, Complex.norm_exp]

theorem continuous_latticePhase (w : E) : Continuous (fun x => latticePhase x w) := by
  unfold latticePhase
  fun_prop

/-- Modulation translates Fourier frequency. -/
theorem fourier_mul_latticePhase (f : E → ℂ) (v w : E) :
    (𝓕 (fun x => latticePhase x v * f x)) w = (𝓕 f) (w - v) := by
  simp only [Real.fourier_eq', latticePhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_right]
  push_cast
  ring

/-- One summable Gaussian bound controls all bounded translates of an affine lattice. -/
theorem gaussian_summable_affine_translates (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (v : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ u : Z → ℝ, Summable u ∧ ∀ x : X, ‖x‖ ≤ R → ∀ k : Z,
      ‖gaussianKernel a (B (WithLp.toLp 2 (x + integerPoint k)) + v)‖ ≤ u k := by
  -- Pull the spatial shift back to integer coordinates and enlarge the radius.
  let z : X := (B.symm v).ofLp
  obtain ⟨u, hu, hb⟩ := gaussian_summable_translates B ha
    (R + ‖z‖) (add_nonneg hR (norm_nonneg z))
  have he (x : X) (k : Z) :
      B (WithLp.toLp 2 ((x + z) + integerPoint k)) =
        B (WithLp.toLp 2 (x + integerPoint k)) + v := by
    change B ((WithLp.toLp 2 x + B.symm v) + euclideanIntegerPoint k) =
      B (WithLp.toLp 2 x + euclideanIntegerPoint k) + v
    simp only [map_add, B.apply_symm_apply]
    abel
  refine ⟨u, hu, fun x hx k => ?_⟩
  have hx' : ‖x + z‖ ≤ R + ‖z‖ :=
    (norm_add_le x z).trans (add_le_add hx le_rfl)
  simpa only [he] using hb (x + z) hx' k

/-- Gaussian samples on every affine full lattice are absolutely summable. -/
theorem summable_norm_gaussian_affine_lattice (B : E ≃L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (v : E) :
    Summable (fun k : Z => ‖gaussianKernel a (B (euclideanIntegerPoint k) + v)‖) := by
  obtain ⟨u, hu, hb⟩ := gaussian_summable_affine_translates B ha v 0 le_rfl
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hu
  intro k
  simpa only [zero_add, euclideanIntegerPoint] using hb 0 (by simp) k

/-- A radial Gaussian multiplied by an additive character. -/
def gaussianModulation (a : ℝ) (w x : E) : ℂ := latticePhase x w * gaussianKernel a x

theorem norm_gaussianModulation (a : ℝ) (w x : E) :
    ‖gaussianModulation a w x‖ = ‖gaussianKernel a x‖ := by
  rw [gaussianModulation, norm_mul, norm_latticePhase, one_mul]

theorem continuous_gaussianModulation (a : ℝ) (w : E) :
    Continuous (gaussianModulation a w) :=
  (continuous_latticePhase w).mul (continuous_gaussianKernel a)

theorem integrable_gaussianModulation {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (gaussianModulation a w) := by
  exact (integrable_gaussianKernel ha).mono
    (continuous_gaussianModulation a w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_gaussianModulation a w x).le)

theorem fourier_gaussianModulation {a : ℝ} (ha : 0 < a) (w ξ : E) :
    (𝓕 (gaussianModulation a w)) ξ =
      gaussianFactor (ι := ι) a • gaussianKernel (Real.pi ^ 2 / a) (ξ - w) := by
  change (𝓕 (fun x => latticePhase x w * gaussianKernel a x)) ξ = _
  rw [fourier_mul_latticePhase, fourier_gaussianKernel ha]

/-- The exact Fourier transform after modulation, translation, and a lattice map. -/
theorem fourier_affine_gaussianModulation (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (v w ξ : E) :
    (𝓕 (fun x => gaussianModulation a w (B x + v))) ξ =
      latticeScale B • (latticePhase v (inverseAdjoint B ξ) *
        (gaussianFactor (ι := ι) a •
          gaussianKernel (Real.pi ^ 2 / a) (inverseAdjoint B ξ - w))) := by
  have h := fourier_comp_linearEquiv (fun x => gaussianModulation a w (x + v)) B ξ
  rw [fourier_comp_add, fourier_gaussianModulation ha] at h
  exact h

/-- Modulation preserves absolute convergence on an affine lattice. -/
theorem summable_norm_gaussianModulation_affine (B : E ≃L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (v w : E) :
    Summable (fun k : Z => ‖gaussianModulation a w (B (euclideanIntegerPoint k) + v)‖) := by
  simpa only [norm_gaussianModulation] using summable_norm_gaussian_affine_lattice B ha v

/-- The shifted dual Gaussian series converges absolutely, even with its phase. -/
theorem summable_norm_dual_gaussian_phase (B : E ≃L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (v w : E) :
    Summable (fun k : Z => ‖latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
      gaussianKernel a (inverseAdjoint B (euclideanIntegerPoint k) - w)‖) := by
  simpa only [norm_mul, norm_latticePhase, one_mul, sub_eq_add_neg,
    inverseAdjointEquiv_apply] using
      summable_norm_gaussian_affine_lattice (inverseAdjointEquiv B) ha (-w)

/-- Gaussian Poisson summation with arbitrary spatial and frequency shifts. -/
theorem gaussian_lattice_poisson_with_characteristics (B : E ≃L[ℝ] E) {a : ℝ}
    (ha : 0 < a) (v w : E) :
    (∑' k : Z, gaussianModulation a w (B (euclideanIntegerPoint k) + v)) =
      latticeScale B • gaussianFactor (ι := ι) a •
        ∑' k : Z, latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
          gaussianKernel (Real.pi ^ 2 / a) (inverseAdjoint B (euclideanIntegerPoint k) - w) := by
  have ha' : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  -- The Fourier coefficients are a phase times a shifted dual Gaussian.
  have hs : Summable (fun k : Z =>
      (𝓕 (fun x => gaussianModulation a w (B x + v))) (euclideanIntegerPoint k)) := by
    apply Summable.of_norm
    refine (((summable_norm_dual_gaussian_phase B ha' v w).mul_left
      |gaussianFactor (ι := ι) a|).mul_left |latticeScale B|).congr fun k => ?_
    rw [fourier_affine_gaussianModulation B ha]
    simp only [norm_smul, Real.norm_eq_abs, norm_mul, norm_latticePhase, one_mul]
  have hc : Continuous (fun x => gaussianModulation a w (B x + v)) :=
    (continuous_gaussianModulation a w).comp (B.continuous.add continuous_const)
  have hi : Integrable (fun x => gaussianModulation a w (B x + v)) :=
    integrable_comp_linearEquiv ((integrable_gaussianModulation ha w).comp_add_right v) B
  have hn : ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ k : Z,
        ‖gaussianModulation a w (B (WithLp.toLp 2 (x + integerPoint k)) + v)‖ ≤ u k := by
    intro R hR
    obtain ⟨u, hu, hb⟩ := gaussian_summable_affine_translates B ha v R hR
    refine ⟨u, hu, fun x hx k => ?_⟩
    rw [norm_gaussianModulation]
    exact hb x hx k
  calc
    _ = ∑' k : Z, (𝓕 (fun x => gaussianModulation a w (B x + v)))
        (euclideanIntegerPoint k) := euclidean_poisson_of_summable_translates hc hi hn hs
    _ = ∑' k : Z, latticeScale B • gaussianFactor (ι := ι) a •
        (latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
          gaussianKernel (Real.pi ^ 2 / a) (inverseAdjoint B (euclideanIntegerPoint k) - w)) := by
      apply tsum_congr
      intro k
      rw [fourier_affine_gaussianModulation B ha]
      simp only [Complex.real_smul]
      ring
    _ = _ := by simp only [Complex.real_smul, tsum_mul_left]

/-- Theta inversion with real characteristics in the conventional `πt` normalization. -/
theorem gaussian_theta_characteristics (B : E ≃L[ℝ] E) {t : ℝ}
    (ht : 0 < t) (v w : E) :
    (∑' k : Z, gaussianModulation (Real.pi * t) w (B (euclideanIntegerPoint k) + v)) =
      latticeScale B • t ^ (-((Module.finrank ℝ E : ℝ) / 2)) •
        ∑' k : Z, latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
          gaussianKernel (Real.pi / t) (inverseAdjoint B (euclideanIntegerPoint k) - w) := by
  have he : Real.pi ^ 2 / (Real.pi * t) = Real.pi / t := by field_simp
  simpa only [gaussianFactor_pi_mul ht, he] using
    gaussian_lattice_poisson_with_characteristics B (mul_pos Real.pi_pos ht) v w

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
