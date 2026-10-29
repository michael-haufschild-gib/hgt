import GaloisForLFunctions.HTGeometry.CoordinateProductFourier
import GaloisForLFunctions.HTGeometry.GaussianThetaCharacteristics
import GaloisForLFunctions.RHTower.GaussianMomentFourier
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz

/-!
# Poisson summation for parity-weighted Gaussians

A Boolean profile selects a squarefree coordinate monomial. Scalar Gaussian
moments and finite-product Fourier factorization give one factor `-i/t` for each
odd coordinate and the usual dimensional factor `t^(-dim/2)`. The monomial is
bounded by a constant times half the Gaussian decay rate, proving integrability,
normal convergence, and absolute affine-lattice summability. Fourier modulation
and affine covariance then give Poisson summation with arbitrary shifts and phases.
-/

noncomputable section
open MeasureTheory
open scoped Classical FourierTransform

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

/-- The even Gaussian or its first odd moment, according to the parity bit. -/
def scalarParityGaussian (ε : Bool) (t x : ℝ) : ℂ :=
  (x : ℂ) ^ ε.toNat * (Real.exp (-(Real.pi * t) * x ^ 2) : ℂ)

theorem scalarParityGaussian_phase (ε : Bool) (t ξ x : ℝ) :
    Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
      scalarParityGaussian ε t x =
        (x : ℂ) ^ ε.toNat * RHTower.gaussPhase (Real.pi * t) (2 * Real.pi * ξ) x := by
  rw [scalarParityGaussian, Complex.ofReal_exp, RHTower.gaussPhase]
  calc
    _ = (x : ℂ) ^ ε.toNat * Complex.exp
        (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I +
          ((-(Real.pi * t) * x ^ 2 : ℝ) : ℂ)) := by
      rw [Complex.exp_add]
      ring
    _ = _ := by
      congr 1
      congr 1
      rw [Real.inner_apply]
      push_cast
      ring

theorem scalarParityGaussian_eq_moment_zero (ε : Bool) (t x : ℝ) :
    scalarParityGaussian ε t x =
      (x : ℂ) ^ ε.toNat * RHTower.gaussPhase (Real.pi * t) 0 x := by
  have h := scalarParityGaussian_phase ε t 0 x
  simpa only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul] using h

theorem integrable_scalarParityGaussian (ε : Bool) {t : ℝ} (ht : 0 < t) :
    Integrable (scalarParityGaussian ε t) := by
  have h := RHTower.integrable_gaussMomentIntegrand (mul_pos Real.pi_pos ht) ε.toNat 0
  exact h.congr (Filter.Eventually.of_forall
    (fun x => (scalarParityGaussian_eq_moment_zero ε t x).symm))

theorem fourier_scalarParityGaussian_eq_moment (ε : Bool) (t ξ : ℝ) :
    (𝓕 (scalarParityGaussian ε t)) ξ =
      RHTower.gaussMoment (Real.pi * t) ε.toNat (2 * Real.pi * ξ) := by
  rw [Real.fourier_eq', RHTower.gaussMoment]
  exact integral_congr_ae (Filter.Eventually.of_forall (scalarParityGaussian_phase ε t ξ))

/-- A scalar parity bit contributes `-i/t` to the reciprocal Gaussian transform. -/
theorem fourier_scalarParityGaussian (ε : Bool) {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    (𝓕 (scalarParityGaussian ε t)) ξ =
      (Real.sqrt (1 / t) : ℂ) * (-Complex.I / (t : ℂ)) ^ ε.toNat *
        scalarParityGaussian ε (1 / t) ξ := by
  have hpt := mul_pos Real.pi_pos ht
  have hp : Real.pi / (Real.pi * t) = 1 / t := by
    field_simp [Real.pi_ne_zero]
  have hk : RHTower.gaussKernel (Real.pi * t) (2 * Real.pi * ξ) =
      Real.exp (-(Real.pi * (1 / t)) * ξ ^ 2) := by
    rw [RHTower.gaussKernel]
    congr 1
    field_simp [Real.pi_ne_zero, ne_of_gt ht]
    ring
  have hj : (RHTower.gaussJetPoly (Real.pi * t) 1).eval (2 * Real.pi * ξ) = -ξ / t := by
    rw [RHTower.gaussJetPoly_succ (Real.pi * t) 0, RHTower.gaussJetPoly_zero]
    simp only [Polynomial.derivative_one, zero_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_one]
    field_simp [Real.pi_ne_zero, ne_of_gt ht]
  rw [fourier_scalarParityGaussian_eq_moment]
  cases ε with
  | false =>
    simp only [Bool.toNat_false, pow_zero, mul_one, scalarParityGaussian, one_mul]
    rw [RHTower.gaussMoment_zero hpt, hp, hk]
  | true =>
    simp only [Bool.toNat_true, pow_one, scalarParityGaussian]
    rw [RHTower.gaussMoment_eq hpt 1 (2 * Real.pi * ξ), hp, hk, hj]
    simp only [pow_one]
    push_cast
    ring

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "X" => ι → ℝ
local notation "Z" => ι → ℤ

/-- Total degree of a squarefree coordinate monomial. -/
def parityDegree (ε : ι → Bool) : ℕ := ∑ i, (ε i).toNat

/-- A squarefree monomial records the odd coordinate directions. -/
def parityMonomial (ε : ι → Bool) (x : E) : ℂ := ∏ i, (x i : ℂ) ^ (ε i).toNat

/-- A Gaussian with a squarefree coordinate parity factor. -/
def parityGaussian (ε : ι → Bool) (t : ℝ) (x : E) : ℂ :=
  parityMonomial ε x * gaussianKernel (Real.pi * t) x

theorem parityGaussian_eq_coordinateProduct (ε : ι → Bool) (t : ℝ) (x : E) :
    parityGaussian ε t x = coordinateProduct (fun i => scalarParityGaussian (ε i) t) x := by
  have hnorm : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [Real.inner_apply, pow_two]
  rw [parityGaussian, parityMonomial, gaussianKernel_eq_ofReal, coordinateProduct]
  simp only [scalarParityGaussian, Finset.prod_mul_distrib]
  congr 1
  rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum, hnorm]

theorem continuous_parityGaussian (ε : ι → Bool) (t : ℝ) :
    Continuous (parityGaussian ε t) := by
  have h : Continuous (parityMonomial ε) := by
    unfold parityMonomial
    fun_prop
  exact h.mul (continuous_gaussianKernel _)

theorem integrable_parityGaussian (ε : ι → Bool) {t : ℝ} (ht : 0 < t) :
    Integrable (parityGaussian ε t) := by
  have he : parityGaussian ε t = coordinateProduct (fun i => scalarParityGaussian (ε i) t) :=
    funext (parityGaussian_eq_coordinateProduct ε t)
  rw [he]
  exact integrable_coordinateProduct (fun i => integrable_scalarParityGaussian (ε i) ht)

/-- The Fourier multiplier combines the scalar Gaussian and odd-coordinate factors. -/
def parityFourierFactor (ε : ι → Bool) (t : ℝ) : ℂ :=
  (Real.sqrt (1 / t) : ℂ) ^ Fintype.card ι * (-Complex.I / (t : ℂ)) ^ parityDegree ε

theorem sqrt_inv_pow_card {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 / t)) ^ Fintype.card ι =
      t ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  rw [finrank_euclideanSpace, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : 0 ≤ 1 / t), one_div,
    Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  congr 1
  ring

theorem parityFourierFactor_eq (ε : ι → Bool) {t : ℝ} (ht : 0 < t) :
    parityFourierFactor ε t = ((t ^ (-((Module.finrank ℝ E : ℝ) / 2)) : ℝ) : ℂ) *
      (-Complex.I / (t : ℂ)) ^ parityDegree ε := by
  rw [parityFourierFactor, ← Complex.ofReal_pow, sqrt_inv_pow_card ht]

theorem fourier_parityGaussian (ε : ι → Bool) {t : ℝ} (ht : 0 < t) (ξ : E) :
    (𝓕 (parityGaussian ε t)) ξ = parityFourierFactor ε t * parityGaussian ε (1 / t) ξ := by
  have he : parityGaussian ε t = coordinateProduct (fun i => scalarParityGaussian (ε i) t) :=
    funext (parityGaussian_eq_coordinateProduct ε t)
  rw [he, fourier_coordinateProduct]
  calc
    _ = ∏ i, ((Real.sqrt (1 / t) : ℂ) * (-Complex.I / (t : ℂ)) ^ (ε i).toNat *
        scalarParityGaussian (ε i) (1 / t) (ξ i)) :=
      Finset.prod_congr rfl (fun i _ => fourier_scalarParityGaussian (ε i) ht (ξ i))
    _ = parityFourierFactor ε t * coordinateProduct
        (fun i => scalarParityGaussian (ε i) (1 / t)) ξ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Finset.prod_pow_eq_pow_sum]
      rfl
    _ = _ := by rw [← parityGaussian_eq_coordinateProduct]

theorem norm_parityMonomial_le (ε : ι → Bool) (x : E) :
    ‖parityMonomial ε x‖ ≤ ‖x‖ ^ parityDegree ε := by
  rw [parityMonomial, norm_prod]
  simp only [norm_pow, Complex.norm_real]
  calc
    _ ≤ ∏ i, ‖x‖ ^ (ε i).toNat := Finset.prod_le_prod
      (fun i _ => pow_nonneg (norm_nonneg _) _)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x i) _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- The polynomial factor is absorbed by half the Gaussian decay rate. -/
theorem exists_parityGaussian_norm_bound (ε : ι → Bool) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E,
      ‖parityGaussian ε t x‖ ≤ C * ‖gaussianKernel (Real.pi * (t / 2)) x‖ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  let m := parityDegree ε
  let C := Real.exp ((m : ℝ) ^ 2 / (2 * Real.pi)) / (Real.sqrt t) ^ m
  refine ⟨C, div_pos (Real.exp_pos _) (pow_pos hs m), ?_⟩
  intro x
  have hp := RHTower.pow_mul_exp_neg_half_pi_sq_le m
    (mul_nonneg hs.le (norm_nonneg x))
  have he : -(Real.pi / 2) * (Real.sqrt t * ‖x‖) ^ 2 =
      -(Real.pi * (t / 2)) * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    ring
  rw [he, mul_pow] at hp
  have hscaled : ‖x‖ ^ m * Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) ≤ C := by
    apply (le_div_iff₀ (pow_pos hs m)).mpr
    nlinarith only [hp]
  rw [parityGaussian, norm_mul, norm_gaussianKernel, norm_gaussianKernel]
  calc
    _ ≤ ‖x‖ ^ m * Real.exp (-(Real.pi * t) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (norm_parityMonomial_le ε x) (Real.exp_pos _).le
    _ = (‖x‖ ^ m * Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2)) *
        Real.exp (-(Real.pi * (t / 2)) * ‖x‖ ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscaled (Real.exp_pos _).le

/-- Parity Gaussians admit a common summable affine-lattice majorant on bounded sets. -/
theorem parityGaussian_summable_affine_translates (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ u : Z → ℝ, Summable u ∧ ∀ x : X, ‖x‖ ≤ R → ∀ k : Z,
      ‖parityGaussian ε t (B (WithLp.toLp 2 (x + integerPoint k)) + v)‖ ≤ u k := by
  obtain ⟨C, hC, hbound⟩ := exists_parityGaussian_norm_bound ε ht
  obtain ⟨u, hu, hub⟩ := gaussian_summable_affine_translates B
    (mul_pos Real.pi_pos (half_pos ht)) v R hR
  refine ⟨fun k => C * u k, hu.mul_left C, fun x hx k => ?_⟩
  exact (hbound _).trans (mul_le_mul_of_nonneg_left (hub x hx k) hC.le)

theorem summable_norm_parityGaussian_affine (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v : E) :
    Summable (fun k : Z => ‖parityGaussian ε t (B (euclideanIntegerPoint k) + v)‖) := by
  obtain ⟨u, hu, hb⟩ := parityGaussian_summable_affine_translates B ε ht v 0 le_rfl
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hu
  intro k
  simpa only [zero_add, euclideanIntegerPoint] using hb 0 (by simp) k

/-- Additive modulation of the parity Gaussian. -/
def parityModulation (ε : ι → Bool) (t : ℝ) (w x : E) : ℂ :=
  latticePhase x w * parityGaussian ε t x

theorem norm_parityModulation (ε : ι → Bool) (t : ℝ) (w x : E) :
    ‖parityModulation ε t w x‖ = ‖parityGaussian ε t x‖ := by
  rw [parityModulation, norm_mul, norm_latticePhase, one_mul]

theorem continuous_parityModulation (ε : ι → Bool) (t : ℝ) (w : E) :
    Continuous (parityModulation ε t w) :=
  (continuous_latticePhase w).mul (continuous_parityGaussian ε t)

theorem integrable_parityModulation (ε : ι → Bool) {t : ℝ} (ht : 0 < t) (w : E) :
    Integrable (parityModulation ε t w) :=
  (integrable_parityGaussian ε ht).mono
    (continuous_parityModulation ε t w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_parityModulation ε t w x).le)

theorem fourier_parityModulation (ε : ι → Bool) {t : ℝ} (ht : 0 < t) (w ξ : E) :
    (𝓕 (parityModulation ε t w)) ξ =
      parityFourierFactor ε t * parityGaussian ε (1 / t) (ξ - w) := by
  change (𝓕 (fun x => latticePhase x w * parityGaussian ε t x)) ξ = _
  rw [fourier_mul_latticePhase, fourier_parityGaussian ε ht]

theorem fourier_affine_parityModulation (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w ξ : E) :
    (𝓕 (fun x => parityModulation ε t w (B x + v))) ξ =
      latticeScale B • (latticePhase v (inverseAdjoint B ξ) *
        (parityFourierFactor ε t * parityGaussian ε (1 / t) (inverseAdjoint B ξ - w))) := by
  have h := fourier_comp_linearEquiv (fun x => parityModulation ε t w (x + v)) B ξ
  rw [fourier_comp_add, fourier_parityModulation ε ht] at h
  exact h

theorem summable_norm_parityModulation_affine (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    Summable (fun k : Z => ‖parityModulation ε t w (B (euclideanIntegerPoint k) + v)‖) := by
  simpa only [norm_parityModulation] using summable_norm_parityGaussian_affine B ε ht v

theorem summable_norm_dual_parity_phase (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    Summable (fun k : Z => ‖latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
      parityGaussian ε t (inverseAdjoint B (euclideanIntegerPoint k) - w)‖) := by
  simpa only [norm_mul, norm_latticePhase, one_mul, sub_eq_add_neg,
    inverseAdjointEquiv_apply] using
      summable_norm_parityGaussian_affine (inverseAdjointEquiv B) ε ht (-w)

/-- Poisson summation for parity Gaussians with arbitrary shifts and additive phases. -/
theorem parity_gaussian_poisson_with_characteristics (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    (∑' k : Z, parityModulation ε t w (B (euclideanIntegerPoint k) + v)) =
      (latticeScale B : ℂ) * parityFourierFactor ε t *
        ∑' k : Z, latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
          parityGaussian ε (1 / t) (inverseAdjoint B (euclideanIntegerPoint k) - w) := by
  have ht' : 0 < 1 / t := one_div_pos.mpr ht
  have hs : Summable (fun k : Z =>
      (𝓕 (fun x => parityModulation ε t w (B x + v))) (euclideanIntegerPoint k)) := by
    apply Summable.of_norm
    refine (((summable_norm_dual_parity_phase B ε ht' v w).mul_left
      ‖parityFourierFactor ε t‖).mul_left |latticeScale B|).congr fun k => ?_
    rw [fourier_affine_parityModulation B ε ht]
    simp only [norm_smul, Real.norm_eq_abs, norm_mul, norm_latticePhase, one_mul]
  have hc : Continuous (fun x => parityModulation ε t w (B x + v)) :=
    (continuous_parityModulation ε t w).comp (B.continuous.add continuous_const)
  have hi : Integrable (fun x => parityModulation ε t w (B x + v)) :=
    integrable_comp_linearEquiv ((integrable_parityModulation ε ht w).comp_add_right v) B
  have hn : ∀ R : ℝ, 0 ≤ R → ∃ u : Z → ℝ, Summable u ∧
      ∀ x : X, ‖x‖ ≤ R → ∀ k : Z,
        ‖parityModulation ε t w (B (WithLp.toLp 2 (x + integerPoint k)) + v)‖ ≤ u k := by
    intro R hR
    obtain ⟨u, hu, hb⟩ := parityGaussian_summable_affine_translates B ε ht v R hR
    refine ⟨u, hu, fun x hx k => ?_⟩
    rw [norm_parityModulation]
    exact hb x hx k
  calc
    _ = ∑' k : Z, (𝓕 (fun x => parityModulation ε t w (B x + v)))
        (euclideanIntegerPoint k) := euclidean_poisson_of_summable_translates hc hi hn hs
    _ = ∑' k : Z, (latticeScale B : ℂ) * parityFourierFactor ε t *
        (latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
          parityGaussian ε (1 / t) (inverseAdjoint B (euclideanIntegerPoint k) - w)) := by
      apply tsum_congr
      intro k
      rw [fourier_affine_parityModulation B ε ht]
      simp only [Complex.real_smul]
      ring
    _ = _ := by rw [tsum_mul_left]

/-- The normalized multiplier is `t^(-dim/2)` times one `-i/t` for each odd coordinate. -/
theorem parity_gaussian_theta_characteristics (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    (∑' k : Z, parityModulation ε t w (B (euclideanIntegerPoint k) + v)) =
      (latticeScale B : ℂ) * ((t ^ (-((Module.finrank ℝ E : ℝ) / 2)) : ℝ) : ℂ) *
        (-Complex.I / (t : ℂ)) ^ parityDegree ε *
          ∑' k : Z, latticePhase v (inverseAdjoint B (euclideanIntegerPoint k)) *
            parityGaussian ε (1 / t) (inverseAdjoint B (euclideanIntegerPoint k) - w) := by
  simpa only [parityFourierFactor_eq ε ht, mul_assoc] using
    parity_gaussian_poisson_with_characteristics B ε ht v w

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
