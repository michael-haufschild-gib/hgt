import GaloisForLFunctions.HTGeometry.FiniteMatrixSpectralHankel

/-!
# Continuum matrix-valued spectral block Hankel geometry

A continuum of latent spectral states `omega` carries a real transfer node and a finite family
of field/reporter couplings.  The block moment matrix indexed jointly by clock order and channel
is the integral Gram matrix of the features

```text
coupling(omega, channel) * node(omega)^order.
```

Pairwise integrability alone makes every finite block positive semidefinite.  If every nonzero
joint clock--channel combination survives on a set of positive spectral measure, the block is
positive definite and its determinant is strictly positive.  This is an observability theorem:
strictness is exactly positive-measure separation of finite reporter combinations, not a premise
about temporal evolution or a field equation.

The result extends `FiniteMatrixSpectralHankel` from finitely many common spectral lines to a
continuum.  It applies to matrix-valued Källén--Lehmann data, multi-field EFT positivity,
mixed scalar/Higgs sectors, lattice correlation matrices, continuum relaxation spectra, and
multi-reporter compact-object or gravitational-wave spectra.

Physics provenance: Li--Xu--Yang--Zhang--Zhou, *Positivity in Multi-Field EFTs*, Phys. Rev. Lett.
127 (2021), 121601, DOI 10.1103/PhysRevLett.127.121601; Wan--Zhou, *Matrix moment approach to
positivity bounds and UV reconstruction from IR*, arXiv:2411.11964; Abbott--Jay--Oare, *Moment
problems and bounds for matrix-valued smeared spectral functions*, arXiv:2508.01377.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Integral Gram matrix of a finite family of real measurable spectral features.  Measurability
is not needed for the definition; integrability hypotheses enter the positivity theorems. -/
def integralFeatureGram
    (μ : Measure Ω) (feature : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ ω, feature i ω * feature j ω ∂μ

/-- The observed continuum feature assembled from finitely many reporter coefficients. -/
def integralFeatureCombination
    [Fintype ι] (feature : ι → Ω → ℝ) (x : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, x i * feature i ω

/-- Every real integral feature Gram matrix is Hermitian. -/
theorem integralFeatureGram_isHermitian
    (μ : Measure Ω) (feature : ι → Ω → ℝ) :
    (integralFeatureGram μ feature).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [integralFeatureGram, star_trivial]
  congr 1
  funext ω
  ring

variable [Fintype ι]

/-- **Continuum Gram identity.**  The quadratic form of the integral feature matrix is the
integral of the squared observed feature combination. -/
theorem integralFeatureGram_quadratic_eq_integral_sq
    (μ : Measure Ω) (feature : ι → Ω → ℝ)
    (hprod : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) μ)
    (x : ι → ℝ) :
    dotProduct (star x) ((integralFeatureGram μ feature).mulVec x) =
      ∫ ω, integralFeatureCombination feature x ω ^ (2 : ℕ) ∂μ := by
  have hterm : ∀ i j,
      Integrable (fun ω => (x i * feature i ω) * (x j * feature j ω)) μ := by
    intro i j
    have h := (hprod i j).const_mul (x i * x j)
    simpa only [Pi.mul_apply] using h.congr (ae_of_all _ fun ω => by ring)
  calc
    dotProduct (star x) ((integralFeatureGram μ feature).mulVec x) =
        ∑ i, ∑ j, x i * (∫ ω, feature i ω * feature j ω ∂μ) * x j := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, integralFeatureGram]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, ∫ ω, (x i * feature i ω) * (x j * feature j ω) ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      calc
        x i * (∫ ω, feature i ω * feature j ω ∂μ) * x j =
            (x i * x j) * ∫ ω, feature i ω * feature j ω ∂μ := by ring
        _ = ∫ ω, (x i * x j) * (feature i ω * feature j ω) ∂μ := by
          rw [integral_const_mul]
        _ = ∫ ω, (x i * feature i ω) * (x j * feature j ω) ∂μ := by
          congr 1
          funext ω
          ring
    _ = ∫ ω, ∑ i, ∑ j,
          (x i * feature i ω) * (x j * feature j ω) ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ]
        exact fun j hj => hterm i j
      · intro i hi
        exact integrable_finsetSum Finset.univ (fun j hj => hterm i j)
    _ = ∫ ω, integralFeatureCombination feature x ω ^ (2 : ℕ) ∂μ := by
      congr 1
      funext ω
      rw [integralFeatureCombination, pow_two, Fintype.sum_mul_sum]

/-- Pairwise-integrable continuum features give a positive-semidefinite integral Gram matrix. -/
theorem integralFeatureGram_posSemidef
    (μ : Measure Ω) (feature : ι → Ω → ℝ)
    (hprod : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) μ) :
    (integralFeatureGram μ feature).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact integralFeatureGram_isHermitian μ feature
  · intro x
    rw [integralFeatureGram_quadratic_eq_integral_sq μ feature hprod x]
    exact integral_nonneg fun ω => sq_nonneg _

/-- Positive-measure separation of every nonzero reporter combination upgrades the integral
feature Gram matrix from semidefinite to positive definite. -/
theorem integralFeatureGram_posDef_of_support
    (μ : Measure Ω) (feature : ι → Ω → ℝ)
    (hprod : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) μ)
    (hseparate : ∀ x : ι → ℝ, x ≠ 0 →
      0 < μ (Function.support (integralFeatureCombination feature x))) :
    (integralFeatureGram μ feature).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact integralFeatureGram_isHermitian μ feature
  · intro x hx
    rw [integralFeatureGram_quadratic_eq_integral_sq μ feature hprod x]
    rw [integral_pos_iff_support_of_nonneg (fun ω => sq_nonneg _)]
    · simpa [Function.support, integralFeatureCombination] using hseparate x hx
    · have hsquare : (fun ω => integralFeatureCombination feature x ω ^ (2 : ℕ)) =
          fun ω => ∑ i, ∑ j,
            (x i * feature i ω) * (x j * feature j ω) := by
        funext ω
        rw [integralFeatureCombination, pow_two, Fintype.sum_mul_sum]
      rw [hsquare]
      exact integrable_finsetSum Finset.univ fun i hi =>
        integrable_finsetSum Finset.univ fun j hj => by
          have h := (hprod i j).const_mul (x i * x j)
          simpa only [Pi.mul_apply] using h.congr (ae_of_all _ fun ω => by ring)

omit [Fintype ι] in
/-- Integral feature Gram matrices send addition of positive measures to matrix addition. -/
theorem integralFeatureGram_add_measure
    (μ ν : Measure Ω) (feature : ι → Ω → ℝ)
    (hμ : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) μ)
    (hν : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) ν) :
    integralFeatureGram (μ + ν) feature =
      integralFeatureGram μ feature + integralFeatureGram ν feature := by
  ext i j
  exact integral_add_measure (hμ i j) (hν i j)

/-- **Pole-plus-continuum strictness.**  A separating spectral component remains strictly
observable after adding any other positive pairwise-integrable spectral component. -/
theorem integralFeatureGram_add_measure_posDef_of_left_support
    (μ ν : Measure Ω) (feature : ι → Ω → ℝ)
    (hμ : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) μ)
    (hν : ∀ i j, Integrable (fun ω => feature i ω * feature j ω) ν)
    (hseparate : ∀ x : ι → ℝ, x ≠ 0 →
      0 < μ (Function.support (integralFeatureCombination feature x))) :
    (integralFeatureGram (μ + ν) feature).PosDef := by
  rw [integralFeatureGram_add_measure μ ν feature hμ hν]
  exact (integralFeatureGram_posDef_of_support μ feature hμ hseparate).add_posSemidef
    (integralFeatureGram_posSemidef ν feature hν)

/-! ### Continuum matrix-valued spectral specialization -/

/-- Matrix-valued moment of a continuum spectrum with finitely many real reporter channels. -/
def continuumMatrixSpectralMoment {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b => ∫ ω, coupling ω a * coupling ω b * node ω ^ k ∂μ

/-- Block moment matrix indexed jointly by clock order and reporter/field channel. -/
def continuumMatrixSpectralBlockHankel {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (n : ℕ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ :=
  fun ia jb => continuumMatrixSpectralMoment μ node coupling
    ((ia.1 : ℕ) + (jb.1 : ℕ)) ia.2 jb.2

/-- Joint clock-channel feature at one latent spectral state. -/
def continuumMatrixSpectralFeature {m n : ℕ}
    (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (ia : Fin n × Fin m) (ω : Ω) : ℝ :=
  coupling ω ia.2 * node ω ^ (ia.1 : ℕ)

/-- The continuum block moment matrix is exactly the integral Gram matrix of its joint spectral
features. -/
theorem continuumMatrixSpectralBlockHankel_eq_integralFeatureGram {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (n : ℕ) :
    continuumMatrixSpectralBlockHankel μ node coupling n =
      integralFeatureGram μ (continuumMatrixSpectralFeature node coupling) := by
  ext ia jb
  simp only [continuumMatrixSpectralBlockHankel, continuumMatrixSpectralMoment,
    integralFeatureGram, continuumMatrixSpectralFeature]
  congr 1
  funext ω
  rw [pow_add]
  ring

/-- **Continuum multi-field spectral positivity.**  Pairwise integrability of the joint
clock-channel features makes every finite block moment matrix positive semidefinite. -/
theorem continuumMatrixSpectralBlockHankel_posSemidef {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (n : ℕ)
    (hint : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) μ) :
    (continuumMatrixSpectralBlockHankel μ node coupling n).PosSemidef := by
  rw [continuumMatrixSpectralBlockHankel_eq_integralFeatureGram]
  exact integralFeatureGram_posSemidef μ
    (continuumMatrixSpectralFeature node coupling) hint

/-- Positive-measure joint reporter separation makes the continuum block moment matrix positive
definite. -/
theorem continuumMatrixSpectralBlockHankel_posDef_of_jointSeparation {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (n : ℕ)
    (hint : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) μ)
    (hseparate : ∀ x : Fin n × Fin m → ℝ, x ≠ 0 →
      0 < μ (Function.support
        (integralFeatureCombination
          (continuumMatrixSpectralFeature node coupling) x))) :
    (continuumMatrixSpectralBlockHankel μ node coupling n).PosDef := by
  rw [continuumMatrixSpectralBlockHankel_eq_integralFeatureGram]
  exact integralFeatureGram_posDef_of_support μ
    (continuumMatrixSpectralFeature node coupling) hint hseparate

/-- A jointly separating continuum or discrete spectral component keeps the full mixed
pole-plus-continuum block positive definite after any additional positive spectral component is
added. -/
theorem continuumMatrixSpectralBlockHankel_add_measure_posDef_of_leftSeparation
    {m : ℕ}
    (μ ν : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (n : ℕ)
    (hμ : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) μ)
    (hν : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) ν)
    (hseparate : ∀ x : Fin n × Fin m → ℝ, x ≠ 0 →
      0 < μ (Function.support
        (integralFeatureCombination
          (continuumMatrixSpectralFeature node coupling) x))) :
    (continuumMatrixSpectralBlockHankel (μ + ν) node coupling n).PosDef := by
  rw [continuumMatrixSpectralBlockHankel_eq_integralFeatureGram]
  exact integralFeatureGram_add_measure_posDef_of_left_support μ ν
    (continuumMatrixSpectralFeature node coupling) hμ hν hseparate

/-- Joint positive-measure separation makes every finite continuum block determinant strictly
positive. -/
theorem det_continuumMatrixSpectralBlockHankel_pos_of_jointSeparation {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (n : ℕ)
    (hint : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) μ)
    (hseparate : ∀ x : Fin n × Fin m → ℝ, x ≠ 0 →
      0 < μ (Function.support
        (integralFeatureCombination
          (continuumMatrixSpectralFeature node coupling) x))) :
    0 < (continuumMatrixSpectralBlockHankel μ node coupling n).det :=
  (continuumMatrixSpectralBlockHankel_posDef_of_jointSeparation
    μ node coupling n hint hseparate).det_pos

/-- Scalar moment sequence observed in one selected field/reporter channel. -/
def continuumMatrixSpectralChannelMoment {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (a : Fin m) (k : ℕ) : ℝ :=
  continuumMatrixSpectralMoment μ node coupling k a a

/-- A single-channel Hankel matrix is a principal submatrix of the joint spectral block. -/
theorem momentHankelMatrix_continuumMatrixSpectralChannelMoment_eq_submatrix {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (a : Fin m) (n : ℕ) :
    momentHankelMatrix
        (continuumMatrixSpectralChannelMoment μ node coupling a) n =
      (continuumMatrixSpectralBlockHankel μ node coupling n).submatrix
        (fun i => (i, a)) (fun i => (i, a)) := by
  rfl

/-- **Scalar extraction law.**  Joint continuum separation discharges strict scalar Hankel
positivity in every individual channel.  This connects multi-field spectral representations
directly to the existing scalar moment and RH-facing determinant APIs. -/
theorem det_momentHankelMatrix_continuumMatrixSpectralChannelMoment_pos_of_jointSeparation
    {m : ℕ}
    (μ : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (a : Fin m) (n : ℕ)
    (hint : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) μ)
    (hseparate : ∀ x : Fin n × Fin m → ℝ, x ≠ 0 →
      0 < μ (Function.support
        (integralFeatureCombination
          (continuumMatrixSpectralFeature node coupling) x))) :
    0 < (momentHankelMatrix
      (continuumMatrixSpectralChannelMoment μ node coupling a) n).det := by
  rw [momentHankelMatrix_continuumMatrixSpectralChannelMoment_eq_submatrix]
  exact ((continuumMatrixSpectralBlockHankel_posDef_of_jointSeparation
    μ node coupling n hint hseparate).submatrix
      (fun i j h => congrArg Prod.fst h)).det_pos

/-- Mixed pole-plus-continuum strictness descends to every scalar reporter channel.  One
separating positive component is sufficient; all other positive components may be merely
semidefinite. -/
theorem det_momentHankelMatrix_continuumMatrixSpectralChannelMoment_add_measure_pos_of_leftSeparation
    {m : ℕ}
    (μ ν : Measure Ω) (node : Ω → ℝ) (coupling : Ω → Fin m → ℝ)
    (a : Fin m) (n : ℕ)
    (hμ : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) μ)
    (hν : ∀ ia jb : Fin n × Fin m,
      Integrable (fun ω =>
        continuumMatrixSpectralFeature node coupling ia ω *
          continuumMatrixSpectralFeature node coupling jb ω) ν)
    (hseparate : ∀ x : Fin n × Fin m → ℝ, x ≠ 0 →
      0 < μ (Function.support
        (integralFeatureCombination
          (continuumMatrixSpectralFeature node coupling) x))) :
    0 < (momentHankelMatrix
      (continuumMatrixSpectralChannelMoment (μ + ν) node coupling a) n).det := by
  rw [momentHankelMatrix_continuumMatrixSpectralChannelMoment_eq_submatrix]
  exact ((continuumMatrixSpectralBlockHankel_add_measure_posDef_of_leftSeparation
    μ ν node coupling n hμ hν hseparate).submatrix
      (fun i j h => congrArg Prod.fst h)).det_pos

end

end HTGeometry
