import GaloisForLFunctions.HTGeometry.CauchyJetFrame
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Complete inverse-Cholesky tower selection

This module formalizes the set-theoretic selector in the cofinal Cholesky manuscript. Fourier
characters determine a finite measure on an additive circle. The real Cayley transform is a
continuous measurable embedding into that circle. Consequently all positive Cayley moments
determine a real probability measure, and equality of every canonical inverse-Cholesky section
selects exactly one carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- Integration against a finite measure as a continuous functional on the continuous functions
of a compact space. -/
noncomputable def continuousMapIntegral (mu : Measure X) [IsFiniteMeasure mu] :
    C(X, Complex) →L[Complex] Complex :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂mu
      map_add' := by
        intro f g
        exact integral_add
          ((BoundedContinuousFunction.mkOfCompact f).integrable mu)
          ((BoundedContinuousFunction.mkOfCompact g).integrable mu)
      map_smul' := by
        intro c f
        exact integral_smul c f }
    (mu.real Set.univ)
    (fun f => by
      simpa only [BoundedContinuousFunction.norm_mkOfCompact]
        using! (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm mu)

@[simp]
theorem continuousMapIntegral_apply (mu : Measure X) [IsFiniteMeasure mu]
    (f : C(X, Complex)) :
    continuousMapIntegral mu f = ∫ x, f x ∂mu := rfl

variable {T : Real} [Fact (0 < T)]

/-- A finite measure on an additive circle is determined by all of its Fourier-character
integrals. -/
theorem addCircle_measure_eq_of_fourier_integral_eq
    (mu nu : Measure (AddCircle T)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : forall n : Int,
      (∫ z, fourier n z ∂mu) = ∫ z, fourier n z ∂nu) :
    mu = nu := by
  let L : C(AddCircle T, Complex) →L[Complex] Complex :=
    continuousMapIntegral mu - continuousMapIntegral nu
  have hspan : Submodule.span Complex (Set.range (@fourier T)) ≤ L.ker := by
    rw [Submodule.span_le]
    rintro f ⟨n, rfl⟩
    change (∫ z, fourier n z ∂mu) - ∫ z, fourier n z ∂nu = 0
    rw [h n, sub_self]
  have htop : (⊤ : Submodule Complex C(AddCircle T, Complex)) ≤ L.ker := by
    rw [← span_fourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan (ContinuousLinearMap.isClosed_ker L)
  have hall (f : C(AddCircle T, Complex)) :
      (∫ z, f z ∂mu) = ∫ z, f z ∂nu := by
    have hf : f ∈ L.ker := htop Submodule.mem_top
    change (∫ z, f z ∂mu) - ∫ z, f z ∂nu = 0 at hf
    exact sub_eq_zero.mp hf
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(AddCircle T, Complex) :=
    ⟨fun x => (f x : Complex), Complex.continuous_ofReal.comp f.continuous⟩
  have hc := hall fc
  have hmu : Integrable fc mu := (BoundedContinuousFunction.mkOfCompact fc).integrable mu
  have hnu : Integrable fc nu := (BoundedContinuousFunction.mkOfCompact fc).integrable nu
  calc
    ∫ x, f x ∂mu = ∫ x, Complex.re (fc x) ∂mu := by rfl
    _ = Complex.re (∫ x, fc x ∂mu) := integral_re hmu
    _ = Complex.re (∫ x, fc x ∂nu) := congrArg Complex.re hc
    _ = ∫ x, Complex.re (fc x) ∂nu := (integral_re hnu).symm
    _ = ∫ x, f x ∂nu := by rfl

/-- For probability measures, nonnegative Fourier characters suffice: the negative characters are
their complex conjugates. -/
theorem addCircle_measure_eq_of_nat_fourier_integral_eq
    (mu nu : Measure (AddCircle T)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : forall n : Nat,
      (∫ z, fourier (n : Int) z ∂mu) = ∫ z, fourier (n : Int) z ∂nu) :
    mu = nu := by
  apply addCircle_measure_eq_of_fourier_integral_eq
  intro n
  cases n with
  | ofNat k => exact h k
  | negSucc k =>
      rw [show Int.negSucc k = -((k + 1 : Nat) : Int) by omega]
      simp_rw [fourier_neg]
      rw [integral_conj, integral_conj, h (k + 1)]

/-- The Cayley transform has unit norm on the real line. -/
theorem norm_realCayley (x : Real) : norm (realCayley x) = 1 := by
  have hnorm : norm ((x : Complex) - I) = norm ((x : Complex) + I) := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    norm_num [Complex.normSq_apply]
  rw [realCayley, norm_div, hnorm, div_self]
  rw [norm_ne_zero_iff]
  intro h
  have him := congrArg Complex.im h
  norm_num [Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im] at him

/-- Cayley transform valued in the multiplicative unit circle. -/
def circleCayley (x : Real) : Circle :=
  ⟨realCayley x, mem_sphere_zero_iff_norm.mpr (norm_realCayley x)⟩

@[simp]
theorem circleCayley_coe (x : Real) : (circleCayley x : Complex) = realCayley x := rfl

lemma real_add_I_ne_zero (x : Real) : (x : Complex) + I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im] at him

/-- The real Cayley transform is continuous. -/
theorem continuous_realCayley : Continuous realCayley := by
  unfold realCayley
  exact (Complex.continuous_ofReal.sub continuous_const).mul
    ((Complex.continuous_ofReal.add continuous_const).inv₀ real_add_I_ne_zero)

/-- The real Cayley transform is injective. -/
theorem injective_realCayley : Function.Injective realCayley := by
  intro x y h
  unfold realCayley at h
  field_simp [real_add_I_ne_zero] at h
  have him := congrArg Complex.im h
  norm_num at him
  linarith

theorem continuous_circleCayley : Continuous circleCayley :=
  continuous_realCayley.subtype_mk _

theorem injective_circleCayley : Function.Injective circleCayley := by
  intro x y h
  apply injective_realCayley
  exact congrArg ((↑) : Circle → Complex) h

/-- Real Cayley transform in the unit additive-circle coordinate used by Fourier analysis. -/
noncomputable def addCircleCayley (x : Real) : AddCircle (1 : Real) :=
  (AddCircle.homeomorphCircle one_ne_zero).symm (circleCayley x)

theorem continuous_addCircleCayley : Continuous addCircleCayley :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp continuous_circleCayley

theorem injective_addCircleCayley : Function.Injective addCircleCayley :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.injective.comp injective_circleCayley

theorem measurableEmbedding_addCircleCayley : MeasurableEmbedding addCircleCayley :=
  continuous_addCircleCayley.measurableEmbedding injective_addCircleCayley

@[simp]
theorem fourier_addCircleCayley_nat (n : Nat) (x : Real) :
    fourier (n : Int) (addCircleCayley x) = realCayley x ^ n := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  unfold addCircleCayley
  rw [Homeomorph.apply_symm_apply]
  simp

/-- The complete sequence of Cayley moments determines a probability measure on the real line. -/
theorem measure_eq_of_forall_cayleyMoment_eq
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : forall n : Nat, cayleyMoment mu n = cayleyMoment nu n) :
    mu = nu := by
  letI : IsProbabilityMeasure (Measure.map addCircleCayley mu) :=
    Measure.isProbabilityMeasure_map measurableEmbedding_addCircleCayley.measurable.aemeasurable
  letI : IsProbabilityMeasure (Measure.map addCircleCayley nu) :=
    Measure.isProbabilityMeasure_map measurableEmbedding_addCircleCayley.measurable.aemeasurable
  have hmap : Measure.map addCircleCayley mu = Measure.map addCircleCayley nu := by
    apply addCircle_measure_eq_of_nat_fourier_integral_eq
    intro n
    rw [integral_map measurableEmbedding_addCircleCayley.measurable.aemeasurable
      ((fourier (n : Int)).continuous.aestronglyMeasurable),
      integral_map measurableEmbedding_addCircleCayley.measurable.aemeasurable
        ((fourier (n : Int)).continuous.aestronglyMeasurable)]
    simp only [fourier_addCircleCayley_nat]
    simpa only [cayleyMoment] using h n
  exact measurableEmbedding_addCircleCayley.map_injective hmap

/-- Equality at every finite canonical inverse-Cholesky level selects exactly one real probability
measure. This is the set-theoretic complete-tower selector from the manuscript. -/
theorem measure_eq_of_completeCanonicalFrame_eq
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : forall N, (circleToeplitzGram N (cayleyMomentZ mu)).PosDef)
    (hnu : forall N, (circleToeplitzGram N (cayleyMomentZ nu)).PosDef)
    (hframe : forall N,
      gramSchmidtInverseFrame (circleToeplitzGram N (cayleyMomentZ mu)) (hmu N) =
        gramSchmidtInverseFrame (circleToeplitzGram N (cayleyMomentZ nu)) (hnu N)) :
    mu = nu := by
  apply measure_eq_of_forall_cayleyMoment_eq
  intro n
  have hgram := (gramSchmidtInverseFrame_eq_iff_gram_eq
    (circleToeplitzGram n (cayleyMomentZ mu))
    (circleToeplitzGram n (cayleyMomentZ nu)) (hmu n) (hnu n)).mp (hframe n)
  exact (circleToeplitzGram_cayleyMomentZ_eq_iff mu nu n).mp hgram n le_rfl

/-- Any coherent equality of inverse-Cholesky frames at every finite level selects the underlying
probability measure. Canonicality is needed to define the tower intrinsically, but determinacy
itself only uses the inverse-frame identities. -/
theorem measure_eq_of_completeInverseCholeskyFrame_eq
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (Cmu Cnu : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hmu : ∀ N, IsInverseCholeskyFrame (Cmu N)
      (circleToeplitzGram N (cayleyMomentZ mu)))
    (hnu : ∀ N, IsInverseCholeskyFrame (Cnu N)
      (circleToeplitzGram N (cayleyMomentZ nu)))
    (hframe : ∀ N, Cmu N = Cnu N) :
    mu = nu := by
  apply measure_eq_of_forall_cayleyMoment_eq
  intro n
  have hnu' := hnu n
  rw [← hframe n] at hnu'
  have hgram := gram_eq_of_same_inverseCholesky (Cmu n)
    (circleToeplitzGram n (cayleyMomentZ mu))
    (circleToeplitzGram n (cayleyMomentZ nu)) (hmu n) hnu'
  exact (circleToeplitzGram_cayleyMomentZ_eq_iff mu nu n).mp hgram n le_rfl

/-- The bounded continuous `n`-th Cayley character on the real line. -/
noncomputable def cayleyPowerBCF (n : ℕ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => realCayley x ^ n) (continuous_realCayley.pow n) 1 (fun x => by
      rw [norm_pow, norm_realCayley, one_pow])

/-- Real part of the bounded continuous `n`-th Cayley character. -/
noncomputable def cayleyPowerReBCF (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (realCayley x ^ n).re)
    (Complex.continuous_re.comp (continuous_realCayley.pow n)) 1 (fun x => by
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans_eq
        (by rw [norm_pow, norm_realCayley, one_pow]))

/-- Imaginary part of the bounded continuous `n`-th Cayley character. -/
noncomputable def cayleyPowerImBCF (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (realCayley x ^ n).im)
    (Complex.continuous_im.comp (continuous_realCayley.pow n)) 1 (fun x => by
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans_eq
        (by rw [norm_pow, norm_realCayley, one_pow]))

@[simp]
theorem cayleyPowerBCF_apply (n : ℕ) (x : ℝ) :
    cayleyPowerBCF n x = realCayley x ^ n := rfl

@[simp]
theorem cayleyPowerReBCF_apply (n : ℕ) (x : ℝ) :
    cayleyPowerReBCF n x = (realCayley x ^ n).re := rfl

@[simp]
theorem cayleyPowerImBCF_apply (n : ℕ) (x : ℝ) :
    cayleyPowerImBCF n x = (realCayley x ^ n).im := rfl

/-- Every fixed Cayley moment is weakly continuous on real probability measures. -/
theorem continuous_cayleyMoment (n : ℕ) :
    Continuous (fun mu : ProbabilityMeasure ℝ => cayleyMoment (mu : Measure ℝ) n) := by
  have hre := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cayleyPowerReBCF n)
  have him := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (cayleyPowerImBCF n)
  have hcomplex : Continuous (fun mu : ProbabilityMeasure ℝ =>
      (((∫ x, cayleyPowerReBCF n x ∂(mu : Measure ℝ)) : ℝ) : ℂ) +
        ((∫ x, cayleyPowerImBCF n x ∂(mu : Measure ℝ)) : ℝ) * I) :=
    (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  convert hcomplex using 1
  funext mu
  rw [cayleyMoment]
  have hint : Integrable (fun x : ℝ => realCayley x ^ n) (mu : Measure ℝ) :=
    (cayleyPowerBCF n).integrable (mu : Measure ℝ)
  apply Complex.ext
  · simpa using (integral_re hint).symm
  · simpa using (integral_im hint).symm

/-- Every fixed two-sided Hermitian Cayley moment is weakly continuous. -/
theorem continuous_cayleyMomentZ (q : ℤ) :
    Continuous (fun mu : ProbabilityMeasure ℝ => cayleyMomentZ (mu : Measure ℝ) q) := by
  cases q with
  | ofNat n => exact continuous_cayleyMoment n
  | negSucc n => exact continuous_star.comp (continuous_cayleyMoment (n + 1))

/-- Every finite Toeplitz Gram section varies continuously in the weak topology of probability
measures. -/
theorem continuous_circleToeplitzGram_cayleyMomentZ (N : ℕ) :
    Continuous (fun mu : ProbabilityMeasure ℝ =>
      circleToeplitzGram N (cayleyMomentZ (mu : Measure ℝ))) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  exact continuous_cayleyMomentZ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))

end

end GaloisForLFunctions.HTGeometry
