import GaloisForLFunctions.Bottcher.PoissonBoundary
import GaloisForLFunctions.HTGeometry.BernsteinSzegoProbabilityApproximation
import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw
import Mathlib.Probability.ProductMeasure

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

/-- Open unit disk, as parameter space for circle Poisson laws. -/
abbrev CirclePoissonParameter := Metric.ball (0 : ℂ) 1

/-- Poisson density on normalized circle Haar measure. -/
def circlePoissonDensity (a : CirclePoissonParameter) (z : Circle) : ℝ≥0∞ :=
  ENNReal.ofReal (poissonKernel 0 (a : ℂ) (z : ℂ))

/-- Harmonic measure on the unit circle viewed from `a`. -/
def circlePoissonMeasure (a : CirclePoissonParameter) : Measure Circle :=
  circleLebesgue.withDensity (circlePoissonDensity a)

theorem continuous_circlePoissonDensity_real (a : CirclePoissonParameter) :
    Continuous (fun z : Circle => poissonKernel 0 (a : ℂ) (z : ℂ)) := by
  exact (Bottcher.poissonKernel_continuousOn_sphere
    (c := (0 : ℂ)) (R := 1) a.2).restrict

theorem circlePoissonDensity_nonneg (a : CirclePoissonParameter) (z : Circle) :
    0 ≤ poissonKernel 0 (a : ℂ) (z : ℂ) := by
  exact Bottcher.poissonKernel_nonneg z.2 a.2

instance (a : CirclePoissonParameter) : IsProbabilityMeasure (circlePoissonMeasure a) := by
  rw [isProbabilityMeasure_iff, circlePoissonMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hint : Integrable (fun z : Circle => poissonKernel 0 (a : ℂ) (z : ℂ))
      circleLebesgue :=
    (continuous_circlePoissonDensity_real a).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmass := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall (circlePoissonDensity_nonneg a))
  rw [integral_circleLebesgue_eq_circleAverage
    (fun z : ℂ => poissonKernel 0 (a : ℂ) z)
    (continuous_circlePoissonDensity_real a).aestronglyMeasurable,
    Bottcher.poissonKernel_circleAverage_eq_one a.2] at hmass
  simpa [circlePoissonDensity] using hmass.symm

/-- Circle Poisson law as a bundled probability measure. -/
def circlePoissonProbabilityMeasure (a : CirclePoissonParameter) : ProbabilityMeasure Circle :=
  ⟨circlePoissonMeasure a, inferInstance⟩

theorem integral_circlePoissonMeasure_eq_circleAverage (a : CirclePoissonParameter)
    (F : ℂ → ℂ) (hF : Continuous fun z : Circle => F (z : ℂ)) :
    ∫ z : Circle, F (z : ℂ) ∂(circlePoissonMeasure a) =
      Real.circleAverage (fun z => (poissonKernel 0 (a : ℂ) z : ℂ) * F z) 0 1 := by
  have hdens : AEMeasurable (circlePoissonDensity a) circleLebesgue :=
    (ENNReal.continuous_ofReal.comp (continuous_circlePoissonDensity_real a)).measurable.aemeasurable
  have hdensTop : ∀ᵐ z ∂circleLebesgue, circlePoissonDensity a z < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [circlePoissonMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdens hdensTop]
  have hpoint : (λ z : Circle => (circlePoissonDensity a z).toReal • F (z : ℂ)) =
      fun z : Circle => (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) * F (z : ℂ) := by
    funext z
    rw [circlePoissonDensity, ENNReal.toReal_ofReal (circlePoissonDensity_nonneg a z)]
    simp [Complex.real_smul]
  rw [hpoint]
  simpa using integral_circleLebesgue_eq_circleAverage_complex
    (fun z : ℂ => (poissonKernel 0 (a : ℂ) z : ℂ) * F z)
    (((Complex.continuous_ofReal.comp (continuous_circlePoissonDensity_real a)).mul hF).aestronglyMeasurable)

theorem integral_circlePoissonMeasure_coe_pow (a : CirclePoissonParameter) (n : ℕ) :
    ∫ z : Circle, (z : ℂ) ^ n ∂(circlePoissonMeasure a) = (a : ℂ) ^ n := by
  rw [integral_circlePoissonMeasure_eq_circleAverage a (fun z => z ^ n) (by fun_prop)]
  have hd : DiffContOnCl ℂ (fun z : ℂ => z ^ n) (Metric.ball 0 1) := by
    exact ⟨differentiableOn_pow n, continuousOn_pow n⟩
  have h := DiffContOnCl.circleAverage_poissonKernel_smul hd a.2
  have heq : (poissonKernel 0 (a : ℂ) • fun z : ℂ => z ^ n) =
      fun z : ℂ => (poissonKernel 0 (a : ℂ) z : ℂ) * z ^ n := by
    funext z
    simp [Complex.real_smul]
  rw [← heq]
  exact h

private theorem circle_coe_zpow_negSucc_eq_conj_pow (z : Circle) (n : ℕ) :
    (z : ℂ) ^ (Int.negSucc n) = conj (z : ℂ) ^ (n + 1) := by
  rw [zpow_negSucc, ← inv_pow, ← Complex.inv_eq_conj (Circle.norm_coe z)]

/-- Exact two-sided Fourier moments of circle harmonic measure. -/
theorem integral_circlePoissonMeasure_coe_zpow (a : CirclePoissonParameter) (q : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ q ∂(circlePoissonMeasure a) =
      match q with
      | Int.ofNat n => (a : ℂ) ^ n
      | Int.negSucc n => conj (a : ℂ) ^ (n + 1) := by
  cases q with
  | ofNat n =>
      simpa using integral_circlePoissonMeasure_coe_pow a n
  | negSucc n =>
      simp_rw [circle_coe_zpow_negSucc_eq_conj_pow, ← map_pow]
      rw [integral_conj, integral_circlePoissonMeasure_coe_pow]

/-- Circle Poisson law transported to the unit additive circle used by the infinite-torus Fourier
API. -/
def addCirclePoissonProbabilityMeasure (a : CirclePoissonParameter) :
    ProbabilityMeasure UnitAddCircle :=
  ProbabilityMeasure.map (circlePoissonProbabilityMeasure a)
    (f := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm)
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous.aemeasurable

/-- Exact local Fourier coefficient of the transported Poisson law. -/
theorem integral_fourier_addCirclePoissonProbabilityMeasure
    (a : CirclePoissonParameter) (q : ℤ) :
    ∫ z : UnitAddCircle, fourier q z
        ∂(addCirclePoissonProbabilityMeasure a : Measure UnitAddCircle) =
      match q with
      | Int.ofNat n => (a : ℂ) ^ n
      | Int.negSucc n => conj (a : ℂ) ^ (n + 1) := by
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  rw [addCirclePoissonProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
  rw [integral_map e.symm.continuous.aemeasurable (fourier q).continuous.aestronglyMeasurable]
  change (∫ z : Circle, fourier q (e.symm z) ∂(circlePoissonMeasure a)) = _
  have hfourier (z : Circle) : fourier q (e.symm z) = (z : ℂ) ^ q := by
    rw [fourier_apply, AddCircle.toCircle_zsmul]
    have he : AddCircle.toCircle (e.symm z) = z := by
      rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
      exact e.apply_symm_apply z
    rw [he]
    exact Circle.coe_zpow z q
  simpa only [hfourier] using integral_circlePoissonMeasure_coe_zpow a q

/-- Two-sided local Poisson Fourier moment. -/
def circlePoissonFourierMoment (a : CirclePoissonParameter) : ℤ → ℂ
  | Int.ofNat n => (a : ℂ) ^ n
  | Int.negSucc n => conj (a : ℂ) ^ (n + 1)

/-- Product Poisson probability law on an arbitrary countable product torus. -/
def torusPoissonMeasure {I : Type*} (a : I → CirclePoissonParameter) :
    Measure (I → UnitAddCircle) :=
  Measure.infinitePi fun i => (addCirclePoissonProbabilityMeasure (a i) : Measure UnitAddCircle)

instance {I : Type*} (a : I → CirclePoissonParameter) :
    IsProbabilityMeasure (torusPoissonMeasure a) := by
  unfold torusPoissonMeasure
  infer_instance

/-- Product Poisson law as a bundled probability measure. -/
def torusPoissonProbabilityMeasure {I : Type*} (a : I → CirclePoissonParameter) :
    ProbabilityMeasure (I → UnitAddCircle) :=
  ⟨torusPoissonMeasure a, inferInstance⟩

/-- Exact finite-support Fourier character law of a product Poisson state. -/
theorem integral_infiniteTorusFourier_torusPoissonMeasure
    {I : Type*} (a : I → CirclePoissonParameter) (n : I →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(torusPoissonMeasure a) =
      n.prod fun i q => circlePoissonFourierMoment (a i) q := by
  classical
  let μ : I → Measure UnitAddCircle :=
    fun i => (addCirclePoissonProbabilityMeasure (a i) : Measure UnitAddCircle)
  let S : Finset I := n.support
  have hmap : Measure.map S.restrict (Measure.infinitePi μ) =
      Measure.pi fun i : ↑S => μ i := by
    exact Measure.infinitePi_map_restrict μ (I := S)
  have hfun : (fun x : I → UnitAddCircle => infiniteTorusFourier n x) =
      fun x => ∏ i : ↑S, fourier (n i) (x i) := by
    funext x
    simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Finsupp.prod]
    dsimp only [S]
    exact (Finset.prod_attach n.support fun i => fourier (n i) (x i)).symm
  rw [torusPoissonMeasure, hfun]
  change (∫ x, ∏ i : ↑S, fourier (n i) (x i) ∂(Measure.infinitePi μ)) = _
  calc
    (∫ x, ∏ i : ↑S, fourier (n i) (x i) ∂(Measure.infinitePi μ)) =
        ∫ y : (↑S → UnitAddCircle), ∏ i : ↑S, fourier (n i) (y i)
          ∂(Measure.pi fun i : ↑S => μ i) := by
      rw [← hmap, integral_map S.measurable_restrict.aemeasurable]
      · rfl
      · have hc : Continuous (fun y : (↑S → UnitAddCircle) =>
            ∏ i : ↑S, fourier (n i) (y i)) := by
          apply continuous_finsetProd (Finset.univ : Finset ↑S)
          intro i _
          exact (fourier (n i)).continuous.comp (continuous_apply i)
        exact hc.aestronglyMeasurable
    _ = ∏ i : ↑S, ∫ z : UnitAddCircle, fourier (n i) z ∂(μ i) := by
      exact integral_fintype_prod_eq_prod (fun i : ↑S => fourier (n i))
    _ = ∏ i : ↑S, circlePoissonFourierMoment (a i) (n i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa [μ, circlePoissonFourierMoment] using
        integral_fourier_addCirclePoissonProbabilityMeasure (a i) (n i)
    _ = n.prod fun i q => circlePoissonFourierMoment (a i) q := by
      simp only [Finsupp.prod]
      dsimp only [S]
      exact Finset.prod_attach n.support fun i =>
        circlePoissonFourierMoment (a i) (n i)

/-- Unbundled prime Poisson disk parameter `p^(-σ+it)`. -/
def primePoissonParameterValue (σ t : ℝ) (p : Nat.Primes) : ℂ :=
  Complex.exp ((((-σ : ℝ) : ℂ) + (t : ℂ) * I) *
    (Real.log (p.1 : ℝ) : ℂ))

theorem norm_primePoissonParameterValue (σ t : ℝ) (p : Nat.Primes) :
    ‖primePoissonParameterValue σ t p‖ = Real.exp (-σ * Real.log (p.1 : ℝ)) := by
  rw [primePoissonParameterValue, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Prime Poisson parameter bundled with its open-disk proof. -/
def primePoissonParameter (σ t : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    CirclePoissonParameter := by
  refine ⟨primePoissonParameterValue σ t p, ?_⟩
  rw [mem_ball_zero_iff, norm_primePoissonParameterValue]
  have hp1 : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hp : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hσ) hp

@[simp]
theorem coe_primePoissonParameter (σ t : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    ((primePoissonParameter σ t hσ p : CirclePoissonParameter) : ℂ) =
      primePoissonParameterValue σ t p := rfl

/-- Ordinary-prime product Poisson spectral measure. -/
def primePoissonMeasure (σ t : ℝ) (hσ : 0 < σ) :
    Measure (Nat.Primes → UnitAddCircle) :=
  torusPoissonMeasure (primePoissonParameter σ t hσ)

instance (σ t : ℝ) (hσ : 0 < σ) :
    IsProbabilityMeasure (primePoissonMeasure σ t hσ) := by
  unfold primePoissonMeasure
  infer_instance

/-- Bundled ordinary-prime product Poisson spectral law. -/
def primePoissonProbabilityMeasure (σ t : ℝ) (hσ : 0 < σ) :
    ProbabilityMeasure (Nat.Primes → UnitAddCircle) :=
  ⟨primePoissonMeasure σ t hσ, inferInstance⟩

/-- Every finite prime character has the exact product-Poisson moment. -/
theorem integral_infiniteTorusFourier_primePoissonMeasure
    (σ t : ℝ) (hσ : 0 < σ) (n : Nat.Primes →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure σ t hσ) =
      n.prod fun p q => circlePoissonFourierMoment (primePoissonParameter σ t hσ p) q := by
  exact integral_infiniteTorusFourier_torusPoissonMeasure
    (primePoissonParameter σ t hσ) n

/-- Each fixed local prime moment depends continuously on the positive real aperture. -/
theorem continuous_primePoissonLocalMoment (t : ℝ) (p : Nat.Primes) (q : ℤ) :
    Continuous (fun σ : Set.Ioi (0 : ℝ) =>
      circlePoissonFourierMoment (primePoissonParameter σ t σ.2 p) q) := by
  cases q with
  | ofNat n =>
      simp only [circlePoissonFourierMoment, coe_primePoissonParameter,
        primePoissonParameterValue]
      fun_prop
  | negSucc n =>
      simp only [circlePoissonFourierMoment, coe_primePoissonParameter,
        primePoissonParameterValue]
      fun_prop

/-- Every finite-support prime Poisson character moment is continuous in the positive real
aperture. -/
theorem continuous_primePoissonCharacterMoment (t : ℝ) (n : Nat.Primes →₀ ℤ) :
    Continuous (fun σ : Set.Ioi (0 : ℝ) =>
      n.prod fun p q => circlePoissonFourierMoment (primePoissonParameter σ t σ.2 p) q) := by
  classical
  unfold Finsupp.prod
  apply continuous_finsetProd n.support
  intro p hp
  exact continuous_primePoissonLocalMoment t p (n p)

/-- Fixed-height product Poisson states vary weakly continuously throughout the positive
half-plane, including convergence from the normal bulk to the critical aperture. -/
theorem continuous_primePoissonProbabilityMeasure_fixedHeight (t : ℝ) :
    Continuous (fun σ : Set.Ioi (0 : ℝ) =>
      primePoissonProbabilityMeasure σ t σ.2) := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  apply probabilityMeasure_tendsto_of_infiniteTorusFourier_integral_tendsto
  intro n
  change Tendsto
    (fun σ : Set.Ioi (0 : ℝ) =>
      ∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure σ t σ.2))
    (nhds σ₀)
    (nhds (∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure σ₀ t σ₀.2)))
  let moment : Set.Ioi (0 : ℝ) → ℂ := fun σ =>
    n.prod fun p q => circlePoissonFourierMoment (primePoissonParameter σ t σ.2 p) q
  have heq : (fun σ : Set.Ioi (0 : ℝ) =>
      ∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure σ t σ.2)) = moment := by
    funext σ
    exact integral_infiniteTorusFourier_primePoissonMeasure σ t σ.2 n
  rw [integral_infiniteTorusFourier_primePoissonMeasure σ₀ t σ₀.2 n]
  rw [heq]
  change Tendsto moment (nhds σ₀) (nhds (moment σ₀))
  exact (continuous_primePoissonCharacterMoment t n).continuousAt

/-- Literal weak-* normal-to-critical boundary convergence at fixed height. -/
theorem tendsto_primePoissonProbabilityMeasure_to_critical (t : ℝ) :
    Tendsto (fun σ : Set.Ioi (0 : ℝ) => primePoissonProbabilityMeasure σ t σ.2)
      (nhds ⟨1 / 2, by norm_num⟩)
      (nhds (primePoissonProbabilityMeasure (1 / 2) t (by norm_num))) := by
  exact (continuous_primePoissonProbabilityMeasure_fixedHeight t).continuousAt


end

end GaloisForLFunctions.HTGeometry
