import GaloisForLFunctions.HTGeometry.BernsteinSzegoReconstruction
import GaloisForLFunctions.HTGeometry.BernsteinSzegoWeldBounds
import GaloisForLFunctions.HTGeometry.RieszSingularSzegoCollapse
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Bernstein--Szegő probability approximations

The reciprocal-square finite OPUC density is promoted here from its angular moment formula to an
actual probability measure on the circle.  Its Fourier moments agree with the formal
Bernstein--Szegő moments, so the exact prefix-reconstruction theorem becomes a literal equality of
finite measure Gram sections.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal Topology ComplexOrder

noncomputable section

/-- Complex-valued version of the normalized-Haar/circle-average bridge. -/
theorem integral_circleLebesgue_eq_circleAverage_complex (F : ℂ → ℂ)
    (hF : AEStronglyMeasurable (fun z : Circle => F (z : ℂ)) circleLebesgue) :
    ∫ z : Circle, F (z : ℂ) ∂circleLebesgue = Real.circleAverage F 0 1 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  rw [circleLebesgue] at hF ⊢
  rw [integral_map
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable hF]
  simp only [AddCircle.homeomorphCircle_apply]
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  have hcv : (fun a : ℝ => F ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle) : ℂ)) =
      fun a : ℝ => F (circleMap 0 1 (2 * Real.pi * a)) := by
    funext a
    congr 1
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp
  rw [hcv]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun θ => F (circleMap 0 1 θ)) (show (2 * Real.pi) ≠ 0 by positivity)
  simp only [mul_zero, mul_one] at hcomp
  rw [hcomp, Real.circleAverage]

/-- The reciprocal-square Bernstein--Szegő density as a genuine finite circle measure. -/
noncomputable def bernsteinSzegoMeasure {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) : Measure Circle :=
  circleLebesgue.withDensity fun z => ENNReal.ofReal (bernsteinSzegoDensity c hG z)

noncomputable instance bernsteinSzegoMeasure_isFinite {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    IsFiniteMeasure (bernsteinSzegoMeasure c hG) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    exists_bernsteinSzegoDensity_uniform_bounds c hG
  have hle : ∫⁻ z, ENNReal.ofReal (bernsteinSzegoDensity c hG z) ∂circleLebesgue ≤
      ENNReal.ofReal upper := by
    calc
      ∫⁻ z, ENNReal.ofReal (bernsteinSzegoDensity c hG z) ∂circleLebesgue ≤
          ∫⁻ _, ENNReal.ofReal upper ∂circleLebesgue :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hbounds z).2
      _ = ENNReal.ofReal upper * circleLebesgue Set.univ := lintegral_const _
      _ = ENNReal.ofReal upper := by rw [measure_univ, mul_one]
  exact isFiniteMeasure_withDensity
    (ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top))

/-- Fourier integration against the actual Bernstein--Szegő measure is exactly the formal moment
sequence constructed by the finite OPUC theory. -/
theorem circleMeasureMomentZ_bernsteinSzegoMeasure {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (q : ℤ) :
    circleMeasureMomentZ (bernsteinSzegoMeasure c hG) q = bernsteinSzegoMoment c hG q := by
  let dens : Circle → ℝ≥0∞ := fun z => ENNReal.ofReal (bernsteinSzegoDensity c hG z)
  have hdensMeas : AEMeasurable dens circleLebesgue :=
    (ENNReal.continuous_ofReal.comp (bernsteinSzegoDensity_continuous c hG)).measurable.aemeasurable
  have hdensTop : ∀ᵐ z ∂circleLebesgue, dens z < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [circleMeasureMomentZ, bernsteinSzegoMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdensMeas hdensTop]
  change (∫ z : Circle, (dens z).toReal • (z : ℂ) ^ (-q) ∂circleLebesgue) = _
  calc
    (∫ z : Circle, (dens z).toReal • (z : ℂ) ^ (-q) ∂circleLebesgue) =
        ∫ z : Circle, (z : ℂ) ^ (-q) *
          bernsteinSzegoComplexWeight c hG (z : ℂ) ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [show (dens z).toReal = bernsteinSzegoDensity c hG z by
        exact ENNReal.toReal_ofReal (bernsteinSzegoDensity_pos c hG z).le]
      simp only [bernsteinSzegoDensity, bernsteinSzegoComplexWeight, Complex.real_smul,
        Complex.ofReal_inv]
      ring
    _ = Real.circleAverage
        (fun z : ℂ => z ^ (-q) * bernsteinSzegoComplexWeight c hG z) 0 1 := by
      have hzpow : Continuous (fun z : Circle => (z : ℂ) ^ (-q)) :=
        (continuousOn_zpow₀ (-q)).comp_continuous continuous_subtype_val fun z => by simp
      have hweight : Continuous
          (fun z : Circle => bernsteinSzegoComplexWeight c hG (z : ℂ)) :=
        (bernsteinSzegoComplexWeight_continuousOn_sphere c hG).comp_continuous
          continuous_subtype_val fun z => z.2
      have hmeas : AEStronglyMeasurable
          (fun z : Circle => (z : ℂ) ^ (-q) * bernsteinSzegoComplexWeight c hG (z : ℂ))
          circleLebesgue := (hzpow.mul hweight).aestronglyMeasurable
      exact integral_circleLebesgue_eq_circleAverage_complex
        (fun z : ℂ => z ^ (-q) * bernsteinSzegoComplexWeight c hG z) hmeas
    _ = bernsteinSzegoMoment c hG q := rfl

/-- The zero Fourier moment of a probability measure is one. -/
theorem circleMeasureMomentZ_zero (mu : Measure Circle) [IsProbabilityMeasure mu] :
    circleMeasureMomentZ mu 0 = 1 := by
  simp [circleMeasureMomentZ]

/-- When the input moment sequence is normalized, the Bernstein--Szegő measure has total mass
one. -/
theorem bernsteinSzegoMeasure_univ {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram (N + 1) c).PosDef) (hc0 : c 0 = 1) :
    bernsteinSzegoMeasure c hG Set.univ = 1 := by
  have hmoment : circleMeasureMomentZ (bernsteinSzegoMeasure c hG) 0 = 1 := by
    rw [circleMeasureMomentZ_bernsteinSzegoMeasure]
    exact ((bernsteinSzegoMoment_prefix c hG (0 : Fin (N + 2))).1).trans hc0
  rw [circleMeasureMomentZ] at hmoment
  simp only [neg_zero, zpow_zero, integral_const, smul_eq_mul, mul_one] at hmoment
  apply (ENNReal.toReal_eq_one_iff _).mp
  simpa [measureReal_def, Complex.real_smul] using congrArg Complex.re hmoment

/-- The canonical probability measure at truncation depth `N`. -/
noncomputable def bernsteinSzegoProbabilityApproximation
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite) (N : ℕ) :
    ProbabilityMeasure Circle :=
  let hG := circleMeasureGramTower_posDef_of_infiniteSupport
    (mu : Measure Circle) hmu (N + 1)
  ⟨bernsteinSzegoMeasure (circleMeasureMomentZ (mu : Measure Circle)) hG,
    IsProbabilityMeasure.mk (bernsteinSzegoMeasure_univ
      (circleMeasureMomentZ (mu : Measure Circle)) hG
      (circleMeasureMomentZ_zero (mu : Measure Circle)))⟩

/-- The actual truncation measure has exactly the formal Bernstein--Szegő moment sequence. -/
theorem bernsteinSzegoProbabilityApproximation_moment
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) (q : ℤ) :
    circleMeasureMomentZ (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) q =
      bernsteinSzegoMoment (circleMeasureMomentZ (mu : Measure Circle))
        (circleMeasureGramTower_posDef_of_infiniteSupport
          (mu : Measure Circle) hmu (N + 1)) q := by
  exact circleMeasureMomentZ_bernsteinSzegoMeasure _ _ q

/-- Every positive and negative Fourier coordinate through the truncation depth is reproduced
exactly by the probability approximation. -/
theorem bernsteinSzegoProbabilityApproximation_moment_prefix
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (N : ℕ) (k : Fin (N + 2)) :
    circleMeasureMomentZ (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle)
        (k : ℤ) = circleMeasureMomentZ (mu : Measure Circle) (k : ℤ) ∧
      circleMeasureMomentZ (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle)
        (-(k : ℤ)) = circleMeasureMomentZ (mu : Measure Circle) (-(k : ℤ)) := by
  simpa only [bernsteinSzegoProbabilityApproximation_moment] using
    bernsteinSzegoMoment_prefix (circleMeasureMomentZ (mu : Measure Circle))
      (circleMeasureGramTower_posDef_of_infiniteSupport
        (mu : Measure Circle) hmu (N + 1)) k

/-- A fixed Fourier coordinate is eventually reproduced exactly. -/
theorem bernsteinSzegoProbabilityApproximation_moment_eventuallyEq
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite)
    (q : ℤ) :
    (fun N => circleMeasureMomentZ
      (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) q) =ᶠ[atTop]
        fun _ => circleMeasureMomentZ (mu : Measure Circle) q := by
  cases q with
  | ofNat n =>
      filter_upwards [eventually_ge_atTop n] with N hN
      let k : Fin (N + 2) := ⟨n, by omega⟩
      exact (bernsteinSzegoProbabilityApproximation_moment_prefix mu hmu N k).1
  | negSucc n =>
      filter_upwards [eventually_ge_atTop (n + 1)] with N hN
      let k : Fin (N + 2) := ⟨n + 1, by omega⟩
      simpa only [Int.ofNat_eq_coe, Int.reduceNegSucc] using
        (bernsteinSzegoProbabilityApproximation_moment_prefix mu hmu N k).2

/-- The actual Bernstein--Szegő probability measure reproduces the full finite Toeplitz section
at its truncation depth. -/
theorem bernsteinSzegoProbabilityApproximation_gram_eq
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite) (N : ℕ) :
    circleMeasureGramTower
        (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) (N + 1) =
      circleMeasureGramTower (mu : Measure Circle) (N + 1) := by
  unfold circleMeasureGramTower
  have hmom : circleMeasureMomentZ
      (bernsteinSzegoProbabilityApproximation mu hmu N : Measure Circle) =
        bernsteinSzegoMoment (circleMeasureMomentZ (mu : Measure Circle))
          (circleMeasureGramTower_posDef_of_infiniteSupport
            (mu : Measure Circle) hmu (N + 1)) := by
    funext q
    exact bernsteinSzegoProbabilityApproximation_moment mu hmu N q
  rw [hmom]
  exact circleToeplitzGram_bernsteinSzegoMoment_eq
    (circleMeasureMomentZ (mu : Measure Circle))
      (circleMeasureGramTower_posDef_of_infiniteSupport
        (mu : Measure Circle) hmu (N + 1))

/-- Fourier moments determine probability measures on the multiplicative circle. -/
theorem circle_measure_eq_of_forall_moment_eq
    (mu nu : Measure Circle) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : ∀ q : ℤ, circleMeasureMomentZ mu q = circleMeasureMomentZ nu q) :
    mu = nu := by
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let mu' : Measure (AddCircle (1 : ℝ)) := Measure.map e.symm mu
  let nu' : Measure (AddCircle (1 : ℝ)) := Measure.map e.symm nu
  letI : IsProbabilityMeasure mu' :=
    Measure.isProbabilityMeasure_map e.symm.continuous.aemeasurable
  letI : IsProbabilityMeasure nu' :=
    Measure.isProbabilityMeasure_map e.symm.continuous.aemeasurable
  have hmap : mu' = nu' := by
    apply addCircle_measure_eq_of_fourier_integral_eq
    intro n
    rw [mu', nu', integral_map e.symm.continuous.aemeasurable
      (fourier n).continuous.aestronglyMeasurable,
      integral_map e.symm.continuous.aemeasurable
        (fourier n).continuous.aestronglyMeasurable]
    have hfourier (z : Circle) : fourier n (e.symm z) = (z : ℂ) ^ n := by
      rw [fourier_apply, AddCircle.toCircle_zsmul]
      have he : AddCircle.toCircle (e.symm z) = z := by
        rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
        exact e.apply_symm_apply z
      rw [he]
    simpa only [circleMeasureMomentZ, neg_neg, hfourier] using h (-n)
  exact e.symm.measurableEmbedding.map_injective hmap

/-- The complete two-sided Fourier-moment coordinate on circle probability laws. -/
noncomputable def completeCircleMomentSequence (mu : ProbabilityMeasure Circle) : ℤ → ℂ :=
  fun q => circleMeasureMomentZ (mu : Measure Circle) q

/-- Every fixed circle Fourier moment varies continuously in the weak topology. -/
theorem continuous_circleMeasureMomentZ (q : ℤ) :
    Continuous (fun mu : ProbabilityMeasure Circle =>
      circleMeasureMomentZ (mu : Measure Circle) q) := by
  have hpow : Continuous (fun z : Circle => (z : ℂ) ^ (-q)) :=
    (continuousOn_zpow₀ (-q)).comp_continuous continuous_subtype_val fun z => by simp
  let fre : C(Circle, ℝ) := ⟨fun z => ((z : ℂ) ^ (-q)).re, hpow.re⟩
  let fim : C(Circle, ℝ) := ⟨fun z => ((z : ℂ) ^ (-q)).im, hpow.im⟩
  have hre := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact fre)
  have him := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact fim)
  have hcomplex : Continuous (fun mu : ProbabilityMeasure Circle =>
      (((∫ z, fre z ∂(mu : Measure Circle)) : ℝ) : ℂ) +
        ((∫ z, fim z ∂(mu : Measure Circle)) : ℝ) * I) :=
    (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)
  convert hcomplex using 1
  funext mu
  have hint : Integrable (fun z : Circle => (z : ℂ) ^ (-q)) (mu : Measure Circle) :=
    (BoundedContinuousFunction.mkOfCompact
      (⟨fun z => (z : ℂ) ^ (-q), hpow⟩ : C(Circle, ℂ))).integrable (mu : Measure Circle)
  apply Complex.ext
  · simpa [circleMeasureMomentZ, fre] using (integral_re hint).symm
  · simpa [circleMeasureMomentZ, fim] using (integral_im hint).symm

/-- The whole Fourier-moment sequence is weakly continuous. -/
theorem continuous_completeCircleMomentSequence :
    Continuous completeCircleMomentSequence := by
  apply continuous_pi
  exact continuous_circleMeasureMomentZ

/-- The complete Fourier-moment sequence is faithful. -/
theorem injective_completeCircleMomentSequence :
    Function.Injective completeCircleMomentSequence := by
  intro mu nu h
  apply ProbabilityMeasure.toMeasure_injective
  apply circle_measure_eq_of_forall_moment_eq
  intro q
  exact congrFun h q

/-- On the compact circle probability space, the complete moment sequence is a closed topological
embedding. -/
theorem isClosedEmbedding_completeCircleMomentSequence :
    Topology.IsClosedEmbedding completeCircleMomentSequence := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_completeCircleMomentSequence
  · exact injective_completeCircleMomentSequence
  · exact continuous_completeCircleMomentSequence.isClosedMap

/-- Canonical Bernstein--Szegő probability approximations converge weakly to their source circle
law because every Fourier coordinate is eventually exact. -/
theorem bernsteinSzegoProbabilityApproximation_tendsto
    (mu : ProbabilityMeasure Circle) (hmu : (mu : Measure Circle).support.Infinite) :
    Tendsto (bernsteinSzegoProbabilityApproximation mu hmu) atTop (𝓝 mu) := by
  rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff]
  rw [tendsto_pi_nhds]
  intro q
  exact tendsto_const_nhds.congr'
    (bernsteinSzegoProbabilityApproximation_moment_eventuallyEq mu hmu q).symm

end

end GaloisForLFunctions.HTGeometry
