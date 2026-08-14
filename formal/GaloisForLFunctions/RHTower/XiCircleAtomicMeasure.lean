import GaloisForLFunctions.RHTower.XiSchurDiscGerm
import GaloisForLFunctions.HTGeometry.CircleSingularWitness
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction
import GaloisForLFunctions.HTGeometry.FAndMRieszSchurConsequences

/-!
# The atomic Xi circle measure

Under the Riemann hypothesis the centered Xi spectrum is real, and its Cayley images
`(t - i)/(t + i)` lie on the unit circle.  Weighting each by the normalized Cauchy weight
`1/(b(t² + 1))` produces a probability measure on the circle carried by a countable set, hence
mutually singular with circle Lebesgue measure.
-/

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem xiCayleyValue_norm (t : ℝ) :
    ‖((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)‖ = 1 := by
  have hsq : ‖(t : ℂ) - Complex.I‖ ^ 2 = ‖(t : ℂ) + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  have hne : (t : ℂ) + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have heq : ‖(t : ℂ) - Complex.I‖ = ‖(t : ℂ) + Complex.I‖ := by
    nlinarith [norm_nonneg ((t : ℂ) - Complex.I), norm_nonneg ((t : ℂ) + Complex.I), hsq]
  rw [norm_div, heq, div_self (norm_ne_zero_iff.mpr hne)]

/-- The Cayley image on the unit circle of a real centered spectral point. -/
def xiCayleyPoint (q : XiZeroCopy) : Circle :=
  ⟨((xiRealSpectralPoint q : ℂ) - Complex.I) / ((xiRealSpectralPoint q : ℂ) + Complex.I), by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using
      xiCayleyValue_norm (xiRealSpectralPoint q)⟩

/-- The normalized Cauchy weight carried by one centered spectral point. -/
def xiAtomWeight (q : XiZeroCopy) : ENNReal :=
  ENNReal.ofReal (1 / (xiBasepointSlope.re * (xiRealSpectralPoint q ^ 2 + 1)))

/-- **The atomic Xi circle measure.** -/
def xiCircleAtomicMeasure : Measure Circle :=
  Measure.sum fun q => xiAtomWeight q • Measure.dirac (xiCayleyPoint q)

theorem xiCircleAtomicMeasure_compl_range :
    xiCircleAtomicMeasure (Set.range xiCayleyPoint)ᶜ = 0 := by
  have hcount : (Set.range xiCayleyPoint).Countable := Set.countable_range _
  have hmeas : MeasurableSet (Set.range xiCayleyPoint)ᶜ := hcount.measurableSet.compl
  have hterm : ∀ q : XiZeroCopy,
      (xiAtomWeight q • Measure.dirac (xiCayleyPoint q)) ((Set.range xiCayleyPoint)ᶜ) = 0 := by
    intro q
    rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas,
      Set.indicator_of_notMem (by simp) _]
    simp
  rw [xiCircleAtomicMeasure, Measure.sum_apply _ hmeas, tsum_congr hterm]
  exact tsum_zero

/-- **The atomic Xi circle measure is a probability measure under the Riemann hypothesis.** -/
theorem xiCircleAtomicMeasure_univ_of_rh (hRH : RiemannHypothesis) :
    xiCircleAtomicMeasure Set.univ = 1 := by
  have hbpos : 0 < xiBasepointSlope.re := xiBasepointSlope_re_pos_of_rh hRH
  have hsum : Summable fun q : XiZeroCopy => 1 / (xiRealSpectralPoint q ^ 2 + 1) :=
    summable_xiCauchyWeight_of_rh hRH
  have hscaled : Summable fun q : XiZeroCopy =>
      1 / (xiBasepointSlope.re * (xiRealSpectralPoint q ^ 2 + 1)) := by
    have := hsum.mul_left (1 / xiBasepointSlope.re)
    refine this.congr fun q => ?_
    field_simp
  have hnonneg : ∀ q : XiZeroCopy,
      0 ≤ 1 / (xiBasepointSlope.re * (xiRealSpectralPoint q ^ 2 + 1)) := by
    intro q
    have : 0 < xiRealSpectralPoint q ^ 2 + 1 := by positivity
    positivity
  have htsum : ∑' q : XiZeroCopy,
      1 / (xiBasepointSlope.re * (xiRealSpectralPoint q ^ 2 + 1)) = 1 := by
    have hcongr : ∀ q : XiZeroCopy,
        1 / (xiBasepointSlope.re * (xiRealSpectralPoint q ^ 2 + 1))
          = (1 / xiBasepointSlope.re) * (1 / (xiRealSpectralPoint q ^ 2 + 1)) := by
      intro q
      field_simp
    rw [tsum_congr hcongr, tsum_mul_left, ← xiBasepointSlope_re_eq_tsum_of_rh hRH]
    field_simp
  have hterm : ∀ q : XiZeroCopy,
      (xiAtomWeight q • Measure.dirac (xiCayleyPoint q)) Set.univ = xiAtomWeight q := by
    intro q
    rw [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ]
    simp
  rw [xiCircleAtomicMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_congr hterm]
  simp only [xiAtomWeight]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hscaled, htsum, ENNReal.ofReal_one]

/-- **The atomic Xi circle measure is singular with respect to circle Lebesgue measure.** -/
theorem mutuallySingular_xiCircleAtomicMeasure :
    xiCircleAtomicMeasure ⟂ₘ circleLebesgue :=
  mutuallySingular_circleLebesgue_of_countable (Set.countable_range xiCayleyPoint)
    xiCircleAtomicMeasure_compl_range

/-- A point of positive mass lies in the topological support. -/
theorem mem_support_of_measure_singleton_pos {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {mu : Measure X} {x : X} (h : 0 < mu {x}) : x ∈ mu.support := by
  rw [Measure.mem_support_iff, Filter.frequently_smallSets]
  exact fun t ht => ⟨{x}, Set.singleton_subset_iff.mpr (mem_of_mem_nhds ht), h⟩

theorem xiAtomWeight_pos_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    0 < xiAtomWeight q := by
  have hb : 0 < xiBasepointSlope.re := xiBasepointSlope_re_pos_of_rh hRH
  have ht : (0 : ℝ) < xiRealSpectralPoint q ^ 2 + 1 := by positivity
  rw [xiAtomWeight, ENNReal.ofReal_pos]
  positivity

theorem xiCircleAtomicMeasure_singleton_pos_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    0 < xiCircleAtomicMeasure {xiCayleyPoint q} := by
  have hmeas : MeasurableSet ({xiCayleyPoint q} : Set Circle) := measurableSet_singleton _
  have hterm : (xiAtomWeight q • Measure.dirac (xiCayleyPoint q)) {xiCayleyPoint q}
      = xiAtomWeight q := by
    rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas]
    simp
  have hle : xiAtomWeight q ≤ xiCircleAtomicMeasure {xiCayleyPoint q} := by
    rw [xiCircleAtomicMeasure, Measure.sum_apply _ hmeas]
    calc xiAtomWeight q
        = (xiAtomWeight q • Measure.dirac (xiCayleyPoint q)) {xiCayleyPoint q} := hterm.symm
      _ ≤ ∑' r : XiZeroCopy,
            (xiAtomWeight r • Measure.dirac (xiCayleyPoint r)) {xiCayleyPoint q} :=
          ENNReal.le_tsum q
  exact lt_of_lt_of_le (xiAtomWeight_pos_of_rh hRH q) hle

/-- The centered Xi spectrum is an infinite set of points. -/
theorem range_xiSpectralPoint_infinite : (Set.range xiSpectralPoint).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image norm).bddAbove
  have htend := tendsto_norm_xiSpectralPoint_cofinite
  have hev : ∀ᶠ q : XiZeroCopy in Filter.cofinite, B + 1 ≤ ‖xiSpectralPoint q‖ :=
    Filter.tendsto_atTop.mp htend (B + 1)
  obtain ⟨q, hq⟩ := hev.exists
  have hmem : ‖xiSpectralPoint q‖ ∈ norm '' Set.range xiSpectralPoint :=
    ⟨xiSpectralPoint q, Set.mem_range_self q, rfl⟩
  have := hB hmem
  linarith

theorem range_xiRealSpectralPoint_infinite_of_rh (hRH : RiemannHypothesis) :
    (Set.range xiRealSpectralPoint).Infinite := by
  have himg : Set.range xiSpectralPoint
      = Complex.ofReal '' Set.range xiRealSpectralPoint := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨xiRealSpectralPoint q, Set.mem_range_self q,
        (xiSpectralPoint_eq_ofReal_of_rh hRH q).symm⟩
    · rintro ⟨t, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, xiSpectralPoint_eq_ofReal_of_rh hRH q⟩
  intro hfin
  exact range_xiSpectralPoint_infinite (by rw [himg]; exact hfin.image _)

theorem xiCayleyPoint_injOn_ordinate {s t : ℝ}
    (h : ((s : ℂ) - Complex.I) / ((s : ℂ) + Complex.I)
      = ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)) : s = t := by
  have hs : (s : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
  have ht : (t : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
  rw [div_eq_div_iff hs ht] at h
  have hcast : ((s : ℂ)) = ((t : ℂ)) := by
    have h2 : (2 : ℂ) * Complex.I * ((s : ℂ) - (t : ℂ)) = 0 := by
      linear_combination h
    have hI : (2 : ℂ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero]
    have := mul_eq_zero.mp h2
    rcases this with h3 | h3
    · exact absurd h3 hI
    · exact sub_eq_zero.mp h3
  exact_mod_cast hcast

theorem inverseCayley_xiCayleyPoint (q : XiZeroCopy) :
    (Complex.I * (1 + ((xiCayleyPoint q : Circle) : ℂ))
      / (1 - ((xiCayleyPoint q : Circle) : ℂ))).re = xiRealSpectralPoint q := by
  have hs : ((xiRealSpectralPoint q : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have := congrArg Complex.im hz
    simp at this
  have hval : Complex.I * (1 + ((xiCayleyPoint q : Circle) : ℂ))
      / (1 - ((xiCayleyPoint q : Circle) : ℂ))
      = ((xiRealSpectralPoint q : ℝ) : ℂ) := by
    show Complex.I * (1 + (((xiRealSpectralPoint q : ℝ) : ℂ) - Complex.I)
        / (((xiRealSpectralPoint q : ℝ) : ℂ) + Complex.I))
      / (1 - (((xiRealSpectralPoint q : ℝ) : ℂ) - Complex.I)
        / (((xiRealSpectralPoint q : ℝ) : ℂ) + Complex.I)) = _
    field_simp
    ring
  rw [hval, Complex.ofReal_re]

theorem range_xiCayleyPoint_infinite_of_rh (hRH : RiemannHypothesis) :
    (Set.range xiCayleyPoint).Infinite := by
  have hmap : Set.range xiRealSpectralPoint
      ⊆ (fun c : Circle => (Complex.I * (1 + (c : ℂ)) / (1 - (c : ℂ))).re)
        '' Set.range xiCayleyPoint := by
    rintro t ⟨q, rfl⟩
    exact ⟨xiCayleyPoint q, Set.mem_range_self q, inverseCayley_xiCayleyPoint q⟩
  intro hfin
  exact range_xiRealSpectralPoint_infinite_of_rh hRH ((hfin.image _).subset hmap)

/-- **The atomic Xi circle measure has infinite support under the Riemann hypothesis.** -/
theorem xiCircleAtomicMeasure_support_infinite_of_rh (hRH : RiemannHypothesis) :
    xiCircleAtomicMeasure.support.Infinite := by
  refine (range_xiCayleyPoint_infinite_of_rh hRH).mono ?_
  rintro _ ⟨q, rfl⟩
  exact mem_support_of_measure_singleton_pos (xiCircleAtomicMeasure_singleton_pos_of_rh hRH q)

/-- The atomic Xi circle measure as a probability measure. -/
def xiCircleProbabilityMeasure (hRH : RiemannHypothesis) : ProbabilityMeasure Circle :=
  ⟨xiCircleAtomicMeasure, ⟨xiCircleAtomicMeasure_univ_of_rh hRH⟩⟩

@[simp]
theorem coe_xiCircleProbabilityMeasure (hRH : RiemannHypothesis) :
    ((xiCircleProbabilityMeasure hRH : ProbabilityMeasure Circle) : Measure Circle)
      = xiCircleAtomicMeasure := rfl

/-- **Atomic condensation of the Xi circle carrier.**  Under the Riemann hypothesis the atomic Xi
circle measure has infinite support and is singular to circle Lebesgue measure, so the singular
Schur-defect collapse and the Bernstein--Szegő cofinal approximation both hold for it. -/
theorem xiSchur_atomicCondensation_of_rh (hRH : RiemannHypothesis) :
    ∃ hmu : ((xiCircleProbabilityMeasure hRH : ProbabilityMeasure Circle) :
        Measure Circle).support.Infinite,
      GaloisForLFunctions.HTGeometry.HasSingularSchurDefectCollapse
          ((xiCircleProbabilityMeasure hRH : ProbabilityMeasure Circle) : Measure Circle) hmu ∧
        GaloisForLFunctions.HTGeometry.HasBernsteinSzegoCofinalApproximation
          (xiCircleProbabilityMeasure hRH) hmu :=
  ⟨xiCircleAtomicMeasure_support_infinite_of_rh hRH,
    GaloisForLFunctions.HTGeometry.singularSchurDefect_doubleBoundary
      (xiCircleProbabilityMeasure hRH) (xiCircleAtomicMeasure_support_infinite_of_rh hRH)
      mutuallySingular_xiCircleAtomicMeasure⟩

/-- The Cayley value of a real ordinate, as a complex number. -/
def xiCayleyValue (t : ℝ) : ℂ := ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)

theorem coe_xiCayleyPoint (q : XiZeroCopy) :
    ((xiCayleyPoint q : Circle) : ℂ) = xiCayleyValue (xiRealSpectralPoint q) := rfl

theorem ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro hz
  have := congrArg Complex.im hz
  simp at this

theorem normSq_ofReal_add_I (t : ℝ) : Complex.normSq ((t : ℂ) + Complex.I) = t ^ 2 + 1 := by
  rw [Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im]
  ring

/-- **The conformal Poisson transfer.**  The half-plane Poisson weight of a real ordinate at the
Cayley image of a disc point is the disc Poisson kernel at the ordinate's circle point, divided by
the Cauchy weight normalizer. -/
theorem im_cayleyDisc_div_normSq (t : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    (cayleyDisc w).im / Complex.normSq ((t : ℂ) - cayleyDisc w)
      = poissonKernel 0 w (xiCayleyValue t) / (t ^ 2 + 1) := by
  have hne : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  have ht : (t : ℂ) + Complex.I ≠ 0 := ofReal_add_I_ne_zero t
  have hsub : (t : ℂ) - cayleyDisc w
      = ((t : ℂ) + Complex.I) * (xiCayleyValue t - w) / (1 - w) := by
    rw [cayleyDisc, xiCayleyValue]
    field_simp
    ring
  have hnorm : ‖xiCayleyValue t‖ = 1 := xiCayleyValue_norm t
  have hnsq : Complex.normSq ((t : ℂ) - cayleyDisc w)
      = (t ^ 2 + 1) * ‖xiCayleyValue t - w‖ ^ 2 / ‖1 - w‖ ^ 2 := by
    rw [hsub, Complex.normSq_div, Complex.normSq_mul, normSq_ofReal_add_I,
      ← Complex.sq_norm, ← Complex.sq_norm]
  rw [hnsq, cayleyDisc_im w, poissonKernel_def]
  simp only [sub_zero]
  rw [hnorm]
  have hden : ‖1 - w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have ht2 : (t : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  by_cases hzw : ‖xiCayleyValue t - w‖ ^ 2 = 0
  · rw [hzw]
    simp
  · field_simp
    ring

end

end RHTower
