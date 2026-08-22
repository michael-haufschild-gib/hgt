import GaloisForLFunctions.HTGeometry.GoldenRuleSelfEnergy

/-!
# §VIII Lemma 3: the harmonic measure `dμ_ρ` of `ρ` with respect to the line `iℝ`

§VIII, Lemma 3 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  "for `ρ ∈ ℂ` we let `dμ_ρ(z)` be the harmonic measure of `ρ` with respect to the line
  `iℝ ⊂ ℂ`.  It is a probability measure on the line `iℝ` and coincides with the Dirac mass at
  `ρ` when `ρ` is on the line."

The harmonic measure of `ρ = a + ib` with respect to the imaginary axis is the half-plane Poisson
kernel of height `|a|` centred at `b`.  This module packages it:

* `connesHarmonicDensity` / `connesHarmonicMeasure` - the density and the measure;
* `connes_harmonicMeasure_isProbabilityMeasure` - it is a probability measure whenever `ρ` is off
  the line;
* `connes_harmonic_dirac_limit` - it converges to the Dirac mass at `ρ` as `ρ` approaches the
  line, for an arbitrary **complex** integrand (Connes pairs it with `f̂(Χ̃, z)`), which the
  corpus's real-valued concentration limit did not cover.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **§VIII Lemma 3.**  The density of the harmonic measure of `ρ` with respect to the imaginary
axis: the half-plane Poisson kernel of height `|Re ρ|` centred at `Im ρ`. -/
def connesHarmonicDensity (ρ : ℂ) (t : ℝ) : ℝ := halfPlanePoisson |ρ.re| (t - ρ.im)

theorem connesHarmonicDensity_pos {ρ : ℂ} (hρ : ρ.re ≠ 0) (t : ℝ) :
    0 < connesHarmonicDensity ρ t :=
  halfPlanePoisson_pos (abs_pos.mpr hρ) _

theorem connesHarmonicDensity_nonneg {ρ : ℂ} (hρ : ρ.re ≠ 0) (t : ℝ) :
    0 ≤ connesHarmonicDensity ρ t := (connesHarmonicDensity_pos hρ t).le

theorem connes_harmonicDensity_integrable {ρ : ℂ} (hρ : ρ.re ≠ 0) :
    Integrable (connesHarmonicDensity ρ) volume := by
  have hbase := integrable_halfPlanePoisson (abs_pos.mpr hρ)
  have hshift := hbase.comp_sub_right ρ.im
  exact hshift

/-- **§VIII Lemma 3, total mass one.** -/
theorem connes_harmonicDensity_integral {ρ : ℂ} (hρ : ρ.re ≠ 0) :
    (∫ t : ℝ, connesHarmonicDensity ρ t) = 1 := by
  have hshift : (∫ t : ℝ, halfPlanePoisson |ρ.re| (t - ρ.im))
      = ∫ t : ℝ, halfPlanePoisson |ρ.re| t :=
    integral_sub_right_eq_self (fun t : ℝ => halfPlanePoisson |ρ.re| t) ρ.im
  show (∫ t : ℝ, halfPlanePoisson |ρ.re| (t - ρ.im)) = 1
  rw [hshift, integral_halfPlanePoisson (abs_pos.mpr hρ)]

/-- **§VIII Lemma 3.**  The harmonic measure of `ρ` with respect to the line `iℝ`. -/
def connesHarmonicMeasure (ρ : ℂ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (connesHarmonicDensity ρ t)

/-- **§VIII Lemma 3, "it is a probability measure".** -/
theorem connes_harmonicMeasure_isProbabilityMeasure {ρ : ℂ} (hρ : ρ.re ≠ 0) :
    IsProbabilityMeasure (connesHarmonicMeasure ρ) := by
  constructor
  rw [connesHarmonicMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (connes_harmonicDensity_integrable hρ)
    (Filter.Eventually.of_forall (connesHarmonicDensity_nonneg hρ)),
    connes_harmonicDensity_integral hρ]
  simp

/-- **§VIII Lemma 3, "coincides with the Dirac mass at `ρ` when `ρ` is on the line".**  The
complex-valued concentration limit: as the height goes to zero, pairing against the harmonic
measure returns the value at the centre. -/
theorem connes_harmonic_dirac_limit {f : ℝ → ℂ} (hf : Integrable f volume) {b : ℝ}
    (hc : ContinuousAt f b) :
    Tendsto (fun ε : ℝ => ((∫ t : ℝ, halfPlanePoisson ε (t - b) * (f t).re : ℝ) : ℂ)
        + Complex.I * ((∫ t : ℝ, halfPlanePoisson ε (t - b) * (f t).im : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (f b)) := by
  have hre : Integrable (fun t : ℝ => (f t).re) volume := hf.re
  have him : Integrable (fun t : ℝ => (f t).im) volume := hf.im
  have hcre : ContinuousAt (fun t : ℝ => (f t).re) b :=
    Complex.continuous_re.continuousAt.comp hc
  have hcim : ContinuousAt (fun t : ℝ => (f t).im) b :=
    Complex.continuous_im.continuousAt.comp hc
  have h1 := tendsto_halfPlanePoisson_density hre hcre
  have h2 := tendsto_halfPlanePoisson_density him hcim
  have h1' : Tendsto (fun ε : ℝ => ((∫ t : ℝ, halfPlanePoisson ε (t - b) * (f t).re : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (((f b).re : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt).tendsto.comp h1
  have h2' : Tendsto (fun ε : ℝ => ((∫ t : ℝ, halfPlanePoisson ε (t - b) * (f t).im : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (((f b).im : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt).tendsto.comp h2
  have hsum := h1'.add ((h2'.const_mul Complex.I))
  have hval : (((f b).re : ℝ) : ℂ) + Complex.I * (((f b).im : ℝ) : ℂ) = f b := by
    rw [mul_comm]
    exact Complex.re_add_im (f b)
  rw [hval] at hsum
  exact hsum

end

end GaloisForLFunctions.RHTower
