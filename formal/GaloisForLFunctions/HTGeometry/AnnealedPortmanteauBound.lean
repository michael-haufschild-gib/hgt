/-
# Annealed upper bounds along a weakly convergent family

Weak convergence controls continuous statistics only, but an upper semicontinuous statistic is
squeezed from above by continuous majorants with almost the same limit integral, so its upper limit
along the family is still at most its limit integral.  Markov's inequality then turns that annealed
bound into a bound on the limiting probability of any event on which the statistic is large.

Main results:
* `limsup_integral_le_of_tendsto_of_upperSemicontinuous` — **the annealed Portmanteau bound**.
* `limsup_measureReal_ge_le_of_tendsto` — the Markov form.
* `limsup_measureReal_le_of_subset_ge` — the form used at an exponentially small level.
-/
import GaloisForLFunctions.HTGeometry.UpperSemicontinuousMajorant
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Filter MeasureTheory Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Annealed

variable {Omega : Type*} [MetricSpace Omega] [CompactSpace Omega] [MeasurableSpace Omega]
  [BorelSpace Omega] [Nonempty Omega]
variable {gamma : Type*} {l : Filter gamma} [l.NeBot]

theorem integrable_of_bounded_norm {mu : Measure Omega} [IsFiniteMeasure mu] {f : Omega → ℝ}
    (hmeas : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : Integrable f mu :=
  (MeasureTheory.integrable_const M).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- **The annealed Portmanteau bound.**  Along a weakly convergent family of probability measures
the upper limit of the mean of an upper semicontinuous statistic is at most its limit mean. -/
theorem limsup_integral_le_of_tendsto_of_upperSemicontinuous
    {mus : gamma → ProbabilityMeasure Omega} {mu : ProbabilityMeasure Omega}
    (hconv : Tendsto mus l (𝓝 mu))
    {f : Omega → ℝ} (hf : UpperSemicontinuous f) (h0 : ∀ x, 0 ≤ f x) {M : ℝ}
    (hM : ∀ x, f x ≤ M) :
    l.limsup (fun i => ∫ x, f x ∂(mus i : Measure Omega))
      ≤ ∫ x, f x ∂(mu : Measure Omega) := by
  classical
  have hmeas : Measurable f := hf.measurable
  have hM0 : (0 : ℝ) ≤ M := le_trans (h0 (Classical.arbitrary _)) (hM _)
  have habs : ∀ x, |f x| ≤ M := fun x => abs_le.mpr ⟨by linarith [h0 x, hM x], hM x⟩
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨g, hgc, hfg, hgM, hgint⟩ := exists_continuous_majorant hf h0 hM
    (mu : Measure Omega) (eps := eps / 2) (by linarith)
  have hgabs : ∀ x, |g x| ≤ M := fun x => abs_le.mpr ⟨by linarith [h0 x, hfg x, hM0], hgM x⟩
  have hgconv : Tendsto (fun i => ∫ x, g x ∂(mus i : Measure Omega)) l
      (𝓝 (∫ x, g x ∂(mu : Measure Omega))) :=
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
      (BoundedContinuousFunction.mkOfCompact ⟨g, hgc⟩)
  have hev : ∀ᶠ i in l, (∫ x, f x ∂(mus i : Measure Omega))
      ≤ (∫ x, f x ∂(mu : Measure Omega)) + eps := by
    have hnear : ∀ᶠ i in l, (∫ x, g x ∂(mus i : Measure Omega))
        < (∫ x, g x ∂(mu : Measure Omega)) + eps / 2 := by
      exact hgconv (Iio_mem_nhds (by linarith))
    refine hnear.mono fun i hi => ?_
    have hmono : (∫ x, f x ∂(mus i : Measure Omega)) ≤ ∫ x, g x ∂(mus i : Measure Omega) :=
      MeasureTheory.integral_mono (integrable_of_bounded_norm hmeas habs)
        (integrable_of_bounded_norm hgc.measurable hgabs) (Pi.le_def.mpr hfg)
    linarith [hgint]
  refine Filter.limsup_le_of_le ?_ hev
  refine Filter.IsBoundedUnder.isCoboundedUnder_le ?_
  refine ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i => ?_)⟩
  exact MeasureTheory.integral_nonneg (Pi.le_def.mpr h0)

/-- Markov's inequality for a bounded nonnegative statistic under a probability measure. -/
theorem measureReal_ge_le_integral_div {nu : Measure Omega} [IsProbabilityMeasure nu]
    {f : Omega → ℝ} (hmeas : Measurable f) (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {theta : ℝ} (htheta : 0 < theta) :
    nu.real {x | theta ≤ f x} ≤ (∫ x, f x ∂nu) / theta := by
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (Pi.le_def.mpr h0))
    (integrable_of_bounded_norm (mu := nu) hmeas hM) theta
  rw [le_div_iff₀ htheta, mul_comm]
  exact hmark

/-- **The Markov form of the annealed bound.**  The limiting probability that the statistic reaches
a level is at most its limit mean divided by that level. -/
theorem limsup_measureReal_ge_le_of_tendsto
    {mus : gamma → ProbabilityMeasure Omega} {mu : ProbabilityMeasure Omega}
    (hconv : Tendsto mus l (𝓝 mu))
    {f : Omega → ℝ} (hf : UpperSemicontinuous f) (h0 : ∀ x, 0 ≤ f x) {M : ℝ}
    (hM : ∀ x, f x ≤ M) {theta : ℝ} (htheta : 0 < theta) :
    l.limsup (fun i => (mus i : Measure Omega).real {x | theta ≤ f x})
      ≤ (∫ x, f x ∂(mu : Measure Omega)) / theta := by
  classical
  have hmeas : Measurable f := hf.measurable
  have hM0 : (0 : ℝ) ≤ M := le_trans (h0 (Classical.arbitrary _)) (hM _)
  have habs : ∀ x, |f x| ≤ M := fun x => abs_le.mpr ⟨by linarith [h0 x, hM x], hM x⟩
  have hstep : ∀ i, (mus i : Measure Omega).real {x | theta ≤ f x}
      ≤ (∫ x, f x ∂(mus i : Measure Omega)) / theta :=
    fun i => measureReal_ge_le_integral_div (nu := (mus i : Measure Omega)) hmeas h0 habs htheta
  have hmain := limsup_integral_le_of_tendsto_of_upperSemicontinuous hconv hf h0 hM
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) l
      (fun i => (mus i : Measure Omega).real {x | theta ≤ f x}) := by
    refine Filter.IsBoundedUnder.isCoboundedUnder_le ?_
    exact ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i => measureReal_nonneg)⟩
  refine le_of_forall_pos_le_add fun eps heps => ?_
  have hev : ∀ᶠ i in l, (mus i : Measure Omega).real {x | theta ≤ f x}
      ≤ (∫ x, f x ∂(mu : Measure Omega)) / theta + eps := by
    have hint : ∀ᶠ i in l, (∫ x, f x ∂(mus i : Measure Omega))
        ≤ (∫ x, f x ∂(mu : Measure Omega)) + eps * theta := by
      by_contra hcon
      rw [Filter.not_eventually] at hcon
      have hfreq : ∃ᶠ i in l, (∫ x, f x ∂(mu : Measure Omega)) + eps * theta
          ≤ ∫ x, f x ∂(mus i : Measure Omega) := hcon.mono fun i hi => (not_le.mp hi).le
      have hbdd : Filter.IsBoundedUnder (· ≤ ·) l
          (fun i => ∫ x, f x ∂(mus i : Measure Omega)) := by
        refine ⟨M, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i => ?_)⟩
        have := MeasureTheory.integral_mono
          (integrable_of_bounded_norm (mu := (mus i : Measure Omega)) hmeas habs)
          (MeasureTheory.integrable_const (μ := (mus i : Measure Omega)) M) (Pi.le_def.mpr hM)
        simpa using this
      have hlt : (∫ x, f x ∂(mu : Measure Omega)) + eps * theta
          ≤ l.limsup (fun i => ∫ x, f x ∂(mus i : Measure Omega)) :=
        Filter.le_limsup_of_frequently_le hfreq hbdd
      nlinarith [hmain, hlt, mul_pos heps htheta]
    refine hint.mono fun i hi => ?_
    refine le_trans (hstep i) ?_
    have hdiv : (∫ x, f x ∂(mus i : Measure Omega)) / theta
        ≤ ((∫ x, f x ∂(mu : Measure Omega)) + eps * theta) / theta := by
      have hmul := mul_le_mul_of_nonneg_right hi (le_of_lt (inv_pos.mpr htheta))
      rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at hmul
    refine le_trans hdiv (le_of_eq ?_)
    field_simp
  exact Filter.limsup_le_of_le hcob hev

/-- **The annealed bound on an event contained in a superlevel set.**  This is the form used when
the event is low circuit complexity and the statistic is the accessibility potential. -/
theorem limsup_measureReal_le_of_subset_ge
    {mus : gamma → ProbabilityMeasure Omega} {mu : ProbabilityMeasure Omega}
    (hconv : Tendsto mus l (𝓝 mu))
    {f : Omega → ℝ} (hf : UpperSemicontinuous f) (h0 : ∀ x, 0 ≤ f x) {M : ℝ}
    (hM : ∀ x, f x ≤ M) {theta : ℝ} (htheta : 0 < theta)
    {E : Set Omega} (hE : ∀ x ∈ E, theta ≤ f x) :
    l.limsup (fun i => (mus i : Measure Omega).real E)
      ≤ (∫ x, f x ∂(mu : Measure Omega)) / theta := by
  classical
  have hmeas : Measurable f := hf.measurable
  have hsub : E ⊆ {x | theta ≤ f x} := fun x hx => hE x hx
  have hmono : ∀ i, (mus i : Measure Omega).real E
      ≤ (mus i : Measure Omega).real {x | theta ≤ f x} := by
    intro i
    refine measureReal_mono hsub ?_
    exact measure_ne_top _ _
  refine le_trans ?_ (limsup_measureReal_ge_le_of_tendsto hconv hf h0 hM htheta)
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall hmono) ?_ ?_
  · refine Filter.IsBoundedUnder.isCoboundedUnder_le ?_
    exact ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i => measureReal_nonneg)⟩
  · exact ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i =>
      measureReal_le_one)⟩

end Annealed


section HardeningCone

/-- **Theorem K's containment.**  Under the deterministic hardening-cone inequality the
continuum-time backward event lies inside a single endpoint event, so no time mesh and no union
bound over `u` is needed. -/
theorem endpoint_le_of_exists_backward
    {S : ℝ → ℕ} {Cminus Cplus : ℝ → ℕ} {T U : ℝ} {s : ℕ}
    (hcone : ∀ u, 0 ≤ u → u ≤ U → Cplus T ≤ Cminus (T - u) + S u)
    (hev : ∃ u, 0 ≤ u ∧ u ≤ U ∧ Cminus (T - u) + S u ≤ s) :
    Cplus T ≤ s := by
  obtain ⟨u, hu0, huU, hle⟩ := hev
  exact le_trans (hcone u hu0 huU) hle

/-- The backward event of `(11bt)`, in the form in which the containment applies. -/
theorem exists_backward_of_le_sub
    {S : ℝ → ℕ} {Cminus : ℝ → ℕ} {T U : ℝ} {s : ℕ}
    {u : ℝ} (hu0 : 0 ≤ u) (huU : u ≤ U) (hS : S u ≤ s) (hle : Cminus (T - u) ≤ s - S u) :
    ∃ u, 0 ≤ u ∧ u ≤ U ∧ Cminus (T - u) + S u ≤ s :=
  ⟨u, hu0, huU, by omega⟩

end HardeningCone

end GaloisForLFunctions.HTGeometry

end
