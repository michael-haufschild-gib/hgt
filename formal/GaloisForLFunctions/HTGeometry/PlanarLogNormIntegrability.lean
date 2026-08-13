import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Topology
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Planar local integrability of the logarithmic norm of a meromorphic function

The logarithmic norm `log ‖f·‖` of a meromorphic function with no locally vanishing branch is
integrable on every closed disc.  The factorized-rational presentation writes it, off a codiscrete
set, as a finite integer combination of logarithmic kernels `log ‖· - u‖` plus the logarithmic
norm of a nonvanishing analytic factor; the kernels are integrable by the polar-coordinate bound
`r·|log r| ≤ S·|log S| + 1`, the analytic part is continuous on the compact disc, and codiscrete
sets carry full planar measure.

This is the area-integrability input for radially averaged Jensen formulas: it bounds annulus
integrals of `log ‖f·‖` by the area of the annulus, which is what makes divisor-counting
asymptotics of doubly periodic functions accessible without period-cell contour integration.

* `mul_abs_log_le`, `integrableOn_log_norm_zero`, `integrableOn_log_norm_sub`;
* `meromorphic_integrableOn_log_norm`.
-/

open Filter MeasureTheory Metric Real

namespace GaloisForLFunctions.HTGeometry

/-- The radial polar weight of the planar logarithmic kernel is bounded on bounded intervals. -/
theorem mul_abs_log_le (S : ℝ) (hS : 1 ≤ S) {r : ℝ} (hr : 0 < r) (hrS : r ≤ S) :
    r * |log r| ≤ S * |log S| + 1 := by
  rcases le_or_gt r 1 with h1 | h1
  · have hb := abs_log_mul_self_lt r hr h1
    have hcomm : |log r * r| = r * |log r| := by
      rw [abs_mul, abs_of_pos hr, mul_comm]
    rw [hcomm] at hb
    nlinarith [abs_nonneg (log S), hS]
  · have hlogpos : 0 ≤ log r := log_nonneg h1.le
    have hlogmono : log r ≤ log S := log_le_log (by linarith) hrS
    rw [abs_of_nonneg hlogpos, abs_of_nonneg (log_nonneg hS)]
    nlinarith [hlogpos, hlogmono, hr.le, hrS]

/-- **The planar logarithmic kernel is integrable on closed discs**, by polar coordinates. -/
theorem integrableOn_log_norm_zero (S : ℝ) :
    IntegrableOn (fun z : ℂ => log ‖z‖) (closedBall (0 : ℂ) S) := by
  set T : ℝ := max S 1 with hT
  have hT1 : 1 ≤ T := le_max_right S 1
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  refine IntegrableOn.mono_set ?_ (closedBall_subset_closedBall (le_max_left S 1))
  set C : ℝ := T * |log T| + 1 with hC
  have hC0 : 0 < C := by positivity
  constructor
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable.restrict
  · rw [hasFiniteIntegral_iff_enorm]
    have hind : ∫⁻ z in closedBall (0 : ℂ) T, ‖log ‖z‖‖ₑ
        = ∫⁻ z, (closedBall (0 : ℂ) T).indicator (fun z : ℂ => ‖log ‖z‖‖ₑ) z := by
      rw [lintegral_indicator (measurableSet_closedBall)]
    rw [hind, ← Complex.lintegral_comp_polarCoord_symm]
    -- bound the polar integrand by C/r · r = C on the strip (0,T] × (-π,π)
    have hbound : ∀ p : ℝ × ℝ, p ∈ polarCoord.target →
        ENNReal.ofReal p.1 • (closedBall (0 : ℂ) T).indicator
          (fun z : ℂ => ‖log ‖z‖‖ₑ) (Complex.polarCoord.symm p)
        ≤ (Set.Ioc (0:ℝ) T ×ˢ Set.Ioo (-π) π).indicator (fun _ => ENNReal.ofReal C) p := by
      rintro ⟨r, θ⟩ hp
      rw [polarCoord_target] at hp
      obtain ⟨hr, hθ⟩ := hp
      simp only [Set.mem_Ioi] at hr
      have hnorm : ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖ = |r| := by
        simp [Complex.polarCoord_symm_apply]
      by_cases hrT : r ≤ T
      · have hmem : (Complex.polarCoord.symm (r, θ) : ℂ) ∈ closedBall (0 : ℂ) T := by
          rw [mem_closedBall, dist_zero_right, hnorm, abs_of_pos hr]
          exact hrT
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (by
          exact Set.mk_mem_prod (Set.mem_Ioc.mpr ⟨hr, hrT⟩) hθ)]
        have hval : ‖log ‖(Complex.polarCoord.symm (r, θ) : ℂ)‖‖ₑ
            = ENNReal.ofReal |log r| := by
          rw [hnorm, abs_of_pos hr]
          rw [Real.enorm_eq_ofReal_abs]
        rw [hval, smul_eq_mul, ← ENNReal.ofReal_mul (le_of_lt hr)]
        exact ENNReal.ofReal_le_ofReal (mul_abs_log_le T hT1 hr hrT)
      · have hnotmem : (Complex.polarCoord.symm (r, θ) : ℂ) ∉ closedBall (0 : ℂ) T := by
          rw [mem_closedBall, dist_zero_right, hnorm, abs_of_pos hr]
          exact fun h => hrT h
        rw [Set.indicator_of_notMem hnotmem]
        simp
    calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • (closedBall (0 : ℂ) T).indicator
          (fun z : ℂ => ‖log ‖z‖‖ₑ) (Complex.polarCoord.symm p)
        ≤ ∫⁻ p in polarCoord.target,
            (Set.Ioc (0:ℝ) T ×ˢ Set.Ioo (-π) π).indicator (fun _ => ENNReal.ofReal C) p :=
          setLIntegral_mono' polarCoord.open_target.measurableSet hbound
      _ ≤ ∫⁻ p, (Set.Ioc (0:ℝ) T ×ˢ Set.Ioo (-π) π).indicator (fun _ => ENNReal.ofReal C) p :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal C * volume (Set.Ioc (0:ℝ) T ×ˢ Set.Ioo (-π) π) := by
          rw [lintegral_indicator ((measurableSet_Ioc).prod (measurableSet_Ioo))]
          simp [lintegral_const, Measure.restrict_apply]
      _ < ⊤ := by
          have hvol : volume (Set.Ioc (0:ℝ) T ×ˢ Set.Ioo (-π) π)
              = volume (Set.Ioc (0:ℝ) T) * volume (Set.Ioo (-π) π) := by
            rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
          rw [hvol]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioo]))

/-- **The translated planar logarithmic kernel is integrable on every closed disc.** -/
theorem integrableOn_log_norm_sub (u c : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => log ‖z - u‖) (closedBall c R) := by
  have hmp : MeasurePreserving (fun z : ℂ => z + -u) volume volume :=
    measurePreserving_add_right volume (-u)
  have hme : MeasurableEmbedding (fun z : ℂ => z + -u) :=
    (MeasurableEquiv.addRight (-u)).measurableEmbedding
  set S : ℝ := ‖c - u‖ + |R| with hS
  have hint : IntegrableOn (fun z : ℂ => log ‖z‖) (closedBall (0 : ℂ) S) :=
    integrableOn_log_norm_zero _
  have hkey := (hmp.integrableOn_comp_preimage hme).mpr hint
  have hcomp : ((fun z : ℂ => log ‖z‖) ∘ fun z : ℂ => z + -u) = fun z : ℂ => log ‖z - u‖ := by
    funext z
    simp [sub_eq_add_neg]
  rw [hcomp] at hkey
  refine hkey.mono_set ?_
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  show z + -u ∈ closedBall (0 : ℂ) S
  rw [mem_closedBall, dist_zero_right]
  calc ‖z + -u‖ = ‖(z - c) + (c - u)‖ := by ring_nf
    _ ≤ ‖z - c‖ + ‖c - u‖ := norm_add_le _ _
    _ ≤ |R| + ‖c - u‖ := by
        gcongr
        exact hz.trans (le_abs_self R)
    _ = S := by rw [hS]; ring

/-- **The logarithmic norm of a meromorphic function is integrable on closed discs.**  The
factorized presentation splits it into finitely many logarithmic kernels and a continuous part,
off a codiscrete set of full planar measure. -/
theorem meromorphic_integrableOn_log_norm {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall c |R|))
    (hfin : ∀ u : (closedBall c |R| : Set ℂ), meromorphicOrderAt f (u : ℂ) ≠ ⊤) :
    IntegrableOn (fun z => log ‖f z‖) (closedBall c |R|) := by
  classical
  set U : Set ℂ := closedBall c |R| with hU
  have hfinsupp : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall c |R|)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hf.extract_zeros_poles hfin hfinsupp
  have hlog := MeromorphicOn.extract_zeros_poles_log hg_ne hfg
  have hae : (fun z => log ‖f z‖) =ᶠ[ae (volume.restrict U)]
      ((∑ᶠ u, fun z => ((MeromorphicOn.divisor f U u : ℝ)) * log ‖z - u‖)
        + fun z => log ‖g z‖) :=
    ae_restrict_le_codiscreteWithin measurableSet_closedBall hlog
  rw [integrableOn_congr_fun_ae hae]
  apply Integrable.add
  · -- the finite sum of kernels
    have hsub : (Function.support fun u => (fun z : ℂ =>
        ((MeromorphicOn.divisor f U u : ℝ)) * log ‖z - u‖)) ⊆ hfinsupp.toFinset := by
      intro u hu
      have hu' : u ∈ (MeromorphicOn.divisor f U).support := by
        by_contra hne
        have h0 : MeromorphicOn.divisor f U u = 0 := by
          by_contra hcon
          exact hne (by simpa using hcon)
        apply hu
        funext z
        simp only [Pi.zero_apply]
        show ((MeromorphicOn.divisor f U u : ℝ)) * log ‖z - u‖ = 0
        rw [h0, Int.cast_zero, zero_mul]
      exact Finset.mem_coe.mpr (hfinsupp.mem_toFinset.mpr hu')
    rw [finsum_eq_sum_of_support_subset _ hsub]
    have hterm : ∀ u ∈ hfinsupp.toFinset,
        IntegrableOn (fun z : ℂ => ((MeromorphicOn.divisor f U u : ℝ)) * log ‖z - u‖) U := by
      intro u _
      exact (integrableOn_log_norm_sub u c |R|).const_mul _
    -- Finset.sum of functions applied pointwise
    have hfun : (∑ u ∈ hfinsupp.toFinset, fun z : ℂ =>
        ((MeromorphicOn.divisor f U u : ℝ)) * log ‖z - u‖)
        = fun z : ℂ => ∑ u ∈ hfinsupp.toFinset,
          ((MeromorphicOn.divisor f U u : ℝ)) * log ‖z - u‖ := by
      funext z
      simp
    rw [hfun]
    exact MeasureTheory.integrable_finsetSum _ hterm
  · -- the analytic nonvanishing part
    have hcont : ContinuousOn (fun z => log ‖g z‖) U := by
      apply ContinuousOn.log
      · exact hg_an.continuousOn.norm
      · intro z hz
        exact norm_ne_zero_iff.mpr (hg_ne ⟨z, hz⟩)
    exact hcont.integrableOn_compact (isCompact_closedBall c |R|)

end GaloisForLFunctions.HTGeometry
