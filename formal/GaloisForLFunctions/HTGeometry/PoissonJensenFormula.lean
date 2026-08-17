import Mathlib
import GaloisForLFunctions.HTGeometry.PoissonInteriorLogKernel

/-!
# The Poisson–Jensen formula

Jensen's formula computes the plain circle average of `log ‖f‖`.  Poisson–Jensen computes the
Poisson average against the Herglotz–Riesz kernel at an interior point `w`, and is the starting
point of Nevanlinna's estimate for the logarithmic derivative.

The proof follows mathlib's proof of Jensen's formula: extract the divisor of `f` as an explicit
factorized rational times a zero-free analytic factor `g`, evaluate the Poisson average of each
divisor term by the Blaschke-corrected kernel of `PoissonInteriorLogKernel`, and evaluate the
Poisson average of `log ‖g‖` by the Poisson formula for harmonic functions.
-/

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real InnerProductSpace MeromorphicOn

theorem continuousOn_re_herglotzRieszKernel {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    ContinuousOn (Complex.re ∘ herglotzRieszKernel c w) (sphere c |R|) := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hne : ∀ z ∈ sphere c |R|, (z - c) - (w - c) ≠ 0 := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos hR] at hz
    intro h0
    have hzw : z = w := by linear_combination h0
    rw [hzw] at hz
    linarith
  apply Complex.continuous_re.comp_continuousOn
  simp only [herglotzRieszKernel_fun_def]
  exact ContinuousOn.div (by fun_prop) (by fun_prop) hne

/-- **Poisson–Jensen formula.**  For a meromorphic function on a closed disc, not identically
zero, the Poisson average of `log ‖f‖` over the boundary circle equals the sum of the divisor
contributions through the Blaschke-corrected kernels plus the value at the interior point of the
logarithm of the zero-free factor. -/
theorem poissonJensen {c w : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (h₁f : MeromorphicOn f (closedBall c |R|))
    (h₂f : ∀ u : (closedBall c |R| : Set ℂ), meromorphicOrderAt f u ≠ ⊤)
    (hw : w ∈ ball c R) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c |R|) ∧
      (∀ u : (closedBall c |R| : Set ℂ), g u ≠ 0) ∧
      (Real.log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (closedBall c |R|)]
        (∑ᶠ u, ((divisor f (closedBall c |R|) u : ℝ) * Real.log ‖· - u‖)) + (Real.log ‖g ·‖) ∧
      Real.circleAverage ((Complex.re ∘ herglotzRieszKernel c w) • (Real.log ‖f ·‖)) c R
        = (∑ᶠ u, (divisor f (closedBall c |R|) u : ℝ) *
            Real.log ‖innerLogKernel c u R w‖) + Real.log ‖g w‖ := by
  classical
  have habs : |R| = R := abs_of_pos hR
  set CB := closedBall c |R| with hCB
  have h₃f : (divisor f CB).support.Finite :=
    (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles h₂f h₃f
  have h₄g := extract_zeros_poles_log h₂g h₃g
  refine ⟨g, h₁g, h₂g, h₄g, ?_⟩
  set P : ℂ → ℝ := Complex.re ∘ herglotzRieszKernel c w with hP
  have hPcont : ContinuousOn P (sphere c |R|) := continuousOn_re_herglotzRieszKernel hw
  set S : ℂ → ℝ := ∑ᶠ u, ((divisor f CB u : ℝ) * Real.log ‖· - u‖) with hS
  set L : ℂ → ℝ := (Real.log ‖g ·‖) with hL
  -- replace `log ‖f‖` by its divisor decomposition on the circle
  have hcongr : (P • (Real.log ‖f ·‖)) =ᶠ[Filter.codiscreteWithin (sphere c |R|)] (P • (S + L)) := by
    have := Filter.codiscreteWithin_mono (sphere_subset_closedBall (x := c) (ε := |R|)) h₄g
    filter_upwards [this] with z hz
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [hz]
  rw [circleAverage_congr_codiscreteWithin hcongr hR.ne']
  -- split the average
  have hSint : CircleIntegrable S c R := circleIntegrable_log_norm_factorizedRational _
  have hLint : CircleIntegrable L c R :=
    ((h₁g.mono sphere_subset_closedBall).meromorphicOn).circleIntegrable_log_norm
  have hsplit : P • (S + L) = P • S + P • L := smul_add P S L
  rw [hsplit, circleAverage_add (hSint.smul_of_continuousOn hPcont)
    (hLint.smul_of_continuousOn hPcont)]
  congr 1
  · -- the divisor part
    have hfin : S = ∑ u ∈ h₃f.toFinset, ((divisor f CB u : ℝ) * Real.log ‖· - u‖) := by
      rw [hS]
      apply finsum_eq_sum_of_support_subset
      intro u hu
      simp only [Function.mem_support] at hu
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro hzero
      apply hu
      funext z
      simp [hzero]
    rw [hfin]
    have hsmul : P • (∑ u ∈ h₃f.toFinset, ((divisor f CB u : ℝ) * Real.log ‖· - u‖))
        = ∑ u ∈ h₃f.toFinset, (P • ((divisor f CB u : ℝ) • (fun z => Real.log ‖z - u‖))) := by
      funext z
      simp only [Pi.smul_apply', Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      rfl
    rw [hsmul, circleAverage_sum (fun u _ => by
      refine CircleIntegrable.smul_of_continuousOn ?_ hPcont
      exact ((MeromorphicOn.circleIntegrable_log_norm (f := fun z => z - u)
        (fun z _ => (analyticAt_id.sub analyticAt_const).meromorphicAt))).smul _)]
    have hval : ∀ u ∈ h₃f.toFinset,
        Real.circleAverage (P • ((divisor f CB u : ℝ) • (fun z => Real.log ‖z - u‖))) c R
          = (divisor f CB u : ℝ) * Real.log ‖innerLogKernel c u R w‖ := by
      intro u hu
      have humem : u ∈ CB := by
        have : u ∈ Function.support (divisor f CB) := by
          simpa using hu
        exact (divisor f CB).supportWithinDomain this
      have hcomm : P • ((divisor f CB u : ℝ) • (fun z => Real.log ‖z - u‖))
          = (divisor f CB u : ℝ) • (P • (fun z => Real.log ‖z - u‖)) := by
        funext z
        show P z * ((divisor f CB u : ℝ) * Real.log ‖z - u‖)
          = (divisor f CB u : ℝ) * (P z * Real.log ‖z - u‖)
        ring
      have humem' : u ∈ closedBall c R := by
        rw [hCB, habs] at humem
        exact humem
      rw [hcomm, circleAverage_smul,
        circleAverage_re_herglotzRieszKernel_mul_log_of_mem_closedBall humem' hw]
      simp
    rw [Finset.sum_congr rfl hval]
    symm
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro hzero
    apply hu
    simp [hzero]
  · -- the zero-free part
    have hharm : HarmonicOnNhd L (closedBall c |R|) := by
      intro x hx
      exact AnalyticAt.harmonicAt_log_norm (h₁g x hx) (h₂g ⟨x, hx⟩)
    have hwmem : w ∈ ball c |R| := by rwa [habs]
    have := HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul hharm hwmem
    rw [habs] at this
    exact this

end GaloisForLFunctions.HTGeometry.PoissonJensen
