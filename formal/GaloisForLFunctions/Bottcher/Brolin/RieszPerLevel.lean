/-
# Böttcher tower — Brolin GAP-A: the level-`n` Riesz identity

This module discharges the **per-level** step of GAP-A: the finite normalized
pullback measure `preBrolinMeasure c n` is the distributional
`(2π)⁻¹ Δ greenApprox_n` (tested against `C²` compactly supported functions),

  `IsRieszMeasureOfSmooth (preBrolinMeasure c n) (fun z => greenApprox c z n)`.

`preBrolinMeasure c n = (2ⁿ)⁻¹ · rootCountingMeasure` is a finite average of Dirac
masses on the level-`n` zero pullback, and `greenApprox c z n = (2ⁿ)⁻¹ log‖f_c^[n] z‖`
is the corresponding logarithmic potential (away from the finite atoms).  The
identity is therefore the atomic fundamental solution
`(2π)⁻¹ Δ log‖·−ρ‖ = δ_ρ` (`fundamentalSolutionProp_holds`, RieszLogIBP) summed by
linearity over the root multiset, then scaled.

The single mathlib-absent enabler is 2D log-integrability against a `C²` bump:
`Integrable (log‖·−ρ‖ · Δφ)`.  We build it from local integrability of `log‖·‖`
(dominated by `‖z‖⁻¹ + ‖z‖`, using `integrableOn_ball_of_norm_le_rpow`), multiply
by the bounded compactly-supported `Δφ`, and translate to arbitrary center `ρ` by
the measure-preserving shift `z ↦ z − ρ`.

This is the first of the three GAP-A limbs (per-level → `L¹_loc` potential limit →
Weyl support theorem).
-/
import GaloisForLFunctions.Bottcher.Brolin.RieszLogIBP
import GaloisForLFunctions.Bottcher.Brolin.FiniteMeasures
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory Complex Filter Metric Set Laplacian InnerProductSpace
open scoped Laplacian Real Topology

namespace Bottcher

noncomputable section

/-- **Local integrability of the planar log kernel.**  `z ↦ log‖z‖` is locally
integrable on `ℂ`.  On each compact `K ⊆ ball 0 R` we dominate `|log‖z‖|` by
`‖z‖⁻¹ + ‖z‖` (via `log x ≤ x − 1` applied to `x` and `x⁻¹`); `‖z‖⁻¹` is ball
integrable by the `‖·‖^(−1)` decay estimate and `‖z‖` is continuous. -/
theorem locallyIntegrable_log_norm : LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.exists_pos_norm_lt
  have hsub : K ⊆ ball 0 R := fun z hz => mem_ball_zero_iff.mpr (hR z hz)
  refine (?_ : IntegrableOn (fun z : ℂ => Real.log ‖z‖) (ball 0 R)).mono_set hsub
  have hinv : IntegrableOn (fun z : ℂ => ‖z‖⁻¹) (ball 0 R) := by
    have hd : (1:ℕ) ≤ Module.finrank ℝ ℂ := by simp [Complex.finrank_real_complex]
    have hα : (1:ℝ) < (Module.finrank ℝ ℂ : ℝ) := by
      rw [Complex.finrank_real_complex]; norm_num
    refine integrableOn_ball_of_norm_le_rpow (C := 1) hd hα ?_ ?_
    · exact Filter.Eventually.of_forall (fun z => by
        rw [one_mul, Real.rpow_neg_one]
        exact le_of_eq (Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))))
    · exact (continuous_norm.measurable.inv).aestronglyMeasurable
  have hnorm : IntegrableOn (fun z : ℂ => ‖z‖) (ball 0 R) :=
    (continuous_norm.locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall
  have hg : IntegrableOn (fun z : ℂ => ‖z‖⁻¹ + ‖z‖) (ball 0 R) := hinv.add hnorm
  refine Integrable.mono' hg (continuous_norm.measurable.log.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  by_cases hz : z = 0
  · simp [hz]
  · have ht : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : Real.log ‖z‖⁻¹ ≤ ‖z‖⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_inv] at h1
      nlinarith [ht.le, inv_nonneg.mpr ht.le]
    · have h2 : Real.log ‖z‖ ≤ ‖z‖ - 1 := Real.log_le_sub_one_of_pos ht
      nlinarith [inv_nonneg.mpr ht.le]

/-- **Centered log-kernel integrability against a `C²` bump.**
`z ↦ log‖z‖ · Δφ(z)` is integrable when `φ` is `C²` with compact support: `log‖·‖`
is locally integrable, `Δφ` is bounded and supported in a ball, so the product is
supported in that ball and integrable there. -/
theorem integrable_log_norm_mul_laplacian_centered (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => Real.log ‖z‖ * Δ φ z) := by
  have hcΔ : Continuous (Δ φ) := by
    have hcont : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
      hφ.continuous_iteratedFDeriv (by norm_num)
    rw [show (Δ φ) = fun x => iteratedFDeriv ℝ 2 φ x ![1, 1] + iteratedFDeriv ℝ 2 φ x ![I, I] from
      laplacian_eq_iteratedFDeriv_complexPlane φ]
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1,1]).continuous.comp hcont).add
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![I,I]).continuous.comp hcont)
  obtain ⟨R, hR0, hR⟩ := hφc.exists_pos_le_norm
  have hΔloc : ∀ z : ℂ, R < ‖z‖ → Δ φ z = 0 := by
    intro z hz
    have hEZ : φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) :=
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
        (fun x hx => hR x (le_of_lt hx))
    rw [(laplacian_congr_nhds hEZ).eq_of_nhds]; simp
  have hΔc : HasCompactSupport (Δ φ) := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 R) (fun z hz => by
      rw [Function.mem_support] at hz; rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h; exact hz (hΔloc z (by linarith [not_le.mp h])))
  obtain ⟨M, hM⟩ := hΔc.exists_bound_of_continuous hcΔ
  have hlogInt : IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.closedBall 0 R) :=
    locallyIntegrable_log_norm.integrableOn_isCompact (isCompact_closedBall 0 R)
  have hbdd : IntegrableOn (fun z => Δ φ z * Real.log ‖z‖) (Metric.closedBall 0 R) :=
    hlogInt.bdd_mul hcΔ.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => hM z))
  have hfeq : (fun z => Real.log ‖z‖ * Δ φ z)
      = (Metric.closedBall 0 R).indicator (fun z => Real.log ‖z‖ * Δ φ z) := by
    funext z
    by_cases hz : z ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hΔloc z (by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz; exact hz), mul_zero]
  rw [hfeq]
  refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
  exact hbdd.congr_fun (fun z _ => mul_comm _ _) measurableSet_closedBall

/-- **Translated log-kernel integrability.** `z ↦ log‖z−ρ‖ · Δφ(z)` is integrable
for `C²` compact-support `φ` and any center `ρ`.  Reduces to the centered case for
`ψ(x) = φ(x+ρ)` (`Δψ = (Δφ)(·+ρ)`) via the measure-preserving shift `z ↦ z − ρ`. -/
theorem integrable_log_norm_sub_mul_laplacian (ρ : ℂ) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => Real.log ‖z - ρ‖ * Δ φ z) := by
  have hψ : ContDiff ℝ 2 (fun x => φ (x + ρ)) := contDiff_comp_add_right φ ρ hφ
  have hψc : HasCompactSupport (fun x => φ (x + ρ)) := hasCompactSupport_comp_add_right φ ρ hφc
  have hcent := integrable_log_norm_mul_laplacian_centered (fun x => φ (x + ρ)) hψ hψc
  rw [laplacian_comp_add_right] at hcent
  have hmp : MeasurePreserving (fun z : ℂ => z - ρ) volume volume :=
    measurePreserving_sub_right volume ρ
  have hres := (hmp.integrable_comp hcent.aestronglyMeasurable).mpr hcent
  refine hres.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Function.comp_apply, sub_add_cancel]

/-- **Integrability of the finite root-log potential against a bump.**  The kernel
sum `z ↦ (∑_{r∈s} log‖z−r‖) · Δφ(z)` is integrable for any finite atom multiset
`s`, by summing `integrable_log_norm_sub_mul_laplacian` over `s`. -/
theorem integrable_rootLogSum_mul_laplacian (s : Multiset ℂ) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => (s.map (fun r => Real.log ‖z - r‖)).sum * Δ φ z) := by
  induction s using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero, zero_mul]
      exact integrable_zero _ _ _
  | cons a t ih =>
      have heq : (fun z => ((a ::ₘ t).map (fun r => Real.log ‖z - r‖)).sum * Δ φ z)
          = fun z => Real.log ‖z - a‖ * Δ φ z
              + (t.map (fun r => Real.log ‖z - r‖)).sum * Δ φ z := by
        funext z; rw [Multiset.map_cons, Multiset.sum_cons, add_mul]
      rw [heq]
      exact (integrable_log_norm_sub_mul_laplacian a φ hφ hφc).add ih

/-- **Finite Riesz identity for a Dirac multiset.**  `∫ (∑_{r∈s} log‖z−r‖) Δφ(z) dz
= 2π · ∑_{r∈s} φ(r)`.  Multiset linearity of the atomic fundamental solution
`fundamentalSolutionProp_holds`. -/
theorem integral_rootLogSum_mul_laplacian (s : Multiset ℂ) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z, (s.map (fun r => Real.log ‖z - r‖)).sum * Δ φ z)
      = 2 * Real.pi * (s.map φ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have heq : (fun z => ((a ::ₘ t).map (fun r => Real.log ‖z - r‖)).sum * Δ φ z)
          = fun z => Real.log ‖z - a‖ * Δ φ z
              + (t.map (fun r => Real.log ‖z - r‖)).sum * Δ φ z := by
        funext z; rw [Multiset.map_cons, Multiset.sum_cons, add_mul]
      rw [heq, integral_add (integrable_log_norm_sub_mul_laplacian a φ hφ hφc)
        (integrable_rootLogSum_mul_laplacian t φ hφ hφc),
        fundamentalSolutionProp_holds a φ hφ hφc, ih,
        Multiset.map_cons, Multiset.sum_cons, mul_add]

/-- **The level-`n` Riesz identity (GAP-A, per-level limb).**  The finite normalized
pullback measure is the smooth-distributional Laplacian of the `n`-th Green
approximant:

  `μ_{c,n} = (2π)⁻¹ Δ greenApprox_n`  against every `C²` compact-support test.

Away from the finitely many level-`n` zero-pullback atoms,
`greenApprox c z n = (2ⁿ)⁻¹ ∑_{r} log‖z − r‖`; the finite atoms are Lebesgue-null,
so the identity descends from `integral_rootLogSum_mul_laplacian` by scaling. -/
theorem isRieszMeasureOfSmooth_preBrolinMeasure (c : ℂ) (n : ℕ) :
    IsRieszMeasureOfSmooth (preBrolinMeasure c n) (fun z => greenApprox c z n) := by
  intro φ hφ hφc
  set s := (quadraticPolyIterate c n).roots with hs
  have haefin : ∀ᵐ z ∂(volume : Measure ℂ), (quadratic c)^[n] z ≠ 0 := by
    have hfin : {z : ℂ | (quadratic c)^[n] z = 0}.Finite := by
      have hsub : {z : ℂ | (quadratic c)^[n] z = 0}
          ⊆ (↑(quadraticPolyIterate c n).roots.toFinset : Set ℂ) := by
        intro z hz
        rw [Set.mem_setOf_eq] at hz
        rw [Finset.mem_coe, Multiset.mem_toFinset,
          Polynomial.mem_roots (quadraticPolyIterate_monic_finiteMeasures c n).ne_zero,
          Polynomial.IsRoot.def, quadraticPolyIterate_eval]
        exact hz
      exact Set.Finite.subset (Finset.finite_toSet _) hsub
    rw [ae_iff]; simp only [not_ne_iff]; exact hfin.measure_zero volume
  have haeI : (fun z => greenApprox c z n * Δ φ z)
      =ᵐ[volume] fun z => (2 ^ n : ℝ)⁻¹ * ((s.map (fun r => Real.log ‖z - r‖)).sum * Δ φ z) := by
    filter_upwards [haefin] with z hz
    have hzeval : (quadraticPolyIterate c n).eval z ≠ 0 := by
      rw [quadraticPolyIterate_eval]; exact hz
    rw [greenApprox, rootLogSum_eq_log_eval_of_monic (quadraticPolyIterate_monic_finiteMeasures c n) hzeval,
      quadraticPolyIterate_eval]
    ring
  rw [integral_preBrolinMeasure_eq_root_average c n φ, integral_congr_ae haeI,
    integral_const_mul, integral_rootLogSum_mul_laplacian s φ hφ hφc]
  have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt Real.two_pi_pos
  field_simp
  ring

/-- **GAP-A limit bridge (Fubini form).**  If a finite measure `μ` has a.e.
logarithmic-potential representation of `G` (`G = −Uᵘ` Lebesgue-a.e.) and the
log kernel is jointly integrable against `volume ⊗ μ` for every `C²` bump, then
`μ` is the smooth-distributional `(2π)⁻¹ ΔG`:

  `∫ φ dμ = (2π)⁻¹ ∫ G · Δφ`.

The proof is Fubini plus the atomic fundamental solution `fundamentalSolutionProp_holds`:
`∫ G Δφ = ∫∫ log‖z−w‖ Δφ(z) dμ(w) dz = ∫ (∫ log‖z−w‖ Δφ(z) dz) dμ(w) = ∫ 2π φ dμ`.
It converts the level-`n` identity `isRieszMeasureOfSmooth_preBrolinMeasure` to the
limit **without any `L¹_loc` convergence** — the only limiting input is the a.e.
potential representation `hrep` (basin representation + Julia-null). -/
theorem isRieszMeasureOfSmooth_of_potentialRep_ae (μ : Measure ℂ) [IsFiniteMeasure μ]
    (G : ℂ → ℝ)
    (hrep : (fun z => G z) =ᵐ[volume] fun z => - logPotential μ z)
    (hint : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      Integrable (Function.uncurry (fun z w => Real.log ‖z - w‖ * Δ φ z)) (volume.prod μ)) :
    IsRieszMeasureOfSmooth μ G := by
  intro φ hφ hφc
  have hInner : (fun z => G z * Δ φ z)
      =ᵐ[volume] fun z => ∫ w, Real.log ‖z - w‖ * Δ φ z ∂μ := by
    filter_upwards [hrep] with z hz
    rw [hz, logPotential, ← integral_neg, integral_mul_const]
    congr 1
    simp only [logKernel, neg_neg]
  have key : (∫ z, G z * Δ φ z) = 2 * Real.pi * ∫ w, φ w ∂μ := by
    rw [integral_congr_ae hInner, integral_integral_swap (hint φ hφ hφc)]
    have hcongr : (fun w => ∫ z, Real.log ‖z - w‖ * Δ φ z) = fun w => 2 * Real.pi * φ w := by
      funext w; exact fundamentalSolutionProp_holds w φ hφ hφc
    rw [hcongr, integral_const_mul]
  rw [key]
  have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt Real.two_pi_pos
  field_simp

/-- **Joint integrability of the log kernel against `volume ⊗ μ`.**  For a finite
measure `μ` carried by `closedBall 0 A` and a `C²` bump `φ` (with `Δφ` supported in
`closedBall 0 R`), `(z,w) ↦ log‖z−w‖ · Δφ(z)` is `volume ⊗ μ` integrable.  The
`z`-marginal for fixed `w` is `integrable_log_norm_sub_mul_laplacian`; the `w`-marginal
is bounded uniformly by translating the ball, `∫_{ball 0 R}|log‖z−w‖|dz ≤ ∫_{ball 0 (R+A)}|log‖z‖|dz`.
This discharges the `hint` hypothesis of `isRieszMeasureOfSmooth_of_potentialRep_ae`. -/
theorem kernel_integrable_prod (μ : Measure ℂ) [IsFiniteMeasure μ] {A : ℝ}
    (hA : μ (Metric.closedBall 0 A)ᶜ = 0) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (Function.uncurry (fun z w => Real.log ‖z - w‖ * Δ φ z)) (volume.prod μ) := by
  have hcΔ : Continuous (Δ φ) := by
    have hcont : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
      hφ.continuous_iteratedFDeriv (by norm_num)
    rw [show (Δ φ) = fun x => iteratedFDeriv ℝ 2 φ x ![1, 1] + iteratedFDeriv ℝ 2 φ x ![I, I] from
      laplacian_eq_iteratedFDeriv_complexPlane φ]
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1,1]).continuous.comp hcont).add
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![I,I]).continuous.comp hcont)
  obtain ⟨R, hR0, hR⟩ := hφc.exists_pos_le_norm
  have hΔloc : ∀ z : ℂ, R < ‖z‖ → Δ φ z = 0 := by
    intro z hz
    have hEZ : φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) :=
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
        (fun x hx => hR x (le_of_lt hx))
    rw [(laplacian_congr_nhds hEZ).eq_of_nhds]; simp
  have hΔc : HasCompactSupport (Δ φ) := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 R) (fun z hz => by
      rw [Function.mem_support] at hz; rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h; exact hz (hΔloc z (by linarith [not_le.mp h])))
  obtain ⟨M, hM⟩ := hΔc.exists_bound_of_continuous hcΔ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hBint : IntegrableOn (fun z : ℂ => |Real.log ‖z‖|) (Metric.closedBall 0 (R+A)) :=
    ((locallyIntegrable_log_norm.integrableOn_isCompact
      (isCompact_closedBall 0 (R+A))).norm).congr
      (Filter.Eventually.of_forall (fun z => (Real.norm_eq_abs _)))
  set B : ℝ := ∫ z in Metric.closedBall (0:ℂ) (R+A), |Real.log ‖z‖| with hBdef
  have hboundw : ∀ w : ℂ, w ∈ Metric.closedBall 0 A →
      (∫ z, |Real.log ‖z - w‖ * Δ φ z|) ≤ M * B := by
    intro w hw
    have hwA : ‖w‖ ≤ A := by rwa [Metric.mem_closedBall, dist_zero_right] at hw
    have htrans : (∫ z, |Real.log ‖z - w‖ * Δ φ z|)
        = ∫ z, |Real.log ‖z‖ * Δ φ (z + w)| := by
      rw [← integral_add_right_eq_self (fun z => |Real.log ‖z - w‖ * Δ φ z|) w]
      apply integral_congr_ae; refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [add_sub_cancel_right]
    rw [htrans]
    have hdom : ∀ z : ℂ, |Real.log ‖z‖ * Δ φ (z + w)|
        ≤ (Metric.closedBall 0 (R+A)).indicator (fun z : ℂ => M * |Real.log ‖z‖|) z := by
      intro z
      by_cases hz : z ∈ Metric.closedBall 0 (R+A)
      · rw [Set.indicator_of_mem hz, abs_mul, mul_comm M]
        have hMw : |Δ φ (z + w)| ≤ M := by rw [← Real.norm_eq_abs]; exact hM (z + w)
        exact mul_le_mul_of_nonneg_left hMw (abs_nonneg _)
      · rw [Set.indicator_of_notMem hz]
        have hzw : Δ φ (z + w) = 0 := by
          apply hΔloc
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
          by_contra hle
          rw [not_lt] at hle
          have hzle : ‖z‖ ≤ R + A := by
            calc ‖z‖ = ‖(z + w) - w‖ := by ring_nf
            _ ≤ ‖z + w‖ + ‖w‖ := norm_sub_le _ _
            _ ≤ R + A := by linarith
          linarith
        rw [hzw, mul_zero, abs_zero]
    have hindint : Integrable
        ((Metric.closedBall 0 (R+A)).indicator (fun z : ℂ => M * |Real.log ‖z‖|)) := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact hBint.const_mul M
    have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
      hindint (Filter.Eventually.of_forall hdom)
    calc (∫ z, |Real.log ‖z‖ * Δ φ (z + w)|)
        ≤ ∫ z, (Metric.closedBall 0 (R+A)).indicator (fun z : ℂ => M * |Real.log ‖z‖|) z := hle
      _ = M * B := by
          rw [integral_indicator measurableSet_closedBall, integral_const_mul]
  -- assemble via integrable_prod_iff on the swapped product, then swap
  have hAEg : AEStronglyMeasurable
      (Function.uncurry (fun w z => Real.log ‖z - w‖ * Δ φ z)) (μ.prod volume) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact ((continuous_snd.sub continuous_fst).norm).measurable.log
    · exact hcΔ.measurable.comp measurable_snd
  have haew : ∀ᵐ w ∂μ, w ∈ Metric.closedBall (0:ℂ) A := by
    rw [ae_iff]
    have : {w : ℂ | ¬ w ∈ Metric.closedBall (0:ℂ) A} = (Metric.closedBall (0:ℂ) A)ᶜ := by
      ext w; simp
    rw [this]; exact hA
  have hprodμ : Integrable
      (Function.uncurry (fun w z => Real.log ‖z - w‖ * Δ φ z)) (μ.prod volume) := by
    refine (integrable_prod_iff hAEg).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall
        (fun w => integrable_log_norm_sub_mul_laplacian w φ hφ hφc)
    · refine Integrable.mono' (integrable_const (M * B)) (hAEg.norm.integral_prod_right') ?_
      filter_upwards [haew] with w hw
      have hnn : 0 ≤ ∫ z, ‖Function.uncurry (fun w z => Real.log ‖z - w‖ * Δ φ z) (w, z)‖ ∂volume :=
        integral_nonneg (fun z => norm_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      have heq : (∫ z, ‖Function.uncurry (fun w z => Real.log ‖z - w‖ * Δ φ z) (w, z)‖ ∂volume)
          = ∫ z, |Real.log ‖z - w‖ * Δ φ z| := by
        apply integral_congr_ae; refine Filter.Eventually.of_forall (fun z => ?_)
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
      rw [heq]; exact hboundw w hw
  refine hprodμ.swap.congr (Filter.Eventually.of_forall (fun p => ?_))
  obtain ⟨z, w⟩ := p
  rfl



/-- **GAP-A limit bridge, carrier form.**  For a finite measure carried by a ball,
the smooth Riesz identity follows from the a.e. potential representation alone
(joint integrability is automatic via `kernel_integrable_prod`). -/
theorem isRieszMeasureOfSmooth_of_potentialRep_ae_carrier (μ : Measure ℂ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : μ (Metric.closedBall 0 A)ᶜ = 0) (G : ℂ → ℝ)
    (hrep : (fun z => G z) =ᵐ[volume] fun z => - logPotential μ z) :
    IsRieszMeasureOfSmooth μ G :=
  isRieszMeasureOfSmooth_of_potentialRep_ae μ G hrep
    (fun φ hφ hφc => kernel_integrable_prod μ hA φ hφ hφc)

end

end Bottcher
