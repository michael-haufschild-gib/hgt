import GaloisForLFunctions.HTGeometry.ClockTwoSpeciesFoliation
import GaloisForLFunctions.HTGeometry.KleinGordonRegularProbes

/-!
# Foliated charts carry probes of the regularity the conformal transfer needs

A chart admitting a non-null foliation whose invariants are functions of the leaf label carries
probes obtained by solving a linear ordinary differential equation along the label. Such a probe is
twice differentiable only on the tube over the interval where the ODE was solved — exactly the
regularity the conformal calculus consumes, once that calculus is read on a region.

With this the conformal transfer applies to foliated charts as well, so the reconstruction covers
every conformal rescaling of a foliated chart, not only of the flat one.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-! ## Composition with the leaf label -/

section Comp

variable {d : ℕ}

/-- **A field constant along the leaves is regular on the tube.** If `w` is twice differentiable on
an interval and the leaf label is smooth, then `w ∘ φ` has differentiable partials on the tube over
that interval. -/
theorem differentiablePartialsOn_comp {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {w dw ddw : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hw1 : ∀ t ∈ S, HasDerivAt w (dw t) t) (hw2 : ∀ t ∈ S, HasDerivAt dw (ddw t) t) :
    SmoothMetricChart.DifferentiablePartialsOn (fun y => w (φ y)) (φ ⁻¹' S) where
  base := fun x hx => differentiableAt_comp (differentiableAt_of_contDiff_infty hφ x) (hw1 (φ x) hx)
  coord := by
    intro i x hx
    have heq : (coordPartial i fun y => w (φ y)) =ᶠ[nhds x]
        fun y => dw (φ y) * coordPartial i φ y :=
      Filter.eventuallyEq_of_mem ((hS.preimage hφ.continuous).mem_nhds hx) fun y hy =>
        coordPartial_comp (differentiableAt_of_contDiff_infty hφ y) (hw1 (φ y) hy) i
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact (differentiableAt_comp (differentiableAt_of_contDiff_infty hφ x) (hw2 (φ x) hx)).mul
      (differentiableAt_of_contDiff_infty (contDiff_coordPartial hφ i) x)

end Comp

/-! ## Regular probes on a foliated chart -/

section Foliation

variable {d : ℕ} (M : SmoothMetricChart d)

/-- **Regular clock probes on a chart with a leaf-label foliation.** -/
theorem regularOpenProbes_foliation {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) :
    RegularOpenProbes M.dalembert (fun y => V (φ y)) := by
  intro x₀
  obtain ⟨w, dw, ddw, ε, hε, hwb, hd1, hd2, heq⟩ :=
    exists_localLinearProbe (hRc.div hPc hP0) (hV.div hPc hP0) (φ x₀)
  have hSopen : IsOpen (Ioo (φ x₀ - ε) (φ x₀ + ε)) := isOpen_Ioo
  have hTopen : IsOpen (φ ⁻¹' Ioo (φ x₀ - ε) (φ x₀ + ε)) := hSopen.preimage hφ.continuous
  have hx₀T : x₀ ∈ φ ⁻¹' Ioo (φ x₀ - ε) (φ x₀ + ε) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hureg : SmoothMetricChart.DifferentiablePartialsOn (fun y => w (φ y))
      (φ ⁻¹' Ioo (φ x₀ - ε) (φ x₀ + ε)) := differentiablePartialsOn_comp hφ hSopen hd1 hd2
  have hux₀ : w (φ x₀) = 1 := hwb
  have hcont : ContinuousAt (fun y => w (φ y)) x₀ := (hureg.base x₀ hx₀T).continuousAt
  have hne : ∀ᶠ y in nhds x₀, w (φ y) ≠ 0 := by
    refine hcont.eventually_ne ?_
    rw [hux₀]
    norm_num
  obtain ⟨W₀, hW₀sub, hW₀open, hW₀mem⟩ := mem_nhds_iff.mp hne
  refine ⟨W₀ ∩ φ ⁻¹' Ioo (φ x₀ - ε) (φ x₀ + ε), hW₀open.inter hTopen, ⟨hW₀mem, hx₀T⟩,
    fun y => w (φ y), hureg.mono inter_subset_right, fun z hz => ?_, fun z hz => hW₀sub hz.1⟩
  have hred := dalembert_comp M hφ hSopen hd1 hd2 (hz.2 : φ z ∈ Ioo (φ x₀ - ε) (φ x₀ + ε))
  have hPne := hP0 (φ z)
  have hE : ddw (φ z) + R (φ z) / P (φ z) * dw (φ z)
      + V (φ z) / P (φ z) * w (φ z) = 0 := heq (φ z)
  have hPR : P (φ z) * (R (φ z) / P (φ z)) = R (φ z) := by field_simp
  have hPV : P (φ z) * (V (φ z) / P (φ z)) = V (φ z) := by field_simp
  have hzero : P (φ z) * (ddw (φ z) + R (φ z) / P (φ z) * dw (φ z)
      + V (φ z) / P (φ z) * w (φ z)) = 0 := by rw [hE]; ring
  have hmul : P (φ z) * ddw (φ z) + R (φ z) * dw (φ z) + V (φ z) * w (φ z) = 0 := by
    calc P (φ z) * ddw (φ z) + R (φ z) * dw (φ z) + V (φ z) * w (φ z)
        = P (φ z) * ddw (φ z) + P (φ z) * (R (φ z) / P (φ z)) * dw (φ z)
          + P (φ z) * (V (φ z) / P (φ z)) * w (φ z) := by rw [hPR, hPV]
      _ = P (φ z) * (ddw (φ z) + R (φ z) / P (φ z) * dw (φ z)
          + V (φ z) / P (φ z) * w (φ z)) := by ring
      _ = 0 := hzero
  show M.dalembert (fun y => w (φ y)) z + V (φ z) * w (φ z) = 0
  rw [hred, hP z, hR z]
  linarith [hmul]

/-- **Regular probes for the conformal potential of a species on a foliated chart.** -/
theorem regularOpenProbes_foliationConformal {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {P R : ℝ → ℝ} (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ₀) (a massSq : ℝ) :
    RegularOpenProbes M.dalembert (fun y => foliationPotential P R a massSq σ₀ (φ y)) :=
  regularOpenProbes_foliation M hφ hP hR hPc hRc hP0
    (contDiff_foliationPotential hPc hRc a massSq hσ)

end Foliation

/-! ## Conformal rescalings of a foliated chart -/

section Rescaled

variable {d : ℕ} (M : SmoothMetricChart d)

open ExponentialSecondOrderClockCalculus

/-- **Clock probes on every conformal rescaling of a foliated chart.** The probe of the foliation is
carried along the rescaling by conjugation with the conformal weight. -/
theorem regularOpenProbes_conformalRescale_foliation {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) :
    RegularOpenProbes (M.conformalRescale sigma hsigma).dalembert
      (M.conformalTransferPotential sigma fun y => V (φ y)) :=
  regularOpenProbes_conformalRescale M hsigma
    (regularOpenProbes_foliation M hφ hP hR hPc hRc hP0 hV)

/-- **The two-species scale law on an arbitrary conformal rescaling of a foliated chart.** The
reconstructed scale is the foliation scale corrected by the rescaling — conformal covariance of the
reconstruction, with the probes constructed on both charts. -/
theorem twoSpecies_scale_reconstruction_conformalRescale_foliation {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x)) (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {σ₀ : ℝ → ℝ} (hσ₀ : ContDiff ℝ ∞ σ₀) (a : ℝ)
    {sigma : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (M.conformalRescale sigma hsigma).dalembert
        (M.conformalTransferPotential sigma
          fun y => foliationPotential P R a massSq₁ σ₀ (φ y)) u W →
        SolvesPotentialWaveOn (M.conformalRescale sigma hsigma).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (M.conformalRescale sigma hsigma).dalembert
        (M.conformalTransferPotential sigma
          fun y => foliationPotential P R a massSq₂ σ₀ (φ y)) u W →
        SolvesPotentialWaveOn (M.conformalRescale sigma hsigma).dalembert other₂ u W)
    (x : Fin d → ℝ) :
    (other₁ x - other₂ x) / (massSq₁ - massSq₂) =
      Real.exp (2 * (σ₀ (φ x) - sigma x)) := by
  have e₁ : other₁ = M.conformalTransferPotential sigma
      fun y => foliationPotential P R a massSq₁ σ₀ (φ y) :=
    potential_eq_of_openProbes
      (regularOpenProbes_conformalRescale_foliation M hφ hP hR hPc hRc hP0
        (contDiff_foliationPotential hPc hRc a massSq₁ hσ₀) hsigma).openProbes h₁
  have e₂ : other₂ = M.conformalTransferPotential sigma
      fun y => foliationPotential P R a massSq₂ σ₀ (φ y) :=
    potential_eq_of_openProbes
      (regularOpenProbes_conformalRescale_foliation M hφ hP hR hPc hRc hP0
        (contDiff_foliationPotential hPc hRc a massSq₂ hσ₀) hsigma).openProbes h₂
  have hdiff := foliationPotential_difference P R a massSq₁ massSq₂ σ₀ (φ x)
  have hne : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
  have hsplit : M.conformalTransferPotential sigma
        (fun y => foliationPotential P R a massSq₁ σ₀ (φ y)) x -
      M.conformalTransferPotential sigma
        (fun y => foliationPotential P R a massSq₂ σ₀ (φ y)) x =
      Real.exp (-2 * sigma x) *
        (foliationPotential P R a massSq₁ σ₀ (φ x) -
          foliationPotential P R a massSq₂ σ₀ (φ x)) := by
    simp only [SmoothMetricChart.conformalTransferPotential]
    ring
  have hexp : Real.exp (-2 * sigma x) * Real.exp (2 * σ₀ (φ x)) =
      Real.exp (2 * (σ₀ (φ x) - sigma x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e₁, e₂, hsplit, hdiff, ← hexp]
  field_simp

end Rescaled

end GaloisForLFunctions.HTGeometry
