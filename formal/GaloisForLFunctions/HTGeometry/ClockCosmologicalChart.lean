import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonConformallyFlat

/-!
# Cosmological charts and the conformal invariance of causality

A conformal rescaling multiplies every squared interval by a positive factor, so it leaves the
timelike directions, the cones and the chronological diamond unchanged: the causal structure of a
conformally flat chart is the causal structure of the flat one.

The cosmological charts — the flat chart rescaled by a smooth function of the time coordinate, which
is a Friedmann metric in conformal time — are therefore covered by the conformally flat
reconstruction, and the diamond form of the law transports to them verbatim.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

/-! ## Causality is conformally invariant -/

namespace SmoothPseudoMetric

variable {d : ℕ} (g : SmoothPseudoMetric d)

theorem squaredInterval_conformal (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    (x v : Fin d → ℝ) :
    (g.conformal sigma hsigma).squaredInterval x v =
      Real.exp (2 * sigma x) * g.squaredInterval x v := by
  simp only [squaredInterval, conformal_metric, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem neg_conformal_iff (sigma : (Fin d → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma)
    (x v : Fin d → ℝ) :
    (g.conformal sigma hsigma).squaredInterval x v < 0 ↔ g.squaredInterval x v < 0 := by
  rw [squaredInterval_conformal]
  have hpos : 0 < Real.exp (2 * sigma x) := Real.exp_pos _
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem timelikeCone_conformal {d : ℕ} (g : SmoothPseudoMetric d) (sigma : (Fin d → ℝ) → ℝ)
    (hsigma : ContDiff ℝ ∞ sigma) (x : Fin d → ℝ) :
    (g.conformal sigma hsigma).timelikeCone x = g.timelikeCone x := by
  ext v
  exact g.neg_conformal_iff sigma hsigma x v

theorem chronoFuture_conformal {d : ℕ} (g : SmoothPseudoMetric (d + 1))
    (sigma : (Fin (d + 1) → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) (p : Fin (d + 1) → ℝ) :
    chronoFuture (g.conformal sigma hsigma) p = chronoFuture g p := by
  ext x
  exact and_congr_left fun _ => g.neg_conformal_iff sigma hsigma p (x - p)

theorem chronoPast_conformal {d : ℕ} (g : SmoothPseudoMetric (d + 1))
    (sigma : (Fin (d + 1) → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) (q : Fin (d + 1) → ℝ) :
    chronoPast (g.conformal sigma hsigma) q = chronoPast g q := by
  ext x
  exact and_congr_left fun _ => g.neg_conformal_iff sigma hsigma q (x - q)

/-- **The chronological diamond is a conformal invariant.** -/
theorem chronoDiamond_conformal {d : ℕ} (g : SmoothPseudoMetric (d + 1))
    (sigma : (Fin (d + 1) → ℝ) → ℝ) (hsigma : ContDiff ℝ ∞ sigma) (p q : Fin (d + 1) → ℝ) :
    chronoDiamond (g.conformal sigma hsigma) p q = chronoDiamond g p q := by
  rw [chronoDiamond, chronoDiamond, chronoFuture_conformal, chronoPast_conformal]

end SmoothPseudoMetric

/-! ## Cosmological charts -/

section Cosmological

variable {d N : ℕ}

/-- The conformal factor of a cosmological chart: a smooth function of the time coordinate. -/
noncomputable def cosmologicalFactor {A : ℝ → ℝ} (_hA : ContDiff ℝ ∞ A) (d : ℕ) :
    (Fin (d + 1) → ℝ) → ℝ := fun y => A (y 0)

theorem contDiff_cosmologicalFactor {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (d : ℕ) :
    ContDiff ℝ ∞ (cosmologicalFactor hA d) :=
  hA.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0).contDiff

/-- **A cosmological chart**: the flat chart rescaled by a smooth function of the time coordinate,
that is, a Friedmann metric written in conformal time. -/
noncomputable def cosmologicalChart {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (d : ℕ) :
    SmoothMetricChart (d + 1) :=
  (kgChart d).conformalRescale (cosmologicalFactor hA d) (contDiff_cosmologicalFactor hA d)

/-- **Clock probes for every smooth potential on a cosmological chart.** -/
theorem regularOpenProbes_cosmologicalChart {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {P : (Fin (d + 1) → ℝ) → ℝ} (hP : ContDiff ℝ ∞ P) :
    RegularOpenProbes (cosmologicalChart hA d).dalembert P :=
  regularOpenProbes_conformalRescale_kgChart (N := N) hN (contDiff_cosmologicalFactor hA d) hP

/-- **The two-species conformal clock scale law on a cosmological chart.** -/
theorem twoSpecies_scale_reconstruction_cosmological {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {tau : (Fin (d + 1) → ℝ) → ℝ} (htau : ContDiff ℝ ∞ tau)
    {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (cosmologicalChart hA d).dalembert
        ((cosmologicalChart hA d).conformalPotential 0 massSq tau) u W →
        SolvesPotentialWaveOn (cosmologicalChart hA d).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn (cosmologicalChart hA d).dalembert
        ((cosmologicalChart hA d).conformalPotential 0 0 tau) u W →
        SolvesPotentialWaveOn (cosmologicalChart hA d).dalembert other₂ u W)
    (x : Fin (d + 1) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * tau x) :=
  twoSpecies_scale_reconstruction_conformallyFlat (N := N) hN (contDiff_cosmologicalFactor hA d)
    htau hmass h₁ h₂ x

end Cosmological

/-! ## The diamond form on a conformally flat chart -/

section Diamond

variable {d N : ℕ}

/-- **The two-species scale law inside a causal diamond of a conformally flat chart.** The diamond is
the same set as in the flat chart, because a conformal rescaling does not move the cones. -/
theorem twoSpecies_scale_reconstruction_conformallyFlat_diamond
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    {sigma : (Fin (d + 1) → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma)
    {tau : (Fin (d + 1) → ℝ) → ℝ} (htau : ContDiff ℝ ∞ tau)
    {massSq : ℝ} (hmass : massSq ≠ 0) (p q : Fin (d + 1) → ℝ)
    {other₁ other₂ : (Fin (d + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      W ⊆ kgDiamond d p q →
      SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert
        (((kgChart d).conformalRescale sigma hsigma).conformalPotential 0 massSq tau) u W →
        SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (d + 1) → ℝ) → ℝ) (W : Set (Fin (d + 1) → ℝ)), IsOpen W →
      W ⊆ kgDiamond d p q →
      SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert
        (((kgChart d).conformalRescale sigma hsigma).conformalPotential 0 0 tau) u W →
        SolvesPotentialWaveOn ((kgChart d).conformalRescale sigma hsigma).dalembert other₂ u W)
    {x : Fin (d + 1) → ℝ} (hx : x ∈ kgDiamond d p q) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * tau x) := by
  have hpot : ContDiff ℝ ∞
      (((kgChart d).conformalRescale sigma hsigma).conformalPotential 0 massSq tau) := by
    rw [conformalPotential_weight_zero]
    exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul htau))
  exact scale_reconstruction_on_region ((kgChart d).conformalRescale sigma hsigma) 0 htau hmass
    (isOpen_kgDiamond d p q)
    (openProbesOn_of_openProbes (isOpen_kgDiamond d p q)
      (regularOpenProbes_conformalRescale_kgChart (N := N) hN hsigma hpot).openProbes)
    h₁ h₂ hx

end Diamond

end GaloisForLFunctions.HTGeometry
