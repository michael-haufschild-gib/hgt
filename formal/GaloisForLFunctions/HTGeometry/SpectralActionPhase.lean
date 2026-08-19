/-
# The spectral action as a ray-constant measurable phase

The dephasing engine consumes a phase which is constant on rays, measurable on the whole space, and
analytic and nonconstant on a full-measure open cone.  The spectral action of a character supplies
one once the spectrum is labelled canonically: the increasing rearrangement of the eigenvalues is
continuous in the coefficients, so the action is continuous, and normalising the argument makes it
ray-constant.  The cone is the simple-spectrum part of the punctured unit ball, whose complement is
the zero set of the spectral discriminant and hence null.

Main results:
* `sortedSpectralAction`, `continuous_sortedSpectralAction` — the canonically labelled action.
* `spectralActionPhase` — its ray-constant extension, with `spectralActionPhase_smul`,
  `measurable_spectralActionPhase`, `spectralActionPhase_of_norm_one`.
* `simpleSpectrumCone`, `isOpen_simpleSpectrumCone`, `volume_ball_sdiff_simpleSpectrumCone` —
  **the full-measure open cone**.
* `tendsto_integral_exp_sortedSpectralAction_zero` — **angular dephasing for the spectral action**.
-/
import GaloisForLFunctions.HTGeometry.SortedSpectrumContinuity
import GaloisForLFunctions.HTGeometry.SphereAnalyticPushforward
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure

open Filter Topology Set MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The spectral action of a character, in the canonical increasing labelling of the spectrum. -/
def sortedSpectralAction {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (k : Fin D → ℝ) (θ : Fin N → ℝ) : ℝ :=
  ∑ j, k j * sortedTuple (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j

theorem continuous_spectralEnsembleMatrix (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    Continuous (fun θ : Fin N → ℝ => spectralEnsembleMatrix P θ) := by
  refine continuous_finsetSum _ fun a _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply a)).smul continuous_const

/-- **The canonically labelled spectral action is continuous.** -/
theorem continuous_sortedSpectralAction {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    Continuous (sortedSpectralAction hP k) := by
  have hsort : Continuous
      (fun θ : Fin N → ℝ => sortedTuple (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues) :=
    continuous_sortedTuple_eigenvalues (continuous_spectralEnsembleMatrix P)
      (fun θ => isHermitian_spectralEnsembleMatrix hP θ)
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp hsort)

section Phase

variable {m : ℕ}

/-- The ray-constant phase of a spectral action: its value at the normalised argument. -/
def spectralActionPhase {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ)
    (y : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  sortedSpectralAction hP k (fun a => ‖y‖⁻¹ * (WithLp.ofLp y) a)

/-- **The phase is constant on rays.** -/
theorem spectralActionPhase_smul {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) (r : ℝ) (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin (m + 1))) :
    spectralActionPhase hP k (r • y) = spectralActionPhase hP k y := by
  refine congrArg (sortedSpectralAction hP k) ?_
  funext a
  have hn : ‖r • y‖ = r * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hc : (WithLp.ofLp (r • y)) a = r * (WithLp.ofLp y) a := rfl
  rw [hn, hc, mul_inv, mul_comm (r⁻¹) (‖y‖⁻¹), mul_assoc, ← mul_assoc (r⁻¹) r,
    inv_mul_cancel₀ hr.ne', one_mul]

/-- The phase is measurable. -/
theorem measurable_spectralActionPhase {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    Measurable (spectralActionPhase hP k) := by
  refine (continuous_sortedSpectralAction hP k).measurable.comp ?_
  refine measurable_pi_lambda _ fun a => ?_
  exact (continuous_norm.measurable.inv).mul
    (((continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (m + 1) => ℝ))).measurable)

/-- On the unit sphere the phase is the spectral action itself. -/
theorem spectralActionPhase_of_norm_one {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ)
    {y : EuclideanSpace ℝ (Fin (m + 1))} (hy : ‖y‖ = 1) :
    spectralActionPhase hP k y = sortedSpectralAction hP k (WithLp.ofLp y) := by
  refine congrArg (sortedSpectralAction hP k) ?_
  funext a
  rw [hy, inv_one, one_mul]

/-- The simple-spectrum part of the punctured unit ball. -/
def simpleSpectrumCone (P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ) :
    Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {y | MvPolynomial.eval (WithLp.ofLp y) (spectralDiscriminantPoly P) ≠ 0} ∩
    (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 \ {0})

theorem isOpen_simpleSpectrumCone (P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ) :
    IsOpen (simpleSpectrumCone P) := by
  refine IsOpen.inter ?_ (Metric.isOpen_ball.sdiff isClosed_singleton)
  have hcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        MvPolynomial.eval (WithLp.ofLp y) (spectralDiscriminantPoly P)) :=
    (MvPolynomial.continuous_eval _).comp (PiLp.continuous_ofLp 2 _)
  exact isOpen_ne_fun hcont continuous_const

/-- **The complement of the simple-spectrum cone in the punctured ball is null.** -/
theorem volume_ball_sdiff_simpleSpectrumCone {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ}
    (hDisc : spectralDiscriminantPoly P ≠ 0) :
    volume ((Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 \ {0}) \ simpleSpectrumCone P)
      = 0 := by
  have hsub : ((Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 \ {0}) \ simpleSpectrumCone P)
      ⊆ {y : EuclideanSpace ℝ (Fin (m + 1)) |
          MvPolynomial.eval (WithLp.ofLp y) (spectralDiscriminantPoly P) = 0} := by
    rintro y ⟨hy, hny⟩
    by_contra hzero
    exact hny ⟨hzero, hy⟩
  refine measure_mono_null hsub ?_
  refine measure_eq_zero_of_preimage_eq_zero (euclCoord (m + 1)).toEquiv
    (measurePreserving_euclCoord_symm (m + 1)) ?_
  exact realMvPolynomial_zero_set_volume_fin (m + 1) (spectralDiscriminantPoly P) hDisc

/-- **Angular dephasing for the spectral action.**  On a family whose discriminant does not vanish
identically, and whose canonically labelled spectral action is analytic and nonconstant on every
open patch of the simple-spectrum cone, the oscillatory shell integral of the action against any
bounded measurable amplitude tends to zero. -/
theorem tendsto_integral_exp_sortedSpectralAction_zero
    {P : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hDisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ)
    (hana : AnalyticOnNhd ℝ (spectralActionPhase hP k) (simpleSpectrumCone P))
    (hnc : ∀ V : Set (EuclideanSpace ℝ (Fin (m + 1))), IsOpen V → V.Nonempty →
      V ⊆ simpleSpectrumCone P →
      ∃ p ∈ V, ∃ q ∈ V, spectralActionPhase hP k p ≠ spectralActionPhase hP k q)
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (m + 1)))) : ℝ) : ℂ) * Complex.I)
        ∂(volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) := by
  refine Filter.Tendsto.congr (fun t => ?_)
    (tendsto_integral_exp_sphere_phase_zero (measurable_spectralActionPhase hP k)
      (fun r hr y => spectralActionPhase_smul hP k r hr y)
      (isOpen_simpleSpectrumCone P) hana hnc
      (volume_ball_sdiff_simpleSpectrumCone hDisc) g hg hC0 hC)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [spectralActionPhase_of_norm_one hP k (mem_sphere_zero_iff_norm.mp x.2)]

end Phase

end

end GaloisForLFunctions.HTGeometry
