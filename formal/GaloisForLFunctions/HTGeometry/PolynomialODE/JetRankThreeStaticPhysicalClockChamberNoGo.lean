import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSourcePositiveSeamNoGo
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth

/-!
# Static physical-clock chamber does not force theta D1

The exact reduced modular ray `Z=-t`, `R=5/2`, `S=-t` enters every strict local chamber known
to contain the physical theta orbit: negative drift, positive gap and transverse shear, strict
diagonal source cone, and projective clock `0 < -Z < 3/10`.  Nevertheless the universal
rank-three reflected D1 polynomial stays negative for sufficiently small positive `t`, by
continuity from the rational negative seam state.

Therefore no static semialgebraic argument using only these established chamber inequalities can
close the finite TCD/S6F D1 gate.  A successful proof must use actual orbit incidence, a stronger
dynamical invariant, or theta-specific singular-face transport.
-/

open Complex Real Set Filter Topology

namespace HTGeometry

noncomputable section

/-- Lyapunov image of the reduced modular ray
`Z = -t`, `R = 5/2`, `S = -t`. -/
def modularThetaLyapunovStrictClockRay (t : ℝ) :
    ModularThetaLyapunovState → ℂ
  | .S => (-t : ℝ)
  | .A => ((25 / 4 : ℝ) * (1 - t ^ (2 : ℕ)) : ℝ)
  | .W => ((11 / 6 : ℝ) * t : ℝ)

/-- Complete static chamber presently known on the missing physical interval, restricted to the
strict clock ray. -/
def modularThetaLyapunovStrictClockChamber (t : ℝ) : Prop :=
  0 < t ∧ t < 3 / 10 ∧
    (modularThetaLyapunovStrictClockRay t .S).re < 0 ∧
    0 < (modularThetaLyapunovStrictClockRay t .A).re ∧
    0 < (modularThetaLyapunovStrictClockRay t .W).re ∧
    18 <
      2 * (modularThetaLyapunovStrictClockRay t .S).re ^ (2 : ℕ) +
        3 * (modularThetaLyapunovStrictClockRay t .A).re ∧
    -(1 / 3 : ℝ) * (modularThetaLyapunovStrictClockRay t .S).re <
      (modularThetaLyapunovStrictClockRay t .W).re

/-- The ray is the exact Lyapunov image of reduced modular data
`Z=-t`, `R=5/2`, `S=-t`. -/
theorem modularThetaLyapunovStrictClockRay_reducedCoordinate_eq (t : ℝ) :
    (modularThetaLyapunovStrictClockRay t .S).re = -t ∧
    (modularThetaLyapunovStrictClockRay t .A).re =
      (5 / 2 : ℝ) ^ (2 : ℕ) * (1 - (-t) ^ (2 : ℕ)) ∧
    (modularThetaLyapunovStrictClockRay t .W).re =
      (2 / 3 : ℝ) * (-t) - (5 / 2 : ℝ) * (-t) := by
  constructor
  · rfl
  constructor
  · change (25 / 4 : ℝ) * (1 - t ^ (2 : ℕ)) =
      (5 / 2 : ℝ) ^ (2 : ℕ) * (1 - (-t) ^ (2 : ℕ))
    ring
  · change (11 / 6 : ℝ) * t =
      (2 / 3 : ℝ) * (-t) - (5 / 2 : ℝ) * (-t)
    ring

@[simp] theorem modularThetaLyapunovStrictClockRay_zero :
    modularThetaLyapunovStrictClockRay 0 =
      modularThetaLyapunovSeamState (5 / 2) := by
  funext i
  cases i <;>
    norm_num [modularThetaLyapunovStrictClockRay,
      modularThetaLyapunovSeamState]

private theorem continuous_modularThetaLyapunovStrictClockRay :
    Continuous modularThetaLyapunovStrictClockRay := by
  apply continuous_pi
  intro i
  cases i <;>
    simp only [modularThetaLyapunovStrictClockRay]
  · fun_prop
  · fun_prop
  · fun_prop

private theorem continuous_modularThetaLyapunovStrictClockRay_D1 :
    Continuous (fun t : ℝ =>
      (MvPolynomial.eval (modularThetaLyapunovStrictClockRay t)
        modularThetaLyapunovReflectedEighthPolynomial).re) := by
  exact Complex.continuous_re.comp
    ((GaloisForLFunctions.HTGeometry.contDiff_mvPolynomial_eval
      modularThetaLyapunovReflectedEighthPolynomial).continuous.comp
        continuous_modularThetaLyapunovStrictClockRay)

/-- Negative D1 occupies a full right neighborhood of the rational seam along the strict reduced
clock ray.  This is the robust positive survivor exposed by the static-chamber obstruction. -/
theorem exists_rightNeighborhood_modularThetaLyapunov_strictClockChamber_D1_neg :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      modularThetaLyapunovStrictClockChamber t ∧
      (MvPolynomial.eval (modularThetaLyapunovStrictClockRay t)
        modularThetaLyapunovReflectedEighthPolynomial).re < 0 := by
  let D : ℝ → ℝ := fun t =>
    (MvPolynomial.eval (modularThetaLyapunovStrictClockRay t)
      modularThetaLyapunovReflectedEighthPolynomial).re
  have hD0 : D 0 < 0 := by
    dsimp only [D]
    rw [modularThetaLyapunovStrictClockRay_zero,
      eval_modularThetaLyapunovReflectedEighthPolynomial_seam]
    norm_num
    exact modularThetaReflectedEighthSeamPolynomial_twentyFiveFourths_re_neg
  have hDnhds : D ⁻¹' Iio 0 ∈ 𝓝 0 := by
    exact continuous_modularThetaLyapunovStrictClockRay_D1.continuousAt
      (Iio_mem_nhds hD0)
  rcases Metric.mem_nhds_iff.1 hDnhds with ⟨δ, hδ, hball⟩
  let ε : ℝ := min δ (1 / 10)
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hδ (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro t ht0 htε
  have htδ : t < δ := htε.trans_le (min_le_left _ _)
  have htupper : t < 1 / 10 := htε.trans_le (min_le_right _ _)
  have htD : D t < 0 := by
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_of_pos ht0] using htδ
    exact hball htball
  refine ⟨?_, htD⟩
  unfold modularThetaLyapunovStrictClockChamber
  refine ⟨ht0, by nlinarith, ?_, ?_, ?_, ?_, ?_⟩
  · simp [modularThetaLyapunovStrictClockRay, ht0]
  · simp only [modularThetaLyapunovStrictClockRay, Complex.ofReal_re]
    nlinarith [sq_nonneg t]
  · simp [modularThetaLyapunovStrictClockRay, ht0]
  · simp only [modularThetaLyapunovStrictClockRay, Complex.ofReal_re]
    nlinarith [sq_nonneg t]
  · simp only [modularThetaLyapunovStrictClockRay, Complex.ofReal_re]
    nlinarith

/-- The negative seam D1 chamber penetrates the complete strict static chamber currently known
to contain the physical theta orbit.  Equivalently, strict drift/gap/shear/source inequalities
plus the projective clock cap do not force rank-three D1 positivity. -/
theorem exists_modularThetaLyapunov_strictClockChamber_D1_neg :
    ∃ t : ℝ,
      modularThetaLyapunovStrictClockChamber t ∧
      (MvPolynomial.eval (modularThetaLyapunovStrictClockRay t)
        modularThetaLyapunovReflectedEighthPolynomial).re < 0 := by
  obtain ⟨ε, hε, hall⟩ :=
    exists_rightNeighborhood_modularThetaLyapunov_strictClockChamber_D1_neg
  refine ⟨ε / 2, hall (ε / 2) (by positivity) ?_⟩
  linarith

/-- **Static physical-clock no-go.**  The complete strict local chamber and projective clock cap
do not imply positivity of universal rank-three theta D1. -/
theorem modularThetaLyapunov_strictClockChamber_not_sufficient_for_D1 :
    ¬ ∀ t : ℝ, modularThetaLyapunovStrictClockChamber t →
      0 < (MvPolynomial.eval (modularThetaLyapunovStrictClockRay t)
        modularThetaLyapunovReflectedEighthPolynomial).re := by
  intro h
  obtain ⟨t, ht, hneg⟩ :=
    exists_modularThetaLyapunov_strictClockChamber_D1_neg
  have hpos := h t ht
  linarith

end

end HTGeometry
