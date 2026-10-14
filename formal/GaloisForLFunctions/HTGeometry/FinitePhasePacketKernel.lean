import GaloisForLFunctions.HTGeometry.FinitePhasePacket

/-! # The exact Hermitian kernel of coherent phase energy -/

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory
noncomputable section

theorem conj_paperRotationPhase (t : ℝ) :
    starRingEnd ℂ (paperRotationPhase t) = paperRotationPhase (-t) := by
  change starRingEnd ℂ (Complex.exp ((t : ℂ) * Complex.I)) =
    Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
  rw [← Complex.exp_conj]
  simp

theorem integral_paperRotationPhase (t : ℝ) :
    (∫ x in (0 : ℝ)..1, paperRotationPhase (t * x)) =
      forwardWindowKernel ((t : ℂ) * Complex.I) := by
  have he : (fun x : ℝ => paperRotationPhase (t * x)) =
      fun x : ℝ => Complex.exp (((t : ℂ) * Complex.I) * x) := by
    funext x
    change Complex.exp _ = Complex.exp _
    congr 1
    push_cast
    ring
  rw [he]
  simpa [forwardModeAverage] using forwardModeAverage_eq_kernel 1 ((t : ℂ) * Complex.I) one_ne_zero

theorem finitePhasePacket_norm_sq_expansion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (x : ℝ) :
    ((‖finitePhasePacket s a ω x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ (a i) * a j) *
        paperRotationPhase ((ω j - ω i) * x) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, finitePhasePacket,
    map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, conj_paperRotationPhase]
  have hp : paperRotationPhase (-(ω i * x)) * paperRotationPhase (ω j * x) =
      paperRotationPhase ((ω j - ω i) * x) := by
    rw [← paperRotationPhase_add]
    congr 1
    ring
  calc
    _ = (starRingEnd ℂ (a i) * a j) *
        (paperRotationPhase (-(ω i * x)) * paperRotationPhase (ω j * x)) := by ring
    _ = _ := by rw [hp]

theorem finitePhaseEnergy_eq_kernel {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) :
    (finitePhaseEnergy s a ω : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (starRingEnd ℂ (a i) * a j) *
        forwardWindowKernel (((ω j - ω i : ℝ) : ℂ) * Complex.I) := by
  have hc (i j : ι) : Continuous (fun x : ℝ =>
      (starRingEnd ℂ (a i) * a j) * paperRotationPhase ((ω j - ω i) * x)) :=
    continuous_const.mul
      (paperRotationPhase_lipschitz.continuous.comp (continuous_const.mul continuous_id))
  rw [finitePhaseEnergy, ← intervalIntegral.integral_ofReal]
  simp_rw [finitePhasePacket_norm_sq_expansion]
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => (continuous_finsetSum s (fun j _ => hc i j)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hc i j).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul, integral_paperRotationPhase]

end
end GaloisForLFunctions.HTGeometry
