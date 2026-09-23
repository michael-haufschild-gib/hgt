import GaloisForLFunctions.HTGeometry.QuantumNullPrincipalAngle
import GaloisForLFunctions.HTGeometry.QuantumBilinearNullActivation

/-!
# Spectral-rank and relative-velocity diagnostics for quantum null spaces

Two diagnostics from arXiv:2609.07645 are realized on the corpus's exact rotating
rank-one information model. Normalized spectral rank remains one while explicit
eigenvectors rotate. In contrast, squared relative velocity change on the normalized
qubit curve is `4 sin((t-s)/2)^(2 : ℕ)`.
-/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Paper's normalized spectral-rank statistic with a selected leading eigenvalue. -/
def normalizedSpectralRank
    {ι : Type*} [Fintype ι] (lambda : ι → ℝ) (leading : ι) : ℝ :=
  ∑ i, |lambda i / lambda leading|

theorem normalizedSpectralRank_nonnegative
    {ι : Type*} [Fintype ι] (lambda : ι → ℝ) (leading : ι) :
    0 ≤ normalizedSpectralRank lambda leading := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

def anchoredRankOneSpectrum
    {ι : Type*} [DecidableEq ι] (leading : ι) (a : ℝ) : ι → ℝ :=
  fun i => if i = leading then a else 0

/-- Every nonzero anchored rank-one spectrum has normalized spectral rank one. -/
theorem normalizedSpectralRank_anchoredRankOne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (leading : ι) (a : ℝˣ) :
    normalizedSpectralRank (anchoredRankOneSpectrum leading (a : ℝ)) leading = 1 := by
  unfold normalizedSpectralRank anchoredRankOneSpectrum
  rw [Finset.sum_eq_single leading]
  · simp [Units.ne_zero a]
  · intro i hi hne
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ leading)).elim

/-- Explicit constant spectrum of the rotating information projector. -/
def rotatingInformationEigenvalues : Fin 2 → ℝ := ![1, 0]

theorem rotatingInformation_normalizedSpectralRank :
    normalizedSpectralRank rotatingInformationEigenvalues 0 = 1 := by
  simp [normalizedSpectralRank, rotatingInformationEigenvalues, Fin.sum_univ_two]

def rotatingVisibleDirection (t : ℝ) : Fin 2 → ℝ := ![Real.cos t, Real.sin t]

/-- The rotating visible direction is the unit-eigenvalue eigenvector. -/
theorem rotatingInformation_mulVec_visible (t : ℝ) :
    (HTGeometry.rotatingInformation t).mulVec (rotatingVisibleDirection t) =
      rotatingVisibleDirection t := by
  ext i
  fin_cases i
  · simp [HTGeometry.rotatingInformation, rotatingVisibleDirection, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.gram_apply, RCLike.inner_apply]
    rw [show Real.cos t * Real.cos t * Real.cos t +
        Real.sin t * Real.cos t * Real.sin t =
      Real.cos t * (Real.cos t ^ 2 + Real.sin t ^ 2) by ring,
      Real.cos_sq_add_sin_sq]
    ring
  · simp [HTGeometry.rotatingInformation, rotatingVisibleDirection, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.gram_apply, RCLike.inner_apply]
    rw [show Real.cos t * Real.sin t * Real.cos t +
        Real.sin t * Real.sin t * Real.sin t =
      Real.sin t * (Real.cos t ^ 2 + Real.sin t ^ 2) by ring,
      Real.cos_sq_add_sin_sq]
    ring

/-- The rotating null direction is the zero-eigenvalue eigenvector. -/
theorem rotatingInformation_mulVec_null (t : ℝ) :
    (HTGeometry.rotatingInformation t).mulVec (HTGeometry.rotatingNullDirection t) = 0 := by
  ext i
  fin_cases i <;>
    simp [HTGeometry.rotatingInformation, HTGeometry.rotatingNullDirection, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.gram_apply, RCLike.inner_apply] <;> ring

/-- Relative finite-difference change used to diagnose velocity inflation. -/
def relativeVelocityChange
    {E : Type*} [NormedAddCommGroup E] (new old : E) : ℝ := ‖new - old‖ / ‖new‖

theorem qgtQubitTangent_inner (s t : ℝ) :
    inner ℂ (HTGeometry.qgtQubitTangent s 1) (HTGeometry.qgtQubitTangent t 1) =
      (Real.cos (t - s) : ℂ) := by
  unfold HTGeometry.qgtQubitTangent
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.inner_apply, Complex.conj_ofReal]
  norm_cast
  norm_num
  rw [Real.cos_sub]
  ring

/-- Exact geometric inflation of finite-difference velocity along the qubit curve. -/
theorem qgtQubitTangent_relativeVelocityChange_sq (s t : ℝ) :
    relativeVelocityChange (HTGeometry.qgtQubitTangent t 1)
        (HTGeometry.qgtQubitTangent s 1) ^ 2 =
      4 * Real.sin ((t - s) / 2) ^ 2 := by
  unfold relativeVelocityChange
  rw [div_pow, norm_sub_sq (𝕜 := ℂ),
    HTGeometry.qgtQubitTangent_norm_sq, HTGeometry.qgtQubitTangent_norm_sq,
    qgtQubitTangent_inner]
  simp only [RCLike.re_to_complex, Complex.ofReal_re, one_pow, div_one]
  have hcos : Real.cos (s - t) = Real.cos (t - s) := by
    rw [show s - t = -(t - s) by ring, Real.cos_neg]
  rw [hcos]
  have htrig : 1 - 2 * Real.cos (t - s) + 1 =
      4 * Real.sin ((t - s) / 2) ^ 2 := by
    conv_lhs => rw [show t - s = 2 * ((t - s) / 2) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq ((t - s) / 2)]
  exact htrig

end
end GaloisForLFunctions.HTGeometry
