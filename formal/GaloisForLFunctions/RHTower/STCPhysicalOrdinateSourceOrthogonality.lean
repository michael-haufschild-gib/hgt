import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHermitianGram
import GaloisForLFunctions.RHTower.DeningerInvZetaPole

/-!
# Physical-ordinate orthogonality of the literal signed squarefree source

The unitary phase `gamma * log n` is unscaled. Distinct fixed physical ordinates
have asymptotically orthogonal normalized Möbius source vectors at the Euler
boundary, since their squarefree partition overlap is regular away from the
zeta pole while the normalizing partition diverges. This is the arithmetic
input to the paper-level STC all-height transport singularity theorem.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

private theorem squarefreePartition_continuousAt_offPole
    {z : ℂ} (hz : z ≠ 1) (h2 : 1 < (2 * z).re) :
    ContinuousAt GaloisForLFunctions.squarefreePartition z := by
  have h2one : 2 * z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, one_re] at hre
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, one_re] at h2
    linarith
  have hz2 : riemannZeta (2 * z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re h2
  unfold GaloisForLFunctions.squarefreePartition
  exact (differentiableAt_riemannZeta hz).continuousAt.div
    ((differentiableAt_riemannZeta h2one).continuousAt.comp
      (by fun_prop : ContinuousAt (fun w : ℂ => 2 * w) z)) hz2

private theorem squarefreePartition_inv_tendsto_zero :
    Tendsto (fun sigma : ℝ =>
      (GaloisForLFunctions.squarefreePartition (sigma : ℂ))⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hpath : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with sigma hs
      change (sigma : ℂ) ≠ 1
      exact_mod_cast (ne_of_gt hs : sigma ≠ 1)
  have hzero := deningerInvZeta_tendsto_zero.comp hpath
  have htwo : Tendsto (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) := by
    have hpath2 : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
      have hc : ContinuousAt (fun sigma : ℝ => 2 * (sigma : ℂ)) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (differentiableAt_riemannZeta
      (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp hpath2
  have h := htwo.mul hzero
  convert h using 1
  · funext sigma
    simp only [Function.comp_apply, GaloisForLFunctions.squarefreePartition,
      div_eq_mul_inv, mul_inv_rev, inv_inv]
  · simp

theorem squarefreePartition_fixedPhysicalPhase_tendsto_zero
    {omega : ℝ} (homega : omega ≠ 0) :
    Tendsto (fun sigma : ℝ =>
      GaloisForLFunctions.squarefreePartition
          ((sigma : ℂ) + (omega : ℂ) * I) /
        GaloisForLFunctions.squarefreePartition (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  let z : ℂ := 1 + (omega : ℂ) * I
  have hz : z ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [z] at him
    exact homega him
  have h2 : 1 < (2 * z).re := by
    simp [z]
  have hpath : Tendsto (fun sigma : ℝ =>
      (sigma : ℂ) + (omega : ℂ) * I)
      (𝓝[>] (1 : ℝ)) (𝓝 z) := by
    have hc : ContinuousAt (fun sigma : ℝ =>
        (sigma : ℂ) + (omega : ℂ) * I) 1 := by fun_prop
    simpa [z] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hnum :=
    (squarefreePartition_continuousAt_offPole hz h2).tendsto.comp hpath
  have h := hnum.mul squarefreePartition_inv_tendsto_zero
  convert h using 1
  · funext sigma
    simp only [Function.comp_apply, div_eq_mul_inv]
  · simp

/-- Signed squarefree source with one unscaled physical logarithmic ordinate. -/
def physicalOrdinateMobiusSource (sigma gamma : ℝ) (hsigma : 1 < sigma) :
    lp (fun _ : ℕ => ℂ) 2 :=
  infiniteMobiusCriticalComplexDampedSignedWeightLp sigma
    (((gamma / (sigma - 1) : ℝ) : ℂ) * I) hsigma
      (by simp [Complex.mul_re, Complex.div_im])

theorem physicalOrdinateMobiusSource_inner
    (sigma gamma delta : ℝ) (hsigma : 1 < sigma) :
    inner ℂ (physicalOrdinateMobiusSource sigma gamma hsigma)
      (physicalOrdinateMobiusSource sigma delta hsigma) =
      GaloisForLFunctions.squarefreePartition
        ((sigma : ℂ) + ((delta - gamma : ℝ) : ℂ) * I) /
      GaloisForLFunctions.squarefreePartition (sigma : ℂ) := by
  rw [physicalOrdinateMobiusSource, physicalOrdinateMobiusSource,
    inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap
      hsigma (by simp [Complex.mul_re, Complex.div_im])
        (by simp [Complex.mul_re, Complex.div_im])]
  unfold mobiusCriticalComplexPhaseKernel
    GaloisForLFunctions.squarefreeBoundaryOverlap
  congr 1
  congr 1
  have heps : (sigma - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hsigma.ne'
  have hepsC : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr heps
  have hden : -1 + (sigma : ℂ) ≠ 0 := by
    have heq : -1 + (sigma : ℂ) = ((sigma - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    exact hepsC
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  field_simp [heps, hepsC, hden]
  have hcancel : (-1 + (sigma : ℂ)) * (-1 + (sigma : ℂ))⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  linear_combination (I * (delta : ℂ) - I * (gamma : ℂ)) * hcancel

/-- Distinct fixed physical ordinates become orthogonal at the Euler boundary. -/
theorem physicalOrdinateMobiusSource_offDiagonal_tendsto_zero
    {gamma delta : ℝ} (hgammaDelta : gamma ≠ delta) :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        inner ℂ (physicalOrdinateMobiusSource sigma gamma hsigma)
          (physicalOrdinateMobiusSource sigma delta hsigma)
      else 0)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have homega : delta - gamma ≠ 0 := sub_ne_zero.mpr hgammaDelta.symm
  have h := squarefreePartition_fixedPhysicalPhase_tendsto_zero homega
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hs : 1 < sigma := hsigma
  simp [hs, physicalOrdinateMobiusSource_inner]

end
end RHTower
