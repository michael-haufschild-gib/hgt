import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalScalarMetric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace RHTower.D4BMIngoingCoordinates
open GaloisForLFunctions.HTGeometry Filter Topology
noncomputable section

/-- Static-to-ingoing tortoise function on the real exterior. -/
def tortoise (r : ℝ) : ℝ := (Real.log (r-1)-Real.log (r+1))/2

/-- Static coordinates of an ingoing chart point. -/
def staticPoint (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0-tortoise (x 1), x 1, x 2, x 3]

/-- Actual first derivative of the tortoise function. -/
theorem tortoise_hasDerivAt (r : ℝ) (hr : 1 < r) :
    HasDerivAt tortoise ((r^(2 : ℕ)-1)⁻¹) r := by
  have hm : r-1 ≠ 0 := by linarith
  have hp : r+1 ≠ 0 := by linarith
  have hf : r^(2 : ℕ)-1 ≠ 0 := by nlinarith
  convert! (((hasDerivAt_id r).sub_const 1).log hm).sub
    (((hasDerivAt_id r).add_const 1).log hp) |>.div_const 2 using 1
  dsimp
  field_simp [hm, hp, hf]
  ring

/-- The real differential of the ingoing-to-static coordinate map. -/
def differential (r : ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi ![
    ContinuousLinearMap.proj 0-(r^(2 : ℕ)-1)⁻¹ • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

/-- The displayed triangular coordinate matrix is obtained by differentiation. -/
theorem staticPoint_hasFDerivAt (x : Fin 4 → ℝ) (hr : 1 < x 1) :
    HasFDerivAt staticPoint (differential (x 1)) x := by
  change HasFDerivAt (fun x => ![x 0-tortoise (x 1), x 1, x 2, x 3]) _ x
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · have ht := HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ)
      (f := fun z : Fin 4 → ℝ => z 1) x
      (tortoise_hasDerivAt (x 1) hr) (hasFDerivAt_apply 1 x)
    simpa [staticPoint, differential, Function.comp_def, Pi.sub_apply] using! (hasFDerivAt_apply 0 x).sub ht
  · exact hasFDerivAt_apply 1 x
  · exact hasFDerivAt_apply 2 x
  · exact hasFDerivAt_apply 3 x

/-- Complex matrix of the actual coordinate differential. -/
def jacobian (r : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,-(r^(2 : ℕ)-1)⁻¹,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]

/-- Complexification of the actual real differential agrees entrywise. -/
theorem differential_matrix (r : ℝ) (i j : Fin 4) :
    ((differential r (Pi.single j 1) i : ℝ) : ℂ) = jacobian r i j := by
  fin_cases i <;> fin_cases j <;> simp [differential, jacobian]

/-- Tensor components under the differentiated coordinate change. -/
def pullback (r : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (jacobian r).transpose * M * jacobian r

/-- The actual separated envelope written in inverse radius. -/
def compactEnvelope (s a : ℂ) (v : ℝ) (u : ℂ) : ℂ :=
  a*Complex.exp (s*((v : ℂ)+Complex.log (1+u)))

private theorem log_radial (r : ℝ) (hr : 1 < r) :
    Real.log (1-r⁻¹^(2 : ℕ)) = Real.log (r-1)+Real.log (r+1)-2*Real.log r := by
  have h0 : r ≠ 0 := by linarith
  have hm : r-1 ≠ 0 := by linarith
  have hp : r+1 ≠ 0 := by linarith
  rw [show 1-r⁻¹^(2 : ℕ) = (r-1)*(r+1)/r^(2 : ℕ) by field_simp; ring,
    Real.log_div (mul_ne_zero hm hp) (pow_ne_zero 2 h0), Real.log_mul hm hp,
    Real.log_pow]
  ring

/-- The original radial branch and actual time change give the regular envelope. -/
theorem envelope_staticPoint (s a : ℂ) (x : Fin 4 → ℝ) (hr : 1 < x 1) :
    D4BMFundamentalScalarMetric.envelope s a (staticPoint x) =
      compactEnvelope s a (x 0) (x 1 : ℂ)⁻¹ := by
  have h0 : x 1 ≠ 0 := by linarith
  have hp : x 1+1 ≠ 0 := by linarith
  have hz : 0 < 1-(x 1)⁻¹^(2 : ℕ) := by
    have h : (x 1)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hr
    have h' : 0 < (x 1)⁻¹ := inv_pos.mpr (by linarith)
    nlinarith
  have hu : 0 < 1+(x 1)⁻¹ := by positivity
  rw [D4BMFundamentalScalarMetric.envelope_eq_exp]
  dsimp [staticPoint, D4BMMetricReconstruction.bmCoordinate, compactEnvelope]
  rw [show 1-(x 1 : ℂ)⁻¹^(2 : ℕ) = ((1-(x 1)⁻¹^(2 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
    show 1+(x 1 : ℂ)⁻¹ = ((1+(x 1)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hz.le, ← Complex.ofReal_log hu.le, log_radial _ hr,
    show 1+(x 1)⁻¹ = (x 1+1)/(x 1) by field_simp,
    Real.log_div hp h0]
  congr 2
  dsimp [tortoise]
  push_cast
  ring

/-- Holomorphic extension in inverse radius at every point of the logarithm chart. -/
theorem compactEnvelope_contDiffAt (s a : ℂ) (v : ℝ) (u : ℂ)
    (hu : 1+u ∈ Complex.slitPlane) (m : WithTop ℕ∞) :
    ContDiffAt ℂ m (compactEnvelope s a v) u := by
  exact contDiffAt_const.mul (Complex.contDiff_exp.contDiffAt.comp u
    (contDiffAt_const.mul (contDiffAt_const.add
      ((Complex.contDiffAt_log hu).comp u (contDiffAt_const.add contDiffAt_id)))))

/-- At the physical horizon the envelope has a finite, fixed value. -/
theorem compactEnvelope_horizon (s a : ℂ) (v : ℝ) :
    Tendsto (compactEnvelope s a v) (nhds 1)
      (nhds (a*Complex.exp (s*((v : ℂ)+Complex.log 2)))) := by
  simpa [compactEnvelope, show (1 : ℂ)+1=2 by norm_num] using
    (compactEnvelope_contDiffAt s a v 1 (by norm_num [Complex.mem_slitPlane_iff]) 0).continuousAt.tendsto

/-- At the asymptotic boundary the radial part tends to one. -/
theorem compactEnvelope_boundary (s a : ℂ) (v : ℝ) :
    Tendsto (compactEnvelope s a v) (nhds 0) (nhds (a*Complex.exp (s*(v : ℂ)))) := by
  simpa [compactEnvelope] using
    (compactEnvelope_contDiffAt s a v 0 (by norm_num [Complex.mem_slitPlane_iff]) 0).continuousAt.tendsto

end
end RHTower.D4BMIngoingCoordinates
