import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomGaussianHorizon
import GaloisForLFunctions.CompletedArithmeticForms.InverseTraceStability

/-!
# Explicit mixed-head horizons for the first theta atom

The inverse trace of each Gaussian head converts the all-order source error into
a relative quadratic estimate. Exact parity and source congruences give an explicit
lower boundary for the least failing full signed Hankel dimension.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- The shifted Gaussian comparison retains every mixed moment. -/
def gaussianShiftedHead (N s : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  finiteHankelMatrix (fun k => gaussianMoment (k + s)) N

private theorem gaussianMoment_shiftedModel (s k : ℕ) :
    gaussianMoment (k + s) =
      scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) k := by
  rw [Nat.add_comm k s]
  simp only [gaussianMoment, scaledGammaMoment, pow_add, gammaShapeMoment_add]
  rw [add_comm (1 / 2 : ℝ) (s : ℝ)]
  ring

theorem gaussianShiftedHead_posDef (N s : ℕ) : (gaussianShiftedHead N s).PosDef := by
  have hg : 0 < gaussianMoment s :=
    mul_pos (pow_pos (by positivity) s) (gammaShapeMoment_pos (by positivity) s)
  simpa only [gaussianShiftedHead, gaussianMoment_shiftedModel] using
    scaledGammaHankel_posDef hg (show (0 : ℝ) < 16 by positivity)
      (show (0 : ℝ) < (s : ℝ) + 1 / 2 by positivity) N

/-- The determinant fixes the denominator of the finite Gaussian inverse. -/
theorem det_gaussianShiftedHead (N s : ℕ) :
    (gaussianShiftedHead N s).det =
      ∏ i : Fin N, gaussianMoment s * 16 ^ (2 * i.val) *
        (i.val.factorial : ℝ) * gammaShapeMoment ((s : ℝ) + 1 / 2) i.val := by
  simpa only [gaussianShiftedHead, gaussianMoment_shiftedModel] using
    det_scaledGammaHankel (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) N

/-- Explicit finite inverse cost for the complete shifted Gaussian head. -/
def gaussianInverseTrace (N s : ℕ) : ℝ := (gaussianShiftedHead N s)⁻¹.trace

theorem gaussianInverseTrace_nonneg (N s : ℕ) : 0 ≤ gaussianInverseTrace N s := by
  unfold gaussianInverseTrace Matrix.trace
  exact sum_nonneg fun i _ => (gaussianShiftedHead_posDef N s).inv.posSemidef.diag_nonneg

/-- The inverse cost is a finite cofactor sum over the exact positive Gamma determinant. -/
theorem gaussianInverseTrace_eq_cofactor_div (N s : ℕ) :
    gaussianInverseTrace N s = (gaussianShiftedHead N s).adjugate.trace /
      (∏ i : Fin N, gaussianMoment s * 16 ^ (2 * i.val) *
        (i.val.factorial : ℝ) * gammaShapeMoment ((s : ℝ) + 1 / 2) i.val) := by
  rw [gaussianInverseTrace, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.trace_smul,
    smul_eq_mul, det_gaussianShiftedHead]
  ring

/-- Uniform numerator of the relative source error at a specified rank and shift. -/
def firstAtomMixedErrorNumerator (N s : ℕ) : ℝ :=
  (N : ℝ) * gaussianInverseTrace N s * ((2 * (s + 2 * N)).factorial : ℝ) *
    firstAtomGaussianErrorConstant

theorem firstAtomMixedErrorNumerator_nonneg (N s : ℕ) :
    0 ≤ firstAtomMixedErrorNumerator N s := by
  have hT := gaussianInverseTrace_nonneg N s
  have hD := firstAtomGaussianErrorConstant_pos
  unfold firstAtomMixedErrorNumerator
  positivity

/-- The Gaussian inverse turns the source approximation into a complete relative form estimate. -/
theorem firstAtomBalancedHead_relative_error_le {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (N s : ℕ) (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (firstAtomBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v| ≤
      (firstAtomMixedErrorNumerator N s / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  let ε := ((2 * (s + 2 * N)).factorial : ℝ) * firstAtomGaussianErrorConstant /
    thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hε : 0 ≤ ε := by
    have hD := firstAtomGaussianErrorConstant_pos
    dsimp [ε]
    positivity
  have he (i j : Fin N) :
      |finiteHankelMatrix (firstAtomBalancedMoment s x) N i j - gaussianShiftedHead N s i j| ≤ ε := by
    have hf : ((2 * (i.val + j.val + s)).factorial : ℝ) ≤
        ((2 * (s + 2 * N)).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (show 2 * (i.val + j.val + s) ≤ 2 * (s + 2 * N) by omega)
    exact (firstAtomScaledEvenJet_gaussian_error_le hq (i.val + j.val + s)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hf firstAtomGaussianErrorConstant_pos.le) hqp.le)
  have h := relative_error_le_inverseTrace (gaussianShiftedHead_posDef N s) hε he v
  convert h using 1
  dsimp [firstAtomMixedErrorNumerator, gaussianInverseTrace, ε]
  ring

/-- Paying the explicit rank cost leaves half of the entire Gaussian comparison form. -/
theorem firstAtomBalancedHead_half_posDef_of_scale {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (N s : ℕ)
    (hscale : 2 * firstAtomMixedErrorNumerator N s < thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (firstAtomBalancedMoment s x) N -
      (1 / 2 : ℝ) • gaussianShiftedHead N s).PosDef := by
  have hG := gaussianShiftedHead_posDef N s
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [gaussianShiftedHead, finiteHankelMatrix, Nat.add_comm]
  · intro v hv
    rw [star_trivial]
    have hg : 0 < v ⬝ᵥ gaussianShiftedHead N s *ᵥ v := by
      simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 (x := v) hv
    have he := (abs_le.mp (firstAtomBalancedHead_relative_error_le hq N s v)).1
    have hc : firstAtomMixedErrorNumerator N s / thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
      apply (div_lt_iff₀ hqp).mpr
      linarith only [hscale]
    have hs : v ⬝ᵥ (finiteHankelMatrix (firstAtomBalancedMoment s x) N -
        (1 / 2 : ℝ) • gaussianShiftedHead N s) *ᵥ v =
      v ⬝ᵥ (finiteHankelMatrix (firstAtomBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v +
        (1 / 2) * (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
      simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      ring
    rw [hs]
    nlinarith only [he, mul_pos (sub_pos.mpr hc) hg]

private theorem firstAtomBalancedHead_posDef_of_scale {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (N s : ℕ)
    (hscale : 2 * firstAtomMixedErrorNumerator N s < thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (firstAtomBalancedMoment s x) N).PosDef := by
  have hhalf := firstAtomBalancedHead_half_posDef_of_scale hq N s hscale
  have hG := (gaussianShiftedHead_posDef N s).smul (by norm_num : (0 : ℝ) < 1 / 2)
  have hsum := hhalf.add hG
  simpa only [sub_add_cancel] using hsum

/-- Source mass and physical scale transfer the quantified balanced estimate without loss of sign. -/
theorem firstAtomShiftedHead_posDef_of_scale {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (N s : ℕ)
    (hscale : 2 * firstAtomMixedErrorNumerator N s < thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix
      (fun k => (-1 : ℝ) ^ (k + s) * thetaCuspFirstAtomReflectionJet (2 * (k + s)) x) N).PosDef := by
  have hA := firstAtomBalancedHead_posDef_of_scale hq N s hscale
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => f * q ^ i.val)
  have hqp : 0 < q := by dsimp [q]; linarith only [hq]
  have hf : f ≠ 0 := by
    intro h
    have hp := firstAtom_mass_pos hq
    change 0 < f ^ 2 at hp
    rw [h, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hp
    exact lt_irrefl 0 hp
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hqp.ne')) hi
  have he : finiteHankelMatrix
      (fun k => (-1 : ℝ) ^ (k + s) * thetaCuspFirstAtomReflectionJet (2 * (k + s)) x) N =
      q ^ s • (Dᴴ * finiteHankelMatrix (firstAtomBalancedMoment s x) N * D) := by
    ext i j
    simp only [D, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, finiteHankelMatrix, firstAtomBalancedMoment,
      thetaCuspFirstAtomScaledEvenJet]
    change _ = q ^ s * (f * q ^ i.val *
      (_ / (f ^ 2 * q ^ (i.val + j.val + s))) * (f * q ^ j.val))
    rw [pow_add, pow_add]
    field_simp [hf, hqp.ne']
    ring
  rw [he]
  exact (hA.conjTranspose_mul_mul_same hD).smul (pow_pos hqp s)

/-- Both parity costs, together with the physical domain of the analytic comparison. -/
def firstAtomMixedScale (N : ℕ) : ℝ :=
  3 + 2 * (firstAtomMixedErrorNumerator ((N + 1) / 2) 0 +
    firstAtomMixedErrorNumerator (N / 2) 1)

theorem firstAtomMixedScale_ge_three (N : ℕ) : 3 ≤ firstAtomMixedScale N := by
  unfold firstAtomMixedScale
  linarith only [firstAtomMixedErrorNumerator_nonneg ((N + 1) / 2) 0,
    firstAtomMixedErrorNumerator_nonneg (N / 2) 1]

/-- Every full signed head has an explicit physical-scale positivity horizon. -/
theorem firstAtomSignedHead_posDef_of_scale (N : ℕ) {x : ℝ}
    (hscale : firstAtomMixedScale N ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (firstAtomSignedSequence x) N).PosDef := by
  have hq := (firstAtomMixedScale_ge_three N).trans hscale
  have he : 2 * firstAtomMixedErrorNumerator ((N + 1) / 2) 0 <
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold firstAtomMixedScale at hscale
    linarith only [hscale, firstAtomMixedErrorNumerator_nonneg (N / 2) 1]
  have ho : 2 * firstAtomMixedErrorNumerator (N / 2) 1 <
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold firstAtomMixedScale at hscale
    linarith only [hscale, firstAtomMixedErrorNumerator_nonneg ((N + 1) / 2) 0]
  rw [firstAtomSignedSequence_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨firstAtomShiftedHead_posDef_of_scale hq ((N + 1) / 2) 0 he,
    firstAtomShiftedHead_posDef_of_scale hq (N / 2) 1 ho⟩

/-- The explicit full-head reserve bounds the first failing mixed dimension from below. -/
theorem firstAtomFailureRank_gt_of_scale (N : ℕ) {x : ℝ}
    (hscale : firstAtomMixedScale N ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    N < firstAtomFailureRank x := by
  have hA := (firstAtomSignedHead_posDef_of_scale N hscale).posSemidef
  by_contra h
  have hle : firstAtomFailureRank x ≤ N := le_of_not_gt h
  let e : Fin (firstAtomFailureRank x) → Fin N := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
  have hsub := hA.submatrix e
  have he : (finiteHankelMatrix (firstAtomSignedSequence x) N).submatrix e e =
      finiteHankelMatrix (firstAtomSignedSequence x) (firstAtomFailureRank x) := by
    ext i j
    rfl
  rw [he] at hsub
  exact firstAtomFailureRank_spec x hsub

/-- An explicit center for the full mixed signed head. -/
def firstAtomMixedHorizon (N : ℕ) : ℝ :=
  max 0 (Real.log (firstAtomMixedScale N / Real.pi) / 2)

/-- The mixed-head lower boundary holds simultaneously in rank and source center. -/
theorem firstAtomFailureRank_gt_of_horizon (N : ℕ) {x : ℝ}
    (hx : firstAtomMixedHorizon N ≤ x) :
    N < firstAtomFailureRank x := by
  have hQ : 0 < firstAtomMixedScale N := lt_of_lt_of_le (by norm_num) (firstAtomMixedScale_ge_three N)
  have hxlog : Real.log (firstAtomMixedScale N / Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0 (Real.log (firstAtomMixedScale N / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos hQ Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  apply firstAtomFailureRank_gt_of_scale N
  simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_div_cancel₀ _ Real.pi_ne_zero] using hm

#print axioms det_gaussianShiftedHead
#print axioms gaussianInverseTrace_eq_cofactor_div
#print axioms firstAtomBalancedHead_relative_error_le
#print axioms firstAtomBalancedHead_half_posDef_of_scale
#print axioms firstAtomSignedHead_posDef_of_scale
#print axioms firstAtomFailureRank_gt_of_scale
#print axioms firstAtomFailureRank_gt_of_horizon

end GaloisForLFunctions.CompletedArithmeticForms
