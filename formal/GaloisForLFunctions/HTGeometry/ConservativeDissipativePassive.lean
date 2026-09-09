import GaloisForLFunctions.HTGeometry.ConservativeDissipativeResolvent
import GaloisForLFunctions.RHTower.PairedTranslationResolventCalculus

set_option autoImplicit false

/-!
# Passive paired-translation responses from conservative–dissipative steps

The discrete energy split induced by Schaffer–Exl (arXiv:2609.04530)
feeds the existing paired-translation Cayley contact identity. Constructed
strict disk contractions remove the source theorem's contraction premise.
The passive response power splits exactly into disk attenuation and the
original physical observation damping, and vanishes only on zero input.
-/
open scoped InnerProductSpace NNReal Ring
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- A strictly interior disk radius constructed from an unrestricted real parameter. -/
def passiveRadius (u : ℝ) : ℝ := (2 + u ^ 2)⁻¹

theorem passiveRadius_pos (u : ℝ) : 0 < passiveRadius u := by unfold passiveRadius; positivity

theorem passiveRadius_lt_one (u : ℝ) : passiveRadius u < 1 := by
  unfold passiveRadius
  apply (inv_lt_one₀ (by positivity : 0 < 2 + u ^ 2)).mpr
  nlinarith [sq_nonneg u]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Strict disk contraction obtained from an unrestricted conservative–dissipative midpoint step. -/
def passiveDiskStep (A : E →L[ℂ] E) (B : E →L[ℂ] F) (t : ℝ≥0) (u : ℝ) : E →L[ℂ] E :=
  (passiveRadius u : ℂ) • cayleyStep A B t

theorem passiveDiskStep_norm_lt_one (A : E →L[ℂ] E) (B : E →L[ℂ] F) (t : ℝ≥0) (u : ℝ) :
    ‖passiveDiskStep A B t u‖ < 1 :=
  _root_.RHTower.norm_real_smul_lt_one (passiveRadius_pos u).le (passiveRadius_lt_one u)
    (cayleyStep_opNorm_le_one A B t)

/-- Geometric response inverse associated with the constructed disk step. -/
def passiveSolve (A : E →L[ℂ] E) (B : E →L[ℂ] F) (t : ℝ≥0) (u : ℝ) : E →L[ℂ] E :=
  (1 - passiveDiskStep A B t u)⁻¹ʳ

theorem passiveSolve_equation (A : E →L[ℂ] E) (B : E →L[ℂ] F) (t : ℝ≥0) (u : ℝ) (x : E) :
    (1 - passiveDiskStep A B t u) (passiveSolve A B t u x) = x := by
  have h := congrArg (fun T : E →L[ℂ] E => T x)
    (_root_.RHTower.one_sub_mul_inverse _ (passiveDiskStep_norm_lt_one A B t u))
  simpa only [passiveSolve, mul_apply_eq_comp, one_apply_eq_self] using h

/-- Passive response in the paired-translation corpus's Cayley normalization. -/
def passiveResponse (A : E →L[ℂ] E) (B : E →L[ℂ] F) (t : ℝ≥0) (u : ℝ) : E →L[ℂ] E :=
  (1 + passiveDiskStep A B t u) * passiveSolve A B t u

/-- The corpus contact identity applies without an assumed contraction. -/
theorem passiveResponse_power (A : E →L[ℂ] E) (B : E →L[ℂ] F)
    (t : ℝ≥0) (u : ℝ) (x : E) :
    RCLike.re ⟪passiveResponse A B t u x, x⟫_ℂ =
      ‖passiveSolve A B t u x‖ ^ 2 -
        ‖passiveDiskStep A B t u (passiveSolve A B t u x)‖ ^ 2 := by
  have h := _root_.RHTower.re_inner_cayley_eq (passiveDiskStep A B t u) (passiveSolve A B t u x)
  rw [passiveSolve_equation] at h
  exact h

/-- Exact passive power separates disk attenuation from the paper's physical damping. -/
theorem passiveResponse_power_decomposition (A : E →L[ℂ] E) (B : E →L[ℂ] F)
    (t : ℝ≥0) (u : ℝ) (x : E) :
    RCLike.re ⟪passiveResponse A B t u x, x⟫_ℂ =
      (1 - passiveRadius u ^ 2) * ‖passiveSolve A B t u x‖ ^ 2 +
        4 * (t : ℝ) * passiveRadius u ^ 2 *
          ‖B (implicitStep A B t (passiveSolve A B t u x))‖ ^ 2 := by
  rw [passiveResponse_power]
  change ‖passiveSolve A B t u x‖ ^ 2 -
    ‖(passiveRadius u : ℂ) • cayleyStep A B t (passiveSolve A B t u x)‖ ^ 2 = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (passiveRadius_pos u)]
  have h := cayleyStep_energy A B t (passiveSolve A B t u x)
  nlinarith [sq_nonneg (passiveRadius u)]

/-- The response power is nonnegative for arbitrary coefficients and input. -/
theorem passiveResponse_power_nonneg (A : E →L[ℂ] E) (B : E →L[ℂ] F)
    (t : ℝ≥0) (u : ℝ) (x : E) : 0 ≤ RCLike.re ⟪passiveResponse A B t u x, x⟫_ℂ := by
  rw [passiveResponse_power_decomposition]
  have hp := passiveRadius_pos u
  have hl := passiveRadius_lt_one u
  have hc : 0 ≤ 1 - passiveRadius u ^ 2 := by nlinarith
  exact add_nonneg (mul_nonneg hc (sq_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) t.coe_nonneg) (sq_nonneg _)) (sq_nonneg _))

/-- Only zero input has zero passive power, even when the underlying damping has a kernel. -/
theorem passiveResponse_power_eq_zero_iff (A : E →L[ℂ] E) (B : E →L[ℂ] F)
    (t : ℝ≥0) (u : ℝ) (x : E) :
    RCLike.re ⟪passiveResponse A B t u x, x⟫_ℂ = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [passiveResponse_power_decomposition] at h
    have hp := passiveRadius_pos u
    have hl := passiveRadius_lt_one u
    have hc : 0 < 1 - passiveRadius u ^ 2 := by nlinarith
    have hn : 0 ≤ 4 * (t : ℝ) * passiveRadius u ^ 2 *
        ‖B (implicitStep A B t (passiveSolve A B t u x))‖ ^ 2 := by positivity
    have hy : ‖passiveSolve A B t u x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖passiveSolve A B t u x‖]
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp hy)
    have he := passiveSolve_equation A B t u x
    rw [hz, map_zero] at he
    exact he.symm
  · rintro rfl
    simp

end
end GaloisForLFunctions.HTGeometry.SchafferExl
