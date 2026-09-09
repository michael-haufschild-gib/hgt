import GaloisForLFunctions.HTGeometry.GomesGaussianChargeDilation
import GaloisForLFunctions.HTGeometry.HermiteCompleteness

/-!
# Completeness of the charged Gaussian ladder

Positive coordinate dilation identifies every charged rung with a nonzero scalar multiple
of the corpus's Hermite state. The inverse Jacobian law then transfers the existing
Hermite completeness theorem. Hence all charged coefficient measurements together
separate Schwartz states exactly, with no completeness premise supplied.
-/

noncomputable section
open MeasureTheory
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The charged ladder is precisely the dilated Hermite family with its raising normalization. -/
theorem gomesGaussianChargeLadder_eq_dilatedHermite (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    gomesGaussianChargeLadder a n =
      ((2 * (Real.pi : ℂ) * Real.sqrt a.val) ^ n) •
        gomesGaussianChargeDilation a (hermiteSchwartz n) := by
  induction n with
  | zero =>
    simp only [pow_zero, one_smul, hermiteSchwartz_zero, gomesGaussianChargeDilation_ground,
      gomesGaussianChargeLadder_zero]
  | succ n ih =>
    rw [← gomesGaussianChargeLadder_raise, ih, map_smul, gomesGaussianChargeDilation_creation,
      creationCLM_hermiteSchwartz, map_smul, smul_smul, smul_smul]
    congr 1
    rw [pow_succ]
    ring

/-- Vanishing of every charged coefficient is exactly vanishing of the Schwartz state. -/
theorem gomesGaussianChargeLadder_complete_iff (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    (∀ n : ℕ, schwartzPair ψ (gomesGaussianChargeLadder a n) = 0) ↔ ψ = 0 := by
  constructor
  · intro h
    have hs : 0 < Real.sqrt a.val := Real.sqrt_pos.mpr a.property
    have hc : 2 * (Real.pi : ℂ) * Real.sqrt a.val ≠ 0 := by
      exact_mod_cast ne_of_gt (mul_pos (mul_pos (by linarith : (0 : ℝ) < 2) Real.pi_pos) hs)
    have hf : gomesGaussianChargeUndilation a ψ = 0 := by
      apply hermiteSchwartz_complete
      intro n
      have hn := h n
      rw [gomesGaussianChargeLadder_eq_dilatedHermite, schwartzPair_smul_right] at hn
      nth_rw 1 [← gomesGaussianChargeDilation_right_inverse a ψ] at hn
      rw [gomesGaussianChargeDilation_pair] at hn
      have hp := (mul_eq_zero.mp hn).resolve_left (pow_ne_zero n hc)
      exact (smul_eq_zero.mp hp).resolve_left (inv_ne_zero hs.ne')
    have hψ := gomesGaussianChargeDilation_right_inverse a ψ
    rw [hf, map_zero] at hψ
    exact hψ.symm
  · rintro rfl n
    rw [schwartzPair_comm, schwartzPair_zero_right]

/-- Bilinearity under subtraction on the actual Schwartz pairing. -/
theorem gomesSchwartzPair_sub_left (f g h : 𝓢(ℝ, ℂ)) :
    schwartzPair (f - g) h = schwartzPair f h - schwartzPair g h := by
  rw [schwartzPair_eq_integral, schwartzPair_eq_integral, schwartzPair_eq_integral]
  simp only [sub_apply, sub_mul]
  have hf := (mulS f h).integrable (μ := (volume : Measure ℝ))
  have hg := (mulS g h).integrable (μ := (volume : Measure ℝ))
  change Integrable (fun x => mulS f h x) volume at hf
  change Integrable (fun x => mulS g h x) volume at hg
  simp only [mulS_apply] at hf hg
  exact integral_sub hf hg

/-- The full charged observation record determines the original Schwartz state. -/
theorem gomesGaussianChargeLadder_coefficients_injective (a : Set.Ioi (0 : ℝ)) :
    Function.Injective (fun ψ : 𝓢(ℝ, ℂ) => fun n : ℕ =>
      schwartzPair ψ (gomesGaussianChargeLadder a n)) := by
  intro f g h
  apply sub_eq_zero.mp
  apply (gomesGaussianChargeLadder_complete_iff a (f - g)).mp
  intro n
  have hn : schwartzPair f (gomesGaussianChargeLadder a n) =
      schwartzPair g (gomesGaussianChargeLadder a n) := congrFun h n
  rw [gomesSchwartzPair_sub_left, hn, sub_self]

/-- Vanishing of all actual Hilbert coefficients likewise characterizes the zero Schwartz state. -/
theorem gomesGaussianChargeLadder_inner_complete_iff (a : Set.Ioi (0 : ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    (∀ n : ℕ, inner ℂ ((gomesGaussianChargeLadder a n).toLp 2 volume) (ψ.toLp 2 volume) = 0) ↔
      ψ = 0 := by
  have h (n : ℕ) : inner ℂ ((gomesGaussianChargeLadder a n).toLp 2 volume) (ψ.toLp 2 volume) =
      schwartzPair ψ (gomesGaussianChargeLadder a n) := by
    rw [schwartzPair_comm, schwartzPair_eq_inner, gomesGaussianChargeLadder_conj]
  simp only [h]
  exact gomesGaussianChargeLadder_complete_iff a ψ

end GaloisForLFunctions.HTGeometry
