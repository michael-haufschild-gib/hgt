import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Nodal reversal defeats a zero-mean angular-energy shortcut

For a real differentiable profile the radial-subtracted derivative residual vanishes
away from its zeros. Cosine supplies an exact smooth periodic zero-mean profile with
positive mass and zero integrated residual. Its residual is genuinely integrable and
is nonzero at a node; the zero integral is not Lean's nonintegrability fallback.

This tests only the inference from smooth periodic zero-mean data to positive integrated
angular energy. The profile is not claimed to be Maass, cuspidal, or inversion invariant.
The source-specific positive replacement is proved in SelbergMaassTraceDirection.
-/

open Set MeasureTheory
namespace GaloisForLFunctions.RHTower.SelbergNodalAngularToy
noncomputable section

/-- Actual scalar derivative residual after subtracting the squared-amplitude radial slope. -/
def residual (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv h x - deriv (fun t => h t ^ (2 : ℕ)) x / (2 * h x ^ (2 : ℕ)) * h x) ^ (2 : ℕ)

/-- For a real differentiable profile, all residual energy is concentrated at its zeros. -/
theorem residual_eq_zero_off_zeros {h : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ h x) (hx : h x ≠ 0) : residual h x = 0 := by
  have hs : deriv (fun t => h t ^ (2 : ℕ)) x = (2 : ℝ) * h x * deriv h x := by
    simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hd.hasDerivAt.fun_pow 2).deriv
  unfold residual
  rw [hs]
  field_simp [hx]
  ring

/-- At a real profile zero, the residual retains the full derivative square. -/
theorem residual_at_zero {h : ℝ → ℝ} {x : ℝ} (hx : h x = 0) :
    residual h x = deriv h x ^ (2 : ℕ) := by
  simp [residual, hx]

/-- The exact nodal set of cosine is countable. -/
theorem cosine_zeros_countable : {x : ℝ | Real.cos x = 0}.Countable := by
  have he : {x : ℝ | Real.cos x = 0} = Set.range (fun k : ℤ => (2 * (k : ℝ) + 1) * Real.pi / 2) := by
    ext x
    simp only [mem_setOf_eq, mem_range, Real.cos_eq_zero_iff]
    exact exists_congr (fun k => eq_comm)
  rw [he]
  exact countable_range _

/-- The cosine residual vanishes almost everywhere despite its direction reversals. -/
theorem cosine_residual_ae_zero : residual Real.cos =ᵐ[volume] (fun _ => 0) := by
  filter_upwards [cosine_zeros_countable.ae_notMem volume] with x hx
  exact residual_eq_zero_off_zeros Real.differentiableAt_cos hx

/-- The actual residual is integrable; its zero integral is not a fallback for nonintegrability. -/
theorem cosine_residual_integrable : Integrable (residual Real.cos) := by
  exact (integrable_zero ℝ ℝ volume).congr cosine_residual_ae_zero.symm

/-- The exact angular residual integrates to zero on every compact interval. -/
theorem cosine_residual_integral (a b : ℝ) : (∫ x in a..b, residual Real.cos x) = 0 := by
  calc
    (∫ x in a..b, residual Real.cos x) = ∫ _x in a..b, (0 : ℝ) :=
      intervalIntegral.integral_congr_ae (cosine_residual_ae_zero.mono (fun _ hx _ => hx))
    _ = 0 := intervalIntegral.integral_zero

/-- The nodal residual is nonzero at the first cosine zero. -/
theorem cosine_residual_at_node : residual Real.cos (Real.pi / 2) = 1 := by
  rw [residual_at_zero Real.cos_pi_div_two, Real.deriv_cos, Real.sin_pi_div_two]
  norm_num

/-- A smooth nonzero periodic zero-mean profile need not have positive integrated angular residual. -/
theorem zero_mean_does_not_force_angular_energy :
    ∃ h : ℝ → ℝ, ContDiff ℝ 2 h ∧ Function.Periodic h (2 * Real.pi) ∧
      h 0 = 1 ∧ h Real.pi = -1 ∧
      (∫ x in (0 : ℝ)..2 * Real.pi, h x) = 0 ∧
      0 < (∫ x in (0 : ℝ)..2 * Real.pi, h x ^ (2 : ℕ)) ∧
      Integrable (residual h) ∧ (∫ x in (0 : ℝ)..2 * Real.pi, residual h x) = 0 := by
  refine ⟨Real.cos, Real.contDiff_cos, Real.cos_periodic, Real.cos_zero, Real.cos_pi, ?_, ?_,
    cosine_residual_integrable, cosine_residual_integral _ _⟩
  · rw [integral_cos, Real.sin_two_pi, Real.sin_zero, sub_self]
  · rw [integral_cos_sq, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
    nlinarith [Real.pi_pos]

end
end GaloisForLFunctions.RHTower.SelbergNodalAngularToy
