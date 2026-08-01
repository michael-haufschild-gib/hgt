import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.IntermediateValue

/-!
# A continuous phase lift is unique once normalized

Two continuous real functions with the same unit-modulus exponential differ by a continuous
integer multiple of `2 π`.  On a connected domain such a difference cannot move: were it to change,
the intermediate value theorem would force it to pass through `π`, which is not a multiple of
`2 π`.  So agreeing at a single point forces the two lifts to agree everywhere.

This is the uniqueness half of phase lifting.  It is what turns "the inner function determines the
phase" from a statement about boundary values at one point into a statement about the whole
function.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- The difference of two lifts of the same phase is a multiple of `2 π` at every point. -/
theorem sub_mem_two_pi_int_of_exp_eq {f g : ℝ → ℝ}
    (hexp : ∀ x, Complex.exp ((f x : ℂ) * Complex.I) = Complex.exp ((g x : ℂ) * Complex.I))
    (x : ℝ) : ∃ n : ℤ, f x - g x = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp x)
  refine ⟨n, ?_⟩
  have hI : (((f x - g x : ℝ)) : ℂ) * Complex.I
      = (((2 * Real.pi * n : ℝ)) : ℂ) * Complex.I := by
    push_cast
    linear_combination hn
  have hcast : (((f x - g x : ℝ)) : ℂ) = (((2 * Real.pi * n : ℝ)) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero hI
  exact_mod_cast hcast

/-- `π` is not an integer multiple of `2 π`. -/
theorem pi_ne_two_pi_mul_int (n : ℤ) : Real.pi ≠ 2 * Real.pi * n := by
  intro h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : (1 : ℝ) = 2 * n := by
    field_simp at h
    rcases h with h | h
    · linarith
    · exact absurd h hpi
  have h2 : (2 : ℤ) * n = 1 := by exact_mod_cast h1.symm
  omega

theorem neg_pi_ne_two_pi_mul_int (n : ℤ) : -Real.pi ≠ 2 * Real.pi * n := by
  intro h
  exact pi_ne_two_pi_mul_int (-n) (by push_cast; linarith)

/-- **Uniqueness of the continuous phase lift.**  Two continuous lifts of the same phase that agree
at one point agree everywhere. -/
theorem eq_of_exp_eq_of_eq_at {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hexp : ∀ x, Complex.exp ((f x : ℂ) * Complex.I) = Complex.exp ((g x : ℂ) * Complex.I))
    {x₀ : ℝ} (h₀ : f x₀ = g x₀) : f = g := by
  have hd : Continuous (fun x => f x - g x) := hf.sub hg
  have hzero : f x₀ - g x₀ = 0 := by rw [h₀]; ring
  funext x₁
  by_contra hne
  have hdne : f x₁ - g x₁ ≠ 0 := fun h => hne (by linarith [sub_eq_zero.mp h])
  obtain ⟨n, hn⟩ := sub_mem_two_pi_int_of_exp_eq hexp x₁
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    simp at hn
    exact hdne hn
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the difference is at least a full turn away from zero, so it must cross `π` or `-π`
  have hIVT := intermediate_value_uIcc (a := x₀) (b := x₁) hd.continuousOn
  rcases lt_or_gt_of_ne hdne with hlt | hgt
  · -- difference negative: it crosses `-π`
    have hle : f x₁ - g x₁ ≤ -(2 * Real.pi) := by
      rw [hn]
      have : (n : ℝ) ≤ -1 := by
        have : n ≤ -1 := by omega_nat <;> omega
        exact_mod_cast this
      nlinarith
    have hmem : -Real.pi ∈ uIcc (f x₀ - g x₀) (f x₁ - g x₁) := by
      rw [hzero, uIcc_of_ge (by linarith)]
      constructor <;> linarith
    obtain ⟨y, -, hy⟩ := hIVT hmem
    obtain ⟨m, hm⟩ := sub_mem_two_pi_int_of_exp_eq hexp y
    exact neg_pi_ne_two_pi_mul_int m (by rw [← hy, hm])
  · -- difference positive: it crosses `π`
    have hge : 2 * Real.pi ≤ f x₁ - g x₁ := by
      rw [hn]
      have : (1 : ℝ) ≤ (n : ℝ) := by
        have : 1 ≤ n := by omega_nat <;> omega
        exact_mod_cast this
      nlinarith
    have hmem : Real.pi ∈ uIcc (f x₀ - g x₀) (f x₁ - g x₁) := by
      rw [hzero, uIcc_of_le (by linarith)]
      constructor <;> linarith
    obtain ⟨y, -, hy⟩ := hIVT hmem
    obtain ⟨m, hm⟩ := sub_mem_two_pi_int_of_exp_eq hexp y
    exact pi_ne_two_pi_mul_int m (by rw [← hy, hm])

end GaloisForLFunctions.HTGeometry
