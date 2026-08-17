import GaloisForLFunctions.HTGeometry.MassCarrierShellPowers

/-!
# Bounds and closure rules for the shell expansions

Assembling a product of expansions needs, besides the expansions themselves, a bound for each factor
on the disc and a bound for each truncating polynomial.  For a shell power both come from the same
place: the modulus of a principal power with a real exponent is that power of the modulus, and on the
disc of the binomial radius the base stays above one half.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ExpansionExtras

/-- A monomial is its own expansion, with no error. -/
theorem hasPolyExpansion_monomial (r : ℝ) (n k : ℕ) :
    HasPolyExpansion r n 0 (fun w => w ^ k) (Polynomial.X ^ k) := by
  intro w _
  simp

/-- The truncating polynomial inherits the bound of the function it expands. -/
theorem HasPolyExpansion.norm_poly_le {r C Bf : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hf : HasPolyExpansion r n C f P) (hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ Bf) (hC : 0 ≤ C)
    {w : ℂ} (hw : ‖w‖ ≤ r) : ‖P.eval w‖ ≤ Bf + C * r ^ n := by
  have hrn : ‖w‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg w) hw n
  have h1 := hf w hw
  have h2 := hfb w hw
  have h3 := norm_sub_norm_le (P.eval w) (f w)
  have h4 : ‖P.eval w - f w‖ = ‖f w - P.eval w‖ := norm_sub_rev _ _
  rw [h4] at h3
  nlinarith [h1, h2, h3, hC, hrn]

/-- Finite sums of expansions. -/
theorem HasPolyExpansion.finsetSum {ι : Type*} {r : ℝ} {n : ℕ} (s : Finset ι)
    {f : ι → ℂ → ℂ} {P : ι → Polynomial ℂ} {C : ι → ℝ}
    (h : ∀ i ∈ s, HasPolyExpansion r n (C i) (f i) (P i)) :
    HasPolyExpansion r n (∑ i ∈ s, C i) (fun w => ∑ i ∈ s, f i w) (∑ i ∈ s, P i) := by
  intro w hw
  have heval : (∑ i ∈ s, P i).eval w = ∑ i ∈ s, (P i).eval w := by
    rw [Polynomial.eval_finsetSum]
  rw [heval, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => h i hi w hw

end ExpansionExtras

section ShellBounds

/-- On the binomial disc the shell base stays above one half. -/
theorem half_le_norm_one_add_shell {x r : ℝ} (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ r) : (1 : ℝ) / 2 ≤ ‖1 + (x : ℂ) ^ 2 * w ^ 2‖ := by
  have hu := norm_shell_arg hxr hw
  have h := norm_sub_norm_le (1 : ℂ) (-((x : ℂ) ^ 2 * w ^ 2))
  have hn : ‖(-((x : ℂ) ^ 2 * w ^ 2) : ℂ)‖ = ‖(x : ℂ) ^ 2 * w ^ 2‖ := norm_neg _
  have h2 : (1 : ℂ) - -((x : ℂ) ^ 2 * w ^ 2) = 1 + (x : ℂ) ^ 2 * w ^ 2 := by ring
  rw [h2, norm_one, hn] at h
  linarith

/-- **The shell power is bounded on the binomial disc.** -/
theorem norm_shellPow_le {α : ℝ} (hα : α ≤ 0) {x r : ℝ} (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ r) :
    ‖(1 + (x : ℂ) ^ 2 * w ^ 2) ^ ((α : ℝ) : ℂ)‖ ≤ (2 : ℝ) ^ (-α) := by
  have hge := half_le_norm_one_add_shell hxr hw
  rw [Complex.norm_cpow_real]
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hge hα
  refine le_trans h (le_of_eq ?_)
  rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num,
    ← Real.rpow_mul (by norm_num)]
  ring_nf

end ShellBounds

end

end GaloisForLFunctions.HTGeometry
