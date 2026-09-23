import GaloisForLFunctions.RHTower.ArchimedeanSingleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The tent-weighted prime window has the squared main term

The corpus computes the **sharp** (box) moving prime window and finds the exact square-root main term
`4(1 - e^{-L/2})·√n`.  The window that actually appears in the rectangular screw criterion is not the
box but its **second difference**, which is the tent — and the tent is the autocorrelation of the
box.  Its main term is therefore the *square* of the box constant.

Concretely, the main term of `Σ_k (Λ(k)/√k)·tent_L(x - log k)` is obtained by replacing `dψ(y)` with
`dy`, giving `∫ tent_L(x-u) e^{u/2} du = e^{x/2}·∫₀^{2L} tent_L(v) e^{-v/2} dv`, and

```text
∫₀^{2L} tent_L(v) e^{-v/2} dv  =  4 (1 - e^{-L/2})² .
```

The square is not a coincidence: the tent is `1_{[0,L]} * 1_{[0,L]}`, so its Laplace transform at
`1/2` is the square of `∫₀^L e^{-v/2}dv = 2(1 - e^{-L/2})`.  **The positivity structure of the Weil
form appears here as an arithmetic square**, exactly matching the Fejér weight
`4sin²(Lγ/2)/γ²` on the zero side, which is the squared modulus of the same box transform.

So the three sides of the rectangular criterion carry the same square:

```text
prime side       main term  4(1 - e^{-L/2})² · e^{x/2}
zero side        weights    |∫₀^L e^{-iγu}du|² = 4sin²(Lγ/2)/γ²
archimedean side kernel     the collapsed integral in the same tent
```

This file proves the integral identity by exhibiting antiderivatives on the two halves of the tent.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- Antiderivative of `v ↦ v·e^{-v/2}`. -/
def tentAntiderivLeft (v : ℝ) : ℝ := -2 * v * Real.exp (-v / 2) - 4 * Real.exp (-v / 2)

/-- Antiderivative of `v ↦ (2L - v)·e^{-v/2}`. -/
def tentAntiderivRight (L v : ℝ) : ℝ :=
  -2 * (2 * L - v) * Real.exp (-v / 2) + 4 * Real.exp (-v / 2)

theorem hasDerivAt_tentAntiderivLeft (v : ℝ) :
    HasDerivAt tentAntiderivLeft (v * Real.exp (-v / 2)) v := by
  unfold tentAntiderivLeft
  have hexp : HasDerivAt (fun w : ℝ => Real.exp (-w / 2))
      (Real.exp (-v / 2) * (-1 / 2)) v := by
    have h1 : HasDerivAt (fun w : ℝ => -w / 2) (-1 / 2) v := by
      simpa using ((hasDerivAt_id v).neg).div_const 2
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-v / 2)).comp v h1
  have hlin : HasDerivAt (fun w : ℝ => -2 * w) (-2 : ℝ) v := by
    simpa using (hasDerivAt_id v).const_mul (-2 : ℝ)
  have hprod := (hlin.mul hexp).sub (hexp.const_mul (4 : ℝ))
  convert hprod using 1
  all_goals try rfl
  all_goals ring

theorem hasDerivAt_tentAntiderivRight (L v : ℝ) :
    HasDerivAt (tentAntiderivRight L) ((2 * L - v) * Real.exp (-v / 2)) v := by
  unfold tentAntiderivRight
  have hexp : HasDerivAt (fun w : ℝ => Real.exp (-w / 2))
      (Real.exp (-v / 2) * (-1 / 2)) v := by
    have h1 : HasDerivAt (fun w : ℝ => -w / 2) (-1 / 2) v := by
      simpa using ((hasDerivAt_id v).neg).div_const 2
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-v / 2)).comp v h1
  have hlin : HasDerivAt (fun w : ℝ => -2 * (2 * L - w)) (2 : ℝ) v := by
    have h2 : HasDerivAt (fun w : ℝ => 2 * L - w) (-1 : ℝ) v := by
      exact (hasDerivAt_id v).const_sub (2 * L)
    simpa using h2.const_mul (-2 : ℝ)
  have hprod := (hlin.mul hexp).add (hexp.const_mul (4 : ℝ))
  convert hprod using 1
  all_goals try rfl
  all_goals ring

/-- **The left half of the tent.**  `∫₀^L v e^{-v/2} dv = -2L e^{-L/2} + 4(1 - e^{-L/2})`. -/
theorem integral_tent_left (L : ℝ) :
    (∫ v in (0 : ℝ)..L, v * Real.exp (-v / 2))
      = -2 * L * Real.exp (-L / 2) + 4 * (1 - Real.exp (-L / 2)) := by
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_tentAntiderivLeft v)]
  · unfold tentAntiderivLeft
    simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop

/-- **The right half of the tent.**  `∫_L^{2L} (2L - v) e^{-v/2} dv
= 2L e^{-L/2} - 4 e^{-L/2} + 4 e^{-L}`. -/
theorem integral_tent_right (L : ℝ) :
    (∫ v in L..(2 * L), (2 * L - v) * Real.exp (-v / 2))
      = 2 * L * Real.exp (-L / 2) - 4 * Real.exp (-L / 2) + 4 * Real.exp (-L) := by
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_tentAntiderivRight L v)]
  · unfold tentAntiderivRight
    have h2 : -(2 * L) / 2 = -L := by ring
    simp only [sub_self, h2]
    ring_nf
  · apply Continuous.intervalIntegrable
    fun_prop

/-- **The squared main term.**  Adding the two halves,
`∫₀^{2L} tent_L(v) e^{-v/2} dv = 4(1 - e^{-L/2})²`. -/
theorem tent_laplace_half (L : ℝ) :
    ((-2 * L * Real.exp (-L / 2) + 4 * (1 - Real.exp (-L / 2)))
      + (2 * L * Real.exp (-L / 2) - 4 * Real.exp (-L / 2) + 4 * Real.exp (-L)))
      = 4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ) := by
  have hsq : Real.exp (-L) = Real.exp (-L / 2) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring_nf
  rw [hsq]
  ring

/-- The constant is nonnegative, and is the square of the sharp-window constant
`2(1 - e^{-L/2})`. -/
theorem tent_constant_is_square (L : ℝ) :
    4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ) = (2 * (1 - Real.exp (-L / 2))) ^ (2 : ℕ) := by ring

end RHTower
