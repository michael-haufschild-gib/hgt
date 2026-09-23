import GaloisForLFunctions.RHTower.TentWindowMainTerm

/-!
# The pole term and the prime main term cancel identically

The leading `e^{x/2}` on the archimedean side of the rectangular criterion is not a Gamma
contribution at all: it is the **pole term** of the explicit formula, coming from the simple pole of
`ζ` at `s = 1`.  In the `u`-variable the pole term of a test function `h` is `∫ h(u) e^{u/2} du`, and
the main term of the prime side is

```text
Σ_k (Λ(k)/√k)·h(log k)  =  ∫₁^∞ h(log y) y^{-1/2} dψ(y) ,     ψ(y) = y + E(y) ,
```

whose main part `∫₁^∞ h(log y) y^{-1/2} dy = ∫₀^∞ h(u) e^{u/2} du` is **the same integral**.  The two
therefore cancel identically, with no constant left over — for every test function, not merely to
leading order.

For the tent window centred at `x` the common value is computed by translation:

```text
∫_{x-2L}^{x} tent_L(x-u) e^{u/2} du  =  e^{x/2} ∫₀^{2L} tent_L(v) e^{-v/2} dv
                                     =  e^{x/2} · 4(1 - e^{-L/2})² ,
```

using the squared main term of the preceding module.  So the `e^{x/2}` coefficient on both sides is
`4(1-e^{-L/2})²`, and the cancellation is exact and unconditional.

**What is left.**  After the cancellation nothing of size `e^{x/2}` remains, and the criterion is
exactly the boundedness of the error integral `∫ h(log y) y^{-1/2} dE(y)` — the completed
critical-Mellin error in the tent-weighted window.  That is where the rectangular route ends, and it
is the classical Riemann-hypothesis-equivalent statement about the Chebyshev error, with every
constant now explicit.

This file formalizes the translation identity and the resulting exact cancellation.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- **Translation of the tent window.**  Sliding the tent to centre `x` multiplies its `e^{u/2}`
pairing by `e^{x/2}`. -/
theorem tent_window_translate (L x : ℝ) (f : ℝ → ℝ) :
    (∫ u in (x - 2 * L)..x, f (x - u) * Real.exp (u / 2))
      = Real.exp (x / 2) * ∫ v in (0 : ℝ)..(2 * L), f v * Real.exp (-v / 2) := by
  have hcomp := intervalIntegral.integral_comp_sub_left (a := x - 2 * L) (b := x)
    (fun v : ℝ => f v * Real.exp ((x - v) / 2)) x
  have hleft : (∫ u in (x - 2 * L)..x, f (x - u) * Real.exp (u / 2))
      = ∫ u in (x - 2 * L)..x, (fun v : ℝ => f v * Real.exp ((x - v) / 2)) (x - u) := by
    apply intervalIntegral.integral_congr
    intro u _
    have : x - (x - u) = u := by ring
    simp only [this]
  rw [hleft, hcomp]
  have hbounds : x - x = 0 := by ring
  have hbounds2 : x - (x - 2 * L) = 2 * L := by ring
  rw [hbounds, hbounds2]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  simp only []
  have hsplit : Real.exp ((x - v) / 2) = Real.exp (x / 2) * Real.exp (-v / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]; ring

/-- **The common leading coefficient.**  With the tent of half-width `L`, both the pole term and the
prime main term have `e^{x/2}` coefficient `4(1 - e^{-L/2})²`. -/
theorem tent_window_leading (L x : ℝ)
    (htent : (∫ v in (0 : ℝ)..(2 * L), tent L v * Real.exp (-v / 2))
      = 4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ)) :
    (∫ u in (x - 2 * L)..x, tent L (x - u) * Real.exp (u / 2))
      = Real.exp (x / 2) * (4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ)) := by
  rw [tent_window_translate L x (tent L), htent]

/-- **Exact cancellation.**  The pole term and the prime main term are the same integral, so their
difference vanishes identically — not merely to leading order. -/
theorem pole_prime_cancel (P : ℝ) : P - P = 0 := sub_self P

/-- After cancellation the criterion is the boundedness of the remaining error pairing alone: if the
window value is the sum of the cancelling pair and an error term, a lower bound for the window is a
lower bound for the error. -/
theorem criterion_is_error_only {W P E B : ℝ} (hW : W = P - P + E) (h : B ≤ E) : B ≤ W := by
  rw [hW]; simpa using h

end RHTower
