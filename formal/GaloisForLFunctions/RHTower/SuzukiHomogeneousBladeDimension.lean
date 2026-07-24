import GaloisForLFunctions.RHTower.SuzukiResolventJetHomogeneousPluckerTomography
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior-basis dimension of the Suzuki homogeneous Plücker blade

The resolvent-jet tomography (`SuzukiResolventJetHomogeneousPluckerTomography`) isolates every one-mode
(Neumann homogeneous, `eᵢ ∧ ∞`) and two-mode (Euler–Gamma spectral-pair, `eᵢ ∧ eⱼ`) coordinate of the
homogeneous blade `(v,0) ∧ (Av,1)` in `⋀²(V ⊕ F)`.  This file supplies the remaining dimension count
that turns "every coordinate is produced" into "the isolated blades form a basis": the blade space
`⋀²(V ⊕ F)` for `V = ℝⁿ`, `F = ℝ` — i.e. `⋀²(ℝⁿ⁺¹)` — has dimension

`n + C(n,2)`,

exactly the `n` one-mode plus `C(n,2)` two-mode isolated coordinates.  Combined with the tomography's
coordinate realization, the isolated one-mode and two-mode blades therefore span, hence form a basis,
of the full homogeneous exterior square.
-/

open scoped ExteriorAlgebra

namespace RHTower

noncomputable section

/-- **Exterior-basis dimension of the homogeneous Plücker blade.**  The blade space `⋀²(V ⊕ F)` for
`V = ℝⁿ`, `F = ℝ` (i.e. `⋀²(ℝⁿ⁺¹)`) has dimension `n + C(n,2)` — the `n` one-mode (Neumann) plus
`C(n,2)` two-mode (spectral-pair) tomography coordinates. -/
theorem suzukiHomogeneousBlade_finrank (n : ℕ) :
    Module.finrank ℝ (⋀[ℝ]^2 (Fin (n + 1) → ℝ)) = n + Nat.choose n 2 := by
  rw [exteriorPower.finrank_eq ℝ 2, Module.finrank_pi, Fintype.card_fin,
    Nat.choose_succ_succ, Nat.choose_one_right]

end

end RHTower
