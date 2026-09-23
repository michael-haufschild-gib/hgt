import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The second variation of a quadratic-rate identity

A quadratic-rate identity `L² = κ Q` restricted to a line `x ↦ H₀ + x V` with `V` orthogonal to
`H₀` reads `F(x)² = κ (Q₀ + x² Q_V)`.  The first variation of the spectral action along a
zero-diagonal perturbation vanishes, so differentiating twice at `x = 0` leaves the pole-free
identity

`F(0) · F''(0) = κ Q_V`.

That identity is the source of the residue argument: its left factor is affine in the attached
local field and its right factor has no spectral pole.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The second variation.**  With a vanishing first variation, a quadratic-rate identity along a
line reduces to a pole-free product identity. -/
theorem quadraticRate_secondVariation {F F' : ℂ → ℂ} {F'' κ Q₀ Qv : ℂ}
    (hF : ∀ᶠ x in 𝓝 (0 : ℂ), HasDerivAt F (F' x) x)
    (hF' : HasDerivAt F' F'' 0) (hF'0 : F' 0 = 0)
    (hid : ∀ᶠ x in 𝓝 (0 : ℂ), F x ^ (2 : ℕ) = κ * (Q₀ + x ^ (2 : ℕ) * Qv)) :
    F 0 * F'' = κ * Qv := by
  -- first differentiation, valid on a neighbourhood
  have hid' : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ᶠ y in 𝓝 x, F y ^ (2 : ℕ) = κ * (Q₀ + y ^ (2 : ℕ) * Qv) :=
    hid.eventually_nhds
  have hstep : ∀ᶠ x in 𝓝 (0 : ℂ), 2 * F x * F' x = κ * (2 * x * Qv) := by
    filter_upwards [hF, hid'] with x hx hlocal
    have hEq : (fun y : ℂ => F y ^ (2 : ℕ)) =ᶠ[𝓝 x] fun y : ℂ => κ * (Q₀ + y ^ (2 : ℕ) * Qv) := hlocal
    have hleft : HasDerivAt (fun y => F y ^ (2 : ℕ)) (2 * F x ^ (1 : ℕ) * F' x) x := hx.pow 2
    have hright : HasDerivAt (fun y : ℂ => κ * (Q₀ + y ^ (2 : ℕ) * Qv)) (κ * (2 * x * Qv)) x := by
      have hinner : HasDerivAt (fun y : ℂ => Q₀ + y ^ (2 : ℕ) * Qv) (2 * x * Qv) x := by
        have hpow : HasDerivAt (fun y : ℂ => y ^ (2 : ℕ)) ((2 : ℂ) * x ^ (2 - 1)) x :=
          hasDerivAt_pow 2 x
        simpa using (hpow.mul_const Qv).const_add Q₀
      exact hinner.const_mul κ
    have hleft' : HasDerivAt (fun y : ℂ => κ * (Q₀ + y ^ (2 : ℕ) * Qv)) (2 * F x ^ (1 : ℕ) * F' x) x :=
      hleft.congr_of_eventuallyEq hEq.symm
    have huniq := hleft'.unique hright
    simpa using huniq
  -- second differentiation, at the base point
  have hF0 : HasDerivAt F (F' 0) 0 := hF.self_of_nhds
  have hleft2 : HasDerivAt (fun x : ℂ => 2 * F x * F' x)
      (2 * F' 0 * F' 0 + 2 * F 0 * F'') 0 := by
    have h1 : HasDerivAt (fun x : ℂ => 2 * F x) (2 * F' 0) 0 := hF0.const_mul 2
    exact h1.mul hF'
  have hright2 : HasDerivAt (fun x : ℂ => κ * (2 * x * Qv)) (κ * (2 * Qv)) 0 := by
    have hlin : HasDerivAt (fun x : ℂ => 2 * x * Qv) (2 * Qv) 0 := by
      have h2 : HasDerivAt (fun x : ℂ => 2 * x) (2 : ℂ) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 : ℂ)
      simpa using h2.mul_const Qv
    exact hlin.const_mul κ
  have hEq2 : (fun x : ℂ => 2 * F x * F' x) =ᶠ[𝓝 (0 : ℂ)] fun x : ℂ => κ * (2 * x * Qv) := hstep
  have hleft2' : HasDerivAt (fun x : ℂ => κ * (2 * x * Qv))
      (2 * F' 0 * F' 0 + 2 * F 0 * F'') 0 := hleft2.congr_of_eventuallyEq hEq2.symm
  have hfinal := hleft2'.unique hright2
  rw [hF'0] at hfinal
  have : 2 * (F 0 * F'') = 2 * (κ * Qv) := by linear_combination hfinal
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) this

end GaloisForLFunctions.HTGeometry
