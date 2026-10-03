import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralSignChange

/-!
# Littlewood's theorem for `θ`: `θ(x) - x = Ω±(√x logloglog x)`

Since `0 ≤ ψ - θ ≤ C√x`, the two sides of Littlewood's theorem for `ψ`
(`chebyshevPsi_sub_omega_pm_littlewood`) transfer to `θ`: the lower side directly, the upper side
after absorbing `C√x` into half of `c√x logloglog x`.  In particular `θ(x) > x` for arbitrarily
large `x`.
-/

open Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- **`θ(x) - x < -c√x logloglog x` infinitely often**, `c = 1/(70π³)`. -/
theorem frequently_chebyshevTheta_sub_lt_littlewood :
    ∃ᶠ x : ℝ in atTop, Chebyshev.theta x - x
      < -(littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))) :=
  frequently_chebyshevPsi_sub_lt_littlewood.mono fun x hx => by
    have := Chebyshev.theta_le_psi x
    linarith

/-- **`θ(x) - x > (c/2)√x logloglog x` infinitely often**, `c = 1/(70π³)`. -/
theorem frequently_littlewood_lt_chebyshevTheta_sub :
    ∃ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))
      < Chebyshev.theta x - x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hc0 : 0 < littlewoodConst / 28 := by have := littlewoodConst_pos; positivity
  have hev : ∀ᶠ x : ℝ in atTop, |C| ≤ littlewoodConst / 28 * Real.log (Real.log (Real.log x)) :=
    tendsto_logLogLog_atTop.eventually_ge_atTop (|C| / (littlewoodConst / 28)) |>.mono
      fun x hx => by rwa [div_le_iff₀ hc0, mul_comm] at hx
  refine (frequently_littlewood_lt_chebyshevPsi_sub.and_eventually hev).mono ?_
  rintro x ⟨hx, hb⟩
  have hpt := hC x
  have hs := Real.sqrt_nonneg x
  have h1 : C * Real.sqrt x ≤ |C| * Real.sqrt x := mul_le_mul_of_nonneg_right (le_abs_self C) hs
  have h2 : |C| * Real.sqrt x
      ≤ littlewoodConst / 28 * Real.log (Real.log (Real.log x)) * Real.sqrt x :=
    mul_le_mul_of_nonneg_right hb hs
  have e : littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x))
      = 2 * (littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))) := by ring
  nlinarith

/-- **Littlewood for `θ`, both sides.**  In particular `θ(x) > x` and `θ(x) < x` each hold for
arbitrarily large `x`. -/
theorem chebyshevTheta_sub_omega_pm_littlewood :
    (∃ᶠ x : ℝ in atTop, Chebyshev.theta x - x
      < -(littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))))
    ∧ ∃ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))
      < Chebyshev.theta x - x := by
  refine ⟨?_, frequently_littlewood_lt_chebyshevTheta_sub⟩
  refine (frequently_chebyshevTheta_sub_lt_littlewood.and_eventually
    (tendsto_logLogLog_atTop.eventually_ge_atTop 0)).mono fun x ⟨hx, hL⟩ => ?_
  have : 0 ≤ littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) := by
    have := littlewoodConst_pos
    positivity
  nlinarith

end

end RHTower
