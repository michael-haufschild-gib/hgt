import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamRadiation

/-!
# Pole-free form and horizon value of the scalar–scalar forcing

The forcing `−(r²(r²−1)/4)·ssMasterSource` of the scalar–scalar `++` Green problem has no pole at
the horizon: the simple pole of the master source at `r = 1` is cancelled, leaving the rational
function `srcForcing = −N(r)/(4r³(2−μ))` with `N` an even polynomial of degree six in `r`
(`ssForcing_eq_srcForcing`). Its horizon value `srcForcing s μ 1 = −N(1)/(4(2−μ))` is explicit
(`srcForcing_horizon`), and at the physical harmonic `μ = (s+1)(s+2)` the factor `s` of `N` cancels
the zero of `2 − μ = −s(s+3)` (`srcForcing_physical_horizon`). The leading growth at the AdS
boundary is `r³/8`, independent of the rate.
-/

set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry.TwistedRadial Set
open scoped ContDiff
noncomputable section

/-- The pole-free scalar–scalar forcing `−N(r)/(4r³(2−μ))` as a Horner radial function. -/
def srcForcing (s μ : ℂ) : ℝ → ℂ :=
  ratCoef [(((9 / 4 : ℂ) * s ^ (2 : ℕ) + (-9 / 16 : ℂ) * s ^ (2 : ℕ) * μ + (1 / 32 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (75 / 8 : ℂ) * s ^ (3 : ℕ) + (-7 / 4 : ℂ) * s ^ (3 : ℕ) * μ + (1 / 16 : ℂ) * s ^ (3 : ℕ) * μ ^ (2 : ℕ) + (129 / 8 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * μ + (1 / 32 : ℂ) * s ^ (4 : ℕ) * μ ^ (2 : ℕ) + (59 / 4 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) * μ + (61 / 8 : ℂ) * s ^ (6 : ℕ) + (-3 / 16 : ℂ) * s ^ (6 : ℕ) * μ + (17 / 8 : ℂ) * s ^ (7 : ℕ) + (1 / 4 : ℂ) * s ^ (8 : ℕ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s + (-1 / 2 : ℂ) * s * μ + (-1 / 4 : ℂ) * s * μ ^ (2 : ℕ) + (5 / 8 : ℂ) * s ^ (2 : ℕ) + (9 / 16 : ℂ) * s ^ (2 : ℕ) * μ + (-5 / 8 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-79 / 8 : ℂ) * s ^ (3 : ℕ) + (17 / 8 : ℂ) * s ^ (3 : ℕ) * μ + (-27 / 2 : ℂ) * s ^ (4 : ℕ) + (29 / 16 : ℂ) * s ^ (4 : ℕ) * μ + (-51 / 8 : ℂ) * s ^ (5 : ℕ) + (-11 / 8 : ℂ) * s ^ (6 : ℕ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ) * μ + (-1 / 4 : ℂ) * μ ^ (2 : ℕ) + (1 : ℂ) * s + (-1 / 2 : ℂ) * s * μ + (-2 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ)))] 3 0

theorem srcForcing_eq_srcMaster (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0)
    (hμ : (2 : ℂ) - μ ≠ 0) :
    srcForcing s μ r = -(((r : ℂ) ^ (2 : ℕ) * ((r : ℂ) ^ (2 : ℕ) - 1)) / 4) * srcMaster s μ r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold srcForcing srcMaster
  simp only [ratCoef, horner]
  field_simp
  ring

/-- On the horizon coordinate interval the Green forcing is the pole-free forcing at the exterior
radius. -/
theorem ssForcing_eq_srcForcing (s μ : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    ssForcing s μ z = srcForcing s μ (rOfZ z) := by
  unfold ssForcing
  rw [srcForcing_eq_srcMaster s μ (one_lt_rOfZ hz) hs hμ]

/-- The forcing is smooth on the whole closed-horizon exterior `r ≥ 1`, in particular at `r = 1`. -/
theorem srcForcing_contDiffOn (s μ : ℂ) : ContDiffOn ℝ ∞ (srcForcing s μ) (Ioi 1) :=
  contDiffOn_ratCoef _ _ _

/-- Horizon value of the scalar–scalar forcing. -/
theorem srcForcing_horizon (s μ : ℂ) (hμ : (2 : ℂ) - μ ≠ 0) :
    srcForcing s μ 1 = ((1 : ℂ) + (-1 / 4 : ℂ) * μ ^ (2 : ℕ) + (3 : ℂ) * s + (-1 : ℂ) * s * μ + (-1 / 4 : ℂ) * s * μ ^ (2 : ℕ) + (7 / 8 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * μ + (-19 / 32 : ℂ) * s ^ (2 : ℕ) * μ ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 8 : ℂ) * s ^ (3 : ℕ) * μ + (1 / 16 : ℂ) * s ^ (3 : ℕ) * μ ^ (2 : ℕ) + (21 / 8 : ℂ) * s ^ (4 : ℕ) + (-3 / 16 : ℂ) * s ^ (4 : ℕ) * μ + (1 / 32 : ℂ) * s ^ (4 : ℕ) * μ ^ (2 : ℕ) + (67 / 8 : ℂ) * s ^ (5 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) * μ + (25 / 4 : ℂ) * s ^ (6 : ℕ) + (-3 / 16 : ℂ) * s ^ (6 : ℕ) * μ + (17 / 8 : ℂ) * s ^ (7 : ℕ) + (1 / 4 : ℂ) * s ^ (8 : ℕ)) / (2 - μ) := by
  unfold srcForcing
  simp only [ratCoef, horner]
  push_cast
  field_simp
  ring

/-- At the physical harmonic `μ = (s+1)(s+2)` the horizon value is regular at `s = 0`: the factor
`s` of the numerator cancels the zero of `2 − μ = −s(s+3)`. -/
theorem srcForcing_physical_horizon (s : ℂ) (hs : s ≠ 0) (h3 : s + 3 ≠ 0) :
    srcForcing s ((s + 1) * (s + 2)) 1 =
      ((3 : ℂ) + (35 / 4 : ℂ) * s + (75 / 8 : ℂ) * s ^ (2 : ℕ) + (135 / 32 : ℂ) * s ^ (3 : ℕ) + (-57 / 16 : ℂ) * s ^ (4 : ℕ) +
        (-23 / 8 : ℂ) * s ^ (5 : ℕ) + (-13 / 16 : ℂ) * s ^ (6 : ℕ) + (-3 / 32 : ℂ) * s ^ (7 : ℕ)) / (s + 3) := by
  have hμ : (2 : ℂ) - (s + 1) * (s + 2) ≠ 0 := by
    have : (2 : ℂ) - (s + 1) * (s + 2) = -(s * (s + 3)) := by ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero hs h3)
  rw [srcForcing_horizon s _ hμ]
  field_simp
  ring

end
end RHTower.D4BMScalarStream
