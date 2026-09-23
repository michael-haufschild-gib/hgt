import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamMasterIdentity

/-!
# The harmonic scalar stream: operator components as the seven Kodama–Ishibashi coefficients

For the scalar-stream jet at time rate `2s` whose angular jet satisfies the eigen-relation
`Pyy = μ P / y² − Pxx` (`ΔY = μ Y`), every component of the linearized cosmological Einstein
operator is one of the seven coefficient functions of `ThetaCuspHawkingBMScalarStreamMasterIdentity`
times the corresponding angular structure: `Y` on the orbit block, `∂Y` on the mixed block, `Y γ_ij`
and the trace-free covariant Hessian of `Y` on the angular block. Together with `master_identity`
this is the sourced master equation of the scalar sector on the Birmingham–Mokhtari background.
-/

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section
variable {s r y μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ}

local notation "K" => metricJet (2 * s) r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy
local notation "J" => D4BMBackground.jet r y

theorem harmonic_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (hP : Pyy = μ * P / y ^ (2 : ℕ) - Pxx) :
    Linearization.cosmological J K (-3) 0 0 = harmonicTT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * P := by
  rw [metricJet_cosmological_0_0 hr hy hf]; rw [hP]; unfold harmonicTT; field_simp
  ring

theorem harmonic_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (hP : Pyy = μ * P / y ^ (2 : ℕ) - Pxx) :
    Linearization.cosmological J K (-3) 0 1 = harmonicTR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * P := by
  rw [metricJet_cosmological_0_1 hr hy hf]; rw [hP]; unfold harmonicTR; field_simp
  ring

theorem harmonic_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (hP : Pyy = μ * P / y ^ (2 : ℕ) - Pxx) :
    Linearization.cosmological J K (-3) 1 1 = harmonicRR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * P := by
  rw [metricJet_cosmological_1_1 hr hy hf]; rw [hP]; unfold harmonicRR; field_simp
  ring

theorem harmonic_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological J K (-3) 0 2 = harmonicT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * Px := by
  rw [metricJet_cosmological_0_2 hr hy hf]; unfold harmonicT; field_simp

theorem harmonic_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological J K (-3) 0 3 = harmonicT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * Py := by
  rw [metricJet_cosmological_0_3 hr hy hf]; unfold harmonicT; field_simp

theorem harmonic_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological J K (-3) 1 2 = harmonicR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * Px := by
  rw [metricJet_cosmological_1_2 hr hy hf]; unfold harmonicR; field_simp

theorem harmonic_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological J K (-3) 1 3 = harmonicR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * Py := by
  rw [metricJet_cosmological_1_3 hr hy hf]; unfold harmonicR; field_simp

theorem harmonic_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological J K (-3) 2 3 = harmonicTF s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * (Pxy + Px / y) := by
  rw [metricJet_cosmological_2_3 hr hy hf]; unfold harmonicTF; field_simp
  ring

theorem harmonic_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0)
    (hP : Pyy = μ * P / y ^ (2 : ℕ) - Pxx) :
    Linearization.cosmological J K (-3) 2 2 =
      harmonicL s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * P / y ^ (2 : ℕ) + harmonicTF s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * (Pxx - Py / y - μ * P / (2 * y ^ (2 : ℕ))) := by
  rw [metricJet_cosmological_2_2 hr hy hf]; rw [hP]; unfold harmonicL harmonicTF; field_simp
  ring

theorem harmonic_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological J K (-3) 3 3 =
      harmonicL s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * P / y ^ (2 : ℕ) - harmonicTF s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 * (Pxx - Py / y - μ * P / (2 * y ^ (2 : ℕ))) := by
  rw [metricJet_cosmological_3_3 hr hy hf]; unfold harmonicL harmonicTF; field_simp
  ring

end
end RHTower.D4BMScalarStream
