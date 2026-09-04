import GaloisForLFunctions.RHTower.RouteJTwoIndexResidual
import GaloisForLFunctions.RHTower.RouteJBeatModeProfile

/-!
# The uniform law of the Route J residual

`J_k(δ) = M_k(δ) + E_k(δ)` with the **uniform main term**

`M_k(δ) = (cosh δ)^{-1/2} · 2 (2 sin φ)^{-1/2} · [a(k,σ) C_{4k+3} cos θ_{k,3} + b(k,σ) C_{4k+4} cos θ_{k,4}]`

(`σ = sech δ`, `φ = arccos σ`, `θ_{k,j} = (4k + j + ½) φ − π/4`, `a, b` the two-index coefficients)
and the explicit error `|E_k(δ)| ≤ (cosh δ)^{-1/2} (|a| + |b|) · 400 / (sin φ · (4k+3))` for all
`δ > 0`, `k ≥ 2`.  The beat law (`k → ∞`, `δ` fixed) and the scaling profile `Φ`
(`2k sech δ → X`) are the two limits of `M_k(δ)`; see `RouteJUniformLawLimits`.
-/

open Filter Topology Finset
open scoped Real

namespace RHTower
namespace RouteJUniform

open LegendreBoost RouteJProfile CosineModeResponse RouteJBeatMode

/-- The uniform main term. -/
noncomputable def uniformMain (δ : ℝ) (k : ℕ) : ℝ :=
  Real.cosh δ ^ (-(1 / 2 : ℝ)) * (2 * beatSfac δ) *
    (twoIndexA k (1 / Real.cosh δ) * cb (4 * k + 3) * Real.cos (beatPhase δ k 3) +
      twoIndexB k (1 / Real.cosh δ) * cb (4 * k + 4) * Real.cos (beatPhase δ k 4))

theorem legendre_beat_err_le {δ : ℝ} (hδ : 0 < δ) {k j : ℕ} (hN : 8 ≤ 4 * k + j) :
    |legendre (4 * k + j) (1 / Real.cosh δ) -
        2 * cb (4 * k + j) * beatSfac δ * Real.cos (beatPhase δ k j)| ≤
      400 / (Real.sin (beatAngle δ) * ((4 * k + j : ℕ) : ℝ)) := by
  have h := legendre_laplaceHeine (beatAngle_pos hδ) (beatAngle_lt_pi δ) hN
  rw [cos_beatAngle] at h
  unfold beatSfac beatPhase
  exact h

/-- **The uniform law.**  For every `δ > 0` and `k ≥ 2`,
`|J_k(δ) − M_k(δ)| ≤ (cosh δ)^{-1/2} (|a| + |b|) · 400/(sin φ (4k+3))`. -/
theorem abs_residual_sub_uniformMain_le {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 2 ≤ k) :
    |residualJetOf (cosineModeDeterminantJet δ) k - uniformMain δ k| ≤
      Real.cosh δ ^ (-(1 / 2 : ℝ)) *
        (|twoIndexA k (1 / Real.cosh δ)| + |twoIndexB k (1 / Real.cosh δ)|) *
        (400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3))) := by
  rw [residual_eq_twoIndex]
  unfold uniformMain
  have h3 := legendre_beat_err_le hδ (k := k) (j := 3) (by omega)
  have h4 := legendre_beat_err_le hδ (k := k) (j := 4) (by omega)
  have hs := sin_beatAngle_pos hδ
  have hk3 : (0 : ℝ) < 4 * k + 3 := by positivity
  have h4' : 400 / (Real.sin (beatAngle δ) * ((4 * k + 4 : ℕ) : ℝ)) ≤
      400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    push_cast
    nlinarith
  have h3' : 400 / (Real.sin (beatAngle δ) * ((4 * k + 3 : ℕ) : ℝ)) =
      400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3)) := by push_cast; rfl
  rw [h3'] at h3
  set a := twoIndexA k (1 / Real.cosh δ)
  set b := twoIndexB k (1 / Real.cosh δ)
  set e3 := legendre (4 * k + 3) (1 / Real.cosh δ) -
    2 * cb (4 * k + 3) * beatSfac δ * Real.cos (beatPhase δ k 3) with he3
  set e4 := legendre (4 * k + 4) (1 / Real.cosh δ) -
    2 * cb (4 * k + 4) * beatSfac δ * Real.cos (beatPhase δ k 4) with he4
  have hid : Real.cosh δ ^ (-(1 / 2 : ℝ)) *
      (a * legendre (4 * k + 3) (1 / Real.cosh δ) + b * legendre (4 * k + 4) (1 / Real.cosh δ)) -
      Real.cosh δ ^ (-(1 / 2 : ℝ)) * (2 * beatSfac δ) *
        (a * cb (4 * k + 3) * Real.cos (beatPhase δ k 3) +
          b * cb (4 * k + 4) * Real.cos (beatPhase δ k 4)) =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) * (a * e3 + b * e4) := by
    rw [he3, he4]; ring
  rw [hid, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos δ).le _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.cosh_pos δ).le _)
  have hE : (400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3))) ≥ 0 := by positivity
  calc |a * e3 + b * e4| ≤ |a| * |e3| + |b| * |e4| := by
        calc |a * e3 + b * e4| ≤ |a * e3| + |b * e4| := abs_add_le _ _
          _ = |a| * |e3| + |b| * |e4| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * (400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3))) +
        |b| * (400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3))) := by
        gcongr
        exact h4.trans h4'
    _ = (|a| + |b|) * (400 / (Real.sin (beatAngle δ) * (4 * (k : ℝ) + 3))) := by ring

end RouteJUniform
end RHTower
