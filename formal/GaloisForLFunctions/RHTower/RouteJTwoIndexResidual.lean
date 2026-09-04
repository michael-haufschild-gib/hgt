import GaloisForLFunctions.RHTower.LegendreShiftReduction
import GaloisForLFunctions.RHTower.SemilocalDiagonalLegendre

/-!
# The Route J residual as an exact two-index Legendre combination

`residualJetOf (cosineModeDeterminantJet δ) k
   = (cosh δ)^{-1/2} · (a(k, σ) P_{4k+3}(σ) + b(k, σ) P_{4k+4}(σ))`,  `σ = sech δ`,

with `a = R₁ a₁ + R₂ a₂ + a₀`, `b = R₁ b₁ + R₂ b₂ + b₀`, `R₁ = r_{2k} r_{2k+1}`, `R₂ = r_{2k+2} r_{2k+3}`
and explicit rational `a_i, b_i`.  The leading behaviour `a ≈ 64 k² σ (1−σ²)`, `b ≈ −64 k² σ² (1−σ²)`
carries the beat law; the next order `a ≈ 136 k σ(1−σ²)`, `b ≈ 8k(1−σ²)(1−22σ²)` carries the
`√X cos 4X` term of the scaling profile.  All cancellations of the five-term Legendre form are
performed by the recurrence, so a first-order Laplace–Heine estimate becomes uniform.
-/

open Finset

namespace RHTower
namespace RouteJUniform

open LegendreBoost RouteJProfile CosineModeResponse

noncomputable def coefAR1 (k s : ℝ) : ℝ := -(shA0 k s)
noncomputable def coefAR2 (k s : ℝ) : ℝ := shA8 k s
noncomputable def coefA0 (k s : ℝ) : ℝ := 4 * s * (k + 1) * (8 * k + 9)
noncomputable def coefBR1 (k s : ℝ) : ℝ := 1 - shB0 k s
noncomputable def coefBR2 (k s : ℝ) : ℝ := shB8 k s - 1
noncomputable def coefB0 (k s : ℝ) : ℝ := -(8 * k + 9) * (8 * k * s ^ 2 + 11 * s ^ 2 - 3) / 2

/-- `R₁ = r_{2k} r_{2k+1}`. -/
noncomputable def radProd1 (k : ℕ) : ℝ :=
  semilocalArchimedeanJacobiCoefficient (2 * k) * semilocalArchimedeanJacobiCoefficient (2 * k + 1)
/-- `R₂ = r_{2k+2} r_{2k+3}`. -/
noncomputable def radProd2 (k : ℕ) : ℝ :=
  semilocalArchimedeanJacobiCoefficient (2 * k + 2) * semilocalArchimedeanJacobiCoefficient (2 * k + 3)

noncomputable def twoIndexA (k : ℕ) (s : ℝ) : ℝ :=
  radProd1 k * coefAR1 k s + radProd2 k * coefAR2 k s + coefA0 k s
noncomputable def twoIndexB (k : ℕ) (s : ℝ) : ℝ :=
  radProd1 k * coefBR1 k s + radProd2 k * coefBR2 k s + coefB0 k s

theorem coefA0_eq (k : ℕ) (s : ℝ) :
    coefA0 k s = 2 * ((2 * (k : ℝ) + 1 + 1 / 2) * (2 * (k : ℝ) + 1 + 1)) * shA2 k s -
      2 * ((2 * (k : ℝ) + 2 + 1 / 2) * (2 * (k : ℝ) + 2 + 1)) * shA6 k s := by
  unfold coefA0 shA2 shA6
  have h1 : (0 : ℝ) < 4 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 3 := by positivity
  field_simp
  ring

theorem coefB0_eq (k : ℕ) (s : ℝ) :
    coefB0 k s = -2 * ((2 * (k : ℝ) + 1 + 1 / 2) * (2 * (k : ℝ) + 1 + 1)) * (1 - shB2 k s) -
      2 * ((2 * (k : ℝ) + 2 + 1 / 2) * (2 * (k : ℝ) + 2 + 1)) * (shB6 k s - 1) := by
  unfold coefB0 shB2 shB6
  have h1 : (0 : ℝ) < 4 * k + 3 := by positivity
  have h2 : (0 : ℝ) < 4 * k + 5 := by positivity
  have h3 : (0 : ℝ) < 2 * k + 3 := by positivity
  field_simp
  ring

/-- **The residual jet is an exact two-index Legendre combination.** -/
theorem residual_eq_twoIndex (δ : ℝ) (k : ℕ) :
    residualJetOf (cosineModeDeterminantJet δ) k =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) *
        (twoIndexA k (1 / Real.cosh δ) * legendre (4 * k + 3) (1 / Real.cosh δ) +
          twoIndexB k (1 / Real.cosh δ) * legendre (4 * k + 4) (1 / Real.cosh δ)) := by
  rw [residualJetOf_cosineMode_eq_legendre, legendre_shift0, legendre_shift2, legendre_shift6,
    legendre_shift8, semilocalArchimedeanJacobiCoefficient_sq (2 * k + 1),
    semilocalArchimedeanJacobiCoefficient_sq (2 * k + 2)]
  unfold twoIndexA twoIndexB radProd1 radProd2 coefAR1 coefAR2 coefBR1 coefBR2
  rw [coefA0_eq, coefB0_eq]
  push_cast
  ring

end RouteJUniform
end RHTower
