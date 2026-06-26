/-
# Local analytic inverse of the Böttcher coordinate (hDisc lift, L3 entry)

The dyadic-cover lift `hliftF`/`hliftG` (the genuine remaining analytic input of the disconnected case,
`Q62Assembly.noRelation_of_disconnected_lifts`) is built from **local sections** of `φ_c` glued along the
covering map `f_c^[n]`. The atomic ingredient is the local analytic inverse of `φ_c` near a point of the
escape region: since `φ_c` is analytic on `escapeOpen c` with non-vanishing derivative
(`FigureEight.logDeriv_bottcherCoord_ne_zero_escape` ⟹ `φ_c' ≠ 0`), the holomorphic inverse function
theorem gives an analytic `ψ` with `ψ ∘ φ_c = id` near `z₀` and `φ_c ∘ ψ = id` near `φ_c(z₀)`.

This is brick 1 of the `hDisc` lift (local section → glue along cover → deck map → figure-eight
independence). It does NOT by itself discharge `hliftF`; it supplies the local-inverse atom.
-/
import GaloisForLFunctions.Bottcher.FigureEight

open Filter Topology Complex

namespace Bottcher

/-- **`φ_c'(z) ≠ 0` on `escapeOpen c`** (the complex derivative): `logDeriv φ_c = φ_c'/φ_c ≠ 0`
(`logDeriv_bottcherCoord_ne_zero_escape`) and `φ_c ≠ 0`, so the numerator `φ_c'` is nonzero. -/
theorem deriv_bottcherCoord_ne_zero {c z : ℂ} (hz : z ∈ escapeOpen c) :
    deriv (bottcherCoord c) z ≠ 0 := by
  have hlog := logDeriv_bottcherCoord_ne_zero_escape hz
  rw [logDeriv_apply] at hlog
  intro h; rw [h, zero_div] at hlog; exact hlog rfl

/-- **Local analytic inverse of `φ_c` near ∞.** At any `z₀ ∈ escapeOpen c`, since `φ_c` is analytic with
`φ_c'(z₀) ≠ 0`, the holomorphic inverse function theorem gives an analytic local inverse `ψ`, with
`ψ ∘ φ_c = id` near `z₀` (`eventually_left_inverse`) and `φ_c ∘ ψ = id` near `φ_c(z₀)`
(`eventually_right_inverse`). The local-section atom for the dyadic-cover lift `hliftF`/`hliftG`. -/
theorem exists_localInverse_bottcherCoord {c z₀ : ℂ} (hz₀ : z₀ ∈ escapeOpen c) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (bottcherCoord c z₀) ∧
      (∀ᶠ z in 𝓝 z₀, ψ (bottcherCoord c z) = z) ∧
      (∀ᶠ w in 𝓝 (bottcherCoord c z₀), bottcherCoord c (ψ w) = w) := by
  have han : AnalyticAt ℂ (bottcherCoord c) z₀ := analyticOnNhd_bottcherCoord_full c z₀ hz₀
  have hd0 : deriv (bottcherCoord c) z₀ ≠ 0 := deriv_bottcherCoord_ne_zero hz₀
  have hsd : HasStrictDerivAt (bottcherCoord c) (deriv (bottcherCoord c) z₀) z₀ :=
    han.hasStrictDerivAt
  refine ⟨hsd.localInverse _ _ _ hd0, ?_, ?_, ?_⟩
  · exact han.analyticAt_localInverse hd0
  · exact hsd.eventually_left_inverse hd0
  · exact hsd.eventually_right_inverse hd0

end Bottcher
