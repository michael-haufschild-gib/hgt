/-
# The global logarithmic derivative `ω = φ_c'/φ_c` on the basin (Böttcher primitive setup)

The single-valued Böttcher coordinate `φ_c` on the (annular, π₁ = ℤ) connected basin is the obstruction
that gates the connected-case transcendence `hGtr` (and the dyadic lift `hDisc`). `log φ_c` is multivalued
(period `2πi` around `K_c`), but its **derivative** `φ_c'/φ_c = 2·∂G_c` is single-valued and holomorphic on
the whole basin — because `G_c` is harmonic there (`BasinBranching.harmonicOnNhd_greenLimit_basin`) and the
Wirtinger `∂`-derivative of a harmonic function is holomorphic
(`HarmonicAt.differentiableAt_complex_partial`).

This file constructs that global `ω` and records it is **conservative** (`DifferentiableOn.isConservativeOn`).
The single missing analytic step to single-valued `φ_c` on a *simply-connected* basin region `V` is then the
**Poincaré lemma** `IsConservativeOn ω V + IsSimplyConnected V ⟹ IsExactOn ω V`: a primitive `F` (with
`F' = ω`, hence `Re F = G_c` up to constant — the harmonic conjugate, `log φ_c`, so `φ_c = exp F`). Mathlib
provides exactness only on balls (`DifferentiableOn.isExactOn_ball`) and on `ℂ`; the simply-connected case is
the genuine remaining frontier brick. With it, `β := exp F` on a simply-connected basin neighbourhood of a
dendrite Julia point supplies both `hβmod` (`‖β‖ = exp G_c`) and — anchored to `escapeOpen` where it equals
`φ_c` — `hβrel`, feeding `ConnectedTranscendence.dendrite_branch_limit`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.HasPrimitives

open Complex Set

namespace Bottcher

/-- The **logarithmic derivative** `ω = φ_c'/φ_c = 2·∂G_c` — the Wirtinger `∂`-derivative of the Green's
function, single-valued on the basin even though `log φ_c` is not. -/
noncomputable def greenLogDeriv (c : ℂ) : ℂ → ℂ :=
  fun z => fderiv ℝ (greenLimit c) z 1 - Complex.I * fderiv ℝ (greenLimit c) z Complex.I

/-- **`ω` is holomorphic on the whole basin.** At each basin point `G_c` is harmonic
(`harmonicOnNhd_greenLimit_basin`), and the Wirtinger `∂`-derivative of a harmonic function is complex
differentiable (`HarmonicAt.differentiableAt_complex_partial`). -/
theorem differentiableOn_greenLogDeriv (c : ℂ) :
    DifferentiableOn ℂ (greenLogDeriv c) (filledJulia c)ᶜ := by
  intro z hz
  have hh := harmonicOnNhd_greenLimit_basin c z hz
  exact (HarmonicAt.differentiableAt_complex_partial hh).differentiableWithinAt

/-- **`ω` is conservative on the basin** (`DifferentiableOn.isConservativeOn`): all rectangle integrals
vanish. On any simply-connected basin region this upgrades — via the Poincaré lemma — to exactness, i.e. a
single-valued primitive `F = log φ_c` with `Re F = G_c`. -/
theorem isConservativeOn_greenLogDeriv (c : ℂ) :
    IsConservativeOn (greenLogDeriv c) (filledJulia c)ᶜ :=
  (differentiableOn_greenLogDeriv c).isConservativeOn

end Bottcher
