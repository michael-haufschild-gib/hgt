/-
# Explicit single-valued basin Böttcher branches (natural-boundary route, modulus side)

The natural-boundary contradiction (`STATUS.md`) needs, near a Julia point, a single-valued analytic
branch of `φ_c` on the basin with the genuine Böttcher modulus `‖·‖ = exp(G_c)`. The other agent's
`CoverConstruction.exists_greenConjugate_explicit` realizes such branches **explicitly**, level by level,
with NO abstract monodromy gluing:

> `explicitBranch c n z := exp(2⁻ⁿ · bottcherLog c (f_c^[n] z))` on
> `explicitDomain c n := {z | f_c^[n] z ∈ escapeOpen c ∩ slitPlane}`,

a single-valued analytic function (composition of the single-valued `bottcherLog` with the entire
iterate `f_c^[n]`), with `Re(2⁻ⁿ·bottcherLog∘f^[n]) = G_c`, hence `‖explicitBranch c n‖ = exp(G_c)`.
As `n → ∞` these domains reach arbitrarily deep into the basin toward `J_c`.

This file packages those branches as the engine-ready modulus datum (`norm_explicitBranch` is exactly the
`hmod` of `DendriteBoundary.no_continuation_dendrite`).

**The monodromy is not bypassed.** `explicitBranch c n` is a *2ⁿ-th root* of `bottcherCoord c ∘ f_c^[n]`
(via `bottcherCoord_quadratic` iterated), so it equals `bottcherCoord c` (the deep-exterior `φ_c`) only up
to a 2ⁿ-th root of unity `ζ` — the dyadic monodromy. Hence this branch is a *sheet* `ζ·φ_c`, and it carries
an algebraic relation `P(z, φ_c) = 0` only on the sheet where `ζ = 1`. Selecting that sheet globally across
the basin (`ζ ≡ 1`, the connected-`J_c` / trivial-monodromy condition) is the remaining analytic core,
owned by the basin-construction lane (`BasinConnected`/`BasinBranching`).
-/
import GaloisForLFunctions.Bottcher.CoverConstruction

open Complex Set Filter Topology

namespace Bottcher

/-- The explicit single-valued basin Böttcher branch `exp(2⁻ⁿ·bottcherLog c (f_c^[n] z))`. -/
noncomputable def explicitBranch (c : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => Complex.exp (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z))

/-- Its domain `{z | f_c^[n] z ∈ escapeOpen c ∩ slitPlane}` — a deep fundamental region in the basin. -/
def explicitDomain (c : ℂ) (n : ℕ) : Set ℂ :=
  {z : ℂ | (quadratic c)^[n] z ∈ escapeOpen c ∩ Complex.slitPlane}

/-- `explicitDomain c n` is open (preimage of an open set under the entire iterate `f_c^[n]`). -/
theorem isOpen_explicitDomain (c : ℂ) (n : ℕ) : IsOpen (explicitDomain c n) := by
  have hcont : Continuous ((quadratic c)^[n]) :=
    continuousOn_univ.mp (analyticOnNhd_quadratic_iterate c n).continuousOn
  exact hcont.isOpen_preimage _ ((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane)

/-- **The explicit basin branch is analytic** on its domain (`exp` of the analytic green-conjugate). -/
theorem analyticOnNhd_explicitBranch (c : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (explicitBranch c n) (explicitDomain c n) :=
  (exists_greenConjugate_explicit c n).1.cexp

/-- **The explicit basin branch carries the genuine Böttcher modulus** `‖·‖ = exp(G_c)` — exactly the
`hmod` datum `DendriteBoundary.no_continuation_dendrite` consumes, from a single-valued branch. -/
theorem norm_explicitBranch (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ explicitDomain c n) :
    ‖explicitBranch c n z‖ = Real.exp (greenFunctionDyn c z) := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz.1
  have hzK : z ∉ filledJulia c := not_mem_filledJulia_of_iterate n (not_mem_filledJulia hc hz2)
  have hre : (((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[n] z)).re = greenLimit c z :=
    (exists_greenConjugate_explicit c n).2 hz
  rw [explicitBranch, Complex.norm_exp, hre, greenFunctionDyn, if_neg hzK]

end Bottcher
