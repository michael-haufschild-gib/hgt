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

/-- **The explicit branch is a `2^n`-th root of `φ_c ∘ f^[n]`**: `(explicitBranch c n z)^{2^n} =
bottcherCoord c (f_c^[n] z)`. (Exponentiating `exp(2⁻ⁿ·bottcherLog(f^[n]z))` to the `2^n`.) -/
theorem explicitBranch_pow (c : ℂ) (n : ℕ) (z : ℂ) :
    (explicitBranch c n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z) := by
  rw [explicitBranch, bottcherCoord, ← Complex.exp_nat_mul]
  congr 1
  have h2n : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero n two_ne_zero
  push_cast
  field_simp

/-- **The explicit branch is a root-of-unity sheet of `φ_c` on the escape regime.** On `escapeOpen c`,
`explicitBranch c n z = ζ · bottcherCoord c z` for a `2^n`-th root of unity `ζ` — the dyadic monodromy
sheet. (From `explicitBranch_pow` + `bottcherCoord_iterate`: both `2^n`-th powers equal `φ_c(z)^{2^n}`.)
Selecting the `ζ = 1` sheet globally across the connected basin is exactly Böttcher single-valuedness. -/
theorem explicitBranch_isRootOfUnity_smul (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ escapeOpen c) :
    ∃ ζ : ℂ, ζ ^ (2 ^ n) = 1 ∧ explicitBranch c n z = ζ * bottcherCoord c z := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  refine ⟨explicitBranch c n z / bottcherCoord c z, ?_, ?_⟩
  · rw [div_pow, explicitBranch_pow, bottcherCoord_iterate hc hz2 n, div_self
      (pow_ne_zero _ (bottcherCoord_ne_zero c z))]
  · rw [div_mul_cancel₀ _ (bottcherCoord_ne_zero c z)]

/-- **Functional equation of the explicit branch**: `explicitBranch c n (z²+c) = (explicitBranch c (n+1) z)²`.
The level-`n` branch at `f_c z` is the square of the level-`(n+1)` branch at `z` — the explicit-branch
form of `φ_c(z²+c) = φ_c(z)²`, the consistency that threads the levels into one continuation. -/
theorem explicitBranch_quadratic (c : ℂ) (n : ℕ) (z : ℂ) :
    explicitBranch c n (quadratic c z) = (explicitBranch c (n + 1) z) ^ (2 : ℕ) := by
  rw [explicitBranch, explicitBranch, ← Complex.exp_nat_mul]
  congr 1
  rw [show (quadratic c)^[n] (quadratic c z) = (quadratic c)^[n + 1] z from
      (Function.iterate_succ_apply (quadratic c) n z).symm]
  push_cast
  ring

/-- `explicitBranch c 0 = bottcherCoord c` — the base level is `φ_c` itself. -/
theorem explicitBranch_zero (c : ℂ) : explicitBranch c 0 = bottcherCoord c := by
  funext z
  rw [explicitBranch, bottcherCoord]
  norm_num

/-- On the escape regime the explicit branch's relation equals the relation evaluated at its sheet
`ζ·φ_c` (`ζ^{2^n}=1`). The hook by which a sheet inherits `φ_c`'s minimal relation when the sheet rotation
is a Galois conjugacy (the dyadic case). -/
theorem explicitBranch_relation_eq_sheet (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) :
    ∃ ζ : ℂ, ζ ^ (2 ^ n) = 1 ∧
      (∑ i ∈ P.support, (P.coeff i).aeval z * (explicitBranch c n z) ^ i)
        = ∑ i ∈ P.support, (P.coeff i).aeval z * (ζ * bottcherCoord c z) ^ i := by
  obtain ⟨ζ, hζ, hsmul⟩ := explicitBranch_isRootOfUnity_smul c n hz
  exact ⟨ζ, hζ, by rw [hsmul]⟩

end Bottcher
