/-
The zero-density engine: the Littlewood gap-counting reduction that turns a zero-density estimate
into `RH₂`, and the exact separation between the Bohr–Landau `O(T)` bound and the Ingham/Carlson
`o(T)` bound that the reduction requires.

Every zero-density argument has the same skeleton.  Let `N T` count the ξ-zeros right of a line
`Re s = σ₀ > 1/2` up to height `T`.  Littlewood's lemma bounds this count by a log-modulus integral on
a line `Re s = σ₁ < σ₀` a fixed gap `δ = σ₀ − σ₁ > 0` to the left:

  δ · N T ≤ Λ T + o(T),     Λ T = ∫₀ᵀ log⁺ |ξ(σ₁ + it)| dt.

The density of zeros is then controlled by the *growth of the log-integral* `Λ`:

* **Bohr–Landau** (`boundedDensity_of_gapCounting`).  A finite mean value `∫₀ᵀ |ξ(σ₁+it)|² dt ≪ T`
  gives, by Jensen's inequality, `Λ T ≪ T`, hence `N T ≤ (B/δ) · T`.  This is `O(T)` — a linear
  density bound.
* **Ingham/Carlson** (`subLinearDensity_of_gapCounting`).  The *fourth* moment gives the sharper
  `Λ T = o(T)`, hence `N T = o(T)` — a sublinear density bound.

The distinction is decisive here.  The recurrence contradiction (`rhLadder_one_of_recurrence_of_density`)
needs a *sublinear* upper bound to beat the linear lower bound a defect would create: Bohr–Landau's
`O(T)` is not enough (`bohrLandau_insufficient_for_recurrence`), only Carlson's `o(T)` is.  The
composite `rhLadder_one_of_recurrence_gapCounting` assembles the whole chain: recurrence + Littlewood
gap-counting + Carlson sublinear log-integral ⟹ `RHLadder 1`.

This file proves the reduction skeleton in full.  The two analytic inputs it consumes are exactly the
classical kernels absent from mathlib: **Littlewood's lemma for ξ** (`GapCounting` — connectable to the
rectangle contour count `completedGN_rectIntegral_logDeriv`) and **Carlson's `o(T)` log-integral**
(`SubLinearDensity Λ` — the fourth-moment mean value via the approximate functional equation).
-/
import GaloisForLFunctions.RHTower.QuadrantSeamConservation

namespace RHTower

/-- **Littlewood gap-counting.**  The right-of-`σ₀` zero count `N` is bounded, up to the positive gap
`δ = σ₀ − σ₁`, by a log-modulus integral `Λ` on the line `σ₁`: `δ · N T ≤ Λ T` for all large `T`.
This is the counting half of every zero-density theorem (Littlewood's lemma), stated as an interface
because its proof for ξ is the rectangle argument-principle count, not yet wired to `Λ`. -/
def GapCounting (N Λ : ℝ → ℝ) (δ : ℝ) : Prop := ∃ T₀, ∀ T ≥ T₀, δ * N T ≤ Λ T

/-- **Sublinear density from a sublinear log-integral** (the Carlson step).  If the count is
gap-bounded by a log-integral with a positive gap and the log-integral is `o(T)`, the count is `o(T)`.
Carlson's fourth-moment estimate makes `Λ` sublinear; this transports the sublinearity to `N`. -/
theorem subLinearDensity_of_gapCounting {N Λ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : GapCounting N Λ δ) (hΛ : SubLinearDensity Λ) : SubLinearDensity N := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hgap
  obtain ⟨T₁, hT₁⟩ := hΛ (ε * δ) (by positivity)
  refine ⟨max T₀ T₁, fun T hT => ?_⟩
  have h0 : δ * N T ≤ Λ T := hT₀ T (le_trans (le_max_left _ _) hT)
  have h1 : Λ T ≤ (ε * δ) * T := hT₁ T (le_trans (le_max_right _ _) hT)
  nlinarith [h0, h1, hδ]

/-- **Bohr–Landau (linear density).**  If the log-integral is only linearly bounded `Λ T ≤ B · T`
(the second-moment/Jensen bound), the count obeys `N T ≤ (B/δ) · T`.  This is `O(T)` — sharp for the
second moment, but not sublinear. -/
theorem boundedDensity_of_gapCounting {N Λ : ℝ → ℝ} {δ B : ℝ} (hδ : 0 < δ)
    (hgap : GapCounting N Λ δ) (hB : ∃ T₁, ∀ T ≥ T₁, Λ T ≤ B * T) :
    ∃ T₂, ∀ T ≥ T₂, N T ≤ (B / δ) * T := by
  obtain ⟨T₀, hT₀⟩ := hgap
  obtain ⟨T₁, hT₁⟩ := hB
  refine ⟨max T₀ T₁, fun T hT => ?_⟩
  have h0 : δ * N T ≤ Λ T := hT₀ T (le_trans (le_max_left _ _) hT)
  have h1 : Λ T ≤ B * T := hT₁ T (le_trans (le_max_right _ _) hT)
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  nlinarith [h0, h1]

/-- **A linear density bound cannot close the recurrence contradiction.**  A count that is only
linearly bounded above by `A · T` with `A ≥ c` is fully consistent with a linear lower bound `c · T`:
there is no contradiction.  This is why the reduction needs Carlson's sublinear bound, not merely
Bohr–Landau's linear one — the `O(T)` face is genuinely insufficient. -/
theorem bohrLandau_insufficient_for_recurrence {c A : ℝ} (hcA : c ≤ A) :
    ∃ N : ℝ → ℝ, LinearLowerBound N c ∧ (∃ T₂, ∀ T ≥ T₂, N T ≤ A * T) := by
  refine ⟨fun T => A * T, ⟨0, fun T hT => ?_⟩, ⟨0, fun T _ => le_refl _⟩⟩
  nlinarith [hcA, hT]

/-- **The reduced `RH₂` chain.**  Assemble the density reduction with the recurrence contradiction.
Given a putative right-half zero count `N` and a log-integral `Λ`:

* **Defect recurrence** — a single odd right-half zero forces a positive linear lower bound on `N`;
* **Littlewood gap-counting** — `N` is `δ`-gap-bounded by `Λ`;
* **Carlson density** — `Λ` is `o(T)`;

then every right-half ξ-zero has even multiplicity: `RHLadder 1`.  The three hypotheses are the exact
open/classical kernels: replication (open core), Littlewood's lemma for ξ (classical, connectable to
the project's rectangle contour count), and Carlson's fourth-moment `o(T)` estimate (classical, absent
from mathlib). -/
theorem rhLadder_one_of_recurrence_gapCounting {N Λ : ℝ → ℝ} {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hrec : (∃ ρ, XiDefect ρ) → LinearLowerBound N c)
    (hgap : GapCounting N Λ δ) (hΛ : SubLinearDensity Λ) : RHLadder 1 :=
  rhLadder_one_of_recurrence_of_density hc hrec
    (subLinearDensity_of_gapCounting hδ hgap hΛ)

end RHTower
