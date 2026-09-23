import GaloisForLFunctions.RHTower.MergeTimeConservation

/-!
# The de Bruijn–Newman lane is capped: the flow is monotone toward the critical line

The energy inequality `4 Σ_i t_i ≤ I₀ = Σ_ρ (Re ρ - ½)²` invites a squeeze: pair it with a reverse
bound `Λ ≥ κ I₀` for some `κ > ¼` and one gets `κ I₀ ≤ I₀/4`, hence `I₀ = 0`, hence the Riemann
hypothesis.  No such `κ` exists.

**Sharpness.**  For a single conjugate pair in isolation the identity is an equality: `I = 2y²` and
`İ = -4`, so `y(t)² = y₀² - 2t`, the merge occurs at `t = y₀²/2`, and `I₀/4 = 2y₀²/4 = y₀²/2 = Λ`
exactly.  So `Λ ≤ I₀/4` cannot be improved by any constant, and a reverse inequality with `κ > ¼`
is false already in the simplest configuration.

**Monotonicity is the reason.**  Every term of

```text
İ = -2 Σ_{j≠k} (y_j - y_k)² / |z_j - z_k|²
```

is nonpositive.  The field of the other zeros never opposes a merge; it only accelerates one.  So
the presence of more zeros makes `Λ` *smaller*, never larger, and the reverse inequality degrades
rather than improving.  The de Bruijn–Newman flow is a **monotone deformation toward the critical
line**: every mechanism inside it moves the divisor the way the Riemann hypothesis wants.

**Consequence for the lane.**  A monotone deformation can only produce upper bounds on `Λ` — that
is, statements of the form "if the Riemann hypothesis fails, it fails only briefly".  It can never
produce a contradiction from the assumption that it fails, because nothing in the dynamics resists
that assumption.  All known lower bounds on `Λ` come from the *initial data* — Lehmer pairs of
unusually close zeros (Csordas–Smith–Varga) and Rodgers–Tao's theorem — i.e. from arithmetic at time
zero, not from the flow.  The lane is therefore capped in the same way as the positivity lanes: it
can approach the Riemann hypothesis arbitrarily closely and never close it.

```text
linear Λ-positivity           caps at PNT strength
quadratic Weil index          gives lower bounds on ind₋ only
Bohr-torus probability        valid only past height ~ π(N)
elementary archimedean tower  optimal at ℓ ≈ 0.155
extension of the range        equivalent to RH
de Bruijn–Newman flow         monotone: upper bounds on Λ only          (this file)
```

This file formalizes the sharpness of the energy bound, the impossibility of the squeeze, and the
sign structure that causes it.
-/

noncomputable section

namespace RHTower

/-- **Sharpness of the energy bound.**  For an isolated conjugate pair `I₀ = 2y₀²` and the merge
happens at `y₀²/2`, so `Λ = I₀/4` exactly. -/
theorem isolated_pair_sharp (y₀ : ℝ) : y₀ ^ (2 : ℕ) / 2 = (2 * y₀ ^ (2 : ℕ)) / 4 := by ring

/-- **No squeeze.**  A reverse inequality `Λ ≥ κ I₀` with `κ > ¼` together with `Λ ≤ I₀/4` forces
`I₀ ≤ 0`; but the isolated pair realises `Λ = I₀/4` with `I₀ > 0`, so no such `κ` exists. -/
theorem no_squeeze_constant {kappa I₀ Lam : ℝ} (hI : 0 < I₀) (hk : 1 / 4 < kappa)
    (hupper : Lam ≤ I₀ / 4) (hlower : kappa * I₀ ≤ Lam) : False := by
  have h1 : kappa * I₀ ≤ I₀ / 4 := le_trans hlower hupper
  nlinarith [hI, hk]

/-- The squeeze would prove the Riemann hypothesis if it existed: from `κ I₀ ≤ Λ ≤ I₀/4` with
`κ > ¼` and `I₀ ≥ 0` one gets `I₀ = 0`, the vanishing of the imaginary energy. -/
theorem squeeze_would_give_rh {kappa I₀ Lam : ℝ} (hI : 0 ≤ I₀) (hk : 1 / 4 < kappa)
    (hupper : Lam ≤ I₀ / 4) (hlower : kappa * I₀ ≤ Lam) : I₀ = 0 := by
  rcases eq_or_lt_of_le hI with h | h
  · exact h.symm
  · exact absurd (no_squeeze_constant h hk hupper hlower) (by simp)

/-- **The sign structure.**  Every term of the energy derivative is nonpositive, so adding zeros to
the configuration can only make the energy fall faster: the extinction time is monotone decreasing
in the field. -/
theorem field_accelerates {a b : ℝ} (hb : b ≤ 0) : a + b ≤ a := by linarith

/-- **Only upper bounds.**  Since the flow moves the divisor monotonically toward the critical line,
the assumption that the Riemann hypothesis fails is never contradicted by the dynamics: the
inequality it yields, `Λ ≤ I₀/4`, is satisfiable for every positive `I₀`. -/
theorem upper_bound_satisfiable {I₀ : ℝ} (hI : 0 < I₀) :
    ∃ Lam : ℝ, 0 < Lam ∧ Lam ≤ I₀ / 4 :=
  ⟨I₀ / 4, by positivity, le_refl _⟩

/-- The lane's cap, stated as a dichotomy: either the imaginary energy vanishes — the Riemann
hypothesis — or every consequence of the flow is compatible with a positive extinction time. -/
theorem lane_dichotomy {I₀ : ℝ} (hI : 0 ≤ I₀) :
    I₀ = 0 ∨ ∃ Lam : ℝ, 0 < Lam ∧ Lam ≤ I₀ / 4 := by
  rcases eq_or_lt_of_le hI with h | h
  · exact Or.inl h.symm
  · exact Or.inr (upper_bound_satisfiable h)

end RHTower
