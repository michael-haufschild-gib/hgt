/-
# Natural boundary of u₀ at the unit circle

The function `u₀(z) = ∑_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}` has the unit circle `{|z|=1}` as
a natural boundary — it cannot be analytically continued across any arc of the unit circle.

## Proof strategy

Substituting `w = 1/z`, the companion series is `U₀(w) = u₀(1/w) = ∑_{n≥0} 2^{-(n+1)} w^{2^{n+1}-1}`.
- The exponents `2^{n+1}-1` satisfy `lim_{n→∞} λ_{n+1}/λ_n = 2 > 1`, so the series has
  **Hadamard gaps** (Ostrowski–Hadamard gap theorem).
- Every point on the unit circle `|w|=1` is a singular point of U₀.
- Equivalently, every point on the unit circle `|z|=1` is a singular point of u₀.

In Lean: the gap theorem is not yet in Mathlib (v4.30.0). The natural boundary is stated with the
genuine *analytic-continuation* predicate `ContinuesAcross` (NOT `¬AnalyticAt` of the junk-extended
tsum, which is trivially true for the wrong reason — see the ⚠ note below) and isolated as a single
`sorry`-theorem `u0_natural_boundary`; the convergence side is proven.
-/
import GaloisForLFunctions.U0.U0Series
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.Algebraic.Basic

open Complex Filter Topology U0

namespace U0NaturalBoundary

/-! ## Radius of convergence of U₀ = 1 -/

/-- The companion series U₀(w) = u₀(1/w) converges absolutely for |w| < 1. -/
theorem U0_summable_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n : ℕ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (2 : ℝ) ^ (-(n + 1 : ℤ)))
  · exact summable_two_zpow_neg
  · intro n
    rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_two]
    have hw1 : ‖w‖ ≤ 1 := le_of_lt hw
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    have hexp : (0 : ℤ) ≤ 2 ^ (n + 1) - 1 := by
      have h : (1 : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast Nat.one_le_two_pow
      linarith
    have hwpow : ‖w‖ ^ (2 ^ (n + 1) - 1 : ℤ) ≤ 1 := by
      lift (2 ^ (n + 1) - 1 : ℤ) to ℕ using hexp with m hm
      rw [zpow_natCast]
      exact pow_le_one₀ hw0 hw1
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(↑n + 1 : ℤ)) := zpow_nonneg (by norm_num) _
    linarith [mul_le_mul_of_nonneg_left hwpow h2]

/-! ## The single irreducible analytic core

⚠ **Correctness note (junk-extension trap).** `∑'` is `0` wherever the series diverges, so the
*literal* tsum function jumps to `0` across `‖·‖=1` and is trivially non-`AnalyticAt` there — for the
WRONG reason (a discontinuous junk extension, which an *algebraic* function would share). That trivial
statement does **not** encode a natural boundary and does **not** imply transcendence. The genuine
content is *analytic continuation from the domain of convergence*, captured by `ContinuesAcross`:
an analytic `g` near `z₀` agreeing with the function on the convergence-side neighborhood. Junk values
off the domain cannot satisfy this, so it carries real content. -/

/-- `f` continues analytically across `z₀` from the domain `D`: some `g` analytic at `z₀` agrees with
`f` on a `D`-side neighborhood of `z₀`. Its negation, for every boundary point, is a *genuine* natural
boundary (unlike `¬ AnalyticAt` of a junk-extended tsum). -/
def ContinuesAcross (f : ℂ → ℂ) (D : Set ℂ) (z₀ : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ ∀ᶠ w in nhdsWithin z₀ D, g w = f w

/-- The exterior `{z | 1 < ‖z‖}`, the genuine domain of convergence of `u₀`. -/
def Ext : Set ℂ := {z : ℂ | 1 < ‖z‖}

/-- **Natural boundary of u₀ — the one irreducible analytic core (genuine form).**

`u₀` (analytic on the exterior `Ext`) does not continue analytically across any point of the unit
circle. This — not the junk `¬AnalyticAt` form — is the real content equivalent to "u₀ transcendental
over ℂ(z)". It is the only analytic input the `U0` development rests on; everything else (functional
equation, convergence, doubly-exponential divergence) is proven.

**Why a `sorry`, not an `axiom`:** it is *provable*; only the supporting infrastructure is Mathlib-
missing. As a theorem, `#print axioms` of anything using it shows `sorryAx` (a debt), not a new axiom.

**Proof blueprint — softer than the generic Ostrowski–Hadamard gap theorem because it uses the Mahler
functional equation `(2/w)·U₀(w) = 1 + U₀(w²)` that this specific series satisfies:**

1. *Radius of convergence exactly 1.* `U0_summable_lt_one` (converges `‖w‖<1`) + doubly-exponential
   `U0term_norm_tendsto_atTop` (diverges `‖w‖>1`) bracket it. [PROVEN]
2. *Seed singularity.* A power series of radius `1` fails to continue across **some** boundary point
   (else compactness of the circle ⟹ continuation to an annulus ⟹ radius `>1`). ← the lone
   Mathlib-missing input; far more elementary than the full gap theorem.
3. *Propagation by the functional equation.* continues across `w₀ (≠0)` ⟹ continues across both square
   roots `±√w₀` (`U₀(w) = (w/2)(1+U₀(w²))`, `w↦√w₀` a local biholomorphism). Contrapositive spreads the
   singularity to square roots.
4. *Density.* the `2ⁿ`-th roots of the seed are dense on the circle.
5. *Close up.* `{z | ¬ ContinuesAcross …}` is closed (continuation is an open condition); closed ⊇ dense
   ⟹ the whole circle. ∎

So the three-card independence result reduces, on the analytic side, to step 2 alone. -/
theorem u0_natural_boundary :
    ∀ z₀ : ℂ, ‖z₀‖ = 1 → ¬ ContinuesAcross u0 Ext z₀ := by
  sorry

/-- The companion series equals `u₀ ∘ (·⁻¹)` as tsums: `(w⁻¹)^{-(2^{n+1}-1)} = w^{2^{n+1}-1}`.
Pure algebra; underlies the `w ↦ 1/w` bridge between the u₀-side and U₀-side boundary statements. -/
theorem u0_inv_eq_companion (w : ℂ) :
    u0 w⁻¹ = ∑' n : ℕ, (2 : ℂ) ^ (-(n + 1 : ℤ)) * w ^ (2 ^ (n + 1) - 1 : ℤ) := by
  simp only [u0]; congr 1; ext n; congr 1
  rw [inv_zpow, zpow_neg, inv_inv]

end U0NaturalBoundary
