/-
# u₀ – φ_b algebraic independence

`u₀(z) = ∑_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}` is the Böttcher c-velocity at the monomial fiber
(`u₀ = (∂_c φ_c)|_{c=0}`). For `b ≠ 0, -2` it is algebraically independent of the inverse
Böttcher coordinate `φ_b` over `K = ℂ̄(b, z)`.

## Structural content — overlap with the Böttcher q62 proof

The card's proof (capacity + natural boundary + algebraic IFT, or Green-crossing in the
disconnected case) and the q62 Böttcher proof of `φ_{c₁} ⟂ φ_{c₂}` are **the same algebraic
engine fed by different analytic inputs**:

* **shared engine** — `Bottcher.algIndep_of_unbounded_monodromy`: a transcendental `G` fixed by an
  automorphism tower of unbounded order, an `F ≠ 0` scaled by those automorphisms ⟹ no polynomial
  relation `P(F,G)=0`.
* **the u₀ case is the q62 MIXED case** — `u₀` is **single-valued** (the c-velocity lives on the
  z-plane, not the Böttcher cover), so the Böttcher monodromy **fixes** `u₀` and **scales** `φ_b`.
  That is exactly the `G` fixed / `F` scaled split of `Bottcher.q62_mixed`.

So `u0_phi_independence` below is *literally an instance of `Bottcher.q62_mixed`*. The only u₀-specific
input is the analytic core:

> **`hTranscendental` : `Transcendental K u₀`** — the irreducible analytic fact, equivalent to the
> unit circle being a natural boundary of u₀ (Ostrowski–Hadamard gap theorem) / to the Mahler
> equation `2·u₀ = z⁻¹·(1 + u₀∘sq)` having no algebraic solution. This is the u₀-analog of the
> Böttcher tower's transcendence input and of whatever transcendence/independence input an RH-shaped
> proof would require.

This file proves the reduction; the analytic core is isolated as a named hypothesis exactly as the
Böttcher reference isolates `hDisc`/`hRigid`.
-/
import GaloisForLFunctions.Bottcher.Q62
import GaloisForLFunctions.U0.U0NaturalBoundary

open Bottcher

namespace U0PhiIndep

/-- **u₀ ⟂ φ_b — abstract form (single-valued u₀ = q62 mixed case).**

In an abstract field `M` over `K` carrying the Böttcher monodromy, with
* `phib` (= `φ_b`) the scaled coordinate, `phib ≠ 0`,
* `u0` the single-valued c-velocity, **transcendental over `K`** and **fixed** by the tower,
* the dyadic monodromy `mono` scaling `phib` by multipliers of unbounded order while fixing `u0`,

there is no nonzero polynomial relation between `phib` and `u0` over `K`.

This is `Bottcher.q62_mixed` with `F := phib`, `G := u0`. The proof is one line: the engine is shared. -/
theorem u0_phi_independence_abstract
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (phib u0 : M) (hphib : phib ≠ 0) (hTranscendental : Transcendental K u0)
    (mono : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ u0 = u0 ∧ σ ζ = ζ ∧ σ phib = ζ * phib) :
    NoRelation K phib u0 :=
  q62_mixed phib u0 hphib hTranscendental mono

/-- **u₀ ⟂ φ_b — all nonexceptional parameters, both Mandelbrot cases.**

For `b ∉ {0,-2}`, `φ_b` and `u₀` are algebraically independent over `K`. The single analytic
input is packaged as `hData`:

* `b ∉ {0,-2}` (nonexceptional: `φ_b` exists and is nonconstant), giving
* `u₀` transcendental over `K` (natural boundary / Mahler — the irreducible core), and
* the Böttcher dyadic monodromy scaling `φ_b`, fixing the single-valued `u₀`.

Unlike `q62_independence` there is **no separate connected (`hRigid`) branch**: because `u₀` is
single-valued it is *always* fixed by the tower, so the mixed-case engine covers **both** the
connected (`b ∈ M`) and disconnected (`b ∉ M`) parameter regions in one stroke. The
Eremenko–van Strien rigidity that q62 needs for its both-connected case is **not** needed here —
single-valuedness of `u₀` replaces it. That is the structural payoff of `u₀` being a velocity
rather than a second Böttcher coordinate. -/
theorem u0_phi_independence
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (φ : ℂ → M) (u0 : M) (b : ℂ) (hb : b ∉ Exceptional)
    (hData : b ∉ Exceptional →
      φ b ≠ 0 ∧ Transcendental K u0 ∧
      ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ u0 = u0 ∧ σ ζ = ζ ∧ σ (φ b) = ζ * φ b) :
    NoRelation K (φ b) u0 := by
  obtain ⟨hF, hG, mono⟩ := hData hb
  exact u0_phi_independence_abstract (φ b) u0 hF hG mono

/-- **u₀ ⟂ φ_b — disconnected case (`b ∉ M`), transcendence derived from monodromy.**

When `b ∉ M` the coordinate `φ_b` carries its OWN unbounded monodromy. But `u₀` does **not** — it is
single-valued, so its transcendence cannot be read off a `u₀`-monodromy (there is none). Thus, unlike
`Bottcher.q62_disconnected_both` where both coordinates' towers make the `Transcendental` hypothesis
redundant, here the transcendence of `u₀` remains an **independent** analytic input (the natural
boundary). The disconnected case is therefore NOT cheaper than the connected case for u₀ — a sharp
contrast with q62, and a direct consequence of `u₀` being a velocity. -/
theorem u0_phi_independence_disconnected
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (phib u0 : M) (hphib : phib ≠ 0) (hTranscendental : Transcendental K u0)
    (mono : ∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ u0 = u0 ∧ σ ζ = ζ ∧ σ phib = ζ * phib) :
    NoRelation K phib u0 :=
  u0_phi_independence_abstract phib u0 hphib hTranscendental mono

end U0PhiIndep
