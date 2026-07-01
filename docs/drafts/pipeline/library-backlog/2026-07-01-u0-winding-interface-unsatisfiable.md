# Ticket: U0 image-winding deep-data interface is unsatisfiable — replaced by the circle-window reduction

- **Date:** 2026-07-01
- **From:** Fable (Hurwitz/U0 formalization session)
- **Type:** interface correction (formal reduction tree) + new proved reduction
- **Affects:** `u0-phi-independence*` cards; `U0CardTheorems.PhibImageWindingDeepData`,
  `PhibImageWindingEscapeDeepData` and every `*_deepData` / `*_imageWinding*` conditional endpoint.

## Finding [PROVED HERE, paper-level; not yet formalized in Lean]

`PhibImageWindingDeepData U b` demands, per depth `d`, a closed C¹ loop `γ` with
`f^[d+1] ∘ γ` of ODD winding about `0`, where `γ` stays in a domain `Ext` with
`f^[d+1](Ext) ⊆ escapeOpen b` — i.e. `γ` avoids the bad set
`B_{d+1} = (f^[d+1])⁻¹((escapeOpen b)ᶜ)`.

That winding is ALWAYS even, for every parameter `b` and every depth:

1. All zeros of `f^[d+1]` lie in `B_{d+1}` (`f^[d+1]` maps them to `0`, and `|0| ≤ max 2 ‖b‖`).
2. By the argument principle, `wind(f^[d+1]∘γ, 0) = Σ_C wind(γ, C) · N_C`, summing over the
   connected components `C` of `B_{d+1}`, `N_C` = number of zeros of `f^[d+1]` in `C` (with
   multiplicity); `wind(γ, ·)` is constant on each `C` since `γ` avoids `C` and `C` is connected.
3. `N_C` is even for every component, by induction on depth: `B₁ = f⁻¹({‖w‖ ≤ max 2 ‖b‖})` is
   CONNECTED (the disk contains the critical value `b`, since `‖b‖ ≤ max 2 ‖b‖`; the quadratic
   preimage of a disk containing the critical value is connected) with total degree 2.  For the
   step, a component `C` of `B_{k+1}` maps into a component `C''` of `B_k` and
   `deg(f^[k+1]|_C) = deg(f|_{C→C''}) · deg(f^[k]|_{C''})` — even because the second factor is.

Hence the integral `∮ dlog(f^[d+1]∘γ) = 2πi·(2m+1)` demanded by the interface is impossible.
Every conditional endpoint downstream of `PhibImageWindingDeepData` (incl. the escape-local
variant) is vacuous: the branch can never be discharged.  This mirrors the earlier carrier
correction in `U0PhiLifts.lean` (the base-plane `hliftF` that was unsatisfiable): base-plane
certificates for the dyadic root tower keep failing for structural reasons — the monodromy/parity
lives on the cover, not the base.

## Replacement (landed, axiom-clean)

`formal/GaloisForLFunctions/U0/U0PhiCircleWindow.lean`
(+ card wrapper `FullyProvenNewTargets.u0_phi_circle_window : U0PhiCircleWindowTarget`):

- `u0_windowed_relation_false` / `u0_phi_windowed_no_relation_3var` — the natural-boundary engine
  fired at `D = Ω ∩ Ext` for a window `(Ω, φ)`: `φ` analytic on an open preconnected `Ω` touching
  the unit circle at some `z₁`, `Ω ∩ Ext` preconnected, and the relation `P(z, φ(z), u₀(z)) = 0`
  (positive `u₀`-degree, separable-specialization data at some `w ∈ Ω`) required only on a
  NONEMPTY OPEN `V ⊆ Ω ∩ Ext` — identity theorem propagates it across the window; near the circle
  the window is invisible (`D ∩ ball = Ext ∩ ball`), so `u0_natural_boundary` and the lens
  localize.  Axioms: `[propext, Classical.choice, Quot.sound]`.

## The one remaining analytic input (shared with the q62 continuation program)

The window continuation itself: `(Ω, φ)` with `φ` agreeing with `bottcherCoord b` on a far-field
piece and `Ω` reaching a unit-circle point (the Green-crossing `G_b(z₀) > G_b(0)`; Riesz–Jensen
proof in the disconnected card).  This is the same sub-critical Böttcher continuation object the
q62 lane is building (`CylinderUnivalence`/`BasinBranching` bricks).  Once it exists, the u₀ card
closes through `u0_phi_circle_window` with V = the far-field overlap; the u₀-degree-0 residue
(relations in `φ` alone) is the φ-transcendence card, also served by the same window via the
`J_b`-natural-boundary instance of the engine.

## Also this session (Hurwitz, for cross-reference)

Genuine-`hzeta` capstones landed (`Hurwitz/N2HZeta.lean`): the N=2 card and the all-N quadratic
block now hold against the actual Hurwitz zeta — see `Hurwitz/STATUS.md` Update 7.  Area
build-rot from the mathlib bump repaired (4 missing transitive imports).
