# The HT-composition transcendence wall — where this corpus's open cores converge

- **ID:** ht-composition-transcendence-wall
- **Stage:** 0-backlog (cross-cutting FRONTIER MAP / synthesis, computation-backed)
- **Type:** STRUCTURAL SYNTHESIS — locates the shared open core of three cards
- **Source:** Turing id=1923–1926; unifies feigenbaum-ht-ade-continuation, log-derivative-ht-theory (Thm B/ψ(Γ)),
  ade-boundary-hinf-ht. Computational confirmation: psigamma_diff (Runpod), feig q-difference probes.

## The finding

Deciding "is f HT?" for a COMPOSED object f = (outer)∘(inner) splits cleanly:

**EASY (already decided by the closure lemmas, Thms B/D/E):** outer ∈ {exp, log, power, log-derivative}.
- exp(Γ) HT ⟺ Γ HT (G=exp(F) HT ⟺ F HT). Provably HT.
- (Γ)^a HT for a≠0 (Theorem E). G·H, G/H handled by log-derivative additivity.
- These reduce because the outer operation has a log-derivative identity that the DA-field closure resolves.

**HARD (the open cores — no closure lemma applies):** outer is a GENERAL HT function (ψ = digamma) or the
SELF (self-composition), with no exp/log/power reduction.
- **ψ(Γ)** (log-derivative-ht-theory, Thm B/C): ψ(Γ) not DA of order 1 [PROVED, movable log singularity];
  order ≥2 open. Outer = ψ, not exp/log.
- **Feigenbaum g**, g(g(u))=λg(αu) (feigenbaum-ht-ade-continuation): self-composition; HT open.
- **ade-boundary construction**: a bounded DA with a natural boundary — the reverse construction, same regime.

## Why the hard cases resist EVERY structural lever (computation-backed)

1. **Closure lemmas don't reduce them** (outer ≠ exp/log/power) — by definition of the hard class.
2. **Difference-Galois has no input.** The ONLY machinery that PROVES HT (difference-Galois on a linear
   difference equation — e.g. Γ(z+1)=zΓ(z) proves Γ HT) requires the object to be DIFFERENCE-ALGEBRAIC. But
   the compositions BREAK it:
   - ψ(Γ): NOT difference-algebraic in z→z+1 (probe: σ_min=1.4e-5 vs controls Γ,exp at 1e-41). The shift
     doesn't pass through the composition (ψ(Γ(z+1))=ψ(zΓ(z)), no clean relation).
   - Feigenbaum g: NOT q-difference-algebraic w.r.t. σ_α (three probes). g(g(u))=λg(αu) is nonlinear-iterative,
     not a Mahler equation.
3. **Other analytic levers are DA-compatible** (so can't force HT): movable log singularities (log tan is DA);
   z log z growth (DA, order 2); natural boundaries with unbounded derivatives (Chazy/E2 DA); branch points.

## The missing tool (the named research frontier)

A transcendence / difference-Galois theory for objects defined by a **composition or iteration** functional
equation that are themselves **not difference-algebraic** and whose outer operation is **not exp/log/power**.
Equivalently: extend difference-Galois from linear difference equations to nonlinear-iterative / composition
equations. This is what all three cores bottleneck at; no structural shortcut survives (each lever above is
DA-compatible). The partial results (ψ(Γ) order-1; the ade-boundary theorem; the Feigenbaum no-low-order-ODE/
holonomic/q-difference characterization) are the reachable floor; the deep HT-status is above this wall.

## Status
- [x] Synthesis stated; the easy/hard divide made precise; difference-algebraicity break computation-confirmed.
- [ ] The missing machinery is genuinely open research (difference-Galois for compositions/iterations).
- Banked partials live on the three source cards; this card is the map, not a new theorem.
