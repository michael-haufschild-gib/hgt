# Renormalized intersection theory of the scaling surface (programme)

- **ID:** rit-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme of pillar theorems
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.6
- **Statement:** Build the renormalized intersection pairing on the scaling surface (local terms at all places coupled through the product formula, running counterterm, Hodge index on the pole-orthogonal hyperplane) and prove its pillar theorems unconditionally.

## Goal
Answer the questions of §2.6 with theorems: product-formula gluing of the global pole, Hodge index on
the pole-orthogonal hyperplane (equivalence with RH), Künneth square index, canonical finite part,
collision quantum as an index, confinement, ℤ vs 𝔽_q.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: each pillar has a complete paper proof
- [ ] 2 → 3  formalized: each pillar is a Lean theorem in `formal/GaloisForLFunctions/RenormalizedIntersectionTheory`

## Approach
P1 hyperbolic plane / renormalized Hodge index: AKG gluing formula + HKT index law.
P2 product-formula gluing: expand ∏_{p∈S}(χ_p + χ_p⁻¹) = Σ_ε χ^ε; pairs {ε, −ε}; HKT exact pair formula
with separating unit ∏_{p∈S} p; extremal ε ↔ archimedean boost on S-units; archimedean-continuous ⇔ ε constant.
P3 Künneth square: Kronecker inertia of Gram matrices (HTGeometry) + positive squares of K_ζ unbounded.
P4 finite part: Mertens Σ_{n≤N} Λ(n)/n − log N → −γ (RHTower).
P5 pole class on integer slopes: boost functional = √(log N)·⟨·, v_1⟩.
P6 collision quantum: HKT HeatCollisionsCountTheIndex + gluing formula.

## Log
- 2026-10-31 — created in 1-in-progress
