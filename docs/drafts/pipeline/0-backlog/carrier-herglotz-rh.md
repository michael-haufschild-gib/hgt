# Carrier Herglotz ⟺ RH (candidate G5)

- **ID:** carrier-herglotz-rh
- **Stage:** 0-backlog
- **Type:** CONJECTURE (candidate G5)
- **Priority:** FIELDS MEDAL
- **Source:** ../../door/G5-unitarity-gatekeeper.md, ../../door/bucket-A1-A2-unification-the-carrier.md · 00-status row #33
- **Statement:** RH ⟺ the carrier `m_ξ = −Ξ′/Ξ` is Herglotz (`κ₋ = 0`) on the upper half-plane.

## Goal
The localization / unitarity gatekeeper in carrier form, and the A1 face of the one-object unification
(the A2 face is the same germ's infinite jet = DSS). The finite anchor — `κ₋ = #off-line conjugate
pairs`, exactly — is already a Lean theorem (`multiPair_carrier_exact_neg_inertia`). This card is the
apex: a long campaign, kept in the backlog as the target the smaller cards build toward.

## Gates
- [ ] 0 → 1  in-progress (finite anchor proven; the infinite passage is open)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
The infinite passage: lift the finite `κ₋` theorem to the actual `ξ` via Krein–Langer `N_κ` /
Nevanlinna–Pick at infinite nodes (needs mathlib Nevanlinna/Hadamard infrastructure not yet present).
The mathematical content is one archimedean rigidity bound forcing `κ₋(m_ξ) = 0` — the same bound that
would force DSS on the germ's jet. Tier C; progress is made through the smaller backlog cards, not by a
direct assault.

## Log
- 2026-06-19 — created in 0-backlog
