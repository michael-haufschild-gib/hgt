# Carrier Herglotz ⟺ RH (candidate G5)

- **ID:** carrier-herglotz-rh
- **Stage:** 0-backlog
- **Type:** CONJECTURE (candidate G5)
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
- 2026-06-20 (novelty-loop R02) — **Causality reading + universal-marginality conjecture** (full piece
  in `logs/2026-06-20-novelty-generation-loop.md`). Herglotz = Cauchy transform of a positive measure =
  **causal/passive** transfer function (Kramers–Kronig) = positive-real impedance = Hamburger moment
  problem (κ₋ = #negative-norm/ghost states). So **RH ⟺ the carrier is a causal, passive arithmetic
  system**; off-line zeros = acausal/active modes (concrete A2/"time" reading). Verified seam split: the
  archimedean digamma piece −½ψ(s/2) is **unconditionally Herglotz** (Im ψ>0 across C⁺), the prime piece
  −ζ′/ζ is sign-indefinite — ∞ is causal for free, the primes' causality is RH. dBN heat flow = relaxation
  to passivity, κ₋(t) a Lyapunov functional ↓ to 0 at Λ_dBN (Rodgers–Tao Λ≥0; Newman Λ=0 = marginal
  causality). **Conjecture:** ζ is tuned to the *edge* of every natural deformation (convergence s=1 [R01],
  causality Λ=0, signature σ=½ #190); A1=σ=½ margin, A2=s=1 margin are two faces of one self-criticality.
  Shared missing lemma with R01: a positivity-preserving continuation across the abscissa. ~60–70% prior-true.
- 2026-06-20 (codex experiment R18) — **Cayley-Schur inner-defect split for A1/A2.** Re-read the finite carrier/Cayley infrastructure and reframed the carrier germ by `theta_xi=(m_xi-i)/(m_xi+i)`. The finite `κ₋=#off-line pairs` theorem says the RH defect is a discrete negative-square count; in the Schur disk picture this is exactly a finite Blaschke inner factor, morally `theta_xi=B_defect*theta_0` with `deg B_defect=κ₋`. Thus A1/RH is `deg B_defect=0`, while A2/DSS belongs to the outer/infinite Taylor jet. This explains why the one-carrier unification is real but non-coercive: generic Herglotz/Schur theory cannot make inner-degree zero force algebraic independence of the outer jet, or vice versa; any bridge must use the Euler/arithmetic realization cut. Full working log in `logs/codex_experiment.md` Round 18.
