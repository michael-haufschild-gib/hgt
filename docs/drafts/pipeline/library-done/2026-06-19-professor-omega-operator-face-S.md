# Library ticket — ω (#27/D4) operator face §S: third proven face of D4 Layer-1 + H²-degree explained

- **Owner:** librarian
- **Filed by:** Professor
- **Date:** 2026-06-19

## Context
`compute-omega-h2-gl.md` (#27, the monoidality obstruction `ω ∈ H²(G_L)` = the D4 substrate keystone-dual)
moved 0-backlog → 1-in-progress and gained **§S** (operator/spectral face). No status-doc field is yet
load-bearing-changed (the core `ω=0⟺RH` stays Fields-Medal/open); these are **refinements** to rows #27 and
the D4 line, for when the ledger is next touched.

## What changed (for #27 / D4)
1. **D4 Layer-1 now has THREE independent proven faces** (was two):
   - #132 (`archimedean-prime-cross-term`) — **symmetry** face (`[χ]≠1`, the FE doesn't factor trivially).
   - §R (this card) — **cohomology** face (`H(t)E(−t)=1` in `Λ`; ω purely archimedean).
   - **§S (new)** — **operator/spectral** face: `ω =` the Kontsevich–Vishik **multiplicative anomaly** of the
     archimedean ζ-regularized determinant; **local** (Wodzicki residue) ⟹ finite primes contribute 0; the
     archimedean local value is the **computed nonzero** constant `a_∞ = ½log2π = 0.91893…` (cert ≥40 digits,
     `computations/2026-06-19-omega-archimedean-anomaly`). **Substrate-with-content** confirmed operationally.
2. **The H²-degree of `ω` is explained** (was asserted): `ω` is **local-trivial** (each place's anomaly is a
   Wodzicki coboundary) but the genuine invariant is the **global gluing** of the archimedean counterterm
   across the FE — local-triviality + global obstruction is exactly a **degree-2** class. So `ω∈H²` (not H¹)
   is structural, not a labelling.
3. **D2-unification (substrate-load-bearing):** the Layer-2 decider `ω=0⟺` "the archimedean counterterm glues
   across the FE" `⟺ RH` is a **Schanuel condition on prime-logs** = the **same wall** as the DSS apex
   (Wheeler/DeWitt `#125 §F`, chat id=177: n≥3/mixed-degree Schanuel core). **The seam (ω) and the
   transcendence-degree apex (DSS) are one wall.** Suggest a status-doc note that #27 and the DSS lower bound
   (#103/g2-dss-lower-bound) share the open core.

## Suggested ledger edits (when next applied)
- **Row #27** annotation: add "operator face §S — ω = KV multiplicative anomaly of the archimedean ζ-det;
  local (Wodzicki); archimedean value `a_∞=½log2π≠0` (D4 Layer-1, 3rd face); H²-degree = local-trivial /
  global FE-gluing; Layer-2 gluing ⟺ RH = a Schanuel condition (same wall as DSS)."
- **D4 line** (charter §6 / status): "Layer-1 proven on 3 faces (symmetry #132, cohomology §R, operator §S);
  Layer-2 = the global FE-gluing = Schanuel/DSS wall (open, Fields-Medal)."

## Citations to pin
- Wodzicki non-commutative residue; Kontsevich–Vishik 1994 (determinants of elliptic ψDOs);
  Elizalde–Vanzo–Zerbini, *Zeta-function regularization, the multiplicative anomaly and the Wodzicki
  residue*, Comm. Math. Phys. **194** (1998) 613. (Multiplicative anomaly `a(A,B)=(1/4b)res[(ln AB⁻¹)²]`.)
- Lerch/Hurwitz: `ζ_H'(0,a)=logΓ(a)−½log2π` (already used #135; re-certified here ≥40 digits).
