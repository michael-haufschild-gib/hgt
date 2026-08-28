# Two-Volterra domination producer loop — state after cycles 1–6 (2026-08-28)

Cards: `1-in-progress/source-contraction-two-volterra-domination.md` (hub, full cycle log incl.
cross-agent correction), `1-in-progress/theta-krein-pick-congruence.md`,
`1-in-progress/theta-kernel-cp-deficit-domination.md` (cycle-6 frame). Numerics archived in
`2-fully-proven/computations/2026-08-28-two-volterra-domination-loop/`.

## Target
Produce, from the literal theta source and uniformly in rank, the contraction `K₋∘K₊^{−1}` for
`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`.

## Lean landed this loop (all unconditional, axioms standard)
- `RHTower/ThetaTailKreinXiCentTiltCollapse.lean`: channel collapse `K± = e^{−ws}(ξc′ ± cξc)`,
  all-plane division-free tilt algebra, lossless wall `tilt₋ = −conj tilt₊`.
- `RHTower/ThetaTailKreinTiltDiagonalLaw.lean`: rank-one A2 law
  `‖tilt₊‖²−‖tilt₋‖² = 4c·Re(ξc′ξ̄c)`, line parity, wall vanishing of `Re(ξc′ξ̄c)`.
- `RHTower/XiCentEulerAtomFactorization.lean`: `xiCent = ζ(w+1/2)·atomFactor` on `Re > −1/2`;
  atom's ζ-pole-shadow zero at `w = 1/2`; EXACT truncation no-go: two-atom causal truncation
  vanishes at `w = −1/2 + iπ/log2` with atom ≠ 0 (`2^{−iπ/log2} = −1`, no numerics).
- `RHTower/ThetaTailKernelGeometricDeficitSplit.lean` (cycle-6 foundation):
  `k(x,t) = ∫_{s>0}(x+t+2s)Φ(x+s)Φ(t+s)ds`; exact AM–GM split `k = 2M + D`;
  **M manifestly PSD** (`thetaTailGeometricKernel_quadraticForm_nonneg` — integral of a square
  of the nonneg family `√(y+s)Φ(y+s)`); D entrywise ≥ 0, zero diagonal, symmetric.
- (C₅ thread) `RHTower/ThetaCuspFifthRootGaussianDeviationMargin.lean`.

## Killed (witnesses on cards)
Shape classes; FE-symmetrized single atom (Riemann–Siegel low-height phase deficit); causal AND
even source truncations (two-atom causal now EXACT in Lean); Mourre/flow (⟶ Levinson–Montgomery);
C6 semigroup transport (⟺ Sondow–Dumitrescu/Jensen receiver, corpus-owned
`strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound`).

## Corrected claim (cross-agent review, recorded on hub card)
Lehmer pairs are on-line near-degeneracy, not RH failure; the COMPLETE Laguerre hierarchy
characterizes LP (Csordas–Vishnyakova) and detects nonreal zeros at finite order (corpus:
`exists_completedFluxTaylorCoeff_line_pair_ne_of_re_ne_half`); only FINITE jet prefixes are blind
(`finiteCorrectionDepth_divisorBlind`). Wall-jet approaches fail as producers because prefixes are
blind and the full hierarchy is receiver-equivalent — not because jets "cannot see."

## Structural facts (receiver web, exact)
λ_c = tilt₋/tilt₊: Bezoutian = diagonal congruence of its half-plane Pick matrix; RH ⟺ λ_c Schur
on Re>0 ⟺ Lagarias ⟺ SD ⟺ Jensen; |λ_c| ≤ 1 on Re ≥ 1/2 unconditional, ≡ 1 on Re = 0 (Lean);
poles barred from the line unless double zero; wall-normal contraction jets = Laguerre hierarchy
(`u = εL₁ + ε³L₂/6 + O(ε⁵)`, verified to ε⁴; dps ≥ 60 for L₂ stencils — dps-30 gives spurious
negatives).

## Active frame (cycle 6): CP vs deficit
RH ⟺ `2M + D ⪰ 0` with M manifestly PSD and D a zero-diagonal displacement kernel. Frozen:
CP-1 (separation-restricted domination, Schur-test route), CP-2 (k completely positive — would
prove RH, may be false: DNN ≠ CP), CP-3 (double-commutator comparison `2C₁ ⪰ (√x−√t)²C₀`,
sufficient-only, expected tight/false — its failure pattern steers the next splitting). The HCF
displacement-kernel no-go marks where naive domination fails: the needed "pair repulsion" is now
one inequality between two explicit integrals of the same positive family.

## Do-not-revisit
Soft kernel classes; source truncations (both parities); single-place completions; atom
induction; Mourre-as-such; transport/monotonicity/jet reformulations (Jensen web);
unconditional-Laguerre-as-producer. Queued formalizations: C1 shape-class kill (transcendental
enclosures); single-atom Mellin integral (upgrades factorization to the literal atom transform).
