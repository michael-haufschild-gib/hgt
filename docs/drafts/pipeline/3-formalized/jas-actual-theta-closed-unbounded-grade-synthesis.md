# JAS actual-theta closed unbounded grade synthesis

- **ID:** JAS-ACTUAL-THETA-CLOSED-UNBOUNDED-GRADE-SYNTHESIS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `JointAncestryActualThetaGradeNormEscape`,
  `JointAncestryCriticalMixedPrimeGradeIncidence`, `BoundedDiagonalOperatorLp`, and
  `SourceLinearClosedRelationSplitting`
- **Statement:** Canonical actual completed-theta prime-grade packets are exactly coordinate values
  of a closed, densely defined, single-valued linear relation; its domain is dense and nonclosed,
  and no bounded operator realizes the same coordinate law.

## Goal and RH chain

Close positive survivor forced by bounded-synthesis no-go. Corpus chain:

`actual completed-theta all-grade L2 chain + normalized injective prime packets`
→ `closed coefficient-faithful prime-to-actual-grade synthesis relation`
→ `RFHM support-cutting corner/higher-compound source-linearity for every Xi divisor rho`
→ `XiPrimePoissonReflectionSewing rho`
→ `XiDivisorSyndromeIsInternalOnly rho` by
  `xiPrimePoissonReflectionSewing_iff_internalOnly`
→ `Re rho = 1/2` by `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`
→ `RiemannHypothesis`.

This card targets only second object in chain. It does not claim operator-family intertwining or
the remaining support-cutting sewing.

## Gates

- [x] 0 → 1  in-progress: corpus search, frozen theorem, exact RH chain, hostile audit
- [x] 1 → 2  fully-proven: dependency-closed proof
- [x] 2 → 3  formalized: direct check, leaf build, axiom audit, umbrella import
- [ ] 3 → 4  publication-ready: standalone theorem, proof, certificate, Door-2 audit

## Formalized theorem

`[THEOREM] [NOVELTY UNVERIFIED]`

Let `w_p` be norm of actual completed-theta grade indexed by prime `p`, and let `U` be canonical
isometric normalized prime-grade synthesis. There is a submodule `R` of orthogonal Hilbert sum
`ell2(Primes) ⊕ L2Amplification Nat (JASCriticalPrimePoissonL2 t)` such that:

1. `R` is closed;
2. its source domain is dense but not closed;
3. `R` is single-valued;
4. `(e_p, w_p U e_p)` belongs to `R` for every prime `p`;
5. no bounded operator has graph containing every such coordinate pair.

## Corpus basis and proof architecture

- `tendsto_norm_jointAncestryCompletedThetaGradeL2_atTop` and positivity make reciprocal actual
  grade weights a bounded nonzero null sequence.
- `deningerMultiplier_denseRange_of_ne_zero` gives dense domain; its nonclosed-range theorem gives
  genuine unboundedness.
- `orthonormal_jointAncestryCriticalPrimeInjectiveGradePacket` gives isometric `U`.
- Define `R` as graph of inverse reciprocal multiplier followed by `U`, expressed as intersection
  of kernels of bounded coordinate equations. Kernel form gives closedness; multiplier injectivity
  gives single-valuedness.
- `not_JASCriticalPrimeActualThetaInjectiveGradeSynthesis` excludes every bounded realization of
  same coordinate law.

## Dependency-closed proof

Write `w_p > 0` for actual theta-grade norm at `natEquivPrimes.symm p` and choose
`c = min(1, sqrt(jasActualThetaPositiveIntervalMass)) > 0`. Norm escape and its fixed-interval
lower bound give `c ≤ w_p`, so `g_p = c / w_p` is nonzero and has modulus at most one. Moreover
`g_(natEquivPrimes n) → 0`. Therefore diagonal multiplier `D_g` is injective with dense nonclosed
range.

Let `U` be canonical isometry synthesizing normalized collision-free prime-grade packets. Define
`R` by two bounded equations on `ell2(Primes) ⊕ packetHilbert`:

- `c u = D_g (U* v)`;
- `U U* v = v`.

Thus `R` is intersection of two kernels and is closed. Pairs `(D_g x, c U x)` lie in `R`; hence
its domain contains dense range of `D_g`. Conversely first equation and `c ≠ 0` put every domain
vector in that range, so domain equals the dense nonclosed range. If `(0,v) ∈ R`, injectivity of
`D_g` forces `U* v = 0`, and second equation forces `v = 0`; hence relation is single-valued. For
coordinate `p`, `D_g(w_p e_p) = c e_p` and `U(w_p e_p)` is literal actual theta-weighted packet,
so `(e_p, actualPacket_p) ∈ R`. Prior norm-escape theorem excludes every bounded operator with
these coordinate values.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.JointAncestryActualThetaClosedUnboundedGradeSynthesis`
- Main theorem: `jasActualThetaClosedUnboundedGradeSynthesis`
- Supporting certificate:
  - `isClosed_jasActualThetaClosedGradeSynthesisRelation`
  - `jasActualThetaClosedGradeSynthesisRelation_domain_eq_range`
  - `not_isClosed_jasActualThetaClosedGradeSynthesisRelation_domain`
  - `jasActualThetaClosedGradeSynthesisRelation_singleValued`
  - `jasActualThetaClosedGradeSynthesisRelation_coordinate_mem`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/JointAncestryActualThetaClosedUnboundedGradeSynthesis.lean`
- Leaf audit:
  `lake build GaloisForLFunctions.RHTower.JointAncestryActualThetaClosedUnboundedGradeSynthesis`
- Audited theorem axioms: `[propext, Classical.choice, Quot.sound]` only.
- Wired into `GaloisForLFunctions.RHTower`; umbrella build intentionally not run.

## Hostile audit

- Not RH: relation is coefficient-faithful but not yet source-linear for forward/reflected
  prime-Poisson operator families.
- Not an infrastructure-only abstraction: coordinate values are literal actual theta norm-weighted
  critical prime packets already defined in corpus.
- Exact positive survivor of prior no-go; it replaces impossible bounded synthesis with strongest
  closed unbounded realization.
- Literature novelty remains unverified; exact JAS construction is corpus-specific.
- 2026-08-29 arXiv search found standard Xi--theta approximation and generic diagonal/unbounded
  operator literature, but no exact prime-indexed actual-theta relation or JAS sewing construction.

## Log

- 2026-08-29 — frozen from corpus search after bounded actual-grade no-go and exact Xi sewing
  endpoint audit.
- 2026-08-29 — proved and formalized exact closed unbounded positive survivor; direct check, leaf
  build, axiom audit, and umbrella wiring passed.
