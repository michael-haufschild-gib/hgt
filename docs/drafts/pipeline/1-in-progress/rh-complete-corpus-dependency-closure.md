# RH Complete-Corpus Dependency Closure

- **ID:** rh-complete-corpus-dependency-closure
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** complete current `formal/` tree and every current card under `docs/drafts/pipeline/`
- **Statement:** The current research corpus contains a source-clean finite dependency DAG whose terminal theorem is `RiemannHypothesis`; every missing edge can be stated as an explicit non-circular glue lemma and proved from other corpus nodes.

## Goal

Construct the full backward dependency graph from every formal RH endpoint, match its hypotheses against all Lean declarations and pipeline theorems regardless of status, and close the strongest surviving chain. The proof may use any mathematical detour and any finite chain length. No umbrella import, named route taxonomy, card stage, or literature-shaped decomposition is authoritative over the actual current declarations and proofs.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem `<name>`, touched modules green, formal lint PASS
- [ ] 3 → 4 publication-ready: standalone paper with theorem, proof, Lean certificate, and Door-2

## Constraint

The authoritative corpus is exactly:

1. every Lean file under `formal/`, including files not reachable from `GaloisForLFunctions.lean` or `GaloisForLFunctions.RHTower`;
2. every pipeline card under stages `0` through `5`, read by mathematical content rather than status label.

Prior Route A–D summaries and umbrella-level capstone lists are excluded from the proof search.

## Attack

1. Enumerate every formal theorem concluding `RiemannHypothesis` or an equivalent proposition.
2. Normalize each endpoint into primitive hypotheses and reject hypotheses that merely restate RH or feed the zero divisor into the source.
3. Search all formal declarations and all pipeline claims for producers of each primitive hypothesis, including producers expressed in different coordinates.
4. Generate several competing cross-corpus chains before selecting one.
5. Attack the best chain through boundary, symmetric, degenerate, fake-family, and parent-theory cases.
6. Promote an edge only after its paper proof is complete; promote the terminal chain only after Lean verification.

## Current Open Core

[OPEN CORE] Construct, from the completed Euler--Gamma source before reading the Xi divisor, the
cofinal Gauss/Sonin realization of the diagonal Fock lift

```text
T_0 k_x = k_x tensor (t |-> exp(-x t)),
```

and prove it contractive on the safe completed-source RKHS.  Equivalently, prove the
source-resolved four-channel passivity inequality for every finite rational-node packet and pass
to the closed cofinal graph without losing the defect index.  This is the narrowest surviving
source-side statement found in the complete corpus; its defect index is exactly the total
right-half off-line Xi multiplicity.

## Environment-wide audit `[PROVED]`

- The current tree contains 1,672 Lean files.  The root umbrella reaches 1,624 and misses 48.
- Three RH-bearing modules are outside the root closure:
  `CompletedFluxLaguerreReader`, `CompletedSEMContourBoundary`, and `PrimeClockScaleFactor`.
- Importing the root together with those omitted RH-bearing modules yields 133 declarations whose
  types mention `RiemannHypothesis` and no unconditional declaration of `RiemannHypothesis`.
- The omitted criteria are exact readers or selectors.  None supplies an unconditional producer
  for its RH-bearing premise.

Thus the umbrella gap concealed criteria but not a completed proof.  The dependency search must
construct one new source-to-orientation edge.

## Corpus-wide charge collapse `[PROVED FROM CURRENT CARDS]`

The strongest analytically faithful criteria are not independent missing hypotheses.  They carry
one common integer obstruction:

```text
total right-half off-line Xi multiplicity
  = ind_-(J),
J(x,y) = [Q(x)+Q(y)]/(x+y),
Q(x) = Xi'(1/2+x)/Xi(1/2+x),
  = sup_(a>0) kappa(a)
  = ind_-(I-T_0^*T_0).
```

Here `kappa(a)` is the restricted-Weil aperture Morse charge.  The real Euler-ray kernel uses only
absolutely convergent completed Euler data at `1/2+x>1`; the aperture realization and the diagonal
Fock realization preserve its complete negative index.  Consequently proving any one of these
three carriers nonnegative proves RH, but transporting between them cannot by itself remove the
charge.

## Candidate attacks and verdicts

1. **Square Evans/source normalization.**  The finite Evans determinant and the non-Schatten
   Birman--Schwinger line exactly detect the aperture spectrum.  The final inequality
   `bar_mu_a ||(A_a^+ + bar_mu_a I)^(-1)|| < 1` is algebraically equivalent to `A_a^+>0` and
   therefore contributes no coercivity.  `[BRIDGE; NOT THE MISSING EDGE]`
2. **Aperture spectral flow.**  The charge starts at zero, is integer-valued and nondecreasing, and
   every off-line packet appears at a finite aperture.  Orientation of the determinant line counts
   crossings but does not forbid the first crossing.  `[BRIDGE; NEEDS A SOURCE NO-CROSSING LAW]`
3. **Real Euler-ray complete positivity.**  The cofinal shifted family collapses to the single
   kernel `J` above.  Pointwise positivity of `Q` and the safe kernel with denominator `x+y-1` do
   not cross the half-unit seam: the scalar Schur ratio is indefinite on every distinct pair.
   `[LIVE, BUT RH-EQUIVALENT UNTIL A SOURCE FACTORIZATION IS BUILT]`
4. **Finite Gauss/subset Fock carriers.**  Every finite place set has a canonical positive graded
   carrier and compact Hardy realization.  The missing theorem is uniform channel-resolved
   Gauss/Sonin convergence to `T_0` with contraction and index preservation.  This is the strongest
   surviving constructive path because its finite objects are unconditionally positive and retain
   prime labels, Gamma covariance, and the critical Mellin defect.  `[SELECTED]`
5. **Critical contour-jump energy.**  A source bound `||ell_E||_2^2<=4` would exclude even one
   off-line zero.  Current source identities determine the causal Euler-line continuation, whereas
   `ell_E` is the difference between that continuation and the critical Hardy boundary.  Identifying
   the two without a new boundary theorem is circular.  `[SECONDARY LIVE PATH]`
6. **Differential/hypertranscendental forcing.**  Finite rational quartet or residue surgery
   preserves the complete translated differential field and every finite structural matroid while
   changing the orientation index arbitrarily.  Joint Hurwitz monodromy and universal constraint
   geometry therefore cannot select the RH chamber without an additional pointed infinite source
   section.  `[NO-GO AS A STANDALONE SELECTOR]`

## Status Registers

- [CONJECTURE] A long cross-coordinate chain exists and is hidden by the present file and card partitioning.
- [PROVED] The corpus contains no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration according to the current generated gap report.
- [PROVED] No unconditional Lean declaration of `RiemannHypothesis` exists in the combined current RH-bearing environment.
- [OPEN CORE] Prove the source-resolved diagonal-Fock contraction, or construct a genuinely different source law that annihilates the same integer charge.
- [NOVELTY UNVERIFIED] Any completed glue theorem remains scientifically unclassified until the proof, parent-theory, literature, and rediscovery gates are run.

## Log

- 2026-07-12 — moved directly into progress for complete-corpus dependency reconstruction.
