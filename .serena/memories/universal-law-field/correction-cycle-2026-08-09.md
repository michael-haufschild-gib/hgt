# Correction cycle after user challenge — 2026-08-09 (Claude)

User verdict on the gas cycles: errors + not corpus-grounded. All three points confirmed.

## Errata applied (in-tree)

1. ULF-GAS-1 Cor 3.2: independent half-planes for the grand response were WRONG; exact coupled
   chamber is Re(sigma+u) > 0 AND Re(sigma+u+v) > 1 (fixed by user/other agent; failure loop 6
   records the counterexample sigma=2, u=v=-0.9).
2. ULF-GAS-3: sigma=1 CLT claim was FALSE — Lindeberg fails at the wall (top-decade primes carry
   jumps of size ~ log P ~ s_P). Corrected: CLT only for 1/2 < sigma < 1; NEW Theorem 3.2 proves
   the sigma=1 limit is the DICKMAN infinitely divisible law (Levy measure du/u on (0,1]) via
   per-prime char functions + Mertens partial summation. Wall fluctuation = macroscopic Poisson
   jumps = condensation signature.
3. ULF-GAS-4 Cor 2.2: conflated the fermionic gas's mode fan with the order-transferred fan. The
   fermionic mode field DOES condense at 1/2 (depth-2 Bernoulli modes); only ORDER-organ
   statements transfer along the Euler law-identity. Corrected with explicit warning. Separation
   sharpened p^3 -> p^2 (deterministic: Z/p^2 vs (Z/p)^2).

## Rediscovery incident (method lesson)

My candidate "regularization license law" (Hadamard normalizer preserves Hankel PSD iff it is a
moment sequence) is ALREADY IN THE CORPUS: `rh-producer-map-corpus.md` §15 +
`HTGeometry/HankelNormalizationPositivity.lean` — and the corpus goes further: §17 multiplicative
blindness theorem (`tendsto_mul_regularized`), §18-20 weld Loewner domination REFUTED by one
quadratic, §21 finite/positive/Hankel trilemma for all linear block combinations, §22 no-defect
escape closed by Hamburger circularity, §23 D0 regularity-undecidability straddle. READ LANE
CARDS TO THE END before conjecturing — memories are not enough.

## New driver

`1-in-progress/universal-law-field/stuck-route-obstruction-matrix.md` (ULF-MATRIX-1): 11 walls
tabulated from proved corpus records; gas layer honestly re-scoped as INSTANCES not explanations;
frozen central-law candidate = REGULARIZATION TRILEMMA (any finite-making observer of a divergent
positive source is leading-blind OR exits positivity with exact budget OR is circular), open core
= one theorem containing corpus branches (a)(b)(c) as corollaries, falsification = a fourth
branch = a new route shape. Queue: 1. trilemma; 2. read UV-corner modules
(archimedeanPrimeEulerQuadraticCorner*) before any gas-relevance claim; 3. prove Schur-complement
degeneracy of the weld escape (heuristic note in matrix §2); 4. Lee-Yang second-jet test;
5. GAS-5 parked.

## Key corpus facts to never re-derive

- Raw prime Grams cofinally PSD free; regularization kills it; multiplicative = blind, subtractive
  = non-PSD (weld), no-defect = circular. One live object: THE UV MODEL (noncompact Euler
  corners, `..._not_isCompactOperator`).
- RH needs an UPPER bound on a count; corpus engines bound below; zero-density ceiling
  (2-2sigma)(2sigma-1); escape needs non-moment structure (Guth-Maynard shape).
- Criterion trichotomy: weaker / per-zero / exactly-RH; only group 3 alive.
- Lee-Yang: survivor E*XiC, E pays log2/2; next test = second central jet tree-uniform floor.
