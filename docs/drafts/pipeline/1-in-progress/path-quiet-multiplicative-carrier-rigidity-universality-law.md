# Path-quiet multiplicative-carrier rigidity universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.PathQuietMultiplicativeCarrierRigidityUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`QuietPathRigidity.quiet_path_rigidity` proves that arbitrary high C¹ crossings with vanishing
length-weighted quiet budget annihilate every Dirichlet coefficient of index at least two.
`GaussianQuietMultiplicativeCarrierRigidityUniversalityLaw` shows how coefficient annihilation,
multiplicative normalization, and analytic continuation turn the distinct Gaussian straight-strip
mechanism into global carrier triviality.

Corpus research finds no theorem applying that global upgrade to arbitrary path quietness.

## Statement

Let `F` be entire, exactly reflection-symmetric, and represented on `Re s ≥ c`, `c ≥ 1/2`, by the
Dirichlet series of a multiplicative arithmetic function `a`. Suppose one has top and bottom C¹
crossing paths at heights comparable to `±T_k`, carrier bound `q_k`, path length at most `L_k`, and

`(q_k L_k + 1) / T_k² → 0`.

Then `F(s) = 1` for every complex `s`.

## Dependency-closed proof

1. `quiet_path_rigidity` gives `a n = 0` for every `n ≥ 2`.
2. The Dirichlet term at zero vanishes by definition.
3. Multiplicativity gives `a 1 = 1`.
4. Hence the absolutely convergent L-series equals `1` throughout the representing half-plane.
5. `F` agrees with that L-series there. The open half-plane `c < Re s` supplies an eventual
   equality near `c + 1`.
6. The identity theorem on connected `ℂ` extends `F = 1` globally.

No integer-valued coefficient hypothesis, zero computation, or new analytic premise is added.

## Novelty audit

Corpus audit: Gaussian all-scale quietness has a global multiplicative-carrier theorem; arbitrary
C¹ path quietness has only coefficient annihilation. This global path theorem is absent.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/PathQuietMultiplicativeCarrierRigidityUniversalityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.
