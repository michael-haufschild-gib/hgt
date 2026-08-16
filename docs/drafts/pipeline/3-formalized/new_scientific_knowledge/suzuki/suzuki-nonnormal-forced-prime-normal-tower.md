# Nonnormal Source-Forced Prime-Normal Tower

- **ID:** suzuki-nonnormal-forced-prime-normal-tower
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route O / Suzuki finite-recurrence trace-zero higher-rank frontier
- **Statement:** Every finite source-forced prime-normal tower for an arbitrary bounded, possibly nonnormal adjacency solves the exact differential equation up to one explicit next-word residual.

## Goal

Remove self-adjointness and normality from the source-selected prime-normal expansion.  This is the
prime part of the higher-rank finite-to-flat connector.  It does not replace the still-missing
Gamma/logistic/exterior coupling.

## Gates

- [x] 0 → 1 in-progress: exact source equation and collision audit fixed
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: unconditional Lean theorem, leaf build green, axiom audit standard-only
- [ ] 3 → 4 publication-ready: standalone exposition and external peer audit

## Theorem

Let (X) be a complex normed space, let (B:X\to X) be any bounded complex-linear operator, and
let (A\in X).  No adjoint, normality, diagonalizability, or spectral hypothesis is imposed.  For
(m,k\in\mathbb N), put
[
  \alpha=m+\tfrac12,qquad
  f_{m,0}=\frac{2m+1}{4m+4},
  qquad
  f_{m,k+1}=f_{m,k}\frac{2(m+k)+3}{4(m+k)+8},
]
and
[
  v_{m,k}=f_{m,k}B^kA,qquad
  F_{m,N}(t)=\sum_{k=0}^{N}e^{-(\alpha+k+1)t}v_{m,k}.
]
Define the reparametrized prime-normal expression
[
  \mathcal D_{B,t}(F,\dot F)
    =2e^t\dot F-B\dot F+e^tF .
]
Then, for every (m,N,t,B,A),
[
  \mathcal D_{B,t}(F_{m,N},\dot F_{m,N})
  =-\alpha e^{-\alpha t}A
   +(\alpha+N+1)e^{-(\alpha+N+1)t}Bv_{m,N}.                 \tag{1}
]
Thus every interior operator word cancels exactly and truncation exposes precisely the next omitted
word.

The coefficients also satisfy
[
  f_{m,k}\,\theta_m=\theta_{m+k+1},qquad
  0<f_{m,k}\le 2^{-(k+1)},                                  \tag{2}
]
where (	heta_k) is the corpus's universal Suzuki prime-normal grade factor.  Consequently
[
  \lVert v_{m,k}\rVert
  \le 2^{-(k+1)}\lVert B\rVert^k\lVert A\rVert.           \tag{3}
]

## Proof [PROVED HERE]

For one term (e^{-(\alpha+k+1)t}v_{m,k}), direct differentiation gives
[
\begin{aligned}
 \mathcal D_{B,t}
 &\left(e^{-(\alpha+k+1)t}v_{m,k},
  -(\alpha+k+1)e^{-(\alpha+k+1)t}v_{m,k}\right)\\
 &=
 -(2\alpha+2k+1)e^{-(\alpha+k)t}v_{m,k}
 +(\alpha+k+1)e^{-(\alpha+k+1)t}Bv_{m,k}.                  \tag{4}
\end{aligned}
]
The initial recurrence
[
  -(2\alpha+1)f_{m,0}=-\alpha
]
makes the first diagonal term in (4) exactly the source in (1).  The successor recurrence is
equivalent to
[
 -(2\alpha+2k+3)v_{m,k+1}+(\alpha+k+1)Bv_{m,k}=0.          \tag{5}
]
The second term of grade (k) and first term of grade (k+1) have the same exponential factor, so
(5) cancels them.  Induction over the finite prefix leaves only the source and terminal residual,
proving (1).

The identity in (2) follows by induction from the grade recurrence for (	heta): the (k=0)
factor is exactly (	heta_{m+1}/	heta_m), and each successor multiplier is the next (	heta)
ratio.  Each ratio is strictly positive and at most (1/2), proving the coefficient bound.
Submultiplicativity of bounded operators gives (3).

## Scientific content and frontier effect

Existing corpus results split into two weaker regimes:

1. the universal prime-normal coefficient recurrence, without an exact arbitrary-operator forced
   prefix law; and
2. the literal one-prime terminal block, where nonnormality is removed by a special (2\times2)
   diagonal similarity.

Equation (1) works for arbitrary bounded (B), including higher-rank nondiagonalizable operators,
and identifies the truncation defect rather than assuming it away.  It therefore eliminates
self-adjointness/normality as an algebraic obstruction in the prime-forced source-normal tower.
Remaining finite-to-flat obstruction is now localized to control and identification of the delayed
Gamma/logistic/exterior forcing acting on this tower.

## Novelty audit

- Internal searches used `scripts/formal_tools.py research` for “Suzuki nonnormal forced prime
  normal finite truncation residual”, “source selected finite-to-flat higher rank Gamma”, and
  “arbitrary finite conormal expansion source”.  No theorem with (1), arbitrary (B), and the exact
  (	heta)-tail quotient (2) was found.
- Closest internal result, `SuzukiOnePrimeTerminalForcedHardy`, uses a special one-prime diagonal
  similarity and does not imply the arbitrary-adjacency telescoping law.
- Literature audit included Suzuki's 2022–2026 screw-function and Hamiltonian papers.  Generic
  operator binomial/Neumann expansions are classical; novelty claimed here is only the exact
  source-forced Suzuki recurrence, its nonnormal finite residual law, and its identification with
  the existing prime-normal grade sequence.

## Hostile audit

- No infinite-series convergence is claimed for arbitrary (B); (1) is a finite exact identity.
- No Gamma factor is deleted or treated as lower order.
- No bound on the literal higher-rank propagator follows from (3) alone when (lVert B\rVert\ge2).
- No finite-to-flat limit, source/Gamma naturality, or RH conclusion is claimed.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.SuzukiNonnormalForcedPrimeNormalTower`
- **Capstone:** `suzukiNonnormalPrimeExpression_partial_eq_source_add_residual`
- **Coefficient identification:** `suzukiForcedPrimeNormalFactor_mul_gradeFactor`
- **Uniform word bound:** `norm_suzukiForcedPrimeNormalTower_le`
- **Derivative certificate:** `hasDerivAt_suzukiForcedPrimeNormalPartial`
- **Verification:** `lake env lean GaloisForLFunctions/RHTower/SuzukiNonnormalForcedPrimeNormalTower.lean`
- **Leaf build:** `lake build GaloisForLFunctions.RHTower.SuzukiNonnormalForcedPrimeNormalTower`
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`

## Log

- 2026-08-16 — corpus-first collision audit; theorem originated and proved on paper.
- 2026-08-16 — unconditional Lean formalization, umbrella wiring, leaf build, and axiom audit complete.
