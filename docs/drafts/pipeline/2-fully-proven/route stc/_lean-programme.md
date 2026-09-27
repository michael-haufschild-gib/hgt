# Route STC folder → stage 3: Lean programme ledger

Goal (user /goal, 2026-09-27): formalize, unconditionally, every paper theorem of every card in this
folder; move each card to `3-formalized/route stc/` when all its displayed results have closed Lean
theorems (`lake --old env lean` clean, `#print axioms` = propext/Classical.choice/Quot.sound only,
wired into `RHTower.lean`/`HTGeometry.lean`). Delete this file when the folder is empty.

Stage-3 convention (as for theta): `git mv` card into `3-formalized/route stc/`, set Stage/Status,
append a Log line, add `<card>-formalized.md` certificate (module + table card item → Lean theorem).

## Shared layers (build once, reuse)

| Layer | Content | Module | Status |
|-|-|-|-|
| P1 prime windows | `prime_between` iterated: n primes in `(P,(1+ε)^n P]`, cofinal; prime triples with `q/p→e^d`, `r/q→e^e` | `STCPrimeWindowPackets` | done |
| P2 prime ℓ² matrices | column-not-ℓ² ⇒ no bounded operator; rank-one `P_x`; finite-rank ⇒ compact; HS kernels | search corpus (`DiagonalEllTwoOperator`, `HilbertSchmidtOperator`, `SoninCalkinNormBound`) | audit |
| P3 prime-log-square pole | `F(v)=Σ(log p)²p^{-1-v} = v^{-2}+O(1)`, complex version near 0 in `Re>0` | `PrimeLogPowZetaAbelPole`, `STCPrimeHeightFiberAbel` | audit |
| P4 Laplace/exponential density | exponentials dense in `L²((0,∞),t dt)`; Laplace continuity | search corpus | audit |
| P5 hyperbolic sinc kernel | `S(g(x-y)/2) = (1/a)∫ e^{u(x-y)}`, Andréief, exp-Vandermonde sign, inertia | `Zeta5AndreiefTransfer`, `NavierStokesRealExponentialVandermonde` | audit |
| P6 operator ideals | trace class / HS / essential norm / Calkin on `L²(0,∞)` and `ℓ²(P)` | `SchattenOneBanach`, `HilbertSchmidtOperator`, `SoninTimeBandHilbertSchmidt` | audit |

## Cards (status: todo / partial / done)

| Card | Existing Lean | Missing | Status |
|-|-|-|-|
| odd-curvature-three-prime-obstruction | `RouteRCrossPrimeStokesFourChannelObstruction` | public limit statement (2), gauge invariance (4), olean | done → 3-formalized |
| all-prime-gamma-stokes-pair-bridge | `DeningerGammaAllPrimeStokesPairBridge` | (5) all ordered quadruples, no rank-one calibration, `K/(BB)=n log(q/p)/4`, inf = 0 (PNT), rank ≤2/≤4 packets, no scalar×rescaling identification (needs ordered-rank) | done → 3-formalized |
| cofinal-triangle-holonomy-all-grades | — | (1) limit, (2a) rational normal form, (5) correction lower bound, non-Hilbert divergence | done → 3-formalized |
| ordered-curvature-unbounded-rank | four-channel identity | rank ≤4 symmetric, rank n ordered via P1 + det continuity, S_n invertible, fixed-k no-go | done → 3-formalized |
| hyperbolic-gap-flat-completion | `HyperbolicGapFlatCompletion` (core) | continuous rigidity (3)-(4), prime-only rigidity via P1, source specialization (2), complex seam (5), domain classification (6), half-density ℓ² | todo |
| hyperbolic-gap-krein-signature | two-point case | general inertia (P5), measure version, finite-channel repair | todo |
| flat-gap-exterior-spectral-reader | abstract no-go | (1),(2),(4)-(6), nonclosability, compact-measure and Gaussian carrier no-go, transport current | todo |
| gamma-prime-hilbert-chamber | — | chamber equivalence, compactness, scalar strong limit, Stokes wall `u>2|g|`, ordered kernel HS | todo |
| prime-height-commutator-calkin-ghost | source identity | ghost operator X on ℓ²(P) | todo |
| prime-square-positivity-wall | `F=-Q'` | Laurent (1), negativity, kernel not PSD | done → 3-formalized |
| source-work-grade-duality | involution + factorization | strict monotone E, no Φ, edge limits, (5),(6), (7) slope and branch uniqueness | done → 3-formalized |
| euler-prime-boundary-tangent-space | Gram limit | S(v)=v⁻²+O(1), (2), density, weak null, Gamma-law limit, (5)-(7), fixed grade | todo |
| prime-boundary-height-fibers | fixed-height limit | ℓ² Gram (1), (2) complete, moving (3), completion (4), reader (7) | todo |
| physical-ordinate-transport-singularity | source Gram, rigged bound | divergence, countable support, (5)-(14) | todo |
| poisson-mertens-clock-commutator | physical column wall | bounded noncompact K, σ_ess=[0,4], commutator, powers, reflected columns, Wiener–Hopf model, HS, phase twist, theta kernel non-selfadjoint | todo |
| mertens-trace-class-xi-divisor-barrier | — | E ∈ S₁, Tr E = 0, signed spectrum, B_θ ∉ S₁, no transport, relative determinant | todo |
| poisson-thermal-chirality-flat-primitive | symbol even/decreasing | multipliers, functional calculus, trace-class lift, sign instability, edge law, boundary trace | todo |
| universal-boundary-pontryagin-countermodel | — | construction, HS, commutator (5), eigenvectors, neutral-subspace bound | todo |

## Log

- 2026-09-27: ledger created; inventory of existing STC leaves done.
- 2026-09-27: P1 layer + four cards closed (modules `STCPrimeWindowPackets`, `STCCofinalTriangleHolonomy`, `STCOrderedCurvatureRank`, `STCGammaPairCalibrationGeometry`; public additions to `RouteRCrossPrimeStokesFourChannelObstruction`).
- 2026-09-27: prime-square-positivity-wall closed (`STCPrimeSquarePositivityWall`).
- 2026-09-27: source-work-grade-duality closed (`STCSourceWorkSeamEnergy`).
