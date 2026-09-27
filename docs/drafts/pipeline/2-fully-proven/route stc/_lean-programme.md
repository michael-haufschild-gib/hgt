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
| P2 ℓ² matrices | `HasLpMatrix`, column obstruction, matrix ⇒ operator uniqueness, `rankOne` matrix/compact, `lpWedge`, rank ≤ 2, transport | `HTGeometry.LpTwoMatrixOperators` (+ `isTraceClass_lpWedge_primes`) | done |
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
| hyperbolic-gap-flat-completion | `HyperbolicGapFlatCompletion` (core) | continuous rigidity (3)-(4), prime-only rigidity via P1, source specialization (2), complex seam (5), domain classification (6), half-density ℓ² | done → 3-formalized |
| hyperbolic-gap-krein-signature | two-point case | general inertia (P5), measure version, finite-channel repair | done → 3-formalized |
| flat-gap-exterior-spectral-reader | abstract no-go | (1),(2),(4)-(6), nonclosability, compact-measure and Gaussian carrier no-go, transport current | done → 3-formalized |
| gamma-prime-hilbert-chamber | — | chamber equivalence, compactness, scalar strong limit, Stokes wall `u>2|g|`, ordered kernel HS | done → 3-formalized |
| prime-height-commutator-calkin-ghost | source identity | ghost operator X on ℓ²(P) | done → 3-formalized |
| prime-square-positivity-wall | `F=-Q'` | Laurent (1), negativity, kernel not PSD | done → 3-formalized |
| source-work-grade-duality | involution + factorization | strict monotone E, no Φ, edge limits, (5),(6), (7) slope and branch uniqueness | done → 3-formalized |
| euler-prime-boundary-tangent-space | Gram limit | S(v)=v⁻²+O(1), (2), density, weak null, Gamma-law limit, (5)-(7), fixed grade | done → 3-formalized |
| prime-boundary-height-fibers | fixed-height limit | ℓ² Gram (1), (2) complete, moving (3), completion (4), reader (7) | done → 3-formalized |
| physical-ordinate-transport-singularity | source Gram, rigged bound | divergence, countable support, (5)-(14) | todo |
| poisson-mertens-clock-commutator | physical column wall | bounded noncompact K, σ_ess=[0,4], commutator, powers, reflected columns, Wiener–Hopf model, HS, phase twist, theta kernel non-selfadjoint | todo |
| mertens-trace-class-xi-divisor-barrier | — | E ∈ S₁, Tr E = 0, signed spectrum, B_θ ∉ S₁, no transport, relative determinant | todo |
| poisson-thermal-chirality-flat-primitive | symbol even/decreasing | multipliers, functional calculus, trace-class lift, sign instability, edge law, boundary trace | todo |
| universal-boundary-pontryagin-countermodel | — | construction, HS, commutator (5), eigenvectors, neutral-subspace bound | done → 3-formalized |

## Log

- 2026-09-27: ledger created; inventory of existing STC leaves done.
- 2026-09-27: P1 layer + four cards closed (modules `STCPrimeWindowPackets`, `STCCofinalTriangleHolonomy`, `STCOrderedCurvatureRank`, `STCGammaPairCalibrationGeometry`; public additions to `RouteRCrossPrimeStokesFourChannelObstruction`).
- 2026-09-27: prime-square-positivity-wall closed (`STCPrimeSquarePositivityWall`).
- 2026-09-27: source-work-grade-duality closed (`STCSourceWorkSeamEnergy`).
- 2026-09-27: P2 layer `LpTwoMatrixOperators`; hyperbolic-gap-flat-completion closed (`STCHyperbolicGapFlatCompletionSource`).
- 2026-09-27: prime-height-commutator-calkin-ghost closed (`STCPrimeHeightCalkinGhost`).
- 2026-09-27: gamma-prime-hilbert-chamber closed (`STCGammaPrimeHilbertChamber`, `STCGammaPrimeWallScaling`); P2 gained `tendsto_inner_lp_of_coord`, `finrank_range_le_card`; `STCOrderedCurvatureRank` gained the det version.
- 2026-09-27: flat-gap-exterior-spectral-reader closed (STCFlatGapSpectralBand, STCFlatGapMeasureReaderNoGo); moved to stage 3.
- 2026-09-27: hyperbolic-gap-krein-signature closed (HTGeometry.ExponentialKernelAlternatingInertia, STCHyperbolicGapKreinSignature); moved to stage 3.
- 2026-09-27: universal-boundary-pontryagin-countermodel closed (STCUniversalBoundaryPontryaginCountermodel, HedenmalmCompactSourceEigenmode, HTGeometry.PontryaginNeutralEigenvectorBound); moved to stage 3.
- 2026-09-27: prime-boundary-height-fibers closed (STCPrimeLogSquarePoleScaling, STCPrimeBoundaryHeightFibers, HTGeometry.ExponentialFeatureTangentSpace); moved to stage 3.
- 2026-09-27: euler-prime-boundary-tangent-space closed (STCPrimeBoundaryTangentSpace, STCPrimeBoundaryGammaLaw); moved to stage 3.

## Plan for the last four cards (2026-09-27)

Order: PMC (poisson-mertens-clock-commutator) → MTC (mertens-trace-class) → PTC (thermal chirality) → POT
(physical-ordinate transport). PMC is the base of MTC and PTC.

- PMC layers: (a) prime shells `S_n = {n ≤ log log p < n+1}`, `m_n → 1` (corpus Mertens II:
  `tendsto_primeRecipSum_sub_logLog`, sharp rate `Sieve.abs_mertensS_sub_logLog_sub_const_le`);
  (b) `K(p,q) = (pq)^{-1/2} h(x_p-x_q)`, `h = sech²(·/2)` (existing `stcPrimePoissonKernel`), bounded by
  weighted Schur test (corpus `WeightedSchurTest`), positive (Poisson Gram); (c) commutator
  `C = (x_p-x_q)K`, bounded, skew; (d) physical powers `T^β` phase diagram (column sums
  `Σ 1/(p (log p)^s)`, s > 0); (e) Calkin model: cell isometry `U`, Wiener–Hopf `W`, `UKU* - W`
  Hilbert–Schmidt, `σ_ess` via Weyl sequences (definition: unit weakly-null approximate eigenvectors),
  `0 ≤ W ≤ 4`, plane-wave packets; (f) reflected kernels; phase twist; theta-inverse self-adjointness no-go.
- MTC layers: trace class of `E = A - W` via block nuclear bounds (cosine-series or H² route), trace zero via
  cell compressions, signed spectrum, theta inverse not trace class (growth / RvM), relative determinant.
- PTC layers: Fourier multiplier of `h` (`4πξ/sinh(πξ)`, corpus `CoshFourierTransform`), commutator
  symbol, trace-class lift, boundary trace anomaly, sign-instability example, edge asymptotics.
- POT layers: Gram (3) (existing `STCPhysicalOrdinateSourceOrthogonality`), norm divergence, countable
  support, exact multiplier (5)–(9), finite-packet interpolation, graph collapse (10), rigged recovery
  (11)–(12) (existing `STCRiggedPrimeSeamBound`), zero-density rigidity (13)–(14), Banach algebra `A_η`.
