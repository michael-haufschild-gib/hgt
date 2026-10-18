# Sharp initial-prefix observability

- **Field:** Bézout–Valuation Incidence Mechanics
- **Type:** THEOREM (dependency-closed paper proof and Lean 4 verified)
- **Count:** Contribution 005; verified total **5 / 250**. One connected package.
- **Source:** Extends the exact finite-prefix discrepancy duality package.
- **Target:** Classify weights invisible to an initial interval of prefix observations,
  and prove the exact shortest observation horizon for recovering all nonconstant
  coefficients. An invertibility statement alone is insufficient: retain the explicit
  kernel, reconstruction, and a sharp horizon witness.

## Exact theorem package

Write `L(M)=finiteFloorSum N c M-M*finiteHarmonicSum N c` and `S=min(T,N)`.
For all natural `N,T` and all real weights `c`,

`(∀ 1≤M≤T, L(M)=0)` iff
`T=0 ∨ ((∀ 2≤d≤S, c(d)=0) ∧ (Σ_{d=S+1}^N c(d)/d=0))`.

Thus `L(1),…,L(N-1)` determine `c(2),…,c(N)` uniquely, while `c(1)` is
unobservable. Simultaneous vanishing is equivalent to zero sieve variance.
The statements include `N=0,1` and `T=0`.

For arbitrary data `a(1),…,a(n)`, set `z(1)=a(1)` and
`z(m)=a(m)-a(m-1)` for `m≥2`. The divisor-antidiagonal Möbius lift
`b(d)=Σ_{uv=d} μ(u)z(v)`, followed by the existing endpoint correction
`kerPEndpointWeight (n+1) b`, gives harmonic sum zero and exactly those
observations. This is an explicit inverse; no premise on `a(0)` is needed.
Applying it to actual observations recovers every coefficient `2,…,n+1`.

At level `n+2`, the weight supported at `n+1,n+2` with values `n+1,-(n+2)`
has zero harmonic sum, vanishes at every prefix through `n`, has discrepancy
`n+1` at the next prefix, and has positive sieve variance. Hence the horizon
cannot be shortened at any nontrivial level.

For `Fin n` rows `m=i+1` and columns `d=j+2`, define
`A(m,d)=floor(m/d)-m/d`, `R(m,e)=Re(R_e(m))`, and `T(e,d)=1_{e|d}/d`.
The actual arithmetic matrices satisfy

- `A=R*T` and `det(A)=(-1)^n/(n+1)`;
- `det(T)=1/(n+1)!` and `det(R)=(-1)^n*n!`;
- `K=R*diag(1/φ(e))*Rᵀ` is positive definite,
  `K(m,m)=sievePrefixDualEnergy (n+1) m`, and
  `det(K)=(n!)²/∏_{e=2}^{n+1}φ(e)>0`.

Dimension zero is included. These form one connected observability and
interpolation contribution; the individual corollaries receive no extra credit.

## Prior-work audit

- Deep corpus query `finite prefix discrepancy reconstruct sieve weights minimal
  observations`, 60-second budget, returned 20 candidates and 20 source arguments.
  All names were inspected. Retrieval was partial, with pending coverage and a
  reranking deadline; no novelty conclusion follows from that search alone.
- Exhaustive source-text search for reconstruction/injectivity/observability near
  `discrepancy`, `fractSum`, or `floorSum` found no matching theorem. The nearby
  `ArithmeticInteractionScaleLaw` concerns second-order Leibniz deformation and
  multiplicative scale response, a different object.
- Reuse existing finite divisor inversion and prefix first-difference APIs. Search
  the corpus again by that mechanism before writing new Lean.
- A focused lexical corpus query `Ramanujan determinant` returned zero hits;
  source-text search for the same pair also found no hit. This is limited evidence,
  not a novelty certificate. Broaden to floor/divisor-incidence determinants.
- Broadened deep query `floor function divisor incidence matrix determinant`
  returned 20 candidates and 20 source arguments, all inspected. Retrieval was
  partial after a semantic deadline; the reported source inventory was complete,
  but most compiler metadata was pending or stale. Existing
  `finiteDivisorIncidenceMatrixReal` / `finiteMobiusDivisorIncidenceMatrixComplex`
  and their unit theorems are relevant dependencies to inspect before formalization.
- Complete paper and corpus audits, then formalize exact statements under the field
  directory. This preliminary search did not itself add code, experiments, or count credit.

## Current paper audit and strengthened capstones

For arbitrary `N,T≥0`, put `S=min(T,N)`. The exact all-level statement is

`(∀ M∈[1,T], L_N,c(M)=0)` iff
`T=0 ∨ ((∀ d∈[2,S], c(d)=0) ∧ Σ_{d=S+1}^N c(d)/d=0)`.

The `N=0` and `T=0` cases are empty sums. Otherwise `S≥1`. Vanishing observations
give `s_N,c(m)=H` for `1≤m≤T` by first differences. At `m=1`, `H=c(1)`.
Increasing induction on `2≤m≤S` then gives `c(m)=0`: all proper divisors other
than one have already vanished. Split the harmonic sum at `S`; its remaining tail
must vanish. Conversely, these coefficient conditions give `H=c(1)`, while every
non-one divisor visible at an observed time has index at most `S` and coefficient
zero. Thus every observed increment and prefix discrepancy vanishes.

At `T=N-1`, this kernel is precisely `c(2)=…=c(N)=0`; the final tail contains only
`c(N)/N`. Applying this to `c-b` gives exact reconstruction uniqueness modulo the
constant coefficient. This is also the zero-variance kernel by positivity of the
totient diagonal and the already proved triangular multiples inversion.

For arbitrary prescribed data `a`, normalize only its unobserved value at zero:
`z(1)=a(1)`, `z(m)=a(m)-a(m-1)` for `m≥2`. Define
`b(d)=Σ_{uv=d} μ(u)z(v)` and apply the existing `kerPEndpointWeight (N+1) b`.
Existing Möbius inversion gives divisor sum `z(m)`. Existing endpoint correction
preserves every divisor sum at `m<N+1` and forces harmonic sum zero. Telescoping
therefore realizes every `a(1),…,a(N)` exactly. No premise on `a(0)` is needed.

For every `n≥0`, weights at `n+1,n+2` equal to `n+1,-(n+2)` have harmonic sum zero,
vanish on all prefixes through `n`, and give discrepancy `n+1` at prefix `n+1`.
This witnesses the sharp horizon at every nontrivial level, including level two.

For the determinant package, use `Fin n` rows `m=i+1` and columns `d=j+2` at level
`n+1`. Let `A(m,d)=floor(m/d)-m/d`. The column operation argument above gives
`det(A)=(-1)^n/(n+1)`; the empty determinant case is `n=0`. The exact coordinate
formula from contribution 004 factors `A=R*T`, where `R(m,e)=Re(R_e(m))` and
`T(e,d)=1_{e|d}/d` for `2≤e,d≤n+1`. The latter is upper triangular, with determinant
`1/(n+1)!`. Hence `det(R)=(-1)^n*n!`. The Gram matrix is
`K=R*diag(1/φ(e))*Rᵀ`, giving `det(K)=(n!)²/∏_{e=2}^{n+1}φ(e)>0`.
Since `R` is invertible and the inverse-totient diagonal is positive definite,
the Gram matrix itself is positive definite. This is part of the same package.
Every step uses exact finite identities; no computation or asymptotic premise is used.

The full prefix matrix detects every nonconstant coordinate, including modes invisible
to the Möbius-weighted one-step covariance. The determinant controls volume and rank;
it does not supply a uniform condition-number estimate, a small-discrepancy estimate,
or cancellation for any distinguished arithmetic source. The short-horizon obstruction
is accompanied by its positive survivor: the exact hidden-tail conservation law and
the explicit reconstruction once the sharp horizon is reached.

## Plan and verification gates

`update_plan` is unavailable; this card stores the plan.

1. [x] Renew corpus search and inspect existing divisor-inversion/endpoint APIs.
2. [x] Close the paper proof, including empty levels and the determinant sign.
3. [x] Verify installed-toolchain APIs and formalize kernel, reconstruction, sharp
   horizon, and the connected determinant/Gram identities.
4. [x] Named-source checks, all public axiom closures, umbrella wiring, index, lint,
   ledger update, and cleanup. Count one package only after those gates.

Fresh deep query `finite divisor sum inverse floor prefix determinant` returned
20 candidates and 20 source arguments, all inspected. It was partial with pending
coverage and a semantic timeout; it supplied no competing fixed-prefix theorem.
Focused lexical `sievedDivisorSum` returned all 20 matches (offset 20 was empty).
Existing bulk divisor sums, endpoint preservation, and prefix first differences are
dependencies to reuse. Existing divisor-incidence determinant-one results concern
the incidence matrix, not the centered floor observation matrix above.
An exhaustive source-text sweep for floor-matrix/determinant, prefix reconstruction,
and Ramanujan determinant terms returned 14 lines. All were inspected; the closest
results were generic divisor-defect telescoping, Bernstein–Szegő Toeplitz recovery,
and a conditional prime-insertion budget. None supplies this finite sieve observation
kernel or its exact matrix determinants.

## Verification and disposition

Counted once as contribution 005 after completing the paper proof, novelty audit,
and the following verification gates:

- Installed-toolchain API probes, the mathlib-only determinant prototype, and the
  combined full scratch proof passed Lean. No statement was weakened.
- Named original-source check: `lake --old env lean -j 1 --root=…/formal -o …`,
  exit 0, no warnings or other diagnostics. No probe commands remain in the source.
- Production module:
  `formal/GaloisForLFunctions/BezoutValuationIncidence/SharpInitialPrefixObservabilityAndExactGramDeterminants.lean`.
  It contains 21 public theorems, 8 public definitions, 10 private theorem helpers,
  and 1 private definition: 40 declarations, one contribution.
- All 21 public theorem axiom closures passed, including the simp-tagged
  zero-prefix theorem. Each is exactly `propext`, `Classical.choice`, `Quot.sound`.
  The audit parser checked every name and rejected additional diagnostics.
  Raw audit: `logs/bvi-root-2026-10-18-prefix-observability-axioms.txt`.
- The compiled artifact was installed atomically. SHA-256 matches the checked
  output and the artifact is newer than the unchanged source:
  `0d69a22b5f02dc1b3dabd5ac264fe10bd27e89ac6cca8eaaa27d0e3fdf2e8baa`.
  Source SHA-256:
  `3c0716b0b04f4239363ed29ff78c193d90a56c7295d41a2100fa863123c1733b`.
- All 11 field modules are imported exactly once by the field umbrella. No umbrella
  or full-project Lean build was run.
- `scripts/formal_tools.py index`: exit 0. The focused lexical query returned all
  40 declarations across two pages. Every name, kind, line, module, and source path
  matched exactly; no declaration was sampled or omitted.
- `scripts/formal_tools.py lint`: exit 1, solely for five unrelated missing imports:
  `RHTower.SuzukiCriticalBetaKernel`, `BiScaleUncertainty.ClampedRampLatticeSum`,
  `BiScaleUncertainty.FactorialMuntzBoundaryPole`,
  `BiScaleUncertainty.FactorialMuntzBoundaryRepair`, and
  `BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer`.
  No field or proof-debt findings. This is not a repository-wide passing lint gate.
- Another agent's StationaryResolvent build was replacing shared compiled artifacts.
  Named-source and axiom checks therefore used an isolated compiled-import snapshot.
  A guarded fill confirmed all 9,355 inherited project modules before checking;
  no dependency source or other agent's process was changed.
- All owned processes reached terminal status. Guarded cleanup exited 0 and removed
  all 34 owned `/tmp/bvi5-*` paths, verifying source and installed artifact hashes
  before and after deletion. Whitespace check passed. No numerical experiments.

The next uncounted candidate is
`docs/drafts/pipeline/0-backlog/bvi-integral-prefix-lattice-and-prime-rank-defect-2026-10-18.md`.
Its integral equivalence, prime-rank defects, and proposed canonical Smith factors
still require their own paper, novelty, and Lean audits. General Smith and cokernel
results already in the corpus are dependencies, not new contributions.
