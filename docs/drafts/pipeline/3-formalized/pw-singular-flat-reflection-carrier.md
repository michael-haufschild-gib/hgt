# PW singular flat reflection carrier

- **ID:** PW-SFRC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` PW-B route (read-only ledger)
- **Statement:** The literal first Parikh--Wilczek endpoint winding supplies the unique all-orders-flat positive-ray multiplier forced by exact critical-line Gamma reflection, yielding an explicit continuous-at-zero but nonanalytic source-independent singular/transseries carrier for the missing functional-equation partner.

## Goal

Discharge the singular/transseries carrier premise in the PW-B proof chain

`literal finite-energy PW winding -> singular flat Borel multiplier -> exact Gamma FE partner -> fixed-grade partner balance -> positive Deninger Ward -> RH`.

This theorem does not assume balance and is not an RH receiver: it constructs the previously missing
pre-divisor functional-equation partner carrier directly from the finite-energy source.  Success leaves
one genuinely dynamical burden: derive balance of the resulting forward/reflected pair from a source
law before Xi-copy specialization.

## Frozen proof-chain conjecture

For `x>0`, let `epsilon=x/4`.  The source endpoint identity gives

`W_0(epsilon)=exp(-1/x)`.

Define the positive-ray multiplier

`A(y)=y^(-1/2) exp(sqrt(y)) W_0(sqrt(y)/4)` for `y>0`, and `A(0)=0`.

Equivalently, `A(x^2)=x^(-1) exp(x-1/x)`.  Hence for every logarithmic coordinate
`u in R`, with `x=exp(u)`,

`exp(u/2-exp(u)) A(exp(2u)) = exp(-u/2-exp(-u))`.

Therefore the singular PW log profile is pointwise the reflected Gamma profile.  It is continuous
and integrable, and its Fourier transform is exactly

`Gamma(1/2 + 2*pi*i*xi)`

at every real frequency.  Moreover `A` extends continuously by zero at the Borel origin, is
all-orders flat there, is positive on the positive ray, and is not analytic at zero.  The last
claim is forced both by flat nonvanishing and by the already-proved analytic infinite-row no-go.

## Corpus basis and collision audit

- `schwarzschildParikhWilczekWindingTerm_energyEndpoint`: literal finite-energy source sector is
  `exp(-EndpointAction(n)/epsilon)`.
- `schwarzschildParikhWilczekEndpointAction_zero`: first action is exactly `1/4`.
- `PWAnalyticInfiniteBorelReflectionData.forced_kernel`: Fourier uniqueness forces
  `x exp(-x) A(x^2)=exp(-1/x)` for any exact regular reflection producer.
- `no_PWAnalyticInfiniteBorelReflectionData`: analyticity at zero is impossible.
- `integrable_schwarzschildParikhWilczekReflectedGammaLogProfile` and
  `fourier_schwarzschildParikhWilczekReflectedGammaLogProfile`: target profile and exact Gamma
  transform already closed.
- `not_schwarzschildParikhWilczekFiniteEnergyLocalFEReflectionProducer`: a local reciprocal-energy
  pullback on finite support is impossible; this candidate is a singular nonlocal grade multiplier,
  not that killed branch.
- Corpus search found no construction of the forced multiplier, no identification with the literal
  first endpoint winding, and no existence theorem for a singular PW reflection carrier.

## Literature audit (through 2026-08-30)

- Parikh--Wilczek derives the nonthermal conservation-law action
  `Im S=4*pi*omega*(M-omega/2)` and its endpoint exponential sectors, but no Mellin Gamma-reflection
  multiplier or RH/Ward bridge: arXiv:hep-th/9907001.
- Hatsuda proves Borel summability of Schwarzschild/RN quasinormal WKB series and explains
  exponentially small Stokes ambiguities, but studies QNM spectral resummation rather than the
  PW tunnelling Mellin-grade reflection carrier: arXiv:1906.07232.
- Hatsuda--Shiga (2026) derives exact-WKB quantum-period quantization for extremal RN/Kerr QNMs;
  boundary conditions select spectral quantization, not this PW endpoint/Gamma identity:
  arXiv:2605.01321.
- Costin's rank-one resurgence theorem and exact-WKB literature classify generalized Borel sums and
  Stokes jumps from differential equations/boundary data.  They do not identify the explicit
  source multiplier above or its reflected Gamma transform: arXiv:math/0608408 and
  arXiv:2008.00379.

Novelty claim is the exact cross-model carrier and its rigidity, not the classical fact that
`exp(-1/x)` is flat.

## Gates

- [x] 0 -> 1 in-progress: source-pure frozen conjecture, explicit RH chain, corpus/literature audit
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, direct check, targeted `lake build`, axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, Lean certificate, novelty audit

## Approach

1. Use the first endpoint action at `epsilon=x/4` to identify the forced flat factor exactly.
2. Prove the source-defined multiplier formula and pointwise logarithmic-profile reflection.
3. Transport continuity, integrability, and Fourier/Gamma evaluation through profile equality.
4. Prove continuous extension and all-orders flatness at zero; prove positivity off zero.
5. Use analytic quasianalyticity or the existing analytic no-go to prove nonanalyticity.
6. Package uniqueness: every exact reflection multiplier agrees with this source multiplier on the
   positive ray by the corpus forced-kernel theorem.

## Hostile audit targets

- Multiplier must be constructed before Xi-divisor specialization and contain no Xi data.
- Match the exact scale `epsilon=x/4`; no adjustable action or fitted Stokes constant.
- Prove existence, not only the already-known necessity equation.
- Prove uniqueness on the full positive ray.
- Do not claim the carrier forces partner balance; isolate that remaining dynamical premise.

## Paper proof `[PROVED HERE]`

Write `W_0(epsilon)` for the first literal endpoint winding.  For `x>0`, put
`epsilon=x/4`.  The exact endpoint theorem and `EndpointAction(0)=1/4` give

`W_0(x/4)=exp(-(1/4)/(x/4))=exp(-1/x)`.                                      (1)

Define `A:R->R` by `A(y)=0` for `y<=0`, and for `y>0` by

`A(y)=sqrt(y)^(-1) exp(sqrt(y)) W_0(sqrt(y)/4)`.

Using (1) with `x=sqrt(y)` gives the closed source formula

`A(y)=sqrt(y)^(-1) exp(sqrt(y)-1/sqrt(y))`.                                  (2)

In particular `A(y)>0` for every `y>0`.  This is not a fitted Stokes coefficient: action,
normalization, and scale are all fixed by the literal first endpoint winding.

For continuity at zero, set `t=1/sqrt(y)`.  As `y->0+`, `t->+infinity`, and (2) becomes

`A(y)=t exp(1/t-t)`.

Here `exp(1/t)->1`, while `t exp(-t)->0`; hence `A(y)->0=A(0)`.  On the negative half-line
`A` is identically zero, and away from zero continuity is elementary, so `A` is continuous on
`R`.  More strongly, for every natural `N`,

`A(y)/y^N = t^(2N+1) exp(1/t-t) -> 0`,                                      (3)

because every polynomial is dominated by `exp(t)`.  Thus the carrier is all-orders flat at the
Borel origin.

Now let `u` be real and set `x=exp(u)`.  Since `exp(2u)=x^2`, (2) gives

`A(exp(2u))=exp(-u) exp(exp(u)-exp(-u))`.

Multiplication by the forward PW logarithmic Gamma profile yields

`exp(u/2-exp(u)) A(exp(2u))
 = exp(-u/2-exp(-u))`.                                                       (4)

The right side is exactly `schwarzschildParikhWilczekReflectedGammaLogProfile(u)`.
Consequently the source-built singular profile is continuous and integrable, and equality under
the Fourier integral together with the corpus Gamma transform gives, for every real `xi`,

`Fourier(profile_A)(xi)=Gamma(1/2+2*pi*xi*i)`.                               (5)

This proves existence of the missing source-independent nonanalytic reflection carrier.

It is also unique on the positive ray.  Let `B` be any multiplier whose logarithmic profile is
continuous and integrable and whose Fourier transform equals the reflected target at every real
frequency.  `L1` Fourier uniqueness gives equality of the two profiles almost everywhere;
continuity upgrades this to pointwise equality.  The forward exponential factor never vanishes,
so solving the pointwise equation gives

`B(exp(2u))=exp(-u) exp(exp(u)-exp(-u))=A(exp(2u))`.

Every positive `y` is `exp(2u)` for `u=(log y)/2`, hence `B(y)=A(y)` for all `y>0`.

Finally no globally continuous complex multiplier analytic at zero can restrict to this carrier.
If such a multiplier existed, positive-ray agreement and (4) would make its logarithmic profile
identically the reflected profile.  It would therefore populate every field of
`PWAnalyticInfiniteBorelReflectionData`, contradicting the dependency-closed theorem
`no_PWAnalyticInfiniteBorelReflectionData`.  Equivalently, (3), positivity, and analytic
quasianalyticity already give the contradiction.  Thus the exact carrier lies sharply in the
all-orders-flat nonanalytic sector left open by the prior analytic no-go.

## Hostile audit

- **Pre-divisor construction:** `A` uses only PW endpoint action and elementary exponentials; no
  Xi zero, zeta value, or RH predicate occurs.
- **Scale rigidity:** `epsilon=x/4` is forced by endpoint action `1/4`; no free parameter remains.
- **Existence versus necessity:** equation (4) constructs an actual profile; it does not merely
  repeat the prior forced-kernel equation.
- **Full positive-ray uniqueness:** exponential parametrization is surjective onto `(0,infinity)`.
- **Integrability:** inherited from literal pointwise equality with the already-proved reflected
  Gamma profile, not assumed as an asymptotic heuristic.
- **Analytic boundary:** continuous and all-orders flat, positive immediately to the right, hence
  necessarily nonanalytic; this exactly evades rather than contradicts the analytic no-go.
- **Remaining burden:** nothing here forces forward/reflected partner balance on Xi copies.  The
  only surviving PW-B step is a genuine source law producing that balance (or equivalent positive
  Ward cancellation).

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekSingularFlatReflectionCarrier.lean`
- Unconditional carrier theorem:
  `RHTower.schwarzschildParikhWilczek_singularFlatReflectionCarrier`.
- Exact source weld:
  `RHTower.schwarzschildParikhWilczekSingularFlatMultiplier_eq_source`.
- All-orders-flat certificate:
  `RHTower.tendsto_schwarzschildParikhWilczekSingularFlatMultiplier_div_pow_zero`.
- Reflected-Gamma transform:
  `RHTower.fourier_schwarzschildParikhWilczekSingularFlatLogProfile`.
- Positive-ray uniqueness:
  `RHTower.PWPositiveRaySingularBorelReflectionData.multiplier_eq_source_of_pos`.
- Sharp analytic exclusion:
  `RHTower.no_continuous_analytic_schwarzschildParikhWilczekSingularFlatMultiplier_extension`.
- Direct `lake env lean` check and targeted module build pass; module is wired into
  `GaloisForLFunctions.RHTower` without building the umbrella.
- Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
- Global lint remains nonzero solely because unrelated shared-worktree modules are currently
  unwired; this module is reachable and appears in no lint error.

## Log

- 2026-08-30 — frozen at Stage 1 after corpus and primary-literature collision audits.
- 2026-08-30 — `[PROVED HERE]`; source scale, profile identity, continuity/flatness, Fourier
  reflection, positive-ray uniqueness, and nonanalyticity audit closed; promoted to Stage 2.
- 2026-08-30 — exact carrier, rigidity, flatness, and analytic-exclusion package formalized,
  directly checked, targeted-built, wired, and axiom-audited; promoted to Stage 3.
