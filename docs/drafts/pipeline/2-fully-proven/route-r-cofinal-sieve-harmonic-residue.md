# Route R cofinal sieve harmonic residue

- **ID:** route-r-cofinal-sieve-harmonic-residue
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `cofinal-bockstein-polarized-adelic-stokes.md` · first-wall open core
- **Statement:** Conditional Euler-sieve tail variation recovers, coefficient-faithfully and independently of summable perturbations, the oriented `1/p` coefficient of every Route R critical-wall prime field.

## Goal

Replace the abstract phrase “harmonic residue” in
`[OPEN CORE — ROUTE_R_FIRST_WALL_SOURCE_RESIDUE_VANISHING]` by an explicit pre-divisor source
operation. The operation must be defined only from an enumeration of ordinary primes and nested
Euler-sieve densities, must ignore every `ell^1` perturbation cofinally, and must recover the
already-proved critical-wall orientations `-1`, `0`, `+1`.

This does not assume a Xi zero is critical. It constructs the coefficient-faithful source reporter
whose zero-limit law remains to be derived from fixed-source-orientation Stokes/Cartier structure.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and refreshed external novelty audit

## Internal corpus audit

- `[CORPUS]` `PrimeSieveDensityTelescope` proves that losses
  `D_n / p_n`, where `D_n=prod_{k<n}(1-1/p_k)`, are positive and sum to one.
- `[CORPUS]` `RouteRPrimeSieveVariationCapReporter` uses the unshifted mass-one measure as a
  convergent consumer of the prime-log cap. It does not descend modulo `ell^1`.
- `[CORPUS]` `RouteRCriticalWallOrientedHarmonicQuantization` proves that the moving first-wall
  coefficient is `-1/p`, `0`, or `+1/p` modulo `ell^1`, according to grade orientation.
- `[CORPUS]` `DeningerRealKummerArakelovBoundary` closes finite prime packets only after adding an
  archimedean logarithmic coordinate; it has no all-prime harmonic residue.
- `[CORPUS]` `RouteRDegreeSixBVGreenPhysicalCyclicDescentWall` constructs a normalized cyclic source
  reader but proves that agreement with fixed physical evaluation is still the RH-bearing step.

No corpus theorem constructs a cofinal reporter whose limit factors through the affine quotient
`C·(1/p) + ell^1`.

## External audit

Classical Mertens/sieve sources contain the finite product
`prod_{p≤x}(1-1/p)` and its decay; probabilistic sieve literature treats local loss measures.
Searches for “conditional Euler product sieve tail”, “prime harmonic l1 quotient residue”, and
“sieve density tail probability” found no source stating the cofinal coefficient-recovery theorem
below or its Route R critical-wall application. The nearest background located was Kowalski's
abstract probabilistic large-sieve framework (`arXiv:math/0610021`) and standard expositions of
Mertens's product theorem. Novelty status remains `[NOVELTY UNVERIFIED]`; no literature priority is
claimed.

## Conjecture loop

### Attempt 1 — unshifted sieve reporter `[FALSIFIED]`

For one fixed enumeration `e`, try

`R(a)=sum_n (D_n/p_n) · p_n a_n = sum_n D_n a_n`.

It gives `R(1/p)=1`, but for `a=c/p+b` with `b in ell^1` it gives
`R(a)=c+sum_n D_n b_n`. The second term generally is nonzero. Thus the unshifted reporter is a
positive detector but not coefficient-faithful on the harmonic quotient.

**Positive survivor.** Restart the same source measure after every finite prime prefix. Summable
errors then live in a shrinking tail.

### Attempt 2 — normalized global tail `[FALSIFIED AS REPRESENTATION]`

Divide the global loss tail after `N` by remaining mass `D_N`. This is mathematically correct, but
it hides the source geometry behind a quotient by a small number and complicates positivity at the
formal level.

**Stronger replacement.** Rebuild the nested sieve from density one on the literal tail
`e(N),e(N+1),...`. Its density is automatically in `(0,1]`; no division or nonzero premise occurs.

### Attempt 3 — cofinal restarted sieve residue `[PROVED HERE] [BRIDGE] [NOVELTY UNVERIFIED]`

Let `e : N ≃ Primes`. For `N,n≥0`, put

`D_{N,n}=prod_{k<n}(1-1/e(N+k))`, `w_{N,n}=D_{N,n}/e(N+n)`

and, for a prime field `a`,

`S_N(a)=sum_{n≥0} D_{N,n} a(e(N+n))
       =sum_{n≥0} w_{N,n} e(N+n)a(e(N+n))`.

Then:

1. `w_{N,n}>0` and `sum_n w_{N,n}=1` for every `N`;
2. if `b` is summable over the primes, then
   `|S_N(b)| ≤ sum_n |b(e(N+n))| → 0`;
3. if `a(p)=c/p+b(p)` with `b in ell^1`, then `S_N(a)→c`;
4. the coefficient `c` is unique and the limit is independent of enumeration;
5. for the Route R critical-wall coefficient `W_t`,
   `S_N(W_t)→-1` for `t>0`, `0` for `t=0`, and `+1` for `t<0`.

## Complete paper proof `[PROVED HERE]`

Every factor `1-1/e(N+k)` lies strictly between zero and one, so
`0<D_{N,n}≤1`. The recurrence

`D_{N,n+1}=D_{N,n}(1-1/e(N+n))`

gives the exact loss identity

`D_{N,n}-D_{N,n+1}=D_{N,n}/e(N+n)=w_{N,n}`.

Hence finite sums telescope:

`sum_{n<M} w_{N,n}=1-D_{N,M}`.

The reciprocal-prime series remains divergent after deletion of the first `N` terms. Since
`1-x≤exp(-x)` for `x≥0`,

`0<D_{N,M}≤exp(-sum_{n<M} 1/e(N+n))→0`.

Therefore `sum_n w_{N,n}=1`, proving (1).

If `b` is summable, absolute convergence of `S_N(b)` follows from `D_{N,n}≤1`, and

`|S_N(b)|≤sum_n D_{N,n}|b(e(N+n))|
           ≤sum_n |b(e(N+n))|`.

The last quantity tends to zero because it is the tail of a convergent nonnegative series. This
proves (2). For `h(p)=1/p`, the identity `D_{N,n}h(e(N+n))=w_{N,n}` and (1) give
`S_N(h)=1`. Linearity now yields `S_N(c h+b)=c+S_N(b)→c`, proving (3). If two coefficients `c,d`
represent the same field modulo `ell^1`, the same cofinal reporters tend to both `c` and `d`; limit
uniqueness gives `c=d`. Because this proof works for every enumeration, (4) follows.

For `t>0`, the prior critical-wall theorem gives `W_t+h in ell^1`, so (3) with `c=-1` gives
`S_N(W_t)→-1`. For `t<0`, it gives `W_t-h in ell^1`, hence limit `+1`. At `t=0`, `W_t=0`.
This proves (5).

## Hostile audit

- No RH premise, divisor criticality, fixed-ideal preservation, or physical cyclic descent occurs.
- Reporter is not declared zero. Its off-centre limits are explicitly nonzero, preventing circular
  use as an annihilator.
- Construction is not another equivalent endpoint: it adds an explicit source functor from nested
  prime-sieve variation to the harmonic quotient and proves stability under all summable errors.
- Result does not close Route R. Remaining theorem is now concrete: fixed-source-orientation
  Stokes/Cartier structure must force `S_N(W_{t_rho})→0` at Xi support points. Quantization and limit
  uniqueness then force `t_rho=0`.

## Door / frontier delta

Old open core: “prove zero harmonic residue” for a tail-Roos class, with no source-native meaning of
residue.

New open core: prove one explicit limit law for restarted nested sieve variation:

`Tendsto (fun N => S_N(W_{t_rho})) atTop (nhds 0)`.

All analytic quotient ambiguity has been removed. Any proposed source-dagger or Stokes producer can
now be tested coefficientwise against this reporter.

## Log

- 2026-08-06 — created directly in stage 1 after corpus and literature audit; attempts 1–2
  falsified; attempt 3 dependency-closed on paper.
- 2026-08-06 — advanced to stage 2 after complete proof and hostile circularity audit.
